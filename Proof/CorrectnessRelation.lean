import Proof.Semantics
import Proof.Analysis

namespace Proof

def ContextFree : Expr → Prop
| Expr.thisE      => False
| Expr.paramE     => False
| Expr.newC _ a b => ContextFree a ∧ ContextFree b
| Expr.app a b    => ContextFree a ∧ ContextFree b
| Expr.proj a _   => ContextFree a
| Expr.gproj _ _  => True
| Expr.val _      => True

def ValueFree : Expr → Prop
| Expr.thisE      => True
| Expr.paramE     => True
| Expr.newC _ a b => ValueFree a ∧ ValueFree b
| Expr.app a b    => ValueFree a ∧ ValueFree b
| Expr.proj a _   => ValueFree a
| Expr.gproj _ _  => True
| Expr.val _      => False

def Heap.opOf (H : Heap) : Value → Set OPair
  | Value.loc ℓ =>
    match H ℓ with
    | some o => {(o.g, o.cls)}
    | none   => ∅
  | Value.btrue  => ∅
  | Value.bfalse => ∅

inductive KJR (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) :
    Expr → Set OPair → Prop
  | val {v} : KJR G σ L H S (Expr.val v) (H.opOf v)
  | thisE {t p κ} :
      S.topCall = some (Frame.call t p κ) →
      KJR G σ L H S Expr.thisE (H.opOf (Value.loc t))
  | paramE {t p κ} :
      S.topCall = some (Frame.call t p κ) →
      KJR G σ L H S Expr.paramE (H.opOf p)
  | proj {e i K} :
      KJR G σ L H S e K → KJR G σ L H S (Expr.proj e i) (⋃ p ∈ K, σ.Fld i p.1 p.2)
  | gproj {G₀ i} : KJR G σ L H S (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJR G σ L H S (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJR G σ L H S e₁ K₁ → KJR G σ L H S (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret G p.2)

/-- `KJR` is deterministic. -/
theorem KJR.det {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ {e K K'}, KJR G σ L H S e K → KJR G σ L H S e K' → K = K'
  | _, _, _, .val, .val => rfl
  | _, _, _, .thisE htc, .thisE htc' => by rw [htc] at htc'; cases htc'; rfl
  | _, _, _, .paramE htc, .paramE htc' => by rw [htc] at htc'; cases htc'; rfl
  | _, _, _, .proj h, .proj h' => by rw [KJR.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJR.det h h']

/-- Plug monotonicity of `KJR`: if every runtime K-set of the contractum `eₓ`
    is covered by some runtime K-set of the redex `eᵣ`, the same holds after
    plugging both into an evaluation context `E`.  Only the head position of a
    projection/application feeds the surrounding K-set (`newC` and the argument
    position ignore the subterm), so the covering propagates layer by layer. -/
theorem KJR.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx) (K : Set OPair), KJR G σ L H S (E.plug eₓ) K →
      ∃ K', KJR G σ L H S (E.plug eᵣ) K' ∧ K ⊆ K' := by
  intro E
  induction E with
  | hole => exact h
  | projc E i ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | proj hK₀ =>
      obtain ⟨K', hK', hsub⟩ := ih _ hK₀
      exact ⟨_, .proj hK', Set.biUnion_subset_biUnion_left hsub⟩
  | appL E a ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | app hK₀ =>
      obtain ⟨K', hK', hsub⟩ := ih _ hK₀
      exact ⟨_, .app hK', Set.biUnion_subset_biUnion_left hsub⟩
  | appR w E _ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | app hK₀ =>
      cases hK₀
      exact ⟨_, .app .val, subset_rfl⟩
  | newL C E a _ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | newC => exact ⟨_, .newC, subset_rfl⟩
  | newR C w E _ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | newC => exact ⟨_, .newC, subset_rfl⟩

/-! ### Heap/value typing -/

/-- Param soundness of the call stack: every call frame's argument, if it
    points to an allocated object, has that object's owner pair inside
    `σ.Param(G)(D)` for the receiver's class `D`.  (The conclusion is
    conditional on allocation — `H.opOf p ⊆ σ.Param G D` in `Heap.opOf`
    terms — rather than asserting allocatedness, so that establishing it for
    a freshly pushed frame needs only a K-set bound on the argument.) -/
def ParamInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G C, S' <:+ S → S'.topInit = some (i, cfs, r)
    → Stack.TopInit S' G → Frame.call t p κ ∈ cfs → H t = some C
      → ∀ ℓ, p = Value.loc ℓ → ∀ D, H ℓ = some D → (D.g, D.cls) ∈ σ.Param G C.cls

/-- Heap typing (Fld soundness): for every allocated object `H ℓ = C(v₁, v₂)`
    and field index `i`, if that field holds a location `ℓ'` pointing to an
    allocated object `H ℓ' = C'(…)`, then `C'`'s owner pair lies in
    `σ.Fldᵢ((G, C))` — the owner-pair set the analysis `⇓ᴷ` predicts for the
    `i`-th field of a `C`-object owned by `G`.  Boolean values carry no class
    and are vacuously sound.  This is what makes `E-Proj` preserve `Inv`. -/
def FldInv (σ : Sigma) (H : Heap) (S: Stack) : Prop :=
  ∀ (S' : Stack) G l (C : ClassName) (v₁ v₂ : Value),
    S' <:+ S → Stack.TopInit S' G → H l = some (ClsIns.mk C G v₁ v₂)
      → ∀ i ℓ', (ClsIns.mk C G v₁ v₂).field i = Value.loc ℓ' →
        ∃ c', H ℓ' = some c' ∧ (c'.g, c'.cls) ∈ σ.Fld i G C

/-- Global-table typing: initialized global fields have their owner pairs
    inside `GFldᵢ`. -/
def GTableInv (σ : Sigma) (H : Heap) (Γ : GTable) : Prop :=
  ∀ g o, Γ g = some o →
    ∀ i ℓ', o.field i = some (Value.loc ℓ') →
      ∃ c', H ℓ' = some c' ∧ (c'.g, c'.cls) ∈ σ.GFld i g

/-- Ret soundness of a returning value against the topmost call frame.
    Guarded by `S.topInit = some …` (like `ArgInv`/`CallInv`, which pins the
    ambient `G`): on an init-frame-less stack `Stack.TopInit` holds vacuously
    of *every* `G`, and the bound is not provable for arbitrary `G`. -/
def RetInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → Stack.TopInit S G
    → ∀ t p κ, S.topCall = some (Frame.call t p κ) → ∀ D, H t = some D
      → ∀ K, KJR G σ L H S e K → K ⊆ σ.Ret G D.cls

/-- Runtime Param soundness of a focus expression (the runtime shadow of
    `param_re`, Step 2g): for *every* application subterm, the argument's
    runtime K-set lies inside `σ.Param G D` for every owner pair `(_, D)` the
    function position may denote.  Structural (rather than quantified over
    evaluation-context decompositions) so that apps not yet in evaluation
    position — e.g. inside the second argument of an unreduced `newC` — are
    covered before reduction exposes them. -/
def ArgSound (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Expr → Prop
  | Expr.app e₁ e₂ =>
      ArgSound G σ L H S e₁ ∧ ArgSound G σ L H S e₂ ∧
      ∀ K₁ K₂, KJR G σ L H S e₁ K₁ → KJR G σ L H S e₂ K₂ →
        ∀ p ∈ K₁, K₂ ⊆ σ.Param G p.2
  | Expr.newC _ e₁ e₂ => ArgSound G σ L H S e₁ ∧ ArgSound G σ L H S e₂
  | Expr.proj e _ => ArgSound G σ L H S e
  | _ => True

/-- `ArgSound` of the focus, for the global named by the stack's topmost init
    frame.  Guarded by `S.topInit = some …` (which pins `G`, unlike the
    vacuously universal `Stack.TopInit` on init-frame-less stacks), mirroring
    how `RetInv` is vacuous without a top call frame.  This is what makes a
    pushed call frame `Param`-sound in `E-AppBeta`. -/
def ArgInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → Stack.TopInit S G →
    ArgSound G σ L H S e

/-- `ArgSound` restricts to the expression sitting in the hole of an
    evaluation context. -/
theorem ArgSound.of_plug {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ (E : ECtx) {e : Expr}, ArgSound G σ L H S (E.plug e) → ArgSound G σ L H S e
  | .hole, _, h => h
  | .projc E _, _, h => ArgSound.of_plug E h
  | .appL E _, _, h => ArgSound.of_plug E h.1
  | .appR _ E, _, h => ArgSound.of_plug E h.2.1
  | .newL _ E _, _, h => ArgSound.of_plug E h.1
  | .newR _ _ E, _, h => ArgSound.of_plug E h.2

/-- Plug monotonicity of `ArgSound`, the companion of `KJR.plug_mono`: if the
    contractum `eₓ` is itself `ArgSound` and every runtime K-set of `eₓ` is
    covered by one of the redex `eᵣ`, then `ArgSound` transports from
    `E[eᵣ]` to `E[eₓ]`.  The K-set bound of each application layer around the
    hole survives because its hypotheses only shrink (contravariance in the
    `KJR` positions). -/
theorem ArgSound.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (hx : ArgSound G σ L H S eₓ)
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), ArgSound G σ L H S (E.plug eᵣ) → ArgSound G σ L H S (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => ArgSound.plug_mono hx h E hr
  | .appL E a, hr =>
      ⟨ArgSound.plug_mono hx h E hr.1, hr.2.1, fun K₁ K₂ hK₁ hK₂ p hp => by
        obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.plug_mono h E K₁ hK₁
        exact hr.2.2 K₁' K₂ hK₁' hK₂ p (hsub₁ hp)⟩
  | .appR w E, hr =>
      ⟨trivial, ArgSound.plug_mono hx h E hr.2.1, fun K₁ K₂ hK₁ hK₂ p hp => by
        obtain ⟨K₂', hK₂', hsub₂⟩ := KJR.plug_mono h E K₂ hK₂
        exact hsub₂.trans (hr.2.2 K₁ K₂' hK₁ hK₂' p hp)⟩
  | .newL _ E _, hr => ⟨ArgSound.plug_mono hx h E hr.1, hr.2⟩
  | .newR _ _ E, hr => ⟨hr.1, ArgSound.plug_mono hx h E hr.2⟩

/-- On value-free expressions, the runtime `KJR` is covered by the static
    `⇓ᴷ` in context `c`, provided `c` accounts for the stack-consulting rules:
    in a class context `some C`, `hthis`/`hparam` bound the runtime
    `this`/`param` K-sets by the analysis' `This`/`Param` sets (only a
    covering `K ⊆ K'`, since the runtime sets are single owner pairs); in the
    empty context (`KJ0` has no `thisE`/`paramE` rules) the expression must be
    `this`/`param`-free, and the hypotheses are vacuous.  The structural rules
    are identical on both sides, and the `proj`/`app` K-sets are monotone in
    the head's K-set, so the covering propagates. -/
theorem KJR.to_kjc {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} {c : Ctx}
    (hthis : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C, {(G', C)})
    (hparam : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.paramE K → K ⊆ σ.Param G C)
    {e : Expr} {K : Set OPair} (hpf : c = none → ContextFree e) (hvf : ValueFree e)
    (hK : KJR G σ L H S e K) : ∃ K', KJC G σ L c e K' ∧ K ⊆ K' := by
  induction hK with
  | val => exact False.elim hvf
  | thisE htc =>
    cases c with
    | none => exact False.elim (hpf rfl)
    | some C => exact ⟨_, KJ.thisE, hthis C rfl _ (.thisE htc)⟩
  | paramE htc =>
    cases c with
    | none => exact False.elim (hpf rfl)
    | some C => exact ⟨_, KJ.paramE, hparam C rfl _ (.paramE htc)⟩
  | proj h ih =>
    obtain ⟨K', hK', hsub⟩ := ih hpf hvf
    exact ⟨_, KJC.proj hK', Set.biUnion_subset_biUnion_left hsub⟩
  | gproj => exact ⟨_, KJC.gproj, subset_rfl⟩
  | newC => exact ⟨_, KJC.newC, subset_rfl⟩
  | app h ih =>
    obtain ⟨K', hK', hsub⟩ := ih (fun hc => (hpf hc).1) hvf.1
    exact ⟨_, KJC.app hK', Set.biUnion_subset_biUnion_left hsub⟩

/-- Reachable code is `ArgSound`: every application subterm is reachable
    (`RE` is closed under subexpressions), its parts' runtime K-sets are
    covered by their static `⇓ᴷ` K-sets (`KJR.to_kjc` in context `c`), and
    `param_re` bounds the argument.  At `c = none` the stack-consulting
    hypotheses are vacuous and this establishes `ArgInv` when an initializer
    becomes the focus (I-Push / I-Next); at `c = some C` it establishes
    `ArgInv` for a callee body once the fresh frame's runtime `This`/`Param`
    bounds are known (E-AppBeta). -/
theorem ArgSound.of_re {σ : Sigma} {L : Program} {G : GlobName} {H : Heap} {S : Stack}
    {c : Ctx} (hσ : FixPoint σ L)
    (hthis : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C, {(G', C)})
    (hparam : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.paramE K → K ⊆ σ.Param G C) :
    ∀ e, RE σ L G c e → (c = none → ContextFree e) → ValueFree e →
      ArgSound G σ L H S e := by
  intro e
  induction e with
  | thisE => intro _ _ _; trivial
  | paramE => intro _ _ _; trivial
  | val v => intro _ _ hvf; exact False.elim hvf
  | gproj G₀ i => intro _ _ _; trivial
  | proj e i ih => intro hre hpf hvf; exact ih (RE.proj hre) hpf hvf
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hre hpf hvf
    exact ⟨ih₁ (RE.newC₁ hre) (fun hc => (hpf hc).1) hvf.1,
           ih₂ (RE.newC₂ hre) (fun hc => (hpf hc).2) hvf.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    intro hre hpf hvf
    refine ⟨ih₁ (RE.app₁ hre) (fun hc => (hpf hc).1) hvf.1,
            ih₂ (RE.app₂ hre) (fun hc => (hpf hc).2) hvf.2, ?_⟩
    intro K₁ K₂ hK₁ hK₂ p hp
    obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).1) hvf.1 hK₁
    obtain ⟨K₂', hK₂', hsub₂⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).2) hvf.2 hK₂
    exact hsub₂.trans
      (hσ.param_re hre hK₁' hK₂' p.2 (mem_classes.mpr ⟨p.1, hsub₁ hp⟩))

/-! ### The runtime calls bound (`Calls0R`)

  The runtime shadow of `Calls0`/`rm_init`/`rm_closed`: every application
  subterm of the focus can only call classes in `σ.RM G`.  Like `ArgSound`
  (and for the same two reasons) it is *structural* rather than an inductive
  `e calls K` judgment: (i) apps not yet in evaluation position must be
  covered before reduction exposes them, and (ii) at the use site
  (`inv_step_app`'s `RMInv` case) the bound must be *read off* at the redex —
  an inductive judgment would additionally need a derivation for the whole
  focus, which does not exist when an unevaluated sibling in the context has
  `this`/`param` in function position over a stack without a top call
  frame. -/

/-- Runtime calls soundness of a focus expression (the `Calls0R` bound): for
    every application subterm, the classes its function position may denote at
    runtime (`KJR`) lie in `σ.RM G`.  This is what names the callee class in
    `E-AppBeta`: at the redex `ℓ(v)` the function position's runtime K-set is
    `{(G, cls ℓ)}`, so `cls ℓ ∈ σ.RM G` — the missing `RMInv` obligation for
    the pushed frame. -/
def CallSound (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Expr → Prop
  | Expr.app e₁ e₂ =>
      CallSound G σ L H S e₁ ∧ CallSound G σ L H S e₂ ∧
      ∀ K₁, KJR G σ L H S e₁ K₁ → classes K₁ ⊆ σ.RM G
  | Expr.newC _ e₁ e₂ => CallSound G σ L H S e₁ ∧ CallSound G σ L H S e₂
  | Expr.proj e _ => CallSound G σ L H S e
  | _ => True

/-- `CallSound` of the focus, for the global named by the stack's topmost init
    frame — guarded exactly like `ArgInv`. -/
def CallInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → Stack.TopInit S G →
    CallSound G σ L H S e

/-- `CallSound` restricts to the expression sitting in the hole of an
    evaluation context. -/
theorem CallSound.of_plug {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ (E : ECtx) {e : Expr}, CallSound G σ L H S (E.plug e) → CallSound G σ L H S e
  | .hole, _, h => h
  | .projc E _, _, h => CallSound.of_plug E h
  | .appL E _, _, h => CallSound.of_plug E h.1
  | .appR _ E, _, h => CallSound.of_plug E h.2.1
  | .newL _ E _, _, h => CallSound.of_plug E h.1
  | .newR _ _ E, _, h => CallSound.of_plug E h.2

/-- `classes` is monotone. -/
theorem classes_mono {K K' : Set OPair} (h : K ⊆ K') : classes K ⊆ classes K' :=
  fun _ hx => let ⟨p, hp, he⟩ := hx; ⟨p, h hp, he⟩

/-- Plug monotonicity of `CallSound`, the analogue of `ArgSound.plug_mono`:
    if the contractum `eₓ` is itself `CallSound` and every runtime K-set of
    `eₓ` is covered by one of the redex `eᵣ`, then `CallSound` transports from
    `E[eᵣ]` to `E[eₓ]`. -/
theorem CallSound.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (hx : CallSound G σ L H S eₓ)
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), CallSound G σ L H S (E.plug eᵣ) → CallSound G σ L H S (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => CallSound.plug_mono hx h E hr
  | .appL E a, hr =>
      ⟨CallSound.plug_mono hx h E hr.1, hr.2.1, fun K₁ hK₁ => by
        obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.plug_mono h E K₁ hK₁
        exact (classes_mono hsub₁).trans (hr.2.2 K₁' hK₁')⟩
  | .appR w E, hr => ⟨trivial, CallSound.plug_mono hx h E hr.2.1, hr.2.2⟩
  | .newL _ E _, hr => ⟨CallSound.plug_mono hx h E hr.1, hr.2⟩
  | .newR _ _ E, hr => ⟨hr.1, CallSound.plug_mono hx h E hr.2⟩

/-- `KJ0` is deterministic (needed to match the `KJ0` premise of a `Calls0`
    derivation against the one produced by `KJR.to_kjc`). -/
theorem KJ0.det {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ {e K K'}, KJ0 G σ L e K → KJ0 G σ L e K' → K = K'
  | _, _, _, .proj h, .proj h' => by rw [KJ0.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJ0.det h h']
  | _, _, _, .val, .val => rfl

/-- `KJ0` is total on `this`/`param`-free expressions (the only rules
    consulting a class context are `thisE`/`paramE`, which `KJ0` lacks). -/
theorem KJ0.total {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ e, ContextFree e → ∃ K, KJ0 G σ L e K := by
  intro e
  induction e with
  | thisE => intro hpf; exact False.elim hpf
  | paramE => intro hpf; exact False.elim hpf
  | val v => intro _; exact ⟨_, .val⟩
  | gproj G₀ i => intro _; exact ⟨_, .gproj⟩
  | proj e i ih => intro hpf; obtain ⟨K, hK⟩ := ih hpf; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ => intro _; exact ⟨_, .newC⟩
  | app e₁ e₂ ih₁ ih₂ => intro hpf; obtain ⟨K₁, hK₁⟩ := ih₁ hpf.1; exact ⟨_, .app hK₁⟩

/-- `Calls0` is total on `this`/`param`-free expressions. -/
theorem Calls0.total {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ e, ContextFree e → ∃ K, Calls0 G σ L e K := by
  intro e
  induction e with
  | thisE => intro hpf; exact False.elim hpf
  | paramE => intro hpf; exact False.elim hpf
  | val v => intro _; exact ⟨_, .val⟩
  | gproj G₀ i => intro _; exact ⟨_, .gproj⟩
  | proj e i ih => intro hpf; obtain ⟨K, hK⟩ := ih hpf; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hpf
    obtain ⟨K₁, h₁⟩ := ih₁ hpf.1
    obtain ⟨K₂, h₂⟩ := ih₂ hpf.2
    exact ⟨_, .newC h₁ h₂⟩
  | app e₁ e₂ ih₁ ih₂ =>
    intro hpf
    obtain ⟨K₁, hK₁⟩ := KJ0.total e₁ hpf.1
    obtain ⟨K₂, h₂⟩ := ih₁ hpf.1
    obtain ⟨K₃, h₃⟩ := ih₂ hpf.2
    exact ⟨_, .app hK₁ h₂ h₃⟩

/-- `this`/`param`-free, value-free code whose `Calls0` set lies in `σ.RM G`
    is `CallSound`: `KJR.to_kjc` (at the empty context) covers each function
    position's runtime K-set by its `KJ0` one, whose classes the `Calls0`
    derivation collects.  Together with `rm_init` this establishes `CallInv`
    when an initializer becomes the focus (I-Push / I-Next). -/
theorem CallSound.of_calls0 {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ {e K}, Calls0 G σ L e K → K ⊆ σ.RM G → ContextFree e → ValueFree e →
      CallSound G σ L H S e := by
  intro e K hc
  induction hc with
  | gproj => intro _ _ _; trivial
  | val => intro _ _ hvf; exact False.elim hvf
  | proj h ih => intro hK hpf hvf; exact ih hK hpf hvf
  | newC h₁ h₂ ih₁ ih₂ =>
    intro hK hpf hvf
    exact ⟨ih₁ (Set.subset_union_left.trans hK) hpf.1 hvf.1,
           ih₂ (Set.subset_union_right.trans hK) hpf.2 hvf.2⟩
  | app hkj h₁ h₂ ih₁ ih₂ =>
    intro hK hpf hvf
    refine ⟨ih₁ ((Set.subset_union_right.trans Set.subset_union_left).trans hK) hpf.1 hvf.1,
            ih₂ (Set.subset_union_right.trans hK) hpf.2 hvf.2, ?_⟩
    intro Kr hKr
    obtain ⟨K₁', hK₁', hsub⟩ := KJR.to_kjc (c := none) (fun _ hc => nomatch hc)
      (fun _ hc => nomatch hc) (fun _ => hpf.1) hvf.1 hKr
    have hsub' : Kr ⊆ _ := (KJ0.det hK₁' hkj) ▸ hsub
    exact (classes_mono hsub').trans
      ((Set.subset_union_left.trans Set.subset_union_left).trans hK)

/-- `KJ` is deterministic. -/
theorem KJ.det {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program} :
    ∀ {e K K'}, KJ G C σ L e K → KJ G C σ L e K' → K = K'
  | _, _, _, .thisE, .thisE => rfl
  | _, _, _, .paramE, .paramE => rfl
  | _, _, _, .proj h, .proj h' => by rw [KJ.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJ.det h h']
  | _, _, _, .val, .val => rfl

/-- `KJ` is total (unlike `KJ0`, the class context interprets `this`/`param`,
    so no `ContextFree` side condition is needed). -/
theorem KJ.total {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program} :
    ∀ e, ∃ K, KJ G C σ L e K := by
  intro e
  induction e with
  | thisE => exact ⟨_, .thisE⟩
  | paramE => exact ⟨_, .paramE⟩
  | val v => exact ⟨_, .val⟩
  | gproj G₀ i => exact ⟨_, .gproj⟩
  | proj e i ih => obtain ⟨K, hK⟩ := ih; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ => exact ⟨_, .newC⟩
  | app e₁ e₂ ih₁ ih₂ => obtain ⟨K₁, hK₁⟩ := ih₁; exact ⟨_, .app hK₁⟩

/-- `Calls` is total. -/
theorem Calls.total {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program} :
    ∀ e, ∃ K, Calls G C σ L e K := by
  intro e
  induction e with
  | thisE => exact ⟨_, .thisE⟩
  | paramE => exact ⟨_, .paramE⟩
  | val v => exact ⟨_, .val⟩
  | gproj G₀ i => exact ⟨_, .gproj⟩
  | proj e i ih => obtain ⟨K, hK⟩ := ih; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ =>
    obtain ⟨K₁, h₁⟩ := ih₁
    obtain ⟨K₂, h₂⟩ := ih₂
    exact ⟨_, .newC h₁ h₂⟩
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨K₁, hK₁⟩ := KJ.total e₁
    obtain ⟨K₂, h₂⟩ := ih₁
    obtain ⟨K₃, h₃⟩ := ih₂
    exact ⟨_, .app hK₁ h₂ h₃⟩

/-- The class-context analogue of `CallSound.of_calls0`: value-free
    method-body code whose `Calls` set lies in `σ.RM G` is `CallSound`,
    provided the stack interprets `this`/`param` inside the analysis'
    `This`/`Param` sets (`hthis`/`hparam` — the fresh frame's bounds at
    E-AppBeta, in the shape `KJR.to_kjc` consumes them). -/
theorem CallSound.of_calls {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program}
    {H : Heap} {S : Stack}
    (hthis : ∀ C', (some C : Ctx) = some C' → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C', {(G', C')})
    (hparam : ∀ C', (some C : Ctx) = some C' → ∀ K, KJR G σ L H S Expr.paramE K →
      K ⊆ σ.Param G C') :
    ∀ {e K}, Calls G C σ L e K → K ⊆ σ.RM G → ValueFree e →
      CallSound G σ L H S e := by
  intro e K hc
  induction hc with
  | thisE => intro _ _; trivial
  | paramE => intro _ _; trivial
  | gproj => intro _ _; trivial
  | val => intro _ hvf; exact False.elim hvf
  | proj h ih => intro hK hvf; exact ih hK hvf
  | newC h₁ h₂ ih₁ ih₂ =>
    intro hK hvf
    exact ⟨ih₁ (Set.subset_union_left.trans hK) hvf.1,
           ih₂ (Set.subset_union_right.trans hK) hvf.2⟩
  | app hkj h₁ h₂ ih₁ ih₂ =>
    intro hK hvf
    refine ⟨ih₁ ((Set.subset_union_right.trans Set.subset_union_left).trans hK) hvf.1,
            ih₂ (Set.subset_union_right.trans hK) hvf.2, ?_⟩
    intro Kr hKr
    obtain ⟨K₁', hK₁', hsub⟩ := KJR.to_kjc (c := some C) hthis hparam
      (fun hc => nomatch hc) hvf.1 hKr
    have hsub' : Kr ⊆ _ := (KJ.det hK₁' hkj) ▸ hsub
    exact (classes_mono hsub').trans
      ((Set.subset_union_left.trans Set.subset_union_left).trans hK)

/-- RM soundness of the whole stack: in *every* suffix of `S`, the call frames
    sitting above the suffix's topmost init frame have their receiver's class in
    `σ.RM G` for that init frame's global `G`.  Quantifying over suffixes pairs
    each call frame with the nearest init frame below it, so every segment of
    the stack is constrained, not just the one above the topmost init frame. -/
def RMInv (σ : Sigma) (H: Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r f G l, S' <:+ S → S'.topInit = some (i, cfs, r)
  → Stack.TopInit S' G → f ∈ cfs → f.loc = some l → ∃ C, H l = some C ∧ C.cls ∈ σ.RM G

/-- Runtime `This` soundness of a focus expression (the runtime shadow of
    `this_re`, as `ArgSound` shadows `param_re` and `CallSound` shadows
    `Calls0`): for every application subterm, each owner pair the function
    position may denote at runtime has its owner in `σ.This`.  This is what
    yields the runtime `This` bound for the frame pushed by `E-AppBeta`: at
    the redex `ℓ(v)` the function position's runtime K-set is `{(G, cls ℓ)}`,
    so `G ∈ σ.This G (cls ℓ)` — the `hthis` hypothesis of `KJR.to_kjc` for
    the callee body. -/
def ThisSound (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Expr → Prop
  | Expr.app e₁ e₂ =>
      ThisSound G σ L H S e₁ ∧ ThisSound G σ L H S e₂ ∧
      ∀ K₁, KJR G σ L H S e₁ K₁ → ∀ p ∈ K₁, p.1 ∈ σ.This G p.2
  | Expr.newC _ e₁ e₂ => ThisSound G σ L H S e₁ ∧ ThisSound G σ L H S e₂
  | Expr.proj e _ => ThisSound G σ L H S e
  | _ => True

/-- `This` soundness of the call stack (the per-frame residue of `ThisSound`,
    shaped like `ParamInv`): every call frame's receiver, if allocated, has
    its owner inside `σ.This G C` for the receiver's class `C` and the
    nearest init frame's global `G`. -/
def ThisInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G, S' <:+ S → S'.topInit = some (i, cfs, r)
    → Stack.TopInit S' G → Frame.call t p κ ∈ cfs
    → ∀ D, H t = some D → D.g ∈ σ.This G D.cls

/-- `ThisSound` restricts to the expression sitting in the hole of an
    evaluation context. -/
theorem ThisSound.of_plug {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ (E : ECtx) {e : Expr}, ThisSound G σ L H S (E.plug e) → ThisSound G σ L H S e
  | .hole, _, h => h
  | .projc E _, _, h => ThisSound.of_plug E h
  | .appL E _, _, h => ThisSound.of_plug E h.1
  | .appR _ E, _, h => ThisSound.of_plug E h.2.1
  | .newL _ E _, _, h => ThisSound.of_plug E h.1
  | .newR _ _ E, _, h => ThisSound.of_plug E h.2

/-- Plug monotonicity of `ThisSound`, the analogue of `CallSound.plug_mono`
    (only the function position's K-set is consulted). -/
theorem ThisSound.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (hx : ThisSound G σ L H S eₓ)
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), ThisSound G σ L H S (E.plug eᵣ) → ThisSound G σ L H S (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => ThisSound.plug_mono hx h E hr
  | .appL E a, hr =>
      ⟨ThisSound.plug_mono hx h E hr.1, hr.2.1, fun K₁ hK₁ p hp => by
        obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.plug_mono h E K₁ hK₁
        exact hr.2.2 K₁' hK₁' p (hsub₁ hp)⟩
  | .appR w E, hr => ⟨trivial, ThisSound.plug_mono hx h E hr.2.1, hr.2.2⟩
  | .newL _ E _, hr => ⟨ThisSound.plug_mono hx h E hr.1, hr.2⟩
  | .newR _ _ E, hr => ⟨hr.1, ThisSound.plug_mono hx h E hr.2⟩

/-- Reachable code is `ThisSound`: each application subterm is reachable,
    `KJR.to_kjc` covers its function position's runtime K-set by the static
    one, and `this_re` records every owner/class pair of that K-set in
    `σ.This`.  Context-generalized exactly like `ArgSound.of_re`. -/
theorem ThisSound.of_re {σ : Sigma} {L : Program} {G : GlobName} {H : Heap} {S : Stack}
    {c : Ctx} (hσ : FixPoint σ L)
    (hthis : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C, {(G', C)})
    (hparam : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.paramE K → K ⊆ σ.Param G C) :
    ∀ e, RE σ L G c e → (c = none → ContextFree e) → ValueFree e →
      ThisSound G σ L H S e := by
  intro e
  induction e with
  | thisE => intro _ _ _; trivial
  | paramE => intro _ _ _; trivial
  | val v => intro _ _ hvf; exact False.elim hvf
  | gproj G₀ i => intro _ _ _; trivial
  | proj e i ih => intro hre hpf hvf; exact ih (RE.proj hre) hpf hvf
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hre hpf hvf
    exact ⟨ih₁ (RE.newC₁ hre) (fun hc => (hpf hc).1) hvf.1,
           ih₂ (RE.newC₂ hre) (fun hc => (hpf hc).2) hvf.2⟩
  | app e₁ e₂ ih₁ ih₂ =>
    intro hre hpf hvf
    refine ⟨ih₁ (RE.app₁ hre) (fun hc => (hpf hc).1) hvf.1,
            ih₂ (RE.app₂ hre) (fun hc => (hpf hc).2) hvf.2, ?_⟩
    intro K₁ hK₁ p hp
    obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).1) hvf.1 hK₁
    exact hσ.this_re hre hK₁' rfl p.2 (mem_classes.mpr ⟨p.1, hsub₁ hp⟩)
      ⟨p, hsub₁ hp, rfl⟩

/-- `ThisSound` of the focus, guarded exactly like `ArgInv`/`CallInv`. -/
def ThisSoundInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → Stack.TopInit S G →
    ThisSound G σ L H S e

/-- Stack-chain typing: for every call frame `Frame.call t p E` in the stack,
    the push-time focus `E[t(p)]` — reconstructible from the frame's own
    fields — is Ret/Arg/Call/This-sound over the stack below the frame. -/
def FrameInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ (S': Stack) t p E, (Frame.call t p E) :: S' <:+ S →
    ∀ G i cfs r, S'.topInit = some (i, cfs, r) → Stack.TopInit S' G →
      let redex := Expr.app (Expr.val (Value.loc t)) (Expr.val p)
      (∀ t' p' κ', S'.topCall = some (Frame.call t' p' κ') →
        ∀ D', H t' = some D' →
          ∀ K, KJR G σ L H S' (E.plug redex) K → K ⊆ σ.Ret G D'.cls)
      ∧ ArgSound G σ L H S' (E.plug redex)
      ∧ CallSound G σ L H S' (E.plug redex)
      ∧ ThisSound G σ L H S' (E.plug redex)


/-! ### The subject-reduction invariant -/

/-- The subject-reduction invariant `Inv σ L G` on configurations.  For a focus
    `e`: the globals it references stay in `Dep(G)`, the methods it can call stay
    in `RM(G)`, the call stack is `Param`-sound, the heap / global table are
    value-class sound, and the focus's own applications are argument-sound
    (`ArgInv` — this is what seeds `ParamInv` for the frame pushed by
    `E-AppBeta`), calls-sound (`CallInv` — this is what seeds `RMInv` there)
    and `This`-sound (`ThisSoundInv` — this is what seeds `ThisInv` there,
    and `ThisInv` in turn discharges `KJR.to_kjc`'s `hthis` for the callee
    body).  Because the runtime focus is `this`/`param`-free, the
    context-free judgments `GRef`/`Calls0` are the right ones. -/
def Inv (σ : Sigma) (L : Program) : Config → Prop
  | .mk H Γ S e =>
    ParamInv σ H S
    ∧ FldInv σ H S
    ∧ GTableInv σ H Γ
    ∧ RetInv σ L H S e
    ∧ ArgInv σ L H S e
    ∧ CallInv σ L H S e
    ∧ RMInv σ H S
    ∧ ThisInv σ H S
    ∧ ThisSoundInv σ L H S e
    ∧ FrameInv σ L H S
  | .crash => True

/-- **Step 1 of Theorem 1.**  The invariant holds at the initial configuration
    `⟨∅, ∅, ε, e⟩`, for any focus `e`.  All nine components are vacuous there:
    `Param`/`Fld`/`RM`/`This` soundness bound objects allocated in the (empty)
    heap, `GTable` soundness ranges over the (empty) table, and
    `Ret`/`Arg`/`Call`/`ThisSound` soundness fire only under a topmost init
    frame, which the empty stack lacks.  From here the `inv_step_*` lemmas
    carry `Inv` along every reduction. -/
theorem inv_empty {σ : Sigma} {e : Expr} {L : Program} (_hσ : FixPoint σ L):
    Inv σ L (.mk (fun _ => none) (fun _ => none) List.nil e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ParamInv: no receiver is allocated in the empty heap.
    intro S' i cfs r t p κ G C _ _ _ _ hHt
    simp at hHt
  · -- FldInv: nothing is allocated in the empty heap.
    intro S' G l C v₁ v₂ _ _ hHl
    simp at hHl
  · -- GTableInv: the empty table has no entries.
    intro g o hg
    simp at hg
  · -- RetInv: the empty stack has no topmost init frame.
    intro G i cfs r hti
    simp [Stack.topInit] at hti
  · -- ArgInv: the empty stack has no topmost init frame.
    intro G i cfs r htop
    simp [Stack.topInit] at htop
  · -- CallInv: the empty stack has no topmost init frame.
    intro G i cfs r htop
    simp [Stack.topInit] at htop
  · -- RMInv: no frame's receiver is allocated in the empty heap.
    intro S' i cfs r f G l hsub htop hTopG hf hloc
    rcases List.suffix_nil.mp hsub with rfl
    simp [Stack.topInit] at htop
  · -- ThisInv: the empty stack has no suffix with an init frame.
    intro S' i cfs r t p κ G hsub hti
    rcases List.suffix_nil.mp hsub with rfl
    simp [Stack.topInit] at hti
  · -- ThisSoundInv: the empty stack has no topmost init frame.
    intro G i cfs r htop
    simp [Stack.topInit] at htop
  · -- FrameInv
    intro G i cfs r htop
    simp at htop

/-- **Step 2, E-Proj case.**  `Inv` is preserved by the `E-Proj` reduction
    `E[ℓ.i] → E[vᵢ]`.  For `RetInv`, the contractum's runtime K-set
    `H.opOf vᵢ` is covered by the redex's `σ.Fld i G C` (that is exactly
    `FldInv` at `ℓ`), and `KJR.plug_mono` transports the covering through
    `E`. -/
theorem inv_step_proj {σ : Sigma} {G : GlobName} {L : Program} {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx}
    {ℓ : Loc} {C : ClassName} {v₁ v₂ : Value} {i : Idx} {c : ClsIns}
    (_hG : Stack.TopInit S G) (hC : c = (.mk C G v₁ v₂)) (_hHl : H ℓ = some c) (_hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val (c.field i)))) := by
  obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hts, hframe⟩ := hinv
  subst hC
  -- Covering of the contractum's runtime K-sets by the redex's, for any
  -- ambient global `G'`: `H.opOf vᵢ ⊆ σ.Fld i G C` is exactly `FldInv` at `ℓ`.
  have hP : ∀ (G' : GlobName) K,
      KJR G' σ L H S (Expr.val ((ClsIns.mk C G v₁ v₂).field i)) K →
      ∃ K', KJR G' σ L H S (Expr.proj (Expr.val (Value.loc ℓ)) i) K' ∧ K ⊆ K' := by
    intro G' K hK
    cases hK
    refine ⟨_, .proj .val, ?_⟩
    intro q hq
    cases hfi : (ClsIns.mk C G v₁ v₂).field i with
    | loc ℓ' =>
      rw [hfi] at hq
      cases hHℓ' : H ℓ' with
      | none => simp [Heap.opOf, hHℓ'] at hq
      | some c' =>
        simp [Heap.opOf, hHℓ'] at hq
        subst hq
        obtain ⟨c'', hH'', hmem⟩ :=
          hfld S G ℓ C v₁ v₂ (List.suffix_refl S) _hG _hHl i ℓ' hfi
        rw [hHℓ'] at hH''
        cases hH''
        simpa [Heap.opOf, _hHl] using hmem
    | btrue => simp [hfi, Heap.opOf] at hq
    | bfalse => simp [hfi, Heap.opOf] at hq
  -- `H`/`Γ`/`S` are untouched by E-Proj, so the five stack/heap bounds carry
  -- over verbatim; only `RetInv`, `ArgInv`, `CallInv` and `ThisSoundInv`,
  -- which mention the focus, change.
  refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, ?_, hframe⟩
  · -- RetInv: Proved using hP and KJR.plug_mono
    intro G' i' cfs' r' hti' htiG' t p κ htc D hHt K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
    exact hsub.trans (hret G' i' cfs' r' hti' htiG' t p κ htc D hHt K' hK')
  · -- ArgInv: the contractum is a value (trivially `ArgSound`) and its K-sets
    -- are covered by the redex's, so `ArgSound.plug_mono` transports the bound.
    intro G' i' cfs' r' htop' htiG'
    exact ArgSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G v₁ v₂).field i))
      trivial (hP G') E (harg G' i' cfs' r' htop' htiG')
  · -- CallInv: same transport, via `CallSound.plug_mono`.
    intro G' i' cfs' r' htop' htiG'
    exact CallSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G v₁ v₂).field i))
      trivial (hP G') E (hcall G' i' cfs' r' htop' htiG')
  · -- ThisSoundInv: same transport, via `ThisSound.plug_mono`.
    intro G' i' cfs' r' htop' htiG'
    exact ThisSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G v₁ v₂).field i))
      trivial (hP G') E (hts G' i' cfs' r' htop' htiG')

/-- **Step 2, E-GProj case.**  `Inv` is preserved by the `E-GProj` reduction
    `E[G₁.i] → E[v]` (reading the initialized global field `Γ G₁ = g` with
    `g.field i = v`, mirroring `Step.gproj`).  Heap, table and stack are
    unchanged.  For `RetInv`, the contractum's runtime K-set `H.opOf v` is
    covered by the redex's `σ.GFld i G₁` (that is exactly `GTableInv` at
    `G₁`), and `KJR.plug_mono` transports the covering through `E`. -/
theorem inv_step_gproj {σ : Sigma} {G₁ : GlobName} {L : Program}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} {v : Value} {g : GEntry}
    (_hG : Γ G₁ = some g) (_hvi : g.field i = some v) (_hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G₁ i)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hts, hframe⟩ := hinv
    -- Covering of the contractum's runtime K-sets by the redex's, for any
    -- ambient global `G'`: `H.opOf v ⊆ σ.GFld i G₁` is exactly `GTableInv`.
    have hP : ∀ (G' : GlobName) K, KJR G' σ L H S (Expr.val v) K →
        ∃ K', KJR G' σ L H S (Expr.gproj G₁ i) K' ∧ K ⊆ K' := by
      intro G' K hK
      cases hK
      refine ⟨σ.GFld i G₁, .gproj, ?_⟩
      intro q hq
      cases v with
      | loc ℓ' =>
        cases hHℓ' : H ℓ' with
        | none => simp [Heap.opOf, hHℓ'] at hq
        | some c' =>
          simp [Heap.opOf, hHℓ'] at hq
          subst hq
          obtain ⟨c'', hH'', hmem⟩ := hgtable G₁ g _hG i ℓ' _hvi
          rw [hHℓ'] at hH''
          cases hH''
          exact hmem
      | btrue => simp [Heap.opOf] at hq
      | bfalse => simp [Heap.opOf] at hq
    -- `H`/`Γ`/`S` are untouched by E-GProj, so the five stack/heap bounds carry
    -- over verbatim; only `RetInv`, `ArgInv`, `CallInv` and `ThisSoundInv`,
    -- which mention the focus, change.
    refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, ?_, hframe⟩
    · -- RetInv: Using hP (G.i is inside original K) and KJR.plug_mono for plug
      intro G' i' cfs' r' hti' htiG' t p κ htc D hHt K hK
      obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
      exact hsub.trans (hret G' i' cfs' r' hti' htiG' t p κ htc D hHt K' hK')
    · -- ArgInv: the contractum is a value (trivially `ArgSound`) and its K-sets
      -- are covered by the redex's, so `ArgSound.plug_mono` transports the bound.
      intro G' i' cfs' r' htop' htiG'
      exact ArgSound.plug_mono (eₓ := Expr.val v)
        trivial (hP G') E (harg G' i' cfs' r' htop' htiG')
    · -- CallInv: same transport, via `CallSound.plug_mono`.
      intro G' i' cfs' r' htop' htiG'
      exact CallSound.plug_mono (eₓ := Expr.val v)
        trivial (hP G') E (hcall G' i' cfs' r' htop' htiG')
    · -- ThisSoundInv: same transport, via `ThisSound.plug_mono`.
      intro G' i' cfs' r' htop' htiG'
      exact ThisSound.plug_mono (eₓ := Expr.val v)
        trivial (hP G') E (hts G' i' cfs' r' htop' htiG')

theorem inv_step_app {σ : Sigma} {L : Program} {G  : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {eₐ : Expr} {l : Loc} {v v₁ v₂ : Value}
    {C : ClassName} (hσ : FixPoint σ L) (hG : Stack.TopInit S G) (hHl : H l = some (ClsIns.mk C G v₁ v₂))
    (hbody : Program.HasClass L C eₐ) (hbvf : ValueFree eₐ)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val v))))) :
    Inv σ L (.mk H Γ (Stack.push (Frame.call l v E) S) eₐ) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hts, hframe⟩ := hinv
    -- The fresh frame's bounds, read off the focus invariants at the redex
    -- (the function position's runtime K-set is `{(G, C)}` via `hHl`):
    -- `ThisSound` gives the runtime `This` bound, `ArgSound` the argument
    -- bound, `CallSound` the callee-class bound.
    have hfresh : ∀ i₀ cfs₀ r₀, S.topInit = some (i₀, cfs₀, r₀) →
        G ∈ σ.This G C ∧ H.opOf v ⊆ σ.Param G C ∧ C ∈ σ.RM G := by
      intro i₀ cfs₀ r₀ htopS
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨-, -, hbound⟩ := ThisSound.of_plug E (hts G i₀ cfs₀ r₀ htopS hG)
        exact hbound _ .val (G, C) (by simp [Heap.opOf, hHl])
      · obtain ⟨-, -, hbound⟩ := ArgSound.of_plug E (harg G i₀ cfs₀ r₀ htopS hG)
        exact hbound _ _ .val .val (G, C) (by simp [Heap.opOf, hHl])
      · obtain ⟨-, -, hbound⟩ := CallSound.of_plug E (hcall G i₀ cfs₀ r₀ htopS hG)
        exact hbound _ .val (mem_classes.mpr ⟨G, by simp [Heap.opOf, hHl]⟩)
    -- The first two bounds are exactly `KJR.to_kjc`'s `hthis`/`hparam`
    -- hypotheses over the *new* stack, whose top call frame is the fresh one
    -- (`this ↦ l`, a `(G, C)`-instance; `param ↦ v`).
    have hbridge : ∀ i₀ cfs₀ r₀, S.topInit = some (i₀, cfs₀, r₀) →
        (∀ C', (some C : Ctx) = some C' →
          ∀ K, KJR G σ L H (Stack.push (Frame.call l v E) S) Expr.thisE K →
            K ⊆ ⋃ G' ∈ σ.This G C', {(G', C')}) ∧
        (∀ C', (some C : Ctx) = some C' →
          ∀ K, KJR G σ L H (Stack.push (Frame.call l v E) S) Expr.paramE K →
            K ⊆ σ.Param G C') := by
      intro i₀ cfs₀ r₀ htopS
      obtain ⟨hGthis, hvparam, -⟩ := hfresh i₀ cfs₀ r₀ htopS
      constructor
      · intro C' hC' K hK
        obtain rfl : C = C' := Option.some.inj hC'
        cases hK with
        | thisE htc =>
          simp only [Stack.push, Stack.topCall, Option.some.injEq,
            Frame.call.injEq] at htc
          obtain ⟨rfl, -, -⟩ := htc
          intro q hq
          simp only [Heap.opOf, hHl, Set.mem_singleton_iff] at hq
          subst hq
          exact Set.mem_biUnion hGthis rfl
      · intro C' hC' K hK
        obtain rfl : C = C' := Option.some.inj hC'
        cases hK with
        | paramE htc =>
          simp only [Stack.push, Stack.topCall, Option.some.injEq,
            Frame.call.injEq] at htc
          obtain ⟨-, rfl, -⟩ := htc
          exact hvparam
    -- Pinning: the new stack's topmost init frame is `S`'s own (`topInit`
    -- looks through the pushed call frame), so any ambient `G'` equals `G`.
    have hpin : ∀ G' i' cfs' r',
        (Stack.push (Frame.call l v E) S).topInit = some (i', cfs', r') →
        Stack.TopInit (Stack.push (Frame.call l v E) S) G' →
        ∃ i₀ cfs₀ r₀, S.topInit = some (i₀, cfs₀, r₀) ∧ G' = G := by
      intro G' i' cfs' r' hti' htiG'
      cases htopS : S.topInit with
      | none => simp [Stack.push, Stack.topInit, htopS] at hti'
      | some x =>
        obtain ⟨i₀, cfs₀, r₀⟩ := x
        exact ⟨i₀, cfs₀, r₀, rfl, Option.some.inj
          ((htiG' i₀ (Frame.call l v E :: cfs₀) r₀
              (by simp [Stack.push, Stack.topInit, htopS])).symm.trans
            (hG i₀ cfs₀ r₀ htopS))⟩
    refine ⟨?_, ?_, hgtable, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv: only the freshly pushed frame is new; its argument bound
      -- `H.opOf v ⊆ σ.Param G C` is `ArgInv` at the redex (`KJR.val` gives the
      -- function position the runtime K-set `{(G, C)}` via `hHl`).
      intro S' i cfs r t p₁ κ G₁ C₁ hsub hti htG hf htC₁ ℓ hpℓ D hHD
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · cases htopS : S.topInit with
        | none => simp [Stack.topInit, htopS] at hti
        | some x =>
          obtain ⟨i₀, cfs₀, r₀⟩ := x
          simp [Stack.topInit, htopS] at hti
          obtain ⟨-, rfl, -⟩ := hti
          rcases List.mem_cons.mp hf with heq | hf₀
          · -- `f` is the freshly pushed frame: `t = l`, `p₁ = v`.
            injection heq with ht hp hκ
            rw [ht] at htC₁
            rw [hHl] at htC₁
            cases htC₁
            have hvℓ : v = Value.loc ℓ := hp.symm.trans hpℓ
            -- `G₁ = G`: both name the glob of `S`'s topmost init frame.
            have hG₁G : G₁ = G :=
              Option.some.inj
                ((htG i₀ (Frame.call l v E :: cfs₀) r₀
                    (by simp [Stack.topInit, htopS])).symm.trans (hG i₀ cfs₀ r₀ htopS))
            rw [hG₁G]
            have hAS : ArgSound G σ L H S
                (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val v))) :=
              harg G i₀ cfs₀ r₀ htopS hG
            obtain ⟨-, -, hbound⟩ := ArgSound.of_plug E hAS
            exact hbound _ _ .val .val (G, C)
              (by simp [Heap.opOf, hHl]) (by simp [Heap.opOf, hvℓ, hHD])
          · -- `f` sits in `cfs₀`, below the new frame: reroute through
            -- `hparam` at the suffix `S`.
            have hTopS : Stack.TopInit S G₁ := by
              intro i' cfs' r' htop'
              exact htG i' (Frame.call l v E :: cfs') r' (by simp [Stack.topInit, htop'])
            exact hparam S i₀ cfs₀ r₀ t p₁ κ G₁ C₁ (List.suffix_refl S) htopS hTopS
              hf₀ htC₁ ℓ hpℓ D hHD
      · exact hparam S' i cfs r t p₁ κ G₁ C₁ hsub hti htG hf htC₁ ℓ hpℓ D hHD
    · -- FldInv
      intro S' g ℓᵢ C vₐ vₐb hsub hti hlc i ℓ' hcil
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · -- The heap is unchanged, and `topInit` looks through the new call
        -- frame, so this is exactly the `hfld` instance at the suffix `S`.
        refine hfld S g ℓᵢ C vₐ vₐb (List.suffix_refl S) ?_ hlc i ℓ' hcil
        intro i' cfs' r' htop
        exact hti i' (Frame.call l v E :: cfs') r' (by simp [Stack.topInit, htop])
      · exact hfld S' g ℓᵢ C vₐ vₐb hsub hti hlc i ℓ' hcil
    · -- RetInv: the new focus is the callee body `eₐ`, and the new top call
      -- frame is the freshly pushed one (receiver `l`, a `C`-instance), so
      -- the obligation is `K ⊆ σ.Ret G C`.  `KJR.to_kjc` covers the runtime
      -- K-set by the static `KJ G C` one (its `hthis`/`hparam` hypotheses
      -- are the fresh frame's bounds, `hbridge`), which `ret_init` bounds by
      -- `σ.Ret G C`.
      intro G' i' cfs' r' hti' htiG t p k htc D htd K hK
      obtain ⟨i₀, cfs₀, r₀, htopS, rfl⟩ := hpin G' i' cfs' r' hti' htiG
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      obtain ⟨K', hK', hsub⟩ :=
        KJR.to_kjc (c := some C) hthisB hparamB (fun hc => nomatch hc) hbvf hK
      -- The fresh frame is the top call frame, so `t = l` and `D` is the
      -- `C`-instance at `l`.
      simp only [Stack.push, Stack.topCall, Option.some.injEq, Frame.call.injEq] at htc
      obtain ⟨rfl, -, -⟩ := htc
      rw [hHl] at htd
      cases htd
      exact hsub.trans (hσ.ret_init hbody hK')
    · -- ArgInv: the new focus is the callee body `eₐ` — method-body code in
      -- class context `C`, reachable via `RE.body` (`C ∈ σ.RM G` is
      -- `CallSound` at the redex, `hfresh`) — so the context-generalized
      -- `ArgSound.of_re` applies, with the fresh frame's bounds (`hbridge`)
      -- interpreting `this`/`param`.
      intro G' i' cfs' r' hti' htiG
      obtain ⟨i₀, cfs₀, r₀, htopS, rfl⟩ := hpin G' i' cfs' r' hti' htiG
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      obtain ⟨-, -, hRM⟩ := hfresh i₀ cfs₀ r₀ htopS
      exact ArgSound.of_re hσ hthisB hparamB eₐ (RE.body hRM hbody)
        (fun hc => nomatch hc) hbvf
    · -- CallInv: the callee body's `Calls` set lies in `σ.RM G` (`rm_closed`
      -- at `C ∈ σ.RM G`), and `CallSound.of_calls` covers its runtime K-sets
      -- through the fresh frame's bounds (`hbridge`).
      intro G' i' cfs' r' hti' htiG
      obtain ⟨i₀, cfs₀, r₀, htopS, hG'G⟩ := hpin G' i' cfs' r' hti' htiG
      rw [hG'G]
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      obtain ⟨-, -, hRM⟩ := hfresh i₀ cfs₀ r₀ htopS
      obtain ⟨Kc, hcalls⟩ := Calls.total (G := G) (C := C) (σ := σ) (L := L) eₐ
      exact CallSound.of_calls hthisB hparamB hcalls
        (hσ.rm_closed hRM hbody hcalls) hbvf
    · -- RMInv
      intro S' i cfs r f G' l₁ hsub hti htiG' hf hfl₁
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · -- `topInit` looks through the pushed call frame, so the topmost init
        -- frame of the new stack is `S`'s own.
        have hTopS : Stack.TopInit S G' := by
          intro i' cfs' r' htop'
          exact htiG' i' (Frame.call l v E :: cfs') r' (by simp [Stack.topInit, htop'])
        -- Decompose the new stack's `topInit`: `cfs` is the pushed frame on
        -- top of `S`'s own call-frame list `cfs₀`.
        cases htopS : S.topInit with
        | none => simp [Stack.topInit, htopS] at hti
        | some x =>
          obtain ⟨i₀, cfs₀, r₀⟩ := x
          simp [Stack.topInit, htopS] at hti
          obtain ⟨-, rfl, -⟩ := hti
          rcases List.mem_cons.mp hf with rfl | hf₀
          · -- `f` is the freshly pushed frame: its receiver is `l`, whose
            -- object is the `C`-instance `hHl`, and `G' = G` since both name
            -- the glob of `S`'s topmost init frame.  `C ∈ σ.RM G` is the
            -- runtime calls bound `CallInv` read off at the redex: the
            -- function position's runtime K-set is `{(G, C)}` (`KJR.val` via
            -- `hHl`), whose classes `CallSound` puts inside `σ.RM G`.
            have hG'G : G' = G :=
              Option.some.inj ((hTopS _ _ _ htopS).symm.trans (hG _ _ _ htopS))
            subst hG'G
            simp [Frame.loc] at hfl₁
            subst hfl₁
            refine ⟨_, hHl, ?_⟩
            obtain ⟨-, -, hbound⟩ :=
              CallSound.of_plug E (hcall _ i₀ cfs₀ r₀ htopS hG)
            exact hbound _ .val (mem_classes.mpr ⟨G', by simp [Heap.opOf, hHl]⟩)
          · -- `f` sits in `cfs₀`, below the new frame: reroute through `hrm`
            -- at the suffix `S`.
            exact hrm S i₀ cfs₀ r₀ f G' l₁ (List.suffix_refl S) htopS hTopS hf₀ hfl₁
      · exact hrm S' i cfs r f G' l₁ hsub hti htiG' hf hfl₁
    · -- ThisInv: only the freshly pushed frame is new; its receiver bound
      -- `G ∈ σ.This G C` is `ThisSound` read off at the redex (`hfresh`),
      -- mirroring how `ParamInv` reads off `ArgSound` above.
      intro S' i cfs r t p₁ κ G₁ hsub hti htG hf D hHD
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · cases htopS : S.topInit with
        | none => simp [Stack.topInit, htopS] at hti
        | some x =>
          obtain ⟨i₀, cfs₀, r₀⟩ := x
          simp [Stack.topInit, htopS] at hti
          obtain ⟨-, rfl, -⟩ := hti
          rcases List.mem_cons.mp hf with heq | hf₀
          · -- `f` is the freshly pushed frame: `t = l`, a `(G, C)`-instance.
            injection heq with ht hp hκ
            rw [ht] at hHD
            rw [hHl] at hHD
            cases hHD
            have hG₁G : G₁ = G :=
              Option.some.inj
                ((htG i₀ (Frame.call l v E :: cfs₀) r₀
                    (by simp [Stack.topInit, htopS])).symm.trans (hG i₀ cfs₀ r₀ htopS))
            rw [hG₁G]
            obtain ⟨hGthis, -, -⟩ := hfresh i₀ cfs₀ r₀ htopS
            exact hGthis
          · -- `f` sits in `cfs₀`, below the new frame: reroute through
            -- `hthisinv` at the suffix `S`.
            have hTopS : Stack.TopInit S G₁ := by
              intro i' cfs' r' htop'
              exact htG i' (Frame.call l v E :: cfs') r' (by simp [Stack.topInit, htop'])
            exact hthisinv S i₀ cfs₀ r₀ t p₁ κ G₁ (List.suffix_refl S) htopS hTopS
              hf₀ D hHD
      · exact hthisinv S' i cfs r t p₁ κ G₁ hsub hti htG hf D hHD
    · -- ThisSoundInv: the callee body is reachable method-body code
      -- (`RE.body`), so the context-generalized `ThisSound.of_re` applies
      -- with the fresh frame's bounds (`hbridge`).
      intro G' i' cfs' r' hti' htiG
      obtain ⟨i₀, cfs₀, r₀, htopS, rfl⟩ := hpin G' i' cfs' r' hti' htiG
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      obtain ⟨-, -, hRM⟩ := hfresh i₀ cfs₀ r₀ htopS
      exact ThisSound.of_re hσ hthisB hparamB eₐ (RE.body hRM hbody)
        (fun hc => nomatch hc) hbvf
    · -- FrameInv
      intro S' t p E₁ hsub G' i  cfs r hS'ti hS'tiG' redex
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · -- The frame is the freshly pushed one: `t = l`, `p = v`, `E₁ = E`,
        -- `S' = S`, so `E₁.plug redex` is exactly the pre-state focus and the
        -- four obligations are the redex-focus invariants `hret`/`harg`/
        -- `hcall`/`hts`, instantiated at the ambient `G'`.
        injection heq with hf hS
        injection hf with ht hp hE
        subst ht; subst hp; subst hE; subst hS
        exact ⟨hret G' i cfs r hS'ti hS'tiG',
               harg G' i cfs r hS'ti hS'tiG',
               hcall G' i cfs r hS'ti hS'tiG',
               hts G' i cfs r hS'ti hS'tiG'⟩
      · -- The frame sits inside `S`: reroute through `hframe`.
        exact hframe S' t p E₁ hsub' G' i cfs r hS'ti hS'tiG'

theorem inv_step_ret {σ : Sigma} {L : Program} {G Gₒ : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {eₐ : Expr} {l : Loc} {v v₁ v₂ p : Value}
    {C : ClassName} (_hσ : FixPoint σ L) (_hG : Stack.TopInit S G) (hHl : H l = some (ClsIns.mk C Gₒ v₁ v₂))
    (_hbody : Program.HasClass L C eₐ) (_hbvf : ValueFree eₐ)
    (hinv : Inv σ L (.mk H Γ ((Frame.call l p E)::S) (Expr.val v))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe⟩ := hinv
    -- Covering, shared by the Ret/Arg/Call/ThisSound cases below: under `S`'s
    -- topInit guard, every K-set of the returned value lies inside a K-set of
    -- the popped frame's redex `l(p)`.  The bound `H.opOf v ⊆ σ.Ret G' C` is
    -- the pre-state `hret` at the popped frame (the pre-stack's top call
    -- frame, receiver `l` a `C`-instance), and `KJR.app KJR.val` reproduces
    -- it as the redex's K-set, the union over the singleton `{(Gₒ, C)}`.
    have hcov : ∀ G' i cfs r, S.topInit = some (i, cfs, r) →
        Stack.TopInit S G' → ∀ K, KJR G' σ L H S (Expr.val v) K →
          ∃ K', KJR G' σ L H S
            (Expr.app (Expr.val (Value.loc l)) (Expr.val p)) K' ∧ K ⊆ K' := by
      intro G' i cfs r hti htiG'
      -- Guards lifted to the pre-state stack: its topmost init frame is `S`'s
      -- own, with the popped frame prepended to the call-frame list.
      have htiPre : Stack.topInit ((Frame.call l p E)::S)
          = some (i, Frame.call l p E :: cfs, r) := by
        simp [Stack.topInit, hti]
      have htiGPre : Stack.TopInit ((Frame.call l p E)::S) G' := by
        intro i' cfs' r' htop'
        simp [htiPre] at htop'
        obtain ⟨rfl, -, -⟩ := htop'
        exact htiG' i cfs r hti
      have hval : H.opOf v ⊆ σ.Ret G' C :=
        hret G' i (Frame.call l p E :: cfs) r htiPre htiGPre l p E rfl
          (ClsIns.mk C Gₒ v₁ v₂) hHl (H.opOf v) KJR.val
      have hmem : (Gₒ, C) ∈ H.opOf (Value.loc l) := by simp [Heap.opOf, hHl]
      intro K hK
      cases hK
      exact ⟨_, KJR.app KJR.val, fun x hx => Set.mem_biUnion hmem (hval hx)⟩
    refine ⟨?_, ?_, hgtable, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G' C' hsub hti htiG' hfc htc' l hpl
      exact hparam S' i cfs r t p κ G' C' (hsub.trans (List.suffix_cons _ _)) hti htiG' hfc htc' l hpl
    · -- FldInv
      intro S' G' l C' v₁' v₂' hsub htiG' hHlC' i l' hil
      exact hfld S' G' l C' v₁' v₂' (hsub.trans (List.suffix_cons _ _)) htiG' hHlC' i l' hil
    · -- RetInv: the resumed focus `E.plug (val v)` against the next call
      -- frame down.  `FrameInv` at the popped frame bounds the K-sets of the
      -- push-time focus `E.plug (l(p))` over `S`, and `KJR.plug_mono`
      -- transports the value covering `hcov` through `E`.
      intro G' i cfs r hti htiG' t' p' κ' htc D htD
      obtain ⟨hKbound, -, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      intro K hK
      obtain ⟨K', hK', hsubK⟩ :=
        KJR.plug_mono (hcov G' i cfs r hti htiG') E K hK
      exact hsubK.trans (hKbound t' p' κ' htc D htD K' hK')
    · -- ArgInv: `FrameInv`'s second conjunct is `ArgSound` of the push-time
      -- focus over `S`; `ArgSound.plug_mono` transports it through the value
      -- covering (`ArgSound` of the bare value is `True`).
      intro G' i cfs r hti htiG'
      obtain ⟨-, hargF, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hAS : ArgSound G' σ L H S (Expr.val v) := trivial
      exact ArgSound.plug_mono hAS (hcov G' i cfs r hti htiG') E hargF
    · -- CallInv
      intro G' i cfs r hti htiG'
      obtain ⟨-, -, hcallF, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hCS : CallSound G' σ L H S (Expr.val v) := trivial
      exact CallSound.plug_mono hCS (hcov G' i cfs r hti htiG') E hcallF
    · -- RMInv
      intro S' i cfs r f G' l hsub hti htiG' hf hfl
      exact hrm S' i cfs r f G' l (hsub.trans (List.suffix_cons _ _)) hti htiG' hf hfl
    · -- ThisInv: the stack only shrank; reroute through the pre-state's
      -- `ThisInv` at the suffix.
      intro S' i cfs r t p κ G₁ hsub hti htiG₁ hf D hHt
      exact hthisinv S' i cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
        hti htiG₁ hf D hHt
    · -- ThisSoundInv: same stack-chain gap as `ArgInv`/`CallInv` above, for
      -- `ThisSound` of the stored context.
      intro G' i cfs r hti htiG'
      obtain ⟨-, -, -, htF⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hTS : ThisSound G' σ L H S (Expr.val v) := trivial
      exact ThisSound.plug_mono hTS (hcov G' i cfs r hti htiG') E htF
    · -- FrameInv: the stack only shrank, so every call frame of `S` is a
      -- call frame of the pre-state stack, with the same stack below it;
      -- reroute through `hframe` at the extended suffix.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG'
      exact hframe S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
        G' i cfs r hS'ti hS'tiG'

theorem inv_step_alloc {σ : Sigma} {e₁ e₂ eₐ : Expr} {G : GlobName} {L : Program} {v₁ v₂ : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} {l : Loc} {C: ClassName}
    (htG : Stack.TopInit S G) (_hσ : FixPoint σ L)
    (hHl : H l = none) (_hbody : Program.HasClass L C eₐ) (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.newC C v₁ v₂))))
    : Inv σ L (.mk (Heap.update H l (ClsIns.mk C G v₁ v₂)) Γ S (E.plug (Expr.val (Value.loc l)))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv: the stack is unchanged and the heap only grew at the fresh
      -- `l`.  The receiver `t` is allocated in the old heap (`hrm`), so the
      -- update is invisible to it; an argument location `ℓ ≠ l` is handled by
      -- the old `hparam`.
      intro S' i' cfs r t p κ G' C' hsub hti htiG' hfc hHt ℓ hpℓ D hHD
      obtain ⟨Ct, hHt₀, -⟩ :=
        hrm S' i' cfs r (Frame.call t p κ) G' t hsub hti htiG' hfc rfl
      have htl : t ≠ l := by
        intro h; rw [h, hHl] at hHt₀; simp at hHt₀
      have hHt' : H t = some C' := by simpa [Heap.update, htl] using hHt
      by_cases hℓl : ℓ = l
      · -- `ℓ = l`: a frame argument that was *dangling* in the old heap got
        -- caught by the fresh allocation, and nothing bounds the new object's
        -- owner pair by `σ.Param G' C'.cls`.  Ruled out semantically because
        -- reachable configurations contain no dangling locations, but `Inv`
        -- carries no such closedness component yet — the same gap as (ii) in
        -- the `RetInv` case below.
        sorry
      · have hHD' : H ℓ = some D := by simpa [Heap.update, hℓl] using hHD
        exact hparam S' i' cfs r t p κ G' C' hsub hti htiG' hfc hHt' ℓ hpℓ D hHD'
    · -- FldInv
      intro S' G' l' C' v₁' v₂' hsub htiG' hHl' j ℓ' hfj
      by_cases hl' : l' = l
      · -- `l' = l` is the freshly allocated object: `C' = C`, `G' = G`, and its
        -- fields are the redex arguments `v₁ v₂`.  Missing: their classes lie
        -- in `σ.Fld j G C` — needs `hσ.fld_re` at the reachable `new C(e₁,e₂)`
        -- plus a runtime K-judgment bound on the already-reduced arguments.
        subst hl'
        simp [Heap.update] at hHl'
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hHl'
        sorry
      · -- `l' ≠ l`: an old object, so its fields are old-heap locations
        -- (`hfld`), which are distinct from the fresh `l`.
        have hHl'' : H l' = some (ClsIns.mk C' G' v₁' v₂') := by
          simpa [Heap.update, hl'] using hHl'
        obtain ⟨c', hc', hcls⟩ := hfld S' G' l' C' v₁' v₂' hsub htiG' hHl'' j ℓ' hfj
        have hℓ'l : ℓ' ≠ l := by
          intro h; rw [h, hHl] at hc'; simp at hc'
        exact ⟨c', by simpa [Heap.update, hℓ'l] using hc', hcls⟩
    · -- GTableInv: `Γ` is unchanged, and every field location it mentions is
      -- allocated in the old heap (`hgtable`), hence distinct from the fresh `l`.
      intro g o hg j ℓ' hoj
      obtain ⟨c', hc', hcls⟩ := hgtable g o hg j ℓ' hoj
      have hℓ'l : ℓ' ≠ l := by
        intro h; rw [h, hHl] at hc'; simp at hc'
      exact ⟨c', by simpa [Heap.update, hℓ'l] using hc', hcls⟩
    · -- RetInv: two gaps block the covering argument here.  (i) The
      -- contractum's runtime pair is the heap-recorded `(G, C)`, while the
      -- redex's `KJR.newC` pair is `(G₀, C)` for the *ambient* global `G₀` —
      -- they agree only when the stack pins the ambient global (`TopInit` is
      -- vacuous on init-frame-less stacks).  (ii) `KJR` over the grown heap
      -- `H[l ↦ …]` can exceed `KJR` over `H` at a dangling `loc l` already
      -- sitting in `E` (no closedness component in `Inv`).  Both need new
      -- invariant components.
      sorry
    · -- ArgInv: the covering at the redex holds over the new heap (the
      -- contractum's `H[l ↦ …].opOf (loc l) = {(G, C)}` matches `KJR.newC`'s
      -- `{(G₀, C)}` once the topmost init frame pins the ambient `G₀ = G`),
      -- but transporting the *old* focus's `ArgSound` to the grown heap hits
      -- gap (ii) above: a dangling `loc l` elsewhere in the focus may enlarge
      -- its K-sets.  Needs the closedness component.
      sorry
    · -- CallInv: same as ArgInv — the contractum's covering holds, but
      -- transporting the old focus's `CallSound` to the grown heap hits
      -- gap (ii) above.  Needs the closedness component.
      sorry
    · -- RMInv: the stack is unchanged and every receiver it mentions is
      -- allocated in the old heap (`hrm`), hence distinct from the fresh `l`.
      intro S' i' cfs r f G' l₁ hsub hti htiG' hf hfl₁
      obtain ⟨C₀, hC₀, hcls⟩ := hrm S' i' cfs r f G' l₁ hsub hti htiG' hf hfl₁
      have hl₁l : l₁ ≠ l := by
        intro h; rw [h, hHl] at hC₀; simp at hC₀
      exact ⟨C₀, by simpa [Heap.update, hl₁l] using hC₀, hcls⟩
    · -- ThisInv: the stack is unchanged and every receiver it mentions is
      -- allocated in the old heap (`hrm`), so the update at the fresh `l` is
      -- invisible.
      intro S' i' cfs r t p κ G₁ hsub hti htiG₁ hfc D hHt
      obtain ⟨Ct, hHt₀, -⟩ :=
        hrm S' i' cfs r (Frame.call t p κ) G₁ t hsub hti htiG₁ hfc rfl
      have htl : t ≠ l := by
        intro h; rw [h, hHl] at hHt₀; simp at hHt₀
      have hHt' : H t = some D := by simpa [Heap.update, htl] using hHt
      exact hthisinv S' i' cfs r t p κ G₁ hsub hti htiG₁ hfc D hHt'
    · -- ThisSoundInv: same as `ArgInv` — transporting the old focus's
      -- `ThisSound` to the grown heap hits gap (ii) above.  Needs the
      -- closedness component.
      sorry
    · -- FrameInv
      sorry

theorem inv_step_ipush {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} (hnewG : Γ G = none) (hσ : FixPoint σ L)
    (hG : Program.HasObject L G e₁ e₂)
    (hpf₁ : ContextFree e₁) (hvf₁ : ValueFree e₁) (hpf₂ : ContextFree e₂)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G i))))
    : Inv σ L (.mk H Γ[G↦ ⟨none, none⟩] ((Frame.init1 G e₂ (E.plug (Expr.gproj G i))) :: S) e₁) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv: rcases htop rfl tells us there are no call frames above the new init frame, so vacuous
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases htop with ⟨_, rfl, _⟩
        simp at hcall
      · exact hparam S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
    · -- FldInv: TO FIX
      intro S' G₁ l C v₁ v₂ hsub hti hHl i ℓ' hf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · have hfld' := hfld [] G₁ l C v₁ v₂ (by simp) (by
            intro i cfs r htop
            simp [Stack.topInit] at htop) hHl
        exact hfld' i ℓ' hf
      · exact hfld S' G₁ l C v₁ v₂ hsub hti hHl i ℓ' hf
    · -- GTableInv
      intro g o HGo i ℓ' hi
      by_cases hEq : g = G
      · subst hEq
        have HGo' : some ⟨none, none⟩ = some o := by
          simpa [GTable.update] using HGo
        cases HGo'
        cases i <;> simp [GEntry.field] at hi
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ i ℓ' hi
    · -- RetInv: the pushed `init1` frame hides any call frame, so `topCall`
      -- is `none` and the obligation is vacuous.
      intro G₀ i' cfs' r' hti' hTop t p κ htc
      simp [Stack.topCall] at htc
    · -- ArgInv: the topmost init frame is now `G`'s own, pinning the ambient
      -- global to `G`, and the new focus is `G`'s first initializer —
      -- reachable (`RE.init₁`) initializer code, so `ArgSound.of_re` applies
      -- at the empty context (the stack-consulting hypotheses are vacuous).
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      exact ArgSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₁ (RE.init₁ hG) (fun _ => hpf₁) hvf₁
    · -- CallInv: the topmost init frame is now `G`'s own, pinning the ambient
      -- global to `G`, and the new focus is `G`'s first initializer, whose
      -- `Calls0` set `rm_init` puts inside `σ.RM G` — `CallSound.of_calls0`.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      obtain ⟨K₁, hc₁⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₁ hpf₁
      obtain ⟨K₂, hc₂⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₂ hpf₂
      exact CallSound.of_calls0 hc₁
        (Set.subset_union_left.trans (hσ.rm_init hG hc₁ hc₂)) hpf₁ hvf₁
    · -- RMInv
      intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hf
      · exact hrm S' i cfs r f G₁ l hsub hti hG₁ hf hfl
    · -- ThisInv: the pushed `init1` frame carries no call frames above it,
      -- and the suffixes of `S` are rerouted through the pre-state.
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf D hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hcf
      · exact hthisinv S' i' cfs r t p κ G₁ hsub hti hTopG hcf D hHt
    · -- ThisSoundInv: the new focus is `G`'s first initializer — reachable
      -- (`RE.init₁`) initializer code, so `ThisSound.of_re` applies at the
      -- empty context.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      exact ThisSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₁ (RE.init₁ hG) (fun _ => hpf₁) hvf₁
    · -- FrameInv: the pushed `init1` frame is not a call frame, so the
      -- suffix's `Frame.call` head can only sit inside `S`; reroute through
      -- `hframe`.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG' redex
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · -- The head would have to be the pushed `init1` frame — constructor
        -- clash, so this branch is vacuous.
        injection heq with hf hS
        exact absurd hf (by simp)
      · -- The frame sits inside `S`: reroute through `hframe`.
        exact hframe S' t' p' E₁ hsub' G' i cfs r hS'ti hS'tiG'

theorem inv_step_inext {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program} {v : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} (hnewG : Γ G = none) (_hσ : FixPoint σ L)
    (hG : Program.HasObject L G e₁ e₂)
    (hpf₂ : ContextFree e₂) (hvf₂ : ValueFree e₂) (hpf₁ : ContextFree e₁)
    (hinv : Inv σ L (.mk H Γ ((Frame.init1 G e₂ (E.plug (Expr.gproj G i))) :: S) (Expr.val v)))
    : Inv σ L (.mk H Γ[G↦ ⟨v, none⟩] ((Frame.init2 G (E.plug (Expr.gproj G i))) :: S) e₂) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases htop with ⟨_, rfl, _⟩
        simp at hcall
      · exact hparam S' i cfs r t p κ G₁ C (hsub.trans (List.suffix_cons _ _)) htop hTopG hcall hHt
    · -- FldInv: TO FIX
      intro S' G₁ l C v₁ v₂ hsub hti hHl i ℓ' hf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · have hfld' := hfld [] G₁ l C v₁ v₂ (by simp) (by
            intro i cfs r htop
            simp [Stack.topInit] at htop) hHl
        exact hfld' i ℓ' hf
      · exact hfld S' G₁ l C v₁ v₂ (hsub.trans (List.suffix_cons _ _)) hti hHl i ℓ' hf
    · -- GTableInv
      intro g o HGo i ℓ' hi
      by_cases hEq : g = G
      · subst hEq
        have HGo' : some (⟨v, none⟩ : GEntry) = some o := by
          simpa [GTable.update] using HGo
        cases HGo'
        cases i with
        | one =>
          -- need another Inv focusing on init expressions. If Γ G = some o,
          -- topInit is G init1 e_2, focus is e_1, then e_1 is in GFld G
          -- or topInit is G init2, focus is e_2, then e_2 is in GFld G
          sorry
        | two => simp [GEntry.field] at hi
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ i ℓ' hi
    · -- RetInv: the `init2` frame hides any call frame, so `topCall` is
      -- `none` and the obligation is vacuous.
      intro G₀ i' cfs' r' hti' hTop t p κ htc
      simp [Stack.topCall] at htc
    · -- ArgInv: the topmost init frame is still `G`'s own, and the new focus
      -- is `G`'s second initializer — reachable (`RE.init₂`) initializer
      -- code, so `ArgSound.of_re` applies at the empty context.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      exact ArgSound.of_re (c := none) _hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₂ (RE.init₂ hG) (fun _ => hpf₂) hvf₂
    · -- CallInv: the topmost init frame is still `G`'s own, and the new focus
      -- is `G`'s second initializer, whose `Calls0` set `rm_init` puts inside
      -- `σ.RM G` — `CallSound.of_calls0`.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      obtain ⟨K₁, hc₁⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₁ hpf₁
      obtain ⟨K₂, hc₂⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₂ hpf₂
      exact CallSound.of_calls0 hc₂
        (Set.subset_union_right.trans (_hσ.rm_init hG hc₁ hc₂)) hpf₂ hvf₂
    · -- RMInv: No call frames
      intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hf
      · exact hrm S' i cfs r f G₁ l (hsub.trans (List.suffix_cons _ _)) hti hG₁ hf hfl
    · -- ThisInv: the pushed `init2` frame carries no call frames above it,
      -- and the suffixes of `S` are rerouted through the pre-state (whose
      -- stack extends `S` by the popped `init1` frame).
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf D hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hcf
      · exact hthisinv S' i' cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
          hti hTopG hcf D hHt
    · -- ThisSoundInv: the new focus is `G`'s second initializer — reachable
      -- (`RE.init₂`) initializer code, so `ThisSound.of_re` applies at the
      -- empty context.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      exact ThisSound.of_re (c := none) _hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₂ (RE.init₂ hG) (fun _ => hpf₂) hvf₂
    · -- FrameInv: the pushed `init2` frame is not a call frame, so the
      -- suffix's `Frame.call` head can only sit inside `S`, itself a suffix
      -- of the pre-state stack; reroute through `hframe`.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG' redex
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · injection heq with hf hS
        exact absurd hf (by simp)
      · exact hframe S' t' p' E₁ (hsub'.trans (List.suffix_cons _ _))
          G' i cfs r hS'ti hS'tiG'

theorem inv_step_ipop {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program} {v₁ v₂ : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} (hnewG : Γ G = none) (_hσ : FixPoint σ L)
    (hG : Program.HasObject L G e₁ e₂) (hinv : Inv σ L (.mk H Γ[G↦ ⟨v₁, none⟩] ((Frame.init2 G (E.plug (Expr.gproj G i))) :: S) e₂))
    : Inv σ L (.mk H Γ[G↦ ⟨v₁, v₂⟩] S (E.plug (Expr.gproj G i))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      exact hparam S' i cfs r t p κ G₁ C (hsub.trans (List.suffix_cons _ _)) htop hTopG hcall hHt
    · -- FldInv
      intro S' G₁ l C v₁ v₂ hsub hti hHl i ℓ' hf
      exact hfld S' G₁ l C v₁ v₂ (hsub.trans (List.suffix_cons _ _)) hti hHl i ℓ' hf
    · -- GTableInv
      intro g o HGo i ℓ' hi
      by_cases hEq : g = G
      · subst hEq
        have HGo' : some (⟨v₁, v₂⟩ : GEntry) = some o := by
          simpa [GTable.update] using HGo
        cases HGo'
        cases i with
        | one =>
          -- `v₁` was already recorded in the pre-state entry `G(v₁, ⊥)`, so
          -- this is the old `hgtable` instance at `G`.
          exact hgtable g ⟨v₁, none⟩ (by simp [GTable.update]) Idx.one ℓ'
            (by simpa [GEntry.field] using hi)
        | two =>
          -- `v₂` is the value just computed by `e₂`: its class must lie in
          -- `σ.GFld two G` (`hσ.gfld_init`), which needs the runtime bound
          -- linking the reduced value's class to `KJ0 e₂` (`k_abstracts`) —
          -- the init-frame analogue of `RetInv`, not yet formalised.
          sorry
      · have hΓ : Γ[G↦ ⟨v₁, none⟩] g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ i ℓ' hi
    · -- RetInv: the resumed focus `E.plug (G.i)` must be K-bounded against
      -- the call frame that `S` exposes after the pop — continuation
      -- information that the pre-state's `RetInv` (vacuous under the `init2`
      -- frame) does not carry.  Same stack-chain typing gap as E-Ret.
      sorry
    · -- ArgInv: same stack-chain gap — the resumed context `E` was stored in
      -- the popped `init2` frame, and its `ArgSound` w.r.t. `S` (whose
      -- topmost init frame differs from the popped one) is not recorded by
      -- any `Inv` component.
      sorry
    · -- CallInv: same stack-chain gap, for `CallSound` of the stored context.
      sorry
    · intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      exact hrm S' i cfs r f G₁ l (hsub.trans (List.suffix_cons _ _)) hti hG₁ hf hfl
    · -- ThisInv: the stack only shrank; reroute through the pre-state's
      -- `ThisInv` at the suffix.
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf D hHt
      exact hthisinv S' i' cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
        hti hTopG hcf D hHt
    · -- ThisSoundInv: same stack-chain gap as `ArgInv`/`CallInv` above, for
      -- `ThisSound` of the stored context.
      sorry
    · -- FrameInv: the stack only shrank (the `init2` frame was popped), so
      -- every call frame of `S` is a call frame of the pre-state stack, with
      -- the same stack below it; reroute through `hframe`.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG'
      exact hframe S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
        G' i cfs r hS'ti hS'tiG'

end Proof
