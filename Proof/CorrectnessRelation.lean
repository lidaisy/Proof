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

/-! ### Focus closedness

  Every `Value.loc ℓ` occurring syntactically in the focus points to an
  allocated object.  This is the structural, `KJR`-free companion of
  `ArgSound`/`CallSound`/`ThisSound`: because it never consults `KJR`, its
  `plug_mono` needs no K-set covering hypothesis (only that the contractum is
  itself closed), and its `of_re` analogue collapses to value-freeness
  (reachable program code mentions no runtime locations).  It is the missing
  ingredient behind the `inv_step_alloc` gap-(ii) sorries: on a closed focus a
  fresh allocation `H[l ↦ …]` (with `H l = none`) leaves every `KJR` K-set
  unchanged, because `loc l` cannot occur in the focus. -/

/-- `Closed H e`: every location mentioned in `e` is allocated in `H`.  Boolean
    values, `this`/`param`, and `G.i` mention no location and are vacuously
    closed (the `_` arm). -/
def Closed (H : Heap) : Expr → Prop
  | Expr.val (Value.loc ℓ) => (H ℓ).isSome
  | Expr.newC _ e₁ e₂      => Closed H e₁ ∧ Closed H e₂
  | Expr.app e₁ e₂         => Closed H e₁ ∧ Closed H e₂
  | Expr.proj e _          => Closed H e
  | _                      => True

/-- `Closed` restricts to the expression sitting in the hole of an evaluation
    context (the analogue of `ArgSound.of_plug`). -/
theorem Closed.of_plug {H : Heap} :
    ∀ (E : ECtx) {e : Expr}, Closed H (E.plug e) → Closed H e
  | .hole, _, h => h
  | .projc E _, _, h => Closed.of_plug E h
  | .appL E _, _, h => Closed.of_plug E h.1
  | .appR _ E, _, h => Closed.of_plug E h.2
  | .newL _ E _, _, h => Closed.of_plug E h.1
  | .newR _ _ E, _, h => Closed.of_plug E h.2

/-- Plug monotonicity of `Closed` (the analogue of `ArgSound.plug_mono`).
    Because `Closed` is purely syntactic — unlike the `KJR`-consulting soundness
    predicates — transporting it across a redex→contractum rewrite needs no
    K-set covering hypothesis: the surrounding context's locations stay closed
    (read off the `eᵣ`-plug) and the hole's are closed by `hx`. -/
theorem Closed.plug_mono {H : Heap} {eᵣ eₓ : Expr} (hx : Closed H eₓ) :
    ∀ (E : ECtx), Closed H (E.plug eᵣ) → Closed H (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => Closed.plug_mono hx E hr
  | .appL E _, hr => ⟨Closed.plug_mono hx E hr.1, hr.2⟩
  | .appR _ E, hr => ⟨hr.1, Closed.plug_mono hx E hr.2⟩
  | .newL _ E _, hr => ⟨Closed.plug_mono hx E hr.1, hr.2⟩
  | .newR _ _ E, hr => ⟨hr.1, Closed.plug_mono hx E hr.2⟩

/-- The `of_re` analogue for `Closed`.  Reachable program code mentions no
    runtime locations, so on value-free code closedness is immediate — no `RE`
    derivation or `this`/`param` bounds are needed (contrast `ArgSound.of_re`).
    This is what establishes `Closed` for the fresh focus at I-Push / I-Next /
    E-AppBeta, exactly where the other `of_re` lemmas fire. -/
theorem Closed.of_valueFree {H : Heap} : ∀ e, ValueFree e → Closed H e := by
  intro e
  induction e with
  | thisE => intro _; trivial
  | paramE => intro _; trivial
  | gproj G₀ i => intro _; trivial
  | val v => intro hvf; exact False.elim hvf
  | proj e i ih => intro hvf; exact ih hvf
  | newC C e₁ e₂ ih₁ ih₂ => intro hvf; exact ⟨ih₁ hvf.1, ih₂ hvf.2⟩
  | app e₁ e₂ ih₁ ih₂ => intro hvf; exact ⟨ih₁ hvf.1, ih₂ hvf.2⟩

theorem Closed.mono {H H' : Heap} (hHH' : ∀ ℓ o, H ℓ = some o → H' ℓ = some o) :
  ∀ {e}, Closed H e → Closed H' e := by
  intro e
  induction e with
  | thisE => intro h; trivial
  | paramE => intro _; trivial
  | gproj G₀ i => intro _; trivial
  | val v =>
    intro h
    cases v with
    | loc ℓ' =>
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
      show (H' ℓ').isSome
      rw [hHH' ℓ' o ho]
      rfl
    | _ => trivial
  | proj e i ih => intro h; exact ih h
  | newC C e₁ e₂ ih₁ ih₂ => intro h; exact ⟨ih₁ h.1, ih₂ h.2⟩
  | app e₁ e₂ ih₁ ih₂ => intro h; exact ⟨ih₁ h.1, ih₂ h.2⟩

/-! ### Heap/value typing -/

/-- Param soundness of the call stack: every call frame whose argument is a
    location `ℓ` has `ℓ` allocated, with that object's owner pair inside
    `σ.Param(G)(D)` for the receiver's class `D`.  (The conclusion *asserts*
    allocatedness — `∃ D, H ℓ = some D ∧ …` — rather than being conditional on
    it, so that reading it off at a suffix already supplies old-heap
    allocatedness.  The price is that a freshly pushed frame must establish its
    argument is allocated, which needs a focus-closedness component `Inv` still
    lacks; see the `sorry` in `inv_step_app`.) -/
def ParamInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G C, S' <:+ S → S'.topInit = some (i, cfs, r)
    → Stack.TopInit S' G → Frame.call t p κ ∈ cfs → H t = some C
      → ∀ ℓ, p = Value.loc ℓ → ∃ D, H ℓ = some D ∧ (D.g, D.cls) ∈ σ.Param G C.cls

/-- Heap typing (Fld soundness): for every allocated object `H ℓ = C(v₁, v₂)`
    and field index `i`, if that field holds a location `ℓ'` pointing to an
    allocated object `H ℓ' = C'(…)`, then `C'`'s owner pair lies in
    `σ.Fldᵢ((G, C))` — the owner-pair set the analysis `⇓ᴷ` predicts for the
    `i`-th field of a `C`-object owned by `G`.  Boolean values carry no class
    and are vacuously sound.  This is what makes `E-Proj` preserve `Inv`. -/
def FldInv (σ : Sigma) (H : Heap) (Γ: GTable) : Prop :=
  ∀ G l (C : ClassName) (v₁ v₂ : Value),
    H l = some (ClsIns.mk C G v₁ v₂) → (Γ G).isSome ∧
      ∀ i ℓ', (ClsIns.mk C G v₁ v₂).field i = Value.loc ℓ' →
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
    → ∀ t p κ, S.topCall = some (Frame.call t p κ) → ∃ D, H t = some D
      ∧ (∀ K, KJR G σ L H S e K → K ⊆ σ.Ret G D.cls)

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
    shaped like `ParamInv`): every call frame's receiver `t` is allocated, with
    its owner inside `σ.This G C` for the receiver's class `C` and the
    nearest init frame's global `G`.  Unlike `ParamInv`, allocatedness is free
    here — a call frame's receiver is always an allocated object. -/
def ThisInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G, S' <:+ S → S'.topInit = some (i, cfs, r)
    → Stack.TopInit S' G → Frame.call t p κ ∈ cfs
    → ∃ D, H t = some D ∧ D.g ∈ σ.This G D.cls

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

/-- Init-frame analogue of `RetInv`.  `RetInv` bounds the focus's K-sets by
    `σ.Ret` exactly when a method is executing (`S.topCall = some (call …)`);
    `GInitInv` bounds them by `σ.GFld` in the dual situation — when the topmost
    init frame sits directly on top, with *no* call frames above it (`cfs = []`),
    so the focus is the residual field initializer itself rather than method-body
    code.  Under a pushed call frame the `[]` guard is unsatisfiable, so the
    focus being a callee body (bounded by `Ret`, not `GFld`) is no obstruction. -/
def GInitInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G ifr r (hti : S.topInit = some (ifr, [], r)), Stack.TopInit S G →
    ∀ i, Frame.idx ifr (Stack.topInit_notCall hti) = i
      → ∀ K, KJR G σ L H S e K → K ⊆ σ.GFld i G

/-- Stack-chain typing: for every call frame `Frame.call t p E` in the stack,
    the push-time focus `E[t(p)]` — reconstructible from the frame's own
    fields — is Ret/Arg/Call/This-sound over the stack below the frame, and,
    dually to the `Ret` clause (which fires when a call frame is exposed),
    `GInit`-sound (`GFld`-bounded) whenever the stack below exposes its init
    frame directly (`cfs = []`) — this is what re-establishes `GInitInv` for the
    resumed focus `E[v]` when a method call inside an initializer returns. -/
def FrameInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ (S': Stack) t p E, (Frame.call t p E) :: S' <:+ S →
    ∀ G i cfs r, (hS'ti : S'.topInit = some (i, cfs, r)) → Stack.TopInit S' G →
      let redex := Expr.app (Expr.val (Value.loc t)) (Expr.val p)
      (∀ t' p' κ', S'.topCall = some (Frame.call t' p' κ') →
        ∃ D', H t' = some D' ∧
          ∀ K, KJR G σ L H S' (E.plug redex) K → K ⊆ σ.Ret G D'.cls)
      ∧ ArgSound G σ L H S' (E.plug redex)
      ∧ CallSound G σ L H S' (E.plug redex)
      ∧ ThisSound G σ L H S' (E.plug redex)
      ∧ GInitInv σ L H S' (E.plug redex)

/-- Init-frame stack chain (the init-frame dual of `FrameInv`).  The
    continuation `k` stored in every init frame — `init1 G e₂ k` or `init2 G k`
    — is `GInit`-sound (`GFld`-bounded) over the stack `S'` sitting directly
    below that frame.  `FrameInv` records this for the continuation stored in a
    *call* frame; `InitFrameInv` records it for the continuation stored in an
    *init* frame.  The continuation is threaded unchanged through
    `I-Push → I-Next → I-Pop`: it is seeded at `I-Push` from the pre-state's
    `GInitInv` (`k` is then the resumption `E[G.i]` running over `S'`), carried
    across `I-Next`, and *consumed* at `I-Pop`, where popping the `init2 G`
    frame resumes `k` over `S'` and this component re-establishes `GInitInv`
    for it. -/
def InitFrameInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) G k,
    ((∃ e, Frame.init1 G e k :: S' <:+ S) ∨ Frame.init2 G k :: S' <:+ S)
      → GInitInv σ L H S' k

/-- Closedness of every stored continuation.  For each call frame
    `Frame.call t p E` on the stack, the push-time focus `E[t(p)]` is `Closed`
    (every location it mentions is allocated).  Unlike `FrameInv`'s soundness
    clauses this carries *no* init-frame guard: closedness of the resumed focus
    `E[v]` is required at every `E-Ret`, whether or not an init frame is present.
    It is seeded at `E-AppBeta` from the redex focus's own closedness (which is
    literally `Closed H (E[t(p)])`) and carried thereafter (lifted across heap
    growth by `Closed.mono`).  This is what re-establishes the `Closed` component
    for the resumed focus when a method call returns. -/
def FrameClosedInv (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) t p E, (Frame.call t p E) :: S' <:+ S →
    Closed H (E.plug (Expr.app (Expr.val (Value.loc t)) (Expr.val p)))

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
    ∧ FldInv σ H Γ
    ∧ GTableInv σ H Γ
    ∧ RetInv σ L H S e
    ∧ ArgInv σ L H S e
    ∧ CallInv σ L H S e
    ∧ RMInv σ H S
    ∧ ThisInv σ H S
    ∧ ThisSoundInv σ L H S e
    ∧ FrameInv σ L H S
    ∧ GInitInv σ L H S e
    ∧ InitFrameInv σ L H S
    ∧ Closed H e
    ∧ FrameClosedInv H S
  | .crash => True

theorem inv_empty {σ : Sigma} {e : Expr} {L : Program} (_hσ : FixPoint σ L)
    (hvf : ValueFree e) :
    Inv σ L (.mk (fun _ => none) (fun _ => none) List.nil e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, Closed.of_valueFree e hvf, ?_⟩
  · -- ParamInv: no receiver is allocated in the empty heap.
    intro S' i cfs r t p κ G C _ _ _ _ hHt
    simp at hHt
  · -- FldInv: nothing is allocated in the empty heap.
    intro G l C v₁ v₂ hHl
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
  · -- GInitInv
    intro G ifr r htop
    simp [Stack.topInit] at htop
  · -- InitFrameInv: the empty stack has no init frame.
    intro S' G k hmem
    rcases hmem with ⟨e, hs⟩ | hs <;> simp [List.suffix_nil] at hs
  · -- FrameClosedInv: the empty stack has no call frame.
    intro S' t p E hsub
    simp [List.suffix_nil] at hsub

theorem inv_step_proj {σ : Sigma} {G G₀ : GlobName} {L : Program} {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx}
    {ℓ : Loc} {C : ClassName} {v₁ v₂ : Value} {i : Idx} {c : ClsIns} {o : GEntry}
    (_hG : Stack.TopInit S G) (hG₀ : Γ G₀ = some o) (hC : c = (.mk C G₀ v₁ v₂)) (hHl : H ℓ = some c) (_hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val (c.field i)))) := by
  obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hts, hframe, hgi, hinit, hc, hfclosed⟩ := hinv
  subst hC
  -- Covering of the contractum's runtime K-sets by the redex's, for any
  -- ambient global `G'`: `H.opOf vᵢ ⊆ σ.Fld i G C` is exactly `FldInv` at `ℓ`.
  have hP : ∀ (G' : GlobName) K,
      KJR G' σ L H S (Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)) K →
      ∃ K', KJR G' σ L H S (Expr.proj (Expr.val (Value.loc ℓ)) i) K' ∧ K ⊆ K' := by
    intro G' K hK
    cases hK
    refine ⟨_, .proj .val, ?_⟩
    intro q hq
    cases hfi : (ClsIns.mk C G₀ v₁ v₂).field i with
    | loc ℓ' =>
      rw [hfi] at hq
      cases hHℓ' : H ℓ' with
      | none => simp [Heap.opOf, hHℓ'] at hq
      | some c' =>
        simp [Heap.opOf, hHℓ'] at hq
        subst hq
        obtain ⟨c'', hH'', hmem⟩ :=
          (hfld G₀ ℓ C v₁ v₂ hHl).2 i ℓ' hfi
        rw [hHℓ'] at hH''
        cases hH''
        simpa [Heap.opOf, hHl] using hmem
    | btrue => simp [hfi, Heap.opOf] at hq
    | bfalse => simp [hfi, Heap.opOf] at hq
  -- `H`/`Γ`/`S` are untouched by E-Proj, so the five stack/heap bounds carry
  -- over verbatim; only `RetInv`, `ArgInv`, `CallInv` and `ThisSoundInv`,
  -- which mention the focus, change.
  refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, ?_, hframe, ?_, hinit, ?_, hfclosed⟩
  · -- RetInv: Proved using hP and KJR.plug_mono
    intro G' i' cfs' r' hti' htiG' t p κ htc
    obtain ⟨D, hHt, hbnd⟩ := hret G' i' cfs' r' hti' htiG' t p κ htc
    refine ⟨D, hHt, fun K hK => ?_⟩
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
    exact hsub.trans (hbnd K' hK')
  · -- ArgInv: the contractum is a value (trivially `ArgSound`) and its K-sets
    -- are covered by the redex's, so `ArgSound.plug_mono` transports the bound.
    intro G' i' cfs' r' htop' htiG'
    exact ArgSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i))
      trivial (hP G') E (harg G' i' cfs' r' htop' htiG')
  · -- CallInv: same transport, via `CallSound.plug_mono`.
    intro G' i' cfs' r' htop' htiG'
    exact CallSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i))
      trivial (hP G') E (hcall G' i' cfs' r' htop' htiG')
  · -- ThisSoundInv: same transport, via `ThisSound.plug_mono`.
    intro G' i' cfs' r' htop' htiG'
    exact ThisSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i))
      trivial (hP G') E (hts G' i' cfs' r' htop' htiG')
  · -- GInitInv:
    intro G' ifr r hti htiG' i₁ hi₁ K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
    exact hsub.trans (hgi G' ifr r hti htiG' i₁ hi₁ K' hK')
  · -- Closed: the projected field value is either a boolean (vacuously closed)
    -- or a location, which `FldInv` at `ℓ` proves allocated; then `plug_mono`
    -- transports closedness of the redex (`hc`) to the contractum.
    have heₓ : Closed H (Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)) := by
      cases hfi : (ClsIns.mk C G₀ v₁ v₂).field i with
      | loc ℓ' =>
        obtain ⟨c', hH', -⟩ := (hfld G₀ ℓ C v₁ v₂ hHl).2 i ℓ' hfi
        show (H ℓ').isSome
        rw [hH']
        rfl
      | btrue => trivial
      | bfalse => trivial
    exact Closed.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)) heₓ E hc

theorem inv_step_gproj {σ : Sigma} {G₁ : GlobName} {L : Program}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} {v : Value} {g : GEntry}
    (hG₁ : Γ G₁ = some g) (hvi : g.field i = some v) (_hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G₁ i)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hts, hframe, hgi, hinit, hc, hfclosed⟩ := hinv
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
          obtain ⟨c'', hH'', hmem⟩ := hgtable G₁ g hG₁ i ℓ' hvi
          rw [hHℓ'] at hH''
          cases hH''
          exact hmem
      | btrue => simp [Heap.opOf] at hq
      | bfalse => simp [Heap.opOf] at hq
    -- `H`/`Γ`/`S` are untouched by E-GProj, so the five stack/heap bounds carry
    -- over verbatim; only `RetInv`, `ArgInv`, `CallInv` and `ThisSoundInv`,
    -- which mention the focus, change.
    refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, ?_, hframe, ?_, hinit, ?_, hfclosed⟩
    · -- RetInv: Using hP (G.i is inside original K) and KJR.plug_mono for plug
      intro G' i' cfs' r' hti' htiG' t p κ htc
      obtain ⟨D, hHt, hbnd⟩ := hret G' i' cfs' r' hti' htiG' t p κ htc
      refine ⟨D, hHt, fun K hK => ?_⟩
      obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
      exact hsub.trans (hbnd K' hK')
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
    · -- GInitInv:
      intro G' ifr r hti htiG' i₁ hi₁ K hK
      obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
      exact hsub.trans (hgi G' ifr r hti htiG' i₁ hi₁ K' hK')
    · -- Closed: Use plug_mono. hex is proved by hgtable
      have heₓ : Closed H (Expr.val v) := by
        cases v with
        | loc ℓ' =>
          obtain ⟨c', hH', -⟩ := hgtable G₁ g hG₁ i ℓ' hvi
          show (H ℓ').isSome
          rw [hH']
          rfl
        | btrue => trivial
        | bfalse => trivial
      exact Closed.plug_mono (eₓ := Expr.val v) heₓ E hc

theorem inv_step_app {σ : Sigma} {L : Program} {G  : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {eₐ : Expr} {l : Loc} {v v₁ v₂ : Value}
    {C : ClassName} (hσ : FixPoint σ L) (hG : Stack.TopInit S G) (hHl : H l = some (ClsIns.mk C G v₁ v₂))
    (hbody : Program.HasClass L C eₐ) (hbvf : ValueFree eₐ)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val v))))) :
    Inv σ L (.mk H Γ (Stack.push (Frame.call l v E) S) eₐ) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hts, hframe, hgi, hinit, hc, hfclosed⟩ := hinv
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
    refine ⟨?_, hfld, hgtable, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv: only the freshly pushed frame is new; its argument bound
      -- `H.opOf v ⊆ σ.Param G C` is `ArgInv` at the redex (`KJR.val` gives the
      -- function position the runtime K-set `{(G, C)}` via `hHl`).
      intro S' i cfs r t p₁ κ G₁ C₁ hsub hti htG hf htC₁ ℓ hpℓ
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

            cases hHℓ : H ℓ with
            | none =>
              -- The argument `loc ℓ` occurs in the (closed) focus, so it must be
              -- allocated — contradicting `H ℓ = none`.
              have hcl : Closed H (Expr.val v) := (Closed.of_plug E hc).2
              rw [hvℓ] at hcl
              simp [Closed, hHℓ] at hcl
            | some D =>
              exact ⟨D, rfl, hbound _ _ .val .val (G, C)
                (by simp [Heap.opOf, hHl]) (by simp [Heap.opOf, hvℓ, hHℓ])⟩
          · -- `f` sits in `cfs₀`, below the new frame: reroute through
            -- `hparam` at the suffix `S`.
            have hTopS : Stack.TopInit S G₁ := by
              intro i' cfs' r' htop'
              exact htG i' (Frame.call l v E :: cfs') r' (by simp [Stack.topInit, htop'])
            exact hparam S i₀ cfs₀ r₀ t p₁ κ G₁ C₁ (List.suffix_refl S) htopS hTopS
              hf₀ htC₁ ℓ hpℓ
      · exact hparam S' i cfs r t p₁ κ G₁ C₁ hsub hti htG hf htC₁ ℓ hpℓ
    · -- RetInv: the new focus is the callee body `eₐ`, and the new top call
      -- frame is the freshly pushed one (receiver `l`, a `C`-instance), so
      -- the obligation is `K ⊆ σ.Ret G C`.  `KJR.to_kjc` covers the runtime
      -- K-set by the static `KJ G C` one (its `hthis`/`hparam` hypotheses
      -- are the fresh frame's bounds, `hbridge`), which `ret_init` bounds by
      -- `σ.Ret G C`.
      intro G' i' cfs' r' hti' htiG t p k htc
      obtain ⟨i₀, cfs₀, r₀, htopS, rfl⟩ := hpin G' i' cfs' r' hti' htiG
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      -- The fresh frame is the top call frame, so `t = l` and the receiver's
      -- class is the `C`-instance at `l` (`hHl`).
      simp only [Stack.push, Stack.topCall, Option.some.injEq, Frame.call.injEq] at htc
      obtain ⟨rfl, -, -⟩ := htc
      refine ⟨_, hHl, fun K hK => ?_⟩
      obtain ⟨K', hK', hsub⟩ :=
        KJR.to_kjc (c := some C) hthisB hparamB (fun hc => nomatch hc) hbvf hK
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
      intro S' i cfs r t p₁ κ G₁ hsub hti htG hf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · cases htopS : S.topInit with
        | none => simp [Stack.topInit, htopS] at hti
        | some x =>
          obtain ⟨i₀, cfs₀, r₀⟩ := x
          simp [Stack.topInit, htopS] at hti
          obtain ⟨-, rfl, -⟩ := hti
          rcases List.mem_cons.mp hf with heq | hf₀
          · -- `f` is the freshly pushed frame: `t = l`, a `(G, C)`-instance, so
            -- the receiver `l` is allocated (`hHl`) and its owner bound
            -- `G ∈ σ.This G C` is `ThisSound` read off at the redex (`hfresh`).
            injection heq with ht hp hκ
            rw [ht]
            have hG₁G : G₁ = G :=
              Option.some.inj
                ((htG i₀ (Frame.call l v E :: cfs₀) r₀
                    (by simp [Stack.topInit, htopS])).symm.trans (hG i₀ cfs₀ r₀ htopS))
            rw [hG₁G]
            obtain ⟨hGthis, -, -⟩ := hfresh i₀ cfs₀ r₀ htopS
            exact ⟨_, hHl, hGthis⟩
          · -- `f` sits in `cfs₀`, below the new frame: reroute through
            -- `hthisinv` at the suffix `S`.
            have hTopS : Stack.TopInit S G₁ := by
              intro i' cfs' r' htop'
              exact htG i' (Frame.call l v E :: cfs') r' (by simp [Stack.topInit, htop'])
            exact hthisinv S i₀ cfs₀ r₀ t p₁ κ G₁ (List.suffix_refl S) htopS hTopS
              hf₀
      · exact hthisinv S' i cfs r t p₁ κ G₁ hsub hti htG hf
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
        -- The fifth conjunct is the whole `GInitInv` predicate at the pre-state
        -- focus `E[l(v)]`, which is exactly `hgi` (unlike the first four, it is
        -- not applied to the frame's `G'`/`i`/… — it carries its own `cfs = []`
        -- guard internally).
        exact ⟨hret G' i cfs r hS'ti hS'tiG',
               harg G' i cfs r hS'ti hS'tiG',
               hcall G' i cfs r hS'ti hS'tiG',
               hts G' i cfs r hS'ti hS'tiG',
               hgi⟩
      · -- The frame sits inside `S`: reroute through `hframe`.
        exact hframe S' t p E₁ hsub' G' i cfs r hS'ti hS'tiG'
    · -- GInitInv: the freshly pushed call frame sits above `S`'s topmost init
      -- frame, so the new stack's `topInit` carries a *nonempty* call-frame list
      -- — the `[]` guard is unsatisfiable and the obligation is vacuous.  (This
      -- is why the new focus being the callee body `eₐ`, bounded by `Ret` rather
      -- than `GFld`, is no obstruction: `GInitInv` only fires with the init frame
      -- directly on top.)
      intro G' ifr r hti htiG' i₁ hi₁ K hK
      cases htopS : S.topInit with
      | none => simp [Stack.push, Stack.topInit, htopS] at hti
      | some x =>
        obtain ⟨f, calls, rest⟩ := x
        simp [Stack.push, Stack.topInit, htopS] at hti
    · -- InitFrameInv: the freshly pushed `Frame.call` is not an init frame, so
      -- every init frame of the new stack sits *inside* `S` with the same stack
      -- `S'` below it — the constructor-clash case (the init frame being the
      -- pushed call frame) is impossible — so reroute through the pre-state's
      -- `InitFrameInv` (`hinit`).
      intro S' G' k hsub
      apply hinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · rcases List.suffix_cons_iff.mp h with heq | hsub'
        · simp at heq
        · exact Or.inl ⟨e, hsub'⟩
      · rcases List.suffix_cons_iff.mp h with heq | hsub'
        · simp at heq
        · exact Or.inr hsub'
    · -- Closed
      exact Closed.of_valueFree eₐ hbvf
    · -- FrameClosedInv: the pushed frame `call l v E` stores the continuation `E`,
      -- whose push-time focus `E[l(v)]` is the (closed) pre-state focus `hc`;
      -- every older frame sits in `S` and reroutes through `hfclosed`.
      intro S' t p E' hsub
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · injection heq with hf hS
        injection hf with ht hp hE'
        subst ht; subst hp; subst hE'
        exact hc
      · exact hfclosed S' t p E' hsub'

theorem inv_step_ret {σ : Sigma} {L : Program} {G Gₒ : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {eₐ : Expr} {l : Loc} {v v₁ v₂ p : Value}
    {C : ClassName} (_hσ : FixPoint σ L) (_hG : Stack.TopInit S G) (hHl : H l = some (ClsIns.mk C Gₒ v₁ v₂))
    (_hbody : Program.HasClass L C eₐ) (_hbvf : ValueFree eₐ)
    (hinv : Inv σ L (.mk H Γ ((Frame.call l p E)::S) (Expr.val v))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe, hgi, hinit, hc, hfclosed⟩ := hinv
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
      have hval : H.opOf v ⊆ σ.Ret G' C := by
        obtain ⟨D, hHD, hbnd⟩ :=
          hret G' i (Frame.call l p E :: cfs) r htiPre htiGPre l p E rfl
        rw [hHl] at hHD
        obtain rfl := Option.some.inj hHD
        exact hbnd (H.opOf v) KJR.val
      have hmem : (Gₒ, C) ∈ H.opOf (Value.loc l) := by simp [Heap.opOf, hHl]
      intro K hK
      cases hK
      exact ⟨_, KJR.app KJR.val, fun x hx => Set.mem_biUnion hmem (hval hx)⟩
    refine ⟨?_, hfld, hgtable, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G' C' hsub hti htiG' hfc htc' l hpl
      exact hparam S' i cfs r t p κ G' C' (hsub.trans (List.suffix_cons _ _)) hti htiG' hfc htc' l hpl
    · -- RetInv: the resumed focus `E.plug (val v)` against the next call
      -- frame down.  `FrameInv` at the popped frame bounds the K-sets of the
      -- push-time focus `E.plug (l(p))` over `S`, and `KJR.plug_mono`
      -- transports the value covering `hcov` through `E`.
      intro G' i cfs r hti htiG' t' p' κ' htc
      obtain ⟨hKbound, -, -, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      obtain ⟨D, hHt, hbnd⟩ := hKbound t' p' κ' htc
      refine ⟨D, hHt, fun K hK => ?_⟩
      obtain ⟨K', hK', hsubK⟩ :=
        KJR.plug_mono (hcov G' i cfs r hti htiG') E K hK
      exact hsubK.trans (hbnd K' hK')
    · -- ArgInv: `FrameInv`'s second conjunct is `ArgSound` of the push-time
      -- focus over `S`; `ArgSound.plug_mono` transports it through the value
      -- covering (`ArgSound` of the bare value is `True`).
      intro G' i cfs r hti htiG'
      obtain ⟨-, hargF, -, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hAS : ArgSound G' σ L H S (Expr.val v) := trivial
      exact ArgSound.plug_mono hAS (hcov G' i cfs r hti htiG') E hargF
    · -- CallInv
      intro G' i cfs r hti htiG'
      obtain ⟨-, -, hcallF, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hCS : CallSound G' σ L H S (Expr.val v) := trivial
      exact CallSound.plug_mono hCS (hcov G' i cfs r hti htiG') E hcallF
    · -- RMInv
      intro S' i cfs r f G' l hsub hti htiG' hf hfl
      exact hrm S' i cfs r f G' l (hsub.trans (List.suffix_cons _ _)) hti htiG' hf hfl
    · -- ThisInv: the stack only shrank; reroute through the pre-state's
      -- `ThisInv` at the suffix.
      intro S' i cfs r t p κ G₁ hsub hti htiG₁ hf
      exact hthisinv S' i cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
        hti htiG₁ hf
    · -- ThisSoundInv: same stack-chain gap as `ArgInv`/`CallInv` above, for
      -- `ThisSound` of the stored context.
      intro G' i cfs r hti htiG'
      obtain ⟨-, -, -, htF, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hTS : ThisSound G' σ L H S (Expr.val v) := trivial
      exact ThisSound.plug_mono hTS (hcov G' i cfs r hti htiG') E htF
    · -- FrameInv: the stack only shrank, so every call frame of `S` is a
      -- call frame of the pre-state stack, with the same stack below it;
      -- reroute through `hframe` at the extended suffix.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG'
      exact hframe S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
        G' i cfs r hS'ti hS'tiG'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      let cfs : Stack := List.nil
      obtain ⟨-, -, -, -, hGii⟩ :=
        hframe S l p E (List.suffix_refl _) G' ifr cfs r hti htiG'
      obtain ⟨K', hK', hsubK⟩ :=
        KJR.plug_mono (hcov G' ifr cfs r hti htiG') E K hK
      exact hsubK.trans (hGii G' ifr r hti htiG' j hj K' hK')
    · -- InitFrameInv
      intro S' G' k hsub
      apply hinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · exact Or.inl ⟨e, h.trans (List.suffix_cons _ _)⟩
      · exact Or.inr (h.trans (List.suffix_cons _ _))
    · -- Closed: `FrameClosedInv` at the popped frame gives closedness of the
      -- push-time focus `E[l(p)]`; `plug_mono` swaps the redex for the returned
      -- value `v` (closed by `hc`), yielding closedness of the resumed focus.
      have hEclosed : Closed H (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val p))) :=
        hfclosed S l p E (List.suffix_refl _)
      exact Closed.plug_mono (eₓ := Expr.val v) hc E hEclosed
    · -- FrameClosedInv: the stack only shrank, so every call frame of `S` is a
      -- call frame of the pre-state stack; reroute through `hfclosed`.
      intro S' t' p' E₁ hsub
      exact hfclosed S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))

theorem inv_step_alloc {σ : Sigma} {e₁ e₂ eₐ : Expr} {G : GlobName} {L : Program} {v₁ v₂ : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} {l : Loc} {C: ClassName}
    (htG : Stack.TopInit S G) (_hσ : FixPoint σ L)
    (hHl : H l = none) (_hbody : Program.HasClass L C eₐ) (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.newC C v₁ v₂))))
    : Inv σ L (.mk (Heap.update H l (ClsIns.mk C G v₁ v₂)) Γ S (E.plug (Expr.val (Value.loc l)))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv: the stack is unchanged and the heap only grew at the fresh
      -- `l`.  The receiver `t` is allocated in the old heap (`hrm`), so the
      -- update is invisible to it; the `∃`-form's old `hparam` already places
      -- the argument object in the old heap, so it is distinct from `l`.
      intro S' i' cfs r t p κ G' C' hsub hti htiG' hfc hHt ℓ hpℓ
      obtain ⟨Ct, hHt₀, -⟩ :=
        hrm S' i' cfs r (Frame.call t p κ) G' t hsub hti htiG' hfc rfl
      have htl : t ≠ l := by
        intro h; rw [h, hHl] at hHt₀; simp at hHt₀
      have hHt' : H t = some C' := by simpa [Heap.update, htl] using hHt
      -- The old `hparam` witnesses the argument `ℓ` in the *old* heap, so `ℓ`
      -- is allocated there and hence distinct from the fresh `l`; the previous
      -- `ℓ = l` "dangling" gap cannot arise under the `∃`-form.
      obtain ⟨D, hHD, hmem⟩ :=
        hparam S' i' cfs r t p κ G' C' hsub hti htiG' hfc hHt' ℓ hpℓ
      have hℓl : ℓ ≠ l := by
        intro h; rw [h, hHl] at hHD; simp at hHD
      exact ⟨D, by simpa [Heap.update, hℓl] using hHD, hmem⟩
    · -- FldInv
      intro G' l' C' v₁' v₂' hHl'
      refine ⟨?_, ?_⟩
      · -- Owner `G'` of the object at `l'` is initialized.  For old objects this
        -- is the `.1` of the inductive `hfld`; for the fresh `l` it is the
        -- ambient global of the reachable `new C(e₁,e₂)`, which `TopInit`
        -- guarantees is initialized.  Needs those two facts wired together.
        sorry
      · intro j ℓ' hfj
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
          obtain ⟨c', hc', hcls⟩ := (hfld G' l' C' v₁' v₂' hHl'').2 j ℓ' hfj
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
      intro S' i' cfs r t p κ G₁ hsub hti htiG₁ hfc
      obtain ⟨Ct, hHt₀, -⟩ :=
        hrm S' i' cfs r (Frame.call t p κ) G₁ t hsub hti htiG₁ hfc rfl
      have htl : t ≠ l := by
        intro h; rw [h, hHl] at hHt₀; simp at hHt₀
      obtain ⟨D, hHt', hmem⟩ := hthisinv S' i' cfs r t p κ G₁ hsub hti htiG₁ hfc
      exact ⟨D, by simpa [Heap.update, htl] using hHt', hmem⟩
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
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe, hgi, hinit, -⟩ := hinv
    -- The pushed `init1 G …` frame is the topmost init frame of the new stack,
    -- so any `Stack.TopInit` witness for it pins the ambient global to `G`.
    have hpin : ∀ {G₀ : GlobName},
        Stack.TopInit ((Frame.init1 G e₂ (E.plug (Expr.gproj G i))) :: S) G₀ → G = G₀ := by
      intro G₀ hTop
      have hgl := hTop (Frame.init1 G e₂ (E.plug (Expr.gproj G i))) List.nil S (by simp [Stack.topInit])
      simpa [Frame.glob] using hgl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sorry⟩
    · -- ParamInv: rcases htop rfl tells us there are no call frames above the new init frame, so vacuous
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases htop with ⟨_, rfl, _⟩
        simp at hcall
      · exact hparam S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
    · -- FldInv: the heap is unchanged, so the field-typing half is exactly the
      -- old `hfld`.  The GTable only *gains* the key `G` (mapped to
      -- `⟨none, none⟩`), so `(Γ[G↦…] G₁).isSome` holds regardless of whether
      -- `G₁ = G`: if `G₁ ≠ G` the entry is untouched, and if `G₁ = G` the
      -- update itself makes it `some`.  No "nothing is owned by `G`" invariant
      -- is required.
      intro G₁ l C v₁ v₂ hHl
      obtain ⟨hsome, hfield⟩ := hfld G₁ l C v₁ v₂ hHl
      refine ⟨?_, hfield⟩
      by_cases hEq : G₁ = G
      · subst hEq; simp [GTable.update]
      · simpa [GTable.update, hEq] using hsome
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
      intro G₀ i' cfs' r' _htop' hTopG₀
      obtain rfl := hpin hTopG₀
      exact ArgSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₁ (RE.init₁ hG) (fun _ => hpf₁) hvf₁
    · -- CallInv: the topmost init frame is now `G`'s own, pinning the ambient
      -- global to `G`, and the new focus is `G`'s first initializer, whose
      -- `Calls0` set `rm_init` puts inside `σ.RM G` — `CallSound.of_calls0`.
      intro G₀ i' cfs' r' _htop' hTopG₀
      obtain rfl := hpin hTopG₀
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
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hcf
      · exact hthisinv S' i' cfs r t p κ G₁ hsub hti hTopG hcf
    · -- ThisSoundInv: the new focus is `G`'s first initializer — reachable
      -- (`RE.init₁`) initializer code, so `ThisSound.of_re` applies at the
      -- empty context.
      intro G₀ i' cfs' r' _htop' hTopG₀
      obtain rfl := hpin hTopG₀
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
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      obtain rfl := hpin htiG'
      simp [Stack.topInit] at hti
      obtain ⟨rfl, -, -⟩ := hti
      simp [Frame.idx] at hj
      subst hj
      obtain ⟨K', hK', hsub⟩ := KJR.to_kjc (c := none) (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) (fun _ => hpf₁) hvf₁ hK
      exact hsub.trans (hσ.gfld_init_one hG hK')
    · -- InitFrameInv: the pushed `init1 G e₂ κ` frame (`κ = E[G.i]`) is the
      -- *seeding* step.  A frame recorded by the post-state either *is* that
      -- pushed head — whose stored continuation `κ` is exactly the pre-state
      -- focus, so its `GInit`-soundness over `S` is the pre-state `hgi` — or
      -- sits strictly inside `S`, rerouted through the pre-state's `hinit`.
      intro S' G' k hsub
      rcases hsub with ⟨e, h⟩ | h
      · -- an `init1` frame.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · -- the pushed head: `G' = G`, `k = κ = E[G.i]`, `S' = S`; use `hgi`.
          injection heq with hh hS
          injection hh with hg he hk
          rw [hS, hk]
          exact hgi
        · -- inside `S`: reroute through the pre-state `hinit` (over `S` directly).
          exact hinit S' G' k (Or.inl ⟨e, h'⟩)
      · -- an `init2` frame: it cannot be the pushed `init1` head, so it lies in `S`.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · exact absurd heq (by simp)
        · exact hinit S' G' k (Or.inr h')

theorem inv_step_inext {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program} {v : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} (hnewG : Γ G = some ⟨none, none⟩) (hσ : FixPoint σ L)
    (hG : Program.HasObject L G e₁ e₂)
    (hpf₂ : ContextFree e₂) (hvf₂ : ValueFree e₂) (hpf₁ : ContextFree e₁)
    (hinv : Inv σ L (.mk H Γ ((Frame.init1 G e₂ (E.plug (Expr.gproj G i))) :: S) (Expr.val v)))
    : Inv σ L (.mk H Γ[G↦ ⟨v, none⟩] ((Frame.init2 G (E.plug (Expr.gproj G i))) :: S) e₂) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe, hgi, hinit, -⟩ := hinv
    have hpin : ∀ {G₀ : GlobName},
        Stack.TopInit ((Frame.init2 G (E.plug (Expr.gproj G i))) :: S) G₀ → G = G₀ := by
      intro G₀ hTop
      have hgl := hTop (Frame.init2 G (E.plug (Expr.gproj G i))) List.nil S (by simp [Stack.topInit])
      simpa [Frame.glob] using hgl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sorry⟩
    · -- ParamInv
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases htop with ⟨_, rfl, _⟩
        simp at hcall
      · exact hparam S' i cfs r t p κ G₁ C (hsub.trans (List.suffix_cons _ _)) htop hTopG hcall hHt
    · -- FldInv
      intro G₁ l C v₁ v₂ hHl
      obtain ⟨hsome, hfield⟩ := hfld G₁ l C v₁ v₂ hHl
      refine ⟨?_, ?_⟩
      · by_cases hEq : G₁ = G
        · subst hEq; simp [GTable.update]
        · simpa [GTable.update, hEq] using hsome
      · exact (hfld G₁ l C v₁ v₂ hHl).2
    · -- GTableInv: `G`'s first field is now `v`; entries other than `G` are
      -- untouched, so the old `hgtable` covers them.  For `G`'s first field the
      -- stored value is the old focus `v`, whose runtime K-set the *pre-state*
      -- `GInitInv` (`hgi`, over the `init1` stack) bounds by `σ.GFld one G` —
      -- reading `one` off the topmost `init1` frame.  When `v = loc ℓ'` points
      -- to an allocated object that bound is exactly the required owner-pair
      -- membership; a dangling `v` (`H ℓ' = none`) is the same closedness gap
      -- left open in `inv_step_alloc`.
      intro g o HGo j ℓ' hj
      by_cases hEq : g = G
      · subst hEq
        have HGo' : (⟨v, none⟩ : GEntry) = o := by simpa [GTable.update] using HGo
        subst HGo'
        cases j with
        | one =>
          -- `⟨v, none⟩.field one = v`, so `hj : v = loc ℓ'`.
          simp [GEntry.field] at hj
          subst hj
          -- Pre-state `GInitInv` on the `init1` stack bounds `v = loc ℓ'`.
          have hbound : H.opOf (Value.loc ℓ') ⊆ σ.GFld Idx.one g := by
            refine hgi g (Frame.init1 g e₂ (E.plug (Expr.gproj g i))) S
              (by simp [Stack.topInit]) ?_ Idx.one ?_ (H.opOf (Value.loc ℓ')) KJR.val
            · -- the topmost init frame is `G`'s own
              intro f cfs r htop
              simp [Stack.topInit] at htop
              obtain ⟨rfl, -, -⟩ := htop
              rfl
            · -- its index is `one`
              rfl
          cases hHℓ' : H ℓ' with
          | some c' =>
            exact ⟨c', rfl, hbound (by simp [Heap.opOf, hHℓ'])⟩
          | none =>
            -- `v = loc ℓ'` dangles (`H ℓ' = none`): ruled out for reachable
            -- configs, but `Inv` carries no closedness component yet (cf. the
            -- `FldInv`/`RetInv` sorries in `inv_step_alloc`).
            sorry
        | two => simp [GEntry.field] at hj
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ j ℓ' hj
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
      exact ArgSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
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
        (Set.subset_union_right.trans (hσ.rm_init hG hc₁ hc₂)) hpf₂ hvf₂
    · -- RMInv: No call frames
      intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hf
      · exact hrm S' i cfs r f G₁ l (hsub.trans (List.suffix_cons _ _)) hti hG₁ hf hfl
    · -- ThisInv: the pushed `init2` frame carries no call frames above it,
      -- and the suffixes of `S` are rerouted through the pre-state (whose
      -- stack extends `S` by the popped `init1` frame).
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hcf
      · exact hthisinv S' i' cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
          hti hTopG hcf
    · -- ThisSoundInv: the new focus is `G`'s second initializer — reachable
      -- (`RE.init₂`) initializer code, so `ThisSound.of_re` applies at the
      -- empty context.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀ i' cfs' r' htop'
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      exact ThisSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
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
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      obtain rfl := hpin htiG'
      simp [Stack.topInit] at hti
      obtain ⟨rfl, -, -⟩ := hti
      simp [Frame.idx] at hj
      subst hj
      obtain ⟨K', hK', hsub⟩ := KJR.to_kjc (c := none) (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) (fun _ => hpf₂) hvf₂ hK
      exact hsub.trans (hσ.gfld_init_two hG hK')
    · -- InitFrameInv: the continuation `k` is threaded unchanged from the popped
      -- `init1 G e₂ κ` frame to the pushed `init2 G κ` frame (`κ = E[G.i]`).  A
      -- frame recorded by the post-state either *is* that pushed `init2 G κ`
      -- head — whose continuation `κ` the pre-state's own `init1` frame carried,
      -- so reroute through `hinit`'s `init1` disjunct at `suffix_refl` — or sits
      -- strictly inside `S`, hence below the pre-state's `init1` frame too.
      intro S' G' k hsub
      rcases hsub with ⟨e, h⟩ | h
      · -- an `init1` frame: it cannot be the pushed `init2` head, so it lies in `S`.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · exact absurd heq (by simp)
        · exact hinit S' G' k (Or.inl ⟨e, h'.trans (List.suffix_cons _ _)⟩)
      · -- an `init2` frame: either the pushed head or a frame inside `S`.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · -- the pushed head: `G' = G`, `k = κ`, `S' = S`; the pre-state's own
          -- `init1 G e₂ κ` frame carried this same continuation.
          injection heq with hf hS
          injection hf with hG' hk
          rw [hS, hk]
          exact hinit S G (E.plug (Expr.gproj G i))
            (Or.inl ⟨e₂, List.suffix_refl _⟩)
        · exact hinit S' G' k (Or.inr (h'.trans (List.suffix_cons _ _)))

theorem inv_step_ipop {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program} {v₁ v₂ : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} (hnewG : Γ G = some ⟨v₁, none⟩) (_hσ : FixPoint σ L)
    (hG : Program.HasObject L G e₁ e₂) (hinv : Inv σ L (.mk H Γ ((Frame.init2 G (E.plug (Expr.gproj G i))) :: S) e₂))
    : Inv σ L (.mk H Γ[G↦ ⟨v₁, v₂⟩] S (E.plug (Expr.gproj G i))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, -, hframe, hgi, hinit, -⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sorry⟩
    · -- ParamInv
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      exact hparam S' i cfs r t p κ G₁ C (hsub.trans (List.suffix_cons _ _)) htop hTopG hcall hHt
    · -- FldInv
      intro G₁ l C v₁ v₂ hHl
      refine ⟨?_, ?_⟩
      · -- Owner `G₁` is initialized in `Γ[G ↦ (v₁, v₂)]`.  Here `G` becomes
        -- *fully* initialized, so this strengthens the old `hfld.1`; still needs
        -- the "no object owned by an under-initialized global" invariant.
        sorry
      · -- Fields: heap unchanged and `σ.Fld` is table-independent.
        exact (hfld G₁ l C v₁ v₂ hHl).2
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
          exact hgtable g ⟨v₁, none⟩ hnewG Idx.one ℓ'
            (by simpa [GEntry.field] using hi)
        | two =>

          sorry
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ i ℓ' hi
    · -- RetInv
      sorry
    · -- ArgInv
      sorry
    · -- CallInv
      sorry
    · intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      exact hrm S' i cfs r f G₁ l (hsub.trans (List.suffix_cons _ _)) hti hG₁ hf hfl
    · -- ThisInv
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf
      exact hthisinv S' i' cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
        hti hTopG hcf
    · -- ThisSoundInv
      sorry
    · -- FrameInv
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG'
      exact hframe S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
        G' i cfs r hS'ti hS'tiG'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      have hk : GInitInv σ L H S (E.plug (Expr.gproj G i)) :=
        hinit S G (E.plug (Expr.gproj G i)) (Or.inr (List.suffix_refl _))
      exact hk G' ifr r hti htiG' j hj K hK
    · -- InitFrameInv
      intro S' G' k hsub
      apply hinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · exact Or.inl ⟨e, h.trans (List.suffix_cons _ _)⟩
      · exact Or.inr (h.trans (List.suffix_cons _ _))

end Proof
