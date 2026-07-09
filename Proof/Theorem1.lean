import Proof.Semantics
import Proof.Analysis

/-
  Theorem 1 (paper §"Core Theorems").

    A Global Object's dependencies are captured by Dep(G).

    Given ⟨H, Γ, e⟩, if  object G { val 1 = e₁; val 2 = e₂ } ∈ L̄  and
    eᵢ →* G'.j  for some i, j ∈ {1,2},  then  G' ∈ Dep(G).

  Reading of the statement.  "eᵢ →* G'.j" is read as: starting from a
  configuration whose focus is the initialiser eᵢ, the machine reaches a
  configuration whose focus is an access `G'.j` (i.e. `G'.j` sitting in the hole
  of some evaluation context `E`).  We quantify over the surrounding heap `H` /
  global table `Γ` of the start and end configurations.

  `Dep` here is the helper function `Dep σ L G` computed from the reachable
  expressions `RE` (paper Steps 2c/2d); it is not a component of `σ`.
-/

namespace Proof

/-! ### Direct global references `L̄ ⊢ e ⇓ᵍ Gₑ`

  A proof-side helper (it is not part of the paper's analysis, which works with
  `RE` instead): the set of globals `e` accesses syntactically.  It is the
  focus-shaped counterpart of `Dep`: if `e` is a reachable expression (`RE`)
  and `e ⇓ᵍ Gₑ`, then `Gₑ ⊆ Dep(G)` (`GRef.subset_dep` below). -/
inductive GRef (L : Program) : Expr → Set GlobName → Prop
  | thisE  : GRef L Expr.thisE ∅
  | paramE : GRef L Expr.paramE ∅
  | gproj {G i} : GRef L (Expr.gproj G i) {G}
  | proj {e i Ge} : GRef L e Ge → GRef L (Expr.proj e i) Ge
  | newC {C e₁ e₂ G₁ G₂} :
      GRef L e₁ G₁ → GRef L e₂ G₂ → GRef L (Expr.newC C e₁ e₂) (G₁ ∪ G₂)
  | app {e₁ e₂ G₁ G₂} :
      GRef L e₁ G₁ → GRef L e₂ G₂ → GRef L (Expr.app e₁ e₂) (G₁ ∪ G₂)
  | val {v} : GRef L (Expr.val v) ∅

/-! ### Analysis-judgment infrastructure for subject reduction

  The three syntax-directed judgments `⇓ᴷ` (`KJ0`), `calls` (`Calls0`) and `⇓ᵍ`
  (`GRef`) are *deterministic* (each expression has at most one result set) and,
  on `this`/`param`-free expressions, *total*.  They are also *congruent* under
  evaluation contexts: replacing the contents of a hole by something with the same
  judgment leaves the judgment of the whole expression unchanged.  These are the
  structural facts that make `Inv` preserved by `Step`. -/

/-- `⇓ᵍ` is deterministic. -/
theorem GRef.det {L : Program} : ∀ {e G G'}, GRef L e G → GRef L e G' → G = G'
  | _, _, _, .thisE,      .thisE        => rfl
  | _, _, _, .paramE,     .paramE       => rfl
  | _, _, _, .gproj,      .gproj        => rfl
  | _, _, _, .val,        .val          => rfl
  | _, _, _, .proj h,     .proj h'      => GRef.det h h'
  | _, _, _, .newC h1 h2, .newC h1' h2' => by rw [GRef.det h1 h1', GRef.det h2 h2']
  | _, _, _, .app h1 h2,  .app h1' h2'  => by rw [GRef.det h1 h1', GRef.det h2 h2']

/-- `⇓ᴷ` is deterministic. -/
theorem KJ0.det {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ {e K K'}, KJ0 G σ L e K → KJ0 G σ L e K' → K = K'
  | _, _, _, .gproj,  .gproj   => rfl
  | _, _, _, .newC,   .newC    => rfl
  | _, _, _, .val,    .val     => rfl
  | _, _, _, .proj h, .proj h' => by rw [KJ0.det h h']
  | _, _, _, .app h,  .app h'  => by rw [KJ0.det h h']

/-- `calls` is deterministic. -/
theorem Calls0.det {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ {e K K'}, Calls0 G σ L e K → Calls0 G σ L e K' → K = K'
  | _, _, _, .gproj,        .gproj           => rfl
  | _, _, _, .val,          .val             => rfl
  | _, _, _, .proj h,       .proj h'         => Calls0.det h h'
  | _, _, _, .newC h1 h2,   .newC h1' h2'    => by rw [Calls0.det h1 h1', Calls0.det h2 h2']
  | _, _, _, .app hk h1 h2, .app hk' h1' h2' => by
      rw [KJ0.det hk hk', Calls0.det h1 h1', Calls0.det h2 h2']

/-- `this`/`param`-freeness — the runtime-focus / object-initialiser fragment on
    which the context-free judgments `KJ0`/`Calls0` are total. -/
def ParamFree : Expr → Prop
  | Expr.thisE      => False
  | Expr.paramE     => False
  | Expr.newC _ a b => ParamFree a ∧ ParamFree b
  | Expr.app a b    => ParamFree a ∧ ParamFree b
  | Expr.proj a _   => ParamFree a
  | Expr.gproj _ _  => True
  | Expr.val _      => True

/-- `⇓ᵍ` is total: every expression references some (unique) global set. -/
theorem GRef.exists' (L : Program) : ∀ e, ∃ G, GRef L e G := by
  intro e
  induction e with
  | thisE => exact ⟨_, .thisE⟩
  | paramE => exact ⟨_, .paramE⟩
  | newC C a b iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb; exact ⟨_, .newC ha hb⟩
  | app a b iha ihb =>
      obtain ⟨_, ha⟩ := iha; obtain ⟨_, hb⟩ := ihb; exact ⟨_, .app ha hb⟩
  | proj a i ih => obtain ⟨_, ha⟩ := ih; exact ⟨_, .proj ha⟩
  | gproj G i => exact ⟨_, .gproj⟩
  | val v => exact ⟨_, .val⟩

/-- `⇓ᴷ` is total on `this`/`param`-free expressions. -/
theorem KJ0.exists' {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ {e}, ParamFree e → ∃ K, KJ0 G σ L e K := by
  intro e
  induction e with
  | thisE => intro h; simp only [ParamFree] at h
  | paramE => intro h; simp only [ParamFree] at h
  | newC C a b iha ihb => intro _; exact ⟨_, .newC⟩
  | app a b iha ihb =>
      intro h; simp only [ParamFree] at h
      obtain ⟨_, ha⟩ := iha h.1; exact ⟨_, .app ha⟩
  | proj a i ih => intro h; simp only [ParamFree] at h; obtain ⟨_, ha⟩ := ih h; exact ⟨_, .proj ha⟩
  | gproj G i => intro _; exact ⟨_, .gproj⟩
  | val v => intro _; exact ⟨_, .val⟩

/-- `calls` is total on `this`/`param`-free expressions. -/
theorem Calls0.exists' {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ {e}, ParamFree e → ∃ K, Calls0 G σ L e K := by
  intro e
  induction e with
  | thisE => intro h; simp only [ParamFree] at h
  | paramE => intro h; simp only [ParamFree] at h
  | newC C a b iha ihb =>
      intro h; simp only [ParamFree] at h
      obtain ⟨_, ha⟩ := iha h.1; obtain ⟨_, hb⟩ := ihb h.2; exact ⟨_, .newC ha hb⟩
  | app a b iha ihb =>
      intro h; simp only [ParamFree] at h
      obtain ⟨_, hk⟩ := KJ0.exists' (G := G) (σ := σ) (L := L) h.1
      obtain ⟨_, ha⟩ := iha h.1; obtain ⟨_, hb⟩ := ihb h.2
      exact ⟨_, .app hk ha hb⟩
  | proj a i ih => intro h; simp only [ParamFree] at h; obtain ⟨_, ha⟩ := ih h; exact ⟨_, .proj ha⟩
  | gproj G i => intro _; exact ⟨_, .gproj⟩
  | val v => intro _; exact ⟨_, .val⟩

/-! ### From reachable expressions to `Dep` -/

/-- Globals directly referenced by a reachable expression are dependencies:
    if `e ∈ RE(G)` (in any class context `c`) and `e ⇓ᵍ Gₑ`, then
    `Gₑ ⊆ Dep(G)`.  This is how the `RE`-based `Dep` of the paper is consumed
    by the subject-reduction argument. -/
theorem GRef.subset_dep {σ : Sigma} {L : Program} {G : GlobName} {c : Ctx} :
    ∀ {e Ge}, GRef L e Ge → RE σ L G c e → Ge ⊆ Dep σ L G := by
  intro e Ge hg
  induction hg with
  | thisE => exact fun _ => Set.empty_subset _
  | paramE => exact fun _ => Set.empty_subset _
  | val => exact fun _ => Set.empty_subset _
  | gproj => exact fun hre => Set.singleton_subset_iff.mpr (DepJ.direct hre)
  | proj _ ih => exact fun hre => ih (RE.proj hre)
  | newC _ _ ih₁ ih₂ =>
      exact fun hre => Set.union_subset (ih₁ (RE.newC₁ hre)) (ih₂ (RE.newC₂ hre))
  | app _ _ ih₁ ih₂ =>
      exact fun hre => Set.union_subset (ih₁ (RE.app₁ hre)) (ih₂ (RE.app₂ hre))

/-! ### Congruence of the judgments under evaluation contexts -/

/-- Congruence of `⇓ᵍ` under an evaluation context: if `a` and `a'` reference the
    same globals, then `E[a]` and `E[a']` reference the same globals. -/
theorem GRef.plug_congr {L : Program} {a a' : Expr} {Ga : Set GlobName}
    (ha : GRef L a Ga) (ha' : GRef L a' Ga) :
    ∀ {E : ECtx} {G}, GRef L (E.plug a) G → GRef L (E.plug a') G := by
  intro E
  induction E with
  | hole => intro G h; simp only [ECtx.plug] at h ⊢; rw [← GRef.det ha h]; exact ha'
  | projc E i ih => intro G h; simp only [ECtx.plug] at h ⊢; cases h with | proj h => exact .proj (ih h)
  | appL E e ih => intro G h; simp only [ECtx.plug] at h ⊢; cases h with | app h1 h2 => exact .app (ih h1) h2
  | appR v E ih => intro G h; simp only [ECtx.plug] at h ⊢; cases h with | app h1 h2 => exact .app h1 (ih h2)
  | newL C E e ih => intro G h; simp only [ECtx.plug] at h ⊢; cases h with | newC h1 h2 => exact .newC (ih h1) h2
  | newR C v E ih => intro G h; simp only [ECtx.plug] at h ⊢; cases h with | newC h1 h2 => exact .newC h1 (ih h2)

/-- Monotone version of `GRef.plug_congr`: if the hole contents `a'` reference a
    *subset* of what `a` references (`Ga' ⊆ Ga`), then whatever `E[a']` references
    is contained in what `E[a]` references.  This is what lets a reduction whose
    redex references `{G₁}` step to a value referencing `∅`. -/
theorem GRef.plug_mono {L : Program} {a a' : Expr} {Ga Ga' : Set GlobName}
    (ha : GRef L a Ga) (ha' : GRef L a' Ga') (hsub : Ga' ⊆ Ga) :
    ∀ {E : ECtx} {G'}, GRef L (E.plug a') G' → ∃ G, GRef L (E.plug a) G ∧ G' ⊆ G := by
  intro E
  induction E with
  | hole =>
      intro G' h; simp only [ECtx.plug] at h ⊢
      exact ⟨Ga, ha, by rw [← GRef.det ha' h]; exact hsub⟩
  | projc E i ih =>
      intro G' h; simp only [ECtx.plug] at h ⊢
      cases h with | proj h => obtain ⟨G, hG, hs⟩ := ih h; exact ⟨G, .proj hG, hs⟩
  | appL E e ih =>
      intro G' h; simp only [ECtx.plug] at h ⊢
      cases h with | app h1 h2 =>
        obtain ⟨G, hG, hs⟩ := ih h1
        exact ⟨G ∪ _, .app hG h2, Set.union_subset_union hs (subset_refl _)⟩
  | appR v E ih =>
      intro G' h; simp only [ECtx.plug] at h ⊢
      cases h with | app h1 h2 =>
        obtain ⟨G, hG, hs⟩ := ih h2
        exact ⟨_ ∪ G, .app h1 hG, Set.union_subset_union (subset_refl _) hs⟩
  | newL C E e ih =>
      intro G' h; simp only [ECtx.plug] at h ⊢
      cases h with | newC h1 h2 =>
        obtain ⟨G, hG, hs⟩ := ih h1
        exact ⟨G ∪ _, .newC hG h2, Set.union_subset_union hs (subset_refl _)⟩
  | newR C v E ih =>
      intro G' h; simp only [ECtx.plug] at h ⊢
      cases h with | newC h1 h2 =>
        obtain ⟨G, hG, hs⟩ := ih h2
        exact ⟨_ ∪ G, .newC h1 hG, Set.union_subset_union (subset_refl _) hs⟩

/-- Congruence of `⇓ᴷ` under an evaluation context. -/
theorem KJ0.plug_congr {G : GlobName} {σ : Sigma} {L : Program} {a a' : Expr}
    {Ka : Set ClassName}
    (ha : KJ0 G σ L a Ka) (ha' : KJ0 G σ L a' Ka) :
    ∀ {E : ECtx} {K}, KJ0 G σ L (E.plug a) K → KJ0 G σ L (E.plug a') K := by
  intro E
  induction E with
  | hole => intro K h; simp only [ECtx.plug] at h ⊢; rw [← KJ0.det ha h]; exact ha'
  | projc E i ih => intro K h; simp only [ECtx.plug] at h ⊢; cases h with | proj h => exact .proj (ih h)
  | appL E e ih => intro K h; simp only [ECtx.plug] at h ⊢; cases h with | app h => exact .app (ih h)
  | appR v E ih => intro K h; simp only [ECtx.plug] at h ⊢; cases h with | app h => exact .app h
  | newL C E e ih => intro K h; simp only [ECtx.plug] at h ⊢; cases h with | newC => exact .newC
  | newR C v E ih => intro K h; simp only [ECtx.plug] at h ⊢; cases h with | newC => exact .newC

/-- Monotone version of `KJ0.plug_congr`. -/
theorem KJ0.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {a a' : Expr}
    {Ka Ka' : Set ClassName}
    (ha : KJ0 G σ L a Ka) (ha' : KJ0 G σ L a' Ka') (hsub : Ka' ⊆ Ka) :
    ∀ {E : ECtx} {K'}, KJ0 G σ L (E.plug a') K' → ∃ K, KJ0 G σ L (E.plug a) K ∧ K' ⊆ K := by
  intro E
  induction E with
  | hole =>
    intro K h
    simp only [ECtx.plug] at h ⊢
    rw [← KJ0.det ha' h]
    exact ⟨Ka, ha, hsub⟩
  | projc E i ih =>
    intro K h
    simp only [ECtx.plug] at h ⊢
    cases h with | proj h =>
    obtain ⟨Km, hKm, hs⟩ := ih h
    exact ⟨_, .proj hKm, Set.biUnion_subset_biUnion_left hs⟩
  | appL E e ih =>
    intro K h
    simp only [ECtx.plug] at h ⊢
    cases h with | app h =>
    obtain ⟨K, hKj, hKs⟩ := ih h
    exact ⟨_, .app hKj, Set.biUnion_subset_biUnion_left hKs⟩
  | appR v E ih =>
    intro K h
    simp only [ECtx.plug] at h ⊢
    cases h with | app h =>
    exact ⟨_, .app h, subset_refl _⟩
  | newL C E e ih =>
    intro K h
    simp only [ECtx.plug] at h ⊢
    cases h with | newC =>
    exact ⟨_, .newC, subset_refl _⟩
  | newR C v E ih =>
    intro K h
    simp only [ECtx.plug] at h ⊢
    cases h with | newC =>
    exact ⟨_, .newC, subset_refl _⟩

/-- Congruence of `calls` under an evaluation context.  Because `Calls0` of an
    application also inspects `⇓ᴷ` of the function position, the hole contents must
    agree on `⇓ᴷ` as well as on `calls`. -/
theorem Calls0.plug_congr {G : GlobName} {σ : Sigma} {L : Program} {a a' : Expr}
    {Ka Ca : Set ClassName}
    (hKa : KJ0 G σ L a Ka) (hKa' : KJ0 G σ L a' Ka)
    (ha : Calls0 G σ L a Ca) (ha' : Calls0 G σ L a' Ca) :
    ∀ {E : ECtx} {K}, Calls0 G σ L (E.plug a) K → Calls0 G σ L (E.plug a') K := by
  intro E
  induction E with
  | hole => intro K h; simp only [ECtx.plug] at h ⊢; rw [← Calls0.det ha h]; exact ha'
  | projc E i ih => intro K h; simp only [ECtx.plug] at h ⊢; cases h with | proj h => exact .proj (ih h)
  | appL E e ih =>
      intro K h; simp only [ECtx.plug] at h ⊢
      cases h with | app hk h1 h2 => exact .app (KJ0.plug_congr hKa hKa' hk) (ih h1) h2
  | appR v E ih =>
      intro K h; simp only [ECtx.plug] at h ⊢
      cases h with | app hk h1 h2 => exact .app hk h1 (ih h2)
  | newL C E e ih =>
      intro K h; simp only [ECtx.plug] at h ⊢
      cases h with | newC h1 h2 => exact .newC (ih h1) h2
  | newR C v E ih =>
      intro K h; simp only [ECtx.plug] at h ⊢
      cases h with | newC h1 h2 => exact .newC h1 (ih h2)

/-- Monotone version of `Calls0.plug_congr`: if the hole contents `a'` have a
    smaller `⇓ᴷ` and a smaller `calls` than `a`, then the `calls` of `E[a']` is
    contained in that of `E[a]`.  This is what lets `E-GProj` shrink the redex
    `G₁.i` (with `⇓ᴷ = GFldᵢ(G₁)`) to a value (with `⇓ᴷ = ∅`). -/
theorem Calls0.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {a a' : Expr}
    {Ka Ka' Ca Ca' : Set ClassName}
    (hKa : KJ0 G σ L a Ka) (hKa' : KJ0 G σ L a' Ka') (hKsub : Ka' ⊆ Ka)
    (ha : Calls0 G σ L a Ca) (ha' : Calls0 G σ L a' Ca') (hCsub : Ca' ⊆ Ca) :
    ∀ {E : ECtx} {K'}, Calls0 G σ L (E.plug a') K' →
      ∃ K, Calls0 G σ L (E.plug a) K ∧ K' ⊆ K := by
  intro E
  induction E with
  | hole =>
      intro K' h; simp only [ECtx.plug] at h ⊢
      exact ⟨Ca, ha, by rw [← Calls0.det ha' h]; exact hCsub⟩
  | projc E i ih =>
      intro K' h; simp only [ECtx.plug] at h ⊢
      cases h with | proj h =>
      obtain ⟨K, hK, hs⟩ := ih h
      exact ⟨K, .proj hK, hs⟩
  | appL E e ih =>
      intro K' h; simp only [ECtx.plug] at h ⊢
      cases h with | app hk h1 h2 =>
      obtain ⟨Kf, hKf, sf⟩ := KJ0.plug_mono hKa hKa' hKsub hk
      obtain ⟨Kc, hKc, sc⟩ := ih h1
      exact ⟨_, .app hKf hKc h2,
        Set.union_subset_union (Set.union_subset_union sf sc) (subset_refl _)⟩
  | appR v E ih =>
      intro K' h; simp only [ECtx.plug] at h ⊢
      cases h with | app hk h1 h2 =>
      obtain ⟨Kc, hKc, sc⟩ := ih h2
      exact ⟨_, .app hk h1 hKc, Set.union_subset_union (subset_refl _) sc⟩
  | newL C E e ih =>
      intro K' h; simp only [ECtx.plug] at h ⊢
      cases h with | newC h1 h2 =>
      obtain ⟨Kc, hKc, sc⟩ := ih h1
      exact ⟨_, .newC hKc h2, Set.union_subset_union sc (subset_refl _)⟩
  | newR C v E ih =>
      intro K' h; simp only [ECtx.plug] at h ⊢
      cases h with | newC h1 h2 =>
      obtain ⟨Kc, hKc, sc⟩ := ih h2
      exact ⟨_, .newC h1 hKc, Set.union_subset_union (subset_refl _) sc⟩

/-! ### Runtime-side judgments (groundwork for the `E-AppBeta`/`E-Ret` cases)

  The static `Calls0` bound suffices for `E-Proj`/`E-GProj`, but a β-step
  invokes the *actual* class of the object in the heap; these heap-aware
  variants will replace `Calls0` there. -/

/-- Runtime `⇓ᴷ` of a value: the actual class of the heap object it points to. -/
inductive KJ0R (σ : Sigma) (L : Program) (H : Heap) (Γ : GTable) (v : Value) :
    Set ClassName → Prop
  | val : KJ0R σ L H Γ v (match v with
      | Value.loc l => match H l with
                       | some o => {o.cls}
                       | none   => ∅
      | _ => ∅)

/-- Runtime `calls` of the focus, emulating the calls actually performed by the
    machine.  Unlike the static `Calls0`, an application in this fragment is a
    runtime redex `ℓ(v)`: the function position is already a value, and the class
    whose `apply` gets invoked is the *actual* class of the object at `ℓ` in the
    heap `H` — read off via `KJ0R` — rather than the static over-approximation
    `⇓ᴷ`.  (When `v` is a `bool`, `KJ0R` yields `∅`.)  The argument is left a
    general expression so the judgment also covers the in-progress `v(E)`
    evaluation context. -/
inductive Calls0R (σ : Sigma) (L : Program) (H : Heap) (Γ : GTable) :
    Expr → Set ClassName → Prop
  | gproj {G i} : Calls0R σ L H Γ (Expr.gproj G i) ∅
  | proj {l i K} : Calls0R σ L H Γ l K → Calls0R σ L H Γ (Expr.proj l i) K
  | newC {D v₁ v₂ K₁ K₂} :
      Calls0R σ L H Γ v₁ K₁ → Calls0R σ L H Γ v₂ K₂ →
      Calls0R σ L H Γ (Expr.newC D v₁ v₂) (K₁ ∪ K₂)
  | app {l v K₁ K₂} :
      KJ0R σ L H Γ l K₁ → Calls0R σ L H Γ v K₂ →
      Calls0R σ L H Γ (Expr.app (Expr.val l) v) (K₁ ∪ K₂)
  | val {v} : Calls0R σ L H Γ (Expr.val v) ∅

/-! ### Heap/value typing -/

/-- Heap typing (Fld soundness): for every allocated object `H ℓ = C(v₁, v₂)`
    and field index `i`, if that field holds a location `ℓ'` pointing to an
    allocated object `H ℓ' = C'(…)`, then `C'` lies in `σ.Fldᵢ((G, C))` — the
    class set the analysis `⇓ᴷ` predicts for the `i`-th field of a `C`-object
    during the initialization of `G`.  Boolean values carry no class and are
    vacuously sound.  This is what makes `E-Proj` preserve `Inv`. -/
def FldInv (σ : Sigma) (H : Heap) (S: Stack) : Prop :=
  ∀ (S' : Stack) G l (C : ClassName) (v₁ v₂ : Value),
    S' <:+ S → Stack.TopInit S' G
    → H l = some (ClsIns.mk C G v₁ v₂)
      → ∀ i ℓ' c', (ClsIns.mk C G v₁ v₂).field i = Value.loc ℓ' → H ℓ' = some c'
        → c'.cls ∈ σ.Fld i G C

/-- Global-table typing: initialized global fields have their classes inside
    `GFldᵢ`. -/
def GTableInv (σ : Sigma) (H : Heap) (Γ : GTable) : Prop :=
  ∀ g o, Γ g = some o →
    ∀ i ℓ' c', o.field i = some (Value.loc ℓ') → H ℓ' = some c' →
      c'.cls ∈ σ.GFld i g

/-- Param soundness of the call stack: every call frame's argument has its class
    inside `σ.Param((G, D))` for the receiver's class `D`. -/
def ParamInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G C, S' <:+ S → S'.topInit = some (i, cfs, r)
    → Stack.TopInit S' G → Frame.call t p κ ∈ cfs → H t = some C
      → ∀ ℓ D, p = Value.loc ℓ → H ℓ = some D
        → D.cls ∈ σ.Param G C.cls

/-- Ret soundness of a returning value against the topmost call frame. -/
def RetInv (σ : Sigma) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ v, e = Expr.val v → ∀ G, Stack.TopInit S G
    → ∀ t p κ ℓ' D C, S.topCall = some (Frame.call t p κ)
      → H t = some D → v = Value.loc ℓ' → H ℓ' = some C
        → C.cls ∈ σ.Ret G D.cls

/-- RM soundness of the whole stack: in *every* suffix of `S`, the call frames
    sitting above the suffix's topmost init frame have their receiver's class in
    `σ.RM G` for that init frame's global `G`.  Quantifying over suffixes pairs
    each call frame with the nearest init frame below it, so every segment of
    the stack is constrained, not just the one above the topmost init frame. -/
def RMInv (σ : Sigma) (H: Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r f G l C, S' <:+ S → S'.topInit = some (i, cfs, r)
  → Stack.TopInit S' G → f ∈ cfs → f.loc = some l → H l = some C → C.cls ∈ σ.RM G

/-! ### The subject-reduction invariant -/

/-- The subject-reduction invariant `Inv σ L G` on configurations.  For a focus
    `e`: the globals it references stay in `Dep(G)`, the methods it can call stay
    in `RM(G)`, the call stack is `Param`-sound, and the heap / global table are
    value-class sound.  Because the runtime focus is `this`/`param`-free, the
    context-free judgments `GRef`/`Calls0` are the right ones. -/
def Inv (σ : Sigma) : Config → Prop
  | .mk H Γ S e =>
    ParamInv σ H S
    ∧ FldInv σ H S
    ∧ GTableInv σ H Γ
    ∧ RetInv σ H S e
    ∧ RMInv σ H S
  | .crash => True

/-- **Step 1 of Theorem 1.**  The invariant holds at the start configuration whose
    focus is an initialiser `eᵢ` of `G`.  The `Param`/`Fld`/`GTable`/`RM` bounds
    are properties of the start stack/heap/table alone and are assumed of the
    start configuration (from an empty start configuration they hold vacuously;
    they are preserved thereafter — e.g. by `inv_step_proj`).  `Ret` soundness
    holds because at the start of an initialisation the top of the stack is the
    init frame just pushed by `I-Push` (or the stack is empty), never a call
    frame — recorded as `hcall : S.topCall = none` — so no return is pending.
    The initialisers are `this`/`param`-free, recorded as `hpf₁`/`hpf₂`. -/
theorem inv_init {σ : Sigma} {e : Expr}
    {H : Heap} {Γ : GTable} {S : Stack}
    (hcall : S.topCall = none)
    (hparam : ParamInv σ H S) (hfld : FldInv σ H S)
    (hgtable : GTableInv σ H Γ) (hrm : RMInv σ H S) :
    Inv σ (.mk H Γ S e) := by
  refine ⟨hparam, hfld, hgtable, ?_, hrm⟩
  -- RetInv: the stack's top frame is not a call frame, so no return is pending.
  intro v hv G' hG t p κ ℓ' D C htc
  rw [hcall] at htc
  cases htc

theorem k_abstracts {σ : Sigma} {L : Program} {e : Expr} {H H' : Heap} {Γ Γ': GTable} {S : Stack}
    {l : Loc} {C D : ClsIns} {G : GlobName} {K : Set ClassName} (hσ : FixPoint σ L) (hG : Stack.TopInit S G) (hD : Stack.This S H D)
    (hinv : Inv σ (.mk H Γ S e)) (hre : RE σ L G D.cls e) (hred : Star L (.mk H Γ S e) (.mk H' Γ' S (Expr.val (Value.loc l))))
    (hH'l : H' l = some C) (hKj : KJC G σ L D.cls e K) :
    C.cls ∈ K := sorry

/-- **Step 2, E-Proj case.**  `Inv` is preserved by the `E-Proj` reduction
    `E[ℓ.i] → E[vᵢ]`.  -/
theorem inv_step_proj {σ : Sigma} {L : Program} {G : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {ℓ : Loc} {C : ClassName}
    {v₁ v₂ : Value} {i : Idx} (hG : Stack.TopInit S G)
    (hinv : Inv σ (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))) :
    Inv σ (.mk H Γ S (E.plug (Expr.val ((ClsIns.mk C G v₁ v₂).field i)))) := by
  obtain ⟨hparam, hfld, hgtable, hret, hrm⟩ := hinv
  -- `H`/`Γ`/`S` are untouched by E-Proj, so the four stack/heap bounds carry
  -- over verbatim; only `RetInv`, which mentions the focus, changes.
  refine ⟨hparam, hfld, hgtable, ?_, hrm⟩
  intro v hv G' hG' t p κ ℓ' D C' htc hHt hvloc hHl
  -- `E[w] = val v` forces `E = hole`: every other context wraps the hole in a
  -- non-`val` constructor.
  cases E with
  | hole =>
      -- Pending return: the contractum is a bare value directly above the call
      -- frame `(t, p, κ)`, and `RetInv` demands `C'.cls ∈ σ.Ret G' D.cls` for
      -- the projected field.  No component of the current `Inv` bounds a heap
      -- field's class against `σ.Ret` (a real `FldInv` would only give
      -- `σ.Fld i _ _`, with no `Fld ⊆ Ret` link), so this obligation is not
      -- derivable — `Inv` needs a focus-`⇓ᴷ`-vs-`Ret` component (via `KJ0R`)
      -- for pending returns.
      sorry
  | projc E j => simp [ECtx.plug] at hv
  | appL E e => simp [ECtx.plug] at hv
  | appR w E => simp [ECtx.plug] at hv
  | newL D' E e => simp [ECtx.plug] at hv
  | newR D' w E => simp [ECtx.plug] at hv

/-- **Step 2, E-GProj case.**  `Inv` is preserved by the `E-GProj` reduction
    `E[G₁.i] → E[v]` (reading an initialized global field; stated for an
    arbitrary contractum value `v`).  Heap, table and stack are unchanged.  The
    contractum's `⇓ᵍ`/`⇓ᴷ`/`calls` (`∅`/`∅`/`∅`) are *subsets* of the redex's
    (`{G₁}` / `GFldᵢ(G₁)` / `∅`), so the monotone plug lemmas transport the
    global and call bounds. -/
theorem inv_step_gproj {σ : Sigma} {L : Program} {G G₁ : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} {v : Value}
    (hinv : Inv σ (.mk H Γ S (E.plug (Expr.gproj G₁ i)))) :
    Inv σ (.mk H Γ S (E.plug (Expr.val v))) := by
  obtain ⟨hparam, hfld, hgtable, hret, hrm⟩ := hinv
  have hGr : GRef L (Expr.gproj G₁ i) {G₁} := .gproj
  have hGw : GRef L (Expr.val v) ∅ := .val
  have hKr : KJ0 G σ L (Expr.gproj G₁ i) (σ.GFld i G₁) := .gproj
  have hKw : KJ0 G σ L (Expr.val v) ∅ := .val
  have hCr : Calls0 G σ L (Expr.gproj G₁ i) ∅ := .gproj
  have hCw : Calls0 G σ L (Expr.val v) ∅ := .val
  refine ⟨hparam, hfld, hgtable, ?_, hrm⟩
  · intro Ge hG
    obtain ⟨G₀, hG₀, hsub⟩ := GRef.plug_mono hGr hGw (Set.empty_subset _) hG
    exact hsub.trans (hret G₀ hG₀)

theorem inv_step_app {σ : Sigma} {L : Program} {G G₁ : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {eₐ : Expr} {t : Loc} {l v p : Value}
    (hinv : Inv σ (.mk H Γ S (E.plug (Expr.app l v)))) :
    Inv σ (.mk H Γ S.push (Frame.call l p E) eₐ) := by
  obtain ⟨hparam, hfld, hgtable, hret, hrm⟩ := hinv
  have hGr : GRef L (Expr.gproj G₁ i) {G₁} := .gproj
  have hGw : GRef L (Expr.val v) ∅ := .val
  have hKr : KJ0 G σ L (Expr.gproj G₁ i) (σ.GFld i G₁) := .gproj
  have hKw : KJ0 G σ L (Expr.val v) ∅ := .val
  have hCr : Calls0 G σ L (Expr.gproj G₁ i) ∅ := .gproj
  have hCw : Calls0 G σ L (Expr.val v) ∅ := .val
  refine ⟨hparam, hfld, hgtable, ?_, hrm⟩
  · intro Ge hG
    obtain ⟨G₀, hG₀, hsub⟩ := GRef.plug_mono hGr hGw (Set.empty_subset _) hG
    exact hsub.trans (hret G₀ hG₀)

/-- **Theorem 1.** Under a fixpoint `σ` of the analysis, if `G`'s initialiser
    `eᵢ` can reduce to a configuration that accesses `G'.j`, then
    `G' ∈ Dep(G)`. -/
theorem dep_captures_dependencies
    {L : Program} {σ : Sigma} (hσ : FixPoint σ L)
    {G : GlobName} {e₁ e₂ : Expr} (hobj : Program.HasObject L G e₁ e₂)
    (hpf₁ : ParamFree e₁) (hpf₂ : ParamFree e₂)
    {eᵢ : Expr} (hsel : eᵢ = e₁ ∨ eᵢ = e₂)
    {H H' : Heap} {Γ Γ' : GTable} {E : ECtx} {S S' : Stack}
    {G' : GlobName} {j : Idx}
    (hred : Star L (.mk H Γ S eᵢ) (.mk H' Γ' S' (E.plug (Expr.gproj G' j)))) :
    G' ∈ Dep σ L G := by
  /-
    Proof outline (to be mechanised).

    1. `Inv σ L G` holds at the start configuration: `inv_init` (assuming the
       start heap/table/stack are sound; from an empty start configuration this
       is vacuous).

    2. `Inv` is preserved by every `Step` rule (induction on `Star`):
         • E-Proj:  `inv_step_proj`.
         • E-GProj: `inv_step_gproj`.
         • E-AppBeta `ℓ(v) → body`: the applied class `C = cls(ℓ)` lies in the
           K-set of the function position, hence in `RM(G)` (`hσ.rm_closed`);
           the body is a reachable expression (`RE.body`), so its globals are
           in `Dep(G)` by `GRef.subset_dep` and its calls in `RM(G)` by
           `hσ.rm_closed`; the pushed call frame is `Param`-sound by
           `hσ.param_re`.  This case needs the heap-aware judgments
           `KJ0R`/`Calls0R` to name the actual callee class.
         • E-Ret: the returned value's class is bounded by `Ret`
           (`hσ.ret_init`, `RetInv`), so plugging it into the saved context
           `κ` keeps the bounds.
         • E-NewAlloc: allocation introduces no new globals and no new calls;
           `FldInv` is extended using `hσ.fld_re` at the reachable `new`.
         • I-Push / I-Next / I-Pop: the nested initialisation of a global `G₁`
           refocuses on `G₁`'s own initialisers.  Relative to `Dep(G)` this
           uses `Dep`-transitivity (`Dep.trans`, Step 2d): `G₁ ∈ Dep(G)` by the
           invariant at the triggering access, the new focus's globals lie in
           `Dep(G₁)` (by `inv_init` for `G₁`), hence in `Dep(G)`; tracking this
           across the stack is the paper's Lemma 3.

    3. At the final configuration the focus is `E.plug (Expr.gproj G' j)`,
       whose `⇓ᵍ` contains `G'` (the `gproj` leaf, propagated through `E`).
       By `Inv` that global set is `⊆ Dep σ L G`, so `G' ∈ Dep σ L G`.
  -/
  sorry

end Proof
