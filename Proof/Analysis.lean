import Proof.Syntax

/-
  Abstract interpretation (paper §"Abstract Interpretation").

  The abstract state is
      Σ = (Param, Fld₁, Fld₂, GFld₁, GFld₂, Ret, RM)
  (paper §"Step 1: Class Point-To Domain").  `RE` and `Dep` are *not*
  components of `σ`:

    * `RE σ L G` (Step 2c) is a helper judgment — the expressions reachable
      from the initialization of `G`, derived from `σ.RM`;
    * `Dep σ L G` (Step 2d) is a helper judgment: the transitive closure of
      the direct global accesses read off `RE`.

  `FixPoint σ L` asserts that `σ` is closed under the inference rules of
  Steps 2a–2f, i.e. `σ` is a sound post-fixpoint of the analysis; this is the
  form in which the analysis is consumed by Theorem 1.
-/

namespace Proof

/-- The abstract state `Σ = (Param, Fld₁, Fld₂, GFld₁, GFld₂, Ret, RM)`.
    `Param`, `Fldᵢ` and `Ret` are indexed by the global object `G` whose
    initialization is being analysed as well as by a class
    (paper: `𝔾 × ℂ → P(ℂ)`); `GFldᵢ` and `RM` are indexed by `G` alone and
    yield sets of classes. -/
structure Sigma where
  Param : GlobName → ClassName → Set ClassName
  Fld₁  : GlobName → ClassName → Set ClassName
  Fld₂  : GlobName → ClassName → Set ClassName
  Ret   : GlobName → ClassName → Set ClassName
  GFld₁ : GlobName → Set ClassName
  GFld₂ : GlobName → Set ClassName
  RM    : GlobName → Set ClassName

/-- `Fldᵢ((G, C))`. -/
def Sigma.Fld (σ : Sigma) : Idx → GlobName → ClassName → Set ClassName
  | Idx.one => σ.Fld₁
  | Idx.two => σ.Fld₂

/-- `GFldᵢ(G)`. -/
def Sigma.GFld (σ : Sigma) : Idx → GlobName → Set ClassName
  | Idx.one => σ.GFld₁
  | Idx.two => σ.GFld₂

/-! ### Step 1: class point-to judgment `G; C; σ; L̄ ⊢ e ⇓ᴷ K`

  Syntax directed.  The `this`/`param` cases use the enclosing class `C`; the
  whole judgment is relative to the global `G` under initialization.  (Values
  occur only in runtime foci, never in source programs; they carry no
  statically-tracked class, so `⇓ᴷ` assigns them `∅`.) -/
inductive KJ (G : GlobName) (C : ClassName) (σ : Sigma) (L : Program) :
    Expr → Set ClassName → Prop
  | thisE  : KJ G C σ L Expr.thisE {C}
  | paramE : KJ G C σ L Expr.paramE (σ.Param G C)
  | proj {e i K} :
      KJ G C σ L e K → KJ G C σ L (Expr.proj e i) (⋃ D ∈ K, σ.Fld i G D)
  | gproj {G₀ i} : KJ G C σ L (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJ G C σ L (Expr.newC D e₁ e₂) {D}
  | app {e₁ e₂ K₁} :
      KJ G C σ L e₁ K₁ → KJ G C σ L (Expr.app e₁ e₂) (⋃ D ∈ K₁, σ.Ret G D)
  | val {v} : KJ G C σ L (Expr.val v) ∅

/-- `⇓ᴷ` in the empty class context (the paper's `G; ·; σ; L̄ ⊢ e ⇓ᴷ K`):
    object initializers occur outside any class body, so they contain no
    `this`/`param` and the rules consulting the class position never apply. -/
inductive KJ0 (G : GlobName) (σ : Sigma) (L : Program) : Expr → Set ClassName → Prop
  | proj {e i K} :
      KJ0 G σ L e K → KJ0 G σ L (Expr.proj e i) (⋃ D ∈ K, σ.Fld i G D)
  | gproj {G₀ i} : KJ0 G σ L (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJ0 G σ L (Expr.newC D e₁ e₂) {D}
  | app {e₁ e₂ K₁} :
      KJ0 G σ L e₁ K₁ → KJ0 G σ L (Expr.app e₁ e₂) (⋃ D ∈ K₁, σ.Ret G D)
  | val {v} : KJ0 G σ L (Expr.val v) ∅

/-! ### Step 2a: directly called methods `G; C; σ; L̄ ⊢ e calls K` -/
inductive Calls (G : GlobName) (C : ClassName) (σ : Sigma) (L : Program) :
    Expr → Set ClassName → Prop
  | thisE  : Calls G C σ L Expr.thisE ∅
  | paramE : Calls G C σ L Expr.paramE ∅
  | gproj {G₀ i} : Calls G C σ L (Expr.gproj G₀ i) ∅
  | proj {e i K} : Calls G C σ L e K → Calls G C σ L (Expr.proj e i) K
  | newC {D e₁ e₂ K₁ K₂} :
      Calls G C σ L e₁ K₁ → Calls G C σ L e₂ K₂ →
      Calls G C σ L (Expr.newC D e₁ e₂) (K₁ ∪ K₂)
  | app {e₁ e₂ K₁ K₂ K₃} :
      KJ G C σ L e₁ K₁ → Calls G C σ L e₁ K₂ → Calls G C σ L e₂ K₃ →
      Calls G C σ L (Expr.app e₁ e₂) ((K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls G C σ L (Expr.val v) ∅

/-- `calls` in the empty class context, for object initializers. -/
inductive Calls0 (G : GlobName) (σ : Sigma) (L : Program) : Expr → Set ClassName → Prop
  | gproj {G₀ i} : Calls0 G σ L (Expr.gproj G₀ i) ∅
  | proj {e i K} : Calls0 G σ L e K → Calls0 G σ L (Expr.proj e i) K
  | newC {D e₁ e₂ K₁ K₂} :
      Calls0 G σ L e₁ K₁ → Calls0 G σ L e₂ K₂ →
      Calls0 G σ L (Expr.newC D e₁ e₂) (K₁ ∪ K₂)
  | app {e₁ e₂ K₁ K₂ K₃} :
      KJ0 G σ L e₁ K₁ → Calls0 G σ L e₁ K₂ → Calls0 G σ L e₂ K₃ →
      Calls0 G σ L (Expr.app e₁ e₂) ((K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls0 G σ L (Expr.val v) ∅

/-- The optional class context an expression lives in: `some C` for code in the
    body of `C.apply`, `none` for initializer code (the paper's `·`). -/
abbrev Ctx := Option ClassName

/-- `⇓ᴷ` in an optional class context: dispatches to `KJ0` (initializer code)
    or `KJ` (method-body code). -/
def KJC (G : GlobName) (σ : Sigma) (L : Program) : Ctx → Expr → Set ClassName → Prop
  | none   => KJ0 G σ L
  | some C => KJ G C σ L

/-! ### Step 2c: reachable expressions `e ∈ RE(G)`

  A helper judgment (not a component of `σ`): the expressions whose evaluation
  the initialization of `G` may trigger.  Each expression is tagged with the
  class context it lives in (`Ctx`), so the constraint rules below can invoke
  `⇓ᴷ` in the right context.  `RE` is seeded by the bodies of the reachable
  methods `σ.RM G` and closed under subexpressions.

  Note: we additionally seed `RE` with `G`'s own initializers
  (`init₁`/`init₂`).  The paper's Step 2c omits this rule, but without it
  `Dep(G)` misses the globals referenced directly by the initializers and
  Theorem 1 fails. -/
inductive RE (σ : Sigma) (L : Program) (G : GlobName) : Ctx → Expr → Prop
  | init₁ {e₁ e₂} : Program.HasObject L G e₁ e₂ → RE σ L G none e₁
  | init₂ {e₁ e₂} : Program.HasObject L G e₁ e₂ → RE σ L G none e₂
  | body {C e} : C ∈ σ.RM G → Program.HasClass L C e → RE σ L G (some C) e
  | proj {c e i} : RE σ L G c (Expr.proj e i) → RE σ L G c e
  | newC₁ {c D e₁ e₂} : RE σ L G c (Expr.newC D e₁ e₂) → RE σ L G c e₁
  | newC₂ {c D e₁ e₂} : RE σ L G c (Expr.newC D e₁ e₂) → RE σ L G c e₂
  | app₁ {c e₁ e₂} : RE σ L G c (Expr.app e₁ e₂) → RE σ L G c e₁
  | app₂ {c e₁ e₂} : RE σ L G c (Expr.app e₁ e₂) → RE σ L G c e₂

/-! ### Step 2d: computing `Dep(G)`

  A helper judgment, not a component of `σ`: `G₀ ∈ Dep(G)` iff some reachable
  expression accesses `G₀.i` directly, or transitively so
  (`G' ∈ Dep(G) → Dep(G') ⊆ Dep(G)`). -/
inductive DepJ (σ : Sigma) (L : Program) : GlobName → GlobName → Prop
  /-- A reachable expression accesses `G₀.i` directly. -/
  | direct {G G₀ : GlobName} {c : Ctx} {i : Idx} :
      RE σ L G c (Expr.gproj G₀ i) → DepJ σ L G G₀
  /-- Transitivity: `G' ∈ Dep(G) → Dep(G') ⊆ Dep(G)`. -/
  | trans {G G' G₀ : GlobName} :
      DepJ σ L G G' → DepJ σ L G' G₀ → DepJ σ L G G₀

/-- `Dep(G)`, as a set of globals. -/
def Dep (σ : Sigma) (L : Program) (G : GlobName) : Set GlobName :=
  { G₀ | DepJ σ L G G₀ }

/-- The Step 2d transitivity rule, phrased on `Dep`:
    `G' ∈ Dep(G) → Dep(G') ⊆ Dep(G)`. -/
theorem Dep.trans {σ : Sigma} {L : Program} {G G' : GlobName}
    (h : G' ∈ Dep σ L G) : Dep σ L G' ⊆ Dep σ L G :=
  fun _ h' => DepJ.trans h h'

/-! ### The analysis fixpoint

  `FixPoint σ L` asserts that `σ` is closed under the remaining inference
  rules: `RM` seeding and closure (Step 2b), `Ret` (Step 2e), `GFldᵢ`
  (Step 2f), and the `Fldᵢ`/`Param` constraints over the reachable
  expressions (Step 2f, "Updating Fields and Param Constraints"). -/
structure FixPoint (σ : Sigma) (L : Program) : Prop where
  /-- Step 2b (seeding): methods called by `G`'s own initializers are reachable. -/
  rm_init : ∀ {G e₁ e₂ K₁ K₂}, Program.HasObject L G e₁ e₂ →
      Calls0 G σ L e₁ K₁ → Calls0 G σ L e₂ K₂ → (K₁ ∪ K₂) ⊆ σ.RM G
  /-- Step 2b (closure): `RM` is closed under the `calls` of reachable bodies. -/
  rm_closed : ∀ {G C body K}, C ∈ σ.RM G → Program.HasClass L C body →
      Calls G C σ L body K → K ⊆ σ.RM G
  /-- Step 2e: `Ret((G, C))` contains the `⇓ᴷ` of `C.apply`'s body. -/
  ret_init : ∀ {G C e K}, Program.HasClass L C e →
      KJ G C σ L e K → K ⊆ σ.Ret G C
  /-- Step 2f: `GFldᵢ(G)` contains the `⇓ᴷ` of `G`'s initializers. -/
  gfld_init : ∀ {G e₁ e₂ K₁ K₂}, Program.HasObject L G e₁ e₂ →
      KJ0 G σ L e₁ K₁ → KJ0 G σ L e₂ K₂ →
      K₁ ⊆ σ.GFld Idx.one G ∧ K₂ ⊆ σ.GFld Idx.two G
  /-- Step 2f (constraints): `Fldᵢ((G, D))` bounds for every reachable
      `new D(e₁, e₂) ∈ RE(G)`. -/
  fld_re : ∀ {G c D e₁ e₂ K₁ K₂}, RE σ L G c (Expr.newC D e₁ e₂) →
      KJC G σ L c e₁ K₁ → KJC G σ L c e₂ K₂ →
      K₁ ⊆ σ.Fld Idx.one G D ∧ K₂ ⊆ σ.Fld Idx.two G D
  /-- Step 2f (constraints): `Param((G, D))` bounds for every reachable
      application `e₁(e₂) ∈ RE(G)` with `D` in the `⇓ᴷ` of `e₁`. -/
  param_re : ∀ {G c e₁ e₂ K₁ K₂}, RE σ L G c (Expr.app e₁ e₂) →
      KJC G σ L c e₁ K₁ → KJC G σ L c e₂ K₂ →
      ∀ D ∈ K₁, K₂ ⊆ σ.Param G D

end Proof
