import Proof.Syntax

/-
  Abstract interpretation (paper §"Abstract Interpretation").

  The abstract state is
      Σ = (Param, Fld₁, Fld₂, GFld₁, GFld₂, Ret, RM, This)
  (paper §"Abstract Interpretation").  Abstract values are *owner pairs*
  `(G, C) ∈ 𝔾 × ℂ` (paper §"Notation"): a class `C` is *owned* by the global
  object `G` if an instance of `C` is created during the initialization of
  `G`.  In the range of every component the `𝔾` position is the owner; this
  is what lets field lookups cross global boundaries (the owner-pair domain
  replaces the classes-only domain refuted on 2026-07-09 by the cross-global
  `Fld`-flow counterexample).

  `RE` and `Dep` are *not* components of `σ`:

    * `RE σ L G` (Step 2c) is a helper judgment — the expressions reachable
      from the initialization of `G`, derived from `σ.RM`;
    * `Dep σ L G` (Step 2d) is a helper judgment: the transitive closure of
      the direct global accesses read off `RE`.

  `FixPoint σ L` asserts that `σ` is closed under the inference rules of
  Steps 2a–2g, i.e. `σ` is a sound post-fixpoint of the analysis; this is the
  form in which the analysis is consumed by Theorem 1.
-/

namespace Proof

/-- An *owner pair* `(G, C) ∈ 𝔾 × ℂ` (paper §"Notation"): the class `C`
    together with its owner `G` — the global object during whose
    initialization the `C`-instance was created. -/
abbrev OPair := GlobName × ClassName

/-- `classes(K)` (paper `classes(·)`): the class components of a
    set of owner pairs. -/
def classes (K : Set OPair) : Set ClassName := Prod.snd '' K

def objects (K : Set OPair) : Set GlobName := Prod.fst '' K

@[simp] theorem mem_classes {K : Set OPair} {D : ClassName} :
    D ∈ classes K ↔ ∃ G, (G, D) ∈ K := by
  constructor
  · rintro ⟨⟨G, D'⟩, hp, rfl⟩; exact ⟨G, hp⟩
  · rintro ⟨G, hG⟩; exact ⟨(G, D), hG, rfl⟩

/-- The abstract state `Σ = (Param, Fld₁, Fld₂, GFld₁, GFld₂, Ret, RM, This)`.
    `Param`, `Fldᵢ` and `Ret` are indexed by the global object `G` whose
    initialization is being analysed as well as by a class, and yield sets of
    owner pairs (paper: `𝔾 → ℂ → P(𝔾 × ℂ)`; for `Fldᵢ` the domain pair
    `(G, C)` is itself an owner pair — `G` owns the `C`-object whose fields
    are described).  `GFldᵢ` is indexed by `G` alone and yields owner pairs;
    `RM` yields plain classes (`𝔾 → P(ℂ)`); `This` yields the possible
    *owners* of the receiver (`𝔾 → ℂ → P(𝔾)`). -/
structure Sigma where
  Param : GlobName → ClassName → Set OPair
  Fld₁  : GlobName → ClassName → Set OPair
  Fld₂  : GlobName → ClassName → Set OPair
  Ret   : GlobName → ClassName → Set OPair
  GFld₁ : GlobName → Set OPair
  GFld₂ : GlobName → Set OPair
  RM    : GlobName → Set ClassName
  This  : GlobName → ClassName → Set GlobName

/-- `Fldᵢ((G, C))` — the owner pairs the `i`-th field of a `C`-object owned
    by `G` may point to. -/
def Sigma.Fld (σ : Sigma) : Idx → GlobName → ClassName → Set OPair
  | Idx.one => σ.Fld₁
  | Idx.two => σ.Fld₂

/-- `GFldᵢ(G)` — the owner pairs the `i`-th field of the global `G` may
    point to. -/
def Sigma.GFld (σ : Sigma) : Idx → GlobName → Set OPair
  | Idx.one => σ.GFld₁
  | Idx.two => σ.GFld₂

/-! ### Step 1: class point-to judgment `G; C; σ; L̄ ⊢ e ⇓ᴷ K`

  Syntax directed; `K` is a set of owner pairs.  The `this`/`param` cases use
  the enclosing class `C`; the whole judgment is relative to the global `G`
  under initialization.  (Values occur only in runtime foci, never in source
  programs; they carry no statically-tracked class, so `⇓ᴷ` assigns them `∅`.)

  Two deliberate deviations from the paper's literal rules, both flagged as
  paper gaps:

    * `proj`: the paper writes `e.i ⇓ᴷ ⋃_{D ∈ class(K_e)} Fldᵢ((G, D))`,
      pairing every class with the *ambient* `G` and discarding the owner
      carried in `K_e`.  That literal reading reinstates the Lean-refuted
      cross-global counterexample the owner pairs were introduced to fix
      (an object owned by `g₀` flowing into `g₁`'s init would be projected
      through `Fldᵢ((g₁, ·))`).  We use the owner from the pair:
      `⋃_{(G', D) ∈ K_e} Fldᵢ((G', D))`.
    * `gproj`: the paper writes `G.i ⇓ᴷ GFldᵢ(G)` for the ambient `G` only;
      as before we generalize to an arbitrary accessed global `G₀`, the only
      total reading. -/
inductive KJ (G : GlobName) (C : ClassName) (σ : Sigma) (L : Program) :
    Expr → Set OPair → Prop
  | thisE  : KJ G C σ L Expr.thisE (⋃ G' ∈ σ.This G C, {(G', C)})
  | paramE : KJ G C σ L Expr.paramE (σ.Param G C)
  | proj {e i K} :
      KJ G C σ L e K → KJ G C σ L (Expr.proj e i) (⋃ p ∈ K, σ.Fld i p.1 p.2)
  | gproj {G₀ i} : KJ G C σ L (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJ G C σ L (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJ G C σ L e₁ K₁ → KJ G C σ L (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret G p.2)
  | val {v} : KJ G C σ L (Expr.val v) ∅

/-- `⇓ᴷ` in the empty class context (the paper's `G; ·; σ; L̄ ⊢ e ⇓ᴷ K`):
    object initializers occur outside any class body, so they contain no
    `this`/`param` and the rules consulting the class position never apply. -/
inductive KJ0 (G : GlobName) (σ : Sigma) (L : Program) : Expr → Set OPair → Prop
  | proj {e i K} :
      KJ0 G σ L e K → KJ0 G σ L (Expr.proj e i) (⋃ p ∈ K, σ.Fld i p.1 p.2)
  | gproj {G₀ i} : KJ0 G σ L (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJ0 G σ L (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJ0 G σ L e₁ K₁ → KJ0 G σ L (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret G p.2)
  | val {v} : KJ0 G σ L (Expr.val v) ∅

/-! ### Step 2a: directly called methods `G; C; σ; L̄ ⊢ e calls K`

  `K` is a set of plain classes (it feeds `RM : 𝔾 → P(ℂ)`, Step 2b); in the
  `app` rule the owner pairs of the function position's `⇓ᴷ` are projected to
  their class components via `classes`. -/
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
      Calls G C σ L (Expr.app e₁ e₂) ((classes K₁ ∪ K₂) ∪ K₃)
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
      Calls0 G σ L (Expr.app e₁ e₂) ((classes K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls0 G σ L (Expr.val v) ∅

/-- The optional class context an expression lives in: `some C` for code in the
    body of `C.apply`, `none` for initializer code (the paper's `·`). -/
abbrev Ctx := Option ClassName

/-- `⇓ᴷ` in an optional class context: dispatches to `KJ0` (initializer code)
    or `KJ` (method-body code). -/
def KJC (G : GlobName) (σ : Sigma) (L : Program) : Ctx → Expr → Set OPair → Prop
  | none   => KJ0 G σ L
  | some C => KJ G C σ L

/-! The structural `⇓ᴷ` rules are shared by `KJ0` and `KJ`, so they lift to
    `KJC` in an arbitrary context. -/

theorem KJC.proj {G : GlobName} {σ : Sigma} {L : Program} {c : Ctx} {e : Expr} {i : Idx}
    {K : Set OPair} (h : KJC G σ L c e K) :
    KJC G σ L c (Expr.proj e i) (⋃ p ∈ K, σ.Fld i p.1 p.2) := by
  cases c with
  | none => exact KJ0.proj h
  | some C => exact KJ.proj h

theorem KJC.gproj {G G₀ : GlobName} {σ : Sigma} {L : Program} {c : Ctx} {i : Idx} :
    KJC G σ L c (Expr.gproj G₀ i) (σ.GFld i G₀) := by
  cases c with
  | none => exact KJ0.gproj
  | some C => exact KJ.gproj

theorem KJC.newC {G : GlobName} {σ : Sigma} {L : Program} {c : Ctx} {D : ClassName}
    {e₁ e₂ : Expr} : KJC G σ L c (Expr.newC D e₁ e₂) {(G, D)} := by
  cases c with
  | none => exact KJ0.newC
  | some C => exact KJ.newC

theorem KJC.app {G : GlobName} {σ : Sigma} {L : Program} {c : Ctx} {e₁ e₂ : Expr}
    {K₁ : Set OPair} (h : KJC G σ L c e₁ K₁) :
    KJC G σ L c (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret G p.2) := by
  cases c with
  | none => exact KJ0.app h
  | some C => exact KJ.app h

/-! ### Step 2c: reachable expressions `e ∈ RE(G)`  -/
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

/-! ### The analysis fixpoint -/
structure FixPoint (σ : Sigma) (L : Program) : Prop where
  rm_init : ∀ {G e₁ e₂ K₁ K₂}, Program.HasObject L G e₁ e₂ →
      Calls0 G σ L e₁ K₁ → Calls0 G σ L e₂ K₂ → (K₁ ∪ K₂) ⊆ σ.RM G
  rm_closed : ∀ {G C body K}, C ∈ σ.RM G → Program.HasClass L C body →
      Calls G C σ L body K → K ⊆ σ.RM G
  ret_init : ∀ {G C e K}, Program.HasClass L C e →
      KJ G C σ L e K → K ⊆ σ.Ret G C
  gfld_init_one : ∀ {G e₁ e₂ K₁}, Program.HasObject L G e₁ e₂ →
      KJ0 G σ L e₁ K₁ → K₁ ⊆ σ.GFld Idx.one G
  gfld_init_two : ∀ {G e₁ e₂ K₂}, Program.HasObject L G e₁ e₂ →
      KJ0 G σ L e₂ K₂ → K₂ ⊆ σ.GFld Idx.two G
  fld_re : ∀ {G c D e₁ e₂ K₁ K₂}, RE σ L G c (Expr.newC D e₁ e₂) →
      KJC G σ L c e₁ K₁ → KJC G σ L c e₂ K₂ →
      K₁ ⊆ σ.Fld Idx.one G D ∧ K₂ ⊆ σ.Fld Idx.two G D
  param_re : ∀ {G c e₁ e₂ K₁ K₂}, RE σ L G c (Expr.app e₁ e₂) →
      KJC G σ L c e₁ K₁ → KJC G σ L c e₂ K₂ →
      ∀ D ∈ classes K₁, K₂ ⊆ σ.Param G D
  this_re : ∀ {G G₀ c K₁ e₁ e₂}, RE σ L G c (Expr.app e₁ e₂) → KJC G σ L c e₁ K₁ →
      G₀ = objects K₁ → ∀ D ∈ classes K₁, G₀ ⊆ σ.This G D

end Proof
