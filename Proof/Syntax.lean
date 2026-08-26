import Mathlib.Data.Set.Lattice

/-
  Syntax (paper §"Syntax").

  A small core calculus with classes, object-level globals, and heap-allocated
  objects.  Following the paper:

    * class / global names are drawn from `String`;
    * every class / object has exactly two fields, indexed by `i ∈ {1,2}`;
    * the only term variables are `this` and `param`.
-/

namespace Proof

abbrev ClassName := String
abbrev GlobName  := String
abbrev Loc       := Nat

/-- Field index `i ∈ {1,2}`. -/
inductive Idx
  | one
  | two
  deriving DecidableEq, Repr

/-- Values `v ::= ℓ | true | false` (paper "Grammar").

    Values form their own syntactic category, separate from expressions; they are
    injected into expressions by the `Expr.val` constructor below. -/
inductive Value
  | loc   (ℓ : Loc)                         -- ℓ
  | btrue                                   -- true
  | bfalse                                  -- false
  deriving DecidableEq, Repr

/-- Expressions `e` (paper "Grammar").

    A value `v` becomes an expression via `val v`; this is the only way values
    enter the expression grammar. -/
inductive Expr
  | thisE                                   -- this
  | paramE                                  -- param
  | newC  (C : ClassName) (e₁ e₂ : Expr)    -- new C(e, e)
  | app   (e₁ e₂ : Expr)                    -- e(e)
  | proj  (e : Expr) (i : Idx)              -- e.i
  | gproj (G : GlobName) (i : Idx)          -- G.i
  | val   (v : Value)                       -- v  (value as expression)
  deriving Repr

/-- Values inject into expressions, so a `Value` may be used wherever an `Expr`
    is expected. -/
instance : Coe Value Expr := ⟨Expr.val⟩

/-- A class definition
    `class C(val 1, val 2) { def apply(param) = body }`.
    The two value fields are positional, so only the body is recorded. -/
structure ClassDef where
  name : ClassName
  body : Expr
  deriving Repr

/-- An object (global) definition `object G { val 1 = init₁; val 2 = init₂ }`. -/
structure ObjDef where
  name  : GlobName
  init₁ : Expr
  init₂ : Expr
  deriving Repr

/-- A top-level definition `L`. -/
inductive Def
  | cls (d : ClassDef)
  | obj (d : ObjDef)
  deriving Repr

/-- A program is the sequence of top-level definitions `L̄`
    (the trailing top-level expression `e` is supplied separately by the
    semantics / theorems). -/
abbrev Program := List Def

namespace Program

/-- `class C(val 1, val 2) { def apply(param) = body } ∈ L̄`. -/
def HasClass (L : Program) (C : ClassName) (body : Expr) : Prop :=
  Def.cls ⟨C, body⟩ ∈ L

/-- `object G { val 1 = init₁; val 2 = init₂ } ∈ L̄`. -/
def HasObject (L : Program) (G : GlobName) (init₁ init₂ : Expr) : Prop :=
  Def.obj ⟨G, init₁, init₂⟩ ∈ L

def GlobNames (L : Program) : List GlobName :=
  match L with
  | [] => []
  | d :: ds => match d with
                | Def.cls _ => GlobNames ds
                | Def.obj o => o.name :: GlobNames ds

/-- `L.HasMain`: the program defines at least one object, so a run has an
    object to start with.  This is a *well-formedness hypothesis* on `L`, to be
    discharged (or assumed) at each theorem that mentions `Config.start`.

    It replaces the former `axiom HasMain {L Gₘ e} : L.HasObject Gₘ e btrue`,
    which was unsound in two separate ways.  It was outright inconsistent —
    instantiating it at `L := []` gives `Def.obj _ ∈ []`, hence `False` — and
    even read charitably it asserted that *every* program contains an object of
    *every* name with *any* first initialiser, which hands `Analysis.RE.init₁`
    an arbitrary expression and so makes vacuous any soundness statement that
    consumes an `RE` derivation. -/
def HasMain (L : Program) : Prop := L.GlobNames ≠ []

/-- The intended way to supply `HasMain`: exhibit the main object. -/
theorem HasMain.of_hasObject {L : Program} {G : GlobName} {e₁ e₂ : Expr}
    (h : L.HasObject G e₁ e₂) : L.HasMain := by
  show L.GlobNames ≠ []
  induction L with
  | nil => cases h
  | cons d ds ih =>
      rcases List.mem_cons.1 h with rfl | h'
      · simp [GlobNames]
      · cases d <;> simp [GlobNames, ih h']

/-- `HasMain` says exactly that there is an object definition. -/
theorem HasMain.exists_hasObject {L : Program} (h : L.HasMain) :
    ∃ G e₁ e₂, L.HasObject G e₁ e₂ := by
  induction L with
  | nil => exact absurd rfl h
  | cons d ds ih =>
      match d with
      | Def.cls c =>
          obtain ⟨G, e₁, e₂, hmem⟩ := ih (by simpa [GlobNames] using h)
          exact ⟨G, e₁, e₂, List.mem_cons_of_mem _ hmem⟩
      | Def.obj o => exact ⟨o.name, o.init₁, o.init₂, List.mem_cons_self ..⟩

end Program

end Proof
