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

inductive Expr
  | thisE                                   -- this
  | paramE                                  -- param
  | newC  (C : ClassName) (e₁ e₂ : Expr)    -- new C(e, e)
  | app   (e₁ e₂ : Expr)                    -- e(e)
  | proj  (e : Expr) (i : Idx)              -- e.i
  | gproj (G : GlobName) (i : Idx)          -- G.i
  | val   (v : Value)                       -- v  (value as expression)
  deriving Repr

instance : Coe Value Expr := ⟨Expr.val⟩

structure ClassDef where
  name : ClassName
  body : Expr
  deriving Repr

structure ObjDef where
  name  : GlobName
  init₁ : Expr
  init₂ : Expr
  deriving Repr

inductive Def
  | cls (d : ClassDef)
  | obj (d : ObjDef)
  deriving Repr

abbrev Program := List Def

namespace Program

/-- `class C(val 1, val 2) { def apply(param) = body } ∈ L̄`. -/
def HasClass (L : Program) (C : ClassName) (body : Expr) : Prop :=
  Def.cls ⟨C, body⟩ ∈ L

def HasObject (L : Program) (G : GlobName) (init₁ init₂ : Expr) : Prop :=
  Def.obj ⟨G, init₁, init₂⟩ ∈ L

def GlobNames (L : Program) : List GlobName :=
  match L with
  | [] => []
  | d :: ds => match d with
                | Def.cls _ => GlobNames ds
                | Def.obj o => o.name :: GlobNames ds

def WellFormed (L : Program) : Prop := L.GlobNames ≠ [] ∧ List.Nodup (GlobNames L)

end Program

end Proof
