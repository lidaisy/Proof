import Proof.Syntax

namespace Proof

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

structure Sigma where
  Param : GlobName → ClassName → Set OPair
  Fld₁  : GlobName → ClassName → Set OPair
  Fld₂  : GlobName → ClassName → Set OPair
  Ret   : GlobName → ClassName → Set OPair
  GFld₁ : GlobName → Set OPair
  GFld₂ : GlobName → Set OPair
  RM    : GlobName → Set ClassName
  This  : GlobName → ClassName → Set GlobName

def Sigma.Fld (σ : Sigma) : Idx → GlobName → ClassName → Set OPair
  | Idx.one => σ.Fld₁
  | Idx.two => σ.Fld₂

def Sigma.GFld (σ : Sigma) : Idx → GlobName → Set OPair
  | Idx.one => σ.GFld₁
  | Idx.two => σ.GFld₂

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

inductive KJ0 (G : GlobName) (σ : Sigma) (L : Program) : Expr → Set OPair → Prop
  | proj {e i K} :
      KJ0 G σ L e K → KJ0 G σ L (Expr.proj e i) (⋃ p ∈ K, σ.Fld i p.1 p.2)
  | gproj {G₀ i} : KJ0 G σ L (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJ0 G σ L (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJ0 G σ L e₁ K₁ → KJ0 G σ L (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret G p.2)
  | val {v} : KJ0 G σ L (Expr.val v) ∅

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

abbrev Ctx := Option ClassName

def KJC (G : GlobName) (σ : Sigma) (L : Program) : Ctx → Expr → Set OPair → Prop
  | none   => KJ0 G σ L
  | some C => KJ G C σ L

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

inductive RE (σ : Sigma) (L : Program) (G : GlobName) : Ctx → Expr → Prop
  | init₁ {e₁ e₂} : Program.HasObject L G e₁ e₂ → RE σ L G none e₁
  | init₂ {e₁ e₂} : Program.HasObject L G e₁ e₂ → RE σ L G none e₂
  | body {C e} : C ∈ σ.RM G → Program.HasClass L C e → RE σ L G (some C) e
  | proj {c e i} : RE σ L G c (Expr.proj e i) → RE σ L G c e
  | newC₁ {c D e₁ e₂} : RE σ L G c (Expr.newC D e₁ e₂) → RE σ L G c e₁
  | newC₂ {c D e₁ e₂} : RE σ L G c (Expr.newC D e₁ e₂) → RE σ L G c e₂
  | app₁ {c e₁ e₂} : RE σ L G c (Expr.app e₁ e₂) → RE σ L G c e₁
  | app₂ {c e₁ e₂} : RE σ L G c (Expr.app e₁ e₂) → RE σ L G c e₂

inductive DepJ (σ : Sigma) (L : Program) : GlobName → GlobName → Prop
  | direct {G G₀ : GlobName} {c : Ctx} {i : Idx} :
      RE σ L G c (Expr.gproj G₀ i) → DepJ σ L G G₀
  | trans {G G' G₀ : GlobName} :
      DepJ σ L G G' → DepJ σ L G' G₀ → DepJ σ L G G₀

def Dep (σ : Sigma) (L : Program) (G : GlobName) : Set GlobName :=
  { G₀ | DepJ σ L G G₀ }

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
