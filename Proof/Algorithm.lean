import Proof.Syntax
import Proof.Semantics
import Proof.Analysis

namespace Algorithm

open Proof (GlobName ClassName OPair Idx Program Expr classes)

structure State (G : GlobName) where
  Param : ClassName → Set OPair
  Fld₁  : ClassName → Set OPair
  Fld₂  : ClassName → Set OPair
  Ret   : ClassName → Set OPair
  GFld₁ : Set OPair
  GFld₂ : Set OPair
  RM    : Set ClassName
  This  : ClassName → Set GlobName

def State.Fld {G : GlobName} (σ : State G) : Idx → ClassName → Set OPair
  | Idx.one => σ.Fld₁
  | Idx.two => σ.Fld₂

def State.GFld {G : GlobName} (σ : State G) : Idx → Set OPair
  | Idx.one => σ.GFld₁
  | Idx.two => σ.GFld₂

abbrev FixPoint := (G : GlobName) → Option (State G)

def InFixPoint (F : FixPoint) (G : GlobName) : Prop :=
  ∃ σ : State G, F G = some σ

def FixPoint.lookup (F : FixPoint) (G : GlobName) (hIn : InFixPoint F G) : State G :=
  (F G).get (by obtain ⟨σ, hσ⟩ := hIn; simp [hσ])

@[simp] theorem FixPoint.lookup_eq {F : FixPoint} {G : GlobName} {σ : State G}
    (hIn : InFixPoint F G) (h : F G = some σ) : F.lookup G hIn = σ := by
  simp [FixPoint.lookup, h]

inductive KJ {G : GlobName} (C : ClassName) (σ : State G) (L : Program) (F : FixPoint) :
    Expr → Set OPair → Prop
  | thisE  : KJ C σ L F Expr.thisE (⋃ G' ∈ σ.This C, {(G', C)})
  | paramE : KJ C σ L F Expr.paramE (σ.Param C)
  | proj {e i K} (hK : ∀ p ∈ K, InFixPoint F p.1) :
      KJ C σ L F e K →
      KJ C σ L F (Expr.proj e i) (⋃ p, ⋃ h : p ∈ K, (F.lookup p.1 (hK p h)).Fld i p.2)
  | gproj {G₀ i} (hK : InFixPoint F G₀) :
      KJ C σ L F (Expr.gproj G₀ i) ((F.lookup G₀ hK).GFld i)
  | newC {D e₁ e₂} : KJ C σ L F (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJ C σ L F e₁ K₁ → KJ C σ L F (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret p.2)
  | val {v} : KJ C σ L F (Expr.val v) ∅

inductive KJ0 {G : GlobName} (σ : State G) (L : Program) (F : FixPoint) : Expr → Set OPair → Prop
  | proj {e i K} (hK : ∀ p ∈ K, InFixPoint F p.1) :
      KJ0 σ L F e K →
      KJ0 σ L F (Expr.proj e i) (⋃ p, ⋃ h : p ∈ K, (F.lookup p.1 (hK p h)).Fld i p.2)
  | gproj {G₀ i} (hK : InFixPoint F G₀) :
      KJ0 σ L F (Expr.gproj G₀ i) ((F.lookup G₀ hK).GFld i)
  | newC {D e₁ e₂} : KJ0 σ L F (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJ0 σ L F e₁ K₁ → KJ0 σ L F (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret p.2)
  | val {v} : KJ0 σ L F (Expr.val v) ∅

inductive Calls {G : GlobName} (C : ClassName) (σ : State G) (L : Program) (F : FixPoint) :
    Expr → Set ClassName → Prop
  | thisE  : Calls C σ L F Expr.thisE ∅
  | paramE : Calls C σ L F Expr.paramE ∅
  | gproj {G₀ i} : Calls C σ L F (Expr.gproj G₀ i) ∅
  | proj {e i K} : Calls C σ L F e K → Calls C σ L F (Expr.proj e i) K
  | newC {D e₁ e₂ K₁ K₂} :
      Calls C σ L F e₁ K₁ → Calls C σ L F e₂ K₂ →
      Calls C σ L F (Expr.newC D e₁ e₂) (K₁ ∪ K₂)
  | app {e₁ e₂ K₁ K₂ K₃} :
      KJ C σ L F e₁ K₁ → Calls C σ L F e₁ K₂ → Calls C σ L F e₂ K₃ →
      Calls C σ L F (Expr.app e₁ e₂) ((classes K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls C σ L F (Expr.val v) ∅

inductive Calls0 {G : GlobName} (σ : State G) (L : Program) (F : FixPoint) : Expr → Set ClassName → Prop
  | gproj {G₀ i} : Calls0 σ L F (Expr.gproj G₀ i) ∅
  | proj {e i K} : Calls0 σ L F e K → Calls0 σ L F (Expr.proj e i) K
  | newC {D e₁ e₂ K₁ K₂} :
      Calls0 σ L F e₁ K₁ → Calls0 σ L F e₂ K₂ →
      Calls0 σ L F (Expr.newC D e₁ e₂) (K₁ ∪ K₂)
  | app {e₁ e₂ K₁ K₂ K₃} :
      KJ0 σ L F e₁ K₁ → Calls0 σ L F e₁ K₂ → Calls0 σ L F e₂ K₃ →
      Calls0 σ L F (Expr.app e₁ e₂) ((classes K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls0 σ L F (Expr.val v) ∅

abbrev Ctx := Option ClassName

def KJC {G : GlobName} (σ : State G) (L : Program) (F : FixPoint) : Ctx → Expr → Set OPair → Prop
  | none   => KJ0 σ L F
  | some C => KJ C σ L F

end Algorithm
