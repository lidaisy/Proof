import Proof.Syntax
import Proof.Semantics
import Proof.Analysis
import Proof.AbstractDetectsCycle
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

namespace Algorithm

open Proof (GlobName ClassName OPair Idx Program Expr classes objects)

structure State (G : GlobName) where
  Param : ClassName → Set OPair
  Fld₁  : ClassName → Set OPair
  Fld₂  : ClassName → Set OPair
  Ret   : ClassName → Set OPair
  GFld₁ : Set OPair
  GFld₂ : Set OPair
  RM    : Set ClassName
  This  : ClassName → Set GlobName

def State.zero (G : GlobName) : State G where
  Param := fun _ => ∅
  Fld₁  := fun _ => ∅
  Fld₂  := fun _ => ∅
  Ret   := fun _ => ∅
  GFld₁ := ∅
  GFld₂ := ∅
  RM    := ∅
  This  := fun _ => ∅

def State.Fld {G : GlobName} (σ : State G) : Idx → ClassName → Set OPair
  | Idx.one => σ.Fld₁
  | Idx.two => σ.Fld₂

def State.GFld {G : GlobName} (σ : State G) : Idx → Set OPair
  | Idx.one => σ.GFld₁
  | Idx.two => σ.GFld₂

abbrev FixPoints := (G : GlobName) → Option (State G)

def InFixPoint (F : FixPoints) (G : GlobName) : Prop :=
  ∃ σ : State G, F G = some σ

def FixPoints.lookup (F : FixPoints) (G : GlobName) (hIn : InFixPoint F G) : State G :=
  (F G).get (by obtain ⟨σ, hσ⟩ := hIn; simp [hσ])

@[simp] theorem FixPoint.lookup_eq {F : FixPoints} {G : GlobName} {σ : State G}
    (hIn : InFixPoint F G) (h : F G = some σ) : F.lookup G hIn = σ := by
  simp [FixPoints.lookup, h]

def FixPoints.insert (F : FixPoints) (G : GlobName) (σ : State G) : FixPoints :=
  fun G' => if h : G' = G then some (h ▸ σ) else F G'

@[simp] theorem FixPoints.insert_self {F : FixPoints} {G : GlobName} {σ : State G} :
    F.insert G σ G = some σ := by simp [FixPoints.insert]

@[simp] theorem FixPoints.insert_other {F : FixPoints} {G G' : GlobName} {σ : State G}
    (h : G' ≠ G) : F.insert G σ G' = F G' := by simp [FixPoints.insert, h]

theorem InFixPoint.insert {F : FixPoints} {G : GlobName} {σ : State G} :
    InFixPoint (F.insert G σ) G := ⟨σ, FixPoints.insert_self⟩

@[simp] theorem InFixPoint.mono_insert {F : FixPoints} {G G' : GlobName} {σ : State G}
    (h : InFixPoint F G') : InFixPoint (F.insert G σ) G' := by
  by_cases hG : G' = G
  · subst hG; exact InFixPoint.insert
  · obtain ⟨σ', hσ'⟩ := h; exact ⟨σ', by rw [FixPoints.insert_other hG]; exact hσ'⟩

inductive KJ {G : GlobName} (C : ClassName) (σ : State G) (L : Program) (F : FixPoints) :
    Expr → Set OPair → Set GlobName → Prop
  | thisE  : KJ C σ L F Expr.thisE (⋃ G' ∈ σ.This C, {(G', C)}) ∅
  | paramE : KJ C σ L F Expr.paramE (σ.Param C) ∅
  | proj {e i K D} (hK : ∀ p ∈ K, p.1 = G ∨ InFixPoint F p.1) :
      KJ C σ L F e K D →
      KJ C σ L F (Expr.proj e i)
        (⋃ p, ⋃ h : p ∈ K,
          if hG : p.1 = G then σ.Fld i p.2
          else (F.lookup p.1 ((hK p h).resolve_left hG)).Fld i p.2)
        (D ∪ (objects K \ {G}))
  | gproj {G₀ i} (hK : InFixPoint F G₀) :
      KJ C σ L F (Expr.gproj G₀ i) ((F.lookup G₀ hK).GFld i) {G₀}
  | newC {D e₁ e₂} : KJ C σ L F (Expr.newC D e₁ e₂) {(G, D)} ∅
  | app {e₁ e₂ K₁ D₁} :
      KJ C σ L F e₁ K₁ D₁ → KJ C σ L F (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret p.2) D₁
  | val {v} : KJ C σ L F (Expr.val v) ∅ ∅

inductive KJ0 {G : GlobName} (σ : State G) (L : Program) (F : FixPoints) :
    Expr → Set OPair → Set GlobName → Prop
  | proj {e i K D} (hK : ∀ p ∈ K, p.1 = G ∨ InFixPoint F p.1) :
      KJ0 σ L F e K D →
      KJ0 σ L F (Expr.proj e i)
        (⋃ p, ⋃ h : p ∈ K,
          if hG : p.1 = G then σ.Fld i p.2
          else (F.lookup p.1 ((hK p h).resolve_left hG)).Fld i p.2)
        (D ∪ (objects K \ {G}))
  | gproj {G₀ i} (hK : InFixPoint F G₀) :
      KJ0 σ L F (Expr.gproj G₀ i) ((F.lookup G₀ hK).GFld i) {G₀}
  | newC {D e₁ e₂} : KJ0 σ L F (Expr.newC D e₁ e₂) {(G, D)} ∅
  | app {e₁ e₂ K₁ D₁} :
      KJ0 σ L F e₁ K₁ D₁ → KJ0 σ L F (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret p.2) D₁
  | val {v} : KJ0 σ L F (Expr.val v) ∅ ∅

inductive Calls {G : GlobName} (C : ClassName) (σ : State G) (L : Program) (F : FixPoints) :
    Expr → Set ClassName → Prop
  | thisE  : Calls C σ L F Expr.thisE ∅
  | paramE : Calls C σ L F Expr.paramE ∅
  | gproj {G₀ i} : Calls C σ L F (Expr.gproj G₀ i) ∅
  | proj {e i K} : Calls C σ L F e K → Calls C σ L F (Expr.proj e i) K
  | newC {D e₁ e₂ K₁ K₂} :
      Calls C σ L F e₁ K₁ → Calls C σ L F e₂ K₂ →
      Calls C σ L F (Expr.newC D e₁ e₂) (K₁ ∪ K₂)
  | app {e₁ e₂ K₁ D₁ K₂ K₃} :
      KJ C σ L F e₁ K₁ D₁ → Calls C σ L F e₁ K₂ → Calls C σ L F e₂ K₃ →
      Calls C σ L F (Expr.app e₁ e₂) ((classes K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls C σ L F (Expr.val v) ∅

inductive Calls0 {G : GlobName} (σ : State G) (L : Program) (F : FixPoints) : Expr → Set ClassName → Prop
  | gproj {G₀ i} : Calls0 σ L F (Expr.gproj G₀ i) ∅
  | proj {e i K} : Calls0 σ L F e K → Calls0 σ L F (Expr.proj e i) K
  | newC {D e₁ e₂ K₁ K₂} :
      Calls0 σ L F e₁ K₁ → Calls0 σ L F e₂ K₂ →
      Calls0 σ L F (Expr.newC D e₁ e₂) (K₁ ∪ K₂)
  | app {e₁ e₂ K₁ D₁ K₂ K₃} :
      KJ0 σ L F e₁ K₁ D₁ → Calls0 σ L F e₁ K₂ → Calls0 σ L F e₂ K₃ →
      Calls0 σ L F (Expr.app e₁ e₂) ((classes K₁ ∪ K₂) ∪ K₃)
  | val {v} : Calls0 σ L F (Expr.val v) ∅

abbrev Ctx := Option ClassName

def KJC {G : GlobName} (σ : State G) (L : Program) (F : FixPoints) :
    Ctx → Expr → Set OPair → Set GlobName → Prop
  | none   => KJ0 σ L F
  | some C => KJ C σ L F

/-- `Needs σ L F c e G₀`: analysing `e` cannot proceed until `G₀` is solved. -/
inductive Needs {G : GlobName} (σ : State G) (L : Program) (F : FixPoints) :
    Ctx → Expr → GlobName → Prop
  | projOwner {c e i K D p} :
      KJC σ L F c e K D → p ∈ K → p.1 ≠ G → ¬ InFixPoint F p.1 →
      Needs σ L F c (Expr.proj e i) p.1
  | projSub {c e i G₀} :
      Needs σ L F c e G₀ → Needs σ L F c (Expr.proj e i) G₀
  | gproj {c G₀ i} :
      ¬ InFixPoint F G₀ → Needs σ L F c (Expr.gproj G₀ i) G₀
  | appFun {c e₁ e₂ G₀} :
      Needs σ L F c e₁ G₀ → Needs σ L F c (Expr.app e₁ e₂) G₀

theorem kj_or_needs {G : GlobName} (σ : State G) (L : Program) (F : FixPoints)
    (C : ClassName) (e : Expr) :
    (∃ K D, KJ C σ L F e K D) ∨ (∃ G₀, Needs σ L F (some C) e G₀) := by
  induction e with
  | thisE => exact Or.inl ⟨_, _, KJ.thisE⟩
  | paramE => exact Or.inl ⟨_, _, KJ.paramE⟩
  | newC D e₁ e₂ _ _ => exact Or.inl ⟨_, _, KJ.newC⟩
  | val v => exact Or.inl ⟨_, _, KJ.val⟩
  | gproj G₀ i =>
      by_cases h : InFixPoint F G₀
      · exact Or.inl ⟨_, _, KJ.gproj h⟩
      · exact Or.inr ⟨G₀, Needs.gproj h⟩
  | app e₁ e₂ ih₁ _ =>
      rcases ih₁ with ⟨K₁, D₁, h₁⟩ | ⟨G₀, h₁⟩
      · exact Or.inl ⟨_, _, KJ.app h₁⟩
      · exact Or.inr ⟨G₀, Needs.appFun h₁⟩
  | proj e i ih =>
      rcases ih with ⟨K, D, h⟩ | ⟨G₀, h⟩
      · by_cases hK : ∀ p ∈ K, p.1 = G ∨ InFixPoint F p.1
        · exact Or.inl ⟨_, _, KJ.proj hK h⟩
        · push Not at hK
          obtain ⟨p, hp, hne, hnp⟩ := hK
          exact Or.inr ⟨p.1, Needs.projOwner (c := some C) h hp hne hnp⟩
      · exact Or.inr ⟨G₀, Needs.projSub h⟩

abbrev Stack := List ((G : GlobName) × State G)

def Stack.globs (S : Stack) : List GlobName := S.map Sigma.fst

abbrev Queue := List GlobName

def Queue.remove (Q : Queue) (G : GlobName) :=
match Q with
| [] => []
| g::gs => if g == G then gs else g::(Queue.remove gs G)

inductive RE (G : GlobName) (σ : State G) (L : Program) : Ctx → Expr → Prop
  | init₁ {e₁ e₂} : Program.HasObject L G e₁ e₂ → RE G σ L none e₁
  | init₂ {e₁ e₂} : Program.HasObject L G e₁ e₂ → RE G σ L none e₂
  | body {C e} : C ∈ σ.RM → Program.HasClass L C e → RE G σ L (some C) e
  | proj {c e i} : RE G σ L c (Expr.proj e i) → RE G σ L c e
  | newC₁ {c D e₁ e₂} : RE G σ L c (Expr.newC D e₁ e₂) → RE G σ L c e₁
  | newC₂ {c D e₁ e₂} : RE G σ L c (Expr.newC D e₁ e₂) → RE G σ L c e₂
  | app₁ {c e₁ e₂} : RE G σ L c (Expr.app e₁ e₂) → RE G σ L c e₁
  | app₂ {c e₁ e₂} : RE G σ L c (Expr.app e₁ e₂) → RE G σ L c e₂

inductive DepJ (F : FixPoints) (L : Program) : GlobName → GlobName → Prop
  | direct {G G₀ : GlobName} {c : Ctx} {i : Idx} {h : InFixPoint F G} :
      RE G (F.lookup G h) L c (Expr.gproj G₀ i) → DepJ F L G G₀
  | trans {G G' G₀ : GlobName} :
      DepJ F L G G' → DepJ F L G' G₀ → DepJ F L G G₀

def Dep (F : FixPoints) (L : Program) (G : GlobName) : Set GlobName :=
  { G₀ | DepJ F L G G₀ }

structure FixPoint (G : GlobName) (σ : State G) (L : Program) (F : FixPoints)
  : Prop where
  rm_init : ∀ {e₁ e₂ K₁ K₂}, Program.HasObject L G e₁ e₂ →
      Calls0 σ L F e₁ K₁ → Calls0 σ L F e₂ K₂ → (K₁ ∪ K₂) ⊆ σ.RM
  rm_closed : ∀ {C body K}, C ∈ σ.RM → Program.HasClass L C body →
      Calls C σ L F body K → K ⊆ σ.RM
  ret_init : ∀ {C e K Dp}, Program.HasClass L C e →
      KJ C σ L F e K Dp → K ⊆ σ.Ret C
  gfld_init_one : ∀ {e₁ e₂ K₁ Dp₁}, Program.HasObject L G e₁ e₂ →
      KJ0 σ L F e₁ K₁ Dp₁ → K₁ ⊆ σ.GFld Idx.one
  gfld_init_two : ∀ {e₁ e₂ K₂ Dp₂}, Program.HasObject L G e₁ e₂ →
      KJ0 σ L F e₂ K₂ Dp₂ → K₂ ⊆ σ.GFld Idx.two
  fld_re : ∀ {c D e₁ e₂ K₁ K₂ Dp₁ Dp₂}, RE G σ L c (Expr.newC D e₁ e₂) →
      KJC σ L F c e₁ K₁ Dp₁ → KJC σ L F c e₂ K₂ Dp₂ →
      K₁ ⊆ σ.Fld Idx.one D ∧ K₂ ⊆ σ.Fld Idx.two D
  param_re : ∀ {c e₁ e₂ K₁ K₂ Dp₁ Dp₂}, RE G σ L c (Expr.app e₁ e₂) →
      KJC σ L F c e₁ K₁ Dp₁ → KJC σ L F c e₂ K₂ Dp₂ →
      ∀ D ∈ classes K₁, K₂ ⊆ σ.Param D
  this_re : ∀ {G₀ c K₁ Dp₁ e₁ e₂}, RE G σ L c (Expr.app e₁ e₂) → KJC σ L F c e₁ K₁ Dp₁ →
      G₀ = objects K₁ → ∀ D ∈ classes K₁, G₀ ⊆ σ.This D

structure State.Sub {G : GlobName} (σ σ' : State G) : Prop where
  param : ∀ C, σ.Param C ⊆ σ'.Param C
  fld₁  : ∀ C, σ.Fld₁ C ⊆ σ'.Fld₁ C
  fld₂  : ∀ C, σ.Fld₂ C ⊆ σ'.Fld₂ C
  ret   : ∀ C, σ.Ret C ⊆ σ'.Ret C
  gfld₁ : σ.GFld₁ ⊆ σ'.GFld₁
  gfld₂ : σ.GFld₂ ⊆ σ'.GFld₂
  rm    : σ.RM ⊆ σ'.RM
  this  : ∀ C, σ.This C ⊆ σ'.This C

instance {G : GlobName} : Preorder (State G) where
  le := State.Sub
  le_refl _ :=
    { param := fun _ => subset_rfl,
      fld₁ := fun _ => subset_rfl,
      fld₂ := fun _ => subset_rfl,
      ret := fun _ => subset_rfl,
      gfld₁ := subset_rfl,
      gfld₂ := subset_rfl,
      rm := subset_rfl,
      this := fun _ => subset_rfl }
  le_trans _ _ _ h₁ h₂ :=
    { param := fun C => (h₁.param C).trans (h₂.param C)
      fld₁  := fun C => (h₁.fld₁ C).trans (h₂.fld₁ C)
      fld₂  := fun C => (h₁.fld₂ C).trans (h₂.fld₂ C)
      ret   := fun C => (h₁.ret C).trans (h₂.ret C)
      gfld₁ := h₁.gfld₁.trans h₂.gfld₁
      gfld₂ := h₁.gfld₂.trans h₂.gfld₂
      rm    := h₁.rm.trans h₂.rm
      this  := fun C => (h₁.this C).trans (h₂.this C) }

def State.addRM {G} (σ : State G) (K : Set ClassName) : State G := { σ with RM := σ.RM ∪ K }
def State.addRet {G} (σ : State G) (C : ClassName) (K : Set OPair) : State G :=
  { σ with Ret := fun C' => if C' = C then σ.Ret C' ∪ K else σ.Ret C' }
def State.addFldAt {G} (σ : State G) (i : Idx) (C : ClassName) (K : Set OPair) : State G :=
  if i = Idx.one then
    { σ with Fld₁ := fun C' => if C' = C then σ.Fld₁ C' ∪ K else σ.Fld₁ C' }
  else
    { σ with Fld₂ := fun C' => if C' = C then σ.Fld₂ C' ∪ K else σ.Fld₂ C' }
def State.addParamAt {G} (σ : State G) (Cs : Set ClassName) (K : Set OPair) : State G :=
  { σ with Param := fun C' => σ.Param C' ∪ ⋃ (_ : C' ∈ Cs), K }
def State.addThisAt {G} (σ : State G) (Cs : Set ClassName) (Gs : Set GlobName) : State G :=
  { σ with This := fun C' => σ.This C' ∪ ⋃ (_ : C' ∈ Cs), Gs }

inductive Grow (L : Program) (F : FixPoints) (G : GlobName) : State G → State G → Prop
  | rmInit {σ e₁ e₂ K₁ K₂} :
      Program.HasObject L G e₁ e₂ → Calls0 σ L F e₁ K₁ → Calls0 σ L F e₂ K₂ →
      Grow L F G σ (σ.addRM (K₁ ∪ K₂))
  | rmClosed {σ C body K} :
      C ∈ σ.RM → Program.HasClass L C body → Calls C σ L F body K →
      Grow L F G σ (σ.addRM K)
  | retInit {σ C e K D} (he : Program.HasClass L C e) (hK : KJ C σ L F e K D) :
      Grow L F G σ (σ.addRet C K)
  | gfldOne {σ e₁ e₂ K₁ D₁} :
      Program.HasObject L G e₁ e₂ → (hK : KJ0 σ L F e₁ K₁ D₁) →
      Grow L F G σ { σ with GFld₁ := σ.GFld₁ ∪ K₁ }
  | gfldTwo {σ e₁ e₂ K₂ D₂} :
      Program.HasObject L G e₁ e₂ → (hK : KJ0 σ L F e₂ K₂ D₂) →
      Grow L F G σ { σ with GFld₂ := σ.GFld₂ ∪ K₂ }
  | fld {σ c Dc e₁ e₂ K₁ K₂ D₁ D₂} :
      RE G σ L c (Expr.newC Dc e₁ e₂) → (hK₁ : KJC σ L F c e₁ K₁ D₁) → (hK₂ : KJC σ L F c e₂ K₂ D₂) →
      Grow L F G σ ((σ.addFldAt Idx.one Dc K₁).addFldAt Idx.two Dc K₂)
  | param {σ c e₁ e₂ K₁ K₂ D₁ D₂} :
      RE G σ L c (Expr.app e₁ e₂) → (hK₁ : KJC σ L F c e₁ K₁ D₁) → (hK₂ : KJC σ L F c e₂ K₂ D₂) →
      Grow L F G σ (σ.addParamAt (classes K₁) K₂)
  | thisG {σ c e₁ e₂ K₁ D₁} :
      RE G σ L c (Expr.app e₁ e₂) → (hK : KJC σ L F c e₁ K₁ D₁) →
      Grow L F G σ (σ.addThisAt (classes K₁) (objects K₁))

def Stable (L : Program) (F : FixPoints) (G : GlobName) (σ : State G) : Prop :=
  (∀ σ', Grow L F G σ σ' → σ' ≤ σ) ∧
  (∀ c e G₀, RE G σ L c e → ¬ Needs σ L F c e G₀)

inductive Config
  | mk (G : GlobName) (σ : State G) (F : FixPoints) (S : Stack) (Q : Queue)
  | done (F : FixPoints)
  | cycle (G : GlobName)
  deriving Inhabited

def Config.object : { c : Config // ∃ G s F S Q, c = .mk G s F S Q } → GlobName
  | ⟨.mk G _ _ _ _, _⟩ => G

def Config.fixpoints : Config → FixPoints
  | .mk _ _ F _ _ => F
  | .done F => F
  | .cycle _ => fun _ => none

def Config.stack : Config → Stack
  | .mk _ _ _ S _ => S
  | _ => []

inductive Solve (L : Program) : Config → Config → Prop
  | step {G : GlobName} {σ σ' : State G} {F : FixPoints} {S : Stack} {Q : Queue} :
      Grow L F G σ σ' →
      Solve L (.mk G σ F S Q) (.mk G σ' F S Q)
  | suspend {G G₀ : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
      {c : Ctx} {e : Expr} :
      RE G σ L c e → Needs σ L F c e G₀ →
      G₀ ≠ G → G₀ ∉ Stack.globs S →
      Solve L (.mk G σ F S Q)
              (.mk G₀ (State.zero G₀) F (⟨G, σ⟩ :: S) (Q.remove G₀))
  | cycle {G G₀ : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
      {c : Ctx} {e : Expr} :
      RE G σ L c e → Needs σ L F c e G₀ →
      (G₀ = G ∨ G₀ ∈ Stack.globs S) →
      Solve L (.mk G σ F S Q) (.cycle G₀)
  | resume {G G' : GlobName} {σ : State G} {σ' : State G'} {F : FixPoints}
      {S : Stack} {Q : Queue} :
      Stable L F G σ →
      Solve L (.mk G σ F (⟨G', σ'⟩ :: S) Q) (.mk G' σ' (F.insert G σ) S Q)
  | next {G G₀ : GlobName} {σ : State G} {F : FixPoints} {Q : Queue} :
      Stable L F G σ → ¬ InFixPoint F G₀ →
      Solve L (.mk G σ F List.nil (G₀ :: Q))
              (.mk G₀ (State.zero G₀) (F.insert G σ) List.nil Q)
  | skip {G G₀ : GlobName} {σ : State G} {F : FixPoints} {Q : Queue} :
      InFixPoint F G₀ →
      Solve L (.mk G σ F List.nil (G₀ :: Q)) (.mk G σ F List.nil Q)
  | finish {G : GlobName} {σ : State G} {F : FixPoints} :
      Stable L F G σ →
      Solve L (.mk G σ F List.nil List.nil) (.done (F.insert G σ))

abbrev Solve.Star (L : Program) : Config → Config → Prop :=
  Relation.ReflTransGen (Solve L)

def Config.start (L : Program) (hL : L.HasMain) : Config :=
  let objects := L.GlobNames
  let G := objects.head hL
  let Q := objects.tail
  .mk G (State.zero G) (fun _ => none) List.nil Q

def FixPoints.glue (F : FixPoints) : Proof.Sigma where
  Param := fun G C => ((F G).map fun σ => σ.Param C).getD ∅
  Fld₁  := fun G C => ((F G).map fun σ => σ.Fld₁ C).getD ∅
  Fld₂  := fun G C => ((F G).map fun σ => σ.Fld₂ C).getD ∅
  Ret   := fun G C => ((F G).map fun σ => σ.Ret C).getD ∅
  GFld₁ := fun G   => ((F G).map fun σ => σ.GFld₁).getD ∅
  GFld₂ := fun G   => ((F G).map fun σ => σ.GFld₂).getD ∅
  RM    := fun G   => ((F G).map fun σ => σ.RM).getD ∅
  This  := fun G C => ((F G).map fun σ => σ.This C).getD ∅

section glue
variable {F : FixPoints} {G : GlobName} {σ : State G}

@[simp] theorem FixPoints.glue_param (h : F G = some σ) : F.glue.Param G = σ.Param := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_fld₁ (h : F G = some σ) : F.glue.Fld₁ G = σ.Fld₁ := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_fld₂ (h : F G = some σ) : F.glue.Fld₂ G = σ.Fld₂ := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_ret (h : F G = some σ) : F.glue.Ret G = σ.Ret := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_gfld₁ (h : F G = some σ) : F.glue.GFld₁ G = σ.GFld₁ := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_gfld₂ (h : F G = some σ) : F.glue.GFld₂ G = σ.GFld₂ := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_rm (h : F G = some σ) : F.glue.RM G = σ.RM := by
  simp [FixPoints.glue, h]
@[simp] theorem FixPoints.glue_this (h : F G = some σ) : F.glue.This G = σ.This := by
  simp [FixPoints.glue, h]

theorem FixPoints.glue_fld (h : F G = some σ) (i : Idx) : F.glue.Fld i G = σ.Fld i := by
  cases i <;> simp [Proof.Sigma.Fld, State.Fld, h]

theorem FixPoints.glue_gfld (h : F G = some σ) (i : Idx) : F.glue.GFld i G = σ.GFld i := by
  cases i <;> simp [Proof.Sigma.GFld, State.GFld, h]

end glue

end Algorithm
