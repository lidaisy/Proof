import Proof.Syntax
import Proof.Semantics
import Proof.Analysis
import Proof.AbstractDetectsCycle
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

namespace Algorithm

open Proof (GlobName ClassName OPair Idx Program Expr classes objects Sigma)

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

theorem State.ext_sub {G : GlobName} {σ σ' : State G}
    (h₁ : State.Sub σ σ') (h₂ : State.Sub σ' σ) : σ = σ' := by
  cases σ
  cases σ'
  -- congr <;> ext
  -- · refine ⟨?_, ?_⟩
  --   · intro x
  --     sorry
  --   · sorry

  -- · exact Set.Subset.antisymm (h₁.fld₁ _) (h₂.fld₁ _)
  -- · exact Set.Subset.antisymm (h₁.fld₂ _) (h₂.fld₂ _)
  -- · exact Set.Subset.antisymm (h₁.ret _) (h₂.ret _)
  -- · exact Set.Subset.antisymm h₁.gfld₁ h₂.gfld₁
  -- · exact Set.Subset.antisymm h₁.gfld₂ h₂.gfld₂
  -- · exact Set.Subset.antisymm h₁.rm h₂.rm
  -- · exact Set.Subset.antisymm (h₁.this _) (h₂.this _)

  sorry

-- instance {G : GlobName} : PartialOrder (State G) where
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
  -- le_antisymm σ₁ σ₂ h₁ h₂ := State.ext_sub h₁ h₂

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

theorem grow_le {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G}
    (hgrow : Grow L F G σ σ')
    : σ ≤ σ' := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G' C'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => simp
    | fld => simp [State.addFldAt]
    | param => simp [State.addParamAt]; sorry
    | thisG => simp [State.addThisAt]
  · intro G' C'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => simp
    | fld => sorry --simp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => simp [State.addThisAt]
  · intro G' C'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => simp
    | fld => sorry --imp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => simp [State.addThisAt]
  · intro G' C'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => sorry --simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => simp
    | fld => simp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => simp [State.addThisAt]
  · intro G'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => sorry -- simp
    | gfldTwo => simp
    | fld => simp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => simp [State.addThisAt]
  · intro G'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => sorry --simp
    | fld => simp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => simp [State.addThisAt]
  · intro G'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => sorry -- simp [State.addRM]
    | rmClosed => sorry -- simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => simp
    | fld => simp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => simp [State.addThisAt]
  · intro G' C'
    induction hgrow with
    | @rmInit e₁ e₂ K₁ K₂ hG hC₁ hC₂ => simp [State.addRM]
    | rmClosed => simp [State.addRM]
    | retInit => simp [State.addRet]
    | gfldOne => simp
    | gfldTwo => simp
    | fld => simp [State.addFldAt]
    | param => simp [State.addParamAt]
    | thisG => sorry -- simp [State.addThisAt]

def Stable (L : Program) (F : FixPoints) (G : GlobName) (σ : State G) : Prop :=
  (∀ σ', Grow L F G σ σ' → σ' ≤ σ) ∧
  (∀ c i G₀, RE G σ L c (Expr.gproj G₀ i) → ¬ Needs σ L F c (Expr.gproj G₀ i) G₀)

inductive Config
  | mk (G : GlobName) (σ : State G) (F : FixPoints) (S : Stack) (Q : Queue)
  | done (F : FixPoints)
  | cycle (G : GlobName)
  deriving Inhabited

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
      {c : Ctx} {i : Idx} :
      RE G σ L c (Expr.gproj G₀ i) → Needs σ L F c (Expr.gproj G₀ i) G₀ →
      G₀ ≠ G → G₀ ∉ Stack.globs S →
      Solve L (.mk G σ F S Q)
              (.mk G₀ (State.zero G₀) F (⟨G, σ⟩ :: S) (Q.remove G₀))
  | cycle {G G₀ : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
      {c : Ctx} {i : Idx} :
      RE G σ L c (Expr.gproj G₀ i) → Needs σ L F c (Expr.gproj G₀ i) G₀ →
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

def Config.start (L : Program) (hL : L.WellFormed) : Config :=
  let objects := L.GlobNames
  let G := objects.head hL.left
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

def Stack.find (S : Stack) (G : GlobName) : Option (State G) :=
  match S with
  | [] => none
  | s :: ss => if h : s.fst = G then (some (h ▸ s.snd)) else Stack.find ss G

def Config.curObj : Config → Option GlobName
  | .mk G _ _ _ _ => G
  | .cycle G => G
  | _ => none

def Config.curState {G : GlobName} : Config → Option (State G)
  | .mk G' σ _ _ _ => if h : G' = G then some (h ▸ σ) else none
  | _ => none

def Config.WellFormed (L : Program) : Config → Prop
| (.mk G _ F S Q) =>
      (List.Perm (G :: (S.globs ++ Q)) L.GlobNames)
    ∧ ¬ InFixPoint F G
    ∧ (∀ G' ∈ S.globs, ¬ InFixPoint F G')
    ∧ (∀ G' ∈ Q, ¬ InFixPoint F G')
| .cycle _ => True
| .done _ => True

theorem config_wellformed_step {L : Program} {c c' : Config} (hstep : Solve L c c')
    (h: c.WellFormed L)
    : c'.WellFormed L := by
  sorry
  -- cases hstep with
  -- | step => exact h
  -- | @suspend G₀ G₁ σ F S Q c i hre hneeds hne hnS =>
  --     refine ⟨?_, ?_, ?_⟩
  --     · cases hneeds with
  --       | gproj h' => exact h'
  --     · intro G' hG'
  --       by_cases heq : G' = G₀
  --       · subst heq; exact h.left
  --       · have hS : G' ∈ S.globs := by -- TODO: factor this out. Used in cycle.lean too
  --           simp [Stack.globs] at hG'
  --           simp [Stack.globs, List.mem_map]
  --           exact hG'.resolve_left heq
  --         exact h.right.left G' hS
  --     · intro G' hG'
  --       have hremove_mem : ∀ {Q : Queue} {G G'}, G' ∈ Queue.remove Q G → G' ∈ Q := by
  --         intro Q G G' hmem
  --         induction Q with
  --         | nil =>
  --             simp [Queue.remove] at hmem
  --         | cons g gs ih =>
  --             by_cases hg : g == G
  --             · have hgs : G' ∈ gs := by
  --                 simpa [Queue.remove, hg] using hmem
  --               simpa using (show G' = g ∨ G' ∈ gs from Or.inr hgs)
  --             · have hsplit : G' = g ∨ G' ∈ Queue.remove gs G := by
  --                 simpa [Queue.remove, hg] using hmem
  --               rcases hsplit with rfl | hsplit
  --               · simp
  --               · have : G' ∈ gs := ih hsplit
  --                 simpa using (show G' = g ∨ G' ∈ gs from Or.inr this)
  --       have hQ : G' ∈ Q := hremove_mem hG'
  --       exact h.right.right G' hQ
  -- | cycle => trivial
  -- | @resume G₀ G₁ σ σ' F S Q hSt =>
  --     refine ⟨?_, ?_, ?_⟩
  --     · have hG₁ : G₁ ∈ Stack.globs (⟨G₁, σ'⟩ :: S) := sorry
  --       have hprev := h.right.left G₁ hG₁
  --       sorry
  --     · intro G' hG'

  --       sorry
  --     · intro G' hG'
  --       sorry
  -- | @next G₀ G₁ σ F Q hSt hfix =>
  --     refine ⟨?_, ?_, ?_⟩
  --     · -- use hfix
  --       sorry
  --     · intro G' hG'
  --       simp [Stack.globs] at hG'
  --     · intro G' hG'
  --       sorry
  -- | @skip G₀ G₁ σ F Q hfix =>
  --     refine ⟨?_, ?_, ?_⟩
  --     · -- use hfix
  --       sorry
  --     · intro G' hG'
  --       simp [Stack.globs] at hG'
  --     · intro G' hG'
  --       sorry
  -- | finish => trivial

theorem config_wellformed {L : Program} {hL : L.WellFormed} {c : Config} (hstar : Solve.Star L (Config.start L hL) c)
    : c.WellFormed L := by
  induction hstar with
  | refl =>
    refine ⟨?_, by simp [InFixPoint], by intro G hG'; simp [InFixPoint], by intro G hG'; simp [InFixPoint]⟩
    have hhead : L.GlobNames.head hL.left :: L.GlobNames.tail = L.GlobNames :=
        List.cons_head_tail hL.left
    simp [Stack.globs, hhead]
  | tail hprev hgrow ih => exact config_wellformed_step hgrow ih

def Config.find (c : Config) (G : GlobName) : Option (State G) :=
    (c.fixpoints G).orElse fun _ =>
      (c.curState (G := G)).orElse fun _ => c.stack.find G

theorem Config.find_curState {L : Program} {c : Config}
    {G : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
    (hc : c = (Config.mk G σ F S Q))
    (h: c.curState = some σ) (hwf : Config.WellFormed L c)
    : Config.find c G = some σ := by
  subst hc
  simp [Config.find]
  have hfn : (Config.mk G σ F S Q).fixpoints G = none := by
    simp [Config.fixpoints]
    by_contra h
    obtain ⟨σ, hσ⟩ := Option.ne_none_iff_exists'.mp h
    exact hwf.right.left ⟨σ, hσ⟩
  exact Or.inr ⟨hfn, Or.inl h⟩

-- theorem Config.find_curStack {L : Program} {c : Config}
--     {G : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
--     (hc : c = (Config.mk G σ F S Q))
--     (hfix : F G = none)
--     (hcur : c.curState (G := G) = none)
--     : Config.find c G = some σ := by
--   subst hc
--   simp [Config.find]
--   exact Or.inr ⟨hfix, Or.inr ⟨hcur, ⟩⟩

def Config.all_data (c : Config) : Proof.Sigma :=
  { Param := fun G C => (c.find G).map (fun σ => σ.Param C) |>.getD ∅
    Fld₁  := fun G C => (c.find G).map (fun σ => σ.Fld₁ C) |>.getD ∅
    Fld₂  := fun G C => (c.find G).map (fun σ => σ.Fld₂ C) |>.getD ∅
    Ret   := fun G C => (c.find G).map (fun σ => σ.Ret C) |>.getD ∅
    GFld₁ := fun G   => (c.find G).map (fun σ => σ.GFld₁) |>.getD ∅
    GFld₂ := fun G   => (c.find G).map (fun σ => σ.GFld₂) |>.getD ∅
    RM    := fun G   => (c.find G).map (fun σ => σ.RM) |>.getD ∅
    This  := fun G C => (c.find G).map (fun σ => σ.This C) |>.getD ∅ }

section all_data
variable {c : Config} {G : GlobName} {σ : State G}

@[simp] theorem Config.all_data_param (h : c.find G = some σ) : c.all_data.Param G = σ.Param := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_fld₁ (h : c.find G = some σ) : c.all_data.Fld₁ G = σ.Fld₁ := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_fld₂ (h : c.find G = some σ) : c.all_data.Fld₂ G = σ.Fld₂ := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_ret (h : c.find G = some σ) : c.all_data.Ret G = σ.Ret := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_gfld₁ (h : c.find G = some σ) : c.all_data.GFld₁ G = σ.GFld₁ := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_gfld₂ (h : c.find G = some σ) : c.all_data.GFld₂ G = σ.GFld₂ := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_rm (h : c.find G = some σ) : c.all_data.RM G = σ.RM := by
  simp [Config.all_data, h]
@[simp] theorem Config.all_data_this (h : c.find G = some σ) : c.all_data.This G = σ.This := by
  simp [Config.all_data, h]

theorem Config.all_data_fld (h : c.find G = some σ) (i : Idx) : c.all_data.Fld i G = σ.Fld i := by
  cases i <;> simp [Proof.Sigma.Fld, State.Fld, h]

theorem Config.all_data_gfld (h : c.find G = some σ) (i : Idx) : c.all_data.GFld i G = σ.GFld i := by
  cases i <;> simp [Proof.Sigma.GFld, State.GFld, h]

end all_data

def State.ofSigma (Sg : Sigma) (G : GlobName) : State G where
  Param := Sg.Param G
  Fld₁  := Sg.Fld₁ G
  Fld₂  := Sg.Fld₂ G
  Ret   := Sg.Ret G
  GFld₁ := Sg.GFld₁ G
  GFld₂ := Sg.GFld₂ G
  RM    := Sg.RM G
  This  := Sg.This G

theorem Config.all_data_state {G : GlobName} {σ : State G} {F : FixPoints}
    {S : Stack} {Q : Queue}
    : σ = (State.ofSigma (Config.mk G σ F S Q).all_data G) := by
  -- simp [State.ofSigma]
  -- refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- · intro C
  --   have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).Param = σ.Param := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_param (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  -- · intro C
  --   have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).Fld₁ = σ.Fld₁ := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_fld₁ (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  -- · intro C
  --   have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).Fld₂ = σ.Fld₂ := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_fld₂ (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  -- · intro C
  --   have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).Ret = σ.Ret := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_ret (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  -- · have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).GFld₁ = σ.GFld₁ := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_gfld₁ (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  -- · have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).GFld₂ = σ.GFld₂:= by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_gfld₂ (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  -- · intro C hRM
  --   have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).RM = σ.RM := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_rm (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  --   rw [heq]
  --   exact hRM
  -- · intro C
  --   have heq : (State.ofSigma (Config.mk G σ F S Q).all_data G).This = σ.This := by
  --     simp [State.ofSigma]
  --     exact (Config.mk G σ F S Q).all_data_this (Config.find_curState (by rfl) (by simp [Config.curState]) (config_wellformed hstar))
  sorry

end Algorithm
