import Proof.Syntax
import Proof.Semantics
import Proof.Analysis
import Proof.AbstractDetectsCycle
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

namespace Algorithm00

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
  ADep  : Set GlobName

def State.zero (G : GlobName) : State G where
  Param := fun _ => ∅
  Fld₁  := fun _ => ∅
  Fld₂  := fun _ => ∅
  Ret   := fun _ => ∅
  GFld₁ := ∅
  GFld₂ := ∅
  RM    := ∅
  This  := fun _ => ∅
  ADep  := ∅

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

theorem InFixPoint.mono_insert {F : FixPoints} {G G' : GlobName} {σ : State G}
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

theorem KJ.deps_inFixPoint {G : GlobName} {C : ClassName} {σ : State G} {L : Program}
    {F : FixPoints} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJ C σ L F e K D) : ∀ G' ∈ D, InFixPoint F G' := by
  induction h with
  | thisE | paramE | newC | val => simp
  | @proj e i K D hK _ ih =>
      rintro G' (hD | ⟨⟨p, hp, rfl⟩, hne⟩)
      · exact ih G' hD
      · simp only [Set.mem_singleton_iff] at hne
        exact (hK p hp).resolve_left hne
  | gproj hK => rintro G' rfl; exact hK
  | app _ ih => exact ih

theorem KJ0.deps_inFixPoint {G : GlobName} {σ : State G} {L : Program}
    {F : FixPoints} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJ0 σ L F e K D) : ∀ G' ∈ D, InFixPoint F G' := by
  induction h with
  | newC | val => simp
  | @proj e i K D hK _ ih =>
      rintro G' (hD | ⟨⟨p, hp, rfl⟩, hne⟩)
      · exact ih G' hD
      · simp only [Set.mem_singleton_iff] at hne
        exact (hK p hp).resolve_left hne
  | gproj hK => rintro G' rfl; exact hK
  | app _ ih => exact ih

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

theorem KJC.deps_inFixPoint {G : GlobName} {σ : State G} {L : Program} {F : FixPoints}
    {c : Ctx} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJC σ L F c e K D) : ∀ G' ∈ D, InFixPoint F G' := by
  cases c with
  | none => exact KJ0.deps_inFixPoint h
  | some C => exact KJ.deps_inFixPoint h

/-- `Needs σ L F c e G₀`: analysing `e` cannot proceed until `G₀` is solved.

    `projOwner` fires on a projection whose subject may hold an object owned by
    an unsolved `G₀`, whose `Fld` the rule would have to read.  It must exclude
    `p.1 = G`: the object under analysis is unsolved by definition, but its own
    fields are read off the current `σ` — `KJ.proj` does exactly that — so
    without `p.1 ≠ G` every `(new C(e,e)).i` in `G`'s own code would report a
    cycle that `Dep` does not have. -/
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
    (h : ∀ G', G' ∈ σ.ADep → InFixPoint F G') : Prop where
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
  adep  : σ.ADep ⊆ σ'.ADep

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
      this := fun _ => subset_rfl,
      adep := subset_rfl }
  le_trans _ _ _ h₁ h₂ :=
    { param := fun C => (h₁.param C).trans (h₂.param C)
      fld₁  := fun C => (h₁.fld₁ C).trans (h₂.fld₁ C)
      fld₂  := fun C => (h₁.fld₂ C).trans (h₂.fld₂ C)
      ret   := fun C => (h₁.ret C).trans (h₂.ret C)
      gfld₁ := h₁.gfld₁.trans h₂.gfld₁
      gfld₂ := h₁.gfld₂.trans h₂.gfld₂
      rm    := h₁.rm.trans h₂.rm
      this  := fun C => (h₁.this C).trans (h₂.this C)
      adep  := h₁.adep.trans h₂.adep }

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
def State.addDeps {G} (σ : State G) (F : FixPoints) (D : Set GlobName)
    (h : ∀ G₀ ∈ D, InFixPoint F G₀) : State G :=
  { σ with ADep := σ.ADep ∪ ⋃ G₀, ⋃ h₀ : G₀ ∈ D, insert G₀ (F.lookup G₀ (h G₀ h₀)).ADep }

theorem dep_to_fixpoint {G : GlobName} {σ : State G} {L : Program} {F : FixPoints}
    {c : Ctx} {e₁ e₂ : Expr} {K₁ K₂ : Set OPair} {D₁ D₂ : Set GlobName}
    (hK₁ : KJC σ L F c e₁ K₁ D₁) (hK₂ : KJC σ L F c e₂ K₂ D₂) :
    ∀ G₀ ∈ D₁ ∪ D₂, InFixPoint F G₀ := by
  rintro G₀ (h | h)
  · exact hK₁.deps_inFixPoint G₀ h
  · exact hK₂.deps_inFixPoint G₀ h

inductive Grow (L : Program) (F : FixPoints) (G : GlobName) : State G → State G → Prop
  | rmInit {σ e₁ e₂ K₁ K₂} :
      Program.HasObject L G e₁ e₂ → Calls0 σ L F e₁ K₁ → Calls0 σ L F e₂ K₂ →
      Grow L F G σ (σ.addRM (K₁ ∪ K₂))
  | rmClosed {σ C body K} :
      C ∈ σ.RM → Program.HasClass L C body → Calls C σ L F body K →
      Grow L F G σ (σ.addRM K)
  | retInit {σ C e K D} (he : Program.HasClass L C e) (hK : KJ C σ L F e K D) :
      Grow L F G σ ((σ.addRet C K).addDeps F D hK.deps_inFixPoint)
  | gfldOne {σ e₁ e₂ K₁ D₁} :
      Program.HasObject L G e₁ e₂ → (hK : KJ0 σ L F e₁ K₁ D₁) →
      Grow L F G σ ({ σ with GFld₁ := σ.GFld₁ ∪ K₁ }.addDeps F D₁ hK.deps_inFixPoint)
  | gfldTwo {σ e₁ e₂ K₂ D₂} :
      Program.HasObject L G e₁ e₂ → (hK : KJ0 σ L F e₂ K₂ D₂) →
      Grow L F G σ ({ σ with GFld₂ := σ.GFld₂ ∪ K₂ }.addDeps F D₂ hK.deps_inFixPoint)
  | fld {σ c Dc e₁ e₂ K₁ K₂ D₁ D₂} :
      RE G σ L c (Expr.newC Dc e₁ e₂) → (hK₁ : KJC σ L F c e₁ K₁ D₁) → (hK₂ : KJC σ L F c e₂ K₂ D₂) →
      Grow L F G σ ((((σ.addFldAt Idx.one Dc K₁).addFldAt Idx.two Dc K₂)).addDeps F (D₁ ∪ D₂)
        (dep_to_fixpoint hK₁ hK₂))
  | param {σ c e₁ e₂ K₁ K₂ D₁ D₂} :
      RE G σ L c (Expr.app e₁ e₂) → (hK₁ : KJC σ L F c e₁ K₁ D₁) → (hK₂ : KJC σ L F c e₂ K₂ D₂) →
      Grow L F G σ ((σ.addParamAt (classes K₁) K₂).addDeps F (D₁ ∪ D₂)
        (dep_to_fixpoint hK₁ hK₂))
  | thisG {σ c e₁ e₂ K₁ D₁} :
      RE G σ L c (Expr.app e₁ e₂) → (hK : KJC σ L F c e₁ K₁ D₁) →
      Grow L F G σ ((σ.addThisAt (classes K₁) (objects K₁)).addDeps F D₁ hK.deps_inFixPoint)
  | adep {σ c G₀ i} (h : InFixPoint F G₀) :
      RE G σ L c (Expr.gproj G₀ i) →
      Grow L F G σ (σ.addDeps F {G₀} (by rintro _ rfl; exact h))

def Stable (L : Program) (F : FixPoints) (G : GlobName) (σ : State G) : Prop :=
  (∀ σ', Grow L F G σ σ' → σ' ≤ σ) ∧
  (∀ c e G₀, RE G σ L c e → ¬ Needs σ L F c e G₀)

structure ADepOk (G : GlobName) (σ : State G) (L : Program) (F : FixPoints) : Prop where
  direct : ∀ {c G₀ i}, RE G σ L c (Expr.gproj G₀ i) → G₀ ∈ σ.ADep
  trans : ∀ {G₀} (_ : G₀ ∈ σ.ADep) (h : InFixPoint F G₀),
      (F.lookup G₀ h).ADep ⊆ σ.ADep

structure OwnersOk (G : GlobName) (σ : State G) : Prop where
  param : ∀ {C p}, p ∈ σ.Param C → p.1 = G ∨ p.1 ∈ σ.ADep
  fld₁ : ∀ {C p}, p ∈ σ.Fld₁ C → p.1 = G ∨ p.1 ∈ σ.ADep
  fld₂ : ∀ {C p}, p ∈ σ.Fld₂ C → p.1 = G ∨ p.1 ∈ σ.ADep
  ret : ∀ {C p}, p ∈ σ.Ret C → p.1 = G ∨ p.1 ∈ σ.ADep
  gfld₁ : ∀ {p}, p ∈ σ.GFld₁ → p.1 = G ∨ p.1 ∈ σ.ADep
  gfld₂ : ∀ {p}, p ∈ σ.GFld₂ → p.1 = G ∨ p.1 ∈ σ.ADep
  this : ∀ {C G'}, G' ∈ σ.This C → G' = G ∨ G' ∈ σ.ADep

theorem OwnersOk.fld {G : GlobName} {σ : State G} (h : OwnersOk G σ) {i : Idx}
    {C : ClassName} {p : OPair} (hp : p ∈ σ.Fld i C) : p.1 = G ∨ p.1 ∈ σ.ADep := by
  cases i
  · exact h.fld₁ hp
  · exact h.fld₂ hp

theorem OwnersOk.gfld {G : GlobName} {σ : State G} (h : OwnersOk G σ) {i : Idx}
    {p : OPair} (hp : p ∈ σ.GFld i) : p.1 = G ∨ p.1 ∈ σ.ADep := by
  cases i
  · exact h.gfld₁ hp
  · exact h.gfld₂ hp

structure Done (G : GlobName) (σ : State G) (L : Program) (F : FixPoints) : Prop where
  solved : ∀ G' ∈ σ.ADep, InFixPoint F G'
  fixpoint : FixPoint G σ L F solved
  adep : ADepOk G σ L F
  owners : OwnersOk G σ

inductive Config
  | mk (G : GlobName) (σ : State G) (F : FixPoints) (S : Stack) (Q : Queue)
  | done (F : FixPoints)
  | cycle (G : GlobName)
  deriving Inhabited

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

/-- The initial configuration: solve the first object of `L`, queue the rest.
    The well-formedness hypothesis `hL : L.HasMain` is what supplies the head of
    `L.GlobNames`; it is a hypothesis carried by every theorem about a run, not
    an axiom (see `Program.HasMain`). -/
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

/-- Declarative reachability inside a solved object is algorithmic reachability
    of its own state. -/
theorem re_of_glue {L : Program} {F : FixPoints} {G : GlobName} {σ : State G}
    (hσ : F G = some σ) {c : Ctx} {e : Expr} (h : Proof.RE F.glue L G c e) :
    RE G σ L c e := by
  induction h with
  | init₁ ho => exact RE.init₁ ho
  | init₂ ho => exact RE.init₂ ho
  | body hC hcl => exact RE.body (by rwa [FixPoints.glue_rm hσ] at hC) hcl
  | proj _ ih => exact RE.proj ih
  | newC₁ _ ih => exact RE.newC₁ ih
  | newC₂ _ ih => exact RE.newC₂ ih
  | app₁ _ ih => exact RE.app₁ ih
  | app₂ _ ih => exact RE.app₂ ih

def Edge (σ : Proof.Sigma) (L : Program) (G G₀ : GlobName) : Prop :=
  ∃ (c : Ctx) (i : Idx), Proof.RE σ L G c (Expr.gproj G₀ i)

/-- If G depends on G₀, then there is a walk from G to G₀. -/
theorem transGen_edge_of_depJ {σ : Proof.Sigma} {L : Program} {G G₀ : GlobName}
    (h : Proof.DepJ σ L G G₀) : Relation.TransGen (Edge σ L) G G₀ := by
  induction h with
  | @direct G G₀ c i hre => exact Relation.TransGen.single ⟨c, i, hre⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

def AEdge (L : Program) (F : FixPoints) (G G₀ : GlobName) : Prop :=
  ∃ (σ : State G) (c : Ctx) (i : Idx),
    Relation.ReflTransGen (Grow L F G) (State.zero G) σ ∧ RE G σ L c (Expr.gproj G₀ i)

/-- **Declarative reachability inside `G` is algorithmic reachability, up to
    growing `G`'s state.**

    `Proof.RE σₐ L G` consults `σₐ` in exactly one rule — `Proof.RE.body`, which
    enters the body of a class `C ∈ σₐ.RM G`.  Every other rule is structural:
    `init₁`/`init₂` come straight from the program, and `proj`/`newC`/`app` only
    descend into a subexpression, so they transfer to the algorithm's `RE`
    verbatim, at the very state the induction hypothesis hands back.

    So the whole bridge reduces to the `RM` case, which is what `hRM` assumes:
    every class the declarative analysis considers reachable from `G` is one the
    algorithm can grow into `G`'s own `RM` — or else `P`, the escape hatch left
    abstract here and instantiated with "`Solve` reports a cycle" in
    `Edge_to_AEdge` below.

    Some such hypothesis is unavoidable: `σₐ` is an *arbitrary* `Sigma`, and one
    with a fat `RM` (say `σₐ.RM G = univ`, which is even a `Proof.FixPoint`)
    carries `Proof.RE` facts about class bodies that no run of `Solve` can ever
    look at.  It is meant to be discharged where `σₐ` is the algorithm's own
    output: there `σₐ.RM G` *is* the `RM` of a state reached from `State.zero G`
    by `Grow`. -/
theorem re_to_grow_re {σₐ : Proof.Sigma} {L : Program} {G : GlobName} {F : FixPoints}
    {P : Prop}
    (hRM : ∀ C ∈ σₐ.RM G,
      P ∨ ∃ σ : State G, Relation.ReflTransGen (Grow L F G) (State.zero G) σ ∧ C ∈ σ.RM)
    {c : Ctx} {e : Expr} (h : Proof.RE σₐ L G c e) :
    P ∨ ∃ σ : State G, Relation.ReflTransGen (Grow L F G) (State.zero G) σ ∧ RE G σ L c e := by
  induction h with
  | init₁ ho => exact Or.inr ⟨State.zero G, Relation.ReflTransGen.refl, RE.init₁ ho⟩
  | init₂ ho => exact Or.inr ⟨State.zero G, Relation.ReflTransGen.refl, RE.init₂ ho⟩
  -- the only rule that consults `σₐ`
  | body hC hcl => exact (hRM _ hC).imp id fun ⟨σ, hgrow, hCσ⟩ => ⟨σ, hgrow, RE.body hCσ hcl⟩
  -- the structural rules keep the state the induction hypothesis produced
  | proj _ ih => exact ih.imp id fun ⟨σ, hgrow, hre⟩ => ⟨σ, hgrow, RE.proj hre⟩
  | newC₁ _ ih => exact ih.imp id fun ⟨σ, hgrow, hre⟩ => ⟨σ, hgrow, RE.newC₁ hre⟩
  | newC₂ _ ih => exact ih.imp id fun ⟨σ, hgrow, hre⟩ => ⟨σ, hgrow, RE.newC₂ hre⟩
  | app₁ _ ih => exact ih.imp id fun ⟨σ, hgrow, hre⟩ => ⟨σ, hgrow, RE.app₁ hre⟩
  | app₂ _ ih => exact ih.imp id fun ⟨σ, hgrow, hre⟩ => ⟨σ, hgrow, RE.app₂ hre⟩

/-- `Edge_to_AEdge` with the escape hatch left abstract, exactly as in
    `re_to_grow_re`: a cycle report is one particular instantiation of `P`.
    Stated at a node `H` that need not be the object the run starts from, so it
    can be applied at every vertex of a walk. -/
theorem Edge_to_AEdge_gen {σₐ : Proof.Sigma} {L : Program} {H G₀ : GlobName} {F : FixPoints}
    {P : Prop}
    (hRM : ∀ C ∈ σₐ.RM H,
      P ∨ ∃ σ : State H, Relation.ReflTransGen (Grow L F H) (State.zero H) σ ∧ C ∈ σ.RM)
    (h : Edge σₐ L H G₀) : P ∨ AEdge L F H G₀ := by
  obtain ⟨c, i, hre⟩ := h
  exact (re_to_grow_re hRM hre).imp id fun ⟨σ, hgrow, hre'⟩ => ⟨σ, c, i, hgrow, hre'⟩

theorem Edge_to_AEdge {σₐ : Proof.Sigma} {L : Program} {G G₀ G' : GlobName} {F : FixPoints}
    {S : Stack} {Q : Queue}
    (hRM : ∀ C ∈ σₐ.RM G, Solve.Star L (.mk G (State.zero G) F S Q) (.cycle G') ∨
      ∃ σ : State G, Relation.ReflTransGen (Grow L F G) (State.zero G) σ ∧ C ∈ σ.RM)
    (h : Edge σₐ L G G₀)
    : Solve.Star L (.mk G (State.zero G) F S Q) (.cycle G') ∨ AEdge L F G G₀ :=
  Edge_to_AEdge_gen hRM h

/-- The object-level fragment needs no escape hatch: if the declarative analysis
    puts no class in `G`'s `RM`, `Proof.RE.body` never fires and every edge is
    already visible from `State.zero G`. -/
theorem Edge_to_AEdge_of_rm_empty {σₐ : Proof.Sigma} {L : Program} {G G₀ : GlobName}
    {F : FixPoints} (hRM : σₐ.RM G = ∅) (h : Edge σₐ L G G₀) : AEdge L F G G₀ := by
  obtain ⟨c, i, hre⟩ := h
  obtain ⟨σ, hgrow, hre'⟩ :=
    (re_to_grow_re (P := False) (F := F)
      (fun C hC => absurd (hRM ▸ hC) (Set.notMem_empty C)) hre).resolve_left not_false
  exact ⟨σ, c, i, hgrow, hre'⟩

/-- **A declarative dependency *path* is an algorithmic one** — the transitive
    closure of `Edge_to_AEdge_gen`.

    The walk is not built by hand: `Relation.TransGen`'s own recursion already
    exposes it one edge at a time, so `exists_walk_of_transGen` is not needed
    here.  `single` is `Edge_to_AEdge_gen` at the sole edge; `tail` turns the
    path `G ⟶⁺ b` handed back by the induction hypothesis and the last edge
    `b ⟶ c` into `G ⟶⁺ c`, with either half able to escape through `P`.

    Note that `hRM` must range over *every* object, not just `G`: the induction
    applies `Edge_to_AEdge_gen` at each vertex the path passes through, and the
    `Proof.RE.body` rule may fire at any of them.  The escape hatch `P` stays a
    single fixed proposition — it is what the whole run reports, so it does not
    depend on which vertex escaped. -/
theorem Trans_Edge_to_Trans_AEdge_gen {σₐ : Proof.Sigma} {L : Program} {G G₀ : GlobName}
    {F : FixPoints} {P : Prop}
    (hRM : ∀ H : GlobName, ∀ C ∈ σₐ.RM H,
      P ∨ ∃ σ : State H, Relation.ReflTransGen (Grow L F H) (State.zero H) σ ∧ C ∈ σ.RM)
    (h : Relation.TransGen (Edge σₐ L) G G₀) :
    P ∨ Relation.TransGen (AEdge L F) G G₀ := by
  induction h with
  | single hedge => exact (Edge_to_AEdge_gen (hRM _) hedge).imp id Relation.TransGen.single
  | tail _ hedge ih =>
      rcases ih with hP | hpath
      · exact Or.inl hP
      · exact (Edge_to_AEdge_gen (hRM _) hedge).imp id hpath.tail

theorem Trans_Edge_to_Trans_AEdge {σₐ : Proof.Sigma} {L : Program} {G G₀ G' : GlobName}
    {F : FixPoints} {S : Stack} {Q : Queue}
    (hRM : ∀ H : GlobName, ∀ C ∈ σₐ.RM H,
      Solve.Star L (.mk G (State.zero G) F S Q) (.cycle G') ∨
        ∃ σ : State H, Relation.ReflTransGen (Grow L F H) (State.zero H) σ ∧ C ∈ σ.RM)
    (h : Relation.TransGen (Edge σₐ L) G G₀)
    : Solve.Star L (.mk G (State.zero G) F S Q) (.cycle G') ∨
      Relation.TransGen (AEdge L F) G G₀ :=
  Trans_Edge_to_Trans_AEdge_gen hRM h

/-- The object-level fragment again needs no escape hatch. -/
theorem Trans_Edge_to_Trans_AEdge_of_rm_empty {σₐ : Proof.Sigma} {L : Program}
    {G G₀ : GlobName} {F : FixPoints} (hRM : ∀ H : GlobName, σₐ.RM H = ∅)
    (h : Relation.TransGen (Edge σₐ L) G G₀) : Relation.TransGen (AEdge L F) G G₀ :=
  (Trans_Edge_to_Trans_AEdge_gen (P := False) (F := F)
    (fun H C hC => absurd (hRM H ▸ hC) (Set.notMem_empty C)) h).resolve_left not_false

section Walks
variable {α : Type*} {r : α → α → Prop}

/-- A `TransGen` step is a walk: `a → l₀ → ⋯ → b`. -/
theorem exists_walk_of_transGen {a b : α} (h : Relation.TransGen r a b) :
    ∃ l : List α, List.IsChain r (a :: (l ++ [b])) := by
  induction h with
  | @single b hab => exact ⟨[], by simpa using hab⟩
  | @tail b c _ hbc ih =>
      obtain ⟨l, hl⟩ := ih
      refine ⟨l ++ [b], ?_⟩
      have hcat : (l ++ [b]) ++ [c] = l ++ [b, c] := by simp
      rw [hcat]
      exact List.isChain_cons_append_cons_cons.2 ⟨hl, hbc, List.isChain_singleton c⟩

/-- **Every vertex of a walk is reachable from its source.**  What a walk gives
    pointwise — `x` occurs somewhere in `a :: l` — the relation gives as a path
    `a ⟶* x`, by following the chain up to `x`. -/
theorem reflTransGen_of_mem_isChain : ∀ (l : List α) (a : α), List.IsChain r (a :: l) →
    ∀ x ∈ a :: l, Relation.ReflTransGen r a x := by
  intro l
  induction l with
  | nil =>
      intro a _ x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      subst hx
      exact Relation.ReflTransGen.refl
  | cons b l ih =>
      intro a hchain x hx
      rw [List.isChain_cons_cons] at hchain
      rcases List.mem_cons.1 hx with rfl | hx'
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.head hchain.1 (ih b hchain.2 x hx')

/-- **The first repetition in a list.**  Scan `l` from the left with `v` holding
    the elements already seen: either nothing repeats, or the scan stops at the
    first element `b` that was seen before.  What matters is not that `b` repeats
    but that everything strictly *before* it is still pairwise distinct — that is
    what makes the cycle `b` closes a simple one. -/
theorem first_dup : ∀ (l v : List α), v.Nodup →
    (v ++ l).Nodup ∨
    ∃ (p q : List α) (b : α), l = p ++ b :: q ∧ (v ++ p).Nodup ∧ b ∈ v ++ p := by
  intro l
  induction l with
  | nil => intro v hv; exact Or.inl (by simpa using hv)
  | cons c l ih =>
      intro v hv
      by_cases hc : c ∈ v
      · exact Or.inr ⟨[], l, c, rfl, by simpa using hv, by simpa using hc⟩
      · have hv' : (v ++ [c]).Nodup :=
          hv.append (List.nodup_singleton c) (List.disjoint_singleton.2 hc)
        rcases ih (v ++ [c]) hv' with hnd | ⟨p, q, b, rfl, hnd, hmem⟩
        · exact Or.inl (by simpa using hnd)
        · exact Or.inr ⟨c :: p, q, b, rfl, by simpa using hnd, by simpa using hmem⟩

/-- **The first element of `l` satisfying `p`.**  Either `p` holds nowhere on
    `l`, or `l` splits as `m ++ x :: r` with `p x` and `p` failing everywhere on
    the prefix `m` — the split a run needs when it must walk `m` unimpeded before
    stopping at `x`. -/
theorem first_sat {p : α → Prop} : ∀ l : List α,
    (∀ x ∈ l, ¬ p x) ∨
    ∃ (m r : List α) (x : α), l = m ++ x :: r ∧ p x ∧ ∀ y ∈ m, ¬ p y := by
  intro l
  induction l with
  | nil => exact Or.inl (by simp)
  | cons c l ih =>
      by_cases hc : p c
      · exact Or.inr ⟨[], l, c, rfl, hc, by simp⟩
      · rcases ih with hnone | ⟨m, r, x, rfl, hx, hm⟩
        · refine Or.inl fun y hy => ?_
          rcases List.mem_cons.1 hy with rfl | hy'
          · exact hc
          · exact hnone y hy'
        · refine Or.inr ⟨c :: m, r, x, rfl, hx, fun y hy => ?_⟩
          rcases List.mem_cons.1 hy with rfl | hy'
          · exact hc
          · exact hm y hy'

/-- **Every closed walk contains a simple cycle** — either through its basepoint,
    or through the first vertex the walk revisits.  Scanning `a`'s walk and
    stopping at the first repetition `b` leaves a repetition-free approach
    `a :: m` followed by a simple cycle `b :: (l ++ [b])`; if that first
    repetition is `a` itself, the walk's own prefix is already a simple cycle
    through `a`.

    The `Nodup` of the second disjunct covers the whole approach
    `a :: (m ++ b :: l)`, not just the cycle `b :: l`: `Solve` suspends every
    object it walks through, so `m` must be repetition-free too, and disjoint
    from the cycle. -/
theorem nodup_or_simple_cycle {a : α} (h : Relation.TransGen r a a) :
    (∃ l : List α, List.IsChain r (a :: (l ++ [a])) ∧ (a :: l).Nodup) ∨
    (∃ m n l : List α, ∃ b : α,
      List.IsChain r (a :: (m ++ (((b :: (l ++ [b])) ++ n) ++ [a]))) ∧
      (a :: (m ++ b :: l)).Nodup) := by
  obtain ⟨w, hw⟩ := exists_walk_of_transGen h
  rcases first_dup w ([a]) (List.nodup_singleton a) with hnd | ⟨p, q, b, rfl, hnd, hmem⟩
  · -- nothing repeats: the walk is already a simple cycle through `a`
    exact Or.inl ⟨w, hw, by simpa using hnd⟩
  · rw [List.singleton_append] at hnd hmem
    rcases List.mem_cons.1 hmem with hba | hbp
    · -- the first repetition is the basepoint: cut the walk there
      rw [hba] at hw
      refine Or.inl ⟨p, ?_, hnd⟩
      rw [show ((p ++ a :: q) ++ [a]) = p ++ a :: (q ++ [a]) by simp] at hw
      exact (List.isChain_cons_split.1 hw).1
    · -- the first repetition is interior: `m` approaches it, `l` closes it
      obtain ⟨m, l, rfl⟩ := List.append_of_mem hbp
      refine Or.inr ⟨m, q, l, b, ?_, hnd⟩
      rw [show (((m ++ b :: l) ++ b :: q) ++ [a]) = m ++ (((b :: (l ++ [b])) ++ q) ++ [a])
        by simp] at hw
      exact hw

end Walks

/-- Growing the current object's state is a run of `Solve.step`s. -/
theorem solve_star_of_grow {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G}
    {S : Stack} {Q : Queue} (h : Relation.ReflTransGen (Grow L F G) σ σ') :
    Solve.Star L (.mk G σ F S Q) (.mk G σ' F S Q) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hgrow ih => exact ih.tail (Solve.step hgrow)

theorem solve_cycle_of_walk {L : Program} {F : FixPoints}
    {G : GlobName} : ∀ (l : List GlobName) (H : GlobName) (S : Stack) (Q : Queue),
      (∀ G' ∈ H :: (l ++ [G]), ¬ InFixPoint F G') →
      List.IsChain (AEdge L F) (H :: (l ++ [G])) →
      (G = H ∨ G ∈ Stack.globs S) →
      (∀ x ∈ l, x ≠ H ∧ x ∉ Stack.globs S) → l.Nodup →
      Solve.Star L (.mk H (State.zero H) F S Q) (.cycle G) := by
  intro l
  induction l with
  | nil =>
      intro H S Q hF hchain hG _ _
      obtain ⟨σ, c, i, hgrow, hre⟩ : AEdge L F H G := List.isChain_pair.1 (by simpa using hchain)
      exact (solve_star_of_grow hgrow).tail
        (Solve.cycle hre (Needs.gproj (hF G (by simp))) hG)
  | cons b l ih =>
      intro H S Q hF hchain hG hdisj hnd
      rw [List.cons_append, List.isChain_cons_cons] at hchain
      obtain ⟨⟨σ, c, i, hgrow, hre⟩, hrest⟩ := hchain
      obtain ⟨hbH, hbS⟩ := hdisj b List.mem_cons_self
      obtain ⟨hbl, hndl⟩ := List.nodup_cons.1 hnd
      have hstep : Solve L (.mk H σ F S Q)
          (.mk b (State.zero b) F (⟨H, σ⟩ :: S) (Q.remove b)) :=
        Solve.suspend hre (Needs.gproj (hF b (by simp))) hbH hbS
      have hglobs : Stack.globs (⟨H, σ⟩ :: S) = H :: Stack.globs S := rfl
      -- the tail of the chain, `b :: (l ++ [G])`, is a sublist of `H :: ((b :: l) ++ [G])`
      have hF' : ∀ G' ∈ b :: (l ++ [G]), ¬ InFixPoint F G' :=
        fun x hx => hF x (List.mem_cons_of_mem H hx)
      refine (solve_star_of_grow hgrow).trans (Relation.ReflTransGen.head hstep
        (ih b (⟨H, σ⟩ :: S) (Q.remove b) hF' hrest ?_ ?_ hndl))
      · rcases hG with rfl | hG
        · exact Or.inr (hglobs ▸ List.mem_cons_self)
        · exact Or.inr (hglobs ▸ List.mem_cons_of_mem H hG)
      · intro x hx
        obtain ⟨hxH, hxS⟩ := hdisj x (List.mem_cons_of_mem b hx)
        refine ⟨fun hxb => hbl (hxb ▸ hx), ?_⟩
        rw [hglobs]
        simpa [hxH] using hxS

/-- **A walk that runs into the stack reports a cycle there.**  Nothing stops the
    run that reaches `G` from already holding some vertex of `G`'s walk suspended
    on its stack — and it need not be stopped: the run then simply never gets as
    far as closing its own cycle.  It suspends along the walk up to the *first*
    vertex `x` that is on the stack, where `Solve.cycle` fires instead of
    `Solve.suspend`, and reports `x`.

    This is what lets the callers below assume their walk avoids the stack: in
    the alternative they already have the cycle they were after, just at another
    object — which is why the conclusion, like `algo_detects_dep`'s, is `∃ G'`.
    Picking the first hit is what keeps the prefix `p` stack-free, so that the
    run really does reach `x`. -/
theorem solve_cycle_of_stack_hit {L : Program} {F : FixPoints} {G z : GlobName}
    (w : List GlobName) (S : Stack) (Q : Queue)
    (hF : ∀ G' ∈ G :: (w ++ [z]), ¬ InFixPoint F G')
    (hchain : List.IsChain (AEdge L F) (G :: (w ++ [z])))
    (hnd : (G :: w).Nodup)
    (hhit : ∃ x ∈ w, x ∈ Stack.globs S) :
    ∃ G', Solve.Star L (.mk G (State.zero G) F S Q) (.cycle G') := by
  obtain ⟨hGw, hwnd⟩ := List.nodup_cons.1 hnd
  rcases first_sat (p := fun x => x ∈ Stack.globs S) w with hfree | ⟨p, q, x, rfl, hxS, hp⟩
  · obtain ⟨y, hy, hyS⟩ := hhit
    exact absurd hyS (hfree y hy)
  -- everything strictly before `x` is off the stack, so the run suspends its way
  -- along `p` and fires `Solve.cycle` on the edge into `x`
  rw [show ((p ++ x :: q) ++ [z]) = p ++ x :: (q ++ [z]) by simp] at hchain
  refine ⟨x, solve_cycle_of_walk p G S Q (fun y hy => hF y ?_)
    (List.isChain_cons_split.1 hchain).1 (Or.inr hxS)
    (fun y hy => ⟨fun hyG => hGw (hyG ▸ List.mem_append_left _ hy), hp y hy⟩)
    (List.Nodup.of_append_left hwnd)⟩
  simp only [List.mem_cons, List.mem_append] at hy ⊢
  tauto

theorem solve_walk_suspend {L : Program} {F : FixPoints} :
    ∀ (m : List GlobName) (H b : GlobName) (S : Stack) (Q : Queue),
      (∀ G' ∈ m ++ [b], ¬ InFixPoint F G') →
      List.IsChain (AEdge L F) (H :: (m ++ [b])) →
      -- only the objects the run suspends *onto* must be off the stack; `H`, which
      -- it starts at and merely pushes, may be on it already
      (H :: m).Nodup → (∀ x ∈ m, x ∉ Stack.globs S) →
      b ∉ H :: m → b ∉ Stack.globs S →
      ∃ (S' : Stack) (Q' : Queue),
        Solve.Star L (.mk H (State.zero H) F S Q) (.mk b (State.zero b) F S' Q') ∧
        ∀ x, x ∈ Stack.globs S' ↔ (x ∈ H :: m ∨ x ∈ Stack.globs S) := by
  intro m
  induction m with
  | nil =>
      intro H b S Q hF hchain _ _ hbH hbS
      obtain ⟨σ, c, i, hgrow, hre⟩ : AEdge L F H b := List.isChain_pair.1 (by simpa using hchain)
      refine ⟨⟨H, σ⟩ :: S, Q.remove b, (solve_star_of_grow hgrow).tail
        (Solve.suspend hre (Needs.gproj (hF b (by simp))) (by simpa using hbH) hbS), ?_⟩
      intro x
      simp [Stack.globs]
  | cons d m ih =>
      intro H b S Q hF hchain hnd hS hbH hbS
      rw [List.cons_append, List.isChain_cons_cons] at hchain
      obtain ⟨⟨σ, c, i, hgrow, hre⟩, hrest⟩ := hchain
      obtain ⟨hHm, hndm⟩ := List.nodup_cons.1 hnd
      have hglobs : Stack.globs (⟨H, σ⟩ :: S) = H :: Stack.globs S := rfl
      have hstep : Solve L (.mk H σ F S Q)
          (.mk d (State.zero d) F (⟨H, σ⟩ :: S) (Q.remove d)) :=
        Solve.suspend hre (Needs.gproj (hF d (by simp)))
          (fun hdH => hHm (hdH ▸ List.mem_cons_self))
          (hS d List.mem_cons_self)
      obtain ⟨S', Q', hstar, hmem⟩ :=
        ih d b (⟨H, σ⟩ :: S) (Q.remove d)
          (fun x hx => hF x (List.mem_cons_of_mem d hx)) hrest hndm
          (fun x hx => by
            rw [hglobs]
            simp only [List.mem_cons, not_or]
            exact ⟨fun hxH => hHm (hxH ▸ List.mem_cons_of_mem d hx),
              hS x (List.mem_cons_of_mem d hx)⟩)
          (fun hb => hbH (List.mem_cons_of_mem H hb))
          (by
            rw [hglobs]
            simp only [List.mem_cons, not_or]
            exact ⟨fun hbH' => hbH (hbH' ▸ List.mem_cons_self), hbS⟩)
      refine ⟨S', Q', (solve_star_of_grow hgrow).trans
        (Relation.ReflTransGen.head hstep hstar), fun x => ?_⟩
      rw [hmem x, hglobs]
      simp only [List.mem_cons]
      tauto

theorem solve_cycle_of_inner_walk {L : Program} {F : FixPoints}
    {G b : GlobName} (m n l : List GlobName) (S : Stack) (Q : Queue)
    (hF : ∀ G' ∈ m ++ b :: l, ¬ InFixPoint F G')
    (hchain : List.IsChain (AEdge L F) (G :: (m ++ (((b :: (l ++ [b])) ++ n) ++ [G]))))
    (hnd : (G :: (m ++ b :: l)).Nodup)
    (hS : ∀ x ∈ m ++ b :: l, x ∉ Stack.globs S) :
    Solve.Star L (.mk G (State.zero G) F S Q) (.cycle b) := by
  -- split the walk at the two occurrences of `b`: approach, cycle, and the
  -- unused tail back to `G`
  rw [show (m ++ (((b :: (l ++ [b])) ++ n) ++ [G])) = (m ++ b :: l) ++ b :: (n ++ [G])
    by simp] at hchain
  have hpre := (List.isChain_cons_split.1 hchain).1
  rw [show ((m ++ b :: l) ++ [b]) = m ++ b :: (l ++ [b]) by simp] at hpre
  obtain ⟨happ, hcyc⟩ := List.isChain_cons_split.1 hpre
  -- what `Nodup` of the approach buys us
  obtain ⟨hG, hrest⟩ := List.nodup_cons.1 hnd
  obtain ⟨hm, hbl, hdisj⟩ := List.nodup_append'.1 hrest
  obtain ⟨hbl', hlnd⟩ := List.nodup_cons.1 hbl
  obtain ⟨S', Q', hstar, hmemS⟩ :=
    solve_walk_suspend m G b S Q
      (fun x hx => hF x (by
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto)) happ
      (List.nodup_cons.2 ⟨fun hGm => hG (List.mem_append_left _ hGm), hm⟩)
      (fun x hx => hS x (List.mem_append_left _ hx))
      (by
        simp only [List.mem_cons, not_or]
        exact ⟨fun hbG => hG (hbG ▸ List.mem_append_right _ List.mem_cons_self),
          fun hbm => hdisj hbm List.mem_cons_self⟩)
      (hS b (List.mem_append_right _ List.mem_cons_self))
  refine hstar.trans
    (solve_cycle_of_walk l b S' Q'
      (fun x hx => hF x (by
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx ⊢
        tauto))
      hcyc (Or.inl rfl) ?_ hlnd)
  intro x hx
  refine ⟨fun hxb => hbl' (hxb ▸ hx), ?_⟩
  have hxml : x ∈ m ++ b :: l := List.mem_append_right _ (List.mem_cons_of_mem b hx)
  rw [hmemS x]
  simp only [List.mem_cons, not_or]
  exact ⟨⟨fun hxG => hG (hxG ▸ hxml), fun hxm => hdisj hxm (List.mem_cons_of_mem b hx)⟩,
    hS x hxml⟩

/-- **If the declarative analysis detects a cycle from `G` to `G`, the algorithm
    will detect a cycle.**

    * L = [ class C { G.1 },        -- never instantiated, never called
      object G { true, true } ]

      Declaratively, with σ_top: "C" ∈ σ_top.RM G = univ and L.HasClass "C" (gproj G one),
      so RE.body gives Proof.RE σ_top L G (some "C") (gproj G one), so DepJ.direct gives
      G ∈ Dep σ_top L G. The hypothesis h of algo_detects_dep holds, and
      σ_top is a genuine Proof.FixPoint.

      Algorithmically: G's initializers are true/true. Nothing calls anything, so
      Grow adds nothing, Needs never fires, G is Stable immediately and the run
      reaches .done. No .cycle configuration is reachable at all, so the conclusion
      ∃ G', Solve.Star L (Config.start L hL) (.cycle G') is false.

    * `hstart` connects `Config.start L hL`, which begins at the head of
      `L.GlobNames`, to `G`'s own start configuration.  It is `.refl` when `G`
      *is* that head object, and otherwise is the business of
      `solve_terminates`: no rule takes the run off the current object until
      that object is `Stable`, so reaching `G` from an unrelated start is a
      termination fact, not a reachability one. -/
theorem algo_detects_dep {G : GlobName} {σ : Proof.Sigma} {L : Program}
    {F : FixPoints} {Q : Queue} {S : Stack} (hL : L.HasMain)
    (hstart : Solve.Star L (Config.start L hL) (.mk G (State.zero G) F S Q))
    (hF : ∀ H : GlobName, Relation.ReflTransGen (AEdge L F) G H → ¬ InFixPoint F H)
    (hRM : ∀ H : GlobName, ∀ C ∈ σ.RM H,
      (∃ G', Solve.Star L (Config.start L hL) (.cycle G')) ∨
        ∃ σ' : State H, Relation.ReflTransGen (Grow L F H) (State.zero H) σ' ∧ C ∈ σ'.RM)
    (h : G ∈ Proof.Dep σ L G) :
    ∃ G', Solve.Star L (Config.start L hL) (.cycle G') := by
  -- the declarative cycle, as a cycle of edges the algorithm can fire on
  have hEdge : Relation.TransGen (Edge σ L) G G := transGen_edge_of_depJ h
  rcases Trans_Edge_to_Trans_AEdge_gen hRM hEdge with hcycle | hAEChain
  · exact hcycle
  rcases nodup_or_simple_cycle hAEChain with ⟨l, hchain, hnd⟩ | ⟨m, n, l, b, hchain, hnd⟩
  · -- the walk revisits nothing before returning to `G`: `G` itself is reported,
    -- unless the run had already walked into an object still on its stack
    have hreach := reflTransGen_of_mem_isChain _ _ hchain
    have hF' : ∀ G' ∈ G :: (l ++ [G]), ¬ InFixPoint F G' := fun x hx => hF x (hreach x hx)
    by_cases hhit : ∃ x ∈ l, x ∈ Stack.globs S
    · obtain ⟨G', hcycle⟩ := solve_cycle_of_stack_hit l S Q hF' hchain hnd hhit
      exact ⟨G', hstart.trans hcycle⟩
    · push Not at hhit
      obtain ⟨hGl, hndl⟩ := List.nodup_cons.1 hnd
      exact ⟨G, hstart.trans (solve_cycle_of_walk l G S Q hF' hchain
        (Or.inl rfl) (fun x hx => ⟨fun hxG => hGl (hxG ▸ hx), hhit x hx⟩) hndl)⟩
  · -- the walk closes a cycle at an interior `b` first: `b` is reported
    -- `hF` is needed on the approach `m` and the cycle `b :: l`, both of which
    -- the walk passes through before its unused tail `n` back to `G`
    have hreach := reflTransGen_of_mem_isChain _ _ hchain
    by_cases hhit : ∃ x ∈ m ++ b :: l, x ∈ Stack.globs S
    · -- the same escape as above, on the walk up to the closing `b`
      have hpre : List.IsChain (AEdge L F) (G :: ((m ++ b :: l) ++ [b])) := by
        rw [show (m ++ (((b :: (l ++ [b])) ++ n) ++ [G])) = (m ++ b :: l) ++ b :: (n ++ [G])
          by simp] at hchain
        exact (List.isChain_cons_split.1 hchain).1
      obtain ⟨G', hcycle⟩ := solve_cycle_of_stack_hit (m ++ b :: l) S Q
        (fun x hx => hF x (hreach x (by
          simp only [List.mem_cons, List.mem_append] at hx ⊢
          tauto))) hpre hnd hhit
      exact ⟨G', hstart.trans hcycle⟩
    · push Not at hhit
      refine ⟨b, hstart.trans (solve_cycle_of_inner_walk m n l S Q
        (fun x hx => hF x (hreach x ?_)) hchain hnd hhit)⟩
      simp only [List.mem_append, List.mem_cons] at hx ⊢
      tauto

/-! ### The stack is a dependency chain -/

/-- `NeedsDep σ L c`: whatever the configuration `c` may suspend on is a
    declarative dependency of the object `c` is solving. -/
def NeedsDep (σ : Proof.Sigma) (L : Program) : Config → Prop
  | .mk G σₐ F _ _ =>
      ∀ (G₀ : GlobName) (c : Ctx) (e : Expr),
        RE G σₐ L c e → Needs σₐ L F c e G₀ → Proof.DepJ σ L G G₀
  | .done _ => True
  | .cycle _ => True

/-- DECLARATIVE: `DepChain σ L G l`: `l` is a chain of dependants of `G`, innermost first —
    the head of `l` depends on `G`, the next one on the head, and so on.  The
    stack of `Solve`, read through `Stack.globs`, is exactly such a chain. -/
def DepChain (σ : Proof.Sigma) (L : Program) : GlobName → List GlobName → Prop
  | _, [] => True
  | G, H :: r => Proof.DepJ σ L H G ∧ DepChain σ L H r

/-- Everything on the chain depends on its base, by walking the chain down and
    composing the links with `DepJ.trans`. -/
theorem DepChain.mem_dep {σ : Proof.Sigma} {L : Program} :
    ∀ (l : List GlobName) (G H : GlobName), DepChain σ L G l → H ∈ l →
      Proof.DepJ σ L H G := by
  intro l
  induction l with
  | nil => intro _ _ _ hmem; simp at hmem
  | cons b r ih =>
      rintro G H ⟨hb, hr⟩ hmem
      rcases List.mem_cons.1 hmem with rfl | hmem'
      · exact hb
      -- `H` sits below `b`: it depends on `b` by the induction hypothesis, and
      -- `b` depends on `G` by the first link
      · exact (ih b H hr hmem').trans hb

/-- The invariant of a `Solve` run: the stack is a `Dep`-chain based at the
    object under analysis, and a reported cycle really is one. -/
def SolveDep (σ : Proof.Sigma) (L : Program) : Config → Prop
  | .mk G _ _ S _ => DepChain σ L G (Stack.globs S)
  | .done _ => True
  | .cycle G₀ => Proof.DepJ σ L G₀ G₀

/-- SolveDep is preserved over a step -/
theorem solve_dep_step {σ : Proof.Sigma} {L : Program} {c c' : Config}
    (hn : NeedsDep σ L c) (hstep : Solve L c c') (h : SolveDep σ L c) :
    SolveDep σ L c' := by
  cases hstep with
  -- growing the current state touches neither the stack nor the current object
  | step _ => exact h
  -- the rule that builds a link: `G` suspends because it needs `G₀`
  | @suspend G G₀ σₐ F S Q cx e hre hneeds _ _ => exact ⟨hn G₀ cx e hre hneeds, h⟩
  | @cycle G G₀ σₐ F S Q cx e hre hneeds hmem =>
      have hGG₀ : Proof.DepJ σ L G G₀ := hn G₀ cx e hre hneeds
      rcases hmem with rfl | hmem
      · exact hGG₀
      -- `G₀` is on the stack, so it depends on `G`, which depends on `G₀`
      · exact (DepChain.mem_dep _ G G₀ h hmem).trans hGG₀
  -- popping keeps the tail of the chain, which is a chain based at `G'`
  | resume _ => exact h.2
  -- the remaining rules leave the run with an empty stack
  | next _ _ => trivial
  | skip _ => exact h
  | finish _ => trivial

theorem needs_dep_step {σ : Proof.Sigma} {L : Program} {c c' : Config}
    (hstep : Solve L c c') (h : NeedsDep σ L c) :
    NeedsDep σ L c' := by
  cases hstep with
  | @step G σ σ' F S Q hgrow =>
    -- cases hgrow
    -- for each case, Needs is false
    sorry
  | @suspend G G₀ σₐ F S Q cx e hre hneeds _ _ =>

    sorry
  | cycle _ => trivial
  | resume _ => sorry
  | next _ _ => sorry
  | skip _ => exact h
  | finish _ => trivial

/-! #### `NeedsDep` at the start -/

theorem not_inFixPoint_none {G : GlobName} : ¬ InFixPoint (fun _ => none) G := by
  rintro ⟨σ, hσ⟩
  simp at hσ

/-- With an empty fixpoint, `KJ0` on the zero state names only `G`'s own objects. -/
theorem kj0_zero_owner {G : GlobName} {L : Program} {F : FixPoints}
    (hF : ∀ G', ¬ InFixPoint F G') {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJ0 (State.zero G) L F e K D) : ∀ p ∈ K, p.1 = G := by
  induction h with
  | @proj e i K D hK _ _ =>
      intro p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨q, hq, hp⟩ := hp
      -- the owner of `q` is `G` (the fixpoint is empty), so the projection reads
      -- `G`'s own — empty — field map
      rw [dif_pos ((hK q hq).resolve_right (hF _))] at hp
      cases i <;> simp [State.zero, State.Fld] at hp
  | gproj hK => exact absurd hK (hF _)
  | newC => intro p hp; simp only [Set.mem_singleton_iff] at hp; simp [hp]
  | app => intro p hp; simp [State.zero] at hp
  | val => intro p hp; simp at hp

/-- With an empty fixpoint, `KJ` on the zero state names only `G`'s own objects. -/
theorem kj_zero_owner {G : GlobName} {C : ClassName} {L : Program} {F : FixPoints}
    (hF : ∀ G', ¬ InFixPoint F G') {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJ C (State.zero G) L F e K D) : ∀ p ∈ K, p.1 = G := by
  induction h with
  | thisE => intro p hp; simp [State.zero] at hp
  | paramE => intro p hp; simp [State.zero] at hp
  | @proj e i K D hK _ _ =>
      intro p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨q, hq, hp⟩ := hp
      rw [dif_pos ((hK q hq).resolve_right (hF _))] at hp
      cases i <;> simp [State.zero, State.Fld] at hp
  | gproj hK => exact absurd hK (hF _)
  | newC => intro p hp; simp only [Set.mem_singleton_iff] at hp; simp [hp]
  | app => intro p hp; simp [State.zero] at hp
  | val => intro p hp; simp at hp

theorem kjc_zero_owner {G : GlobName} {L : Program} {F : FixPoints}
    (hF : ∀ G', ¬ InFixPoint F G') {c : Ctx} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJC (State.zero G) L F c e K D) : ∀ p ∈ K, p.1 = G := by
  cases c with
  | none => exact kj0_zero_owner hF h
  | some C => exact kj_zero_owner hF h

/-- On the zero state no `RE` derivation can use `RE.body` (`RM = ∅`), and every
    other rule is state-independent, so the algorithm's `RE` is a `Proof.RE` for
    an arbitrary `σ`. -/
theorem re_zero {σ : Proof.Sigma} {G : GlobName} {L : Program} {c : Ctx} {e : Expr}
    (h : RE G (State.zero G) L c e) : Proof.RE σ L G c e := by
  induction h with
  | init₁ ho => exact Proof.RE.init₁ ho
  | init₂ ho => exact Proof.RE.init₂ ho
  | body hC _ => simp [State.zero] at hC
  | proj _ ih => exact Proof.RE.proj ih
  | newC₁ _ ih => exact Proof.RE.newC₁ ih
  | newC₂ _ ih => exact Proof.RE.newC₂ ih
  | app₁ _ ih => exact Proof.RE.app₁ ih
  | app₂ _ ih => exact Proof.RE.app₂ ih

/-- `NeedsDep` for the zero state under an empty fixpoint. -/
theorem needs_zero_dep {σ : Proof.Sigma} {G G₀ : GlobName} {L : Program} {F : FixPoints}
    (hF : ∀ G', ¬ InFixPoint F G') {c : Ctx} {e : Expr}
    (h : Needs (State.zero G) L F c e G₀) :
    RE G (State.zero G) L c e → Proof.DepJ σ L G G₀ := by
  induction h with
  -- impossible: on the zero state every `KJ` pair is owned by `G`
  | projOwner hK hp hne _ => exact fun _ => absurd (kjc_zero_owner hF hK _ hp) hne
  | projSub _ ih => exact fun hre => ih (RE.proj hre)
  | gproj _ => exact fun hre => Proof.DepJ.direct (re_zero hre)
  | appFun _ ih => exact fun hre => ih (RE.app₁ hre)

theorem needs_dep {σ : Proof.Sigma} {L : Program} {c : Config}
    {hL : L.HasMain} (hstar : Solve.Star L (Config.start L hL) c)
    : NeedsDep σ L c := by
  induction hstar with
  | refl =>
      intro G₀ c e hre hneeds
      exact needs_zero_dep (fun _ => not_inFixPoint_none) hneeds hre
  | tail hb hstep ih => exact needs_dep_step hstep ih

theorem solve_dep_star {σ : Proof.Sigma} {L : Program} {c : Config} {hL : L.HasMain}
    (hstar : Solve.Star L (Config.start L hL) c) : SolveDep σ L c := by
  induction hstar with
  | refl => exact trivial -- Config.start has an empty stack
  | tail hb hstep ih => exact solve_dep_step (needs_dep hb) hstep ih

/-- The algorithm reports no cycle that the analysis does not have. -/
theorem no_dep_no_cycle {σ : Proof.Sigma} {L : Program} {hL : L.HasMain}
    (h : ∀ G, ¬ G ∈ Proof.Dep σ L G)
    : ¬(∃ G' : GlobName, Solve.Star L (Config.start L hL) (.cycle G')) := by
  rintro ⟨G', hstar⟩
  exact h G' (solve_dep_star hstar)

/-! ### Termination -/

/-- **Progress**: no configuration of the solver is stuck.

    The case analysis is the algorithm's own: a `Stable` object is popped off
    the stack (`resume`), or the queue is advanced (`skip` / `next`), or — with
    both empty — the run is `finish`ed; an unstable object either `Grow`s
    (`step`) or `Needs` some `G₀`, which is `suspend`ed on unless it is the
    object under analysis or already on the stack, in which case a cycle is
    reported. -/
theorem solve_progress {L : Program} {G : GlobName} {σ : State G} {F : FixPoints}
    {S : Stack} {Q : Queue} : ∃ c', Solve L (.mk G σ F S Q) c' := by
  by_cases hst : Stable L F G σ
  · cases S with
    | cons fr S' =>
        obtain ⟨G', σ'⟩ := fr
        exact ⟨_, Solve.resume hst⟩
    | nil =>
        cases Q with
        | nil => exact ⟨_, Solve.finish hst⟩
        | cons G₀ Q' =>
            by_cases hF : InFixPoint F G₀
            · exact ⟨_, Solve.skip hF⟩
            · exact ⟨_, Solve.next hst hF⟩
  · simp only [Stable, not_and_or] at hst
    rcases hst with h | h
    -- something still to add to the state
    · push Not at h
      obtain ⟨σ', hgrow, -⟩ := h
      exact ⟨_, Solve.step hgrow⟩
    -- something still to be solved first
    · push Not at h
      obtain ⟨c, e, G₀, hre, hneeds⟩ := h
      by_cases hcyc : G₀ = G ∨ G₀ ∈ Stack.globs S
      · exact ⟨_, Solve.cycle hre hneeds hcyc⟩
      · push Not at hcyc
        exact ⟨_, Solve.suspend hre hneeds hcyc.1 hcyc.2⟩

/-- **If the algorithm reports no cycle, it terminates in `.done`.**

    By `solve_progress` a run can always be extended, so the only way to fail
    to reach `.done F` is to run forever; what remains is the well-foundedness
    argument, which is why this is stated — and used — as a black box:

    * The conclusion is existential: it is enough that *one* run terminates,
      not that every one does.  This matters, because `Solve.step` may fire on
      a `Grow` that adds nothing (`Stable` forbids only growth that escapes
      `σ`, and `step` does not test for it), so an adversarial run can `step`
      forever.  The run to build is the one that takes `step` only when it
      strictly increases the state, and the rule `solve_progress` selects
      otherwise.
    * Along such a run each `step` is a strict `<` in `State G`, whose height
      is finite because every set a `Grow` adds is drawn from the classes,
      objects and globals *occurring in `L`* — the ambient `ClassName` and
      `GlobName` are `String`, so the bound comes from the program, not the
      type.
    * `suspend` is the only rule that grows the stack, and it fires only for
      `G₀ ∉ Stack.globs S` with `G₀ ≠ G`, so `Stack.globs S` stays duplicate
      free and the stack is bounded by `L.GlobNames`; `resume`, `next`, `skip`
      and `finish` each shrink the stack or the queue.

    The hypothesis is the *reported* cycle, not the declarative one: it is the
    weaker of the two (`no_dep_no_cycle`), and it is what the caller has. -/
theorem solve_no_reported_cycle_done {L : Program} (hL : L.HasMain)
    (h : ¬ ∃ G' : GlobName, Solve.Star L (Config.start L hL) (.cycle G'))
    : ∃ F : FixPoints, Solve.Star L (Config.start L hL) (.done F) := by
  sorry

/-- If there isn't a cycle, Solve terminates -/
theorem solve_no_cycle_done {L : Program} {σ : Proof.Sigma} (hL : L.HasMain)
    (h : ∀ G, ¬ G ∈ Proof.Dep σ L G)
    : ∃ F : FixPoints, Solve.Star L (Config.start L hL) (.done F) :=
  -- no declarative cycle, so nothing for the algorithm to report
  solve_no_reported_cycle_done hL (no_dep_no_cycle h)

/-- If Solve terminates, there is a fixpoint  -/
theorem solve_done_fixpoint {L : Program} {F : FixPoints} {hL : L.HasMain}
    (h : Solve.Star L (Config.start L hL) (.done F)) : Proof.FixPoint F.glue L := by
  sorry

/-- solve either terminates in a cycle or gives a fix point --/
theorem solve_terminates {L : Program} (hL : L.HasMain)
    {σ : Proof.Sigma} (hσ : Proof.FixPoint σ L):
    (∃ F : FixPoints, Proof.FixPoint F.glue L) ∨
    (∃ G' : GlobName, Solve.Star L (Config.start L hL) (.cycle G')) := by
  sorry

end Algorithm00
