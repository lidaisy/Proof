import Proof.Syntax
import Proof.Semantics
import Proof.Analysis
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
  The algorithm (the constructive counterpart of `Analysis.lean`).

  `Analysis.lean` posits one global `Sigma` and asks that it satisfy `FixPoint`.
  Here the analysis is carried out object by object: a `State G` is the fragment
  of that `Sigma` belonging to a single object `G`, and a `FixPoints` map records
  the objects already solved.  `Solve` schedules the objects: it analyses them in
  an arbitrary order, and when the analysis of `G` turns out to need an object
  `G₀` that is not yet solved, `G` is suspended on a stack and `G₀` is solved
  first.  If `G₀` is itself suspended, the program has an initialisation cycle.

  `Solve` deliberately carries no analysis content: the per-object conditions
  live in `FixPoint`/`ADepOk` and are *checked* when an object is closed.  In
  particular `σ.ADep` is not accumulated by the transition rules — see `ADepOk`.
-/

namespace Algorithm

open Proof (GlobName ClassName OPair Idx Program Expr classes objects)

/-! ## Per-object states -/

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

/-- The all-empty state: what an object's analysis starts from. -/
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

/-! ## The map of solved objects -/

abbrev FixPoints := (G : GlobName) → Option (State G)

def InFixPoint (F : FixPoints) (G : GlobName) : Prop :=
  ∃ σ : State G, F G = some σ

def FixPoints.lookup (F : FixPoints) (G : GlobName) (hIn : InFixPoint F G) : State G :=
  (F G).get (by obtain ⟨σ, hσ⟩ := hIn; simp [hσ])

@[simp] theorem FixPoint.lookup_eq {F : FixPoints} {G : GlobName} {σ : State G}
    (hIn : InFixPoint F G) (h : F G = some σ) : F.lookup G hIn = σ := by
  simp [FixPoints.lookup, h]

/-- Record `G`'s finished state.  Used by the closing rules of `Solve`. -/
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

/-! ## Abstraction -/

/-- `KJ C σ L F e K D`: in class context `C`, expression `e` abstracts to the
    owner-pair set `K`, consulting the fixpoints of exactly the objects in `D`.

    `D` records which entries of `F` this derivation reads, and exists only so
    that those reads are well defined (`KJ.deps_inFixPoint`).  It is *not* the
    dependency set of the object under analysis — that is `σ.ADep`, which mirrors
    `Proof.DepJ` and is governed by `ADepOk`.

    Only `proj` (which reads `Fld` of every owner in the subexpression's `K`) and
    `gproj` (which reads `GFld` of `G₀`) perform cross-object lookups — `app`
    reads `σ.Ret`, i.e. the *current* object's table, matching `σ.Ret G p.2` in
    the declarative `Proof.KJ`. -/
inductive KJ {G : GlobName} (C : ClassName) (σ : State G) (L : Program) (F : FixPoints) :
    Expr → Set OPair → Set GlobName → Prop
  | thisE  : KJ C σ L F Expr.thisE (⋃ G' ∈ σ.This C, {(G', C)}) ∅
  | paramE : KJ C σ L F Expr.paramE (σ.Param C) ∅
  | proj {e i K D} (hK : ∀ p ∈ K, InFixPoint F p.1) :
      KJ C σ L F e K D →
      KJ C σ L F (Expr.proj e i)
        (⋃ p, ⋃ h : p ∈ K, (F.lookup p.1 (hK p h)).Fld i p.2) (D ∪ objects K)
  | gproj {G₀ i} (hK : InFixPoint F G₀) :
      KJ C σ L F (Expr.gproj G₀ i) ((F.lookup G₀ hK).GFld i) {G₀}
  | newC {D e₁ e₂} : KJ C σ L F (Expr.newC D e₁ e₂) {(G, D)} ∅
  | app {e₁ e₂ K₁ D₁} :
      KJ C σ L F e₁ K₁ D₁ → KJ C σ L F (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret p.2) D₁
  | val {v} : KJ C σ L F (Expr.val v) ∅ ∅

inductive KJ0 {G : GlobName} (σ : State G) (L : Program) (F : FixPoints) :
    Expr → Set OPair → Set GlobName → Prop
  | proj {e i K D} (hK : ∀ p ∈ K, InFixPoint F p.1) :
      KJ0 σ L F e K D →
      KJ0 σ L F (Expr.proj e i)
        (⋃ p, ⋃ h : p ∈ K, (F.lookup p.1 (hK p h)).Fld i p.2) (D ∪ objects K)
  | gproj {G₀ i} (hK : InFixPoint F G₀) :
      KJ0 σ L F (Expr.gproj G₀ i) ((F.lookup G₀ hK).GFld i) {G₀}
  | newC {D e₁ e₂} : KJ0 σ L F (Expr.newC D e₁ e₂) {(G, D)} ∅
  | app {e₁ e₂ K₁ D₁} :
      KJ0 σ L F e₁ K₁ D₁ → KJ0 σ L F (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret p.2) D₁
  | val {v} : KJ0 σ L F (Expr.val v) ∅ ∅

/-- Every object a `KJ` derivation consults is already in the fixpoint map: the
    lookups performed inside the derivation are well defined. -/
theorem KJ.deps_inFixPoint {G : GlobName} {C : ClassName} {σ : State G} {L : Program}
    {F : FixPoints} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJ C σ L F e K D) : ∀ G' ∈ D, InFixPoint F G' := by
  induction h with
  | thisE | paramE | newC | val => simp
  | @proj e i K D hK _ ih =>
      rintro G' (hD | ⟨p, hp, rfl⟩)
      · exact ih G' hD
      · exact hK p hp
  | gproj hK => rintro G' rfl; exact hK
  | app _ ih => exact ih

theorem KJ0.deps_inFixPoint {G : GlobName} {σ : State G} {L : Program}
    {F : FixPoints} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (h : KJ0 σ L F e K D) : ∀ G' ∈ D, InFixPoint F G' := by
  induction h with
  | newC | val => simp
  | @proj e i K D hK _ ih =>
      rintro G' (hD | ⟨p, hp, rfl⟩)
      · exact ih G' hD
      · exact hK p hp
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

/-! ## `Needs`: the dual of `KJ`

`KJ.proj` cannot even state its conclusion without `hK : ∀ p ∈ K, InFixPoint F p.1`,
so "the derivation is blocked" is not expressible as a `KJ` premise.  `Needs` is
the missing half: it names an object that must be solved before `e` can be
abstracted at all. -/

/-- `Needs σ L F c e G₀`: abstracting `e` requires reading `G₀`'s fixpoint, and
    `F` does not have it yet.

    The shape mirrors `KJ`: only `proj` (which reads `Fld` of every owner in its
    subexpression's `K`) and `gproj` (which reads `GFld G₀`) consult `F`, and
    `KJ.app` descends only into `e₁`.  Nothing is needed for `newC` or for the
    argument of an application: `KJ` does not look at those subexpressions, and
    they are reached separately by `RE`, which is closed under
    `newC₁`/`newC₂`/`app₂`. -/
inductive Needs {G : GlobName} (σ : State G) (L : Program) (F : FixPoints) :
    Ctx → Expr → GlobName → Prop
  | projOwner {c e i K D p} :
      KJC σ L F c e K D → p ∈ K → ¬ InFixPoint F p.1 →
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
      · by_cases hK : ∀ p ∈ K, InFixPoint F p.1
        · exact Or.inl ⟨_, _, KJ.proj hK h⟩
        · push Not at hK
          obtain ⟨p, hp, hnp⟩ := hK
          exact Or.inr ⟨p.1, Needs.projOwner (c := some C) h hp hnp⟩
      · exact Or.inr ⟨G₀, Needs.projSub h⟩

/-! ## Stack and queue -/

/-- The suspended analyses, innermost first. -/
abbrev Stack := List ((G : GlobName) × State G)

/-- The objects whose analysis is currently suspended. -/
def Stack.globs (S : Stack) : List GlobName := S.map Sigma.fst

/-- The objects not yet started. -/
abbrev Queue := List GlobName

def Queue.remove (Q : Queue) (G : GlobName) :=
match Q with
| [] => []
| g::gs => if g == G then gs else g::(Queue.remove gs G)

/-! ## Reachable expressions and the per-object fixpoint -/

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

/-! ### Monotone updates -/

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

/-- `σ.ADep` really is the set of objects `G` depends on.

    The two clauses mirror `Proof.DepJ.direct` and `Proof.DepJ.trans` one for
    one, which is what makes `dep_subset_adep` an induction on `DepJ` with
    exactly these two cases.  Note that `ADep` is therefore *checked* here rather
    than accumulated by `Solve`: the transition rules never touch it. -/
structure ADepOk (G : GlobName) (σ : State G) (L : Program) (F : FixPoints) : Prop where
  direct : ∀ {c G₀ i}, RE G σ L c (Expr.gproj G₀ i) → G₀ ∈ σ.ADep
  trans : ∀ {G₀} (_ : G₀ ∈ σ.ADep) (h : InFixPoint F G₀),
      (F.lookup G₀ h).ADep ⊆ σ.ADep

/-- Every owner pair stored in `σ`'s tables belongs either to `G` itself or to an
    object `G` has already recorded as a dependency.  Together with `ADepOk` this
    is what rules out *spurious* cycle reports: see `kj_owners`. -/
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

/-- `G`'s analysis is finished: its state is a per-object fixpoint, its
    dependency set is correct, and every object it depends on is solved. -/
structure Done (G : GlobName) (σ : State G) (L : Program) (F : FixPoints) : Prop where
  solved : ∀ G' ∈ σ.ADep, InFixPoint F G'
  fixpoint : FixPoint G σ L F solved
  adep : ADepOk G σ L F
  owners : OwnersOk G σ

/-! ## The scheduler -/

inductive Config
  /-- Analysing `G` with partial state `σ`; `S` is suspended, `Q` not yet started. -/
  | mk (G : GlobName) (σ : State G) (F : FixPoints) (S : Stack) (Q : Queue)
  /-- Every object solved. -/
  | done (F : FixPoints)
  /-- `G` was needed while its own analysis was suspended: an initialisation cycle. -/
  | cycle (G : GlobName)
  deriving Inhabited

/-- `Solve` schedules objects; it computes nothing.  A step either suspends the
    current object in favour of one it needs, reports a cycle, or closes the
    current object — the last only if `Done` holds of it.

    There is deliberately no rule for "the needed object is already solved": in
    that case there is no `Needs`, hence no step, and the dependency is consumed
    inside the `KJ` derivation itself. -/
inductive Solve (L : Program) : Config → Config → Prop
  /-- `G`'s analysis reaches an expression needing the unsolved object `G₀`:
      suspend `G` and start on `G₀`. -/
  | suspend {G G₀ : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
      {c : Ctx} {e : Expr} :
      RE G σ L c e → Needs σ L F c e G₀ →
      G₀ ≠ G → G₀ ∉ Stack.globs S →
      Solve L (.mk G σ F S Q)
              (.mk G₀ (State.zero G₀) F (⟨G, σ⟩ :: S) (Q.remove G₀))
  /-- The needed object is itself suspended (`G₀ = G` is the self-cycle). -/
  | cycle {G G₀ : GlobName} {σ : State G} {F : FixPoints} {S : Stack} {Q : Queue}
      {c : Ctx} {e : Expr} :
      RE G σ L c e → Needs σ L F c e G₀ →
      (G₀ = G ∨ G₀ ∈ Stack.globs S) →
      Solve L (.mk G σ F S Q) (.cycle G₀)
  /-- `G` is finished: publish it and resume the object below it on the stack. -/
  | resume {G G' : GlobName} {σ : State G} {σ' : State G'} {F : FixPoints}
      {S : Stack} {Q : Queue} :
      Stable L F G σ →
      Solve L (.mk G σ F (⟨G', σ'⟩ :: S) Q) (.mk G' σ' (F.insert G σ) S Q)
  /-- `G` is finished and nothing is suspended: take the next object off the queue. -/
  | next {G G₀ : GlobName} {σ : State G} {F : FixPoints} {Q : Queue} :
      Stable L F G σ → ¬ InFixPoint F G₀ →
      Solve L (.mk G σ F List.nil (G₀ :: Q))
              (.mk G₀ (State.zero G₀) (F.insert G σ) List.nil Q)
  /-- The head of the queue was already solved as somebody's dependency. -/
  | skip {G G₀ : GlobName} {σ : State G} {F : FixPoints} {Q : Queue} :
      InFixPoint F G₀ →
      Solve L (.mk G σ F List.nil (G₀ :: Q)) (.mk G σ F List.nil Q)
  /-- Stack and queue both exhausted. -/
  | finish {G : GlobName} {σ : State G} {F : FixPoints} :
      Stable L F G σ →
      Solve L (.mk G σ F List.nil List.nil) (.done (F.insert G σ))
  -- step
  | step {G : GlobName} {σ σ' : State G} {F : FixPoints} {S : Stack} {Q : Queue} :
      Grow L F G σ σ' →
      Solve L (.mk G σ F S Q) (.mk G σ' F S Q)

/-- Reflexive-transitive closure of `Solve`. -/
abbrev Solve.Star (L : Program) : Config → Config → Prop :=
  Relation.ReflTransGen (Solve L)

/-- The initial configuration for a program. -/
def Config.start (L : Program) : Config :=
  let objects := L.GlobNames
  let G := objects.head (by
    show L.GlobNames ≠ []
    have hmem : Proof.Def.obj ⟨"", .thisE, .val .btrue⟩ ∈ L :=
      Program.HasMain (Gₘ := "") (e := .thisE)
    induction L with
    | nil => cases hmem
    | cons d ds ih =>
        rcases List.mem_cons.1 hmem with rfl | h
        · simp [Program.GlobNames]
        · cases d <;> simp [Program.GlobNames, ih h])
  let Q := objects.tail
  .mk G (State.zero G) (fun _ => none) List.nil Q

def Config.start1 (G : GlobName) (Q : Queue) : Config :=
  .mk G (State.zero G) (fun _ => none) List.nil Q

/-! ## Back to the declarative side -/

/-- Assemble the per-object tables into the single global `Sigma` of
    `Analysis.lean`.  Unsolved objects contribute nothing. -/
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

/-! ### Invariants of the fixpoint map -/

/-- Every solved object has its dependency bookkeeping in order. -/
def ADepClosed (L : Program) (F : FixPoints) : Prop :=
  ∀ (G : GlobName) (σ : State G), F G = some σ →
    (∀ G' ∈ σ.ADep, InFixPoint F G') ∧ ADepOk G σ L F

/-- Every solved object's tables mention only itself and its dependencies. -/
def OwnersClosed (L : Program) (F : FixPoints) : Prop :=
  ∀ (G : GlobName) (σ : State G), F G = some σ → OwnersOk G σ ∧ ADepOk G σ L F

theorem OwnersClosed.lookup {L : Program} {F : FixPoints} (hF : OwnersClosed L F)
    {G : GlobName} (h : InFixPoint F G) :
    OwnersOk G (F.lookup G h) ∧ ADepOk G (F.lookup G h) L F := by
  obtain ⟨σ, hσ⟩ := h
  rw [FixPoint.lookup_eq _ hσ]
  exact hF G σ hσ

/-- Every object in `F` was closed by a rule of `Solve`, so `Done` holds of it.
    This is the invariant `solve_done_fixpoint` has to maintain. -/
def AllDone (L : Program) (F : FixPoints) : Prop :=
  ∀ (G : GlobName) (σ : State G), F G = some σ → Done G σ L F

theorem AllDone.adepClosed {L : Program} {F : FixPoints} (h : AllDone L F) :
    ADepClosed L F := fun G σ hσ => ⟨(h G σ hσ).solved, (h G σ hσ).adep⟩

theorem AllDone.ownersClosed {L : Program} {F : FixPoints} (h : AllDone L F) :
    OwnersClosed L F := fun G σ hσ => ⟨(h G σ hσ).owners, (h G σ hσ).adep⟩

/-- **`ADep` over-approximates `Dep`.**  This is what connects the algorithm's
    cycle test to `Proof.abstract_detects_cycle`: a declarative dependency of a
    solved object is always recorded in its `ADep`. -/
theorem dep_subset_ade1p {L : Program} {F : FixPoints} (hF : ADepClosed L F)
    {G G₀ : GlobName} (h : Proof.DepJ F.glue L G G₀) :
    ∀ σ : State G, F G = some σ → G₀ ∈ σ.ADep := by
  induction h with
  | direct hre =>
      intro σ hσ
      exact (hF _ σ hσ).2.direct (re_of_glue hσ hre)
  | @trans G G' G₀ _ _ ih₁ ih₂ =>
      intro σ hσ
      have hG' : G' ∈ σ.ADep := ih₁ σ hσ
      obtain ⟨σ', hσ'⟩ := (hF _ σ hσ).1 G' hG'
      refine (hF _ σ hσ).2.trans hG' ⟨σ', hσ'⟩ ?_
      rw [FixPoint.lookup_eq _ hσ']
      exact ih₂ σ' hσ'

/-- An owner drawn from a *solved* object `G₀` that `G` depends on is itself a
    dependency of `G`. -/
theorem adep_of_dep {L : Program} {F : FixPoints} {G : GlobName} {σ : State G}
    (hA : ADepOk G σ L F) {G₀ : GlobName} (h₀ : InFixPoint F G₀) (hmem : G₀ ∈ σ.ADep)
    {q : OPair} (hq : q.1 = G₀ ∨ q.1 ∈ (F.lookup G₀ h₀).ADep) :
    q.1 ∈ σ.ADep := by
  rcases hq with hq | hq
  · exact hq ▸ hmem
  · exact hA.trans hmem h₀ hq

/-- **`ADep` does not over-approximate either: projection owners are already
    dependencies.**  For an `RE`-reachable expression, every owner pair produced
    by `KJ` belongs to `G` itself or to an object already in `σ.ADep`.  So
    `Solve.suspend`/`Solve.cycle` firing on a `Needs.projOwner` — the case where
    the missing object is not named by a `gproj` and hence is not a `DepJ` edge —
    never reports a dependency `Dep` does not have. -/
theorem kj_owners {L : Program} {F : FixPoints} {G : GlobName} {σ : State G}
    {C : ClassName} {e : Expr} {K : Set OPair} {D : Set GlobName}
    (hF : OwnersClosed L F) (hOw : OwnersOk G σ) (hA : ADepOk G σ L F)
    (hGF : ¬ InFixPoint F G) (h : KJ C σ L F e K D) :
    RE G σ L (some C) e → ∀ p ∈ K, p.1 = G ∨ p.1 ∈ σ.ADep := by
  induction h with
  | thisE =>
      intro _ p hp
      simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hp
      obtain ⟨G', hG', rfl⟩ := hp
      exact hOw.this hG'
  | paramE => intro _ p hp; exact hOw.param hp
  | newC => rintro _ p rfl; exact Or.inl rfl
  | val => intro _ p hp; simp at hp
  | app _ _ =>
      intro _ p hp
      simp only [Set.mem_iUnion] at hp
      obtain ⟨q, _, hp⟩ := hp
      exact hOw.ret hp
  | @gproj G₀ i hK =>
      intro hre q hq
      exact Or.inr (adep_of_dep hA hK (hA.direct hre) ((hF.lookup hK).1.gfld hq))
  | @proj e' i K' D' hK _ ih =>
      intro hre q hq
      simp only [Set.mem_iUnion] at hq
      obtain ⟨p, hpK, hq⟩ := hq
      rcases ih (RE.proj hre) p hpK with hp | hp
      · exact absurd (hp ▸ hK p hpK) hGF
      · exact Or.inr (adep_of_dep hA (hK p hpK) hp ((hF.lookup (hK p hpK)).1.fld hq))

theorem done_of_stable {L F G σ} (hOw : OwnersOk G σ) (hAd : ADepOk G σ L F)
    (hsolved : ∀ G' ∈ σ.ADep, InFixPoint F G') (h : Stable L F G σ) : Done G σ L F :=
    by sorry

-- theorem solve_terminates in either .cycle or .done
theorem solve_terminates {L : Program} {G G' : GlobName} {Q : Queue} {F : FixPoints} :
(Solve.Star L (Config.start L) (.done F)) ∨ (Solve.Star L (Config.start L) (.cycle G')) := by
-- if u start with an empty stack, start computing fix point. by kj or needs, you either have
-- the needed G or u need some G'.
-- in first case, nothing is needed from solve. In second case, you suspend or cycle
-- if cycle, done
-- else we do the same thing with the needed global object
-- assume needed global object doesn't cycle (if it does, we are done), then we come
-- back and look at this object that is on the stack.
-- the stack and queue are finite, so it will reach the .done config
sorry

/-! ### From a declarative dependency cycle to a `Solve` cycle report

`dep_subset_adep` says: if `G` depends on itself, then `Solve`, started on `G`,
can reach `.cycle G`.  The run is the obvious one — follow the dependency edges,
suspending at each one — and the only two things it needs are:

* **a *simple* cycle through `G`.**  Following an arbitrary `Dep`-walk from `G`
  back to `G` is not enough: if the walk revisits some intermediate object `A`,
  the algorithm reports `.cycle A`, not `.cycle G`.  `exists_simple_cycle` below
  shortcuts any closed walk at `G` — cutting out the loop between two
  occurrences of a repeated vertex, which is strictly shortening and keeps `G`
  as the basepoint — until no vertex repeats, so the only object already on the
  stack when the walk closes is `G` itself.

* **the edges must be visible to the algorithm.**  `Proof.Dep` is computed
  against an *arbitrary* `σ : Proof.Sigma`, whereas every state `Solve` visits
  after `Config.start1` is `State.zero` (no rule of `Solve` grows a state).  The
  two agree on `Proof.RE.init₁/init₂/proj/newC₁/newC₂/app₁/app₂`, which never
  look at `σ`, but not on `Proof.RE.body`, which needs `C ∈ σ.RM G`.  So a `σ`
  with a fat `RM` can have `Dep`-edges buried in method bodies that the zero
  state cannot reach, and the theorem is *false* without a hypothesis ruling
  that out (take `G`'s two initialisers value-free and put the `G.i` inside the
  body of a class `C ∈ σ.RM G`: `DepJ σ L G G` holds, yet no rule of `Solve`
  applies to `Config.start1 G _` at all).  Hence the hypothesis `hRE`;
  `re_zero_of_re_none` isolates the fragment on which it is automatic, and
  `re_zero_of_re_of_rm_empty` discharges it outright. -/

/-- A single `Proof.DepJ` edge: `G`'s reachable code contains `G₀.i`. -/
def Edge (σ : Proof.Sigma) (L : Program) (G G₀ : GlobName) : Prop :=
  ∃ (c : Ctx) (i : Idx), Proof.RE σ L G c (Expr.gproj G₀ i)

/-- The same edge as the algorithm sees it: from the empty state, i.e. before
    anything at all has been computed.  This is what `Solve.suspend` /
    `Solve.cycle` fire on, since every state reachable from `Config.start1` is
    a `State.zero`. -/
def AEdge (L : Program) (G G₀ : GlobName) : Prop :=
  ∃ (c : Ctx) (i : Idx), RE G (State.zero G) L c (Expr.gproj G₀ i)

/-- `DepJ` is the transitive closure of `Edge`. -/
theorem transGen_edge_of_depJ {σ : Proof.Sigma} {L : Program} {G G₀ : GlobName}
    (h : Proof.DepJ σ L G G₀) : Relation.TransGen (Edge σ L) G G₀ := by
  induction h with
  | @direct G G₀ c i hre => exact Relation.TransGen.single ⟨c, i, hre⟩
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! #### Extracting a simple cycle from a closed walk -/

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

-- /-- A list that is not `Nodup` splits around one of its repetitions. -/
-- theorem not_nodup_decomp : ∀ {l : List α}, ¬ l.Nodup →
--     ∃ (x : α) (s t u : List α), l = s ++ x :: (t ++ x :: u) := by
--   intro l
--   induction l with
--   | nil => intro h; exact absurd List.nodup_nil h
--   | cons b l ih =>
--       intro h
--       by_cases hl : l.Nodup
--       · have hb : b ∈ l := by
--           by_contra hb
--           exact h (List.nodup_cons.2 ⟨hb, hl⟩)
--         obtain ⟨t, u, rfl⟩ := List.append_of_mem hb
--         exact ⟨b, [], t, u, by simp⟩
--       · obtain ⟨x, s, t, u, rfl⟩ := ih hl
--         exact ⟨x, b :: s, t, u, by simp⟩

-- /-- Shortcutting: a closed walk at `a` of length `≤ n + 1` that repeats a vertex
--     contains a strictly shorter closed walk at `a`.  Iterating gives a walk whose
--     vertices are pairwise distinct. -/
-- theorem exists_nodup_walk (a : α) : ∀ (n : ℕ) (l : List α), l.length ≤ n →
--     List.IsChain r (a :: (l ++ [a])) →
--     ∃ l' : List α, List.IsChain r (a :: (l' ++ [a])) ∧ (a :: l').Nodup := by
--   intro n
--   induction n with
--   | zero =>
--       intro l hlen hchain
--       have hl : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
--       subst hl
--       exact ⟨[], hchain, by simp⟩
--   | succ n ih =>
--       intro l hlen hchain
--       by_cases hnd : (a :: l).Nodup
--       · exact ⟨l, hchain, hnd⟩
--       · by_cases ha : a ∈ l
--         · -- `a` occurs again inside the walk: keep the prefix.
--           obtain ⟨s, t, rfl⟩ := List.append_of_mem ha
--           rw [show (s ++ a :: t) ++ [a] = s ++ a :: (t ++ [a]) by simp] at hchain
--           have hlen' : s.length ≤ n := by
--             simp only [List.length_append, List.length_cons] at hlen; omega
--           exact ih s hlen' (List.isChain_cons_split.1 hchain).1
--         · -- some other vertex occurs twice: cut out the loop between them.
--           have hnd' : ¬ l.Nodup := fun hh => hnd (List.nodup_cons.2 ⟨ha, hh⟩)
--           obtain ⟨x, s, t, u, rfl⟩ := not_nodup_decomp hnd'
--           rw [show (s ++ x :: (t ++ x :: u)) ++ [a] = s ++ x :: (t ++ x :: (u ++ [a])) by simp]
--             at hchain
--           obtain ⟨hpre, hpost⟩ := List.isChain_cons_split.1 hchain
--           have hsuf : List.IsChain r (x :: (u ++ [a])) := (List.isChain_cons_split.1 hpost).2
--           have hlen' : (s ++ x :: u).length ≤ n := by
--             simp only [List.length_append, List.length_cons] at hlen ⊢; omega
--           refine ih (s ++ x :: u) hlen' ?_
--           rw [show (s ++ x :: u) ++ [a] = s ++ x :: (u ++ [a]) by simp]
--           exact List.isChain_cons_split.2 ⟨hpre, hsuf⟩

-- /-- **A closed walk contains a simple cycle through its basepoint.**  Note the
--     conclusion keeps the basepoint: shortcutting never leaves `a`. -/
-- theorem exists_simple_cycle {a : α} (h : Relation.TransGen r a a) :
--     ∃ l : List α, List.IsChain r (a :: (l ++ [a])) ∧ (a :: l).Nodup := by
--   obtain ⟨l, hl⟩ := exists_walk_of_transGen h
--   exact exists_nodup_walk a l.length l le_rfl hl

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

/-! #### Transferring reachability to the states `Solve` actually visits -/

/-- A derivation of `Proof.RE` in the *object* context cannot use `RE.body`
    (that rule produces a `some C` context), and no other rule mentions `σ`.
    So object-level reachability transfers to any algorithmic state. -/
theorem re_zero_of_re_none {σ : Proof.Sigma} {L : Program} {G : GlobName} (σ' : State G)
    {c : Ctx} {e : Expr} (h : Proof.RE σ L G c e) : c = none → RE G σ' L c e := by
  induction h with
  | init₁ ho => exact fun _ => RE.init₁ ho
  | init₂ ho => exact fun _ => RE.init₂ ho
  | body _ _ => exact fun hc => by simp at hc
  | proj _ ih => exact fun hc => RE.proj (ih hc)
  | newC₁ _ ih => exact fun hc => RE.newC₁ (ih hc)
  | newC₂ _ ih => exact fun hc => RE.newC₂ (ih hc)
  | app₁ _ ih => exact fun hc => RE.app₁ (ih hc)
  | app₂ _ ih => exact fun hc => RE.app₂ (ih hc)

/-- If no method is declaratively reachable either, then *all* of `σ`'s
    reachability is visible to the algorithm from the empty state. -/
theorem re_zero_of_re_of_rm_empty {σ : Proof.Sigma} {L : Program}
    (hRM : ∀ G', σ.RM G' = ∅) (G : GlobName) (σ' : State G) {c : Ctx} {e : Expr}
    (h : Proof.RE σ L G c e) : RE G σ' L c e := by
  induction h with
  | init₁ ho => exact RE.init₁ ho
  | init₂ ho => exact RE.init₂ ho
  | @body C _ hC _ => exact absurd (hRM G ▸ hC) (Set.notMem_empty C)
  | proj _ ih => exact RE.proj ih
  | newC₁ _ ih => exact RE.newC₁ ih
  | newC₂ _ ih => exact RE.newC₂ ih
  | app₁ _ ih => exact RE.app₁ ih
  | app₂ _ ih => exact RE.app₂ ih

/-! #### The run -/

/-- **Walking a dependency chain with `Solve`.**  `H` is the object under
    analysis and `l ++ [G]` the objects the chain still has to visit; `G` is
    already suspended (or is `H` itself).  Each edge fires `Solve.suspend` —
    legal because the chain's remaining objects are neither `H` nor on the
    stack — and the last edge, whose target `G` *is* on the stack, fires
    `Solve.cycle G`.

    Nothing is ever solved along the way (`hF`), so every `Needs` obligation is
    discharged by `Needs.gproj` and `F` never changes. -/
theorem solve_cycle_of_walk {L : Program} {F : FixPoints} (hF : ∀ G', ¬ InFixPoint F G')
    {G : GlobName} : ∀ (l : List GlobName) (H : GlobName) (S : Stack) (Q : Queue),
      List.IsChain (AEdge L) (H :: (l ++ [G])) →
      (G = H ∨ G ∈ Stack.globs S) →
      (∀ x ∈ l, x ≠ H ∧ x ∉ Stack.globs S) → l.Nodup →
      Solve.Star L (.mk H (State.zero H) F S Q) (.cycle G) := by
  intro l
  induction l with
  | nil =>
      intro H S Q hchain hG _ _
      obtain ⟨c, i, hre⟩ : AEdge L H G := List.isChain_pair.1 (by simpa using hchain)
      exact Relation.ReflTransGen.single (Solve.cycle hre (Needs.gproj (hF G)) hG)
  | cons b l ih =>
      intro H S Q hchain hG hdisj hnd
      rw [List.cons_append, List.isChain_cons_cons] at hchain
      obtain ⟨⟨c, i, hre⟩, hrest⟩ := hchain
      obtain ⟨hbH, hbS⟩ := hdisj b List.mem_cons_self
      obtain ⟨hbl, hndl⟩ := List.nodup_cons.1 hnd
      have hstep : Solve L (.mk H (State.zero H) F S Q)
          (.mk b (State.zero b) F (⟨H, State.zero H⟩ :: S) (Q.remove b)) :=
        Solve.suspend hre (Needs.gproj (hF b)) hbH hbS
      have hglobs : Stack.globs (⟨H, State.zero H⟩ :: S) = H :: Stack.globs S := rfl
      refine Relation.ReflTransGen.head hstep
        (ih b (⟨H, State.zero H⟩ :: S) (Q.remove b) hrest ?_ ?_ hndl)
      · rcases hG with rfl | hG
        · exact Or.inr (hglobs ▸ List.mem_cons_self)
        · exact Or.inr (hglobs ▸ List.mem_cons_of_mem H hG)
      · intro x hx
        obtain ⟨hxH, hxS⟩ := hdisj x (List.mem_cons_of_mem b hx)
        refine ⟨fun hxb => hbl (hxb ▸ hx), ?_⟩
        rw [hglobs]
        simpa [hxH] using hxS

/-- **Walking a chain with `Solve` without closing it.**  Every edge fires
    `Solve.suspend`, legal because the objects walked through are pairwise
    distinct (`hnd`) and none of them is suspended already (`hS`).  The run ends
    on `b`, with `H` and all of `m` added to the stack — which is what the
    caller needs to know to fire `Solve.cycle` later. -/
theorem solve_walk_suspend {L : Program} {F : FixPoints} (hF : ∀ G', ¬ InFixPoint F G') :
    ∀ (m : List GlobName) (H b : GlobName) (S : Stack) (Q : Queue),
      List.IsChain (AEdge L) (H :: (m ++ [b])) →
      (H :: m).Nodup → (∀ x ∈ H :: m, x ∉ Stack.globs S) →
      b ∉ H :: m → b ∉ Stack.globs S →
      ∃ (S' : Stack) (Q' : Queue),
        Solve.Star L (.mk H (State.zero H) F S Q) (.mk b (State.zero b) F S' Q') ∧
        ∀ x, x ∈ Stack.globs S' ↔ (x ∈ H :: m ∨ x ∈ Stack.globs S) := by
  intro m
  induction m with
  | nil =>
      intro H b S Q hchain _ _ hbH hbS
      obtain ⟨c, i, hre⟩ : AEdge L H b := List.isChain_pair.1 (by simpa using hchain)
      refine ⟨⟨H, State.zero H⟩ :: S, Q.remove b, Relation.ReflTransGen.single
        (Solve.suspend hre (Needs.gproj (hF b)) (by simpa using hbH) hbS), ?_⟩
      intro x
      simp [Stack.globs]
  | cons d m ih =>
      intro H b S Q hchain hnd hS hbH hbS
      rw [List.cons_append, List.isChain_cons_cons] at hchain
      obtain ⟨⟨c, i, hre⟩, hrest⟩ := hchain
      obtain ⟨hHm, hndm⟩ := List.nodup_cons.1 hnd
      have hglobs : Stack.globs (⟨H, State.zero H⟩ :: S) = H :: Stack.globs S := rfl
      have hstep : Solve L (.mk H (State.zero H) F S Q)
          (.mk d (State.zero d) F (⟨H, State.zero H⟩ :: S) (Q.remove d)) :=
        Solve.suspend hre (Needs.gproj (hF d))
          (fun hdH => hHm (hdH ▸ List.mem_cons_self))
          (hS d (List.mem_cons_of_mem H List.mem_cons_self))
      obtain ⟨S', Q', hstar, hmem⟩ :=
        ih d b (⟨H, State.zero H⟩ :: S) (Q.remove d) hrest hndm
          (fun x hx => by
            rw [hglobs]
            simp only [List.mem_cons, not_or]
            exact ⟨fun hxH => hHm (hxH ▸ hx), hS x (List.mem_cons_of_mem H hx)⟩)
          (fun hb => hbH (List.mem_cons_of_mem H hb))
          (by
            rw [hglobs]
            simp only [List.mem_cons, not_or]
            exact ⟨fun hbH' => hbH (hbH' ▸ List.mem_cons_self), hbS⟩)
      refine ⟨S', Q', Relation.ReflTransGen.head hstep hstar, fun x => ?_⟩
      rw [hmem x, hglobs]
      simp only [List.mem_cons]
      tauto

/-- **A cycle reachable from `G` is reported too.**  Walk the repetition-free
    approach `m` from `G` to `b` (`solve_walk_suspend`), which leaves `b` under
    analysis and `G :: m` on the stack, then walk `b`'s own simple cycle
    (`solve_cycle_of_walk`): its closing edge finds `b` suspended and fires
    `Solve.cycle b`.  The walk's tail `n` back to `G` is never travelled — the
    algorithm stops as soon as the inner cycle closes. -/
theorem solve_cycle_of_inner_walk {L : Program} {F : FixPoints}
    (hF : ∀ G', ¬ InFixPoint F G') {G b : GlobName} (m n l : List GlobName) (Q : Queue)
    (hchain : List.IsChain (AEdge L) (G :: (m ++ (((b :: (l ++ [b])) ++ n) ++ [G]))))
    (hnd : (G :: (m ++ b :: l)).Nodup) :
    Solve.Star L (.mk G (State.zero G) F List.nil Q) (.cycle b) := by
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
    solve_walk_suspend hF m G b List.nil Q happ
      (List.nodup_cons.2 ⟨fun hGm => hG (List.mem_append_left _ hGm), hm⟩)
      (by simp [Stack.globs])
      (by
        simp only [List.mem_cons, not_or]
        exact ⟨fun hbG => hG (hbG ▸ List.mem_append_right _ List.mem_cons_self),
          fun hbm => hdisj hbm List.mem_cons_self⟩)
      (by simp [Stack.globs])
  refine hstar.trans (solve_cycle_of_walk hF l b S' Q' hcyc (Or.inl rfl) ?_ hlnd)
  intro x hx
  refine ⟨fun hxb => hbl' (hxb ▸ hx), ?_⟩
  rw [hmemS x]
  simp only [Stack.globs, List.map_nil, List.not_mem_nil, or_false, List.mem_cons, not_or]
  exact ⟨fun hxG => hG (hxG ▸ List.mem_append_right _ (List.mem_cons_of_mem b hx)),
    fun hxm => hdisj hxm (List.mem_cons_of_mem b hx)⟩

theorem hRE : ∀ (G' : GlobName) (c : Ctx) (e : Expr),
      Proof.RE σ L G' c e → RE G' (State.zero G') L c e := sorry

/-- **Every declarative dependency cycle is reported.**  Started on an object
    that depends on itself, `Solve` can reach `.cycle G`: it follows a simple
    `Dep`-cycle through `G`, suspending at each edge, until the edge back to `G`
    finds `G` on its own stack.

    `hRE` is what ties `Proof.Dep`'s `σ` to the states `Solve` visits: no rule of
    `Solve` grows a state, so the run stays at `State.zero`, and a `σ` whose `RM`
    makes method bodies reachable would carry `Dep`-edges the algorithm cannot
    see.  It holds vacuously for object-level reachability
    (`re_zero_of_re_none`) and, in general, whenever `σ.RM` is empty
    (`re_zero_of_re_of_rm_empty`). -/
theorem dep_subset_adep {G : GlobName} {σ : Proof.Sigma} {L : Program}
    {Q : Queue} (_hQ : Q = L.GlobNames)

    (h : G ∈ Proof.Dep σ L G) :
    ∃ G', Solve.Star L (Config.start1 G (Q.remove G)) (.cycle G') := by
  -- the declarative cycle, as a cycle of edges the algorithm can fire on
  have hT : Relation.TransGen (AEdge L) G G :=
    (transGen_edge_of_depJ h).mono fun _ _ => fun ⟨c, i, hre⟩ => ⟨c, i, hRE _ c _ hre⟩
  have hF : ∀ G', ¬ InFixPoint (fun _ => none) G' := by
    rintro G' ⟨σ', hσ'⟩
    simp at hσ'
  rcases nodup_or_simple_cycle hT with ⟨l, hchain, hnd⟩ | ⟨m, n, l, b, hchain, hnd⟩
  · -- the walk revisits nothing before returning to `G`: `G` itself is reported
    obtain ⟨hGl, hndl⟩ := List.nodup_cons.1 hnd
    exact ⟨G, solve_cycle_of_walk hF l G ([] : Stack) (Q.remove G) hchain (Or.inl rfl)
      (fun x hx => ⟨fun hxG => hGl (hxG ▸ hx), by simp [Stack.globs]⟩) hndl⟩
  · -- the walk closes a cycle at an interior `b` first: `b` is reported
    exact ⟨b, solve_cycle_of_inner_walk hF m n l (Q.remove G) hchain hnd⟩

-- theorem algo_detects_dep {G : GlobName} {σ : Proof.Sigma} {L : Program}
--     {Q : Queue} (_hQ : Q = L.GlobNames)
--     (h : G ∈ Proof.Dep σ L G) :
--     ∃ G', Solve.Star L (Config.start1 G (Q.remove G)) (.cycle G') := by
--   -- the declarative cycle, as a cycle of edges the algorithm can fire on
--   -- have hT : Relation.TransGen (AEdge L) G G :=
--   --   (transGen_edge_of_depJ h).mono fun _ _ => fun ⟨c, i, hre⟩ => ⟨c, i, hRE _ c _ hre⟩
--   -- have hF : ∀ G', ¬ InFixPoint (fun _ => none) G' := by
--   --   rintro G' ⟨σ', hσ'⟩
--   --   simp at hσ'
--   -- rcases nodup_or_simple_cycle hT with ⟨l, hchain, hnd⟩ | ⟨m, n, l, b, hchain, hnd⟩
--   -- · -- the walk revisits nothing before returning to `G`: `G` itself is reported
--   --   obtain ⟨hGl, hndl⟩ := List.nodup_cons.1 hnd
--   --   exact ⟨G, solve_cycle_of_walk hF l G ([] : Stack) (Q.remove G) hchain (Or.inl rfl)
--   --     (fun x hx => ⟨fun hxG => hGl (hxG ▸ hx), by simp [Stack.globs]⟩) hndl⟩
--   -- · -- the walk closes a cycle at an interior `b` first: `b` is reported
--   --   exact ⟨b, solve_cycle_of_inner_walk hF m n l (Q.remove G) hchain hnd⟩
--   sorry


-- otherwise, the thm below

/-- **The obligation `Solve` exists to discharge.**  Reaching `done F` means the
    glued state is a fixpoint in the sense of `Analysis.lean`, so every theorem
    proved there — `abstract_detects_cycle` in particular — applies to the
    algorithm's output.

    What is still missing is the invariant carrying it: each `Done` in a closing
    rule is established against the `F` current at that moment, whereas
    `Proof.FixPoint` quantifies over the final `F`.  Bridging the two needs
    monotonicity of `KJ`/`Calls` under `FixPoints.insert` (a derivation stays
    valid, with the same `K`, when a further object is added) plus the invariant
    that a closed object is never re-opened. -/
theorem solve_done_fixpoint {L : Program} {G : GlobName} {Q : Queue} {F : FixPoints}
    (h : Solve.Star L (Config.start L) (.done F)) : Proof.FixPoint F.glue L := by
  sorry

-- final theorem: algo terminates and if runtime crashes, algo detects it.

end Algorithm
