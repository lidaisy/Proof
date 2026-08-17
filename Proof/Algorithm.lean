import Proof.Syntax
import Proof.Semantics
import Proof.Analysis
import Mathlib.Logic.Relation

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
      Done G σ L F →
      Solve L (.mk G σ F (⟨G', σ'⟩ :: S) Q) (.mk G' σ' (F.insert G σ) S Q)
  /-- `G` is finished and nothing is suspended: take the next object off the queue. -/
  | next {G G₀ : GlobName} {σ : State G} {F : FixPoints} {Q : Queue} :
      Done G σ L F → ¬ InFixPoint F G₀ →
      Solve L (.mk G σ F List.nil (G₀ :: Q))
              (.mk G₀ (State.zero G₀) (F.insert G σ) List.nil Q)
  /-- The head of the queue was already solved as somebody's dependency. -/
  | skip {G G₀ : GlobName} {σ : State G} {F : FixPoints} {Q : Queue} :
      InFixPoint F G₀ →
      Solve L (.mk G σ F List.nil (G₀ :: Q)) (.mk G σ F List.nil Q)
  /-- Stack and queue both exhausted. -/
  | finish {G : GlobName} {σ : State G} {F : FixPoints} :
      Done G σ L F →
      Solve L (.mk G σ F List.nil List.nil) (.done (F.insert G σ))

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

-- theorem dep_subset_adep: for every cycle in Dep, start from an object in the cycle
-- and Solve would end in .cycle

theorem dep_subset_adep {G : GlobName} {σ : Proof.Sigma} {L : Program}
{Q : Queue} (hQ : Q = L.GlobNames) (h: G ∈ Proof.Dep σ L G) :
Solve.Star L (Config.start1 G (Q.remove G)) (.cycle G) :=

-- by h, G is in RE G
-- By kj_or_needs, G is needed (since G is not in fixpoints)
-- so Solve reaches suspend

sorry

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
