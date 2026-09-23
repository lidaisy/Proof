import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program Sigma GlobName ClassName OPair Idx Expr classes objects)

structure Sigma.Sub (σ σ' : Sigma) : Prop where
  param : ∀ G C, σ.Param G C ⊆ σ'.Param G C
  fld₁  : ∀ G C, σ.Fld₁ G C ⊆ σ'.Fld₁ G C
  fld₂  : ∀ G C, σ.Fld₂ G C ⊆ σ'.Fld₂ G C
  ret   : ∀ G C, σ.Ret G C ⊆ σ'.Ret G C
  gfld₁ : ∀ G, σ.GFld₁ G ⊆ σ'.GFld₁ G
  gfld₂ : ∀ G, σ.GFld₂ G ⊆ σ'.GFld₂ G
  rm    : ∀ G, σ.RM G ⊆ σ'.RM G
  this  : ∀ G C, σ.This G C ⊆ σ'.This G C

instance : Preorder (Sigma) where
  le := Sigma.Sub
  le_refl _ :=
    { param := fun _ _ => subset_rfl,
      fld₁ := fun _ _ => subset_rfl,
      fld₂ := fun _ _ => subset_rfl,
      ret := fun _ _ => subset_rfl,
      gfld₁ := fun _ => subset_rfl,
      gfld₂ := fun _ => subset_rfl,
      rm := fun _ => subset_rfl,
      this := fun _ _ => subset_rfl }
  le_trans _ _ _ h₁ h₂ :=
    { param := fun G C => (h₁.param G C).trans (h₂.param G C)
      fld₁  := fun G C => (h₁.fld₁ G C).trans (h₂.fld₁ G C)
      fld₂  := fun G C => (h₁.fld₂ G C).trans (h₂.fld₂ G C)
      ret   := fun G C => (h₁.ret G C).trans (h₂.ret G C)
      gfld₁ := fun G => (h₁.gfld₁ G).trans (h₂.gfld₁ G)
      gfld₂ := fun G => (h₁.gfld₂ G).trans (h₂.gfld₂ G)
      rm    := fun G => (h₁.rm G).trans (h₂.rm G)
      this  := fun G C => (h₁.this G C).trans (h₂.this G C) }

instance Sigma.instOrderBot : OrderBot (Sigma) where
  bot :=
    { Param := fun _ _ => ∅,
      Fld₁  := fun _ _ => ∅,
      Fld₂  := fun _ _ => ∅,
      Ret   := fun _ _ => ∅,
      GFld₁ := fun _ => ∅,
      GFld₂ := fun _ => ∅,
      RM    := fun _ => ∅,
      This  := fun _ _ => ∅ }
  bot_le f := by
    exact ⟨fun _ _ => Set.empty_subset _,
            fun _ _ => Set.empty_subset _,
            fun _ _ => Set.empty_subset _,
            fun _ _ => Set.empty_subset _,
            fun _ => Set.empty_subset _,
            fun _ => Set.empty_subset _,
            fun _ => Set.empty_subset _,
            fun _ _ => Set.empty_subset _⟩

@[simp] theorem FixPoints.glue_bot : FixPoints.glue (fun _ => none) = ⊥ := rfl

/-! ### Comparing an algorithm state with (the `G`-slice of) a global fixpoint -/

/-- The slice of a global analysis `Sg` at one global `G`, as an algorithm state. -/
def State.ofSigma (Sg : Sigma) (G : GlobName) : State G where
  Param := Sg.Param G
  Fld₁  := Sg.Fld₁ G
  Fld₂  := Sg.Fld₂ G
  Ret   := Sg.Ret G
  GFld₁ := Sg.GFld₁ G
  GFld₂ := Sg.GFld₂ G
  RM    := Sg.RM G
  This  := Sg.This G

theorem State.zero_sub {G : GlobName} (σ : State G) : State.Sub (State.zero G) σ :=
  ⟨fun _ => Set.empty_subset _, fun _ => Set.empty_subset _, fun _ => Set.empty_subset _,
    fun _ => Set.empty_subset _, Set.empty_subset _, Set.empty_subset _, Set.empty_subset _,
    fun _ => Set.empty_subset _⟩

/-- Indexed version of `State.Sub.fld₁`/`fld₂`, against a `Sg`-slice. -/
theorem State.Sub.fld_ofSigma {G : GlobName} {σ : State G} {Sg : Sigma}
    (h : State.Sub σ (State.ofSigma Sg G)) (i : Idx) (C : ClassName) :
    σ.Fld i C ⊆ Sg.Fld i G C := by
  cases i
  · exact h.fld₁ C
  · exact h.fld₂ C

/-- A state already stored in `F` is below `Sg` as soon as `F.glue` is (fields). -/
theorem glue_fld_sub {F : FixPoints} {Sg : Sigma} (hF : Sigma.Sub F.glue Sg)
    {G₀ : GlobName} {τ : State G₀} (hτ : F G₀ = some τ) (i : Idx) (C : ClassName) :
    τ.Fld i C ⊆ Sg.Fld i G₀ C := by
  cases i
  · rw [show τ.Fld Idx.one = τ.Fld₁ from rfl, ← FixPoints.glue_fld₁ hτ]; exact hF.fld₁ G₀ C
  · rw [show τ.Fld Idx.two = τ.Fld₂ from rfl, ← FixPoints.glue_fld₂ hτ]; exact hF.fld₂ G₀ C

/-- A state already stored in `F` is below `Sg` as soon as `F.glue` is (global fields). -/
theorem glue_gfld_sub {F : FixPoints} {Sg : Sigma} (hF : Sigma.Sub F.glue Sg)
    {G₀ : GlobName} {τ : State G₀} (hτ : F G₀ = some τ) (i : Idx) :
    τ.GFld i ⊆ Sg.GFld i G₀ := by
  cases i
  · rw [show τ.GFld Idx.one = τ.GFld₁ from rfl, ← FixPoints.glue_gfld₁ hτ]; exact hF.gfld₁ G₀
  · rw [show τ.GFld Idx.two = τ.GFld₂ from rfl, ← FixPoints.glue_gfld₂ hτ]; exact hF.gfld₂ G₀

/-- Storing a state that is itself below `Sg` keeps the glued analysis below `Sg`. -/
theorem glue_insert_sub {F : FixPoints} {G : GlobName} {σ : State G} {Sg : Sigma}
    (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G)) :
    Sigma.Sub (F.insert G σ).glue Sg := by
  constructor
  case param =>
    intro G' C
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.param C
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.param G' C
  case fld₁ =>
    intro G' C
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.fld₁ C
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.fld₁ G' C
  case fld₂ =>
    intro G' C
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.fld₂ C
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.fld₂ G' C
  case ret =>
    intro G' C
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.ret C
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.ret G' C
  case gfld₁ =>
    intro G'
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.gfld₁
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.gfld₁ G'
  case gfld₂ =>
    intro G'
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.gfld₂
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.gfld₂ G'
  case rm =>
    intro G'
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.rm
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.rm G'
  case this =>
    intro G' C
    by_cases hG : G' = G
    · subst hG; simpa [FixPoints.glue] using hσ.this C
    · simpa [FixPoints.glue, FixPoints.insert_other hG] using hF.this G' C

@[simp] theorem State.addFldAt_one {G : GlobName} (σ : State G) (C : ClassName)
    (K : Set OPair) : σ.addFldAt Idx.one C K =
      { σ with Fld₁ := fun C' => if C' = C then σ.Fld₁ C' ∪ K else σ.Fld₁ C' } := rfl

@[simp] theorem State.addFldAt_two {G : GlobName} (σ : State G) (C : ClassName)
    (K : Set OPair) : σ.addFldAt Idx.two C K =
      { σ with Fld₂ := fun C' => if C' = C then σ.Fld₂ C' ∪ K else σ.Fld₂ C' } := rfl

/-! ### Bridging the per-global judgements to the global ones -/

section Bridge
variable {G : GlobName} {L : Program} {F : FixPoints} {Sg : Sigma} {σ : State G}

/-- The field-projection set computed by the algorithm sits inside the global one. -/
theorem proj_set_sub (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G))
    {K K' : Set OPair} (hK : ∀ p ∈ K, p.1 = G ∨ InFixPoint F p.1) (hsub : K ⊆ K') (i : Idx) :
    (⋃ p, ⋃ h : p ∈ K, if hG : p.1 = G then σ.Fld i p.2
        else (F.lookup p.1 ((hK p h).resolve_left hG)).Fld i p.2)
      ⊆ ⋃ p ∈ K', Sg.Fld i p.1 p.2 := by
  intro x hx
  simp only [Set.mem_iUnion] at hx ⊢
  obtain ⟨p, hp, hx⟩ := hx
  refine ⟨p, hsub hp, ?_⟩
  by_cases hG : p.1 = G
  · rw [dif_pos hG] at hx
    rw [hG]
    exact hσ.fld_ofSigma i p.2 hx
  · rw [dif_neg hG] at hx
    obtain ⟨τ, hτ⟩ := (hK p hp).resolve_left hG
    rw [FixPoint.lookup_eq _ hτ] at hx
    exact glue_fld_sub hF hτ i p.2 hx

theorem kj_bridge (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G))
    {C : ClassName} {e : Expr} {K : Set OPair} {D : Set GlobName} (h : KJ C σ L F e K D) :
    ∃ K', Proof.KJ G C Sg L e K' ∧ K ⊆ K' := by
  induction h with
  | thisE =>
      exact ⟨_, Proof.KJ.thisE, Set.biUnion_mono (hσ.this C) (fun _ _ => subset_rfl)⟩
  | paramE => exact ⟨_, Proof.KJ.paramE, hσ.param C⟩
  | @proj e i K D hK _ ih =>
      obtain ⟨K', hK', hsub⟩ := ih
      exact ⟨_, Proof.KJ.proj hK', proj_set_sub hF hσ hK hsub i⟩
  | @gproj G₀ i hIn =>
      obtain ⟨τ, hτ⟩ := hIn
      refine ⟨_, Proof.KJ.gproj, ?_⟩
      rw [FixPoint.lookup_eq _ hτ]
      exact glue_gfld_sub hF hτ i
  | newC => exact ⟨_, Proof.KJ.newC, subset_rfl⟩
  | @app e₁ e₂ K₁ D₁ _ ih =>
      obtain ⟨K₁', h₁', hsub⟩ := ih
      exact ⟨_, Proof.KJ.app h₁', Set.biUnion_mono hsub (fun p _ => hσ.ret p.2)⟩
  | val => exact ⟨_, Proof.KJ.val, subset_rfl⟩

theorem kj0_bridge (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G))
    {e : Expr} {K : Set OPair} {D : Set GlobName} (h : KJ0 σ L F e K D) :
    ∃ K', Proof.KJ0 G Sg L e K' ∧ K ⊆ K' := by
  induction h with
  | @proj e i K D hK _ ih =>
      obtain ⟨K', hK', hsub⟩ := ih
      exact ⟨_, Proof.KJ0.proj hK', proj_set_sub hF hσ hK hsub i⟩
  | @gproj G₀ i hIn =>
      obtain ⟨τ, hτ⟩ := hIn
      refine ⟨_, Proof.KJ0.gproj, ?_⟩
      rw [FixPoint.lookup_eq _ hτ]
      exact glue_gfld_sub hF hτ i
  | newC => exact ⟨_, Proof.KJ0.newC, subset_rfl⟩
  | @app e₁ e₂ K₁ D₁ _ ih =>
      obtain ⟨K₁', h₁', hsub⟩ := ih
      exact ⟨_, Proof.KJ0.app h₁', Set.biUnion_mono hsub (fun p _ => hσ.ret p.2)⟩
  | val => exact ⟨_, Proof.KJ0.val, subset_rfl⟩

theorem kjc_bridge (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G))
    {c : Ctx} {e : Expr} {K : Set OPair} {D : Set GlobName} (h : KJC σ L F c e K D) :
    ∃ K', Proof.KJC G Sg L c e K' ∧ K ⊆ K' := by
  cases c with
  | none => exact kj0_bridge hF hσ h
  | some C => exact kj_bridge hF hσ h

theorem calls_bridge (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G))
    {C : ClassName} {e : Expr} {K : Set ClassName} (h : Calls C σ L F e K) :
    ∃ K', Proof.Calls G C Sg L e K' ∧ K ⊆ K' := by
  induction h with
  | thisE => exact ⟨_, Proof.Calls.thisE, subset_rfl⟩
  | paramE => exact ⟨_, Proof.Calls.paramE, subset_rfl⟩
  | gproj => exact ⟨_, Proof.Calls.gproj, subset_rfl⟩
  | proj _ ih => obtain ⟨K', h', hsub⟩ := ih; exact ⟨_, Proof.Calls.proj h', hsub⟩
  | newC _ _ ih₁ ih₂ =>
      obtain ⟨K₁', h₁', hs₁⟩ := ih₁
      obtain ⟨K₂', h₂', hs₂⟩ := ih₂
      exact ⟨_, Proof.Calls.newC h₁' h₂', Set.union_subset_union hs₁ hs₂⟩
  | @app e₁ e₂ K₁ D₁ K₂ K₃ hkj _ _ ih₂ ih₃ =>
      obtain ⟨K₁', hkj', hs₁⟩ := kj_bridge hF hσ hkj
      obtain ⟨K₂', h₂', hs₂⟩ := ih₂
      obtain ⟨K₃', h₃', hs₃⟩ := ih₃
      exact ⟨_, Proof.Calls.app hkj' h₂' h₃',
        Set.union_subset_union (Set.union_subset_union (Set.image_mono hs₁) hs₂) hs₃⟩
  | val => exact ⟨_, Proof.Calls.val, subset_rfl⟩

theorem calls0_bridge (hF : Sigma.Sub F.glue Sg) (hσ : State.Sub σ (State.ofSigma Sg G))
    {e : Expr} {K : Set ClassName} (h : Calls0 σ L F e K) :
    ∃ K', Proof.Calls0 G Sg L e K' ∧ K ⊆ K' := by
  induction h with
  | gproj => exact ⟨_, Proof.Calls0.gproj, subset_rfl⟩
  | proj _ ih => obtain ⟨K', h', hsub⟩ := ih; exact ⟨_, Proof.Calls0.proj h', hsub⟩
  | newC _ _ ih₁ ih₂ =>
      obtain ⟨K₁', h₁', hs₁⟩ := ih₁
      obtain ⟨K₂', h₂', hs₂⟩ := ih₂
      exact ⟨_, Proof.Calls0.newC h₁' h₂', Set.union_subset_union hs₁ hs₂⟩
  | @app e₁ e₂ K₁ D₁ K₂ K₃ hkj _ _ ih₂ ih₃ =>
      obtain ⟨K₁', hkj', hs₁⟩ := kj0_bridge hF hσ hkj
      obtain ⟨K₂', h₂', hs₂⟩ := ih₂
      obtain ⟨K₃', h₃', hs₃⟩ := ih₃
      exact ⟨_, Proof.Calls0.app hkj' h₂' h₃',
        Set.union_subset_union (Set.union_subset_union (Set.image_mono hs₁) hs₂) hs₃⟩
  | val => exact ⟨_, Proof.Calls0.val, subset_rfl⟩

theorem re_bridge (hσ : State.Sub σ (State.ofSigma Sg G)) {c : Ctx} {e : Expr}
    (h : RE G σ L c e) : Proof.RE Sg L G c e := by
  induction h with
  | init₁ hobj => exact Proof.RE.init₁ hobj
  | init₂ hobj => exact Proof.RE.init₂ hobj
  | body hRM hcls => exact Proof.RE.body (hσ.rm hRM) hcls
  | proj _ ih => exact Proof.RE.proj ih
  | newC₁ _ ih => exact Proof.RE.newC₁ ih
  | newC₂ _ ih => exact Proof.RE.newC₂ ih
  | app₁ _ ih => exact Proof.RE.app₁ ih
  | app₂ _ ih => exact Proof.RE.app₂ ih

end Bridge

/-! ### A `Grow` step stays below any global fixpoint -/

theorem grow_sub {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G} {Sg : Sigma}
    (hSg : Proof.FixPoint Sg L) (hF : Sigma.Sub F.glue Sg)
    (hσ : State.Sub σ (State.ofSigma Sg G)) (hg : Grow L F G σ σ') :
    State.Sub σ' (State.ofSigma Sg G) := by
  cases hg with
  | @rmInit e₁ e₂ K₁ K₂ hobj hc₁ hc₂ =>
      obtain ⟨K₁', h₁', hs₁⟩ := calls0_bridge hF hσ hc₁
      obtain ⟨K₂', h₂', hs₂⟩ := calls0_bridge hF hσ hc₂
      exact { hσ with
        rm := Set.union_subset hσ.rm
          ((Set.union_subset_union hs₁ hs₂).trans (hSg.rm_init hobj h₁' h₂')) }
  | @rmClosed C body K hRM hcls hc =>
      obtain ⟨K', h', hs⟩ := calls_bridge hF hσ hc
      exact { hσ with
        rm := Set.union_subset hσ.rm (hs.trans (hSg.rm_closed (hσ.rm hRM) hcls h')) }
  | @retInit C e K D he hK =>
      obtain ⟨K', hK', hs⟩ := kj_bridge hF hσ hK
      refine { hσ with ret := ?_ }
      intro C' x hx
      simp only [State.addRet] at hx
      split_ifs at hx with hCC
      · subst hCC
        rcases hx with hx | hx
        · exact hσ.ret C' hx
        · exact hSg.ret_init he hK' (hs hx)
      · exact hσ.ret C' hx
  | @gfldOne e₁ e₂ K₁ D₁ hobj hK =>
      obtain ⟨K₁', hK₁', hs₁⟩ := kj0_bridge hF hσ hK
      exact { hσ with
        gfld₁ := Set.union_subset hσ.gfld₁ (hs₁.trans (hSg.gfld_init_one hobj hK₁')) }
  | @gfldTwo e₁ e₂ K₂ D₂ hobj hK =>
      obtain ⟨K₂', hK₂', hs₂⟩ := kj0_bridge hF hσ hK
      exact { hσ with
        gfld₂ := Set.union_subset hσ.gfld₂ (hs₂.trans (hSg.gfld_init_two hobj hK₂')) }
  | @fld c Dc e₁ e₂ K₁ K₂ D₁ D₂ hre hK₁ hK₂ =>
      obtain ⟨K₁', h₁', hs₁⟩ := kjc_bridge hF hσ hK₁
      obtain ⟨K₂', h₂', hs₂⟩ := kjc_bridge hF hσ hK₂
      obtain ⟨hf₁, hf₂⟩ := hSg.fld_re (re_bridge hσ hre) h₁' h₂'
      refine { hσ with fld₁ := ?_, fld₂ := ?_ }
      · intro C' x hx
        simp only [State.addFldAt_one, State.addFldAt_two] at hx
        split_ifs at hx with hC
        · subst hC
          rcases hx with hx | hx
          · exact hσ.fld₁ C' hx
          · exact hf₁ (hs₁ hx)
        · exact hσ.fld₁ C' hx
      · intro C' x hx
        simp only [State.addFldAt_one, State.addFldAt_two] at hx
        split_ifs at hx with hC
        · subst hC
          rcases hx with hx | hx
          · exact hσ.fld₂ C' hx
          · exact hf₂ (hs₂ hx)
        · exact hσ.fld₂ C' hx
  | @param c e₁ e₂ K₁ K₂ D₁ D₂ hre hK₁ hK₂ =>
      obtain ⟨K₁', h₁', hs₁⟩ := kjc_bridge hF hσ hK₁
      obtain ⟨K₂', h₂', hs₂⟩ := kjc_bridge hF hσ hK₂
      have hp := hSg.param_re (re_bridge hσ hre) h₁' h₂'
      refine { hσ with param := ?_ }
      intro C' x hx
      simp only [State.addParamAt, Set.mem_union, Set.mem_iUnion] at hx
      rcases hx with hx | ⟨hC, hx⟩
      · exact hσ.param C' hx
      · exact hp C' (Set.image_mono hs₁ hC) (hs₂ hx)
  | @thisG c e₁ e₂ K₁ D₁ hre hK =>
      obtain ⟨K₁', h₁', hs₁⟩ := kjc_bridge hF hσ hK
      have ht := hSg.this_re (G₀ := objects K₁') (re_bridge hσ hre) h₁' rfl
      refine { hσ with this := ?_ }
      intro C' x hx
      simp only [State.addThisAt, Set.mem_union, Set.mem_iUnion] at hx
      rcases hx with hx | ⟨hC, hx⟩
      · exact hσ.this C' hx
      · exact ht C' (Set.image_mono hs₁ hC) (Set.image_mono hs₁ hx)

/-! ### The invariant -/

/-- The current config, c,  of the algorithm -- the fixpoints, the current state, and the suspended
    states -- are all below Sg -/
def Config.Below (c : Config) (Sg : Sigma) : Prop :=
  match c with
  | .mk G σ f S _ => f.glue ≤ Sg ∧ State.Sub σ (State.ofSigma Sg G) ∧
      ∀ p ∈ S, State.Sub p.2 (State.ofSigma Sg p.1)
  | .done _ => True
  | .cycle _ => True

def LessThanInv (c : Config) (L : Program) : Prop :=
  ∀ σ : Proof.Sigma, Proof.FixPoint σ L → c.Below σ

theorem less_than_step {L : Program} {c c' : Config}
    (h : LessThanInv c L) (hstep : Solve L c c')
    : LessThanInv c' L := by
  intro Sg hSg
  cases hstep with
  | @step G σ σ' F S Q hg =>
      obtain ⟨hF, hσ, hS⟩ := h Sg hSg
      exact ⟨hF, grow_sub hSg hF hσ hg, hS⟩
  | @suspend G G₀ σ F S Q c e hre hne _ _ =>
      obtain ⟨hF, hσ, hS⟩ := h Sg hSg
      refine ⟨hF, State.zero_sub _, ?_⟩
      intro p hp
      cases hp with
      | head => exact hσ
      | tail _ hp => exact hS p hp
  | cycle _ =>
      trivial
  | @resume G G' σ σ' F S Q _ =>
      obtain ⟨hF, hσ, hS⟩ := h Sg hSg
      refine ⟨glue_insert_sub hF hσ, hS ⟨G', σ'⟩ List.mem_cons_self, ?_⟩
      exact fun p hp => hS p (List.mem_cons_of_mem _ hp)
  | @next G G₀ σ F Q _ _ =>
      obtain ⟨hF, hσ, _⟩ := h Sg hSg
      exact ⟨glue_insert_sub hF hσ, State.zero_sub _, by simp⟩
  | @skip G G₀ σ F Q _ =>
      obtain ⟨hF, hσ, hS⟩ := h Sg hSg
      exact ⟨hF, hσ, hS⟩
  | @finish G σ F _ =>
      trivial

theorem less_than {L : Program} (hL : L.HasMain) {c : Config}
    (hstar : Solve.Star L (Config.start L hL) c)
    : LessThanInv c L := by
  induction hstar with
  | refl =>
    intro σ _
    refine ⟨?_, State.zero_sub _, by simp⟩
    simp only [FixPoints.glue_bot]
    exact bot_le
  | tail hr hgrow ih => exact less_than_step ih hgrow

/-- AlgoDep ≤ Dep. Used in Cycle.lean. -/

def DepLessThan (c : Config) (L : Program) : Prop :=
  ∀ σ : Proof.Sigma, Proof.FixPoint σ L →
  ∀ G : GlobName, Dep c.fixpoints L G ≤ Proof.Dep σ L G

theorem dep_none {L : Program} {G : GlobName} :
    {G₀ | DepJ (fun _ => none) L G G₀} = (∅ : Set GlobName) := by
  ext G₀
  constructor
  · intro h
    induction h with
    | @direct G G₀ c i hIn hRE =>
        rcases hIn with ⟨σ, hσ⟩
        simp at hσ
    | trans h₁ h₂ ih₁ ih₂ =>
        exact ih₁
  · simp

theorem re_insert_other {L : Program} {G G_1 : GlobName} {F : FixPoints}
    {σ : State G} {c : Ctx} {e : Expr} (hne : G_1 ≠ G) (hG_1 : InFixPoint F G_1) :
    RE G_1 ((F.insert G σ).lookup G_1 (by simp [InFixPoint.mono_insert hG_1])) L c e =
      RE G_1 (F.lookup G_1 hG_1) L c e := by
  have hstate :
      ((F.insert G σ).lookup G_1 (by simp [InFixPoint.mono_insert hG_1])) =
        F.lookup G_1 hG_1 := by
    simp [FixPoints.lookup, FixPoints.insert_other hne]
  rw [hstate]

-- theorem dep_insert_self {L : Program} {G : GlobName} {F : FixPoints}
--     {σ : State G} (hG : F G = some σ) :
--     {G₀ | DepJ (F.insert G σ) L G G₀} = {G₀ | DepJ F L G G₀} := by
--   ext G₀
--   constructor
--   · intro h
--     simp at h
--     induction h with
--     | @direct c i hFix hRE =>
--       -- Base case: You have hRE : RE G (F.lookup G hFix) L c (Expr.gproj G₀ i)
--       sorry

--     | trans h1 h2 ih1 ih2 =>
--       -- Inductive case: You have the inductive hypotheses ih1 and ih2
--       sorry
--     -- simp [DepJ, FixPoints.insert_self] at h
--     sorry
--   · sorry

theorem dep_insert_other {L : Program} {G G_1 : GlobName} {F : FixPoints}
    {σ : State G} (hne : G_1 ≠ G) :
    {G₀ | DepJ (F.insert G σ) L G_1 G₀} = {G₀ | DepJ F L G_1 G₀} := by
  ext G₀
  constructor
  · intro h
    induction h with
    | @direct G' G'₀ c i hIn hRE =>
        -- after inserting G, we do not change DepJ because RE isn't changed
        rcases hIn with ⟨σ', hσ'⟩
        simp [FixPoints.insert_other hne] at hσ'
        have hIn' : InFixPoint F G' := ⟨σ', hσ'⟩
        simp [re_insert_other hne hIn'] at hRE
        exact DepJ.direct hRE
    | @trans G1 G2 G3 h₁ h₂ ih₁ ih₂ =>
        sorry
  · intro h
    sorry

-- i dont know if im doing thid all wrong.
-- the heart of the proof should be that if one fipoint
-- is less than the other, then the dep should be less.
-- then dep_less_than_step should depend on that.



theorem dep_less_than_step {L : Program} {c c' : Config}
    (h : DepLessThan c L) (hstep : Solve L c c')
    (hlessc : LessThanInv c L) (hlessc' : LessThanInv c' L)
    : DepLessThan c' L := by
  intro Sg hSg
  cases hstep with
  | @step G σ σ' F S Q hg =>
      obtain hG := h Sg hSg
      -- exact ⟨hF, grow_sub hSg hF hσ hg, hS⟩
      sorry
  | @suspend G G₀ σ F S Q c e hre hne _ _ =>
      obtain hG := h Sg hSg
      -- refine ⟨hF, State.zero_sub _, ?_⟩
      -- intro p hp
      -- cases hp with
      -- | head => exact hσ
      -- | tail _ hp => exact hS p hp
      sorry
  | cycle _ =>
      simp only [Config.fixpoints, Dep, dep_none]
      intro G
      exact bot_le
  | @resume G G' σ σ' F S Q _ =>
      obtain hG := h Sg hSg
      -- refine ⟨glue_insert_sub hF hσ, hS ⟨G', σ'⟩ List.mem_cons_self, ?_⟩
      -- exact fun p hp => hS p (List.mem_cons_of_mem _ hp)
      sorry
  | @next G G₀ σ F Q _ _ =>
      obtain hG := h Sg hSg
      -- exact ⟨glue_insert_sub hF hσ, State.zero_sub _, by simp⟩
      sorry
  | @skip G G₀ σ F Q _ =>
      obtain hG := h Sg hSg
      exact hG
  | @finish G σ F _ =>
      intro G₁
      simp [Config.fixpoints, Dep]
      by_cases hG₁ : G₁ = G
      · subst hG₁
        have hBelow := hlessc Sg hSg
        obtain ⟨_, hσ, _⟩ := hBelow

        sorry
      · have hDepG' : ∀ G' ≠ G, {G₀ | DepJ (F.insert G σ) L G' G₀} = {G₀ | DepJ F L G' G₀} := by
          intro G' hG'
          simp [dep_insert_other hG']
        simp [hDepG' G₁ hG₁]
        exact h Sg hSg G₁


theorem dep_less_than {L : Program} (hL : L.HasMain) {c : Config}
    (hstar : Solve.Star L (Config.start L hL) c)
    : DepLessThan c L := by
  induction hstar with
  | refl =>
    intro σ hF G
    simp only [Config.start, Config.fixpoints, Dep, dep_none]
    exact bot_le
  | tail hr hgrow ih =>
    rename_i c' c''
    have hc' : LessThanInv c' L := (less_than hL hr)
    exact dep_less_than_step ih hgrow hc' (less_than_step hc' hgrow)

end Algorithm
