import Proof.Algorithm.Definition

namespace Proof

@[ext] theorem Sigma.ext {σ₁ σ₂ : Sigma}
    (hParam : σ₁.Param = σ₂.Param)
    (hFld₁ : σ₁.Fld₁ = σ₂.Fld₁)
    (hFld₂ : σ₁.Fld₂ = σ₂.Fld₂)
    (hRet : σ₁.Ret = σ₂.Ret)
    (hGFld₁ : σ₁.GFld₁ = σ₂.GFld₁)
    (hGFld₂ : σ₁.GFld₂ = σ₂.GFld₂)
    (hRM : σ₁.RM = σ₂.RM)
    (hThis : σ₁.This = σ₂.This) :
    σ₁ = σ₂ := by
  cases σ₁ with
  | mk Param Fld₁ Fld₂ Ret GFld₁ GFld₂ RM This =>
      cases σ₂ with
      | mk Param' Fld₁' Fld₂' Ret' GFld₁' GFld₂' RM' This' =>
          cases hParam
          cases hFld₁
          cases hFld₂
          cases hRet
          cases hGFld₁
          cases hGFld₂
          cases hRM
          cases hThis
          rfl

end Proof

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

theorem grow_sub1 {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G} {Sg : Sigma}
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

theorem grow_sub {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G} {Sg : Sigma}
    {S : Stack} {Q : Queue} (hSg : Proof.FixPoint Sg L)
    (hF : Sigma.Sub (Config.mk G σ F S Q).all_data Sg) (hg : Grow L F G σ σ') :
    State.Sub σ' (State.ofSigma Sg G) := by
  sorry

def Config.less (c : Config) (Sg : Sigma) : Prop :=
  match c with
  | .mk _ _ _ _ _ => c.all_data ≤ Sg
  | .done _ => True
  | .cycle _ => True

def LessThanInv (c : Config) (L : Program) : Prop :=
  ∀ σ : Proof.Sigma, Proof.FixPoint σ L → c.less σ

theorem Config.all_data_zero {L : Program} {hL : L.WellFormed}
    : (Config.start L hL).all_data = ⊥ := by
  -- have h : (Config.start L hL).all_data ≤ ⊥ := by
  --     simp [Config.all_data, Config.start]
  --     refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  --     · sorry
  --     · sorry
  --     · sorry
  --     · sorry
  --     · sorry
  --     · sorry
  --     · sorry
  --     · sorry
  -- exact (le_bot_iff : (Config.start L hL).all_data ≤ (⊥ : Sigma) ↔ (Config.start L hL).all_data = ⊥).mp h
  change (Config.start L hL).all_data =
      { Param := fun _ _ => ∅,
        Fld₁  := fun _ _ => ∅,
        Fld₂  := fun _ _ => ∅,
        Ret   := fun _ _ => ∅,
        GFld₁ := fun _ => ∅,
        GFld₂ := fun _ => ∅,
        RM    := fun _ => ∅,
        This  := fun _ _ => ∅ }
  apply Proof.Sigma.ext
  · funext G C
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G C
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G C
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G C
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]
  · funext G C
    by_cases hG : L.GlobNames.head hL.left = G
    · subst hG
      simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero]
    · simp [Config.all_data, Config.start, Config.find, Config.fixpoints,
        Config.stack, Config.curState, Stack.find, State.zero, hG]

theorem less_than_step {L : Program} {c c' : Config}
    (h : LessThanInv c L) (hstep : Solve L c c')
    : LessThanInv c' L := by
  intro Sg hSg
  cases hstep with
  | @step G σ σ' F S Q _ hg =>
    have ih := h Sg hSg
    have hgs := grow_sub hSg ih hg
    -- same old pattern: but maybe a new theorem saying everything aside from
    -- G returns the same answer.
    sorry
  | @suspend G G₀ σ F S Q c i _ _ hre hneeds hne hnS =>
    have ih := h Sg hSg
    -- theorem saying everything aside G G₀ returns the same answer
    sorry
  | cycle _ => trivial
  | @resume G G' σ σ' F S Q _ =>
    have ih := h Sg hSg
    -- theorem saying everything aside G G' returns the same answer
    -- List.mem_cons_self, List.mem_cons_of_mem
    sorry
  | @next G G₀ σ F Q _ _ =>
    have ih := h Sg hSg
    simp [Config.less]
    -- theorem saying everything aside from
    -- G returns the same answer.
    sorry
  | @finish G σ F _ => trivial

theorem less_than {L : Program} (hL : L.WellFormed) {c : Config}
    (hstar : Solve.Star L (Config.start L hL) c)
    : LessThanInv c L := by
  induction hstar with
  | refl =>
      intro σ _
      change (Config.start L hL).all_data ≤ σ
      rw [Config.all_data_zero (hL := hL)]
      exact bot_le
  | tail hr hgrow ih => exact less_than_step ih hgrow

theorem stack_find_sub {S : Stack} {Sg : Proof.Sigma}
    (hS : ∀ p ∈ S, State.Sub p.2 (State.ofSigma Sg p.1)) :
    ∀ {G : GlobName} {τ : State G}, S.find G = some τ →
      State.Sub τ (State.ofSigma Sg G) := by
  induction S with
  | nil =>
      intro G τ hfind
      simp [Stack.find] at hfind
  | cons p ps ih =>
      intro G τ hfind
      cases p with
      | mk Gp σp =>
          by_cases hEq : Gp = G
          · subst G
            simp [Stack.find] at hfind
            cases hfind
            exact hS ⟨Gp, σp⟩ (by simp)
          · have hfind' : Stack.find ps G = some τ := by
              simpa [Stack.find, hEq] using hfind
            apply ih
            · intro p hp
              exact hS p (by simp [hp])
            · exact hfind'

theorem less_than_imp_re_less_than {σ σ': Proof.Sigma} {L : Program}
    {G : GlobName} {ctx : Proof.Ctx} {E : Expr} (hl : σ ≤ σ') (h : Proof.RE σ L G ctx E) :
    Proof.RE σ' L G ctx E := by
  have ⟨_ , _, _, _, _, _, hRM', _⟩ := hl
  induction h with
  | @init₁ _ _ hG => exact Proof.RE.init₁ hG
  | @init₂ _ _ hG => exact Proof.RE.init₂ hG
  | @body C e hRM hC => exact Proof.RE.body ((hRM' G) hRM) hC
  | @proj _ _ _ _ ih => exact Proof.RE.proj ih
  | @newC₁ _ _ _ _ _ ih => exact Proof.RE.newC₁ ih
  | @newC₂ _ _ _ _ _ ih => exact Proof.RE.newC₂ ih
  | @app₁ _ _ _ _ ih => exact Proof.RE.app₁ ih
  | @app₂ _ _ _ _ ih => exact Proof.RE.app₂ ih

theorem less_than_imp_dep_less_than {σ σ': Proof.Sigma} {L : Program}
    {G : GlobName} (h : σ ≤ σ') :
    Proof.Dep σ L G ≤ Proof.Dep σ' L G := by
  simp [Proof.Dep]
  intro Gs hσ'
  induction hσ' with
  | @direct G₁ G₂ ctx i hRE => exact Proof.DepJ.direct (less_than_imp_re_less_than h hRE)
  | @trans G₁ G₂ G₃ h₁ h₂ ih₁ ih₂ => exact Proof.DepJ.trans ih₁ ih₂

end Algorithm
