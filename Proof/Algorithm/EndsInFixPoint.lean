import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program GlobName Expr)

theorem fixpoint_is_stable {c : Config} {G : GlobName}
    {L : Program} (h : InFixPoint c.fixpoints G)
    : Stable L c.fixpoints G (c.fixpoints.lookup G h) := by
  sorry

private theorem stable_to_local_fixpoint {L : Program} {F : FixPoints}
    {G : GlobName} {σ : State G} (h : Stable L F G σ) :
    FixPoint G σ L F := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro e₁ e₂ K₁ K₂ hobj hc₁ hc₂
    have hs := (h.1 _ (Grow.rmInit hobj hc₁ hc₂)).rm
    simpa [State.addRM] using hs
  · intro C body K hC hbody hc
    have hs := (h.1 _ (Grow.rmClosed hC hbody hc)).rm
    simpa [State.addRM] using hs
  · intro C e K Dp hC he hK
    have hs := (h.1 _ (Grow.retInit hC he hK)).ret C
    simpa [State.addRet] using hs
  · intro e₁ e₂ K₁ Dp hobj hK
    have hs := (h.1 _ (Grow.gfldOne hobj hK)).gfld₁
    simpa [State.GFld] using hs
  · intro e₁ e₂ K₂ Dp hobj hK
    have hs := (h.1 _ (Grow.gfldTwo hobj hK)).gfld₂
    simpa [State.GFld] using hs
  · intro c D e₁ e₂ K₁ K₂ Dp₁ Dp₂ hre hk₁ hk₂
    have hs := h.1 _ (Grow.fld hre hk₁ hk₂)
    constructor
    · simpa [State.addFldAt, State.Fld] using hs.fld₁ D
    · simpa [State.addFldAt, State.Fld] using hs.fld₂ D
  · intro c e₁ e₂ K₁ K₂ Dp₁ Dp₂ hre hk₁ hk₂ D hD
    have hs := (h.1 _ (Grow.param hre hk₁ hk₂)).param D
    change (σ.Param D ∪ ⋃ (_ : D ∈ Proof.classes K₁), K₂) ⊆ σ.Param D at hs
    intro p hp
    exact hs (Or.inr (Set.mem_iUnion.mpr ⟨hD, hp⟩))
  · intro G₀ c K₁ Dp₁ e₁ e₂ hre hk hG₀ D hD
    subst G₀
    have hs := (h.1 _ (Grow.thisG hre hk)).this D
    change (σ.This D ∪ ⋃ (_ : D ∈ Proof.classes K₁), Proof.objects K₁) ⊆ σ.This D at hs
    intro G' hG'
    exact hs (Or.inr (Set.mem_iUnion.mpr ⟨hD, hG'⟩))

private theorem hasObject_mem_globNames {L : Program} {G e₁ e₂}
    (hObj : L.HasObject G e₁ e₂) : G ∈ L.GlobNames := by
  induction L with
  | nil => simp [Program.HasObject] at hObj
  | cons d ds ih =>
    cases d with
    | cls cl =>
      simp [Program.HasObject, Program.GlobNames] at hObj ⊢
      exact ih hObj
    | obj ob =>
      simp [Program.HasObject, Program.GlobNames] at hObj ⊢
      rcases hObj with hObj | hObj
      · cases hObj
        simp
      · exact Or.inr (ih hObj)

-- noncomputable def Program.SolvedObjects (L : Program) : Config → Program := by
--   classical
--   exact fun
--     | .mk G σ F _ _ =>
--       L.filter (fun d => match d with
--         | .cls _ => true
--         | .obj o => decide ((Stable L F G σ ∧ o.name = G) ∨ InFixPoint F o.name))
--     | .cycle _ => []
--     | .done F =>
--       L.filter (fun d => match d with
--         | .cls _ => true
--         | .obj o => decide (InFixPoint F o.name))

theorem algo_fixpoint_is_decl_fixpoint {c : Config}
    {L : Program} {hL : L.WellFormed}
    (hC : Solve.Star L (Config.start L hL) c)
    : ∀ L' : Program,
        (∀ d, d ∈ L' → d ∈ L) →
        (∀ G, G ∈ L'.GlobNames → InFixPoint c.fixpoints G) →
        Proof.FixPoint c.fixpoints.glue L' := by
  intro L' hLsub hG
  have empty_fixpoint (hEmpty : ∀ G, G ∉ L'.GlobNames) :
      Proof.FixPoint (FixPoints.glue (fun _ => none)) L' := by
    have hNoObj : ∀ {G e₁ e₂}, ¬ L'.HasObject G e₁ e₂ := by
      intro G e₁ e₂ hObj
      exact hEmpty G (hasObject_mem_globNames hObj)
    have hNoRE : ∀ {G c e}, ¬ Proof.RE (FixPoints.glue (fun _ => none)) L' G c e := by
      intro G c e hRE
      induction hRE with
      | init₁ hObj => exact hNoObj hObj
      | init₂ hObj => exact hNoObj hObj
      | body hRM _ => simp [FixPoints.glue] at hRM
      | proj _ ih => exact ih
      | newC₁ _ ih => exact ih
      | newC₂ _ ih => exact ih
      | app₁ _ ih => exact ih
      | app₂ _ ih => exact ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro G e₁ e₂ K₁ K₂ hObj _ _
      exact (hNoObj hObj).elim
    · intro G C body K hRM _ _
      simp [FixPoints.glue] at hRM
    · intro G C e K hRM _ _
      simp [FixPoints.glue] at hRM
    · intro G e₁ e₂ K₁ hObj _
      exact (hNoObj hObj).elim
    · intro G e₁ e₂ K₂ hObj _
      exact (hNoObj hObj).elim
    · intro G c D e₁ e₂ K₁ K₂ hRE _ _
      exact (hNoRE hRE).elim
    · intro G c e₁ e₂ K₁ K₂ hRE _ _
      exact (hNoRE hRE).elim
    · intro G G₀ c K₁ e₁ e₂ hRE _ _
      exact (hNoRE hRE).elim
  induction hC with
  | refl =>
    apply empty_fixpoint
    simpa [Config.start, Config.fixpoints, InFixPoint] using hG
  | tail hr hgrow ih =>

    induction hgrow with
    | step => exact ih hG
    | suspend => exact ih hG
    | cycle =>
      apply empty_fixpoint
      simpa [Config.fixpoints, InFixPoint] using hG
    | @resume G₀ G₁ σ₀ σ₁ F S Q hst =>
      have hlocal : FixPoint G₀ σ₀ L F := stable_to_local_fixpoint hst
      simp [Config.fixpoints]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro G e₁ e₂ K₁ K₂ hObj hC₁ hC₂
        by_cases heq : G = G₀
        · subst heq
          simp only [FixPoints.glue, FixPoints.insert]
          exact hlocal.rm_init (e₁ := e₁) (e₂ := e₂) sorry sorry sorry
        · have hFG : ∃ σ, F G = some σ := by
            simpa [InFixPoint, Config.fixpoints, FixPoints.insert_other heq] using
              (hG G (hasObject_mem_globNames hObj))
          simp [FixPoints.glue, FixPoints.insert, heq]

          sorry
      · intro G C body K hRM _ _
        sorry
      · intro G C e K hRM _ _
        sorry
      · intro G e₁ e₂ K₁ hObj _
        sorry
      · intro G e₁ e₂ K₂ hObj _
        sorry
      · intro G c D e₁ e₂ K₁ K₂ hRE _ _
        sorry
      · intro G c e₁ e₂ K₁ K₂ hRE _ _
        sorry
      · intro G G₀ c K₁ e₁ e₂ hRE _ _
        sorry
    | next => sorry
    | @finish G₀ σ₀ F hst =>
      -- have hGF : InFixPoint (Config.mk G₀ σ₀ F List.nil List.nil).fixpoints G := by
      --   by_cases heq : G = G₀
      --   · simp [Config.fixpoints, InFixPoint]
      --     simp [Config.fixpoints, InFixPoint, FixPoints.insert] at hF
      --     exact hF
      --   · sorry -- using config.wellformed
      -- have h := ih hGF

      sorry


theorem solve_done_fixpoint {L : Program} {F : FixPoints} {hL : L.WellFormed}
    (h : Solve.Star L (Config.start L hL) (.done F)) : Proof.FixPoint F.glue L :=
  sorry -- algo_fixpoint_is_decl_fixpoint h

end Algorithm
