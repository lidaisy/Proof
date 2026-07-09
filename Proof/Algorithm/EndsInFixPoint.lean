import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program GlobName Expr)

theorem fixpoint_is_stable {c : Config} {G : GlobName} {L : Program}
    {hL : L.WellFormed} (hC : Solve.Star L (Config.start L hL) c)
    (h : InFixPoint c.fixpoints G)
    : Stable L c.fixpoints G (c.fixpoints.lookup G h) := by

  sorry

def FilteredProgram (L : Program) (c : Config) : Program :=
  L.filter (fun d => match d with
  | .cls _ => true
  | .obj o => decide (InFixPoint c.fixpoints o.name))

theorem insertion_maintains_stability {c : Config} {G G' : GlobName} {L : Program}
    {hL : L.WellFormed} {σ : State G} {σ' : State G'} {F : FixPoints}
    (hC : Solve.Star L (Config.start L hL) c) (hfix : F = c.fixpoints)
    (hF: Proof.FixPoint F.glue (FilteredProgram L c)) (hS : Stable L F G σ)
    (hG' : (F.insert G σ) G' = σ')
    : Stable L (F.insert G σ) G' σ' := by

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

theorem FilteredProgram.sub {L L' : Program} {c : Config}
    (hF : L' = FilteredProgram L c)
    : ∀ d, d ∈ L' → d ∈ L := by
  subst L'
  intro d hd
  exact (List.mem_filter.mp hd).1

theorem FilteredProgram.object {L L' : Program} {G : GlobName}
    {c : Config} (hF : L' = FilteredProgram L c) (hG : G ∈ L'.GlobNames)
    : InFixPoint c.fixpoints G := by
  subst L'
  induction L with
  | nil => simp [FilteredProgram, Program.GlobNames] at hG
  | cons d ds ih =>
    cases d with
    | cls cl =>
      exact ih (by simpa [FilteredProgram, Program.GlobNames] using hG)
    | obj ob =>
      by_cases h : InFixPoint c.fixpoints ob.name
      · simp [FilteredProgram, Program.GlobNames, h] at hG
        rcases hG with rfl | hG
        · exact h
        · exact ih hG
      · exact ih (by simpa [FilteredProgram, Program.GlobNames, h] using hG)

theorem calls_bridge {σ₀ : State G₀}
    (h : Proof.Calls0 G (F.insert G₀ σ₀).glue e₁ K₁)
    : Calls0 σ₀ F e₁ K₁ := sorry

private theorem kj0_glue_bridge {G : GlobName} {σ : State G}
    {F : FixPoints} {L : Program} {e : Expr} {K : Set Proof.OPair}
    (hσ : F G = some σ) (hst : Stable L F G σ)
    (howners : ∀ {e i K}, RE G σ L none (Expr.proj e i) →
      Proof.KJ0 G F.glue e K → ∀ p ∈ K, p.1 = G ∨ InFixPoint F p.1)
    (hre : RE G σ L none e) (h : Proof.KJ0 G F.glue e K) :
    ∃ D, KJ0 σ F e K D := by
  revert hre
  induction h with
  | @proj e i K hk ih =>
    intro hre
    obtain ⟨D, hk'⟩ := ih (RE.proj hre)
    have hK := howners hre hk
    have hfields :
        (⋃ p, ⋃ hp : p ∈ K,
          if hG : p.1 = G then σ.Fld i p.2
          else (F.lookup p.1 ((hK p hp).resolve_left hG)).Fld i p.2) =
        ⋃ p ∈ K, F.glue.Fld i p.1 p.2 := by
      apply Set.iUnion_congr
      intro p
      apply Set.iUnion_congr
      intro hp
      split
      · next heq => rw [heq, FixPoints.glue_fld hσ]
      · next hne =>
          obtain ⟨τ, hτ⟩ := (hK p hp).resolve_left hne
          rw [FixPoints.glue_fld hτ, FixPoint.lookup_eq _ hτ]
    exact ⟨_, hfields ▸ KJ0.proj hK hk'⟩
  | @gproj H i =>
    intro hre
    have hin : InFixPoint F H := by
      by_contra hnot
      exact hst.2 none i H hre (Needs.gproj hnot)
    obtain ⟨τ, hτ⟩ := hin
    refine ⟨{H}, ?_⟩
    simpa only [FixPoints.glue_gfld hτ, FixPoint.lookup_eq _ hτ] using
      (KJ0.gproj (σ := σ) (F := F) (i := i) ⟨τ, hτ⟩)
  | newC =>
    intro _
    exact ⟨_, KJ0.newC⟩
  | app _ ih =>
    intro hre
    obtain ⟨D, hk⟩ := ih (RE.app₁ hre)
    exact ⟨D, by simpa only [FixPoints.glue_ret hσ] using KJ0.app hk⟩
  | val =>
    intro _
    exact ⟨_, KJ0.val⟩

/-- Bridge reachable calls when field projections only read current or solved owners. -/
theorem calls0_bridge {G G₀ : GlobName} {σ : State G} {σ₀ : State G₀}
    {F : FixPoints} {L : Program} {e₁ : Expr}
    {K₁: Set Proof.ClassName} (hne : G ≠ G₀) (hσ : F G = some σ)
    (hst : Stable L (F.insert G₀ σ₀) G σ)
    (howners : ∀ {e i K}, RE G σ L none (Expr.proj e i) →
      Proof.KJ0 G (F.insert G₀ σ₀).glue e K →
      ∀ p ∈ K, p.1 = G ∨ InFixPoint (F.insert G₀ σ₀) p.1)
    (hre : RE G σ L none e₁)
    (h : Proof.Calls0 G (F.insert G₀ σ₀).glue e₁ K₁)
    : Calls0 σ (F.insert G₀ σ₀) e₁ K₁ := by
  have hσ' : (F.insert G₀ σ₀) G = some σ := by
    rw [FixPoints.insert_other hne, hσ]
  revert hre
  induction h with
  | gproj =>
    intro _
    exact Calls0.gproj
  | proj _ ih =>
    intro hre
    exact Calls0.proj (ih (RE.proj hre))
  | newC _ _ ih₁ ih₂ =>
    intro hre
    exact Calls0.newC (ih₁ (RE.newC₁ hre)) (ih₂ (RE.newC₂ hre))
  | app hk _ _ ih₁ ih₂ =>
    intro hre
    obtain ⟨D, hk'⟩ := kj0_glue_bridge hσ' hst howners (RE.app₁ hre) hk
    exact Calls0.app hk' (ih₁ (RE.app₁ hre)) (ih₂ (RE.app₂ hre))
  | val =>
    intro _
    exact Calls0.val


theorem algo_fixpoint_is_decl_fixpoint {c : Config}
    {L L' : Program} {hL : L.WellFormed}
    (hC : Solve.Star L (Config.start L hL) c)
    (hF : L' = FilteredProgram L c)
    : Proof.FixPoint c.fixpoints.glue L' := by
  have empty_fixpoint {L' : Program} (hEmpty : ∀ G, G ∉ L'.GlobNames) :
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
  induction hC generalizing L' with
  | refl =>
    apply empty_fixpoint
    intro G hG
    have h := FilteredProgram.object hF hG
    simp [Config.start, Config.fixpoints, InFixPoint] at h
  | tail hr hgrow ih =>

    induction hgrow with
    | step => exact ih hF
    | suspend => exact ih hF
    | cycle =>
      apply empty_fixpoint
      intro G hG
      have h := FilteredProgram.object hF hG
      simp [Config.fixpoints, InFixPoint] at h
    | @resume G₀ G₁ σ₀ σ₁ F S Q hst =>
      subst L'
      have hOld := ih rfl
      have hlocal : FixPoint G₀ σ₀ L F := stable_to_local_fixpoint hst
      simp [Config.fixpoints]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro G e₁ e₂ K₁ K₂ hObj hC₁ hC₂
        by_cases heq : G = G₀
        · subst heq
          simp only [FixPoints.glue, FixPoints.insert]
          exact hlocal.rm_init (e₁ := e₁) (e₂ := e₂)
            (FilteredProgram.sub rfl _ hObj) (calls_bridge hC₁) (calls_bridge hC₂)
        · have hFG : ∃ σ, F G = some σ := by
            simpa [InFixPoint, Config.fixpoints, FixPoints.insert_other heq] using
              (FilteredProgram.object rfl (hasObject_mem_globNames hObj))
          obtain ⟨σ, hσ⟩ := hFG
          have hSt := insertion_maintains_stability (G' := G) (σ' := σ) hr rfl hOld hst
            (by simpa only [Config.fixpoints, FixPoints.insert_other heq] using hσ)
          simp [Config.fixpoints] at hSt
          have hLocalFix := stable_to_local_fixpoint hSt
          simp only [FixPoints.glue, FixPoints.insert_other heq, hσ,
            Option.map_some, Option.getD_some]
          exact hLocalFix.rm_init (e₁ := e₁) (e₂ := e₂)
            (FilteredProgram.sub rfl _ hObj) sorry sorry
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
