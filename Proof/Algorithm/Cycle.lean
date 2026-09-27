import Proof.Algorithm.Definition
import Proof.Algorithm.LessThanInv

namespace Algorithm

open Proof (Program GlobName Expr Idx)

def StackDep (L : Program) : Config → Prop
  | c@(.mk G' _ _ S _) =>
      ∀ G ∈ S.globs, G' ∈ Proof.Dep c.all_data L G
  | .cycle _ => True
  | .done _ => True

theorem Config.all_data_grow {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G}
    {S : Stack} {Q : Queue} (hgrow : Grow L F G σ σ')
    : Config.all_data (.mk G σ F S Q) ≤ Config.all_data (.mk G σ' F S Q) := by
  sorry

theorem Config.stack_to_all {L : Program} {G G' : GlobName} {σ' : State G'} {σ : State G} {F : FixPoints} {ctx : Ctx}
    {E : Expr } {S : Stack} {Q : Queue} (h : RE G' σ' L ctx E) (hS : G' ∈ S.globs)
    : Proof.RE (Config.mk G σ F S Q).all_data L G' ctx E := by
  sorry

theorem Config.all_data_resume {L : Program} {G G' : GlobName} {σ' : State G'} {σ : State G} {F : FixPoints} {ctx : Ctx}
    {E : Expr } {S : Stack} {Q : Queue} (h : RE G' σ' L ctx E) (hS : G' ∈ S.globs)
    : Proof.RE (Config.mk G σ F S Q).all_data L G' ctx E := by
  sorry

theorem stack_dep_step {c c' : Config} {L : Program} {hL : L.HasMain}
    (hstep : Solve L c c') (h : StackDep L c) :
    StackDep L c' := by
  cases hstep with
  | @step G σ σ' F S Q hg =>
      intro G' hG'
      have hless := Config.all_data_grow (S := S) (Q := Q) hg
      have hDep := h G' hG'
      exact (less_than_imp_dep_less_than (G := G') (L := L) hless) hDep
  | @suspend G G₀ σ F S Q c i hre hneeds hne hnS =>
      intro G' hG'
      have hRE_all := Config.stack_to_all (σ := (State.zero G₀)) (F := F) (S := (⟨G, σ⟩ :: S)) (Q := (Q.remove G₀)) hre (by simp [Stack.globs])
      have hDep : G₀ ∈ Proof.Dep (Config.mk G₀ (State.zero G₀) F (⟨G, σ⟩ :: S) (Q.remove G₀)).all_data L G := Proof.DepJ.direct hRE_all
      by_cases heq : G' = G
      · subst heq; exact hDep
      · sorry
      -- have ∀ G' ∈ S.globs, G ∈ Proof.Dep G' by h
      -- then exact Proof.DepJ.trans hDep above
  | cycle =>
      trivial
  | @resume G G' σ σ' F S Q _ =>
      intro G' hG'
      -- again, go by h
      sorry
  | next =>
      intro G' hG'
      trivial
  | skip =>
      intro G' hG'
      trivial
  | finish =>
      trivial

theorem stack_dep_star {c : Config} {L : Program} {hL : L.HasMain}
    (hstar : Solve.Star L (Config.start L hL) c) :
    StackDep L c := sorry

theorem Config.state_to_all {L : Program} {G' : GlobName} {σ' : State G'} {F : FixPoints} {ctx : Ctx}
    {E : Expr } {S : Stack} {Q : Queue} (h : RE G' σ' L ctx E)
    : Proof.RE (Config.mk G' σ' F S Q).all_data L G' ctx E := by
  have hnotFix : ¬ InFixPoint F G' := sorry /- This should be its own theorem in Definition.lean-/
  have hsubeq : State.Sub σ' (State.ofSigma (Config.mk G' σ' F S Q).all_data G') := by
   sorry
  exact re_bridge hsubeq h

theorem report_cycle_then_dep {L : Program} {hL : L.HasMain} :
    ∀ G, Solve.Star L (Config.start L hL) (.cycle G) →
    ∀ σ : Proof.Sigma, Proof.FixPoint σ L → G ∈ Proof.Dep σ L G := by
  intro G hcyc σ hf
  obtain _ | ⟨h_star, h_step⟩ := hcyc
  rename_i c_prev
  rcases c_prev with ⟨ G', σ', F, S, Q ⟩ | F | G'
  · cases h_step with
    | cycle hSRE hneeds hG =>
      rename_i c i
      have hl := (less_than hL h_star) σ hf
      have hbelow := config_below_imp_all_data_less_than hl
      -- factor out (Config.mk G' σ' F S Q).all_data
      have hCRE : Proof.RE (Config.mk G' σ' F S Q).all_data L G' c (Expr.gproj G i) := Config.state_to_all hSRE
      have hCDep : G ∈ Proof.Dep (Config.mk G' σ' F S Q).all_data L G' := Proof.DepJ.direct hCRE
      have hCCyc : G ∈ Proof.Dep (Config.mk G' σ' F S Q).all_data L G := by
        rcases hG with hG' | hG'
        · subst hG'
          exact hCDep
        · have hADep : G' ∈ Proof.Dep (Config.mk G' σ' F S Q).all_data L G := by
            exact (stack_dep_star h_star) G hG'
          exact Proof.DepJ.trans hADep hCDep
      exact less_than_imp_dep_less_than hbelow hCCyc
  · cases h_step
  · cases h_step

end Algorithm
