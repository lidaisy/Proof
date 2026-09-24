import Proof.Algorithm.Definition
import Proof.Algorithm.LessThanInv

namespace Algorithm

open Proof (Program GlobName Expr)

def StackDep (L : Program) : Config → Prop
  | c@(.mk G' _ _ S _) =>
      ∀ G ∈ S.globs, G' ∈ Proof.Dep c.all_data L G
  | .cycle _ => True
  | .done _ => True

theorem stack_dep_step {c c' : Config} {L : Program} {hL : L.HasMain}
    (hstep : Solve L c c') (h : StackDep L c) :
    StackDep L c' := sorry

theorem stack_dep_star {c : Config} {L : Program} {hL : L.HasMain}
    (hstar : Solve.Star L (Config.start L hL) c) :
    StackDep L c := sorry

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
