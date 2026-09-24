import Proof.Algorithm.Definition
import Proof.Algorithm.LessThanInv

namespace Algorithm

open Proof (Program)

-- by the less than all fixpoints lemma, since algoRE has G G₀ (from .cycle),
-- So does all fixpoints.
-- ie. RE G G₀
-- prove h : for any config, G _ _ S _, forall G' in S, G ∈ Dep G' (induction over steps)
-- have hdep : G' ∈ Dep G by definition of RE
-- Now by .cycle either G₀ = G or G₀ on stack
-- if first, exact hdep
-- else, by h, we have trans cycle

def StackDep (L : Program) : Config → Prop
  | .mk G _ F S _ =>
      ∀ G' ∈ S.globs, G ∈ Proof.Dep F.glue L G'
  | .cycle _ => True
  | .done _ => True

-- I don't like the above. Should just make a Dep for Algo...
-- Then prove that G is in AlgoDep G'.
-- Prove that AlgoRE is always less than RE. And so AlgoDep is always
-- less than Dep in LessThanInv.
-- then we have the fact that ∀ σ : Proof.Sigma, Proof.FixPoint σ L → G ∈ Proof.Dep σ L G'

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
    | cycle hare hneeds hG =>
      rename_i c i
      have hl := (less_than hL h_star) σ hf
      have hl_all : (Config.mk G' σ' F S Q).all_data ≤ σ := by sorry
      have hre_all : Proof.RE (Config.mk G' σ' F S Q).all_data L G c (Proof.Expr.gproj G i) := sorry
      have hl_re := less_than_imp_re_less_than (E := (Proof.Expr.gproj G i)) hl_all hre_all
      exact Proof.DepJ.direct hl_re
  · cases h_step
  · cases h_step

end Algorithm
