import Proof.Algorithm.Definition
import Proof.Algorithm.Cycle

namespace Algorithm

open Proof (Program GlobName)

theorem algo_no_cycle_then_no_dep {L : Program} {G : GlobName} {hL : L.HasMain}
    : ¬(∃ G, Solve.Star L (Config.start L hL) (Config.cycle G)) →
      ∃ F, Solve.Star L (Config.start L hL) (Config.done F) ∧
      ¬ ∃ G', G' ∈ Proof.Dep F.glue L G' := by
  -- first part by solve_terminates
  sorry

theorem algo_detects_decl_cycle {L : Program} {hL : L.HasMain} {G : GlobName}
    : ∃ G, ∀ σ : Proof.Sigma, Proof.FixPoint σ L → G ∈ Proof.Dep σ L G →
      ∃ G', Solve.Star L (Config.start L hL) (.cycle G') := by
  -- the above states that exist a fixpoint (by solve_done_fixpoint) with
  -- no dep cycles.
  -- contrapositive of the above says the hypothesis, ie.
  -- ∃ G, ∀ σ : Proof.Sigma, Proof.FixPoint σ L → G ∈ Proof.Dep σ L G
  -- then we've got a cycle. done.
  sorry

end Algorithm
