import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program)

-- by the less than all fixpoints lemma, since algoRE has G G₀ (from .cycle),
-- So does all fixpoints.
-- prove h : for any config, G _ _ S _, forall G' in S, G ∈ Dep G' (induction over steps)
-- have hdep : G' ∈ Dep G by definition
-- Now by .cycle either G₀ = G or G₀ on stack
-- if first, exact hdep
-- else, by h, we have trans cycle


theorem report_cycle_then_dep {L : Program} {hL : L.HasMain} :
    ∃ G, Solve.Star L (Config.start L hL) (.cycle G) →
    ∀ σ : Proof.Sigma, Proof.FixPoint σ L → G ∈ Proof.Dep σ L G := by
  sorry

end Algorithm
