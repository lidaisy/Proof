import Proof.Semantics
import Proof.Analysis
import Proof.CorrectnessRelation

namespace Proof

theorem partially_init_obj_on_stack {Γ : GTable} {G : GlobName} {uᵢ u₁ u₂ : GVal}
    {S : Stack} (hG : Γ G = (GEntry.mk u₁ u₂)) (hsel : uᵢ = u₁ ∨ uᵢ = u₂)
    (hnone : uᵢ = none) : inGlobals G S :=
  sorry

end Proof
