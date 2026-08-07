import Proof.Semantics
import Proof.Stack
import Proof.Analysis
import Proof.CorrectnessRelation
import Mathlib.Tactic.Set
import Proof.AccessImpliesDep
import Proof.StackDepChain
import Proof.PartialOnStack

namespace Proof

theorem abstract_detects_cycle {L : Program} {G Gₘ: GlobName} {S : Stack}
  {σ : Sigma} {E : ECtx} {H : Heap} {Γ : GTable} {i : Idx} {u₁ u₂ : GVal}
  (hσ : FixPoint σ L)
  (hrun : Star L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj Gₘ Idx.one))
      (.mk H Γ S (E.plug (Expr.gproj G i))))
  (hG : Γ G = (GEntry.mk u₁ u₂)) (hnone: u₁ = none ∨ u₂ = none) :
  G ∈ Dep σ L G := by

  have hGOnStack : inGlobals G S := (partially_init_obj_on_stack hrun hG hnone)
  have hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G i))) := inv_preservation hσ hrun
  have hrinv: REInv σ L (.mk H Γ S (E.plug (Expr.gproj G i))) := REInv.preservation hσ hrun
  have hsd : StackDep σ L (.mk H Γ S (E.plug (Expr.gproj G i))) := stack_dep_run hσ hrun

  obtain ⟨f, hfS, hfG⟩ := hGOnStack

  obtain ⟨ifr, cfs, r, hti⟩ := Stack.hasInit_of_glob hfS hfG
  obtain ⟨Gₜ, hGₜ⟩ := Frame.glob_of_notCall (Stack.topInit_notCall hti)
  have htiG : ifr.glob = some Gₜ := hGₜ

  have hGInDepGₜ : G ∈ Dep σ L Gₜ := acc_implies_dep hti htiG hinv hrinv

  obtain ⟨pre, suf, hS⟩ := List.append_of_mem hfS

  rcases StackDep.topInit_dep hsd hti hGₜ hS hfG with rfl | hGₜInDepG
  · exact hGInDepGₜ
  · exact DepJ.trans hGₜInDepG hGInDepGₜ

end Proof
