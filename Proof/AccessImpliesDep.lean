import Proof.Semantics
import Proof.Stack
import Proof.Analysis
import Proof.CorrectnessRelation
import Proof.REInv

namespace Proof

theorem acc_implies_dep {L : Program} {G G': GlobName} {S cfs r : Stack}
  {σ : Sigma} {E : ECtx} {H : Heap} {Γ : GTable} {i : Idx} {ifr : Frame}
  (hti : S.topInit = some (ifr, cfs, r)) (htiG : ifr.glob = some G)
  (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G' i))))
  (hrinv : REInv σ L (.mk H Γ S (E.plug (Expr.gproj G' i)))) :
  G' ∈ Dep σ L G := by

  rcases cfs with _ | ⟨f, fs⟩
  · -- if cfs = []
    have hfoc : RRE σ L G none (E.plug (Expr.gproj G' i)) :=
      (hrinv.1 G ifr ([] : Stack) r hti htiG).2 (Stack.topCall_eq_none_of_topInit_nil hti)
    exact RRE.dep (RRE.plug E hfoc)
  · -- cfs ≠ []
    obtain ⟨t, p, κ, htc⟩ := Stack.topCall_of_topInit_cons hti
    obtain ⟨-, -, -, -, -, -, hrm, -⟩ := hinv
    obtain ⟨C, hHt, -⟩ :=
      hrm S ifr (f :: fs) r (Frame.call t p κ) G t (List.suffix_refl _) hti htiG
        (Stack.topCall_mem_topInit htc hti) rfl
    have hfoc : RRE σ L G C.cls (E.plug (Expr.gproj G' i)) :=
      (hrinv.1 G ifr (f :: fs) r hti htiG).1 t p κ C htc hHt
    exact RRE.dep (RRE.plug E hfoc)

end Proof
