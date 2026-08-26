import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program)

theorem solve_done_fixpoint {L : Program} {F : FixPoints} {hL : L.HasMain}
    (h : Solve.Star L (Config.start L hL) (.done F)) : Proof.FixPoint F.glue L := by
  sorry

end Algorithm
