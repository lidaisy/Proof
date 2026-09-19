import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program GlobName Expr)

theorem every_object_is_in_fixpoint {L : Program} {hL : L.HasMain} {G : GlobName}
    {e₁ e₂ : Expr} {F : FixPoints} (hG : L.HasObject G e₁ e₂)
    (hC : Solve.Star L (Config.start L hL) (.done F))
    : InFixPoint F G := by
  sorry

theorem fixpoint_is_stable {c : Config} {G : GlobName}
    {L : Program} (h : InFixPoint c.fixpoints G)
    : Stable L c.fixpoints G (c.fixpoints.lookup G h) := by
  sorry

theorem solve_done_fixpoint {L : Program} {F : FixPoints} {hL : L.HasMain}
    (h : Solve.Star L (Config.start L hL) (.done F)) : Proof.FixPoint F.glue L := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rm_init
    intro G e₁ e₂ K₁ K₂ hG hCe₁ hCe₂
    sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

end Algorithm
