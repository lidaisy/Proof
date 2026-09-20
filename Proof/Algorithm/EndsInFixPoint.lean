import Proof.Algorithm.Definition

namespace Algorithm

open Proof (Program GlobName Expr)

theorem every_object_is_in_fixpoint {L : Program} {hL : L.HasMain} {G : GlobName}
    {e₁ e₂ : Expr} {c : Config} (hG : L.HasObject G e₁ e₂)
    (hC : Solve.Star L (Config.start L hL) c)
    : InFixPoint c.fixpoints G := by
  sorry

theorem fixpoint_is_stable {c : Config} {G : GlobName}
    {L : Program} (h : InFixPoint c.fixpoints G)
    : Stable L c.fixpoints G (c.fixpoints.lookup G h) := by
  sorry

theorem algo_fixpoint_is_decl_fixpoint {c : Config}
    {L : Program} {hL : L.HasMain} (hC : Solve.Star L (Config.start L hL) c)
    -- add derived L here!!!
    : Proof.FixPoint c.fixpoints.glue L := by
  -- we need to break down Star to base case and inductive case...
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- rm_init
    intro G e₁ e₂ K₁ K₂ hG hCe₁ hCe₂
    -- have hIFP := every_object_is_in_fixpoint hG h
    -- have hS := fixpoint_is_stable (L := L) hIFP
    -- have hGrow := hS.left (F.lookup G hIFP)
    sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry
  · sorry

theorem solve_done_fixpoint {L : Program} {F : FixPoints} {hL : L.HasMain}
    (h : Solve.Star L (Config.start L hL) (.done F)) : Proof.FixPoint F.glue L :=
  algo_fixpoint_is_decl_fixpoint h

end Algorithm
