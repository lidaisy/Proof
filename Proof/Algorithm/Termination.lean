import Proof.Algorithm.Definition

namespace Algorithm

open Proof (GlobName Program)

theorem solve_progress {L : Program} {G : GlobName} {σ : State G} {F : FixPoints}
    {S : Stack} {Q : Queue} : ∃ c', Solve L (.mk G σ F S Q) c' := by
  by_cases hst : Stable L F G σ
  · cases S with
    | cons fr S' =>
        obtain ⟨G', σ'⟩ := fr
        exact ⟨_, Solve.resume hst⟩
    | nil =>
        cases Q with
        | nil => exact ⟨_, Solve.finish hst⟩
        | cons G₀ Q' =>
            by_cases hF : InFixPoint F G₀
            · exact ⟨_, Solve.skip hF⟩
            · exact ⟨_, Solve.next hst hF⟩
  · simp only [Stable, not_and_or] at hst
    rcases hst with h | h
    -- something still to add to the state
    · push Not at h
      obtain ⟨σ', hgrow, -⟩ := h
      exact ⟨_, Solve.step hgrow⟩
    -- something still to be solved first
    · push Not at h
      obtain ⟨c, i, G₀, hre, hneeds⟩ := h
      by_cases hcyc : G₀ = G ∨ G₀ ∈ Stack.globs S
      · exact ⟨_, Solve.cycle hre hneeds hcyc⟩
      · push Not at hcyc
        exact ⟨_, Solve.suspend hre hneeds hcyc.1 hcyc.2⟩

theorem solve_terminates {L : Program} {G : GlobName}
    {hL : L.HasMain}
    (hcyc : ¬(Solve.Star L (Config.start L hL) (Config.cycle G)))
    : ∃ F, Solve.Star L (Config.start L hL) (Config.done F) := by
  -- apply solve_progress and we get c'
  -- cases c'
  -- .done => trivial
  -- .cycle => contradiction
  -- .step =>
  -- .skip
  -- .suspend
  -- .next
  -- .resume
  sorry

-- /-- **If the algorithm reports no cycle, it terminates in `.done`.**

--     By `solve_progress` a run can always be extended, so the only way to fail
--     to reach `.done F` is to run forever; what remains is the well-foundedness
--     argument, which is why this is stated — and used — as a black box:

--     * The conclusion is existential: it is enough that *one* run terminates,
--       not that every one does.  This matters, because `Solve.step` may fire on
--       a `Grow` that adds nothing (`Stable` forbids only growth that escapes
--       `σ`, and `step` does not test for it), so an adversarial run can `step`
--       forever.  The run to build is the one that takes `step` only when it
--       strictly increases the state, and the rule `solve_progress` selects
--       otherwise.
--     * Along such a run each `step` is a strict `<` in `State G`, whose height
--       is finite because every set a `Grow` adds is drawn from the classes,
--       objects and globals *occurring in `L`* — the ambient `ClassName` and
--       `GlobName` are `String`, so the bound comes from the program, not the
--       type.
--     * `suspend` is the only rule that grows the stack, and it fires only for
--       `G₀ ∉ Stack.globs S` with `G₀ ≠ G`, so `Stack.globs S` stays duplicate
--       free and the stack is bounded by `L.GlobNames`; `resume`, `next`, `skip`
--       and `finish` each shrink the stack or the queue.  -/

end Algorithm
