import Proof.Semantics

/-! # Structural lemmas about the frame stack

  The stack datatype and its operations (`Stack.push`/`pop`/`topCall`/`topInit`,
  `Stack.TopInit`, `Stack.HasInit`, …) live in `Proof.Semantics`; this file
  collects the purely structural facts about them, so the invariant files can
  use them without re-deriving anything. -/

namespace Proof

/-- The init frame returned by `topInit` is never a `call` frame: it is
    produced only by the `f :: fs => some (f, [], fs)` branch (with `f` an
    `init1`/`init2`), and the `call` branch merely propagates it unchanged. -/
theorem Stack.topInit_notCall {S : Stack} {i : Frame} {cfs r : Stack}
    (h : S.topInit = some (i, cfs, r)) : i.NotCall := by
  induction S generalizing cfs r with
  | nil => simp [Stack.topInit] at h
  | cons f fs ih =>
    cases f with
    | init1 g e k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        intro t p κ; nofun
    | init2 g k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -, -⟩ := h
        intro t p κ; nofun
    | call t p κ =>
        rw [Stack.topInit] at h
        cases hfs : Stack.topInit fs with
        | none => rw [hfs] at h; simp at h
        | some val =>
            obtain ⟨f', calls, rest⟩ := val
            rw [hfs] at h
            simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, -⟩ := h
            exact ih hfs

/-- `topInit` really does decompose the stack: `S = cfs ++ i :: r`. -/
theorem Stack.topInit_split {S : Stack} {i : Frame} {cfs r : Stack}
    (h : S.topInit = some (i, cfs, r)) : S = cfs ++ i :: r := by
  induction S generalizing i cfs r with
  | nil => simp [Stack.topInit] at h
  | cons f fs ih =>
    cases f with
    | init1 g e k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; simp
    | init2 g k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; simp
    | call t p κ =>
        rw [Stack.topInit] at h
        cases hfs : Stack.topInit fs with
        | none => rw [hfs] at h; simp at h
        | some val =>
            obtain ⟨f', calls, rest⟩ := val
            rw [hfs] at h
            simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            simpa using ih hfs

/-- Every frame collected above the topmost init frame is a `call` frame, hence
    records no global. -/
theorem Stack.topInit_calls_glob {S : Stack} {i : Frame} {cfs r : Stack}
    (h : S.topInit = some (i, cfs, r)) : ∀ g ∈ cfs, g.glob = none := by
  induction S generalizing i cfs r with
  | nil => simp [Stack.topInit] at h
  | cons f fs ih =>
    cases f with
    | init1 g e k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h; simp
    | init2 g k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, rfl, -⟩ := h; simp
    | call t p κ =>
        rw [Stack.topInit] at h
        cases hfs : Stack.topInit fs with
        | none => rw [hfs] at h; simp at h
        | some val =>
            obtain ⟨f', calls, rest⟩ := val
            rw [hfs] at h
            simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg'
            · rfl
            · exact ih hfs g hg'

/-- A stack without a topmost init frame consists entirely of `call` frames. -/
theorem Stack.topInit_eq_none_glob {S : Stack} (h : S.topInit = none) :
    ∀ g ∈ S, g.glob = none := by
  induction S with
  | nil => intro g hg; simp at hg
  | cons f fs ih =>
    cases f with
    | init1 g' e k => simp [Stack.topInit] at h
    | init2 g' k => simp [Stack.topInit] at h
    | call t p κ =>
        rw [Stack.topInit] at h
        cases hfs : Stack.topInit fs with
        | some val => rw [hfs] at h; simp at h
        | none =>
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg'
            · rfl
            · exact ih hfs g hg'

/-- A non-`call` frame is an init frame, so it records some global. -/
theorem Frame.glob_of_notCall {f : Frame} (h : f.NotCall) : ∃ G, f.glob = some G := by
  cases f with
  | init1 g e k => exact ⟨g, rfl⟩
  | init2 g k => exact ⟨g, rfl⟩
  | call t p κ => exact absurd rfl (h t p κ)

/-- If any frame of the stack records a global, the stack has a topmost init
    frame. -/
theorem Stack.hasInit_of_glob {S : Stack} {f : Frame} {G : GlobName}
    (hf : f ∈ S) (hG : f.glob = some G) : S.HasInit := by
  cases hti : S.topInit with
  | none =>
      have hnone := Stack.topInit_eq_none_glob hti f hf
      rw [hG] at hnone
      simp at hnone
  | some v =>
      obtain ⟨i, cfs, r⟩ := v
      exact ⟨i, cfs, r, hti⟩

/-- The frame reported by `topCall` sits among the call frames `cfs` collected
    by `topInit`: `topCall` is exactly the head of `cfs`.  Lets invariants that
    reason about `topCall` (e.g. `RetInv`) borrow the per-frame facts that
    `cfs`-quantified invariants (e.g. `ThisInv`) supply. -/
theorem Stack.topCall_mem_topInit {S : Stack} {i : Frame} {cfs r : Stack}
    {t : Loc} {p : Value} {κ : ECtx}
    (hc : S.topCall = some (Frame.call t p κ))
    (hi : S.topInit = some (i, cfs, r)) : Frame.call t p κ ∈ cfs := by
  cases S with
  | nil => simp [Stack.topCall] at hc
  | cons f fs =>
    cases f with
    | init1 g e k => simp [Stack.topCall] at hc
    | init2 g k => simp [Stack.topCall] at hc
    | call t' p' κ' =>
        simp only [Stack.topCall, Option.some.injEq, Frame.call.injEq] at hc
        obtain ⟨rfl, rfl, rfl⟩ := hc
        rw [Stack.topInit] at hi
        cases hfs : Stack.topInit fs with
        | none => rw [hfs] at hi; simp at hi
        | some val =>
            obtain ⟨f', calls, rest⟩ := val
            rw [hfs] at hi
            simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at hi
            obtain ⟨-, rfl, -⟩ := hi
            exact List.mem_cons_self

/-- No `call` frames above the topmost init frame means the init frame is on
    top, so `topCall` reports nothing. -/
theorem Stack.topCall_eq_none_of_topInit_nil {S : Stack} {i : Frame} {r : Stack}
    (h : S.topInit = some (i, [], r)) : S.topCall = none := by
  cases S with
  | nil => simp [Stack.topInit] at h
  | cons f fs =>
    cases f with
    | init1 g e k => simp [Stack.topCall]
    | init2 g k => simp [Stack.topCall]
    | call t p κ =>
        rw [Stack.topInit] at h
        cases hfs : Stack.topInit fs with
        | none => rw [hfs] at h; simp at h
        | some val =>
            obtain ⟨f', calls, rest⟩ := val
            rw [hfs] at h
            simp at h

/-- Conversely, a non-empty list of call frames above the topmost init frame
    means the head of the stack is a `call` frame, which `topCall` reports. -/
theorem Stack.topCall_of_topInit_cons {S : Stack} {i f : Frame} {fs r : Stack}
    (h : S.topInit = some (i, f :: fs, r)) :
    ∃ t p κ, S.topCall = some (Frame.call t p κ) := by
  cases S with
  | nil => simp [Stack.topInit] at h
  | cons g gs =>
    cases g with
    | init1 a b c => simp [Stack.topInit] at h
    | init2 a b => simp [Stack.topInit] at h
    | call t p κ => exact ⟨t, p, κ, rfl⟩

end Proof
