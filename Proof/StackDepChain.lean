import Proof.Semantics
import Proof.Stack
import Proof.Analysis
import Proof.CorrectnessRelation
import Mathlib.Tactic.Set
import Proof.AccessImpliesDep

namespace Proof

def StackDep (σ : Sigma) (L : Program) : Config → Prop
  | .mk _ _ S _ =>
      ∀ pre f r G, S = pre ++ f :: r → f.glob = some G →
        ∀ g ∈ pre, ∀ G', g.glob = some G' → G' ∈ Dep σ L G
  | .crash => True

theorem StackDep.topInit_dep {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable}
    {S cfs rt: Stack} {e : Expr} {it : Frame} {Gt : GlobName}
    {pre : Stack} {f : Frame} {r : Stack} {Gf : GlobName}
    (hs : StackDep σ L (.mk H Γ S e)) (hti : S.topInit = some (it, cfs, rt))
    (hGt : it.glob = some Gt) (hS : S = pre ++ f :: r)
    (hGf : f.glob = some Gf) :
    Gt = Gf ∨ Gt ∈ Dep σ L Gf := by
  have hSsplit : S = cfs ++ it :: rt := Stack.topInit_split hti
  have h1 : f :: r <:+ S := ⟨pre, hS.symm⟩
  have h2 : it :: rt <:+ S := ⟨cfs, hSsplit.symm⟩
  rcases List.suffix_or_suffix_of_suffix h1 h2 with hsuf | hsuf
  · -- `f` is at or below the topmost init frame
    rcases List.suffix_cons_iff.mp hsuf with heq | hsuf'
    · simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact Or.inl (Option.some.inj (hGt.symm.trans hGf))
    · -- strictly below: the topmost init frame lives in `pre`
      right
      obtain ⟨w, hw⟩ := hsuf'
      have hpre : pre = cfs ++ it :: w := by
        apply List.append_cancel_right (bs := f :: r)
        rw [← hS, hSsplit, ← hw]
        simp
      exact hs pre f r Gf hS hGf it (by rw [hpre]; simp) Gt hGt
  · -- `f` at or below is the only option; anything above is a `call` frame
    rcases List.suffix_cons_iff.mp hsuf with heq | hsuf'
    · simp only [List.cons.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      exact Or.inl (Option.some.inj (hGt.symm.trans hGf))
    · exfalso
      obtain ⟨w, hw⟩ := hsuf'
      have hcfs : pre ++ f :: w = cfs := by
        apply List.append_cancel_right (bs := it :: rt)
        rw [← hSsplit, hS, ← hw]
        simp
      have hfmem : f ∈ cfs := by rw [← hcfs]; simp
      rw [Stack.topInit_calls_glob hti f hfmem] at hGf
      simp at hGf

theorem stack_dep_step {L : Program} {σ : Sigma} {c c' : Config}
  (hinv : Inv σ L c) (hrinv : REInv σ L c) (hstep : Step L c c') (hs : StackDep σ L c) :
  StackDep σ L c' := by
  cases hstep with
  | this _ _ => exact hs
  | param _ _ => exact hs
  | proj _ => exact hs
  | gproj _ _ => exact hs
  | newAlloc _ _ _ _ => exact hs
  | uninit _ _ => trivial
  | @methCall H Γ S E ℓ C G G₀ v v₁ v₂ body _ _ _ _ _ =>
      -- Pushes a `call` frame, which records no global
      intro pre f r Gf hS hGf g hg G' hG'
      rcases pre with _ | ⟨p₀, pre'⟩
      · simp at hg
      · simp only [Stack.push, List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, hS⟩ := hS
        rcases List.mem_cons.mp hg with rfl | hg'
        · simp [Frame.glob] at hG'
        · exact hs pre' f r Gf hS hGf g hg' G' hG'
  | @ret H Γ S κ t C G p v v₁ v₂ _ =>
      -- Pops a `call` frame: every decomposition of `S` extends to one of
      -- `call t p κ :: S` by growing `pre`.
      intro pre f r Gf hS hGf g hg G' hG'
      exact hs (Frame.call t p κ :: pre) f r Gf (by rw [hS]; simp) hGf g
        (List.mem_cons_of_mem _ hg) G' hG'
  | @ipop H Γ S G e₁ e₂ k v₁ v₂ _ _ =>
      -- Pops the `init2 G k` frame: same reasoning as `ret`.
      intro pre f r Gf hS hGf g hg G' hG'
      exact hs (Frame.init2 G k :: pre) f r Gf (by rw [hS]; simp) hGf g
        (List.mem_cons_of_mem _ hg) G' hG'
  | @inext H Γ S G e₁ e₂ k v₁ _ _ _ _ _ =>
      -- Swaps `init1 G e₂ k` for `init2 G k`: the head frame changes shape but
      -- records the *same* global, so the pre-step fact transfers verbatim.
      intro pre f r Gf hS hGf g hg G' hG'
      rcases pre with _ | ⟨p₀, pre'⟩
      · simp at hg
      · simp only [List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, hS⟩ := hS
        have hS2 : Frame.init1 G e₂ k :: S = (Frame.init1 G e₂ k :: pre') ++ f :: r := by
          rw [hS]; simp
        rcases List.mem_cons.mp hg with rfl | hg'
        · -- `g` is the new `init2 G k`; feed the old `init1 G e₂ k` instead
          exact hs _ f r Gf hS2 hGf (Frame.init1 G e₂ k) (by simp) G'
            (by simpa [Frame.glob] using hG')
        · exact hs _ f r Gf hS2 hGf g (List.mem_cons_of_mem _ hg') G' hG'
  | @ipush H Γ S E G i e₁ e₂ hobj _ _ _ _ =>
      intro pre f r Gf hS hGf g hg G₀ hG₀
      rcases pre with _ | ⟨p₀, pre'⟩
      · simp at hg
      · simp only [Stack.push, List.cons_append, List.cons.injEq] at hS
        obtain ⟨rfl, hS⟩ := hS
        rcases List.mem_cons.mp hg with rfl | hg'
        · -- `g` is the freshly pushed `init1 G …` frame, so `G₀ = G`, and the
          -- goal is `G ∈ Dep σ L Gf` for an arbitrary init frame `f` below it.
          simp only [Frame.glob, Option.some.injEq] at hG₀
          subst hG₀
          have hfS : f ∈ S := by rw [hS]; simp
          obtain ⟨it, cfs, rt, hti⟩ := Stack.hasInit_of_glob hfS hGf
          obtain ⟨Gt, hGt⟩ := Frame.glob_of_notCall (Stack.topInit_notCall hti)
          have htiG : Stack.TopInit S Gt := by
            intro i' cfs' r' h
            rw [hti] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -, -⟩ := h
            exact hGt
          -- `acc_implies_dep`: the focus `E.plug (G.i)` is reachable from the *topmost*
          -- init global `Gt`, so `G ∈ Dep(Gt)`.
          have haip : G ∈ Dep σ L Gt := acc_implies_dep hti htiG hinv hrinv
          -- and `f` is either that topmost frame, or below it — in which case
          -- `Gt ∈ Dep(Gf)` already, by the pre-step `StackDep`.
          rcases StackDep.topInit_dep hs hti hGt hS hGf with rfl | hdep
          · exact haip
          · exact DepJ.trans hdep haip
        · exact hs pre' f r Gf hS hGf g hg' G₀ hG₀

theorem stack_dep_star {L : Program} {σ : Sigma} {c c' : Config} (hσ : FixPoint σ L)
  (hinv : Inv σ L c) (hrinv : REInv σ L c) (hs : StackDep σ L c) (hstar : Star L c c') :
  StackDep σ L c' := by
  induction hstar with
  | refl => exact hs
  | head hstep _ ih =>
      exact ih (inv_preservation_step' hσ hinv hstep) (REInv.step' hσ hinv hrinv hstep)
        (stack_dep_step hinv hrinv hstep hs)

theorem stack_dep_run {L : Program} {σ : Sigma} {Gₘ : GlobName} {c : Config}
    (hσ : FixPoint σ L)
    (hstar : Star L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj Gₘ Idx.one)) c) :
    StackDep σ L c := by
  refine stack_dep_star hσ inv_empty REInv.empty ?_ hstar
  intro pre f r G hS
  cases pre <;> simp at hS

end Proof
