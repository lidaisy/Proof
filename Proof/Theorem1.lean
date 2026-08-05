import Mathlib.Tactic.Set
import Proof.Semantics
import Proof.Analysis
import Proof.CorrectnessRelation

namespace Proof

def PartialOnStack : Config → Prop
  | .mk _ Γ S _ =>
      ∀ G u₁ u₂, Γ G = some ⟨u₁, u₂⟩ → (u₁ = none ∨ u₂ = none) → inGlobals G S
  | .crash => True

theorem partial_step {c c': Config} {L : Program}
    (hstep : Step L c c') (h : PartialOnStack c)
    : PartialOnStack c' := by
  cases hstep with
  | @ipush H Γ S E G i e₁ e₂ hobj hΓ _ _ _ =>
      have h : PartialOnStack (.mk H Γ S (E.plug (Expr.gproj G i))) := h
      set Γ' : GTable := Γ[G ↦ ⟨none, none⟩] with hΓ'
      set S' : Stack := Stack.push (Frame.init1 G e₂ (E.plug (Expr.gproj G i))) S with hS'
      simp only [PartialOnStack] at h ⊢
      intro G₀ v₁ v₂ hG₀ hnone
      rw [hΓ'] at hG₀
      rw [hS']
      by_cases hGG : G₀ = G
      · subst hGG
        exact ⟨Frame.init1 G₀ e₂ (E.plug (Expr.gproj G₀ i)), by simp [Stack.push], rfl⟩
      · have hΓG₀ : Γ G₀ = some ⟨v₁, v₂⟩ := by
          simpa [GTable.update, hGG] using hG₀
        obtain ⟨f, hf, hfg⟩ := h G₀ v₁ v₂ hΓG₀ hnone
        exact ⟨f, by simp [Stack.push, hf], hfg⟩
  | @inext H Γ S G e₁ e₂ k v₁ hobj hG _ _ _ =>
      have h : PartialOnStack (.mk H Γ (Frame.init1 G e₂ k :: S) (Expr.val v₁)) := h
      set Γ' : GTable := Γ[G ↦ ⟨some v₁, none⟩] with hΓ'
      set S' : Stack := (Frame.init2 G k :: S) with hS'
      simp only [PartialOnStack] at h ⊢
      intro G₀ v₁ v₂ hG₀ hnone
      rw [hΓ'] at hG₀
      rw [hS']
      by_cases hGG : G₀ = G
      · subst hGG
        exact ⟨Frame.init2 G₀ k, by simp, rfl⟩
      · have hΓG₀ : Γ G₀ = some ⟨v₁, v₂⟩ := by
          simpa [GTable.update, hGG] using hG₀
        obtain ⟨f, hf, hfg⟩ := h G₀ v₁ v₂ hΓG₀ hnone
        rcases List.mem_cons.mp hf with rfl | hfS
        · simp only [Frame.glob, Option.some.injEq] at hfg
          exact absurd hfg.symm hGG
        · exact ⟨f, List.mem_cons_of_mem _ hfS, hfg⟩
  | @ipop H Γ S G e₁ e₂ k v₁ v₂ hobj hG =>
      have h : PartialOnStack (.mk H Γ (Frame.init2 G k :: S) (Expr.val v₂)) := h
      set Γ' : GTable := Γ[G ↦ ⟨some v₁, some v₂⟩] with hΓ'
      set S' : Stack := S with hS'
      simp only [PartialOnStack] at h ⊢
      intro G₀ w₁ w₂ hG₀ hnone
      rw [hΓ'] at hG₀
      rw [hS']
      by_cases hGG : G₀ = G
      · subst hGG
        exfalso
        simp only [GTable.update] at hG₀
        rcases hnone with rfl | rfl <;> simp at hG₀
      · have hΓG₀ : Γ G₀ = some ⟨w₁, w₂⟩ := by
          simpa [GTable.update, hGG] using hG₀
        obtain ⟨f, hf, hfg⟩ := h G₀ w₁ w₂ hΓG₀ hnone
        rcases List.mem_cons.mp hf with rfl | hfS
        · simp only [Frame.glob, Option.some.injEq] at hfg
          exact absurd hfg.symm hGG
        · exact ⟨f, hfS, hfg⟩
  | uninit _ _ => trivial
  | methCall _ _ _ _ _ =>
      simp only [PartialOnStack] at h ⊢
      intro G₀ w₁ w₂ hG₀ hnone
      obtain ⟨f, hf, hfg⟩ := h G₀ w₁ w₂ hG₀ hnone
      exact ⟨f, by simp [Stack.push, hf], hfg⟩
  | ret _ =>
      simp only [PartialOnStack] at h ⊢
      intro G₀ w₁ w₂ hG₀ hnone
      obtain ⟨f, hf, hfg⟩ := h G₀ w₁ w₂ hG₀ hnone
      rcases List.mem_cons.mp hf with rfl | hfS
      · simp only [Frame.glob, reduceCtorEq] at hfg
      · exact ⟨f, hfS, hfg⟩
  | _ => exact h

theorem partial_star {c c': Config} {L : Program}
    (hrun : Star L c c') (h : PartialOnStack c)
    : PartialOnStack c' := by
  induction hrun with
  | refl => exact h
  | @head c c' c'' hstep hrest ih =>
    cases c with
      | crash => cases hstep
      | mk H Γ S e =>
      cases c' with
        | crash =>
            cases hrest with
            | refl => trivial
            | head hs _ => cases hs
        | mk H₁ Γ₁ S₁ e₁ => exact ih (partial_step hstep h)

theorem partially_init_obj_on_stack1 {Γ : GTable} {Gₘ: GlobName}
    {H : Heap} {S : Stack} {e : Expr} {L : Program}
    (hrun : Star L
      (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj Gₘ Idx.one))
      (.mk H Γ S e))
    : ∀ G u₁ u₂, Γ G = (GEntry.mk u₁ u₂) → u₁ = none ∨ u₂ = none → inGlobals G S := by
  intro G u₁ u₂ hG hnone
  have hinit: PartialOnStack (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj Gₘ Idx.one)) := by
    intro G₀ w₁ w₂ hG₀ _
    simp at hG₀
  exact (partial_star hrun hinit) G u₁ u₂ hG hnone

end Proof
