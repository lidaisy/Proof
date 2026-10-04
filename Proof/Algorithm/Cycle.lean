import Proof.Algorithm.Definition
import Proof.Algorithm.LessThanInv

namespace Algorithm

open Proof (Program GlobName Expr Idx Dep)

def StackDep (L : Program) : Config → Prop
  | c@(.mk G' _ _ S _) =>
      (∀ G ∈ S.globs, G' ∈ Dep c.all_data L G)
        ∧ ∀ aft G₀ bef, S.globs = aft ++ (G₀ :: bef) → ∀ G₁ ∈ aft, G₁ ∈ Dep c.all_data L G₀
  | .cycle _ => True
  | .done _ => True

theorem Config.all_data_grow {L : Program} {F : FixPoints} {G : GlobName} {σ σ' : State G}
    {S : Stack} {Q : Queue}
    (hwf : Config.WellFormed L (.mk G σ F S Q)) (hwf' : Config.WellFormed L (.mk G σ' F S Q))
    (hgrow : Grow L F G σ σ')
    : Config.all_data (.mk G σ F S Q) ≤ Config.all_data (.mk G σ' F S Q) := by
  have hgl := grow_le hgrow

  have hf : ∀ G' σfix, ¬G = G' → F G' = some σfix → Config.find (Config.mk G σ F S Q) G' = some σfix := by
    intro G' σfix heq hfix
    simp [Config.find, Config.fixpoints, hfix]
  have hf' : ∀ G' σfix, ¬G = G' → F G' = some σfix → Config.find (Config.mk G σ' F S Q) G' = some σfix := by
    intro G' σfix heq hfix
    simp [Config.find, Config.fixpoints, hfix]
  have hc : ∀ G', ¬G = G' → (Config.mk G σ F S Q).curState (G := G') = none := by
    intro G' heq
    simp [Config.curState, heq]
  have hc' : ∀ G', ¬G = G' → (Config.mk G σ' F S Q).curState (G := G') = none := by
    intro G' heq
    simp [Config.curState, heq]
  have hs : ∀ G' σstack, ¬G = G' → F G' = none → (Config.mk G σ F S Q).curState (G := G') = none →
    S.find G' = some σstack → Config.find (Config.mk G σ F S Q) G' = some σstack := by
    intro G' heq hfix hcur hstack
    simp [Config.find, Config.fixpoints, Config.stack, hcur, hstack]
  have hs' : ∀ G' σstack, ¬G = G' → F G' = none → (Config.mk G σ' F S Q).curState (G := G') = none →
    S.find G' = some σstack → Config.find (Config.mk G σ' F S Q) G' = some σstack := by
    intro G' heq hfix hcur hstack
    simp [Config.find, Config.fixpoints, Config.stack, hcur, hstack]
  have hn : ∀ G', ¬G = G' → F G' = none → (Config.mk G σ F S Q).curState (G := G') = none →
    S.find G' = none → Config.find (Config.mk G σ F S Q) G' = none := by
    intro G' heq hfix hcur hstack
    simp [Config.find, Config.fixpoints, Config.stack, hfix, hcur, hstack]
  have hn' : ∀ G', ¬G = G' → F G' = none → (Config.mk G σ' F S Q).curState (G := G') = none →
    S.find G' = none → Config.find (Config.mk G σ' F S Q) G' = none := by
    intro G' heq hfix hcur hstack
    simp [Config.find, Config.fixpoints, Config.stack, hfix, hcur, hstack]

  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G' C'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_param (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_param (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.1 C'
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_param (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_param (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_param (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_param (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.Param G' C' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.Param G' C' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G' C'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_fld₁ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_fld₁ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.2 C'
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_fld₁ (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_fld₁ (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_fld₁ (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_fld₁ (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.Fld₁ G' C' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.Fld₁ G' C' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G' C'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_fld₂ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_fld₂ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.3 C'
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_fld₂ (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_fld₂ (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_fld₂ (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_fld₂ (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.Fld₂ G' C' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.Fld₂ G' C' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G' C'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_ret (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_ret (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.4 C'
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_ret (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_ret (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_ret (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_ret (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.Ret G' C' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.Ret G' C' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_gfld₁ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_gfld₁ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.5
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_gfld₁ (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_gfld₁ (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_gfld₁ (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_gfld₁ (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.GFld₁ G' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.GFld₁ G' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_gfld₂ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_gfld₂ (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.6
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_gfld₂ (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_gfld₂ (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_gfld₂ (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_gfld₂ (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.GFld₂ G' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.GFld₂ G' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_rm (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_rm (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.7
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_rm (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_rm (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_rm (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_rm (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.RM G' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.RM G' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']
  · intro G' C'
    by_cases heq : G = G'
    · subst heq
      have h := (Config.mk G σ F S Q).all_data_this (Config.find_curState (by rfl) (by simp [Config.curState]) hwf)
      have h' := (Config.mk G σ' F S Q).all_data_this (Config.find_curState (by rfl) (by simp [Config.curState]) hwf')
      rw [h, h']
      exact hgl.8 C'
    · cases hfix : F G' with
      | some σfix =>
        have h := (Config.mk G σ F S Q).all_data_this (hf G' σfix heq hfix)
        have h' := (Config.mk G σ' F S Q).all_data_this (hf' G' σfix heq hfix)
        rw [h, h']
      | none =>
        cases hstack : S.find G' with
        | some σstack =>
          have h := (Config.mk G σ F S Q).all_data_this (hs G' σstack heq hfix (hc G' heq) hstack)
          have h' := (Config.mk G σ' F S Q).all_data_this (hs' G' σstack heq hfix (hc' G' heq) hstack)
          rw [h, h']
        | none =>
          have h : (Config.mk G σ F S Q).all_data.This G' C' = ∅ := by simp [Config.all_data, (hn G' heq hfix (hc G' heq) hstack)]
          have h' : (Config.mk G σ' F S Q).all_data.This G' C' = ∅ := by simp [Config.all_data, (hn' G' heq hfix (hc' G' heq) hstack)]
          rw [h, h']

theorem Config.stack_to_all {L : Program} {G G' : GlobName} {σ' : State G'} {σ : State G} {F : FixPoints} {ctx : Ctx}
    {E : Expr } {S : Stack} {Q : Queue} (h : RE G' σ' L ctx E) (hS : Stack.find S G' = some σ')
    (hwf : (Config.mk G σ F S Q).WellFormed L) (hne : G ≠ G')
    : Proof.RE (Config.mk G σ F S Q).all_data L G' ctx E := by
  induction h with
  | init₁ hobj => exact Proof.RE.init₁ hobj
  | init₂ hobj => exact Proof.RE.init₂ hobj
  | body hRM hcls =>
    have h : (Config.mk G σ F S Q).all_data.RM G' = σ'.RM := ((Config.mk G σ F S Q).all_data_rm (Config.find_curStack (L := L) (rfl) hwf hS hne))
    refine Proof.RE.body ?_ hcls
    rw [h]
    exact hRM
  | proj _ ih => exact Proof.RE.proj ih
  | newC₁ _ ih => exact Proof.RE.newC₁ ih
  | newC₂ _ ih => exact Proof.RE.newC₂ ih
  | app₁ _ ih => exact Proof.RE.app₁ ih
  | app₂ _ ih => exact Proof.RE.app₂ ih

theorem Config.all_data_suspend {L : Program} {F : FixPoints} {G G₀ : GlobName} {σ : State G}
    {S : Stack} {Q : Queue} {c : Ctx} {i : Idx} (hre : RE G σ L c (Expr.gproj G₀ i))
    (hneeds : Needs σ L F c (Expr.gproj G₀ i) G₀) (hne : G₀ ≠ G) (hnS : G₀ ∉ S.globs)
    : Config.all_data (.mk G σ F S Q) ≤
      Config.all_data (.mk G₀ (State.zero G₀) F (⟨G, σ⟩ :: S) (Q.remove G₀)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G' C'

    sorry
  · intro G' C'

    sorry
  · intro G' C'

    sorry
  · intro G' C'

    sorry
  · intro G'

    sorry
  · intro G'

    sorry
  · intro G'

    sorry
  · intro G' C'

    sorry

theorem Config.all_data_resume {L : Program} {G G₀ : GlobName} {σ₀ : State G₀} {σ : State G}
    {F : FixPoints} {S : Stack} {Q : Queue} (hS : Stable L F G σ)
    : Config.all_data (.mk G σ F (⟨G₀, σ₀⟩ :: S) Q) ≤
        Config.all_data (.mk G₀ σ₀ (F.insert G σ) S Q):= by
  -- from Stable get (∀ σ', Grow L F G σ σ' → σ' ≤ σ), so σ' = σ
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G' C'

    sorry
  · intro G' C'

    sorry
  · intro G' C'

    sorry
  · intro G' C'

    sorry
  · intro G'

    sorry
  · intro G'

    sorry
  · intro G'

    sorry
  · intro G' C'

    sorry

theorem stack_dep_step {c c' : Config} {L : Program}
    (hwf : Config.WellFormed L c) (hwf' : Config.WellFormed L c')
    (hstep : Solve L c c') (h : StackDep L c) : StackDep L c' := by
  cases hstep with
  | @step G σ σ' F S Q hg =>
      have hless := Config.all_data_grow (S := S) (Q := Q) hwf hwf' hg
      refine ⟨?_, ?_⟩
      · intro G' hG'
        have hDep := h.left G' hG'
        exact (less_than_imp_dep_less_than (G := G') (L := L) hless) hDep
      · intro aft G₀ bef hS G₁ hG₁
        have hDep := h.right aft G₀ bef hS G₁ hG₁
        exact (less_than_imp_dep_less_than (G := G₀) (L := L) hless) hDep
  | @suspend G G₀ σ F S Q c i hre hneeds hne hnS =>
      have hless := Config.all_data_suspend (Q := Q) hre hneeds hne hnS
      refine ⟨?_, ?_⟩
      · intro G' hG'
        have hRE_all := Config.stack_to_all (σ := (State.zero G₀)) (F := F) (S := (⟨G, σ⟩ :: S)) (Q := (Q.remove G₀)) hre (by simp [Stack.find]) hwf' hne
        have hDep : G₀ ∈ Proof.Dep (Config.mk G₀ (State.zero G₀) F (⟨G, σ⟩ :: S) (Q.remove G₀)).all_data L G := Proof.DepJ.direct hRE_all
        by_cases heq : G' = G
        · subst heq; exact hDep
        · have hG'inS : G' ∈ Stack.globs S := by
            simp [Stack.globs] at hG'
            simp [Stack.globs, List.mem_map]
            exact hG'.resolve_left heq
          have hStackDep_prev := h.left G' hG'inS
          have hStackDep := (less_than_imp_dep_less_than hless) hStackDep_prev
          exact Proof.DepJ.trans hStackDep hDep
      · intro aft G₂ bef hS G₁ hG₁
        by_cases heq : G₁ = G
        · subst heq
          cases aft with
          | nil => simp at hG₁
          | cons a as =>
              have htail : S.globs = as ++ (G₂ :: bef) := by
                simpa using (congrArg List.tail hS)
              have hG₂inS : G₂ ∈ S.globs := by
                rw [htail]
                exact List.mem_append.mpr (Or.inr (by simp))
              have hPrev := h.left G₂ hG₂inS
              exact (less_than_imp_dep_less_than (G := G₂) (L := L) hless) hPrev
        · cases aft with
          | nil => simp at hG₁
          | cons a as =>
              have htail : S.globs = as ++ (G₂ :: bef) := by
                simpa using (congrArg List.tail hS)
              have h' : G :: S.globs = a :: as ++ (G₂ :: bef) := by
                simpa [Stack.globs] using hS
              have hhead : G = a := by
                simpa using (congrArg List.head? h')
              have ha : a = G := by
                simpa [eq_comm] using hhead
              have hG₁a : G₁ ≠ a := by
                intro hEq
                apply heq
                simpa [ha] using hEq
              have hG₁' : G₁ ∈ as := by
                rcases List.mem_cons.mp hG₁ with hEq | hIn
                · exact False.elim (hG₁a hEq)
                · exact hIn
              have hPrev : G₁ ∈ Proof.Dep (Config.mk G σ F S Q).all_data L G₂ :=
                h.right as G₂ bef htail G₁ hG₁'
              exact (less_than_imp_dep_less_than (G := G₂) (L := L) hless) hPrev
  | cycle =>
      trivial
  | @resume G G' σ σ' F S Q hSt =>
      have hless := Config.all_data_resume (σ₀ := σ') (S := S) (Q := Q) hSt
      refine ⟨?_, ?_⟩
      · intro G₀ hG₀
        obtain ⟨aft, bef, hS⟩ := List.append_of_mem hG₀
        have hSplit :
            Stack.globs (⟨G', σ'⟩ :: S) = (G' :: aft) ++ (G₀ :: bef) := by
          change G' :: S.globs = _
          rw [hS]
          simp only [List.cons_append]
        have hStackDep_prev :
            G' ∈ Proof.Dep (Config.mk G σ F (⟨G', σ'⟩ :: S) Q).all_data L G₀ := by
          exact h.right (G' :: aft) G₀ bef hSplit G' (by simp)
        exact (less_than_imp_dep_less_than (G := G₀) (L := L) hless) hStackDep_prev
      · intro aft G₂ bef hS G₁ hG₁
        have hSplit :
            Stack.globs (⟨G', σ'⟩ :: S) = (G' :: aft) ++ (G₂ :: bef) := by
          change G' :: S.globs = _
          rw [hS]
          simp only [List.cons_append]
        have hStackDep_prev :
            G₁ ∈ Proof.Dep (Config.mk G σ F (⟨G', σ'⟩ :: S) Q).all_data L G₂ := by
          exact h.right (G' :: aft) G₂ bef hSplit G₁ (by simp [hG₁])
        exact (less_than_imp_dep_less_than (G := G₂) (L := L) hless) hStackDep_prev
  | next =>
      refine ⟨?_, ?_⟩
      · intro G' hG'
        trivial
      · intro aft Gₒ bef hS G₁ hG₁
        simp [Stack.globs] at hS
  -- | skip =>
  --     refine ⟨?_, ?_⟩
  --     · intro G' hG'
  --       trivial
  --     · intro aft Gₒ bef hS G₁ hG₁
  --       simp [Stack.globs] at hS
  | finish =>
      trivial

theorem stack_dep_star {c : Config} {L : Program} {hL : L.WellFormed}
    (hstar : Solve.Star L (Config.start L hL) c) :
    StackDep L c := by
  induction hstar with
  | refl =>
    refine ⟨?_, ?_⟩
    · intro G hG
      simp [Stack.globs] at hG
    · intro aft G bef hG _ _
      simp [Stack.globs] at hG
  | tail hprev hgrow ih =>
    exact stack_dep_step (config_wellformed hprev)
      (config_wellformed (Relation.ReflTransGen.tail hprev hgrow)) hgrow ih

theorem Config.state_to_all {L : Program} {hL : L.WellFormed} {G' G : GlobName} {σ' : State G'}
    {F : FixPoints} {ctx : Ctx} {S : Stack} {Q : Queue} {i : Idx}
    (hstar : Solve.Star L (Config.start L hL) (Config.mk G' σ' F S Q))
    (h : RE G' σ' L ctx (Expr.gproj G i))
    : Proof.RE (Config.mk G' σ' F S Q).all_data L G' ctx (Expr.gproj G i) := by
  exact re_bridge (Config.all_data_state hstar) h

theorem report_cycle_then_dep {L : Program} {hL : L.WellFormed} :
    ∀ G, Solve.Star L (Config.start L hL) (.cycle G) →
    ∀ σ : Proof.Sigma, Proof.FixPoint σ L → G ∈ Proof.Dep σ L G := by
  intro G hcyc σ hf
  obtain _ | ⟨h_star, h_step⟩ := hcyc
  rename_i c_prev
  rcases c_prev with ⟨ G', σ', F, S, Q ⟩ | F | G'
  · cases h_step with
    | cycle hSRE hneeds hG =>
      rename_i c i
      have hl := (less_than hL h_star) σ hf
      let c_prev := (Config.mk G' σ' F S Q)
      let c_prev_data := c_prev.all_data
      have hCRE : Proof.RE c_prev_data L G' c (Expr.gproj G i) := by
        simpa [c_prev, c_prev_data] using (Config.state_to_all h_star hSRE)
      have hCDep : G ∈ Proof.Dep c_prev_data L G' := Proof.DepJ.direct hCRE
      have hCCyc : G ∈ Proof.Dep c_prev_data L G := by
        rcases hG with hG' | hG'
        · subst hG'
          exact hCDep
        · have hADep : G' ∈ Proof.Dep c_prev_data L G := by
            exact (stack_dep_star h_star).left G hG'
          exact Proof.DepJ.trans hADep hCDep
      exact less_than_imp_dep_less_than hl hCCyc
  · cases h_step
  · cases h_step

end Algorithm
