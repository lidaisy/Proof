import Proof.Semantics
import Proof.Stack
import Proof.Analysis
import Proof.CorrectnessRelation

namespace Proof

inductive RRE (σ : Sigma) (L : Program) (G : GlobName) : Ctx → Expr → Prop
  | static {c e}      : RE σ L G c e → RRE σ L G c e
  | val {c v}         : RRE σ L G c (Expr.val v)
  | thisE {c}         : RRE σ L G c Expr.thisE
  | paramE {c}        : RRE σ L G c Expr.paramE
  | proj {c e i}      : RRE σ L G c e → RRE σ L G c (Expr.proj e i)
  | app {c e₁ e₂}     : RRE σ L G c e₁ → RRE σ L G c e₂ → RRE σ L G c (Expr.app e₁ e₂)
  | newC {c C e₁ e₂}  : RRE σ L G c e₁ → RRE σ L G c e₂ → RRE σ L G c (Expr.newC C e₁ e₂)

/-- Extraction: runtime reachability of a focus `E.plug e` yields runtime
    reachability of the plugged sub-expression `e`. The `RRE` analogue of
    `RE.plug`, but usable on real runtime foci (its hypothesis is inhabited,
    unlike the static `RE.plug`). Induction on `E`, inverting the upward
    constructors — the `static` layer is peeled with the `RE` congruences. -/
theorem RRE.plug {σ : Sigma} {L : Program} {G : GlobName} {c : Ctx} :
    ∀ (E : ECtx) {e : Expr}, RRE σ L G c (E.plug e) → RRE σ L G c e := by
  intro E
  induction E with
  | hole => intro e h; exact h
  | projc E i ih =>
    intro e h; simp only [ECtx.plug] at h
    cases h with
    | static hRE => exact ih (RRE.static (RE.proj hRE))
    | proj h₀ => exact ih h₀
  | appL E a ih =>
    intro e h; simp only [ECtx.plug] at h
    cases h with
    | static hRE => exact ih (RRE.static (RE.app₁ hRE))
    | app h₁ _ => exact ih h₁
  | appR v E ih =>
    intro e h; simp only [ECtx.plug] at h
    cases h with
    | static hRE => exact ih (RRE.static (RE.app₂ hRE))
    | app _ h₂ => exact ih h₂
  | newL C E a ih =>
    intro e h; simp only [ECtx.plug] at h
    cases h with
    | static hRE => exact ih (RRE.static (RE.newC₁ hRE))
    | newC h₁ _ => exact ih h₁
  | newR C v E ih =>
    intro e h; simp only [ECtx.plug] at h
    cases h with
    | static hRE => exact ih (RRE.static (RE.newC₂ hRE))
    | newC _ h₂ => exact ih h₂

/-- Replacement: reachability of `E.plug e` together with reachability of a
    fresh `e'` gives reachability of `E.plug e'`. This is the workhorse for
    **preservation** — a computational step rewrites the redex under a fixed
    context `E`, and the contractum (a value, or a reachable body) is `RRE`. -/
theorem RRE.plug_replace {σ : Sigma} {L : Program} {G : GlobName} {c : Ctx} :
    ∀ (E : ECtx) {e e' : Expr},
      RRE σ L G c (E.plug e) → RRE σ L G c e' → RRE σ L G c (E.plug e') := by
  intro E
  induction E with
  | hole => intro e e' _ h'; exact h'
  | projc E i ih =>
    intro e e' h h'; simp only [ECtx.plug] at h ⊢
    cases h with
    | static hRE => exact RRE.proj (ih (RRE.static (RE.proj hRE)) h')
    | proj h₀ => exact RRE.proj (ih h₀ h')
  | appL E a ih =>
    intro e e' h h'; simp only [ECtx.plug] at h ⊢
    cases h with
    | static hRE => exact RRE.app (ih (RRE.static (RE.app₁ hRE)) h') (RRE.static (RE.app₂ hRE))
    | app h₁ h₂ => exact RRE.app (ih h₁ h') h₂
  | appR v E ih =>
    intro e e' h h'; simp only [ECtx.plug] at h ⊢
    cases h with
    | static hRE => exact RRE.app (RRE.static (RE.app₁ hRE)) (ih (RRE.static (RE.app₂ hRE)) h')
    | app h₁ h₂ => exact RRE.app h₁ (ih h₂ h')
  | newL C E a ih =>
    intro e e' h h'; simp only [ECtx.plug] at h ⊢
    cases h with
    | static hRE => exact RRE.newC (ih (RRE.static (RE.newC₁ hRE)) h') (RRE.static (RE.newC₂ hRE))
    | newC h₁ h₂ => exact RRE.newC (ih h₁ h') h₂
  | newR C v E ih =>
    intro e e' h h'; simp only [ECtx.plug] at h ⊢
    cases h with
    | static hRE => exact RRE.newC (RRE.static (RE.newC₁ hRE)) (ih (RRE.static (RE.newC₂ hRE)) h')
    | newC h₁ h₂ => exact RRE.newC h₁ (ih h₂ h')

/-- Bridge to `Dep`: a runtime-reachable `gproj G' i` accesses `G'` directly, so
    `G' ∈ Dep σ L G`. The only `RRE` rule that can conclude a `gproj` is
    `static`, so this reduces to the static `DepJ.direct`. -/
theorem RRE.dep {σ : Sigma} {L : Program} {G : GlobName} {c : Ctx} {G' : GlobName} {i : Idx}
    (h : RRE σ L G c (Expr.gproj G' i)) : G' ∈ Dep σ L G := by
  cases h with
  | static hRE => exact DepJ.direct hRE

def RE.focus (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → Stack.TopInit S G →
    ((∀ t p κ Cl, S.topCall = some (Frame.call t p κ) → H t = some Cl → RRE σ L G Cl.cls e) ∧
    (S.topCall = none → RRE σ L G none e))

def RE.contCall (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ t p κ (S' : Stack), (Frame.call t p κ) :: S' <:+ S →
    RE.focus σ L H S' (κ.plug (Expr.app (Expr.val (Value.loc t)) (Expr.val p)))

def RE.contInit (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ G κ (S' : Stack), ((∃ e, Frame.init1 G e κ :: S' <:+ S) ∨ Frame.init2 G κ :: S' <:+ S) →
    RE.focus σ L H S' κ

def RE.pendInit (σ : Sigma) (L : Program) (S : Stack) : Prop :=
  ∀ G e κ (S' : Stack), Frame.init1 G e κ :: S' <:+ S → RRE σ L G none e

def REInv (σ : Sigma) (L : Program) : Config → Prop
  | .mk H _Γ S e =>
      RE.focus σ L H S e ∧
      RE.contCall σ L H S ∧
      RE.contInit σ L H S ∧
      RE.pendInit σ L S
  | .crash => True

theorem RE.focus.heap_update_fresh {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {e : Expr} {ℓ : Loc} {o : ClsIns}
    (hrm : RMInv σ H S) (hHl : H ℓ = none) (_hcl : Closed H e)
    (hfoc : RE.focus σ L H S e) :
    RE.focus σ L (H[ℓ ↦ o]) S e := by
  intro G i cfs r hti htiG
  obtain ⟨h1, h2⟩ := hfoc G i cfs r hti htiG
  -- the `topCall = none` branch never looks at the heap
  refine ⟨fun t p κ Cl htc hCt => h1 t p κ Cl htc ?_, h2⟩
  obtain ⟨D, hHt, -⟩ :=
    hrm S i cfs r (Frame.call t p κ) G t (List.suffix_refl _) hti htiG
      (Stack.topCall_mem_topInit htc hti) rfl
  have htl : t ≠ ℓ := by intro h; rw [h, hHl] at hHt; simp at hHt
  rwa [Heap.lookup_update_ne htl] at hCt

theorem RE.contCall.heap_update_fresh {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {ℓ : Loc} {o : ClsIns}
    (hrm : RMInv σ H S) (hHl : H ℓ = none) (hfc : FrameClosedInv H S)
    (hcc : RE.contCall σ L H S) :
    RE.contCall σ L (H[ℓ ↦ o]) S := by
  intro t p κ S' hsuf
  have hsuf' : S' <:+ S := (List.suffix_cons _ _).trans hsuf
  exact (hcc t p κ S' hsuf).heap_update_fresh
    (fun S'' i cfs r f G l hs => hrm S'' i cfs r f G l (hs.trans hsuf')) hHl
    (hfc S' t p κ hsuf)

theorem RE.contInit.heap_update_fresh {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {ℓ : Loc} {o : ClsIns}
    (hrm : RMInv σ H S) (hHl : H ℓ = none) (hifc : InitFrameClosedInv H S)
    (hci : RE.contInit σ L H S) :
    RE.contInit σ L (H[ℓ ↦ o]) S := by
  intro G κ S' hsuf
  have hsuf' : S' <:+ S := by
    rcases hsuf with ⟨_, hs⟩ | hs <;> exact (List.suffix_cons _ _).trans hs
  exact (hci G κ S' hsuf).heap_update_fresh
    (fun S'' i cfs r f G' l hs => hrm S'' i cfs r f G' l (hs.trans hsuf')) hHl
    (hifc S' G κ hsuf)

/-! ### Per-step preservation lemmas for `REInv` -/

theorem reinv_step_this {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {t : Loc} (hinv : REInv σ L (.mk H Γ S (E.plug Expr.thisE))) :
    REInv σ L (.mk H Γ S (E.plug (Expr.val (Value.loc t)))) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, hcc, hci, hpi⟩
  intro G' i cfs r hti hTop
  obtain ⟨h1, h2⟩ := hf G' i cfs r hti hTop
  exact ⟨fun t' p' κ' Cl htc' hCt' => RRE.plug_replace E (h1 t' p' κ' Cl htc' hCt') RRE.val,
    fun htcNone => RRE.plug_replace E (h2 htcNone) RRE.val⟩

theorem reinv_step_param {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {p : Value} (hinv : REInv σ L (.mk H Γ S (E.plug Expr.paramE))) :
    REInv σ L (.mk H Γ S (E.plug (Expr.val p))) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, hcc, hci, hpi⟩
  intro G' i cfs r hti hTop
  obtain ⟨h1, h2⟩ := hf G' i cfs r hti hTop
  exact ⟨fun t' p' κ' Cl htc' hCt' => RRE.plug_replace E (h1 t' p' κ' Cl htc' hCt') RRE.val,
    fun htcNone => RRE.plug_replace E (h2 htcNone) RRE.val⟩

theorem reinv_step_proj {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {ℓ : Loc} {C : ClassName} {v₁ v₂ : Value} {i : Idx} {G : GlobName}
    (hinv : REInv σ L (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))) :
    REInv σ L (.mk H Γ S (E.plug (Expr.val ((ClsIns.mk C G v₁ v₂).field i)))) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, hcc, hci, hpi⟩
  intro G' i cfs r hti hTop
  obtain ⟨h1, h2⟩ := hf G' i cfs r hti hTop
  exact ⟨fun t' p' κ' Cl htc' hCt' => RRE.plug_replace E (h1 t' p' κ' Cl htc' hCt') RRE.val,
    fun htcNone => RRE.plug_replace E (h2 htcNone) RRE.val⟩

theorem reinv_step_gproj {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {G : GlobName} {i : Idx} {v : Value}
    (hinv : REInv σ L (.mk H Γ S (E.plug (Expr.gproj G i)))) :
    REInv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, hcc, hci, hpi⟩
  intro G' i cfs r hti hTop
  obtain ⟨h1, h2⟩ := hf G' i cfs r hti hTop
  exact ⟨fun t' p' κ' Cl htc' hCt' => RRE.plug_replace E (h1 t' p' κ' Cl htc' hCt') RRE.val,
    fun htcNone => RRE.plug_replace E (h2 htcNone) RRE.val⟩

theorem reinv_step_methCall {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {ℓ : Loc} {o : ClsIns} {v : Value} {body : Expr}
    (hHl : H ℓ = some o) (hbody : Program.HasClass L o.cls body)
    (hinv : REInv σ L (.mk H Γ S (E.plug (Expr.app (Expr.val (Value.loc ℓ)) (Expr.val v)))))
    (hin : Inv σ L (.mk H Γ (Stack.push (Frame.call ℓ v E) S) body)):
    REInv σ L (.mk H Γ (Stack.push (Frame.call ℓ v E) S) body) := by
  obtain ⟨-, -, -, -, -, -, hrm, -⟩ := hin
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Focus
    intro G' i cfs r hti' hTop
    refine ⟨?_, ?_⟩
    · -- topCall = some
      intro t' p' κ' Cl htcSome hCt
      show RRE σ L G' Cl.cls body
      have hmem : Frame.call t' p' κ' ∈ cfs := Stack.topCall_mem_topInit htcSome hti'
      obtain ⟨D, hHt, hRM⟩ :=
        hrm _ i cfs r (Frame.call t' p' κ') G' t' (List.suffix_refl _) hti' hTop hmem rfl
      rw [hCt, Option.some.injEq] at hHt
      subst hHt
      -- The pushed frame *is* the top call frame, so `t' = ℓ` and hence `Cl = o`:
      -- the receiver is the object `hbody` gives a method body for.
      simp only [Stack.push, Stack.topCall, Option.some.injEq, Frame.call.injEq] at htcSome
      obtain ⟨rfl, rfl, rfl⟩ := htcSome
      rw [hHl, Option.some.injEq] at hCt
      subst hCt
      exact RRE.static (RE.body hRM hbody)
    · intro htcNone
      simp only [Stack.push, Stack.topCall, reduceCtorEq] at htcNone
  · -- ContCall
    intro t₁ p₁ κ₁ S' hsuf
    rcases List.suffix_cons_iff.mp hsuf with heq | hs
    · -- The suffix *is* the freshly pushed frame `call ℓ v E :: S`, so `S' = S`
      -- and its stored continuation `E.plug (ℓ v)` is exactly the pre-step
      -- focus.  Its `RE.focus` for `S` is `hf` verbatim — no receiver-class
      -- soundness needed.
      simp only [List.cons.injEq, Frame.call.injEq] at heq
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
      exact hf
    · -- The suffix already lives inside `S`: discharge directly with `hcc`.
      exact hcc t₁ p₁ κ₁ S' hs
  · -- ContInit: the pushed frame is a `call` frame, so every init frame of the
    -- new stack already lives in `S` — discharge directly with `hci`.
    intro G₁ κ₁ S' hsuf
    rcases hsuf with ⟨e, hs1⟩ | hs2
    · rcases List.suffix_cons_iff.mp hs1 with heq | hs
      · simp only [List.cons.injEq, reduceCtorEq, false_and] at heq
      · exact hci G₁ κ₁ S' (Or.inl ⟨e, hs⟩)
    · rcases List.suffix_cons_iff.mp hs2 with heq | hs
      · simp only [List.cons.injEq, reduceCtorEq, false_and] at heq
      · exact hci G₁ κ₁ S' (Or.inr hs)
  · -- PendInit
    intro G₁ e κ₁ S' hsuf
    rcases List.suffix_cons_iff.mp hsuf with heq | hs
    · simp only [List.cons.injEq, reduceCtorEq, false_and] at heq
    · exact hpi G₁ e κ₁ S' hs

theorem reinv_step_ret {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {κ : ECtx} {t : Loc} {p v : Value}
    (hinv : REInv σ L (.mk H Γ ((Frame.call t p κ)::S) (Expr.val v))) :
    REInv σ L (.mk H Γ S (κ.plug (Expr.val v))) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Focus
    intro G' i cfs r hti htiG'
    have hκ : RE.focus σ L H S (κ.plug (Expr.app (Expr.val (Value.loc t)) (Expr.val p))) :=
      hcc t p κ S (List.suffix_refl _)
    obtain ⟨h1, h2⟩ := hκ G' i cfs r hti htiG'
    exact ⟨fun t₁ p₁ κ₁ D htcSome ht₁D => RRE.plug_replace κ (h1 t₁ p₁ κ₁ D htcSome ht₁D) RRE.val,
      fun htcNone => RRE.plug_replace κ (h2 htcNone) RRE.val⟩
  · -- ContCall
    intro t₁ p₁ κ₁ S' hsuf
    exact hcc t₁ p₁ κ₁ S' (hsuf.trans (List.suffix_cons _ _))
  · -- ContInit
    intro G' κ₁ S' hsuf
    refine hci G' κ₁ S' ?_
    rcases hsuf with ⟨e, hs⟩ | hs
    · exact Or.inl ⟨e, hs.trans (List.suffix_cons _ _)⟩
    · exact Or.inr (hs.trans (List.suffix_cons _ _))
  · -- PendInit: the popped frame is a `call` frame, so the surviving `init1`
    -- frames are the pre-step ones.
    intro G' e κ₁ S' hsuf
    exact hpi G' e κ₁ S' (hsuf.trans (List.suffix_cons _ _))

theorem reinv_step_alloc {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {C : ClassName} {v₁ v₂ : Value} {ℓ : Loc} {G : GlobName}
    (hHl : H ℓ = none)
    (hi : Inv σ L (.mk H Γ S (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂)))))
    (hinv : REInv σ L (.mk H Γ S (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂))))) :
    REInv σ L (.mk (H[ℓ ↦ ⟨C, G, v₁, v₂⟩]) Γ S (E.plug (Expr.val (Value.loc ℓ)))) := by
  obtain ⟨-, -, -, -, -, -, hrm, -, -, -, -, hcl, hfc, hifc⟩ := hi
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, hcc.heap_update_fresh hrm hHl hfc, hci.heap_update_fresh hrm hHl hifc, hpi⟩
  intro G' i' cfs' r' hti' htiG'
  have hf' : RE.focus σ L (H[ℓ ↦ ⟨C, G, v₁, v₂⟩]) S
      (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂))) :=
    hf.heap_update_fresh hrm hHl hcl
  obtain ⟨h1, h2⟩ := hf' G' i' cfs' r' hti' htiG'
  exact ⟨fun t p κ Cl htc hCt => RRE.plug_replace E (h1 t p κ Cl htc hCt) RRE.val,
    fun htcNone => RRE.plug_replace E (h2 htcNone) RRE.val⟩

theorem reinv_step_ipush {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {E : ECtx} {G : GlobName} {i : Idx} {e₁ e₂ : Expr}
    (hobj : Program.HasObject L G e₁ e₂)
    (hinv : REInv σ L (.mk H Γ S (E.plug (Expr.gproj G i)))) :
    REInv σ L (.mk H (Γ[G↦ ⟨none, none⟩])
      (Stack.push (Frame.init1 G e₂ (E.plug (Expr.gproj G i))) S) e₁) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Focus
    intro G' i' cfs r hti htiG'
    have hGG : G = G' := by
      have hgl := htiG' (Frame.init1 G e₂ (E.plug (Expr.gproj G i))) List.nil S
        (by simp [Stack.push, Stack.topInit])
      simpa [Frame.glob] using hgl
    subst hGG
    refine ⟨fun _ _ _ _ htc _ => absurd htc (by simp [Stack.push, Stack.topCall]), fun _ => ?_⟩
    exact RRE.static (RE.init₁ hobj)
  · -- ContCall
    intro t p κ S' hsuf
    rcases List.suffix_cons_iff.mp hsuf with heq | hs
    · exact absurd heq (by simp)
    · exact hcc t p κ S' hs
  · -- ContInit
    intro G₁ κ₁ S' hsuf
    rcases hsuf with ⟨e, hs1⟩ | hs2
    · rcases List.suffix_cons_iff.mp hs1 with heq | hs
      · simp only [List.cons.injEq, Frame.init1.injEq] at heq
        obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
        exact hf
      · exact hci G₁ κ₁ S' (Or.inl ⟨e, hs⟩)
    · rcases List.suffix_cons_iff.mp hs2 with heq | hs
      · exact absurd heq (by simp)
      · exact hci G₁ κ₁ S' (Or.inr hs)
  · -- PendInit: seeding place
    intro G₁ e κ₁ S' hsuf
    rcases List.suffix_cons_iff.mp hsuf with heq | hs
    · simp only [List.cons.injEq, Frame.init1.injEq] at heq
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := heq
      exact RRE.static (RE.init₂ hobj)
    · exact hpi G₁ e κ₁ S' hs

theorem reinv_step_inext {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {G : GlobName} {e₂ k : Expr} {v₁ : Value}
    (hinv : REInv σ L (.mk H Γ (Frame.init1 G e₂ k :: S) (Expr.val v₁))) :
    REInv σ L (.mk H (Γ[G↦ ⟨some v₁, none⟩]) (Frame.init2 G k :: S) e₂) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- Focus
    intro G' i' cfs r hti htiG'
    have hGG : G = G' := by
      have hgl := htiG' (Frame.init2 G k) List.nil S (by simp [Stack.topInit])
      simpa [Frame.glob] using hgl
    subst hGG
    exact ⟨fun _ _ _ _ htc _ => absurd htc (by simp [Stack.topCall]),
      fun _ => hpi G e₂ k S (List.suffix_refl _)⟩
  · -- ContCall
    intro t p κ S' hsuf
    rcases List.suffix_cons_iff.mp hsuf with heq | hs
    · exact absurd heq (by simp)
    · exact hcc t p κ S' (hs.trans (List.suffix_cons _ _))
  · -- ContInit
    intro G₁ κ₁ S' hsuf
    rcases hsuf with ⟨e, hs1⟩ | hs2
    · rcases List.suffix_cons_iff.mp hs1 with heq | hs
      · exact absurd heq (by simp)
      · exact hci G₁ κ₁ S' (Or.inl ⟨e, (hs.trans (List.suffix_cons _ _))⟩)
    · rcases List.suffix_cons_iff.mp hs2 with heq | hs
      · simp only [List.cons.injEq, Frame.init2.injEq] at heq
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := heq
        exact hci _ _ _ (Or.inl ⟨e₂, List.suffix_refl _⟩)
      · exact hci G₁ κ₁ S' (Or.inr (hs.trans (List.suffix_cons _ _)))
  · -- PendInit
    intro G₁ e κ₁ S' hsuf
    rcases List.suffix_cons_iff.mp hsuf with heq | hs
    · exact absurd heq (by simp)
    · exact hpi G₁ e κ₁ S' (hs.trans (List.suffix_cons _ _))

theorem reinv_step_ipop {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack}
    {G : GlobName} {k : Expr} {v₁ v₂ : Value}
    (hinv : REInv σ L (.mk H Γ (Frame.init2 G k :: S) (Expr.val v₂))) :
    REInv σ L (.mk H (Γ[G↦ ⟨some v₁, some v₂⟩]) S k) := by
  obtain ⟨hf, hcc, hci, hpi⟩ := hinv
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hci _ _ _ (Or.inr (List.suffix_refl _))
  · intro t p κ S' hsuf
    exact hcc t p κ S' (hsuf.trans (List.suffix_cons _ _))
  · intro G₁ κ₁ S' hsuf
    rcases hsuf with ⟨e, hs1⟩ | hs2
    · exact hci G₁ κ₁ S' (Or.inl ⟨e, (hs1.trans (List.suffix_cons _ _))⟩)
    · exact hci G₁ κ₁ S' (Or.inr (hs2.trans (List.suffix_cons _ _)))
  · intro G₁ e κ₁ S' hsuf
    exact hpi G₁ e κ₁ S' (hsuf.trans (List.suffix_cons _ _))

theorem REInv.step {σ : Sigma} {L : Program} {H H' : Heap}
  {Γ Γ' : GTable} {S S': Stack} {e e' : Expr} (hσ : FixPoint σ L) (hi : Inv σ L (.mk H Γ S e))
  (hinv : REInv σ L (.mk H Γ S e)) (hstep : Step L (.mk H Γ S e) (.mk H' Γ' S' e'))
  : REInv σ L (.mk H' Γ' S' e') := by
    cases hstep with
    | this _                      => exact reinv_step_this hinv
    | param _                     => exact reinv_step_param hinv
    | proj _                      => exact reinv_step_proj hinv
    | gproj _ _                   => exact reinv_step_gproj hinv
    | methCall hHi hG hHl hcls hbody =>
        exact reinv_step_methCall hHl hcls hinv (inv_step_app hHi hG hHl hcls hbody hσ hi)
    | ret                         => exact reinv_step_ret hinv
    | newAlloc _ _ _ hHl          => exact reinv_step_alloc hHl hi hinv
    | ipush hobj _                => exact reinv_step_ipush hobj hinv
    | inext _                     => exact reinv_step_inext hinv
    | ipop _                      => exact reinv_step_ipop hinv

theorem REInv.step' {L : Program} {σ : Sigma} {c c' : Config} (hσ : FixPoint σ L)
   (hinv : Inv σ L c) (hrinv : REInv σ L c) (hstep : Step L c c') : REInv σ L c' := by
  cases c with
  | crash => cases hstep
  | mk H Γ S e =>
    cases c' with
    | crash => trivial
    | mk H' Γ' S' e' => exact REInv.step hσ hinv hrinv hstep

theorem REInv.star {L : Program} {σ : Sigma} {c c' : Config}
    (hσ : FixPoint σ L) (hstar : Star L c c') (hinv : Inv σ L c) (hrinv : REInv σ L c) : REInv σ L c' := by
  induction hstar with
  | refl => exact hrinv
  | head hstep _ ih => exact ih (inv_preservation_step' hσ hinv hstep) (REInv.step' hσ hinv hrinv hstep)

/-- `REInv` holds at the initial configuration: the stack is empty, so it has no
    topmost `init` frame (`RE.focus` is vacuous) and no frame at all for the
    three continuation components to quantify over (a `cons` is never a suffix
    of `[]`). -/
theorem REInv.empty {σ : Sigma} {L : Program} {G : GlobName} :
    REInv σ L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj G Idx.one)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro G' i cfs r hti
    simp [Stack.topInit] at hti
  · intro t p κ S' hsuf
    simp at hsuf
  · intro G' κ S' hsuf
    rcases hsuf with ⟨e, hs⟩ | hs <;> simp at hs
  · intro G' e κ S' hsuf
    simp at hsuf

theorem REInv.preservation {G : GlobName} {L : Program} {S : Stack}
    {σ : Sigma} {H : Heap} {Γ : GTable} {e : Expr}
    (hσ : FixPoint σ L)
    (hstar : Star L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj G Idx.one)) (.mk H Γ S e)) :
    REInv σ L (.mk H Γ S e) := by
  have hinv : Inv σ L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj G Idx.one)) := inv_empty
  exact REInv.star hσ hstar hinv REInv.empty

end Proof
