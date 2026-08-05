import Proof.Semantics
import Proof.Analysis
import Proof.CorrectnessRelation

namespace Proof

-- /-- Reachability propagates down an evaluation context: if the whole focus
--     `E.plug e` is reachable from `G`, then so is the plugged sub-expression `e`.
--     Proved by induction on `E`, discharging each frame with the matching `RE`
--     congruence constructor (`proj` / `app₁` / `app₂` / `newC₁` / `newC₂`). -/
-- theorem RE.plug {σ : Sigma} {L : Program} {G : GlobName} {c : Ctx} :
--     ∀ (E : ECtx) {e : Expr}, RE σ L G c (E.plug e) → RE σ L G c e
--   | .hole,        _, h => h
--   | .projc E _,   _, h => RE.plug E (RE.proj h)
--   | .appL E _,    _, h => RE.plug E (RE.app₁ h)
--   | .appR _ E,    _, h => RE.plug E (RE.app₂ h)
--   | .newL _ E _,  _, h => RE.plug E (RE.newC₁ h)
--   | .newR _ _ E,  _, h => RE.plug E (RE.newC₂ h)

/-- Runtime reachability: the runtime analogue of `RE`. Where `RE` is purely
    static, `RRE` additionally admits the runtime leaves produced by reduction
    (values, `this`, `param`) and is closed *upward* under the term
    constructors, so an actual runtime focus (a reduct of a reachable static
    expression, with values sitting in evaluation position) genuinely inhabits
    it. Crucially there is **no** rule concluding a `gproj` other than `static`,
    so a runtime-reachable `gproj` still traces back to a static `RE` fact
    (see `RRE.dep`). Mirrors how `KJR` handles runtime expressions. -/
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

/-- The focus is runtime-reachable from the global `G` pinned by the topmost
    `init` frame, in the context induced by the topmost `call` frame (if any).

    The receiver data `t p κ Cl` is quantified *inside* the `topCall = some`
    branch, not over the whole conjunction: the `topCall = none` branch does not
    mention it, so hoisting it outward would force every consumer of that branch
    to invent dummy witnesses (`Loc`, `Value`, `ECtx`, `ClsIns` have no
    `Inhabited` instances) just to instantiate binders the statement ignores. -/
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

/-- The `init1` analogue of `RE.contInit` for the *pending* second initializer:
    the expression `e` parked in an `init1 G e κ` frame is reachable from that
    frame's own global `G`, in the empty context. Unlike a stored continuation,
    `e` is not a reduct of the current focus, so it cannot be recovered from
    `RE.focus`; `ipush` seeds it from `RE.init₂` and `inext` consumes it when it
    swaps the frame to `init2` and makes `e` the focus. -/
def RE.pendInit (σ : Sigma) (L : Program) (S : Stack) : Prop :=
  ∀ G e κ (S' : Stack), Frame.init1 G e κ :: S' <:+ S → RRE σ L G none e

/-- The config invariant that will supply runtime-reachability of the focus.
    For the top `init` global `G` and the context `c` induced by the enclosing
    call frames, the focus is `RRE`-reachable, and so is every saved
    continuation stored in an `init`/`call` frame (needed so that `ret` / `ipop`
    / `inext`, which resume a continuation, preserve the invariant).

    NB: unlike the earlier `REInvStep`, both `G` and `c` are read off the stack
    rather than held fixed — `methCall` enters context `some C` (via `RE.body`,
    `C ∈ RM G`) and `ipush` switches to a fresh global's initializer.
    Preservation is proved per `Step` rule: `RRE.plug_replace` for the
    computational rules, `RRE.static ∘ RE.body` for `methCall`, and the saved
    continuations for the frame push/pop rules. -/
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
  {Γ Γ' : GTable} {S S': Stack} {e e' : Expr} (hi : Inv σ L (.mk H Γ S e)) (hin : Inv σ L (.mk H' Γ' S' e'))
  (hstep : Step L (.mk H Γ S e) (.mk H' Γ' S' e')) (hinv : REInv σ L (.mk H Γ S e))
  : REInv σ L (.mk H' Γ' S' e') := by
    cases hstep with
    | this _                      => exact reinv_step_this hinv
    | param _                     => exact reinv_step_param hinv
    | proj _                      => exact reinv_step_proj hinv
    | gproj _ _                   => exact reinv_step_gproj hinv
    | methCall _ _ hHl hcls hbody => exact reinv_step_methCall hHl hcls hinv hin
    | ret                         => exact reinv_step_ret hinv
    | newAlloc _ _ _ hHl          => exact reinv_step_alloc hHl hi hinv
    | ipush hobj _                => exact reinv_step_ipush hobj hinv
    | inext _                     => exact reinv_step_inext hinv
    | ipop _                      => exact reinv_step_ipop hinv

/-- No call frames above the topmost `init` frame means no `topCall`: `topInit`
    collects *every* `call` frame it walks past into `cfs`, so an empty `cfs`
    forces the head of the stack to be the init frame itself. Dual to
    `Stack.topCall_mem_topInit`, which turns a `topCall` into membership in
    `cfs`. -/
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

/-- Dually, a nonempty `cfs` means there *is* a `topCall`: `topInit` only grows
    `cfs` by walking past a `call` frame at the head of the stack, and that head
    is exactly what `topCall` reports. Converse of
    `Stack.topCall_eq_none_of_topInit_nil`. -/
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

theorem wrong {L : Program} {G G': GlobName} {S cfs r : Stack}
  {σ : Sigma} {E : ECtx} {H : Heap} {Γ : GTable} {i : Idx} {ifr : Frame}
  (hti : S.topInit = some (ifr, cfs, r)) (htiG : Stack.TopInit S G)
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

/-! ### Multi-step version: `access_implies_dep`

  `wrong` is a *single-configuration* statement: it reads the accessed global
  off the focus of one config, against the global pinned by that config's own
  topmost `init` frame.  To run it at the end of an execution
  `⟨H,Γ,S,eᵢ⟩ →* ⟨H',Γ',S',E[G'.j]⟩` we must transport two things along the run:

    * `Inv` and `REInv` — `REInv.step` does the second, given the first at both
      ends of each step (`hpres` below supplies it: the repo proves the
      per-rule `inv_step_*` lemmas but has no aggregated subject-reduction
      theorem yet, so preservation of `Inv` is taken as a hypothesis);
    * the *pinned global*: `wrong` at the last config talks about the top-init
      global `G₂` of `S'`, not about the `G` we started in.  Every `ipush`
      changes that global, so the run must carry the fact that the current
      pinned global is `G` or one of its dependencies — this is
      `Stack.DepChain`, and re-establishing it at an `ipush` is exactly one
      application of `wrong` at the pre-state (the pushed global is read off
      the focus `E[G₀.i]`), followed by `Dep.trans`.

  `Stack.DepChain` cannot survive the `ipop` that pops `G`'s *own* init frame:
  once `G`'s initialization has returned, the resumed continuation belongs to
  the enclosing global `G_p`, and the globals it accesses lie in `Dep(G_p)`,
  which is strictly larger than `Dep(G)`.  So the run has to be confined to
  `G`'s initialization; `hstay` below states that confinement (`G`'s init
  frame, in whatever `init1`/`init2` shape, is still on the stack with the
  original frames `r` below it), and it is the only place the confinement is
  used: it rules out the offending `ipop`. -/

/-- `G`'s init frame is still live: the stack is `pre ++ f :: r` with `f` the
    frame that records `G` and `r` the frames that sat below it at the start of
    the run.  (`inext` swaps `init1 G e k` for `init2 G k`, so the frame itself
    changes shape during the run — only its `glob` is stable, which is why this
    is not phrased as `S₀ <:+ S`.) -/
def Stack.InsideInit (G : GlobName) (r S : Stack) : Prop :=
  ∃ pre f, S = pre ++ f :: r ∧ f.glob = some G

/-- `Stack.InsideInit` plus: every frame *above* `G`'s init frame records a
    global that `G` depends on.  Consequently the stack's topmost init frame —
    which is either one of those frames or `G`'s own — pins a global in
    `{G} ∪ Dep(G)` (`Stack.DepChain.top`). -/
def Stack.DepChain (σ : Sigma) (L : Program) (G : GlobName) (r S : Stack) : Prop :=
  ∃ pre f, S = pre ++ f :: r ∧ f.glob = some G ∧
    ∀ g ∈ pre, ∀ G₀, g.glob = some G₀ → G₀ ∈ Dep σ L G

/-- `topInit` really is a decomposition: it splits `S` as `cfs ++ i :: r`, and
    the frames it walks past are `call` frames, which record no global. -/
theorem Stack.topInit_decomp : ∀ {S : Stack} {i : Frame} {cfs r : Stack},
    S.topInit = some (i, cfs, r) → S = cfs ++ i :: r ∧ ∀ g ∈ cfs, g.glob = none := by
  intro S
  induction S with
  | nil => intro i cfs r h; simp [Stack.topInit] at h
  | cons f fs ih =>
    intro i cfs r h
    cases f with
    | init1 g e k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, by simp⟩
    | init2 g k =>
        simp only [Stack.topInit, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨rfl, by simp⟩
    | call t p κ =>
        rw [Stack.topInit] at h
        cases hfs : Stack.topInit fs with
        | none => rw [hfs] at h; simp at h
        | some val =>
            obtain ⟨f', calls, rest⟩ := val
            rw [hfs] at h
            simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl⟩ := h
            obtain ⟨heq, hcalls⟩ := ih hfs
            refine ⟨by rw [heq]; rfl, ?_⟩
            intro g hg
            rcases List.mem_cons.mp hg with rfl | hg'
            · rfl
            · exact hcalls g hg'

/-- Dually: a stack of the form `pre ++ f :: r` with `f` an init frame *has* a
    topmost init frame, and that frame is either one of the `pre` frames or `f`
    itself.  Induction on `pre`: a `call` head is walked past by `topInit`, an
    init head is returned immediately. -/
theorem Stack.topInit_append_init : ∀ (pre : Stack) {f : Frame} {r : Stack} {G₂ : GlobName},
    f.glob = some G₂ →
    ∃ i cfs r₂ G₃, (pre ++ f :: r).topInit = some (i, cfs, r₂) ∧ i.glob = some G₃ ∧
      (i ∈ pre ∨ i = f) := by
  intro pre
  induction pre with
  | nil =>
      intro f r G₂ hf
      cases f with
      | call t p κ => simp [Frame.glob] at hf
      | init1 g e k => exact ⟨_, [], r, G₂, rfl, hf, Or.inr rfl⟩
      | init2 g k => exact ⟨_, [], r, G₂, rfl, hf, Or.inr rfl⟩
  | cons g pre ih =>
      intro f r G₂ hf
      cases g with
      | call t p κ =>
          obtain ⟨i, cfs, r₂, G₃, hti, hig, hm⟩ := ih (r := r) hf
          refine ⟨i, Frame.call t p κ :: cfs, r₂, G₃, ?_, hig, ?_⟩
          · simp [Stack.topInit, List.cons_append, hti]
          · rcases hm with hm | rfl
            · exact Or.inl (List.mem_cons_of_mem _ hm)
            · exact Or.inr rfl
      | init1 a b c =>
          exact ⟨_, [], pre ++ f :: r, a, rfl, rfl, Or.inl List.mem_cons_self⟩
      | init2 a b =>
          exact ⟨_, [], pre ++ f :: r, a, rfl, rfl, Or.inl List.mem_cons_self⟩

/-- The global pinned by the topmost init frame of a `DepChain` stack is `G`
    itself or one of `G`'s dependencies. -/
theorem Stack.DepChain.top {σ : Sigma} {L : Program} {G : GlobName} {r S : Stack}
    (h : Stack.DepChain σ L G r S) :
    ∃ i cfs r₂ G₂, S.topInit = some (i, cfs, r₂) ∧ Stack.TopInit S G₂ ∧
      (G₂ = G ∨ G₂ ∈ Dep σ L G) := by
  obtain ⟨pre, f, rfl, hfg, hpre⟩ := h
  obtain ⟨i, cfs, r₂, G₃, hti, hig, hm⟩ := Stack.topInit_append_init pre hfg
  refine ⟨i, cfs, r₂, G₃, hti, ?_, ?_⟩
  · intro i' cfs' r' h'
    rw [hti, Option.some.injEq, Prod.mk.injEq] at h'
    obtain ⟨rfl, -⟩ := h'
    simpa using hig
  · rcases hm with hm | rfl
    · exact Or.inr (hpre i hm G₃ hig)
    · exact Or.inl (by rw [hfg] at hig; simpa using hig.symm)

/-- Preservation of `Stack.DepChain` by a single step.  The only interesting
    cases are `ipush` (the newly pinned global is read off the focus, so `wrong`
    puts it in `Dep` of the currently pinned global, and `Dep.trans` relays it
    to `G`) and `ipop` (popping `G`'s own frame would break the chain — this is
    what `hstay` on the *post*-state excludes, by a length argument). -/
theorem Stack.DepChain.step {σ : Sigma} {L : Program} {G : GlobName} {r : Stack}
    {H H' : Heap} {Γ Γ' : GTable} {S S' : Stack} {e e' : Expr}
    (hstep : Step L (.mk H Γ S e) (.mk H' Γ' S' e'))
    (hinv : Inv σ L (.mk H Γ S e)) (hrinv : REInv σ L (.mk H Γ S e))
    (hdc : Stack.DepChain σ L G r S) (hstay : Stack.InsideInit G r S') :
    Stack.DepChain σ L G r S' := by
  cases hstep with
  | this _ => exact hdc
  | param _ => exact hdc
  | proj _ => exact hdc
  | gproj _ _ => exact hdc
  | newAlloc _ _ _ _ => exact hdc
  | methCall _ _ _ =>
      -- a `call` frame is pushed: it records no global, so the `pre` condition
      -- extends for free
      obtain ⟨pre, f, rfl, hfg, hpre⟩ := hdc
      refine ⟨_ :: pre, f, rfl, hfg, ?_⟩
      intro g hg G₀ hG₀
      rcases List.mem_cons.mp hg with rfl | hg'
      · simp [Frame.glob] at hG₀
      · exact hpre g hg' G₀ hG₀
  | ret =>
      -- a `call` frame is popped: it cannot be `G`'s init frame, so `pre ≠ []`
      obtain ⟨pre, f, heq, hfg, hpre⟩ := hdc
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, -⟩ := heq
          simp [Frame.glob] at hfg
      | cons g pre' =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          exact ⟨pre', f, rfl, hfg, fun g' hg' => hpre g' (List.mem_cons_of_mem _ hg')⟩
  | ipush hobj hΓ =>
      -- the pushed global is the one the focus was accessing: `wrong` at the
      -- pre-state puts it in `Dep` of the currently pinned global
      obtain ⟨i₀, cfs₀, r₀, G₂, hti, htiG, hdle⟩ := hdc.top
      have hdep := wrong hti htiG hinv hrinv
      obtain ⟨pre, f, rfl, hfg, hpre⟩ := hdc
      refine ⟨_ :: pre, f, rfl, hfg, ?_⟩
      intro g hg G₀ hG₀
      rcases List.mem_cons.mp hg with rfl | hg'
      · simp only [Frame.glob, Option.some.injEq] at hG₀
        subst hG₀
        rcases hdle with rfl | hG₂
        · exact hdep
        · exact Dep.trans hG₂ hdep
      · exact hpre g hg' G₀ hG₀
  | inext _ =>
      -- `init1 G₀ e k` is replaced by `init2 G₀ k`: same `glob`, same position
      obtain ⟨pre, f, heq, hfg, hpre⟩ := hdc
      cases pre with
      | nil =>
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact ⟨[], _, rfl, by simpa [Frame.glob] using hfg, by simp⟩
      | cons g pre' =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          refine ⟨_ :: pre', f, rfl, hfg, ?_⟩
          intro g' hg' G₀ hG₀
          rcases List.mem_cons.mp hg' with rfl | hg''
          · exact hpre _ List.mem_cons_self G₀ (by simpa [Frame.glob] using hG₀)
          · exact hpre g' (List.mem_cons_of_mem _ hg'') G₀ hG₀
  | ipop _ =>
      obtain ⟨pre, f, heq, hfg, hpre⟩ := hdc
      cases pre with
      | nil =>
          -- `G`'s own init frame would be popped, leaving the stack `r`; then
          -- `hstay` would need `r = pre' ++ f' :: r`, impossible by length
          simp only [List.nil_append, List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          obtain ⟨pre', f', heq', -⟩ := hstay
          have hl := congrArg List.length heq'
          simp at hl
          exfalso; omega
      | cons g pre' =>
          simp only [List.cons_append, List.cons.injEq] at heq
          obtain ⟨-, rfl⟩ := heq
          exact ⟨pre', f, rfl, hfg, fun g' hg' => hpre g' (List.mem_cons_of_mem _ hg')⟩

/-- The stack of a configuration (the empty stack for `crash`). -/
def Config.stack : Config → Stack
  | .mk _ _ S _ => S
  | .crash => []

/-- The multi-step engine behind `access_implies_dep`: induction on the run,
    transporting `Inv` (by `hpres`), `REInv` (by `REInv.step`) and the
    dependency chain (by `Stack.DepChain.step`) to the last configuration, where
    `wrong` fires once and `Dep.trans` relays its conclusion back to `G`. -/
theorem access_dep_run {σ : Sigma} {L : Program} {G : GlobName} {r : Stack}
    (hσ : FixPoint σ L) :
    ∀ {c₀ c₁ : Config}, Star L c₀ c₁ →
      Inv σ L c₀ → REInv σ L c₀ → Stack.DepChain σ L G r c₀.stack →
      (∀ c₂, Star L c₀ c₂ → Star L c₂ c₁ → Stack.InsideInit G r c₂.stack) →
      ∀ {H' : Heap} {Γ' : GTable} {S' : Stack} {E : ECtx} {G' : GlobName} {j : Idx},
        c₁ = Config.mk H' Γ' S' (E.plug (Expr.gproj G' j)) → G' ∈ Dep σ L G := by
  intro c₀ c₁ hstar
  induction hstar with
  | refl =>
      intro hinv hrinv hdc _ H' Γ' S' E G' j hc
      subst hc
      obtain ⟨i₀, cfs₀, r₀, G₂, hti, htiG, hdle⟩ := hdc.top
      have hdep := wrong hti htiG hinv hrinv
      rcases hdle with rfl | hG₂
      · exact hdep
      · exact Dep.trans hG₂ hdep
  | @head c c' c'' hstep hrest ih =>
      intro hinv hrinv hdc hstay H' Γ' S' E G' j hc
      cases c with
      | crash => cases hstep
      | mk H Γ S e =>
        cases c' with
        | crash =>
            -- `crash` is stuck, so it cannot reach the `.mk` target
            cases hrest with
            | refl => exact Config.noConfusion hc
            | head hs _ => cases hs
        | mk H₁ Γ₁ S₁ e₁ =>
            have hinv' : Inv σ L (Config.mk H₁ Γ₁ S₁ e₁) := inv_preservation_step hσ hinv hstep
            exact ih hinv' (REInv.step hinv hinv' hstep hrinv)
              (hdc.step hstep hinv hrinv (hstay _ (Star.single hstep) hrest))
              (fun c₂ h₁ h₂ => hstay c₂ (Star.head hstep h₁) h₂) hc

/-- **Access implies dependency.**  If, during the initialization of `G`, the
    program accesses `G'.j`, then `G' ∈ Dep(G)`.

    Two hypotheses beyond the single-step data are needed and are discussed at
    the head of this section: `hpres` (preservation of `Inv`, not yet available
    as an aggregated theorem in this development) and `hstay` (the run stays
    inside `G`'s initialization — without it the statement is false, since after
    the `ipop` that ends `G`'s initialization the program resumes in the
    enclosing global's initializer and may access globals outside `Dep(G)`). -/
theorem access_implies_dep {L : Program} {G G': GlobName} {S cfs r S' : Stack}
  {σ : Sigma} {E : ECtx} {H H' : Heap} {Γ Γ' : GTable} {j : Idx} {ifr : Frame}
  {e₁ e₂ eᵢ : Expr} (hσ : FixPoint σ L)
  (hti : S.topInit = some (ifr, cfs, r)) (htiG : Stack.TopInit S G)
  (hHasObj : Program.HasObject L G e₁ e₂) (hsel : eᵢ = e₁ ∨ eᵢ = e₂)
  (hinv : Inv σ L (.mk H Γ S eᵢ)) (hrinv : REInv σ L (.mk H Γ S eᵢ))
  (hstar : Star L (.mk H Γ S eᵢ) (.mk H' Γ' S' (E.plug (Expr.gproj G' j))))
  (hstay : ∀ c₂, Star L (.mk H Γ S eᵢ) c₂ →
    Star L c₂ (.mk H' Γ' S' (E.plug (Expr.gproj G' j))) → Stack.InsideInit G r c₂.stack) :
  G' ∈ Dep σ L G := by
  refine access_dep_run hσ hstar hinv hrinv ?_ hstay rfl
  -- the initial stack is `cfs ++ ifr :: r` with `ifr` pinning `G`; the frames
  -- above it are `call` frames, which record no global
  obtain ⟨hdecomp, hcalls⟩ := Stack.topInit_decomp hti
  refine ⟨cfs, ifr, hdecomp, ?_, ?_⟩
  · simpa using htiG ifr cfs r hti
  · intro g hg G₀ hG₀
    rw [hcalls g hg] at hG₀
    exact absurd hG₀ (by simp)
