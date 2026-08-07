import Proof.Semantics
import Proof.Stack
import Proof.Analysis

namespace Proof

theorem Heap.lookup_update_ne {H : Heap} {l l₀ : Loc} {o : ClsIns}
    (h : l ≠ l₀) : H[l₀ ↦ o] l = H l := by
  simp [Heap.update, h]

theorem GTable.lookup_update_ne {Γ : GTable} {G G₀ : GlobName} {o : GEntry}
    (h : G ≠ G₀) : Γ[G₀ ↦ o] G = Γ G := by
  simp [GTable.update, h]

def Heap.opOf (H : Heap) : Value → Set OPair
  | Value.loc ℓ =>
    match H ℓ with
    | some o => {(o.g, o.cls)}
    | none   => ∅
  | Value.btrue  => ∅
  | Value.bfalse => ∅

theorem KJ.det {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program} :
    ∀ {e K K'}, KJ G C σ L e K → KJ G C σ L e K' → K = K'
  | _, _, _, .thisE, .thisE => rfl
  | _, _, _, .paramE, .paramE => rfl
  | _, _, _, .proj h, .proj h' => by rw [KJ.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJ.det h h']
  | _, _, _, .val, .val => rfl

theorem KJ.total {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program} :
    ∀ e, ∃ K, KJ G C σ L e K := by
  intro e
  induction e with
  | thisE => exact ⟨_, .thisE⟩
  | paramE => exact ⟨_, .paramE⟩
  | val v => exact ⟨_, .val⟩
  | gproj G₀ i => exact ⟨_, .gproj⟩
  | proj e i ih => obtain ⟨K, hK⟩ := ih; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ => exact ⟨_, .newC⟩
  | app e₁ e₂ ih₁ ih₂ => obtain ⟨K₁, hK₁⟩ := ih₁; exact ⟨_, .app hK₁⟩

inductive KJR (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) :
    Expr → Set OPair → Prop
  | val {v} : KJR G σ L H S (Expr.val v) (H.opOf v)
  | thisE {t p κ} :
      S.topCall = some (Frame.call t p κ) →
      KJR G σ L H S Expr.thisE (H.opOf (Value.loc t))
  | paramE {t p κ} :
      S.topCall = some (Frame.call t p κ) →
      KJR G σ L H S Expr.paramE (H.opOf p)
  | proj {e i K} :
      KJR G σ L H S e K → KJR G σ L H S (Expr.proj e i) (⋃ p ∈ K, σ.Fld i p.1 p.2)
  | gproj {G₀ i} : KJR G σ L H S (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJR G σ L H S (Expr.newC D e₁ e₂) {(G, D)}
  | app {e₁ e₂ K₁} :
      KJR G σ L H S e₁ K₁ → KJR G σ L H S (Expr.app e₁ e₂) (⋃ p ∈ K₁, σ.Ret G p.2)

theorem KJR.det {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ {e K K'}, KJR G σ L H S e K → KJR G σ L H S e K' → K = K'
  | _, _, _, .val, .val => rfl
  | _, _, _, .thisE htc, .thisE htc' => by rw [htc] at htc'; cases htc'; rfl
  | _, _, _, .paramE htc, .paramE htc' => by rw [htc] at htc'; cases htc'; rfl
  | _, _, _, .proj h, .proj h' => by rw [KJR.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJR.det h h']

theorem KJR.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx) (K : Set OPair), KJR G σ L H S (E.plug eₓ) K →
      ∃ K', KJR G σ L H S (E.plug eᵣ) K' ∧ K ⊆ K' := by
  intro E
  induction E with
  | hole => exact h
  | projc E i ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | proj hK₀ =>
      obtain ⟨K', hK', hsub⟩ := ih _ hK₀
      exact ⟨_, .proj hK', Set.biUnion_subset_biUnion_left hsub⟩
  | appL E a ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | app hK₀ =>
      obtain ⟨K', hK', hsub⟩ := ih _ hK₀
      exact ⟨_, .app hK', Set.biUnion_subset_biUnion_left hsub⟩
  | appR w E _ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | app hK₀ =>
      cases hK₀
      exact ⟨_, .app .val, subset_rfl⟩
  | newL C E a _ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | newC => exact ⟨_, .newC, subset_rfl⟩
  | newR C w E _ih =>
    intro K hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | newC => exact ⟨_, .newC, subset_rfl⟩

/- Invariants -/

def RuntimeParamFldThisSound (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Expr → Prop
  | Expr.app e₁ e₂ =>
      RuntimeParamFldThisSound G σ L H S e₁ ∧ RuntimeParamFldThisSound G σ L H S e₂ ∧
      ∀ K₁ K₂, KJR G σ L H S e₁ K₁ → KJR G σ L H S e₂ K₂ →
        ∀ p ∈ K₁, K₂ ⊆ σ.Param G p.2 ∧ p.1 ∈ σ.This G p.2
  | Expr.newC C e₁ e₂ =>
      RuntimeParamFldThisSound G σ L H S e₁ ∧ RuntimeParamFldThisSound G σ L H S e₂ ∧
      ∀ K₁ K₂, KJR G σ L H S e₁ K₁ → KJR G σ L H S e₂ K₂ →
        K₁ ⊆ σ.Fld Idx.one G C ∧ K₂ ⊆ σ.Fld Idx.two G C
  | Expr.proj e _ => RuntimeParamFldThisSound G σ L H S e
  | _ => True

def RuntimeParamFldThisInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → i.glob = some G →
    RuntimeParamFldThisSound G σ L H S e

def CallSound (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Expr → Prop
  | Expr.app e₁ e₂ =>
      CallSound G σ L H S e₁ ∧ CallSound G σ L H S e₂ ∧
      ∀ K₁, KJR G σ L H S e₁ K₁ → classes K₁ ⊆ σ.RM G
  | Expr.newC _ e₁ e₂ => CallSound G σ L H S e₁ ∧ CallSound G σ L H S e₂
  | Expr.proj e _ => CallSound G σ L H S e
  | _ => True

def CallInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → i.glob = some G →
    CallSound G σ L H S e

def Closed (H : Heap) : Expr → Prop
  | Expr.val (Value.loc ℓ) => (H ℓ).isSome
  | Expr.newC _ e₁ e₂      => Closed H e₁ ∧ Closed H e₂
  | Expr.app e₁ e₂         => Closed H e₁ ∧ Closed H e₂
  | Expr.proj e _          => Closed H e
  | _                      => True

def GInitInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G ifr r (hti : S.topInit = some (ifr, [], r)), ifr.glob = some G →
    ∀ i, Frame.idx ifr (Stack.topInit_notCall hti) = i
      → ∀ K, KJR G σ L H S e K → K ⊆ σ.GFld i G

def RetInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G i cfs r, S.topInit = some (i, cfs, r) → i.glob = some G
    → ∀ t p κ, S.topCall = some (Frame.call t p κ) → ∀ D, H t = some D
      → (∀ K, KJR G σ L H S e K → K ⊆ σ.Ret G D.cls)

def ParamInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G C, S' <:+ S → S'.topInit = some (i, cfs, r)
    → i.glob = some G → Frame.call t p κ ∈ cfs → H t = some C
      → ∀ ℓ, p = Value.loc ℓ → ∃ D, H ℓ = some D ∧ (D.g, D.cls) ∈ σ.Param G C.cls

def FldInv (σ : Sigma) (H : Heap) (Γ: GTable) : Prop :=
  ∀ G l (C : ClassName) (v₁ v₂ : Value),
    H l = some (ClsIns.mk C G v₁ v₂) → (Γ G).isSome ∧
      ∀ i ℓ', (ClsIns.mk C G v₁ v₂).field i = Value.loc ℓ' →
        ∃ c', H ℓ' = some c' ∧ (c'.g, c'.cls) ∈ σ.Fld i G C

def GTableInv (σ : Sigma) (H : Heap) (Γ : GTable) : Prop :=
  ∀ g o, Γ g = some o →
    ∀ i ℓ', o.field i = some (Value.loc ℓ') →
      ∃ c', H ℓ' = some c' ∧ (c'.g, c'.cls) ∈ σ.GFld i g

def RMInv (σ : Sigma) (H: Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r f G l, S' <:+ S → S'.topInit = some (i, cfs, r)
  → i.glob = some G → f ∈ cfs → f.loc = some l → ∃ C, H l = some C ∧ C.cls ∈ σ.RM G

def ThisInv (σ : Sigma) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) i cfs r t p κ G, S' <:+ S → S'.topInit = some (i, cfs, r)
    → i.glob = some G → Frame.call t p κ ∈ cfs
    → ∃ D, H t = some D ∧ D.g ∈ σ.This G D.cls

def FrameInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ (S': Stack) t p E, (Frame.call t p E) :: S' <:+ S →
    ∀ G i cfs r, S'.topInit = some (i, cfs, r) → i.glob = some G →
      let redex := Expr.app (Expr.val (Value.loc t)) (Expr.val p)
      (∀ t' p' κ', S'.topCall = some (Frame.call t' p' κ') →
        ∀ D', H t' = some D' →
          ∀ K, KJR G σ L H S' (E.plug redex) K → K ⊆ σ.Ret G D'.cls)
      ∧ RuntimeParamFldThisSound G σ L H S' (E.plug redex)
      ∧ CallSound G σ L H S' (E.plug redex)
      ∧ GInitInv σ L H S' (E.plug redex)

def InitFrameInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) G k,
    ((∃ e, Frame.init1 G e k :: S' <:+ S) ∨ Frame.init2 G k :: S' <:+ S)
      → RetInv σ L H S' k ∧ RuntimeParamFldThisInv σ L H S' k ∧ CallInv σ L H S' k ∧ GInitInv σ L H S' k

def FrameClosedInv (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) t p E, (Frame.call t p E) :: S' <:+ S →
    Closed H (E.plug (Expr.app (Expr.val (Value.loc t)) (Expr.val p)))

def InitFrameClosedInv (H : Heap) (S : Stack) : Prop :=
  ∀ (S' : Stack) G k,
    ((∃ e, Frame.init1 G e k :: S' <:+ S) ∨ Frame.init2 G k :: S' <:+ S)
      → Closed H k

theorem RMInv.opOf_update_fresh {σ : Sigma} {H : Heap} {S S' : Stack}
    {i : Frame} {cfs r : Stack} {G : GlobName} {l : Loc} {o : ClsIns}
    (hrm : RMInv σ H S) (hparam : ParamInv σ H S)
    (hHl : H l = none) (hsubS : S' <:+ S)
    (hti : S'.topInit = some (i, cfs, r)) (htiG : i.glob = some G) :
    ∀ t p κ, S'.topCall = some (Frame.call t p κ) →
      H.opOf (Value.loc t) = (H[l ↦ o]).opOf (Value.loc t) ∧
      H.opOf p = (H[l ↦ o]).opOf p := by
  intro t p κ htc
  have hf : Frame.call t p κ ∈ cfs := Stack.topCall_mem_topInit htc hti
  obtain ⟨Ct, hHt, -⟩ := hrm S' i cfs r (Frame.call t p κ) G t hsubS hti htiG hf rfl
  have htl : t ≠ l := by intro h; rw [h, hHl] at hHt; simp at hHt
  refine ⟨?_, ?_⟩
  · have hte : (H[l ↦ o]) t = H t := by simp [Heap.update, htl]
    simp only [Heap.opOf, hte]
  · cases p with
    | loc ℓ =>
      obtain ⟨D, hHℓ, -⟩ :=
        hparam S' i cfs r t (Value.loc ℓ) κ G Ct hsubS hti htiG hf hHt ℓ rfl
      have hℓl : ℓ ≠ l := by intro h; rw [h, hHl] at hHℓ; simp at hHℓ
      have hpe : (H[l ↦ o]) ℓ = H ℓ := by simp [Heap.update, hℓl]
      simp only [Heap.opOf, hpe]
    | btrue => rfl
    | bfalse => rfl

theorem Closed.of_plug {H : Heap} :
    ∀ (E : ECtx) {e : Expr}, Closed H (E.plug e) → Closed H e
  | .hole, _, h => h
  | .projc E _, _, h => Closed.of_plug E h
  | .appL E _, _, h => Closed.of_plug E h.1
  | .appR _ E, _, h => Closed.of_plug E h.2
  | .newL _ E _, _, h => Closed.of_plug E h.1
  | .newR _ _ E, _, h => Closed.of_plug E h.2

theorem Closed.plug_mono {H : Heap} {eᵣ eₓ : Expr} (hx : Closed H eₓ) :
    ∀ (E : ECtx), Closed H (E.plug eᵣ) → Closed H (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => Closed.plug_mono hx E hr
  | .appL E _, hr => ⟨Closed.plug_mono hx E hr.1, hr.2⟩
  | .appR _ E, hr => ⟨hr.1, Closed.plug_mono hx E hr.2⟩
  | .newL _ E _, hr => ⟨Closed.plug_mono hx E hr.1, hr.2⟩
  | .newR _ _ E, hr => ⟨hr.1, Closed.plug_mono hx E hr.2⟩

theorem KJR.plug_mono_grow {G : GlobName} {σ : Sigma} {L : Program} {S : Stack}
    {H H' : Heap} (hgrow : ∀ ℓ o, H ℓ = some o → H' ℓ = some o) {eᵣ eₓ : Expr}
    (h : ∀ K, KJR G σ L H' S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx) (K : Set OPair), Closed H (E.plug eᵣ) →
      KJR G σ L H' S (E.plug eₓ) K →
        ∃ K', KJR G σ L H S (E.plug eᵣ) K' ∧ K ⊆ K' := by
  intro E
  induction E with
  | hole => intro K _ hK; exact h K hK
  | projc E i ih =>
    intro K hcl hK
    simp only [ECtx.plug] at hcl hK ⊢
    cases hK with
    | proj hK₀ =>
      obtain ⟨K', hK', hsub⟩ := ih _ hcl hK₀
      exact ⟨_, .proj hK', Set.biUnion_subset_biUnion_left hsub⟩
  | appL E a ih =>
    intro K hcl hK
    simp only [ECtx.plug] at hcl hK ⊢
    cases hK with
    | app hK₀ =>
      obtain ⟨K', hK', hsub⟩ := ih _ hcl.1 hK₀
      exact ⟨_, .app hK', Set.biUnion_subset_biUnion_left hsub⟩
  | appR w E _ih =>
    intro K hcl hK
    simp only [ECtx.plug] at hcl hK ⊢
    cases hK with
    | app hK₀ =>
      cases hK₀
      have hop : H.opOf w = H'.opOf w := by
        cases w with
        | loc ℓ =>
          obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (show (H ℓ).isSome from hcl.1)
          simp [Heap.opOf, ho, hgrow ℓ o ho]
        | btrue => rfl
        | bfalse => rfl
      exact ⟨_, .app .val, by rw [hop]⟩
  | newL C E a _ih =>
    intro K _ hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | newC => exact ⟨_, .newC, subset_rfl⟩
  | newR C w E _ih =>
    intro K _ hK
    simp only [ECtx.plug] at hK ⊢
    cases hK with
    | newC => exact ⟨_, .newC, subset_rfl⟩

theorem KJR.heap_congr {G : GlobName} {σ : Sigma} {L : Program} {S : Stack}
    {H H' : Heap} (hgrow : ∀ ℓ o, H ℓ = some o → H' ℓ = some o)
    (hstk : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
        H.opOf (Value.loc t) = H'.opOf (Value.loc t) ∧ H.opOf p = H'.opOf p) :
    ∀ {e : Expr} {K : Set OPair}, Closed H e → KJR G σ L H' S e K →
      KJR G σ L H S e K := by
  intro e
  induction e with
  | thisE =>
    intro K _ hK
    cases hK with
    | thisE htc => exact (hstk _ _ _ htc).1 ▸ .thisE htc
  | paramE =>
    intro K _ hK
    cases hK with
    | paramE htc => exact (hstk _ _ _ htc).2 ▸ .paramE htc
  | gproj G₀ i =>
    intro K _ hK
    cases hK with
    | gproj => exact .gproj
  | val v =>
    intro K hcl hK
    cases hK with
    | val =>
      have hv : H.opOf v = H'.opOf v := by
        cases v with
        | loc ℓ =>
          obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp (show (H ℓ).isSome from hcl)
          simp [Heap.opOf, ho, hgrow ℓ o ho]
        | btrue => rfl
        | bfalse => rfl
      exact hv ▸ .val
  | proj e i ih =>
    intro K hcl hK
    cases hK with
    | proj hK₀ => exact .proj (ih hcl hK₀)
  | newC D e₁ e₂ _ih₁ _ih₂ =>
    intro K _ hK
    cases hK with
    | newC => exact .newC
  | app e₁ e₂ ih₁ _ih₂ =>
    intro K hcl hK
    cases hK with
    | app hK₀ => exact .app (ih₁ hcl.1 hK₀)

theorem Closed.of_valueFree {H : Heap} : ∀ e, ValueFree e → Closed H e := by
  intro e
  induction e with
  | thisE => intro _; trivial
  | paramE => intro _; trivial
  | gproj G₀ i => intro _; trivial
  | val v => intro hvf; exact False.elim hvf
  | proj e i ih => intro hvf; exact ih hvf
  | newC C e₁ e₂ ih₁ ih₂ => intro hvf; exact ⟨ih₁ hvf.1, ih₂ hvf.2⟩
  | app e₁ e₂ ih₁ ih₂ => intro hvf; exact ⟨ih₁ hvf.1, ih₂ hvf.2⟩

theorem Closed.mono {H H' : Heap} (hHH' : ∀ ℓ o, H ℓ = some o → H' ℓ = some o) :
  ∀ {e}, Closed H e → Closed H' e := by
  intro e
  induction e with
  | thisE => intro h; trivial
  | paramE => intro _; trivial
  | gproj G₀ i => intro _; trivial
  | val v =>
    intro h
    cases v with
    | loc ℓ' =>
      obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp h
      show (H' ℓ').isSome
      rw [hHH' ℓ' o ho]
      rfl
    | _ => trivial
  | proj e i ih => intro h; exact ih h
  | newC C e₁ e₂ ih₁ ih₂ => intro h; exact ⟨ih₁ h.1, ih₂ h.2⟩
  | app e₁ e₂ ih₁ ih₂ => intro h; exact ⟨ih₁ h.1, ih₂ h.2⟩

theorem RuntimeParamFldThisSound.of_plug {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ (E : ECtx) {e : Expr}, RuntimeParamFldThisSound G σ L H S (E.plug e) → RuntimeParamFldThisSound G σ L H S e
  | .hole, _, h => h
  | .projc E _, _, h => RuntimeParamFldThisSound.of_plug E h
  | .appL E _, _, h => RuntimeParamFldThisSound.of_plug E h.1
  | .appR _ E, _, h => RuntimeParamFldThisSound.of_plug E h.2.1
  | .newL _ E _, _, h => RuntimeParamFldThisSound.of_plug E h.1
  | .newR _ _ E, _, h => RuntimeParamFldThisSound.of_plug E h.2.1

theorem RuntimeParamFldThisSound.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (hx : RuntimeParamFldThisSound G σ L H S eₓ)
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), RuntimeParamFldThisSound G σ L H S (E.plug eᵣ) → RuntimeParamFldThisSound G σ L H S (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => RuntimeParamFldThisSound.plug_mono hx h E hr
  | .appL E a, hr =>
      ⟨RuntimeParamFldThisSound.plug_mono hx h E hr.1, hr.2.1, fun K₁ K₂ hK₁ hK₂ p hp => by
        obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.plug_mono h E K₁ hK₁
        exact hr.2.2 K₁' K₂ hK₁' hK₂ p (hsub₁ hp)⟩
  | .appR w E, hr =>
      ⟨trivial, RuntimeParamFldThisSound.plug_mono hx h E hr.2.1, fun K₁ K₂ hK₁ hK₂ p hp => by
        have asdf := hr.2.2
        obtain ⟨K₂', hK₂', hsub₂⟩ := KJR.plug_mono h E K₂ hK₂
        refine ⟨?_, ?_⟩
        · exact hsub₂.trans (hr.2.2 K₁ K₂' hK₁ hK₂' p hp).1
        · exact (hr.2.2 K₁ K₂' hK₁ hK₂' p hp).2
      ⟩
  | .newL _ E _, hr => ⟨RuntimeParamFldThisSound.plug_mono hx h E hr.1, hr.2.1, fun K₁ K₂ hK₁ hK₂ => by
        obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.plug_mono h E K₁ hK₁
        have h' := hr.2.2 K₁' K₂ hK₁' hK₂
        exact ⟨hsub₁.trans h'.1, h'.2⟩⟩
  | .newR _ _ E, hr => ⟨hr.1, RuntimeParamFldThisSound.plug_mono hx h E hr.2.1, fun K₁ K₂ hK₁ hK₂ => by
        obtain ⟨K₂', hK₂', hsub₂⟩ := KJR.plug_mono h E K₂ hK₂
        have h' := hr.2.2 K₁ K₂' hK₁ hK₂'
        exact ⟨h'.1, hsub₂.trans h'.2⟩⟩

theorem RuntimeParamFldThisSound.heap_congr {G : GlobName} {σ : Sigma} {L : Program} {S : Stack}
    {H H' : Heap} (hgrow : ∀ ℓ o, H ℓ = some o → H' ℓ = some o)
    (hstk : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
        H.opOf (Value.loc t) = H'.opOf (Value.loc t) ∧ H.opOf p = H'.opOf p) :
    ∀ {e : Expr}, Closed H e → RuntimeParamFldThisSound G σ L H S e → RuntimeParamFldThisSound G σ L H' S e := by
  intro e
  induction e with
  | thisE => intro _ _; trivial
  | paramE => intro _ _; trivial
  | gproj => intro _ _; trivial
  | val => intro _ _; trivial
  | proj e i ih => intro hcl hAS; exact ih hcl hAS
  | app e₁ e₂ ih₁ ih₂ =>
    intro hcl hAS
    obtain ⟨h1, h2, h3⟩ := hAS
    exact ⟨ih₁ hcl.1 h1, ih₂ hcl.2 h2, fun K₁ K₂ hK₁ hK₂ =>
      h3 K₁ K₂ (KJR.heap_congr hgrow hstk hcl.1 hK₁) (KJR.heap_congr hgrow hstk hcl.2 hK₂)⟩
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hcl hAS
    obtain ⟨h1, h2, h3⟩ := hAS
    exact ⟨ih₁ hcl.1 h1, ih₂ hcl.2 h2, fun K₁ K₂ hK₁ hK₂ =>
      h3 K₁ K₂ (KJR.heap_congr hgrow hstk hcl.1 hK₁) (KJR.heap_congr hgrow hstk hcl.2 hK₂)⟩

theorem RuntimeParamFldThisSound.plug_mono_grow {G : GlobName} {σ : Sigma} {L : Program} {S : Stack}
    {H H' : Heap} (hgrow : ∀ ℓ o, H ℓ = some o → H' ℓ = some o)
    (hstk : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
        H.opOf (Value.loc t) = H'.opOf (Value.loc t) ∧ H.opOf p = H'.opOf p)
    {eᵣ eₓ : Expr} (hx : RuntimeParamFldThisSound G σ L H' S eₓ)
    (h : ∀ K, KJR G σ L H' S eₓ K → ∃ K', KJR G σ L H' S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), Closed H (E.plug eᵣ) →
      RuntimeParamFldThisSound G σ L H S (E.plug eᵣ) → RuntimeParamFldThisSound G σ L H' S (E.plug eₓ) := by
  intro E hcl hAS
  exact RuntimeParamFldThisSound.plug_mono hx h E (RuntimeParamFldThisSound.heap_congr hgrow hstk hcl hAS)

theorem KJR.to_kjc {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} {c : Ctx}
    (hthis : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C, {(G', C)})
    (hparam : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.paramE K → K ⊆ σ.Param G C)
    {e : Expr} {K : Set OPair} (hpf : c = none → ContextFree e) (hvf : ValueFree e)
    (hK : KJR G σ L H S e K) : ∃ K', KJC G σ L c e K' ∧ K ⊆ K' := by
  induction hK with
  | val => exact False.elim hvf
  | thisE htc =>
    cases c with
    | none => exact False.elim (hpf rfl)
    | some C => exact ⟨_, KJ.thisE, hthis C rfl _ (.thisE htc)⟩
  | paramE htc =>
    cases c with
    | none => exact False.elim (hpf rfl)
    | some C => exact ⟨_, KJ.paramE, hparam C rfl _ (.paramE htc)⟩
  | proj h ih =>
    obtain ⟨K', hK', hsub⟩ := ih hpf hvf
    exact ⟨_, KJC.proj hK', Set.biUnion_subset_biUnion_left hsub⟩
  | gproj => exact ⟨_, KJC.gproj, subset_rfl⟩
  | newC => exact ⟨_, KJC.newC, subset_rfl⟩
  | app h ih =>
    obtain ⟨K', hK', hsub⟩ := ih (fun hc => (hpf hc).1) hvf.1
    exact ⟨_, KJC.app hK', Set.biUnion_subset_biUnion_left hsub⟩

theorem RuntimeParamFldThisSound.of_re {σ : Sigma} {L : Program} {G : GlobName} {H : Heap} {S : Stack}
    {c : Ctx} (hσ : FixPoint σ L)
    (hthis : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C, {(G', C)})
    (hparam : ∀ C, c = some C → ∀ K, KJR G σ L H S Expr.paramE K → K ⊆ σ.Param G C) :
    ∀ e, RE σ L G c e → (c = none → ContextFree e) → ValueFree e →
      RuntimeParamFldThisSound G σ L H S e := by
  intro e
  induction e with
  | thisE => intro _ _ _; trivial
  | paramE => intro _ _ _; trivial
  | val v => intro _ _ hvf; exact False.elim hvf
  | gproj G₀ i => intro _ _ _; trivial
  | proj e i ih => intro hre hpf hvf; exact ih (RE.proj hre) hpf hvf
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hre hpf hvf
    refine ⟨ih₁ (RE.newC₁ hre) (fun hc => (hpf hc).1) hvf.1,
           ih₂ (RE.newC₂ hre) (fun hc => (hpf hc).2) hvf.2, ?_⟩
    intro K₁ K₂ hK₁ hK₂
    obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).1) hvf.1 hK₁
    obtain ⟨K₂', hK₂', hsub₂⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).2) hvf.2 hK₂
    exact ⟨hsub₁.trans (hσ.fld_re hre hK₁' hK₂').1, hsub₂.trans (hσ.fld_re hre hK₁' hK₂').2 ⟩
  | app e₁ e₂ ih₁ ih₂ =>
    intro hre hpf hvf
    refine ⟨ih₁ (RE.app₁ hre) (fun hc => (hpf hc).1) hvf.1,
            ih₂ (RE.app₂ hre) (fun hc => (hpf hc).2) hvf.2, ?_⟩
    intro K₁ K₂ hK₁ hK₂ p hp
    obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).1) hvf.1 hK₁
    obtain ⟨K₂', hK₂', hsub₂⟩ := KJR.to_kjc hthis hparam (fun hc => (hpf hc).2) hvf.2 hK₂
    refine ⟨?_, ?_⟩
    · exact hsub₂.trans (hσ.param_re hre hK₁' hK₂' p.2 (mem_classes.mpr ⟨p.1, hsub₁ hp⟩))
    · exact hσ.this_re hre hK₁' rfl p.2 (mem_classes.mpr ⟨p.1, hsub₁ hp⟩) ⟨p, hsub₁ hp, rfl⟩

theorem CallSound.of_plug {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ (E : ECtx) {e : Expr}, CallSound G σ L H S (E.plug e) → CallSound G σ L H S e
  | .hole, _, h => h
  | .projc E _, _, h => CallSound.of_plug E h
  | .appL E _, _, h => CallSound.of_plug E h.1
  | .appR _ E, _, h => CallSound.of_plug E h.2.1
  | .newL _ E _, _, h => CallSound.of_plug E h.1
  | .newR _ _ E, _, h => CallSound.of_plug E h.2

theorem classes_mono {K K' : Set OPair} (h : K ⊆ K') : classes K ⊆ classes K' :=
  fun _ hx => let ⟨p, hp, he⟩ := hx; ⟨p, h hp, he⟩

theorem CallSound.plug_mono {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (hx : CallSound G σ L H S eₓ)
    (h : ∀ K, KJR G σ L H S eₓ K → ∃ K', KJR G σ L H S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), CallSound G σ L H S (E.plug eᵣ) → CallSound G σ L H S (E.plug eₓ)
  | .hole, _ => hx
  | .projc E _, hr => CallSound.plug_mono hx h E hr
  | .appL E a, hr =>
      ⟨CallSound.plug_mono hx h E hr.1, hr.2.1, fun K₁ hK₁ => by
        obtain ⟨K₁', hK₁', hsub₁⟩ := KJR.plug_mono h E K₁ hK₁
        exact (classes_mono hsub₁).trans (hr.2.2 K₁' hK₁')⟩
  | .appR w E, hr => ⟨trivial, CallSound.plug_mono hx h E hr.2.1, hr.2.2⟩
  | .newL _ E _, hr => ⟨CallSound.plug_mono hx h E hr.1, hr.2⟩
  | .newR _ _ E, hr => ⟨hr.1, CallSound.plug_mono hx h E hr.2⟩

theorem CallSound.heap_congr {G : GlobName} {σ : Sigma} {L : Program} {S : Stack}
    {H H' : Heap} (hgrow : ∀ ℓ o, H ℓ = some o → H' ℓ = some o)
    (hstk : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
        H.opOf (Value.loc t) = H'.opOf (Value.loc t) ∧ H.opOf p = H'.opOf p) :
    ∀ {e : Expr}, Closed H e → CallSound G σ L H S e → CallSound G σ L H' S e := by
  intro e
  induction e with
  | thisE => intro _ _; trivial
  | paramE => intro _ _; trivial
  | gproj => intro _ _; trivial
  | val => intro _ _; trivial
  | proj e i ih => intro hcl hCS; exact ih hcl hCS
  | app e₁ e₂ ih₁ ih₂ =>
    intro hcl hCS
    obtain ⟨h1, h2, h3⟩ := hCS
    exact ⟨ih₁ hcl.1 h1, ih₂ hcl.2 h2,
      fun K₁ hK₁ => h3 K₁ (KJR.heap_congr hgrow hstk hcl.1 hK₁)⟩
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hcl hCS
    obtain ⟨h1, h2⟩ := hCS
    exact ⟨ih₁ hcl.1 h1, ih₂ hcl.2 h2⟩

theorem CallSound.plug_mono_grow {G : GlobName} {σ : Sigma} {L : Program} {H H' : Heap} {S : Stack}
    {eᵣ eₓ : Expr}
    (hx : CallSound G σ L H' S eₓ) (hgrow : ∀ ℓ o, H ℓ = some o → H' ℓ = some o)
    (hstk : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
        H.opOf (Value.loc t) = H'.opOf (Value.loc t) ∧ H.opOf p = H'.opOf p)
    (h : ∀ K, KJR G σ L H' S eₓ K → ∃ K', KJR G σ L H' S eᵣ K' ∧ K ⊆ K') :
    ∀ (E : ECtx), Closed H (E.plug eᵣ) →
      CallSound G σ L H S (E.plug eᵣ) → CallSound G σ L H' S (E.plug eₓ) := by
  intro E hcl hCS
  exact CallSound.plug_mono hx h E (CallSound.heap_congr hgrow hstk hcl hCS)

theorem KJ0.det {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ {e K K'}, KJ0 G σ L e K → KJ0 G σ L e K' → K = K'
  | _, _, _, .proj h, .proj h' => by rw [KJ0.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJ0.det h h']
  | _, _, _, .val, .val => rfl

theorem KJ0.total {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ e, ContextFree e → ∃ K, KJ0 G σ L e K := by
  intro e
  induction e with
  | thisE => intro hpf; exact False.elim hpf
  | paramE => intro hpf; exact False.elim hpf
  | val v => intro _; exact ⟨_, .val⟩
  | gproj G₀ i => intro _; exact ⟨_, .gproj⟩
  | proj e i ih => intro hpf; obtain ⟨K, hK⟩ := ih hpf; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ => intro _; exact ⟨_, .newC⟩
  | app e₁ e₂ ih₁ ih₂ => intro hpf; obtain ⟨K₁, hK₁⟩ := ih₁ hpf.1; exact ⟨_, .app hK₁⟩

theorem Calls0.total {G : GlobName} {σ : Sigma} {L : Program} :
    ∀ e, ContextFree e → ∃ K, Calls0 G σ L e K := by
  intro e
  induction e with
  | thisE => intro hpf; exact False.elim hpf
  | paramE => intro hpf; exact False.elim hpf
  | val v => intro _; exact ⟨_, .val⟩
  | gproj G₀ i => intro _; exact ⟨_, .gproj⟩
  | proj e i ih => intro hpf; obtain ⟨K, hK⟩ := ih hpf; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ =>
    intro hpf
    obtain ⟨K₁, h₁⟩ := ih₁ hpf.1
    obtain ⟨K₂, h₂⟩ := ih₂ hpf.2
    exact ⟨_, .newC h₁ h₂⟩
  | app e₁ e₂ ih₁ ih₂ =>
    intro hpf
    obtain ⟨K₁, hK₁⟩ := KJ0.total e₁ hpf.1
    obtain ⟨K₂, h₂⟩ := ih₁ hpf.1
    obtain ⟨K₃, h₃⟩ := ih₂ hpf.2
    exact ⟨_, .app hK₁ h₂ h₃⟩

theorem CallSound.of_calls0 {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ {e K}, Calls0 G σ L e K → K ⊆ σ.RM G → ContextFree e → ValueFree e →
      CallSound G σ L H S e := by
  intro e K hc
  induction hc with
  | gproj => intro _ _ _; trivial
  | val => intro _ _ hvf; exact False.elim hvf
  | proj h ih => intro hK hpf hvf; exact ih hK hpf hvf
  | newC h₁ h₂ ih₁ ih₂ =>
    intro hK hpf hvf
    exact ⟨ih₁ (Set.subset_union_left.trans hK) hpf.1 hvf.1,
           ih₂ (Set.subset_union_right.trans hK) hpf.2 hvf.2⟩
  | app hkj h₁ h₂ ih₁ ih₂ =>
    intro hK hpf hvf
    refine ⟨ih₁ ((Set.subset_union_right.trans Set.subset_union_left).trans hK) hpf.1 hvf.1,
            ih₂ (Set.subset_union_right.trans hK) hpf.2 hvf.2, ?_⟩
    intro Kr hKr
    obtain ⟨K₁', hK₁', hsub⟩ := KJR.to_kjc (c := none) (fun _ hc => nomatch hc)
      (fun _ hc => nomatch hc) (fun _ => hpf.1) hvf.1 hKr
    have hsub' : Kr ⊆ _ := (KJ0.det hK₁' hkj) ▸ hsub
    exact (classes_mono hsub').trans
      ((Set.subset_union_left.trans Set.subset_union_left).trans hK)

theorem Calls.total {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program} :
    ∀ e, ∃ K, Calls G C σ L e K := by
  intro e
  induction e with
  | thisE => exact ⟨_, .thisE⟩
  | paramE => exact ⟨_, .paramE⟩
  | val v => exact ⟨_, .val⟩
  | gproj G₀ i => exact ⟨_, .gproj⟩
  | proj e i ih => obtain ⟨K, hK⟩ := ih; exact ⟨_, .proj hK⟩
  | newC D e₁ e₂ ih₁ ih₂ =>
    obtain ⟨K₁, h₁⟩ := ih₁
    obtain ⟨K₂, h₂⟩ := ih₂
    exact ⟨_, .newC h₁ h₂⟩
  | app e₁ e₂ ih₁ ih₂ =>
    obtain ⟨K₁, hK₁⟩ := KJ.total e₁
    obtain ⟨K₂, h₂⟩ := ih₁
    obtain ⟨K₃, h₃⟩ := ih₂
    exact ⟨_, .app hK₁ h₂ h₃⟩

theorem CallSound.of_calls {G : GlobName} {C : ClassName} {σ : Sigma} {L : Program}
    {H : Heap} {S : Stack}
    (hthis : ∀ C', (some C : Ctx) = some C' → ∀ K, KJR G σ L H S Expr.thisE K →
      K ⊆ ⋃ G' ∈ σ.This G C', {(G', C')})
    (hparam : ∀ C', (some C : Ctx) = some C' → ∀ K, KJR G σ L H S Expr.paramE K →
      K ⊆ σ.Param G C') :
    ∀ {e K}, Calls G C σ L e K → K ⊆ σ.RM G → ValueFree e →
      CallSound G σ L H S e := by
  intro e K hc
  induction hc with
  | thisE => intro _ _; trivial
  | paramE => intro _ _; trivial
  | gproj => intro _ _; trivial
  | val => intro _ hvf; exact False.elim hvf
  | proj h ih => intro hK hvf; exact ih hK hvf
  | newC h₁ h₂ ih₁ ih₂ =>
    intro hK hvf
    exact ⟨ih₁ (Set.subset_union_left.trans hK) hvf.1,
           ih₂ (Set.subset_union_right.trans hK) hvf.2⟩
  | app hkj h₁ h₂ ih₁ ih₂ =>
    intro hK hvf
    refine ⟨ih₁ ((Set.subset_union_right.trans Set.subset_union_left).trans hK) hvf.1,
            ih₂ (Set.subset_union_right.trans hK) hvf.2, ?_⟩
    intro Kr hKr
    obtain ⟨K₁', hK₁', hsub⟩ := KJR.to_kjc (c := some C) hthis hparam
      (fun hc => nomatch hc) hvf.1 hKr
    have hsub' : Kr ⊆ _ := (KJ.det hK₁' hkj) ▸ hsub
    exact (classes_mono hsub').trans
      ((Set.subset_union_left.trans Set.subset_union_left).trans hK)

def Inv (σ : Sigma) (L : Program) : Config → Prop
  | .mk H Γ S e =>
    ParamInv σ H S
    ∧ FldInv σ H Γ
    ∧ GTableInv σ H Γ
    ∧ RetInv σ L H S e
    ∧ RuntimeParamFldThisInv σ L H S e
    ∧ CallInv σ L H S e
    ∧ RMInv σ H S
    ∧ ThisInv σ H S
    ∧ FrameInv σ L H S
    ∧ GInitInv σ L H S e
    ∧ InitFrameInv σ L H S
    ∧ Closed H e
    ∧ FrameClosedInv H S
    ∧ InitFrameClosedInv H S
  | .crash => True

theorem inv_empty {σ : Sigma} {L : Program} {G : GlobName} :
    Inv σ L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj G Idx.one)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ParamInv: no receiver is allocated in the empty heap.
    intro S' i cfs r t p κ G C _ _ _ _ hHt
    simp at hHt
  · -- FldInv: nothing is allocated in the empty heap.
    intro G l C v₁ v₂ hHl
    simp at hHl
  · -- GTableInv: the empty table has no entries.
    intro g o hg
    simp at hg
  · -- RetInv: the empty stack has no topmost init frame.
    intro G i cfs r hti
    simp [Stack.topInit] at hti
  · -- ArgInv: the empty stack has no topmost init frame.
    intro G i cfs r htop
    simp [Stack.topInit] at htop
  · -- CallInv: the empty stack has no topmost init frame.
    intro G i cfs r htop
    simp [Stack.topInit] at htop
  · -- RMInv: no frame's receiver is allocated in the empty heap.
    intro S' i cfs r f G l hsub htop hTopG hf hloc
    rcases List.suffix_nil.mp hsub with rfl
    simp [Stack.topInit] at htop
  · -- ThisInv: the empty stack has no suffix with an init frame.
    intro S' i cfs r t p κ G hsub hti
    rcases List.suffix_nil.mp hsub with rfl
    simp [Stack.topInit] at hti
  · -- FrameInv: the empty stack has no call frame.
    intro S' t p E hsub
    simp [List.suffix_nil] at hsub
  · -- GInitInv
    intro G ifr r htop
    simp [Stack.topInit] at htop
  · -- InitFrameInv: the empty stack has no init frame.
    intro S' G k hmem
    rcases hmem with ⟨e, hs⟩ | hs <;> simp [List.suffix_nil] at hs
  · -- Closed
    exact Closed.of_valueFree (Expr.gproj G Idx.one) trivial
  · -- FrameClosedInv: the empty stack has no call frame.
    intro S' t p E hsub
    simp [List.suffix_nil] at hsub
  · -- InitFrameClosedInv: the empty stack has no init frame.
    intro S' G k hmem
    rcases hmem with ⟨e, hs⟩ | hs <;> simp [List.suffix_nil] at hs

theorem inv_step_this {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack} {E κ : ECtx}
    {t : Loc} {p : Value} {C : ClsIns}
    (hHasCall : S.topCall = some (Frame.call t p κ)) (hC : H t = some C)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.thisE)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val (Value.loc t)))) := by
  obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv
  have h : ∀ (Ĝ : GlobName) K₁, KJR Ĝ σ L H S (Expr.val (Value.loc t)) K₁ →
        ∃ K', KJR Ĝ σ L H S Expr.thisE K' ∧ K₁ ⊆ K' := by
      intro Ĝ K₁ hK₁
      cases hK₁
      exact ⟨H.opOf (Value.loc t), KJR.thisE hHasCall, subset_rfl⟩
  refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, hframe, ?_, hinit, ?_, hfclosed, hclosedinit⟩
  · -- RetInv
    intro G' i cfs r hti htiG' t' p' k' htc D hD K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (h G') E K hK
    exact hsub.trans (hret G' i cfs r hti htiG' t' p' k' htc D hD K' hK')
  · -- RuntimeParamFldThisInv
    intro G' i cfs r hti htiG'
    have hx : RuntimeParamFldThisSound G' σ L H S (Expr.val (Value.loc t)) := trivial
    exact RuntimeParamFldThisSound.plug_mono hx (h G') E (harg G' i cfs r hti htiG')
  · -- CallInv
    intro G' i cfs r hti htiG'
    have hx : CallSound G' σ L H S (Expr.val (Value.loc t)) := trivial
    exact CallSound.plug_mono hx (h G') E (hcall G' i cfs r hti htiG')
  · -- GInitInv
    intro G' ifr r hti htiG' i' hidx K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (h G') E K hK
    exact hsub.trans (hgi G' ifr r hti htiG' i' hidx K' hK')
  · -- Closed
    have hcl : Closed H (Expr.val (Value.loc t)) := by
      simp [Closed, hC]
    exact Closed.plug_mono (eₓ := (Expr.val (Value.loc t))) hcl E hc

theorem inv_step_param {σ : Sigma} {L : Program} {H : Heap} {Γ : GTable} {S : Stack} {E κ : ECtx}
    {t : Loc} {p : Value} {C : ClsIns}
    (hHasCall : S.topCall = some (Frame.call t p κ)) (hC : H t = some C)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.paramE)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val p))) := by
  obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv
  have h : ∀ (Ĝ : GlobName) K₁, KJR Ĝ σ L H S (Expr.val p) K₁ →
        ∃ K', KJR Ĝ σ L H S Expr.paramE K' ∧ K₁ ⊆ K' := by
      intro Ĝ K₁ hK₁
      cases hK₁
      exact ⟨H.opOf p, KJR.paramE hHasCall, subset_rfl⟩
  refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, hframe, ?_, hinit, ?_, hfclosed, hclosedinit⟩
  · -- RetInv
    intro G' i cfs r hti htiG' t' p' k' htc D hD K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (h G') E K hK
    exact hsub.trans (hret G' i cfs r hti htiG' t' p' k' htc D hD K' hK')
  · -- RuntimeParamFldThisInv
    intro G' i cfs r hti htiG'
    have hx : RuntimeParamFldThisSound G' σ L H S (Expr.val p) := trivial
    exact RuntimeParamFldThisSound.plug_mono hx (h G') E (harg G' i cfs r hti htiG')
  · -- CallInv
    intro G' i cfs r hti htiG'
    have hx : CallSound G' σ L H S (Expr.val p) := trivial
    exact CallSound.plug_mono hx (h G') E (hcall G' i cfs r hti htiG')
  · -- GInitInv
    intro G' ifr r hti htiG' i' hidx K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (h G') E K hK
    exact hsub.trans (hgi G' ifr r hti htiG' i' hidx K' hK')
  · -- Closed
    have hcl : Closed H (Expr.val p) := by
      obtain ⟨fs, rfl⟩ : ∃ fs, S = Frame.call t p κ :: fs := by
        cases S with
        | nil => simp [Stack.topCall] at hHasCall
        | cons f fs =>
          cases f with
          | call t' p' κ' =>
            simp only [Stack.topCall, Option.some.injEq, Frame.call.injEq] at hHasCall
            obtain ⟨rfl, rfl, rfl⟩ := hHasCall
            exact ⟨fs, rfl⟩
          | init1 g e k => simp [Stack.topCall] at hHasCall
          | init2 g k => simp [Stack.topCall] at hHasCall
      exact (Closed.of_plug κ (hfclosed fs t p κ (List.suffix_refl _))).2
    exact Closed.plug_mono (eₓ := (Expr.val p)) hcl E hc

theorem inv_step_proj {σ : Sigma} {G₀ : GlobName} {L : Program} {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx}
    {ℓ : Loc} {C : ClassName} {v₁ v₂ : Value} {i : Idx}
    (hHl : H ℓ = some ⟨C, G₀, v₁, v₂⟩)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)))) := by
  obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv

  have hP : ∀ (G' : GlobName) K,
      KJR G' σ L H S (Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)) K →
      ∃ K', KJR G' σ L H S (Expr.proj (Expr.val (Value.loc ℓ)) i) K' ∧ K ⊆ K' := by
    intro G' K hK
    cases hK
    refine ⟨_, .proj .val, ?_⟩
    intro q hq
    cases hfi : (ClsIns.mk C G₀ v₁ v₂).field i with
    | loc ℓ' =>
      rw [hfi] at hq
      cases hHℓ' : H ℓ' with
      | none => simp [Heap.opOf, hHℓ'] at hq
      | some c' =>
        simp [Heap.opOf, hHℓ'] at hq
        subst hq
        obtain ⟨c'', hH'', hmem⟩ :=
          (hfld G₀ ℓ C v₁ v₂ hHl).2 i ℓ' hfi
        rw [hHℓ'] at hH''
        cases hH''
        simpa [Heap.opOf, hHl] using hmem
    | btrue => simp [hfi, Heap.opOf] at hq
    | bfalse => simp [hfi, Heap.opOf] at hq

  refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, hframe, ?_, hinit, ?_, hfclosed, hclosedinit⟩
  · -- RetInv: Proved using hP and KJR.plug_mono
    intro G' i' cfs' r' hti' htiG' t p κ htc D hHt K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
    exact hsub.trans (hret G' i' cfs' r' hti' htiG' t p κ htc D hHt K' hK')
  · -- ArgInv: the contractum is a value (trivially `RuntimeParamFldThisSound`) and its K-sets
    -- are covered by the redex's, so `RuntimeParamFldThisSound.plug_mono` transports the bound.
    intro G' i' cfs' r' htop' htiG'
    exact RuntimeParamFldThisSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i))
      trivial (hP G') E (harg G' i' cfs' r' htop' htiG')
  · -- CallInv: same transport, via `CallSound.plug_mono`.
    intro G' i' cfs' r' htop' htiG'
    exact CallSound.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i))
      trivial (hP G') E (hcall G' i' cfs' r' htop' htiG')
  · -- GInitInv:
    intro G' ifr r hti htiG' i₁ hi₁ K hK
    obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
    exact hsub.trans (hgi G' ifr r hti htiG' i₁ hi₁ K' hK')
  · -- Closed
    have heₓ : Closed H (Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)) := by
      cases hfi : (ClsIns.mk C G₀ v₁ v₂).field i with
      | loc ℓ' =>
        obtain ⟨c', hH', -⟩ := (hfld G₀ ℓ C v₁ v₂ hHl).2 i ℓ' hfi
        show (H ℓ').isSome
        rw [hH']
        rfl
      | btrue => trivial
      | bfalse => trivial
    exact Closed.plug_mono (eₓ := Expr.val ((ClsIns.mk C G₀ v₁ v₂).field i)) heₓ E hc

theorem inv_step_gproj {σ : Sigma} {G₁ : GlobName} {L : Program}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx} {v : Value} {g : GEntry}
    (hG₁ : Γ G₁ = some g) (hvi : g.field i = some v)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G₁ i)))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv

    have hP : ∀ (G' : GlobName) K, KJR G' σ L H S (Expr.val v) K →
        ∃ K', KJR G' σ L H S (Expr.gproj G₁ i) K' ∧ K ⊆ K' := by
      intro G' K hK
      cases hK
      refine ⟨σ.GFld i G₁, .gproj, ?_⟩
      intro q hq
      cases v with
      | loc ℓ' =>
        cases hHℓ' : H ℓ' with
        | none => simp [Heap.opOf, hHℓ'] at hq
        | some c' =>
          simp [Heap.opOf, hHℓ'] at hq
          subst hq
          obtain ⟨c'', hH'', hmem⟩ := hgtable G₁ g hG₁ i ℓ' hvi
          rw [hHℓ'] at hH''
          cases hH''
          exact hmem
      | btrue => simp [Heap.opOf] at hq
      | bfalse => simp [Heap.opOf] at hq

    refine ⟨hparam, hfld, hgtable, ?_, ?_, ?_, hrm, hthisinv, hframe, ?_, hinit, ?_, hfclosed, hclosedinit⟩
    · -- RetInv: Using hP (G.i is inside original K) and KJR.plug_mono for plug
      intro G' i' cfs' r' hti' htiG' t p κ htc D hHt K hK
      obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
      exact hsub.trans (hret G' i' cfs' r' hti' htiG' t p κ htc D hHt K' hK')
    · -- ArgInv
      intro G' i' cfs' r' htop' htiG'
      exact RuntimeParamFldThisSound.plug_mono (eₓ := Expr.val v)
        trivial (hP G') E (harg G' i' cfs' r' htop' htiG')
    · -- CallInv: same transport, via `CallSound.plug_mono`.
      intro G' i' cfs' r' htop' htiG'
      exact CallSound.plug_mono (eₓ := Expr.val v)
        trivial (hP G') E (hcall G' i' cfs' r' htop' htiG')
    · -- GInitInv:
      intro G' ifr r hti htiG' i₁ hi₁ K hK
      obtain ⟨K', hK', hsub⟩ := KJR.plug_mono (hP G') E K hK
      exact hsub.trans (hgi G' ifr r hti htiG' i₁ hi₁ K' hK')
    · -- Closed: Use plug_mono. hex is proved by hgtable
      have heₓ : Closed H (Expr.val v) := by
        cases v with
        | loc ℓ' =>
          obtain ⟨c', hH', -⟩ := hgtable G₁ g hG₁ i ℓ' hvi
          show (H ℓ').isSome
          rw [hH']
          rfl
        | btrue => trivial
        | bfalse => trivial
      exact Closed.plug_mono (eₓ := Expr.val v) heₓ E hc

theorem inv_step_app {σ : Sigma} {L : Program} {G G₀ : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {eₐ : Expr} {l : Loc} {v v₁ v₂ : Value}
    {C : ClassName} {ifr : Frame} {icfs ir : Stack}
    (hti₀ : S.topInit = some (ifr, icfs, ir)) (htiG₀ : ifr.glob = some G)
    (hHl : H l = some (ClsIns.mk C G₀ v₁ v₂))
    (hbody : Program.HasClass L C eₐ) (hbvf : ValueFree eₐ) (hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val v))))) :
    Inv σ L (.mk H Γ (Stack.push (Frame.call l v E) S) eₐ) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hcall, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv

    have hGglob : ∀ {i₀ : Frame} {cfs₀ r₀ : Stack}, S.topInit = some (i₀, cfs₀, r₀) →
        i₀.glob = some G := fun h => Stack.topInit_glob_eq hti₀ htiG₀ h

    have hfresh : ∀ i₀ cfs₀ r₀, S.topInit = some (i₀, cfs₀, r₀) →
        G₀ ∈ σ.This G C ∧ H.opOf v ⊆ σ.Param G C ∧ C ∈ σ.RM G := by
      intro i₀ cfs₀ r₀ htopS
      refine ⟨?_, ?_, ?_⟩
      · obtain ⟨-, -, hbound⟩ :=
          RuntimeParamFldThisSound.of_plug E (harg G i₀ cfs₀ r₀ htopS (hGglob htopS))
        exact (hbound _ _ .val .val (G₀, C) (by simp [Heap.opOf, hHl])).2
      · obtain ⟨-, -, hbound⟩ :=
          RuntimeParamFldThisSound.of_plug E (harg G i₀ cfs₀ r₀ htopS (hGglob htopS))
        exact (hbound _ _ .val .val (G₀, C) (by simp [Heap.opOf, hHl])).1
      · obtain ⟨-, -, hbound⟩ := CallSound.of_plug E (hcall G i₀ cfs₀ r₀ htopS (hGglob htopS))
        exact hbound _ .val (mem_classes.mpr ⟨G₀, by simp [Heap.opOf, hHl]⟩)

    have hbridge : ∀ i₀ cfs₀ r₀, S.topInit = some (i₀, cfs₀, r₀) →
        (∀ C', (some C : Ctx) = some C' →
          ∀ K, KJR G σ L H (Stack.push (Frame.call l v E) S) Expr.thisE K →
            K ⊆ ⋃ G' ∈ σ.This G C', {(G', C')}) ∧
        (∀ C', (some C : Ctx) = some C' →
          ∀ K, KJR G σ L H (Stack.push (Frame.call l v E) S) Expr.paramE K →
            K ⊆ σ.Param G C') := by
      intro i₀ cfs₀ r₀ htopS
      obtain ⟨hGthis, hvparam, -⟩ := hfresh i₀ cfs₀ r₀ htopS
      constructor
      · intro C' hC' K hK
        obtain rfl : C = C' := Option.some.inj hC'
        cases hK with
        | thisE htc =>
          simp only [Stack.push, Stack.topCall, Option.some.injEq,
            Frame.call.injEq] at htc
          obtain ⟨rfl, -, -⟩ := htc
          intro q hq
          simp only [Heap.opOf, hHl, Set.mem_singleton_iff] at hq
          subst hq
          exact Set.mem_biUnion hGthis rfl
      · intro C' hC' K hK
        obtain rfl : C = C' := Option.some.inj hC'
        cases hK with
        | paramE htc =>
          simp only [Stack.push, Stack.topCall, Option.some.injEq,
            Frame.call.injEq] at htc
          obtain ⟨-, rfl, -⟩ := htc
          exact hvparam

    have hpin : ∀ G' i' cfs' r',
        (Stack.push (Frame.call l v E) S).topInit = some (i', cfs', r') →
        i'.glob = some G' →
        ∃ i₀ cfs₀ r₀, S.topInit = some (i₀, cfs₀, r₀) ∧ G' = G := by
      intro G' i' cfs' r' hti' htiG'
      obtain ⟨cfs₀, -, htopS⟩ := Stack.topInit_cons_call hti'
      exact ⟨i', cfs₀, r', htopS, Option.some.inj (htiG'.symm.trans (hGglob htopS))⟩

    refine ⟨?_, hfld, hgtable, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p₁ κ G₁ C₁ hsub hti htG hf htC₁ ℓ hpℓ
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · obtain ⟨cfs₀, rfl, htopS⟩ := Stack.topInit_cons_call hti
        rcases List.mem_cons.mp hf with heq | hf₀
        · -- `f` is the freshly pushed frame: `t = l`, `p₁ = v`.
          injection heq with ht hp hκ
          rw [ht] at htC₁
          rw [hHl] at htC₁
          cases htC₁
          have hvℓ : v = Value.loc ℓ := hp.symm.trans hpℓ
          have hG₁G : G₁ = G := Option.some.inj (htG.symm.trans (hGglob htopS))
          rw [hG₁G]
          have hAS : RuntimeParamFldThisSound G σ L H S
              (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val v))) :=
            harg G i cfs₀ r htopS (hGglob htopS)
          obtain ⟨-, -, hbound⟩ := RuntimeParamFldThisSound.of_plug E hAS

          cases hHℓ : H ℓ with
          | none => -- false
            have hcl : Closed H (Expr.val v) := (Closed.of_plug E hc).2
            rw [hvℓ] at hcl
            simp [Closed, hHℓ] at hcl
          | some D =>
            exact ⟨D, rfl, (hbound _ _ .val .val (G₀, C)
              (by simp [Heap.opOf, hHl])).1 (by simp [Heap.opOf, hvℓ, hHℓ])⟩
        · exact hparam S i cfs₀ r t p₁ κ G₁ C₁ (List.suffix_refl S) htopS htG
            hf₀ htC₁ ℓ hpℓ
      · exact hparam S' i cfs r t p₁ κ G₁ C₁ hsub hti htG hf htC₁ ℓ hpℓ
    · -- RetInv
      intro G' i' cfs' r' hti' htiG t p k htc D hD
      obtain ⟨i₀, cfs₀, r₀, htopS, rfl⟩ := hpin G' i' cfs' r' hti' htiG
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      simp only [Stack.push, Stack.topCall, Option.some.injEq, Frame.call.injEq] at htc
      obtain ⟨rfl, -, -⟩ := htc
      rw [hHl] at hD
      obtain rfl := Option.some.inj hD
      intro K hK
      obtain ⟨K', hK', hsub⟩ :=
        KJR.to_kjc (c := some C) hthisB hparamB (fun hc => nomatch hc) hbvf hK
      exact hsub.trans (hσ.ret_init hbody hK')
    · -- RuntimeParamFldThisInv
      intro G' i' cfs' r' hti' htiG
      obtain ⟨i₀, cfs₀, r₀, htopS, rfl⟩ := hpin G' i' cfs' r' hti' htiG
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      obtain ⟨-, -, hRM⟩ := hfresh i₀ cfs₀ r₀ htopS
      exact RuntimeParamFldThisSound.of_re hσ hthisB hparamB eₐ (RE.body hRM hbody)
        (fun hc => nomatch hc) hbvf
    · -- CallInv
      intro G' i' cfs' r' hti' htiG
      obtain ⟨i₀, cfs₀, r₀, htopS, hG'G⟩ := hpin G' i' cfs' r' hti' htiG
      rw [hG'G]
      obtain ⟨hthisB, hparamB⟩ := hbridge i₀ cfs₀ r₀ htopS
      obtain ⟨-, -, hRM⟩ := hfresh i₀ cfs₀ r₀ htopS
      obtain ⟨Kc, hcalls⟩ := Calls.total (G := G) (C := C) (σ := σ) (L := L) eₐ
      exact CallSound.of_calls hthisB hparamB hcalls
        (hσ.rm_closed hRM hbody hcalls) hbvf
    · -- RMInv
      intro S' i cfs r f G' l₁ hsub hti htiG' hf hfl₁
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · obtain ⟨cfs₀, rfl, htopS⟩ := Stack.topInit_cons_call hti
        rcases List.mem_cons.mp hf with rfl | hf₀
        · -- `f` is the freshly pushed frame
          have hG'G : G' = G := Option.some.inj (htiG'.symm.trans (hGglob htopS))
          subst hG'G
          simp [Frame.loc] at hfl₁
          subst hfl₁
          refine ⟨_, hHl, ?_⟩
          obtain ⟨-, -, hbound⟩ :=
            CallSound.of_plug E (hcall _ i cfs₀ r htopS (hGglob htopS))
          exact hbound _ .val (mem_classes.mpr ⟨G₀, by simp [Heap.opOf, hHl]⟩)
        · exact hrm S i cfs₀ r f G' l₁ (List.suffix_refl S) htopS htiG' hf₀ hfl₁
      · exact hrm S' i cfs r f G' l₁ hsub hti htiG' hf hfl₁
    · -- ThisInv
      intro S' i cfs r t p₁ κ G₁ hsub hti htG hf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · obtain ⟨cfs₀, rfl, htopS⟩ := Stack.topInit_cons_call hti
        rcases List.mem_cons.mp hf with heq | hf₀
        · -- `f` is the freshly pushed frame
          injection heq with ht hp hκ
          rw [ht]
          have hG₁G : G₁ = G := Option.some.inj (htG.symm.trans (hGglob htopS))
          rw [hG₁G]
          obtain ⟨hGthis, -, -⟩ := hfresh i cfs₀ r htopS
          exact ⟨_, hHl, hGthis⟩
        · exact hthisinv S i cfs₀ r t p₁ κ G₁ (List.suffix_refl S) htopS htG hf₀
      · exact hthisinv S' i cfs r t p₁ κ G₁ hsub hti htG hf
    · -- FrameInv
      intro S' t p E₁ hsub G' i  cfs r hS'ti hS'tiG' redex
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · injection heq with hf hS
        injection hf with ht hp hE
        subst ht; subst hp; subst hE; subst hS
        exact ⟨hret G' i cfs r hS'ti hS'tiG',
               harg G' i cfs r hS'ti hS'tiG',
               hcall G' i cfs r hS'ti hS'tiG',
               hgi⟩
      · exact hframe S' t p E₁ hsub' G' i cfs r hS'ti hS'tiG'
    · -- GInitInv: vacuous: ifr ≠ []
      intro G' ifr r hti htiG' i₁ hi₁ K hK
      cases htopS : S.topInit with
      | none => simp [Stack.push, Stack.topInit, htopS] at hti
      | some x =>
        obtain ⟨f, calls, rest⟩ := x
        simp [Stack.push, Stack.topInit, htopS] at hti
    · -- InitFrameInv: the freshly pushed `Frame.call` is not an init frame, so
      -- every init frame of the new stack sits *inside* `S` with the same stack
      -- `S'` below it — the constructor-clash case (the init frame being the
      -- pushed call frame) is impossible — so reroute through the pre-state's
      -- `InitFrameInv` (`hinit`).
      intro S' G' k hsub
      apply hinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · rcases List.suffix_cons_iff.mp h with heq | hsub'
        · simp at heq
        · exact Or.inl ⟨e, hsub'⟩
      · rcases List.suffix_cons_iff.mp h with heq | hsub'
        · simp at heq
        · exact Or.inr hsub'
    · -- Closed
      exact Closed.of_valueFree eₐ hbvf
    · -- FrameClosedInv: the pushed frame `call l v E` stores the continuation `E`,
      -- whose push-time focus `E[l(v)]` is the (closed) pre-state focus `hc`;
      -- every older frame sits in `S` and reroutes through `hfclosed`.
      intro S' t p E' hsub
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · injection heq with hf hS
        injection hf with ht hp hE'
        subst ht; subst hp; subst hE'
        exact hc
      · exact hfclosed S' t p E' hsub'
    · -- InitFrameClosedInv: the freshly pushed `Frame.call` is not an init frame,
      -- so every init frame of the new stack sits inside `S`; the constructor-clash
      -- head case is impossible and the tail reroutes through `hclosedinit`.
      intro S' G' k hsub
      apply hclosedinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · rcases List.suffix_cons_iff.mp h with heq | hsub'
        · simp at heq
        · exact Or.inl ⟨e, hsub'⟩
      · rcases List.suffix_cons_iff.mp h with heq | hsub'
        · simp at heq
        · exact Or.inr hsub'

theorem inv_step_ret {σ : Sigma} {L : Program} {Gₒ : GlobName}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {l : Loc} {v v₁ v₂ p : Value}
    {C : ClassName} (hHl : H l = some (ClsIns.mk C Gₒ v₁ v₂))
    (hinv : Inv σ L (.mk H Γ ((Frame.call l p E)::S) (Expr.val v))) :
    Inv σ L (.mk H Γ S (E.plug (Expr.val v))) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv
    -- Covering, shared by the Ret/Arg/Call/ThisSound cases below: under `S`'s
    -- topInit guard, every K-set of the returned value lies inside a K-set of
    -- the popped frame's redex `l(p)`.  The bound `H.opOf v ⊆ σ.Ret G' C` is
    -- the pre-state `hret` at the popped frame (the pre-stack's top call
    -- frame, receiver `l` a `C`-instance), and `KJR.app KJR.val` reproduces
    -- it as the redex's K-set, the union over the singleton `{(Gₒ, C)}`.
    have hcov : ∀ G' i cfs r, S.topInit = some (i, cfs, r) →
        i.glob = some G' → ∀ K, KJR G' σ L H S (Expr.val v) K →
          ∃ K', KJR G' σ L H S
            (Expr.app (Expr.val (Value.loc l)) (Expr.val p)) K' ∧ K ⊆ K' := by
      intro G' i cfs r hti htiG'
      -- The guard lifts to the pre-state stack unchanged: its topmost init
      -- frame is `S`'s own `i`, with the popped frame prepended to the
      -- call-frame list, so `htiG'` serves both stacks.
      have hval : H.opOf v ⊆ σ.Ret G' C := by
        have hbnd :=
          hret G' i (Frame.call l p E :: cfs) r (Stack.topInit_push_call hti) htiG'
            l p E rfl _ hHl
        exact hbnd (H.opOf v) KJR.val
      have hmem : (Gₒ, C) ∈ H.opOf (Value.loc l) := by simp [Heap.opOf, hHl]
      intro K hK
      cases hK
      exact ⟨_, KJR.app KJR.val, fun x hx => Set.mem_biUnion hmem (hval hx)⟩
    refine ⟨?_, hfld, hgtable, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G' C' hsub hti htiG' hfc htc' l hpl
      exact hparam S' i cfs r t p κ G' C' (hsub.trans (List.suffix_cons _ _)) hti htiG' hfc htc' l hpl
    · -- RetInv: the resumed focus `E.plug (val v)` against the next call
      -- frame down.  `FrameInv` at the popped frame bounds the K-sets of the
      -- push-time focus `E.plug (l(p))` over `S`, and `KJR.plug_mono`
      -- transports the value covering `hcov` through `E`.
      intro G' i cfs r hti htiG' t' p' κ' htc D hHt K hK
      obtain ⟨hKbound, -, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      obtain ⟨K', hK', hsubK⟩ :=
        KJR.plug_mono (hcov G' i cfs r hti htiG') E K hK
      exact hsubK.trans (hKbound t' p' κ' htc D hHt K' hK')
    · -- ArgInv: `FrameInv`'s second conjunct is `RuntimeParamFldThisSound` of the push-time
      -- focus over `S`; `RuntimeParamFldThisSound.plug_mono` transports it through the value
      -- covering (`RuntimeParamFldThisSound` of the bare value is `True`).
      intro G' i cfs r hti htiG'
      obtain ⟨-, hargF, -, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hAS : RuntimeParamFldThisSound G' σ L H S (Expr.val v) := trivial
      exact RuntimeParamFldThisSound.plug_mono hAS (hcov G' i cfs r hti htiG') E hargF
    · -- CallInv
      intro G' i cfs r hti htiG'
      obtain ⟨-, -, hcallF, -⟩ :=
        hframe S l p E (List.suffix_refl _) G' i cfs r hti htiG'
      have hCS : CallSound G' σ L H S (Expr.val v) := trivial
      exact CallSound.plug_mono hCS (hcov G' i cfs r hti htiG') E hcallF
    · -- RMInv
      intro S' i cfs r f G' l hsub hti htiG' hf hfl
      exact hrm S' i cfs r f G' l (hsub.trans (List.suffix_cons _ _)) hti htiG' hf hfl
    · -- ThisInv: the stack only shrank; reroute through the pre-state's
      -- `ThisInv` at the suffix.
      intro S' i cfs r t p κ G₁ hsub hti htiG₁ hf
      exact hthisinv S' i cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
        hti htiG₁ hf
    · -- FrameInv: the stack only shrank, so every call frame of `S` is a
      -- call frame of the pre-state stack, with the same stack below it;
      -- reroute through `hframe` at the extended suffix.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG'
      exact hframe S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
        G' i cfs r hS'ti hS'tiG'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      let cfs : Stack := List.nil
      obtain ⟨-, -, -, hGii⟩ :=
        hframe S l p E (List.suffix_refl _) G' ifr cfs r hti htiG'
      obtain ⟨K', hK', hsubK⟩ :=
        KJR.plug_mono (hcov G' ifr cfs r hti htiG') E K hK
      exact hsubK.trans (hGii G' ifr r hti htiG' j hj K' hK')
    · -- InitFrameInv
      intro S' G' k hsub
      apply hinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · exact Or.inl ⟨e, h.trans (List.suffix_cons _ _)⟩
      · exact Or.inr (h.trans (List.suffix_cons _ _))
    · -- Closed: `FrameClosedInv` at the popped frame gives closedness of the
      -- push-time focus `E[l(p)]`; `plug_mono` swaps the redex for the returned
      -- value `v` (closed by `hc`), yielding closedness of the resumed focus.
      have hEclosed : Closed H (E.plug (Expr.app (Expr.val (Value.loc l)) (Expr.val p))) :=
        hfclosed S l p E (List.suffix_refl _)
      exact Closed.plug_mono (eₓ := Expr.val v) hc E hEclosed
    · -- FrameClosedInv: the stack only shrank, so every call frame of `S` is a
      -- call frame of the pre-state stack; reroute through `hfclosed`.
      intro S' t' p' E₁ hsub
      exact hfclosed S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
    · -- InitFrameClosedInv: dually, every init frame of `S` is an init frame of
      -- the pre-state stack; reroute through `hclosedinit`.
      intro S' G' k hsub
      apply hclosedinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · exact Or.inl ⟨e, h.trans (List.suffix_cons _ _)⟩
      · exact Or.inr (h.trans (List.suffix_cons _ _))

theorem inv_step_alloc {σ : Sigma} {G : GlobName} {L : Program} {v₁ v₂ : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {l : Loc} {C: ClassName}
    {ifr : Frame} {icfs ir : Stack}
    (hti₀ : S.topInit = some (ifr, icfs, ir)) (htiG₀ : ifr.glob = some G)
    (hG : (Γ G).isSome)
    (hHl : H l = none) (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.newC C v₁ v₂))))
    : Inv σ L (.mk (Heap.update H l (ClsIns.mk C G v₁ v₂)) Γ S (E.plug (Expr.val (Value.loc l)))) := by
    obtain ⟨hparam, hfld, hgtable, hret, harg, hci, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hclosedinit⟩ := hinv
    -- `topInit` is a function, so the guard `htiG₀` names the glob of *any*
    -- decomposition of `S` the invariants hand us.
    have hGglob : ∀ {i₀ : Frame} {cfs₀ r₀ : Stack}, S.topInit = some (i₀, cfs₀, r₀) →
        i₀.glob = some G := fun h => Stack.topInit_glob_eq hti₀ htiG₀ h
    -- The allocation only grows the heap at the fresh `l`, which is distinct
    -- from every location already bound.
    have hgrow : ∀ ℓ o, H ℓ = some o →
        (H[l ↦ ClsIns.mk C G v₁ v₂]) ℓ = some o := by
      intro ℓ o hℓ
      have hℓl : ℓ ≠ l := by intro h; rw [h, hHl] at hℓ; simp at hℓ
      simpa [Heap.update, hℓl] using hℓ
    -- The `topCall` receiver and argument are allocated in the old heap (`hrm`
    -- / `hparam`), hence distinct from the fresh `l`, so the growth leaves their
    -- `opOf` unchanged — the stack-agreement hypothesis of `KJR.heap_congr`.
    have hstk : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
        H.opOf (Value.loc t) = (H[l ↦ ClsIns.mk C G v₁ v₂]).opOf (Value.loc t) ∧
        H.opOf p = (H[l ↦ ClsIns.mk C G v₁ v₂]).opOf p := by
      exact RMInv.opOf_update_fresh hrm hparam hHl (List.suffix_refl _) hti₀ htiG₀
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i' cfs r t p κ G' C' hsub hti htiG' hfc hHt ℓ hpℓ
      obtain ⟨Ct, hHt₀, -⟩ :=
        hrm S' i' cfs r (Frame.call t p κ) G' t hsub hti htiG' hfc rfl
      have htl : t ≠ l := by
        intro h; rw [h, hHl] at hHt₀; simp at hHt₀
      have hHt' : H t = some C' := by simpa [Heap.update, htl] using hHt
      -- The old `hparam` witnesses the argument `ℓ` in the *old* heap, so `ℓ`
      -- is allocated there and hence distinct from the fresh `l`; the previous
      -- `ℓ = l` "dangling" gap cannot arise under the `∃`-form.
      obtain ⟨D, hHD, hmem⟩ :=
        hparam S' i' cfs r t p κ G' C' hsub hti htiG' hfc hHt' ℓ hpℓ
      have hℓl : ℓ ≠ l := by
        intro h; rw [h, hHl] at hHD; simp at hHD
      exact ⟨D, by simpa [Heap.update, hℓl] using hHD, hmem⟩
    · -- FldInv
      intro G' l' C' v₁' v₂' hHl'
      refine ⟨?_, ?_⟩
      · -- Owner `G'` of the object at `l'` is initialized.  For old objects this
        -- is the `.1` of the inductive `hfld`; for the fresh `l` it is the
        -- ambient global of the reachable `new C(e₁,e₂)`, which the rule's
        -- `topInit` guard guarantees is initialized.
        by_cases hEq : G' = G
        · subst hEq
          exact hG
        · -- `G' ≠ G`: the object at `l'` is not the freshly allocated one (whose
          -- owner is `G`), so `l' ≠ l` and the grown heap reads back `H` there.
          have hl' : l' ≠ l := by
            rintro rfl
            simp [Heap.update] at hHl'
            obtain ⟨rfl, rfl, rfl, rfl⟩ := hHl'
            exact hEq rfl
          rw [Heap.lookup_update_ne hl'] at hHl'
          exact (hfld G' l' C' v₁' v₂' hHl').1
      · intro j ℓ' hfj
        by_cases hl' : l' = l
        · -- `l' = l` is the freshly allocated object: `C' = C`, `G' = G`, and its
          -- fields are the redex arguments `v₁ v₂`.  Missing: their classes lie
          -- in `σ.Fld j G C` — needs `hσ.fld_re` at the reachable `new C(e₁,e₂)`
          -- plus a runtime K-judgment bound on the already-reduced arguments.
          subst hl'
          simp [Heap.update] at hHl'
          obtain ⟨rfl, rfl, rfl, rfl⟩ := hHl'
          -- The field location `ℓ'` is one of the constructor arguments `v₁ v₂`.
          -- `ArgInv` at the reachable `new C(v₁,v₂)` bounds its runtime K-set
          -- `H.opOf vⱼ` by `σ.Fld j G C`, and `Closed` proves that argument
          -- location allocated; together they furnish the witness `c'`.
          obtain ⟨-, -, hbound⟩ :=
            RuntimeParamFldThisSound.of_plug E (harg G ifr icfs ir hti₀ htiG₀)
          have hb := hbound (H.opOf v₁) (H.opOf v₂) .val .val
          obtain ⟨hcl₁, hcl₂⟩ := Closed.of_plug E hc
          cases j with
          | one =>
            simp only [ClsIns.field] at hfj
            subst hfj
            have hs : (H ℓ').isSome := hcl₁
            obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hs
            have hℓ'l : ℓ' ≠ l' := by intro h; rw [h, hHl] at hc'; simp at hc'
            exact ⟨c', by simpa [Heap.update, hℓ'l] using hc',
              hb.1 (by simp [Heap.opOf, hc'])⟩
          | two =>
            simp only [ClsIns.field] at hfj
            subst hfj
            have hs : (H ℓ').isSome := hcl₂
            obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp hs
            have hℓ'l : ℓ' ≠ l' := by intro h; rw [h, hHl] at hc'; simp at hc'
            exact ⟨c', by simpa [Heap.update, hℓ'l] using hc',
              hb.2 (by simp [Heap.opOf, hc'])⟩
        · -- `l' ≠ l`: an old object, so its fields are old-heap locations
          -- (`hfld`), which are distinct from the fresh `l`.
          have hHl'' : H l' = some (ClsIns.mk C' G' v₁' v₂') := by
            simpa [Heap.update, hl'] using hHl'
          obtain ⟨c', hc', hcls⟩ := (hfld G' l' C' v₁' v₂' hHl'').2 j ℓ' hfj
          have hℓ'l : ℓ' ≠ l := by
            intro h; rw [h, hHl] at hc'; simp at hc'
          exact ⟨c', by simpa [Heap.update, hℓ'l] using hc', hcls⟩
    · -- GTableInv
      intro g o hg j ℓ' hoj
      obtain ⟨c', hc', hcls⟩ := hgtable g o hg j ℓ' hoj
      have hℓ'l : ℓ' ≠ l := by
        intro h; rw [h, hHl] at hc'; simp at hc'
      exact ⟨c', by simpa [Heap.update, hℓ'l] using hc', hcls⟩
    · -- RetInv
      intro G' i cfs r hti htiG' t p κ htc D hD
      have hf : Frame.call t p κ ∈ cfs := Stack.topCall_mem_topInit htc hti
      obtain ⟨D₀, hHt₀, -⟩ := hthisinv S i cfs r t p κ G' (List.suffix_refl _) hti htiG' hf
      have htl : t ≠ l := by
        intro h; subst h; rw [hHl] at hHt₀; simp at hHt₀
      rw [Heap.lookup_update_ne htl] at hD
      intro K hK
      -- The topmost init frame pins a single ambient global, so the owner `G`
      -- stored in the freshly allocated object equals `RetInv`'s `G'`.
      have hGG' : G = G' := Option.some.inj ((hGglob hti).symm.trans htiG')
      -- Hole covering across the heap growth: over the new heap the contractum
      -- `loc l` has K-set `{(G, C)}` (= `{(G', C)}`), which the redex `newC`'s
      -- `{(G', C)}` covers over the old heap.
      have hhole : ∀ K₀, KJR G' σ L (H[l ↦ ClsIns.mk C G v₁ v₂]) S
          (Expr.val (Value.loc l)) K₀ →
          ∃ K', KJR G' σ L H S (Expr.newC C (Expr.val v₁) (Expr.val v₂)) K' ∧ K₀ ⊆ K' := by
        intro K₀ hK₀
        cases hK₀
        refine ⟨{(G', C)}, .newC, ?_⟩
        subst hGG'
        have hl' : (H[l ↦ ClsIns.mk C G v₁ v₂]) l = some (ClsIns.mk C G v₁ v₂) := by
          simp [Heap.update]
        simp [Heap.opOf, hl']
      obtain ⟨K', hK', hsub⟩ :=
        KJR.plug_mono_grow hgrow hhole E K hc hK
      exact hsub.trans (hret G' i cfs r hti htiG' t p κ htc D hD K' hK')
    · -- ArgInv: the contractum `loc l` is a value (trivially `RuntimeParamFldThisSound`), and
      -- over the new heap its K-set `{(G', C)}` is covered by the redex `newC`'s
      -- `{(G', C)}`; `RuntimeParamFldThisSound.plug_mono_grow` transports the old focus's
      -- `RuntimeParamFldThisSound` across the heap growth (`hgrow`/`hstk`) and the rewrite.
      intro G' i cfs r hti htiG'
      have hGG' : G = G' := Option.some.inj ((hGglob hti).symm.trans htiG')
      refine RuntimeParamFldThisSound.plug_mono_grow hgrow hstk (eₓ := Expr.val (Value.loc l)) trivial
        ?_ E hc (harg G' i cfs r hti htiG')
      intro K hK
      cases hK
      refine ⟨{(G', C)}, .newC, ?_⟩
      subst hGG'
      simp [Heap.opOf, Heap.update]
    · -- CallInv
      intro G' i cfs r hti htiG'
      have hcsr := hci G' i cfs r hti htiG'
      have hGG' : G = G' := Option.some.inj ((hGglob hti).symm.trans htiG')
      refine CallSound.plug_mono_grow (eₓ := Expr.val (Value.loc l)) trivial hgrow hstk ?_ E hc hcsr
      intro K hK
      cases hK
      refine ⟨{(G', C)}, .newC, ?_⟩
      subst hGG'
      simp [Heap.opOf, Heap.update]
    · -- RMInv: the stack is unchanged and every receiver it mentions is
      -- allocated in the old heap (`hrm`), hence distinct from the fresh `l`.
      intro S' i' cfs r f G' l₁ hsub hti htiG' hf hfl₁
      obtain ⟨C₀, hC₀, hcls⟩ := hrm S' i' cfs r f G' l₁ hsub hti htiG' hf hfl₁
      have hl₁l : l₁ ≠ l := by
        intro h; rw [h, hHl] at hC₀; simp at hC₀
      exact ⟨C₀, by simpa [Heap.update, hl₁l] using hC₀, hcls⟩
    · -- ThisInv: the stack is unchanged and every receiver it mentions is
      -- allocated in the old heap (`hrm`), so the update at the fresh `l` is
      -- invisible.
      intro S' i' cfs r t p κ G₁ hsub hti htiG₁ hfc
      obtain ⟨Ct, hHt₀, -⟩ :=
        hrm S' i' cfs r (Frame.call t p κ) G₁ t hsub hti htiG₁ hfc rfl
      have htl : t ≠ l := by
        intro h; rw [h, hHl] at hHt₀; simp at hHt₀
      obtain ⟨D, hHt', hmem⟩ := hthisinv S' i' cfs r t p κ G₁ hsub hti htiG₁ hfc
      exact ⟨D, by simpa [Heap.update, htl] using hHt', hmem⟩
    · -- FrameInv
      intro S' t p E' hsub G' i cfs r hS'ti hS'tiG' redex
      have hsubS : S' <:+ S := (List.suffix_cons _ _).trans hsub
      -- Every call receiver / argument above `S'`'s init frame is allocated in the
      -- old heap (`hrm` / `hparam`), hence distinct from the freshly-allocated `l`,
      -- so the update leaves their `opOf` untouched.  This side condition feeds every
      -- `heap_congr` below, so establish it once here.
      have hstk' := RMInv.opOf_update_fresh (o := ClsIns.mk C G v₁ v₂)
        hrm hparam hHl hsubS hS'ti hS'tiG'
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- RetInv
        intro t' p' k' hS'tc D' hD' K hK
        -- The receiver `t` is old, so the given `D` also lives in the old heap.
        have hf : Frame.call t' p' k' ∈ cfs := Stack.topCall_mem_topInit hS'tc hS'ti
        obtain ⟨Ct, hHt, -⟩ :=
          hrm S' i cfs r (Frame.call t' p' k') G' t' hsubS hS'ti hS'tiG' hf rfl
        have htl : t' ≠ l := by intro h; rw [h, hHl] at hHt; simp at hHt
        have hte : (H[l ↦ ClsIns.mk C G v₁ v₂]) t' = H t' := by simp [Heap.update, htl]
        have hDold : H t' = some D' := hte ▸ hD'
        have hK' : KJR G' σ L H S' (E'.plug redex) K :=
          KJR.heap_congr hgrow hstk' (hfclosed S' t p E' hsub) hK
        exact (hframe S' t p E' hsub G' i cfs r hS'ti hS'tiG').1 t' p' k' hS'tc D' hDold K hK'
      · -- RuntimeParamFldThisSound: the frame's redex/context are unchanged and
        -- only the heap grew.  The pre-state `hframe` supplies the soundness over
        -- the old heap (`.2.1`), and `RuntimeParamFldThisSound.heap_congr`
        -- transports it across the growth — the stack-agreement side condition
        -- holds because every call receiver / argument above `S'`'s init frame is
        -- allocated in the old heap (`hrm` / `hparam`), hence distinct from `l`.
        exact RuntimeParamFldThisSound.heap_congr hgrow hstk' (hfclosed S' t p E' hsub)
          ((hframe S' t p E' hsub G' i cfs r hS'ti hS'tiG').2.1)
      · exact CallSound.heap_congr hgrow hstk' (hfclosed S' t p E' hsub)
          ((hframe S' t p E' hsub G' i cfs r hS'ti hS'tiG').2.2.1)
      · -- GInitInv
        intro G₁ ifr r₀ hti htiG₁ j hj K hK
        have hK' : KJR G₁ σ L H S' (E'.plug redex) K :=
          KJR.heap_congr hgrow hstk' (hfclosed S' t p E' hsub) hK
        exact (hframe S' t p E' hsub G' i cfs r hS'ti hS'tiG').2.2.2
          G₁ ifr r₀ hti htiG₁ j hj K hK'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      have hGG' : G = G' := Option.some.inj ((hGglob hti).symm.trans htiG')
      subst hGG'
      have hK' : ∃ K', KJR G σ L H S (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂))) K' ∧ K ⊆ K' := by
        refine KJR.plug_mono_grow hgrow (eₓ := Expr.val (Value.loc l)) ?_ E K hc hK
        intro K₁ hK₁
        cases hK₁
        refine ⟨{(G, C)}, .newC, ?_⟩
        simp [Heap.opOf, Heap.update]
      obtain ⟨K', hK'⟩ := hK'
      exact hK'.2.trans (hgi G ifr r hti htiG' j hj K' hK'.1)
    · -- InitFrameInv
      intro S' G' k hsub
      have hsubS : S' <:+ S := by
        rcases hsub with ⟨e, h⟩ | h
        · exact (List.suffix_cons _ _).trans h
        · exact (List.suffix_cons _ _).trans h
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- RetInv
        intro G₁ i cfs r hti htiG₁ t p κ htc D hD K hK
        have hstk' := RMInv.opOf_update_fresh (o := ClsIns.mk C G v₁ v₂)
          hrm hparam hHl hsubS hti htiG₁
        -- The receiver `t` is old, so the given `D` also lives in the old heap.
        have hf : Frame.call t p κ ∈ cfs := Stack.topCall_mem_topInit htc hti
        obtain ⟨Ct, hHt, -⟩ :=
          hrm S' i cfs r (Frame.call t p κ) G₁ t hsubS hti htiG₁ hf rfl
        have htl : t ≠ l := by intro h; rw [h, hHl] at hHt; simp at hHt
        have hte : (H[l ↦ ClsIns.mk C G v₁ v₂]) t = H t := by simp [Heap.update, htl]
        have hDold : H t = some D := hte ▸ hD
        have hK' : KJR G₁ σ L H S' k K :=
          KJR.heap_congr hgrow hstk' (hclosedinit S' G' k hsub) hK
        exact (hinit S' G' k hsub).1 G₁ i cfs r hti htiG₁ t p κ htc D hDold K hK'
      · -- RuntimeParamFldThisInv
        intro G₁ i cfs r hti htiG₁
        have hstk' := RMInv.opOf_update_fresh (o := ClsIns.mk C G v₁ v₂)
          hrm hparam hHl hsubS hti htiG₁
        exact RuntimeParamFldThisSound.heap_congr hgrow hstk' (hclosedinit S' G' k hsub)
          ((hinit S' G' k hsub).2.1 G₁ i cfs r hti htiG₁)
      · -- CallInv
        intro G₁ i cfs r hti htiG₁
        have hstk' := RMInv.opOf_update_fresh (o := ClsIns.mk C G v₁ v₂)
          hrm hparam hHl hsubS hti htiG₁
        exact CallSound.heap_congr hgrow hstk' (hclosedinit S' G' k hsub)
          ((hinit S' G' k hsub).2.2.1 G₁ i cfs r hti htiG₁)
      · -- GInitInv
        intro G₁ ifr r hti htiG₁ j hj K hK
        have hstk' : ∀ t p κ, S'.topCall = some (Frame.call t p κ) →
            H.opOf (Value.loc t) = (H[l ↦ ClsIns.mk C G v₁ v₂]).opOf (Value.loc t)
              ∧ H.opOf p = (H[l ↦ ClsIns.mk C G v₁ v₂]).opOf p := by
          intro t p κ htc
          exact absurd (Stack.topCall_mem_topInit htc hti) (by simp)
        have hK' : KJR G₁ σ L H S' k K :=
          KJR.heap_congr hgrow hstk' (hclosedinit S' G' k hsub) hK
        exact (hinit S' G' k hsub).2.2.2 G₁ ifr r hti htiG₁ j hj K hK'
    · -- Closed
      have hcr : Closed H[l ↦ { cls := C, g := G, f₁ := v₁, f₂ := v₂ }]
        (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂))) := Closed.mono hgrow hc
      refine Closed.plug_mono (eₓ := Expr.val (Value.loc l)) (eᵣ := Expr.newC C (Expr.val v₁) (Expr.val v₂)) ?_ E hcr
      show (H[l ↦ { cls := C, g := G, f₁ := v₁, f₂ := v₂ }] l).isSome
      rw [Heap.update]
      simp
    · -- FrameClosedInv: heap growth preserves closedness of every stored call
      -- continuation (`Closed.mono` along `hgrow`); the stack `S` is unchanged.
      intro S' t p E hsub
      exact Closed.mono hgrow (hfclosed S' t p E hsub)
    · -- InitFrameClosedInv: heap growth preserves closedness of every stored init
      -- continuation (`Closed.mono` along `hgrow`).
      intro S' G' k hsub
      exact Closed.mono hgrow (hclosedinit S' G' k hsub)

theorem inv_step_ipush {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program}
    {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {i : Idx}
    (hG : Program.HasObject L G e₁ e₂) (hnewG : Γ G = none)
    (hpf₁ : ContextFree e₁) (hvf₁ : ValueFree e₁) (hpf₂ : ContextFree e₂)
    (hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S (E.plug (Expr.gproj G i))))
    : Inv σ L (.mk H Γ[G↦ ⟨none, none⟩] ((Frame.init1 G e₂ (E.plug (Expr.gproj G i))) :: S) e₁) := by
    obtain ⟨hparam, hfld, hgtable, hret, hpft, hcall, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hifclosed⟩ := hinv
    have hpin : ∀ {G₀ : GlobName} {i' : Frame} {cfs' r' : Stack},
        Stack.topInit ((Frame.init1 G e₂ (E.plug (Expr.gproj G i))) :: S) = some (i', cfs', r') →
        i'.glob = some G₀ → G = G₀ := by
      intro G₀ i' cfs' r' htop hgl
      simp [Stack.topInit] at htop
      obtain ⟨rfl, -, -⟩ := htop
      simpa [Frame.glob] using hgl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv: rcases htop rfl tells us there are no call frames above the new init frame, so vacuous
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases htop with ⟨_, rfl, _⟩
        simp at hcall
      · exact hparam S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
    · -- FldInv: the heap is unchanged, so the field-typing half is exactly the
      -- old `hfld`.  The GTable only *gains* the key `G` (mapped to
      -- `⟨none, none⟩`), so `(Γ[G↦…] G₁).isSome` holds regardless of whether
      -- `G₁ = G`: if `G₁ ≠ G` the entry is untouched, and if `G₁ = G` the
      -- update itself makes it `some`.  No "nothing is owned by `G`" invariant
      -- is required.
      intro G₁ l C v₁ v₂ hHl
      obtain ⟨hsome, hfield⟩ := hfld G₁ l C v₁ v₂ hHl
      refine ⟨?_, hfield⟩
      by_cases hEq : G₁ = G
      · subst hEq; simp [GTable.update]
      · simpa [GTable.update, hEq] using hsome
    · -- GTableInv
      intro g o HGo i ℓ' hi
      by_cases hEq : g = G
      · subst hEq
        have HGo' : some ⟨none, none⟩ = some o := by
          simpa [GTable.update] using HGo
        cases HGo'
        cases i <;> simp [GEntry.field] at hi
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ i ℓ' hi
    · -- RetInv: the pushed `init1` frame hides any call frame, so `topCall`
      -- is `none` and the obligation is vacuous.
      intro G₀ i' cfs' r' hti' hTop t p κ htc
      simp [Stack.topCall] at htc
    · -- ArgInv: the topmost init frame is now `G`'s own, pinning the ambient
      -- global to `G`, and the new focus is `G`'s first initializer —
      -- reachable (`RE.init₁`) initializer code, so `RuntimeParamFldThisSound.of_re` applies
      -- at the empty context (the stack-consulting hypotheses are vacuous).
      intro G₀ i' cfs' r' htop' hTopG₀
      obtain rfl := hpin htop' hTopG₀
      exact RuntimeParamFldThisSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₁ (RE.init₁ hG) (fun _ => hpf₁) hvf₁
    · -- CallInv: the topmost init frame is now `G`'s own, pinning the ambient
      -- global to `G`, and the new focus is `G`'s first initializer, whose
      -- `Calls0` set `rm_init` puts inside `σ.RM G` — `CallSound.of_calls0`.
      intro G₀ i' cfs' r' htop' hTopG₀
      obtain rfl := hpin htop' hTopG₀
      obtain ⟨K₁, hc₁⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₁ hpf₁
      obtain ⟨K₂, hc₂⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₂ hpf₂
      exact CallSound.of_calls0 hc₁
        (Set.subset_union_left.trans (hσ.rm_init hG hc₁ hc₂)) hpf₁ hvf₁
    · -- RMInv
      intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hf
      · exact hrm S' i cfs r f G₁ l hsub hti hG₁ hf hfl
    · -- ThisInv: the pushed `init1` frame carries no call frames above it,
      -- and the suffixes of `S` are rerouted through the pre-state.
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hcf
      · exact hthisinv S' i' cfs r t p κ G₁ hsub hti hTopG hcf
    · -- FrameInv: the pushed `init1` frame is not a call frame, so the
      -- suffix's `Frame.call` head can only sit inside `S`; reroute through
      -- `hframe`.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG' redex
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · -- The head would have to be the pushed `init1` frame — constructor
        -- clash, so this branch is vacuous.
        injection heq with hf hS
        exact absurd hf (by simp)
      · -- The frame sits inside `S`: reroute through `hframe`.
        exact hframe S' t' p' E₁ hsub' G' i cfs r hS'ti hS'tiG'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      obtain rfl := hpin hti htiG'
      simp [Stack.topInit] at hti
      obtain ⟨rfl, -, -⟩ := hti
      simp [Frame.idx] at hj
      subst hj
      obtain ⟨K', hK', hsub⟩ := KJR.to_kjc (c := none) (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) (fun _ => hpf₁) hvf₁ hK
      exact hsub.trans (hσ.gfld_init_one hG hK')
    · -- InitFrameInv
      intro S' G' k hsub
      rcases hsub with ⟨e, h⟩ | h
      · -- an `init1` frame.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · injection heq with hh hS
          injection hh with hg he hk
          rw [hS, hk]
          refine ⟨ ?_, ?_, ?_, ?_⟩
          · exact hret
          · exact hpft
          · exact hcall
          · exact hgi
        · -- inside `S`: reroute through the pre-state `hinit` (over `S` directly).
          exact hinit S' G' k (Or.inl ⟨e, h'⟩)
      · -- an `init2` frame: it cannot be the pushed `init1` head, so it lies in `S`.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · exact absurd heq (by simp)
        · exact hinit S' G' k (Or.inr h')
    · -- Closed
      exact Closed.of_valueFree e₁ hvf₁
    · -- FrameClosedInv
      intro S' t p E' hsub
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · -- the head would have to be the pushed `init1` frame — constructor clash.
        exact absurd heq (by simp)
      · exact hfclosed S' t p E' hsub'
    · -- InitFrameClosedInv
      intro S' G' k hsub
      rcases hsub with ⟨e, h1⟩ | h2
      · rcases List.suffix_cons_iff.mp h1 with heq | hsub'
        · -- the pushed head: `k = E.plug (gproj G i)` is the pre-state focus,
          -- whose closedness is `hc` (heap unchanged).
          injection heq with hh hS
          injection hh with hg he hk
          rw [hk]
          exact hc
        · exact hifclosed S' G' k (Or.inl ⟨e, hsub'⟩)
      · rcases List.suffix_cons_iff.mp h2 with heq | hsub'
        · exact absurd heq (by simp)
        · exact hifclosed S' G' k (Or.inr hsub')

theorem inv_step_inext {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program} {v : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {κ : Expr}
    (hG : Program.HasObject L G e₁ e₂) (hnewG : Γ G = some ⟨none, none⟩)
    (hpf₁ : ContextFree e₁) (hvf₂ : ValueFree e₂) (hpf₂ : ContextFree e₂)
    (hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ ((Frame.init1 G e₂ κ) :: S) (Expr.val v)))
    : Inv σ L (.mk H Γ[G↦ ⟨v, none⟩] ((Frame.init2 G κ) :: S) e₂) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hifclosed⟩ := hinv
    have hpin : ∀ {G₀ : GlobName} {i' : Frame} {cfs' r' : Stack},
        Stack.topInit ((Frame.init2 G κ) :: S) = some (i', cfs', r') →
        i'.glob = some G₀ → G = G₀ := by
      intro G₀ i' cfs' r' htop hgl
      simp [Stack.topInit] at htop
      obtain ⟨rfl, -, -⟩ := htop
      simpa [Frame.glob] using hgl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases htop with ⟨_, rfl, _⟩
        simp at hcall
      · exact hparam S' i cfs r t p κ G₁ C (hsub.trans (List.suffix_cons _ _)) htop hTopG hcall hHt
    · -- FldInv
      intro G₁ l C v₁ v₂ hHl
      obtain ⟨hsome, hfield⟩ := hfld G₁ l C v₁ v₂ hHl
      refine ⟨?_, ?_⟩
      · by_cases hEq : G₁ = G
        · subst hEq; simp [GTable.update]
        · simpa [GTable.update, hEq] using hsome
      · exact (hfld G₁ l C v₁ v₂ hHl).2
    · -- GTableInv: `G`'s first field is now `v`; entries other than `G` are
      -- untouched, so the old `hgtable` covers them.  For `G`'s first field the
      -- stored value is the old focus `v`, whose runtime K-set the *pre-state*
      -- `GInitInv` (`hgi`, over the `init1` stack) bounds by `σ.GFld one G` —
      -- reading `one` off the topmost `init1` frame.  When `v = loc ℓ'` points
      -- to an allocated object that bound is exactly the required owner-pair
      -- membership; a dangling `v` (`H ℓ' = none`) is the same closedness gap
      -- left open in `inv_step_alloc`.
      intro g o HGo j ℓ' hj
      by_cases hEq : g = G
      · subst hEq
        have HGo' : (⟨v, none⟩ : GEntry) = o := by simpa [GTable.update] using HGo
        subst HGo'
        cases j with
        | one =>
          -- `⟨v, none⟩.field one = v`, so `hj : v = loc ℓ'`.
          simp [GEntry.field] at hj
          subst hj
          -- Pre-state `GInitInv` on the `init1` stack bounds `v = loc ℓ'`.
          have hbound : H.opOf (Value.loc ℓ') ⊆ σ.GFld Idx.one g := by
            refine hgi g (Frame.init1 g e₂ κ) S
              (by simp [Stack.topInit]) ?_ Idx.one ?_ (H.opOf (Value.loc ℓ')) KJR.val
            · -- the topmost init frame is `G`'s own
              rfl
            · -- its index is `one`
              rfl
          cases hHℓ' : H ℓ' with
          | some c' =>
            exact ⟨c', rfl, hbound (by simp [Heap.opOf, hHℓ'])⟩
          | none =>
            simp [Closed, hHℓ'] at hc
        | two => simp [GEntry.field] at hj
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ j ℓ' hj
    · -- RetInv: the `init2` frame hides any call frame, so `topCall` is
      -- `none` and the obligation is vacuous.
      intro G₀ i' cfs' r' hti' hTop t p κ htc
      simp [Stack.topCall] at htc
    · -- ArgInv: the topmost init frame is still `G`'s own, and the new focus
      -- is `G`'s second initializer — reachable (`RE.init₂`) initializer
      -- code, so `RuntimeParamFldThisSound.of_re` applies at the empty context.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      exact RuntimeParamFldThisSound.of_re (c := none) hσ (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) e₂ (RE.init₂ hG) (fun _ => hpf₂) hvf₂
    · -- CallInv: the topmost init frame is still `G`'s own, and the new focus
      -- is `G`'s second initializer, whose `Calls0` set `rm_init` puts inside
      -- `σ.RM G` — `CallSound.of_calls0`.
      intro G₀ i' cfs' r' htop' hTopG₀
      have hgl := hTopG₀
      simp [Stack.topInit] at htop'
      obtain ⟨rfl, -, -⟩ := htop'
      simp [Frame.glob] at hgl
      subst hgl
      obtain ⟨K₁, hc₁⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₁ hpf₁
      obtain ⟨K₂, hc₂⟩ := Calls0.total (G := G) (σ := σ) (L := L) e₂ hpf₂
      exact CallSound.of_calls0 hc₂
        (Set.subset_union_right.trans (hσ.rm_init hG hc₁ hc₂)) hpf₂ hvf₂
    · -- RMInv: No call frames
      intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hf
      · exact hrm S' i cfs r f G₁ l (hsub.trans (List.suffix_cons _ _)) hti hG₁ hf hfl
    · -- ThisInv: the pushed `init2` frame carries no call frames above it,
      -- and the suffixes of `S` are rerouted through the pre-state (whose
      -- stack extends `S` by the popped `init1` frame).
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf
      rcases List.suffix_cons_iff.mp hsub with rfl | hsub
      · rcases hti with ⟨_, rfl, _⟩
        simp at hcf
      · exact hthisinv S' i' cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
          hti hTopG hcf
    · -- FrameInv: the pushed `init2` frame is not a call frame, so the
      -- suffix's `Frame.call` head can only sit inside `S`, itself a suffix
      -- of the pre-state stack; reroute through `hframe`.
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG' redex
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · injection heq with hf hS
        exact absurd hf (by simp)
      · exact hframe S' t' p' E₁ (hsub'.trans (List.suffix_cons _ _))
          G' i cfs r hS'ti hS'tiG'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      obtain rfl := hpin hti htiG'
      simp [Stack.topInit] at hti
      obtain ⟨rfl, -, -⟩ := hti
      simp [Frame.idx] at hj
      subst hj
      obtain ⟨K', hK', hsub⟩ := KJR.to_kjc (c := none) (fun _ hc => nomatch hc)
        (fun _ hc => nomatch hc) (fun _ => hpf₂) hvf₂ hK
      exact hsub.trans (hσ.gfld_init_two hG hK')
    · -- InitFrameInv: the continuation `k` is threaded unchanged from the popped
      -- `init1 G e₂ κ` frame to the pushed `init2 G κ` frame (`κ = E[G.i]`).  A
      -- frame recorded by the post-state either *is* that pushed `init2 G κ`
      -- head — whose continuation `κ` the pre-state's own `init1` frame carried,
      -- so reroute through `hinit`'s `init1` disjunct at `suffix_refl` — or sits
      -- strictly inside `S`, hence below the pre-state's `init1` frame too.
      intro S' G' k hsub
      rcases hsub with ⟨e, h⟩ | h
      · -- an `init1` frame: it cannot be the pushed `init2` head, so it lies in `S`.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · exact absurd heq (by simp)
        · exact hinit S' G' k (Or.inl ⟨e, h'.trans (List.suffix_cons _ _)⟩)
      · -- an `init2` frame: either the pushed head or a frame inside `S`.
        rcases List.suffix_cons_iff.mp h with heq | h'
        · -- the pushed head: `G' = G`, `k = κ`, `S' = S`; the pre-state's own
          -- `init1 G e₂ κ` frame carried this same continuation.
          injection heq with hf hS
          injection hf with hG' hk
          rw [hS, hk]
          exact hinit S G κ
            (Or.inl ⟨e₂, List.suffix_refl _⟩)
        · exact hinit S' G' k (Or.inr (h'.trans (List.suffix_cons _ _)))
    · -- Closed
      exact Closed.of_valueFree e₂ hvf₂
    · -- FrameClosedInv
      intro S' t p E' hsub
      rcases List.suffix_cons_iff.mp hsub with heq | hsub'
      · -- the head would have to be the pushed `init1` frame — constructor clash.
        exact absurd heq (by simp)
      · exact hfclosed S' t p E' (hsub'.trans (List.suffix_cons _ _))
    · -- InitFrameClosedInv
      intro S' G' k hsub
      rcases hsub with ⟨e, h1⟩ | h2
      · rcases List.suffix_cons_iff.mp h1 with heq | hsub'
        · exact absurd heq (by simp)
        · exact hifclosed S' G' k (Or.inl ⟨e, (hsub'.trans (List.suffix_cons _ _))⟩)
      · rcases List.suffix_cons_iff.mp h2 with heq | hsub'
        · -- the pushed `init2 G κ` head: `k = κ = E.plug (gproj G i)`.  Its
          -- closedness is carried by the pre-state's own `init1 G e₂ κ` frame
          -- (`hifclosed`), not the pre-state focus `val v`.
          injection heq with hh hS
          injection hh with hg hk
          rw [hk]
          exact hifclosed S G κ (Or.inl ⟨e₂, List.suffix_refl _⟩)
        · exact hifclosed S' G' k (Or.inr (hsub'.trans (List.suffix_cons _ _)))

theorem inv_step_ipop {σ : Sigma} {e₁ e₂ : Expr} {G : GlobName} {L : Program} {v₁ v₂ : Value}
    {H : Heap} {Γ : GTable} {S : Stack} {κ : Expr}
    (hG : Program.HasObject L G e₁ e₂) (hnewG : Γ G = some ⟨v₁, none⟩)
    (hinv : Inv σ L (.mk H Γ ((Frame.init2 G κ) :: S) (Expr.val v₂)))
    : Inv σ L (.mk H Γ[G↦ ⟨v₁, v₂⟩] S κ) := by
    obtain ⟨hparam, hfld, hgtable, hret, -, -, hrm, hthisinv, hframe, hgi, hinit, hc, hfclosed, hifclosed⟩ := hinv
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- ParamInv
      intro S' i cfs r t p κ G₁ C hsub htop hTopG hcall hHt
      exact hparam S' i cfs r t p κ G₁ C (hsub.trans (List.suffix_cons _ _)) htop hTopG hcall hHt
    · -- FldInv: the heap is unchanged, so the field-typing half is exactly the
      -- old `hfld`.  The GTable only overwrites the key `G` (with `⟨v₁, v₂⟩`),
      -- so `(Γ[G↦…] G₁).isSome` holds regardless of whether `G₁ = G`: if
      -- `G₁ ≠ G` the entry is untouched, and if `G₁ = G` the update itself
      -- makes it `some`.
      intro G₁ l C v₁ v₂ hHl
      obtain ⟨hsome, hfield⟩ := hfld G₁ l C v₁ v₂ hHl
      refine ⟨?_, hfield⟩
      by_cases hEq : G₁ = G
      · subst hEq; simp [GTable.update]
      · simpa [GTable.update, hEq] using hsome
    · -- GTableInv: entries other than `G` are untouched (old `hgtable`).  `G`'s
      -- first field still holds the pre-state `v₁` (old `hgtable` at `G`); its
      -- second field is the freshly stored `v₂` — the popped focus `val v₂` —
      -- whose runtime K-set the pre-state `GInitInv` (`hgi`, reading `two` off
      -- the `init2` frame) bounds by `σ.GFld two g`.  A dangling `v₂`
      -- (`H ℓ' = none`) is ruled out by the pre-state focus-closedness `hc`.
      intro g o HGo j ℓ' hj
      by_cases hEq : g = G
      · subst hEq
        have HGo' : some (⟨v₁, v₂⟩ : GEntry) = some o := by
          simpa [GTable.update] using HGo
        cases HGo'
        cases j with
        | one =>
          -- `v₁` was already recorded in the pre-state entry `G(v₁, ⊥)`, so
          -- this is the old `hgtable` instance at `G`.
          exact hgtable g ⟨v₁, none⟩ hnewG Idx.one ℓ'
            (by simpa [GEntry.field] using hj)
        | two =>
          -- `⟨v₁, v₂⟩.field two = v₂`, so `hj : v₂ = loc ℓ'`.
          simp [GEntry.field] at hj
          subst hj
          have hbound : H.opOf (Value.loc ℓ') ⊆ σ.GFld Idx.two g := by
            refine hgi g (Frame.init2 g κ) S
              (by simp [Stack.topInit]) ?_ Idx.two ?_ (H.opOf (Value.loc ℓ')) KJR.val
            · -- the topmost init frame is `g`'s own
              rfl
            · -- its index is `two`
              rfl
          cases hHℓ' : H ℓ' with
          | some c' =>
            exact ⟨c', rfl, hbound (by simp [Heap.opOf, hHℓ'])⟩
          | none =>
            -- `v₂ = loc ℓ'` is the popped focus, so pre-state closedness `hc`
            -- keeps `ℓ'` allocated: `H ℓ' = none` is impossible.
            simp [Closed, hHℓ'] at hc
      · have hΓ : Γ g = some o := by
          simpa [GTable.update, hEq] using HGo
        exact hgtable g o hΓ j ℓ' hj
    · -- RetInv
      intro G' ifr cfs r hti htiG' t p k htc D hD K hK
      have hk : RetInv σ L H S κ :=
        (hinit S G κ (Or.inr (List.suffix_refl _))).1
      exact hk G' ifr cfs r hti htiG' t p k htc D hD K hK
    · -- ArgInv
      intro G' ifr cfs r hti htiG'
      exact (hinit S G κ (Or.inr (List.suffix_refl _))).2.1
        G' ifr cfs r hti htiG'
    · -- CallInv
      intro G' ifr cfs r hti htiG'
      exact (hinit S G κ (Or.inr (List.suffix_refl _))).2.2.1
        G' ifr cfs r hti htiG'
    · intro S' i cfs r f G₁ l hsub hti hG₁ hf hfl
      exact hrm S' i cfs r f G₁ l (hsub.trans (List.suffix_cons _ _)) hti hG₁ hf hfl
    · -- ThisInv
      intro S' i' cfs r t p κ G₁ hsub hti hTopG hcf
      exact hthisinv S' i' cfs r t p κ G₁ (hsub.trans (List.suffix_cons _ _))
        hti hTopG hcf
    · -- FrameInv
      intro S' t' p' E₁ hsub G' i cfs r hS'ti hS'tiG'
      exact hframe S' t' p' E₁ (hsub.trans (List.suffix_cons _ _))
        G' i cfs r hS'ti hS'tiG'
    · -- GInitInv
      intro G' ifr r hti htiG' j hj K hK
      have hk : GInitInv σ L H S κ :=
        (hinit S G κ (Or.inr (List.suffix_refl _))).2.2.2
      exact hk G' ifr r hti htiG' j hj K hK
    · -- InitFrameInv
      intro S' G' k hsub
      apply hinit S' G' k
      rcases hsub with ⟨e, h⟩ | h
      · exact Or.inl ⟨e, h.trans (List.suffix_cons _ _)⟩
      · exact Or.inr (h.trans (List.suffix_cons _ _))
    · -- Closed
      exact hifclosed S G κ (by simp)
    · -- FrameClosedInv
      intro S' t p E' hsub
      exact hfclosed S' t p E' (hsub.trans (List.suffix_cons _ _))
    · -- InitFrameClosedInv: a stored continuation of `S` is also stored in the
      -- pre-state stack `(init2 G κ) :: S` — lift through `List.suffix_cons`.
      intro S' G' k hsub
      rcases hsub with ⟨e, h⟩ | h
      · exact hifclosed S' G' k (Or.inl ⟨e, h.trans (List.suffix_cons _ _)⟩)
      · exact hifclosed S' G' k (Or.inr (h.trans (List.suffix_cons _ _)))

theorem inv_preservation_step {L : Program} {S S' : Stack} {σ : Sigma} {H H' : Heap}
    {Γ Γ' : GTable} {e e' : Expr} (hσ : FixPoint σ L)
    (hinv : Inv σ L (.mk H Γ S e)) (hstep : Step L (.mk H Γ S e) (.mk H' Γ' S' e')) :
    Inv σ L (.mk H' Γ' S' e') := by
  cases hstep with
  | this htcSome htC                    => exact inv_step_this htcSome htC hinv
  | param htcSome htC                   => exact inv_step_param htcSome htC hinv
  | proj hHl                            => exact inv_step_proj hHl hinv
  | gproj hG hv                         => exact inv_step_gproj hG hv hinv
  | methCall hti htiG hHl hcls hbody   => exact inv_step_app hti htiG hHl hcls hbody hσ hinv
  | ret hHl                             => exact inv_step_ret hHl hinv
  | newAlloc hti htiG hGSome hHl       => exact inv_step_alloc hti htiG hGSome hHl hinv
  | ipush hobj hG hcf₁ hvf hcf₂         => exact inv_step_ipush hobj hG hcf₁ hvf hcf₂ hσ hinv
  | inext hobj hG hcf₁ hvf hcf₂         => exact inv_step_inext hobj hG hcf₁ hvf hcf₂ hσ hinv
  | ipop hobj hG                        => exact inv_step_ipop hobj hG hinv

theorem inv_preservation_step' {L : Program} {σ : Sigma} {c c' : Config}
    (hσ : FixPoint σ L) (hinv : Inv σ L c) (hstep : Step L c c') : Inv σ L c' := by
  cases c with
  | crash => cases hstep
  | mk H Γ S e =>
    cases c' with
    | crash => trivial
    | mk H' Γ' S' e' => exact inv_preservation_step hσ hinv hstep

theorem inv_preservation_star {L : Program} {σ : Sigma} {c c' : Config}
    (hσ : FixPoint σ L) (hstar : Star L c c') (hinv : Inv σ L c) : Inv σ L c' := by
  induction hstar with
  | refl => exact hinv
  | head hstep _ ih => exact ih (inv_preservation_step' hσ hinv hstep)

theorem inv_preservation {G : GlobName} {L : Program} {S : Stack}
    {σ : Sigma} {H : Heap} {Γ : GTable} {e : Expr}
    (hσ : FixPoint σ L)
    (hstar : Star L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj G Idx.one)) (.mk H Γ S e)) :
    Inv σ L (.mk H Γ S e) := by
  have hinv : Inv σ L (.mk (fun _ => none) (fun _ => none) List.nil (Expr.gproj G Idx.one)) := inv_empty
  exact inv_preservation_star hσ hstar hinv

end Proof
