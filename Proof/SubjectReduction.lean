import Proof.Semantics
import Proof.Analysis
import Proof.Theorem1

/-
  Subject reduction, take 2 — the `k_abstracts` lemma and the invariant it
  needs.

  This file supersedes the `Inv` machinery of `Theorem1.lean` (it does not
  import it: `Theorem1.lean` currently has unrelated build errors in
  `inv_step_gproj`/`inv_step_app`, and the definitions here are meant to
  replace `ParamInv`/`FldInv`/`GTableInv`/`RetInv`/`RMInv`/`Inv` there).
  Once adopted, delete those definitions from `Theorem1.lean` and add this
  module to `Proof.lean` — until then it must not be imported together with
  `Theorem1.lean`, or the names will clash.

  Changes relative to `Theorem1.lean`, each forced by a Lean-verified
  counterexample to the previous `k_abstracts` statement:

  1. `ValueFree` / `ValueFreeProgram`: the paper's convention that values occur
     only in runtime foci, never in source programs, is now a hypothesis.
     Without it, `L = [class C0 { apply = val ℓ }]` makes `val ℓ` reachable
     (`RE.body`), `KJ.val` assigns it `∅`, and the zero-step run refutes
     `k_abstracts` even under a full `Inv`.

  2. `KJR`: the runtime `⇓ᴷ` of a focus expression — `Theorem1.lean`'s `KJ0R`
     generalized from values to expressions.  A location's class set is read
     off the heap; compound expressions follow the static `KJ0` rules; `this`
     and `param` are read off the top call frame of the stack (`E-AppBeta`
     runs bodies unsubstituted, so the frame *is* their runtime meaning).  The
     static `KJ`/`KJ0` are degenerate on runtime foci (values map to `∅`), so
     the invariant must speak `KJR` instead.

  3. `RetKInv` replaces `RetInv`: when the stack has a pending call frame, the
     *whole focus*'s runtime `⇓ᴷ` — not just a bare returned value — is bounded
     by `σ.Ret` for the frame's receiver class.  `RetInv` is exactly its value
     case (`RetKInv.val_case` below).  This is the component whose absence made
     the `E-Proj`/hole case of `inv_step_proj` underivable.
-/

namespace Proof

/-! ### Value-freeness of source programs

  Values are runtime-only: the expression grammar admits `Expr.val`, but source
  programs (class bodies and object initialisers) must not contain it.  `RE`
  produces only source expressions, so under `ValueFreeProgram` every reachable
  expression is value-free (`RE.valueFree`). -/

/-- Well-formedness of a program: every class body and every object
    initialiser is value-free. -/
structure ValueFreeProgram (L : Program) : Prop where
  cls : ∀ {C body}, Program.HasClass L C body → ValueFree body
  obj : ∀ {G e₁ e₂}, Program.HasObject L G e₁ e₂ → ValueFree e₁ ∧ ValueFree e₂

/-- A value-free expression is not a value, so a `Star` from a reachable
    expression to a value takes at least one step. -/
theorem ValueFree.ne_val {e : Expr} (h : ValueFree e) : ∀ v, e ≠ Expr.val v := by
  intro v hv
  subst hv
  simp [ValueFree] at h

/-- Reachable expressions of a well-formed program are value-free.  (This is
    what rules out the counterexample where a class body is a value literal.) -/
theorem RE.valueFree {σ : Sigma} {L : Program} {G : GlobName} {c : Ctx} {e : Expr}
    (hwf : ValueFreeProgram L) (h : RE σ L G c e) : ValueFree e := by
  induction h with
  | init₁ h => exact (hwf.obj h).1
  | init₂ h => exact (hwf.obj h).2
  | body _ hcls => exact hwf.cls hcls
  | proj _ ih => exact ih
  | newC₁ _ ih => exact ih.1
  | newC₂ _ ih => exact ih.2
  | app₁ _ ih => exact ih.1
  | app₂ _ ih => exact ih.2

/-! ### Runtime `⇓ᴷ` of a focus expression

  `Theorem1.lean`'s `KJ0R` generalized from values to expressions: a value
  gets the actual class of the heap object it points to (via `Heap.clsOf`),
  compound expressions follow the static `KJ0` rules, and — because
  `E-AppBeta` runs a body unsubstituted, recording the receiver and argument
  in the pushed call frame — `this` and `param` are read off the top call
  frame of the stack: `this` is the class of the frame's receiver `t`,
  `param` the class of its argument `p`.  Outside a call (no top call frame)
  `this`/`param` have no derivation, matching their being stuck.
  `L` is carried for uniformity with the static judgments. -/

/-- The class set a value denotes in heap `H`: the actual class of the object
    an allocated location points to; `∅` for unallocated locations and
    booleans. -/
def Heap.clsOf (H : Heap) : Value → Set ClassName
  | Value.loc ℓ =>
    match H ℓ with
    | some o => {o.cls}
    | none   => ∅
  | Value.btrue  => ∅
  | Value.bfalse => ∅

inductive KJR (G : GlobName) (σ : Sigma) (L : Program) (H : Heap) (S : Stack) :
    Expr → Set ClassName → Prop
  | val {v} : KJR G σ L H S (Expr.val v) (H.clsOf v)
  | thisE {t p κ} :
      S.topCall = some (Frame.call t p κ) →
      KJR G σ L H S Expr.thisE (H.clsOf (Value.loc t))
  | paramE {t p κ} :
      S.topCall = some (Frame.call t p κ) →
      KJR G σ L H S Expr.paramE (H.clsOf p)
  | proj {e i K} :
      KJR G σ L H S e K → KJR G σ L H S (Expr.proj e i) (⋃ D ∈ K, σ.Fld i G D)
  | gproj {G₀ i} : KJR G σ L H S (Expr.gproj G₀ i) (σ.GFld i G₀)
  | newC {D e₁ e₂} : KJR G σ L H S (Expr.newC D e₁ e₂) {D}
  | app {e₁ e₂ K₁} :
      KJR G σ L H S e₁ K₁ → KJR G σ L H S (Expr.app e₁ e₂) (⋃ D ∈ K₁, σ.Ret G D)

/-- `KJR` is deterministic. -/
theorem KJR.det {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ {e K K'}, KJR G σ L H S e K → KJR G σ L H S e K' → K = K'
  | _, _, _, .val, .val => rfl
  | _, _, _, .thisE htc, .thisE htc' => by rw [htc] at htc'; cases htc'; rfl
  | _, _, _, .paramE htc, .paramE htc' => by rw [htc] at htc'; cases htc'; rfl
  | _, _, _, .proj h, .proj h' => by rw [KJR.det h h']
  | _, _, _, .gproj, .gproj => rfl
  | _, _, _, .newC, .newC => rfl
  | _, _, _, .app h, .app h' => by rw [KJR.det h h']

/-- On value-free expressions in the *initializer* context the runtime and
    static `⇓ᴷ` coincide: `KJR` only diverges from `KJ0` at value leaves, and
    `KJ0` has no `this`/`param` rules.  This is how the static `hKj` of
    `k_abstracts` is converted into the runtime bound at the start
    configuration when `e` is initializer code. -/
theorem KJ0.toKJR {G : GlobName} {σ : Sigma} {L : Program} {H : Heap} {S : Stack} :
    ∀ {e K}, KJ0 G σ L e K → ValueFree e → KJR G σ L H S e K := by
  intro e K h
  induction h with
  | proj _ ih => intro hvf; exact .proj (ih hvf)
  | gproj => intro _; exact .gproj
  | newC => intro _; exact .newC
  | app _ ih => intro hvf; exact .app (ih hvf.1)
  | val => intro hvf; simp [ValueFree] at hvf

/-- The *method-body* context analogue of `KJ0.toKJR`, as a bound rather than
    an equality: if the stack's current receiver is `D` (`Stack.This`) and the
    top call frame's argument class is inside `σ.Param G D.cls` (the runtime
    reading of `ParamInv` for the top frame), then the runtime `⇓ᴷ` of a
    value-free `e` refines its static `⇓ᴷ` in context `D.cls`.  A bound and
    not an equality because `this ⇓ᴷ {D.cls}` and `param ⇓ᴷ σ.Param G D.cls`
    are static over-approximations of the single runtime classes. -/
theorem KJ.kjr_subset {G : GlobName} {σ : Sigma} {L : Program} {H : Heap}
    {S : Stack} {D : ClsIns} (hD : Stack.This S H D)
    (hparam : ∀ t p κ, S.topCall = some (Frame.call t p κ) →
      H.clsOf p ⊆ σ.Param G D.cls) :
    ∀ {e K}, KJ G D.cls σ L e K → ValueFree e →
      ∀ {K'}, KJR G σ L H S e K' → K' ⊆ K := by
  intro e K h
  induction h with
  | thisE =>
      intro _ K' h'
      cases h' with
      | thisE htc =>
          rename_i t p κ
          have hHt : H t = some D := hD t (by simp [Stack.this, htc])
          simp [Heap.clsOf, hHt]
  | paramE =>
      intro _ K' h'
      cases h' with
      | paramE htc =>
          rename_i t p κ
          exact hparam t p κ htc
  | proj _ ih =>
      intro hvf K' h'
      cases h' with
      | proj h₀ => exact Set.biUnion_subset_biUnion_left (ih hvf h₀)
  | gproj =>
      intro _ K' h'
      cases h' with
      | gproj => exact subset_refl _
  | newC =>
      intro _ K' h'
      cases h' with
      | newC => exact subset_refl _
  | app _ ih =>
      intro hvf K' h'
      cases h' with
      | app h₀ => exact Set.biUnion_subset_biUnion_left (ih hvf.1 h₀)
  | val => intro hvf; simp [ValueFree] at hvf

/-- Ret soundness of the focus against a pending call frame, `⇓ᴷ`-aware:
    whenever the top of the stack is a call frame with receiver `t` of class
    `D`, the *runtime* `⇓ᴷ` of the whole focus is bounded by `σ.Ret G D.cls`.
    The old `RetInv` is the special case where the focus is already a value
    (`RetKInv.val_case`); stating it for arbitrary foci is what survives the
    induction — e.g. `E-Proj` shrinks the focus `ℓ.i` (with runtime `⇓ᴷ`
    `Fldᵢ(G, cls ℓ)`) to the field value, whose class `FldInv` puts back inside
    that same set. -/
def RetKInv (σ : Sigma) (L : Program) (H : Heap) (S : Stack) (e : Expr) : Prop :=
  ∀ G, Stack.TopInit S G
    → ∀ t p κ, S.topCall = some (Frame.call t p κ) → ∀ D, H t = some D
      → ∀ K, KJR G σ L H S e K → K ⊆ σ.Ret G D.cls

/-! ### `k_abstracts` -/

/-- **`⇓ᴷ` abstracts run-time classes.**  Under a fixpoint `σ` of the analysis
    on a value-free program, if a reachable expression `e` (in the class
    context `D.cls` of the current receiver) reduces — at the same stack
    level — to a location `l`, then the class of the object at `l` in the
    final heap lies in the static `⇓ᴷ` of `e`.

    Hypotheses, each necessary (Lean-verified counterexamples otherwise):
    `hσ` ties `σ` to `L`; `hwf` rules out value literals in source code (else
    `RE` reaches a `val` whose `⇓ᴷ` is `∅`); `hinv` ties the running heap,
    global table and stack to `σ` (else an arbitrary `Γ` feeds `E-GProj`
    garbage); `hre`/`hKj` place `e` and its `⇓ᴷ` in the context `D.cls` of
    the receiver recorded by the stack (`hD`).

    Proof plan: convert `hKj` to the runtime bound "every `KJR` of the focus
    is `⊆ K`" — via `KJ.kjr_subset` for the method-body context `D.cls`
    (feeding it `hD` and the top frame's `Param`-soundness from `hinv`), or
    `KJ0.toKJR` for initialiser code — then induct on `hred`, showing each
    `Step` preserves `Inv` and shrinks the focus's `KJR` (same-level steps) or
    re-establishes it from `FixPoint` (`E-AppBeta`/`E-Ret`/`I-*`, via
    `ret_init`, `param_re`, `rm_closed` and `RetKInv`).  At the final
    configuration `KJR` of `val (loc l)` is `{C.cls}` by `hH'l`.

    **v3 REFUTED (2026-07-09, `KAbstractsCheck3.lean`, two Lean-verified
    counterexamples):**

    (A) *Danglers*: `Inv` never requires stored locations to be allocated, so
    `Γ` may hold a dangling `loc 5` (`GTableInv` vacuous); `E-NewAlloc`'s only
    freshness premise is `H ℓ = none`, so the run may allocate at that very
    `ℓ = 5`, laundering a class `σ` never saw into a focus with `⇓ᴷ = ∅`.
    Fix: add a closedness component to `Inv` (all locations occurring in the
    focus, stack frames, heap fields and `Γ` entries are allocated).

    (B) *Cross-global field flow* — a gap in the paper's Step 2f, not just in
    `Inv`: objects allocated during `G₀`'s initialization get their fields
    bounded only in `Fldᵢ((G₀,·))` (`fld_re` fires on `RE G₀`); code reachable
    from `G₁` receiving them via `G₀.i ⇓ᴷ GFldᵢ(G₀)` projects fields through
    `Fldᵢ((G₁,·))`, and no `FixPoint` rule relates the two.  Fix: extend
    `FixPoint` (and paper Step 2f) with an import rule, e.g.
    `RE σ L G c (gproj G₀ i) → ∀ j D, σ.Fld j G₀ D ⊆ σ.Fld j G D`. -/
theorem k_abstracts {σ : Sigma} {L : Program} {e : Expr} {H H' : Heap}
    {Γ Γ' : GTable} {S : Stack} {l : Loc} {C D : ClsIns} {G : GlobName}
    {K : Set ClassName}
    (hσ : FixPoint σ L) (hwf : ValueFreeProgram L)
    (hG : Stack.TopInit S G) (hD : Stack.This S H D)
    (hinv : Inv σ (.mk H Γ S e))
    (hre : RE σ L G D.cls e)
    (hred : Star L (.mk H Γ S e) (.mk H' Γ' S (Expr.val (Value.loc l))))
    (hH'l : H' l = some C)
    (hKj : KJC G σ L D.cls e K) :
    C.cls ∈ K :=




    sorry

end Proof
