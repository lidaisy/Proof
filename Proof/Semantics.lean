import Proof.Syntax

namespace Proof

/-- A heap object `o ::= C(v₁, v₂)`. -/
structure ClsIns where
  cls : ClassName
  g : GlobName
  f₁  : Value
  f₂  : Value
  deriving Repr

def ClsIns.field : ClsIns → Idx → Value
  | c, Idx.one => c.f₁
  | c, Idx.two => c.f₂

def ClsIns.glob : ClsIns → GlobName
  | c => c.g

def ClsMethBody (L : Program) (c : ClassName) : Option Expr :=
  match L with
  | [] => none
  | Def.cls d :: ds => if d.name = c then some d.body else ClsMethBody ds c
  | Def.obj _ :: ds => ClsMethBody ds c

/-- A heap `H` maps locations to objects (`none` = not allocated). -/
abbrev Heap := Loc → Option ClsIns

/-- A global field value `u ::= v | ⊥`; `none` is `⊥`. -/
abbrev GVal := Option Value

/-- A global-table entry `G(u₁, u₂)`. -/
structure GEntry where
  u₁ : GVal
  u₂ : GVal
  deriving Repr

def GEntry.field : GEntry → Idx → GVal
  | g, Idx.one => g.u₁
  | g, Idx.two => g.u₂

/-- A global table `Γ` maps global names to entries (`none` = `G ∉ dom Γ`). -/
abbrev GTable := GlobName → Option GEntry

def Heap.update (H : Heap) (ℓ : Loc) (o : ClsIns) : Heap :=
  fun ℓ' => if ℓ' = ℓ then some o else H ℓ'

def GTable.update (Γ : GTable) (G : GlobName) (g : GEntry) : GTable :=
  fun G' => if G' = G then some g else Γ G'

/-- `H[ℓ ↦ o]`. -/
notation:max H "[" ℓ " ↦ " o "]" => Heap.update H ℓ o
/-- `Γ[G(u₁,u₂)]` for in-place update of the entry of `G`. -/
notation:max Γ "[" G "↦ " g "]" => GTable.update Γ G g

/-! ### Evaluation contexts (call-by-value)

  `E ::= [] | E.i | E(e) | v(E) | new(E, e) | new(v, E)`. -/

inductive ECtx
  | hole
  | projc (E : ECtx) (i : Idx)
  | appL  (E : ECtx) (e : Expr)
  | appR  (v : Value) (E : ECtx)
  | newL  (C : ClassName) (E : ECtx) (e : Expr)
  | newR  (C : ClassName) (v : Value) (E : ECtx)

/-- Plug an expression into the unique hole of an evaluation context. -/
def ECtx.plug : ECtx → Expr → Expr
  | hole,        e => e
  | projc E i,   e => Expr.proj (E.plug e) i
  | appL E a,    e => Expr.app (E.plug e) a
  | appR v E,    e => Expr.app (Expr.val v) (E.plug e)
  | newL C E a,  e => Expr.newC C (E.plug e) a
  | newR C v E,  e => Expr.newC C (Expr.val v) (E.plug e)

inductive Frame where
  | init1 (g : GlobName) (e : Expr) (k : Expr) : Frame
  | init2 (g : GlobName) (k : Expr) : Frame
  | call (t : Loc) (p : Value) (κ : ECtx): Frame

/-- The global name recorded by a frame. -/
def Frame.glob : Frame → Option GlobName
  | init1 g _ _ => g
  | init2 g _   => g
  | call _ _ _ => none

/-- The global name recorded by a frame. -/
def Frame.loc : Frame → Option Loc
  | init1 _ _ _ => none
  | init2 _ _   => none
  | call t _ _ => t

abbrev Stack := List Frame

def Stack.push(f: Frame)(S: Stack) : Stack :=
  f::S

def Stack.pop(S: Stack) : Option (Frame × Stack) :=
  match S with
  | [] => Option.none
  | f :: fs => Option.some (f, fs)

def Stack.topCall(S :Stack) : Option Frame :=
    match S with
  | [] => Option.none
  | f :: _fs => match f with
      | Frame.call _ _ _ => some f
      | _ => none

/-- Find the topmost `init` frame of the stack. Returns the init frame, the
    `call` frames sitting above it (topmost first), and the rest of the stack
    below it, so that `S = calls ++ f :: rest`. `none` if no init frame. -/
def Stack.topInit : Stack → Option (Frame × Stack × Stack)
  | [] => none
  | Frame.call t p κ :: fs =>
      (Stack.topInit fs).map fun (f, calls, rest) => (f, Frame.call t p κ :: calls, rest)
  | f :: fs => some (f, [], fs)

def Stack.TopInit (S : Stack) (G : GlobName) : Prop :=
  ∀ i cfs r, S.topInit = some (i, cfs, r) → i.glob = G

def Stack.this (S: Stack) : Option Loc :=
  match S.topCall with
  | Frame.call t _ _ => t
  | _ => none

def Stack.This (S: Stack) (H : Heap) (C : ClsIns) : Prop :=
  ∀ l, S.this = some l → H l = C

/-- A configuration `cfg ::= ⟨H, Γ, e⟩`, with a separate `Crash`. -/
inductive Config
  | mk (H : Heap) (Γ : GTable) (S: Stack) (e : Expr)
  -- | mkC (H : Heap) (Γ : GTable) (S: Stack) (t: Loc) (p: Value) (e : Expr)
  -- | mkO (H : Heap) (Γ : GTable) (S: Stack) (g: GlobName) (e : Expr)
  | crash
  deriving Inhabited

-- /-! ### Substitution

--   `this` and `param` are the only term variables and the language has no binders
--   that capture them, so substitution is ordinary structural replacement. -/

-- /-- `e[t/this]`. -/
-- def substThis (t : Expr) : Expr → Expr
--   | Expr.thisE        => t
--   | Expr.paramE       => Expr.paramE
--   | Expr.newC C e₁ e₂ => Expr.newC C (substThis t e₁) (substThis t e₂)
--   | Expr.app e₁ e₂    => Expr.app (substThis t e₁) (substThis t e₂)
--   | Expr.proj e i     => Expr.proj (substThis t e) i
--   | Expr.gproj G i    => Expr.gproj G i
--   | Expr.val v        => Expr.val v          -- values contain no variables

-- /-- `e[t/param]`. -/
-- def substParam (t : Expr) : Expr → Expr
--   | Expr.thisE        => Expr.thisE
--   | Expr.paramE       => t
--   | Expr.newC C e₁ e₂ => Expr.newC C (substParam t e₁) (substParam t e₂)
--   | Expr.app e₁ e₂    => Expr.app (substParam t e₁) (substParam t e₂)
--   | Expr.proj e i     => Expr.proj (substParam t e) i
--   | Expr.gproj G i    => Expr.gproj G i
--   | Expr.val v        => Expr.val v          -- values contain no variables



/-! ### The step relation -/

/-- One small step `→` on configurations.  Each computational rule fires a redex
    inside an arbitrary evaluation context `E` (this folds in E-Ctx). -/
inductive Step (L : Program) : Config → Config → Prop where
  /-- E-Proj: `ℓ.i → vᵢ` where `H(ℓ) = C(v₁,v₂)`. -/
  | proj {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {ℓ : Loc} {C : ClassName}
         {v₁ v₂ : Value} {i : Idx} {G : GlobName} :
      H ℓ = some ⟨C, G, v₁, v₂⟩ →
      Step L (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))
             (.mk H Γ S (E.plug (Expr.val ((ClsIns.mk C G v₁ v₂).field i))))
  /-- E-GProj: `G.i → vᵢ` where `G(v₁,v₂) ∈ Γ` is fully initialized. -/
  | gproj {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {G : GlobName} {g : GEntry}
          {i : Idx} {v : Value} :
      Γ G = some g →
      g.field i = some v →
      Step L (.mk H Γ S (E.plug (Expr.gproj G i)))
             (.mk H Γ S (E.plug (Expr.val v)))
  /-- E-UninitGProj: accessing `G.i` with `uᵢ = ⊥` crashes. -/
  | uninit {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {G : GlobName} {g : GEntry} {i : Idx} :
      Γ G = some g →
      g.field i = none →
      Step L (.mk H Γ S (E.plug (Expr.gproj G i))) .crash
  /-- E-AppBeta: `ℓ(v) → body[ℓ/this][v/param]`. -/
  | methCall {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {ℓ : Loc} {C : ClassName}
            {o : ClsIns} {v : Value} {body : Expr} :
      H ℓ = some o →
      o.cls = C →
      Program.HasClass L C body →
      Step L (.mk H Γ S (E.plug (Expr.app (Expr.val (Value.loc ℓ)) (Expr.val v))))
             (.mk H Γ (Stack.push (Frame.call ℓ v E) S) body)
  | ret {H : Heap} {Γ : GTable} {S: Stack} {κ : ECtx} {t : Loc} {C : ClassName}
            {o : ClsIns} {p v : Value} {body : Expr} :
      Step L (.mk H Γ ((Frame.call t p κ)::S) v)
             (.mk H Γ S (κ.plug v))
  /-- E-NewAlloc: `new C(v₁,v₂) → ℓ` for fresh `ℓ`. -/
  | newAlloc {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {C : ClassName} {v₁ v₂ : Value}
             {ℓ : Loc} {body : Expr} {G : GlobName} :
      H ℓ = none →
      Program.HasClass L C body →
      Stack.TopInit S G →
      Step L (.mk H Γ S (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂))))
             (.mk (H[ℓ ↦ ⟨C, G, v₁, v₂⟩]) Γ S (E.plug (Expr.val (Value.loc ℓ))))
  /-- I-Push (macro step): on first access of an uninitialised `G`, run its two-/
  | ipush {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {G : GlobName} {i : Idx}
          {e₁ e₂ : Expr} {H₁ : Heap} {Γ₁ : GTable} {v₁ : Value}
          {H₂ : Heap} {Γ₂ : GTable} :
      Program.HasObject L G e₁ e₂ →
      Γ G = none →
     Step L (.mk H Γ S (E.plug (Expr.gproj G i)))
            (.mk H₂ (Γ₂[G↦ ⟨none, none⟩]) (Stack.push (Frame.init1 G e₂ (E.plug (Expr.gproj G i))) S) e₁)
  /-- I-Next: the first field of `G` has reduced to `v₁`; record `G(v₁,⊥)`,
      swap the top frame to `init2`, and start evaluating the pending `e₂`. -/
  | inext {H : Heap} {Γ : GTable} {S : Stack} {G : GlobName}
          {e₂ k : Expr} {v₁ : Value} :
      Step L (.mk H Γ (Frame.init1 G e₂ k :: S) (Expr.val v₁))
             (.mk H (Γ[G↦ ⟨some v₁, none⟩]) (Frame.init2 G k :: S) e₂)
  /-- I-Pop: the second field of `G` has reduced to `v₂`; record `G(v₁,v₂)`,
      pop the `init2` frame, and resume at the saved resumption `κ`. -/
  | ipop {H : Heap} {Γ : GTable} {S : Stack} {G : GlobName}
          {k : Expr} {v₁ v₂ : Value} :
      Γ G = some ⟨some v₁, none⟩ →
      Step L (.mk H Γ (Frame.init2 G k :: S) (Expr.val v₂))
             (.mk H (Γ[G↦ ⟨some v₁, some v₂⟩]) S k)

/-- Reflexive–transitive closure `→*`. -/
inductive Star (L : Program) : Config → Config → Prop where
  | refl {c} : Star L c c
  | head {c c' c''} : Step L c c' → Star L c' c'' → Star L c c''

namespace Star
variable {L : Program}

theorem single {c c' : Config} (h : Step L c c') : Star L c c' :=
  .head h .refl

theorem trans : ∀ {a b c : Config}, Star L a b → Star L b c → Star L a c
  | _, _, _, .refl,      h₂ => h₂
  | _, _, _, .head s t,  h₂ => .head s (trans t h₂)

end Star

/-- `G ∈ globals(S)`: some frame of the stack records the global `G`. -/
def inGlobals (G : GlobName) (S : Stack) : Prop :=
  ∃ f ∈ S, f.glob = some G

def isInitialized (G : GlobName) (Γ : GTable) (h: (Γ G).isSome): Prop :=
  (((Γ G).get h).field Idx.one).isSome ∧ (((Γ G).get h).field Idx.two).isSome

end Proof
