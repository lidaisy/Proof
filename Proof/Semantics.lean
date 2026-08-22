import Proof.Syntax

namespace Proof

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

abbrev Heap := Loc → Option ClsIns

abbrev GVal := Option Value

structure GEntry where
  u₁ : GVal
  u₂ : GVal
  deriving Repr

def GEntry.field : GEntry → Idx → GVal
  | g, Idx.one => g.u₁
  | g, Idx.two => g.u₂

abbrev GTable := GlobName → Option GEntry

def Heap.update (H : Heap) (ℓ : Loc) (o : ClsIns) : Heap :=
  fun ℓ' => if ℓ' = ℓ then some o else H ℓ'

def GTable.update (Γ : GTable) (G : GlobName) (g : GEntry) : GTable :=
  fun G' => if G' = G then some g else Γ G'

notation:max H "[" ℓ " ↦ " o "]" => Heap.update H ℓ o
notation:max Γ "[" G "↦ " g "]" => GTable.update Γ G g

inductive ECtx
  | hole
  | projc (E : ECtx) (i : Idx)
  | appL  (E : ECtx) (e : Expr)
  | appR  (v : Value) (E : ECtx)
  | newL  (C : ClassName) (E : ECtx) (e : Expr)
  | newR  (C : ClassName) (v : Value) (E : ECtx)

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

def Frame.glob : Frame → Option GlobName
  | init1 g _ _ => g
  | init2 g _   => g
  | call _ _ _ => none

def Frame.loc : Frame → Option Loc
  | init1 _ _ _ => none
  | init2 _ _   => none
  | call t _ _ => t

def Frame.NotCall (f : Frame) : Prop :=
  ∀ t p κ, f ≠ Frame.call t p κ

def Frame.idx (f : Frame) (h : f.NotCall) : Idx :=
  match f with
  | init1 _ _ _ => Idx.one
  | init2 _ _   => Idx.two
  | call t p κ  => absurd rfl (h t p κ)

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

def Stack.topInit : Stack → Option (Frame × Stack × Stack)
  | [] => none
  | Frame.call t p κ :: fs =>
      (Stack.topInit fs).map fun (f, calls, rest) => (f, Frame.call t p κ :: calls, rest)
  | f :: fs => some (f, [], fs)

def Stack.HasInit (S : Stack) : Prop :=
  ∃ i cfs r, S.topInit = some (i, cfs, r)

def Stack.this (S: Stack) : Option Loc :=
  match S.topCall with
  | Frame.call t _ _ => t
  | _ => none

def Stack.This (S: Stack) (H : Heap) (C : ClsIns) : Prop :=
  ∀ l, S.this = some l → H l = C

inductive Config
  | mk (H : Heap) (Γ : GTable) (S: Stack) (e : Expr)
  | crash
  deriving Inhabited

def ContextFree : Expr → Prop
| Expr.thisE      => False
| Expr.paramE     => False
| Expr.newC _ a b => ContextFree a ∧ ContextFree b
| Expr.app a b    => ContextFree a ∧ ContextFree b
| Expr.proj a _   => ContextFree a
| Expr.gproj _ _  => True
| Expr.val _      => True

def ValueFree : Expr → Prop
| Expr.thisE      => True
| Expr.paramE     => True
| Expr.newC _ a b => ValueFree a ∧ ValueFree b
| Expr.app a b    => ValueFree a ∧ ValueFree b
| Expr.proj a _   => ValueFree a
| Expr.gproj _ _  => True
| Expr.val _      => False

inductive Step (L : Program) : Config → Config → Prop where
  | this {H : Heap} {Γ : GTable} {S: Stack} {E κ: ECtx} {t : Loc} {p : Value} {c : ClsIns}:
    S.topCall = Frame.call t p κ →
    H t = some c →
    Step L (.mk H Γ S (E.plug Expr.thisE))
             (.mk H Γ S (E.plug (Expr.val (Value.loc t))))
  | param {H : Heap} {Γ : GTable} {S: Stack} {E κ: ECtx} {t : Loc} {p : Value} {c : ClsIns}:
    S.topCall = Frame.call t p κ →
    H t = some c →
    Step L (.mk H Γ S (E.plug Expr.paramE))
             (.mk H Γ S (E.plug (Expr.val p)))
  | proj {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {ℓ : Loc} {C : ClassName}
         {v₁ v₂ : Value} {i : Idx} {G : GlobName} :
      H ℓ = some ⟨C, G, v₁, v₂⟩ →
      Step L (.mk H Γ S (E.plug (Expr.proj (Expr.val (Value.loc ℓ)) i)))
             (.mk H Γ S (E.plug (Expr.val ((ClsIns.mk C G v₁ v₂).field i))))
  | gproj {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {G : GlobName} {g : GEntry}
          {i : Idx} {v : Value} :
      Γ G = some g →
      g.field i = some v →
      Step L (.mk H Γ S (E.plug (Expr.gproj G i)))
             (.mk H Γ S (E.plug (Expr.val v)))
  | uninit {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {G : GlobName} {g : GEntry} {i : Idx} :
      Γ G = some g →
      g.field i = none →
      Step L (.mk H Γ S (E.plug (Expr.gproj G i))) .crash
  | methCall {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {ℓ : Loc} {C : ClassName}
            {G G₀ : GlobName} {v v₁ v₂ : Value} {body : Expr}
            {ifr : Frame} {cfs r : Stack} :
      S.topInit = some (ifr, cfs, r) →
      ifr.glob = some G →
      H ℓ = some (ClsIns.mk C G₀ v₁ v₂) →
      Program.HasClass L C body →
      ValueFree body →
      Step L (.mk H Γ S (E.plug (Expr.app (Expr.val (Value.loc ℓ)) (Expr.val v))))
             (.mk H Γ (Stack.push (Frame.call ℓ v E) S) body)
  | ret {H : Heap} {Γ : GTable} {S: Stack} {κ : ECtx} {t : Loc} {C : ClassName}
            {G : GlobName} {p v v₁ v₂ : Value} :
      H t = some ⟨C, G, v₁, v₂⟩ →
      Step L (.mk H Γ ((Frame.call t p κ)::S) v)
             (.mk H Γ S (κ.plug v))
  | newAlloc {H : Heap} {Γ : GTable} {S : Stack} {E : ECtx} {C : ClassName} {v₁ v₂ : Value}
             {ℓ : Loc} {G : GlobName} {ifr : Frame} {cfs r : Stack} :
      S.topInit = some (ifr, cfs, r) →
      ifr.glob = some G →
      (Γ G).isSome →
      H ℓ = none →
      Step L (.mk H Γ S (E.plug (Expr.newC C (Expr.val v₁) (Expr.val v₂))))
             (.mk (H[ℓ ↦ ⟨C, G, v₁, v₂⟩]) Γ S (E.plug (Expr.val (Value.loc ℓ))))
  | ipush {H : Heap} {Γ : GTable} {S: Stack} {E : ECtx} {G : GlobName} {i : Idx}
          {e₁ e₂ : Expr} :
      Program.HasObject L G e₁ e₂ →
      Γ G = none →
      ContextFree e₁ →
      ValueFree e₁ →
      ContextFree e₂ →
     Step L (.mk H Γ S (E.plug (Expr.gproj G i)))
            (.mk H (Γ[G↦ ⟨none, none⟩]) (Stack.push (Frame.init1 G e₂ (E.plug (Expr.gproj G i))) S) e₁)
  | inext {H : Heap} {Γ : GTable} {S : Stack} {G : GlobName}
          {e₁ e₂ k : Expr} {v₁ : Value} :
      Program.HasObject L G e₁ e₂ →
      Γ G = some ⟨none, none⟩ →
      ContextFree e₁ →
      ValueFree e₂ →
      ContextFree e₂ →
      Step L (.mk H Γ (Frame.init1 G e₂ k :: S) (Expr.val v₁))
             (.mk H (Γ[G↦ ⟨some v₁, none⟩]) (Frame.init2 G k :: S) e₂)
  | ipop {H : Heap} {Γ : GTable} {S : Stack} {G : GlobName}
          {e₁ e₂ k : Expr} {v₁ v₂ : Value} :
      Program.HasObject L G e₁ e₂ →
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

theorem crash_uninit {L : Program} :
    ∀ {c d : Config}, Star L c d → d = .crash → c ≠ .crash →
    ∃ (H : Heap) (Γ : GTable) (S : Stack) (E : ECtx) (G : GlobName)
      (g : GEntry) (i : Idx),
      Star L c (.mk H Γ S (E.plug (Expr.gproj G i))) ∧
        Γ G = some g ∧ g.field i = none := by
  intro c d h
  induction h with
  | refl => intro hd hc; exact absurd hd hc
  | @head c c' c'' hstep _ ih =>
      intro hd hc
      subst hd
      by_cases hc' : c' = Config.crash
      · -- the step into `.crash` is `uninit`, and it reads `G.i` right here
        subst hc'
        cases hstep with
        | uninit hΓ hfield => exact ⟨_, _, _, _, _, _, _, Star.refl, hΓ, hfield⟩
      · obtain ⟨H, Γ, S, E, G, g, i, hrun, hΓ, hfield⟩ := ih rfl hc'
        exact ⟨H, Γ, S, E, G, g, i, Star.head hstep hrun, hΓ, hfield⟩

/-- `G ∈ globals(S)`: some frame of the stack records the global `G`. -/
def inGlobals (G : GlobName) (S : Stack) : Prop :=
  ∃ f ∈ S, f.glob = some G

end Proof
