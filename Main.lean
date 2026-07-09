import Proof

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

variable (p q r s : Prop)

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
  fun h₃ : p =>
  show r from h₁ (h₂ h₃)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: (p ∧ q) => And.intro h.right h.left)
    (fun h: (q ∧ p) => And.intro h.right h.left)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (fun h: (p ∨ q) =>
      Or.elim h
      (fun hp: p => Or.inr hp)
      (fun hq: q => Or.inl hq)
    )
    (fun h: (q ∨ p) =>
      Or.elim h
      (fun hq: q => Or.inr hq)
      (fun hp: p => Or.inl hp)
    )

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) :=
  fun h: (p ∧ ¬p) =>
    h.right h.left
example : p ∧ ¬q → ¬(p → q) :=
  fun h: (p ∧ ¬q) =>
    fun h1: (p -> q) =>
      have hq : q := h1 h.left
      h.right hq
example : ¬p → (p → q) :=
  fun h: ¬p =>
    fun hp: p =>
      False.elim (h hp)
example : (¬p ∨ q) → (p → q) :=
  fun h: (¬p ∨ q) =>
    fun hp: p =>
      Or.elim h
      (fun hnp: ¬p => absurd hp hnp)
      (fun hq: q => hq)
example : p ∨ False ↔ p :=
  Iff.intro
  (fun h: (p ∨ False) =>
    Or.elim h
    (fun hp: p => hp)
    (fun false: False => False.elim false))
  (fun h: p =>
    Or.inl h)
example : p ∧ False ↔ False := sorry

open Classical
example : (p → q) → (¬q → ¬p) :=
  fun h: (p → q) =>
    fun hnq: ¬q =>
      Or.elim (Classical.em p)
      (fun hp: p =>
        have hq: q := h hp
        absurd hq hnq
      )
      (fun hnp: ¬p => hnp)

variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  (fun h1: (∃ x, p x) =>
    fun h2: ∀ x, ¬ p x =>
      Exists.elim h1
        (fun t =>
          fun ht: p t =>
            show False from (h2 t) ht)
  )
  (fun h3: ¬ (∀ x, ¬ p x) =>
    (byContradiction
      fun h4: ¬ (∃ x, p x) =>
        have h5: (∀ x, ¬ p x) :=
          fun t =>
            fun ht: p t =>
              h4 (Exists.intro t ht)
        show False from h3 h5
    )
  )

variable (α : Type) (p q : α → Prop)
example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
  (fun h: (∀ x, p x ∧ q x) =>
    have hp: ∀ x, p x :=
      fun x =>
        (h x).left
    have hq: ∀ x, q x :=
      fun x =>
        (h x).right
    And.intro hp hq
  )
  (fun h: (∀ x, p x) ∧ (∀ x, q x) =>
    fun x =>
      And.intro (h.left x) (h.right x)
  )

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  fun h1: (∀ x, p x → q x) =>
    fun h2: (∀ x, p x) =>
      fun x =>
        have hpq: p x → q x := h1 x
        have hp: p x := h2 x
        hpq hp

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h: (∀ x, p x) ∨ (∀ x, q x) =>
    Or.elim h
      (fun hp : (∀ x, p x) =>
        have h1: ∀ x, p x ∨ q x :=
          fun x =>
            have h2: p x := hp x
            Or.inl h2
        h1
      )
      (fun hq : (∀ x, q x) =>
        fun x =>
          have h2: q x := hq x
          Or.inr h2
      )

variable (r : Prop)

example : α → ((∀ _x : α, r) ↔ r) :=
  fun a: α =>
    Iff.intro
    (fun h: (∀ _x : α, r) =>
      h a
    )
    (fun hr : r =>
      fun _x: α => hr
    )

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
  (fun h1: ∀ x, p x ∨ r =>
    Or.elim (Classical.em r)
    (fun hr: r => Or.inr hr)
    (fun hnr: ¬ r =>
      Or.inl
      (fun x =>
          Or.elim (h1 x)
          (fun hp: p x => hp
          )
          (fun hr: r => False.elim (hnr hr)
          )
      )
    )
  )
  (fun h2: (∀ x, p x) ∨ r =>
    fun x =>
      Or.elim h2
      (fun h3: (∀ x, p x) =>
        Or.inl (h3 x)
      )
      (fun h4: r =>
        Or.inr h4
      )
  )

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
  (fun h: (∀ x, r → p x) =>
    fun r =>
      fun x =>
        (h x) r
  )
  (fun h: (r → ∀ x, p x) =>
    fun x =>
      fun r =>
        (h r) x
  )

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  Or.elim (Classical.em (shaves barber barber))
    (fun hb: shaves barber barber =>
      have hnb: ¬ shaves barber barber := (h barber).mp hb
      show False from hnb hb)
    (fun hnb: ¬ shaves barber barber =>
      have hb: shaves barber barber := (h barber).mpr hnb
      show False from hnb hb)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hbb: shaves barber barber ↔ ¬ shaves barber barber := h barber
  have hnb : ¬ shaves barber barber :=
    fun hb: shaves barber barber =>
      (hbb.mp hb) hb
  show False from hnb (hbb.mpr hnb)
