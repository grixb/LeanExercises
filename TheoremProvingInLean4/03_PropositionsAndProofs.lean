/-
# Propositions and Proofs

## Exercises

Prove the following identities, replacing the "sorry" placeholders with actual proofs.
-/

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
  (λ (⟨hp, hq⟩ : p ∧ q) =>
    show q ∧ p from ⟨hq, hp⟩)
  (λ (⟨hq, hp⟩ : q ∧ p) =>
    show p ∧ q from ⟨hp, hq⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
  (λ (hpq : p ∨ q) =>
    show q ∨ p from hpq.elim Or.inr Or.inl)
  (λ (hqp : q ∨ p) =>
    show p ∨ q from hqp.elim Or.inr Or.inl)

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
  (λ (⟨⟨hp, hq⟩ , hr⟩ : (p ∧ q) ∧ r) =>
    show p ∧ (q ∧ r) from ⟨hp, ⟨hq, hr⟩⟩)
  (λ (⟨hp, ⟨hq, hr⟩⟩ : p ∧ (q ∧ r)) =>
    show (p ∧ q) ∧ r from ⟨⟨hp, hq⟩ , hr⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
  (λ (hl : (p ∨ q) ∨ r) =>
  show p ∨ (q ∨ r) from hl.elim
    (·.elim Or.inl (Or.inr ∘ Or.inl))
    (Or.inr ∘ Or.inr))
  (λ (hr : p ∨ (q ∨ r)) =>
  show (p ∨ q) ∨ r from hr.elim
    (Or.inl ∘ Or.inl)
    (·.elim (Or.inl ∘ Or.inr) Or.inr))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
  (λ (⟨hp, hqr⟩ : p ∧ (q ∨ r)) =>
  show (p ∧ q) ∨ (p ∧ r) from hqr.elim
    (Or.inl ⟨hp, ·⟩) (Or.inr ⟨hp, ·⟩))
  (λ (hr : (p ∧ q) ∨ (p ∧ r)) =>
  show p ∧ (q ∨ r) from hr.elim
    (λ ⟨hp, hq⟩ => ⟨hp, Or.inl hq⟩)
    (λ ⟨hp, hr⟩ => ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
  (λ (hl : p ∨ (q ∧ r)) =>
  show (p ∨ q) ∧ (p ∨ r) from hl.elim
    (λ (hp : p) => ⟨Or.inl hp, Or.inl hp⟩)
    (λ (⟨hq, hr⟩ : q ∧ r) => ⟨Or.inr hq, Or.inr hr⟩))
  (λ (⟨hpq, hpv⟩ : (p ∨ q) ∧ (p ∨ r)) =>
  show p ∨ (q ∧ r) from match hpq, hpv with
    | Or.inl hp, _ => Or.inl hp
    | _, Or.inl hp => Or.inl hp
    | Or.inr hq, Or.inr hr => Or.inr ⟨hq, hr⟩)

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
  (λ (hpq : p → (q → r)) =>
  show p ∧ q → r from (λ ⟨hp, hq⟩ => hpq hp hq))
  (λ (hpq : p ∧ q → r) =>
  show p → (q → r) from (λ hp hq => hpq ⟨hp, hq⟩))

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
  (λ (hpq : (p ∨ q) → r) =>
  show (p → r) ∧ (q → r) from ⟨hpq ∘ Or.inl, hpq ∘ Or.inr⟩)
  (λ (⟨hpr, hqr⟩ : (p → r) ∧ (q → r)) =>
  show (p ∨ q) → r from (·.elim hpr hqr))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
  (λ (hn : ¬(p ∨ q)) =>
  show ¬p ∧ ¬q from ⟨hn ∘ Or.inl, hn ∘ Or.inr⟩)
  (λ (⟨hnp, hnq⟩ : ¬p ∧ ¬q) =>
  show ¬(p ∨ q) from (·.elim hnp hnq))

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  (λ hn ⟨hp, hq⟩ =>
  show False from hn.elim (· hp) (· hq))

example : ¬(p ∧ ¬p) :=
  (λ ⟨hp, hnp⟩ =>
  show False from absurd hp hnp)

example : p ∧ ¬q → ¬(p → q) :=
  (λ ⟨hp, hnq⟩ hpq =>
  show False from absurd (hpq hp) hnq)

example : ¬p → (p → q) :=
  (λ hnp hp =>
  show q from (hnp hp).elim)

example : (¬p ∨ q) → (p → q) :=
  (λ hn hp => show q
  from hn.elim (hp |> · |> False.elim) id)

example : p ∨ False ↔ p :=
  Iff.intro
  (λ hpf => show p from
    hpf.elim id (·.elim))
  (λ hp => show p ∨ False from
    Or.inl hp)

example : p ∧ False ↔ False :=
  Iff.intro
  (λ ⟨_, fls⟩  => show False from fls)
  (λ fls => show p ∧ False from
    ⟨fls.elim, fls⟩)

example : (p → q) → (¬q → ¬p) :=
  (λ hpq hnq hp => show False from
    absurd (hpq hp) hnq)


/-
Prove the following identities, replacing the "sorry" placeholders with actual proofs.
These require classical reasoning.
-/

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  (λ hpqr => show (p → q) ∨ (p → r) from byCases
    (λ (hp : p) => match hpqr hp with
      | Or.inl hq => Or.inl (λ _ => hq)
      | Or.inr hr => Or.inr (λ _ => hr))
    (λ (hnp : ¬ p) =>
      Or.inl (λ hp => absurd hp hnp)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  (λ hnpq => byCases
    (λ (hp : p) => Or.inr
      (show ¬ q from
        (λ hq => hnpq ⟨hp, hq⟩)))
    (λ (hnp : ¬ p) => Or.inl hnp))

example : ¬(p → q) → p ∧ ¬q :=
  (λ hnpq => byCases
    (λ (hq : q) => absurd (λ _ => hq) hnpq)
    (λ (hnq : ¬ q) => byCases
      (λ (hp : p) => ⟨hp, hnq⟩)
      (λ (hnp : ¬ p) =>
        absurd (λ hp => absurd hp hnp) hnpq)))

example : (p → q) → (¬p ∨ q) :=
  (λ hpq => byCases
    (λ (hp : p) => hp |> hpq |> Or.inr)
    (λ (hnp : ¬ p) => hnp |> Or.inl))

example : (¬q → ¬p) → (p → q) :=
  (λ hnqnp hp => byCases
    (λ (hq : q) => hq)
    (λ (hnq : ¬ q) =>
      absurd hp (hnq |> hnqnp)))

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  (λ hpqp => byContradiction
    (λ hnp =>
      have hpq : p → q :=
        (λ hp => absurd hp hnp)
      absurd (hpqp hpq) hnp))
