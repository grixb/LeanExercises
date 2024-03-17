/-
# Tactics

## Exercises

Go back to the exercises in Chapter Propositions and Proofs and Chapter Quantifiers
and Equality and redo as many as you can now with tactic proofs,
using also `rw` and `simp` as appropriate.
-/

section PropositionsAndProofs

variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  · intro ⟨hp, hq⟩; exact ⟨hq, hp⟩
  · intro ⟨hq, hp⟩; exact ⟨hp, hq⟩

example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  · intro
    | .inl hp => apply Or.inr; assumption
    | .inr hq => apply Or.inl; assumption
  · intro
    | .inr hp => apply Or.inl; assumption
    | .inl hq => apply Or.inr; assumption

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  · intro ⟨⟨hp, hq⟩, hr⟩; exact ⟨hp, ⟨hq, hr⟩⟩
  · intro ⟨hp, ⟨hq, hr⟩⟩; exact ⟨⟨hp, hq⟩, hr⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  · intro
    | .inl (.inl hp) => apply Or.inl; assumption
    | .inl (.inr hq) => apply Or.inr ∘ Or.inl; assumption
    | .inr hr => apply Or.inr ∘ Or.inr; assumption
  · intro
    | .inl hp => apply Or.inl ∘ Or.inl; assumption
    | .inr (.inl hq) => apply Or.inl ∘ Or.inr; assumption
    | .inr (.inr hr) => apply Or.inr; assumption

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro
    | ⟨hp, .inl hq⟩ => apply Or.inl; exact ⟨hp, hq⟩
    | ⟨hp, .inr hr⟩ => apply Or.inr; exact ⟨hp, hr⟩
  · intro
    | .inl ⟨hp, hq⟩ => exact ⟨hp, .inl hq⟩
    | .inr ⟨hp, hr⟩ => exact ⟨hp, .inr hr⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  · intro
    | .inl hp =>
      apply And.intro
      · apply Or.inl; assumption
      · apply Or.inl; assumption
    | .inr ⟨hq, hr⟩ =>
      apply And.intro
      · apply Or.inr; assumption
      · apply Or.inr; assumption
  · intro
    | ⟨.inl _, .inl _⟩ => apply Or.inl; assumption
    | ⟨.inl hp, .inr _⟩ => apply Or.inl; assumption
    | ⟨.inr _, .inl hp⟩ => apply Or.inl; assumption
    | ⟨.inr hq, .inr hr⟩ =>
      apply Or.inr; exact ⟨hq, hr⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  · intro hpq ⟨hp, hq⟩
    apply hpq; exact hp; exact hq
  · intro hpq hp hq;
    have := And.intro hp hq
    apply hpq; assumption

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  · intro hpq; apply And.intro
    · intro hp; apply hpq; apply Or.inl; assumption
    · intro hq; apply hpq; apply Or.inr; assumption
  · intro ⟨hpr, hqr⟩; intro
    | .inl hp => apply hpr; assumption
    | .inr hq => apply hqr; assumption

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro
  · intro hn; apply And.intro;
    · intro; apply hn; apply Or.inl; assumption
    · intro; apply hn; apply Or.inr; assumption
  · intro ⟨hnp, hnq⟩; intro hpq;
    apply Or.elim
    exact hpq; exact hnp; exact hnq

example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro hnpq ⟨hp, hq⟩;
  apply Or.elim; assumption
  · intro hnp; apply hnp; assumption
  · intro hnq; apply hnq; assumption

example : ¬(p ∧ ¬p) := by
  intro ⟨hp, hnp⟩
  apply hnp; assumption

example : p ∧ ¬q → ¬(p → q) := by
  intro ⟨hp, hnq⟩ hpq;
  apply hnq; apply hpq; assumption

example : ¬p → (p → q) := by
  intro hnp hp;
  apply False.elim; apply hnp;
  assumption

example : (¬p ∨ q) → (p → q) := by
  intro hnpq hp;
  cases hnpq with
  | inl hnp =>
    apply False.elim; apply hnp;
    assumption
  | inr hq => exact hq

example : p ∨ False ↔ p := by
  apply Iff.intro
  · intro
    | .inl hp => assumption;
    | .inr False => apply False.elim
  · intro hp
    apply Or.inl; assumption

example : p ∧ False ↔ False := by
  apply Iff.intro
  · intro ⟨_, False⟩; exact False
  · intro False
    apply And.intro
    apply False.elim
    exact False

example : (p → q) → (¬q → ¬p) := by
  intro hpq hnq hp
  have := hpq hp
  apply hnq
  assumption

open Classical

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro hpqr
  apply byCases
  · intro (hp : p)
    have := hpqr hp
    apply Or.elim; assumption
    case left =>
      intro hq; apply Or.inl
      intro; exact hq
    case right =>
      intro hr; apply Or.inr
      intro; exact hr
  · intro (hnp : ¬p)
    apply Or.inl; intro hp
    have := hnp hp
    apply False.elim
    assumption

example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro hnpq
  apply byCases
  · intro (hp : p)
    apply Or.inr; intro hq
    exact show False by
      apply hnpq
      exact ⟨hp, hq⟩
  · intro (hnp : ¬p)
    apply Or.inl; assumption

example : ¬(p → q) → p ∧ ¬q := by
  intro hnpq
  apply byCases
  · intro (hq : q)
    have := by
      apply hnpq
      intro; exact hq
    apply False.elim
    assumption
  · intro (hnq : ¬q)
    apply byCases
    · intro (hp : p)
      exact ⟨hp, hnq⟩
    · intro (hnp : ¬p)
      have := by
        apply hnpq
        intro hp
        apply False.elim
        apply hnp; assumption
      apply False.elim
      assumption

section end
