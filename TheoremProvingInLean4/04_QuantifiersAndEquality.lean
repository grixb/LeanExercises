/-
# Quantifiers and Equality

What follows are some common identities involving the existential quantifier.
In the exercises below, we encourage you to prove as many as you can.
We also leave it to you to determine which are nonconstructive,
and hence require some form of classical reasoning.
-/

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ _x : α, r) → r :=
  (λ ⟨_, hr⟩ => hr)

example (a : α) : r → (∃ _x : α, r) :=
  (λ hr => ⟨a, hr⟩)

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ ⟨w, hw, hr⟩ => ⟨⟨w, hw⟩, hr⟩)
    (λ ⟨⟨w, hw⟩, hr⟩ => ⟨w, hw, hr⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (λ ⟨w, hw⟩ => hw.elim
      (λ wpx => ⟨w, wpx⟩ |> Or.inl)
      (λ wqx => ⟨w, wqx⟩ |> Or.inr))
    (λ hw => hw.elim
      (λ ⟨w, wpx⟩ => ⟨w, wpx |> Or.inl⟩)
      (λ ⟨w, wqx⟩ => ⟨w, wqx |> Or.inr⟩))

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (λ hax ⟨w, hnpw⟩ => w |> hax |> hnpw)
    (λ hnx a => byContradiction
      (λ hnpa => hnx ⟨a, hnpa⟩))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
  -- ⊢ (∃ x, p x) → ¬∀ (x : α), ¬p x
    (λ ⟨w, hpw⟩ hapx =>
    -- ⟨w : α, hpw : p w⟩ : ∃ x, p x
    -- hapx : ∀ (x : α), ¬p x
    -- ⊢ False
      w |> hapx <| hpw)
  -- ⊢ (¬∀ (x : α), ¬p x) → ∃ x, p x
    (λ hnaxpx => byContradiction
    -- hnaxpx : ¬∀ (x : α), ¬p x
    -- ⊢ (¬∃ x, p x) → False
      (λ hnepx => absurd
      -- hnepx : ¬∃ x, p x
      -- ⊢ ∀ (a : α), p a → False
        (λ a hpa =>
        -- a : α
        -- hpa : p a
        -- ⊢ False
          absurd ⟨a, hpa⟩ hnepx)
        hnaxpx))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (λ hnepx a hpa => hnepx ⟨a, hpa⟩)
    (λ haxnpx ⟨w, hpw⟩ =>
    -- haxnpx : ∀ (x : α), ¬p x
    -- ⟨w : α, hpw : p w⟩ : ∃ x, p x
    -- ⊢ False : ¬p w
      absurd hpw (w |> haxnpx))

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ hnaxpx => byContradiction
      (λ hexnpx => absurd
        (λ a => byContradiction
          (λ hna => absurd ⟨a, hna⟩ hexnpx))
        hnaxpx))
    (λ ⟨w, hnw⟩  haxpx =>
      absurd (haxpx w) hnw)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ haxpxr ⟨w, hpw⟩ => haxpxr w hpw)
    (λ hexpxr w hpw => hexpxr ⟨w, hpw⟩)

-- solution hint from the book
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ ⟨w, hpxr⟩ hax => w |> hax |> hpxr)
    (λ haxpxr => byCases
      (λ (haxpx : ∀x, p x) => ⟨a, λ _ => haxpxr haxpx⟩)
      (λ (hnaxpx : ¬∀x, p x) => byContradiction
        (λ hnexpxr => -- ¬∃ x, p x → r
          have haxpx : ∀x, p x := (λ x =>
            byContradiction (λ hnpx =>
              have hexpxr : ∃x, p x → r :=
                ⟨x, λ hpx => absurd hpx hnpx⟩
              absurd hexpxr hnexpxr))
          absurd haxpx hnaxpx)))


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ ⟨w, hrpw⟩ hr => ⟨w, hrpw hr⟩)
    (λ hrexpx => byCases
      (λ (hr : r) =>
        have ⟨w, hpw⟩ := hrexpx hr
        ⟨w, λ _ => hpw⟩)
      (λ (hnr : ¬r) => byContradiction
        (λ hnexrpx =>
          have hexrpx : ∃x, r → p x :=
            ⟨a, λ hr => absurd hr hnr⟩
          absurd hexrpx hnexrpx)))


/-
## Exercises

1. Prove these equivalences:
-/

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
  Iff.intro
    (λ haxpxqx => ⟨
      (· |> haxpxqx |> And.left),
      (· |> haxpxqx |> And.right)⟩)
    (λ ⟨haxpx, haxqx⟩ a =>
      ⟨haxpx a, haxqx a⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
  (λ haxpxqx haxpx a => a |> haxpx |> haxpxqx a)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  (λ ho a => ho.elim
    (λ haxpx => a |> haxpx |> Or.inl)
    (λ haxqx => a |> haxqx |> Or.inr))

/-
You should also try to understand why the reverse implication
is not derivable in the last example.

2. It is often possible to bring a component of a formula
outside a universal quantifier, when it does not depend on the quantified variable.
Try proving these (one direction of the second of these requires classical logic):
-/

example : α → ((∀ _x : α, r) ↔ r) :=
  (λ a => Iff.intro
    (λ haxr => a |> haxr)
    (λ hr _ => hr)
)

example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
  Iff.intro
    (λ haxpxor => byCases
      (λ (hr : r) => Or.inr hr)
      (λ (hnr : ¬r) => Or.inl (λ a =>
        (haxpxor a).elim id
          (λ hr => absurd hr hnr))))
    (λ haxpxr x => haxpxr.elim
      (λ haxpx =>
        x |> haxpx |> Or.inl)
      Or.inr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
  Iff.intro
    (λ haxrpx hr a => a |> haxrpx <| hr)
    (λ hraxpx a hr => hr |> hraxpx <| a)

/-
Consider the "barber paradox," that is, the claim that in a certain town
there is a (male) barber that shaves all and only the men who do not shave themselves.
Prove that this is a contradiction:
-/

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  have hparax := h barber
  byCases
    (λ (hself : shaves barber barber) =>
      hself |> absurd <| hparax.mp <| hself)
    (λ (hnself : ¬shaves barber barber) =>
      hnself |> hparax.mpr |> absurd <| hnself)

/-
Remember that, without any parameters,
an expression of type Prop is just an assertion. Fill in the definitions of prime and
Fermat_prime below, and construct each of the given assertions.
For example, you can say that there are infinitely many primes
by asserting that for every natural number n, there is a prime number greater than n. Goldbach's weak conjecture states that every odd number greater than 5 is the sum of three primes. Look up the definition of a Fermat prime or any of the other statements, if necessary.
-/

def even (n : Nat) : Prop := ∃x : Nat, n = 2*x

def prime (n : Nat) : Prop :=
  ∀m : Nat, m != 1 ∧ m != n → ¬(∃k : Nat, n = k*m)

def infinitely_many_primes : Prop :=
  ∀p : Nat, (p|>prime) → ∃p₂ : Nat, (p₂|>prime) ∧ p₂ > p

def Fermat_prime (n : Nat) : Prop :=
  (n|>prime) ∧ ∃k, k≠0 ∧ n = k^2+1

def infinitely_many_Fermat_primes : Prop :=
  ∀f : Nat, (f|>Fermat_prime) → ∃f₂ : Nat, (f₂|>Fermat_prime) ∧ f₂ > f

def goldbach_conjecture : Prop :=
  ∀g : Nat, (g|>even) ∧ g > 2 →
    ∃p₁ p₂ : Nat, (p₁|>prime) ∧ (p₂|>prime) ∧ g = p₁+p₂

def Goldbach's_weak_conjecture : Prop :=
  ∀g : Nat, (g|>even) ∧ g > 2 →
    ∃p₁ p₂ p₃ : Nat, (p₁|>prime) ∧ (p₂|>prime) ∧ (p₃|>prime)
    ∧ g = p₁ + p₂ + p₃

def Fermat's_last_theorem : Prop := ¬(∃ a b c n : Nat,
  a>0 ∧ b>0 ∧ c>0 ∧ n>2 ∧ (a^n + b^n = c^n))
