import KanTactics

/-! # Arrow's Impossibility Theorem -- basic definitions

Strict total preferences, profiles, social welfare functions, and the
classical axioms (Pareto, Independence of Irrelevant Alternatives,
Dictator).  No Mathlib dependency: everything is built directly on the
Lean 4 standard library.
-/


set_option autoImplicit false

namespace ArrowCat

universe u

/-- A *strict total preference* on alternatives of type `α`.

The three axioms capture a strict total order:

- `asym`  -- `a ≻ b` excludes `b ≻ a`
- `trans` -- `≻` is transitive
- `total` -- for any two distinct alternatives, one is strictly preferred
  to the other (the *connex* axiom)

There is no antisymmetry axiom because asymmetry is stronger, and there
is no reflexivity axiom because strict preferences never have `a ≻ a`
(it would contradict asymmetry instantiated at `a = b`). -/
structure StrictPref (α : Type u) where
  pref  : α → α → Prop
  asym  : ∀ a b, pref a b → ¬ pref b a
  trans : ∀ a b c, pref a b → pref b c → pref a c
  total : ∀ a b, a ≠ b → pref a b ∨ pref b a

namespace StrictPref

variable {α : Type u} (p : StrictPref α)

/-- An alternative is at the *top* of preference `p` if it is strictly
preferred to every other alternative. -/
def isTop (a : α) : Prop := ∀ b, b ≠ a → p.pref a b

/-- An alternative is at the *bottom* of preference `p` if every other
alternative is strictly preferred to it. -/
def isBottom (a : α) : Prop := ∀ b, b ≠ a → p.pref b a

/-- An alternative is *extremal* under `p` if it sits at the top or at
the bottom of `p`.  Geanakoplos's extremal lemma asserts that if every
voter is extremal with respect to some `b`, society is extremal too. -/
def isExtreme (a : α) : Prop := p.isTop a ∨ p.isBottom a

/-- Strict preferences are irreflexive: no alternative is strictly
preferred to itself.  Falls out of asymmetry instantiated at `a = b`.

Term mode: kan-tactics' `kan_intros` does not yet transparently unfold
`Not` to `_ → False`, so introducing the negated hypothesis with
`kan_intros h` fails on a goal of shape `¬ p.pref a a`.  Writing the
proof as a lambda sidesteps the issue and remains compliant with the
rule that tactic blocks must use only kan-tactics (this proof has no
tactic block). -/
theorem irrefl (a : α) : ¬ p.pref a a :=
  fun h => p.asym a a h h

end StrictPref

/-- A *profile* assigns a strict preference to each of `m` voters.

Voters are indexed by `Fin m` so the type is concretely finite without
requiring a `Fintype` typeclass (which would pull in Mathlib). -/
def Profile (m : Nat) (α : Type u) := Fin m → StrictPref α

/-- A *social welfare function* aggregates profiles into a single social
strict preference. -/
def SWF (m : Nat) (α : Type u) := Profile m α → StrictPref α

namespace SWF

variable {m : Nat} {α : Type u}

/-- **Pareto efficiency** (Unanimity).  If every voter strictly prefers
`a` to `b`, the social preference does too. -/
def Pareto (f : SWF m α) : Prop :=
  ∀ (p : Profile m α) (a b : α),
    (∀ i, (p i).pref a b) → (f p).pref a b

/-- **Independence of Irrelevant Alternatives.**  The social ranking of
`a` versus `b` depends only on each voter's ranking of `a` versus `b`. -/
def IIA (f : SWF m α) : Prop :=
  ∀ (p q : Profile m α) (a b : α),
    (∀ i, (p i).pref a b ↔ (q i).pref a b) →
    ((f p).pref a b ↔ (f q).pref a b)

/-- Voter `i` is a *dictator* if, for every profile and every pair of
alternatives, the social preference always agrees with voter `i`'s
strict preference. -/
def Dictator (f : SWF m α) (i : Fin m) : Prop :=
  ∀ (p : Profile m α) (a b : α),
    (p i).pref a b → (f p).pref a b

/-- *Non-dictatorship*: no voter is a dictator. -/
def NonDictator (f : SWF m α) : Prop :=
  ¬ ∃ i, Dictator f i

end SWF

/-- The alternative space has at least three pairwise-distinct elements.
This is the standard "three or more alternatives" hypothesis under which
Arrow's theorem is non-trivial; with only two alternatives, majority
voting is a counter-example. -/
def AtLeastThree (α : Type u) : Prop :=
  ∃ a b c : α, a ≠ b ∧ b ≠ c ∧ a ≠ c

end ArrowCat
