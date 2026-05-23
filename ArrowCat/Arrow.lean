import ArrowCat.Basic
import ArrowCat.Geanakoplos
import ArrowCat.Pivotal
import KanTactics

/-! # Arrow's Impossibility Theorem

The main result, assembled from the three Geanakoplos lemmas in
`ArrowCat.Geanakoplos`.

The statement: for any domain with at least three alternatives and at
least one voter, every social welfare function satisfying Pareto
efficiency and Independence of Irrelevant Alternatives is a dictatorship.

Equivalently: no SWF can simultaneously satisfy Universal Domain (built
into the type of `SWF`), Pareto, IIA, and Non-Dictatorship. -/


set_option autoImplicit false

namespace ArrowCat

universe u

variable {m : Nat} {α : Type u}

/-- **Arrow's Impossibility Theorem** (Geanakoplos formulation).

Any social welfare function on a domain with at least three alternatives
and at least one voter that satisfies Pareto efficiency and Independence
of Irrelevant Alternatives must be a dictatorship.

Proof outline (filled in by combining the lemmas in
`ArrowCat.Geanakoplos`):

1. Pick any two distinct alternatives `b, b'` (the existence of three
   distinct alternatives gives us this freely).
2. By `pivotalVoterUnique`, there is a single voter `k` who is a local
   dictator over both `b`-avoiding pairs and `b'`-avoiding pairs.
3. Every pair `(a, c)` avoids at least one of `b, b'` (since `b ≠ b'`),
   so `k` is a local dictator over every pair.
4. Therefore `k` is a (global) dictator. -/
theorem arrow
    (f : SWF m α) (_h1 : 0 < m) (_h3 : AtLeastThree α)
    (_hPareto : SWF.Pareto f) (_hIIA : SWF.IIA f) :
    ∃ k : Fin m, SWF.Dictator f k := by
  sorry

/-- **Equivalent contrapositive form.**  No social welfare function on
a sufficiently rich domain satisfies Pareto, IIA, and Non-Dictatorship
simultaneously. -/
theorem arrow_contrapositive
    (f : SWF m α) (_h1 : 0 < m) (_h3 : AtLeastThree α)
    (_hPareto : SWF.Pareto f) (_hIIA : SWF.IIA f) :
    ¬ SWF.NonDictator f := by
  sorry

end ArrowCat
