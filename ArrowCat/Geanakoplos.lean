import ArrowCat.Basic
import KanTactics

/-! # Geanakoplos's three lemmas

Following Geanakoplos, _Three Brief Proofs of Arrow's Impossibility
Theorem_ (Economic Theory, 2005), Arrow's theorem decomposes into three
lemmas:

1. `extremalLemma` -- in any profile where every voter places `b`
   extremally (top or bottom), the social ranking also places `b`
   extremally.

2. `pivotalVoterIsLocalDictator` -- there is a voter `k` (the *pivotal
   voter* for `b`) who dictates society's ranking over every pair `(a,c)`
   neither member of which is `b`.

3. Combined with a second application of pivotal-voter analysis over a
   different `b`, the local dictator becomes a global dictator -- the
   payoff is delivered in `ArrowCat.Arrow`.

The lemmas are stated here with `sorry` proofs; filling them in is the
next milestone.  Every proof, when written, must use only kan-tactics in
tactic blocks (term-mode proofs are unrestricted). -/


set_option autoImplicit false

namespace ArrowCat

universe u

variable {m : Nat} {α : Type u}

/-- **Extremal Lemma.**

If `f` satisfies Pareto and IIA, and every voter places `b` extremally
(top or bottom of their personal ranking), then the social preference
also places `b` extremally.

Proof sketch (Geanakoplos): suppose for contradiction that society
places some `a ≠ b` strictly above `b` and some `c ≠ b` strictly below
`b`.  Construct a modified profile that preserves every voter's ranking
of `a` versus `b` and of `c` versus `b`, but flips `a` versus `c` to
match Pareto unanimity.  IIA forces society's `(a,b)` and `(b,c)`
rankings to be unchanged, transitivity then forces `a` strictly above
`c`, contradicting Pareto on the modified profile. -/
theorem extremalLemma
    (f : SWF m α) (_hPareto : SWF.Pareto f) (_hIIA : SWF.IIA f)
    (p : Profile m α) (b : α)
    (_hAllExtreme : ∀ i : Fin m, (p i).isExtreme b) :
    (f p).isExtreme b := by
  sorry

/-- **Pivotal Voter / Local Dictatorship.**

There exists a voter `k` such that for any two alternatives `a, c`
neither of which is `b`, the social preference always agrees with voter
`k`'s strict preference on `(a, c)`.

Proof sketch (Geanakoplos): start from any profile in which every voter
places `b` strictly at the bottom (Pareto then forces `b` strictly at
the bottom for society).  Move `b` to the top one voter at a time.
After all voters have flipped, Pareto forces `b` strictly at the top.
The extremal lemma guarantees that at every intermediate step, society
puts `b` at exactly one extreme; therefore society's stance on `b`
flips at some specific voter `k`.  IIA + the construction shows `k`'s
preferences over any `(a, c)` not involving `b` determine society's. -/
theorem pivotalVoterIsLocalDictator
    (f : SWF m α) (_hPareto : SWF.Pareto f) (_hIIA : SWF.IIA f)
    (_h1 : 0 < m) (_h3 : AtLeastThree α) (b : α) :
    ∃ k : Fin m, ∀ a c : α, a ≠ b → c ≠ b →
      ∀ p : Profile m α, (p k).pref a c → (f p).pref a c := by
  sorry

/-- **Pivot-voter consistency across choices of `b`.**

If `k` is the pivotal voter for `b`, then `k` is also the pivotal voter
for any other alternative `b'`.  This is what promotes local
dictatorship into global dictatorship.

Proof sketch: each voter who is a local dictator over the pair `(a, c)`
for `a, c ≠ b` can be extended to dictate `(b, x)` via a triangle-shaped
argument with a third alternative `x ≠ b`; the same `k` works in every
case because there is only one voter at whom society's stance flips in
the pivotal sequence. -/
theorem pivotalVoterUnique
    (f : SWF m α) (_hPareto : SWF.Pareto f) (_hIIA : SWF.IIA f)
    (_h1 : 0 < m) (_h3 : AtLeastThree α) (b b' : α) (_hbb' : b ≠ b') :
    ∃ k : Fin m,
      (∀ a c : α, a ≠ b  → c ≠ b  → ∀ p : Profile m α, (p k).pref a c → (f p).pref a c) ∧
      (∀ a c : α, a ≠ b' → c ≠ b' → ∀ p : Profile m α, (p k).pref a c → (f p).pref a c) := by
  sorry

end ArrowCat
