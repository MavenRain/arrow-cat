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

/-- **Existence of a `(c, a)`-modified profile.**

Given a profile in which every voter places `b` extremally and three
distinct alternatives `a`, `b`, `c`, there exists a modified profile
`p'` such that

1. every voter ranks `c` strictly above `a` in `p'`, and
2. for every voter, the relative ranking of `(a, b)` is unchanged
   between `p` and `p'`, and
3. for every voter, the relative ranking of `(b, c)` is unchanged
   between `p` and `p'`.

The construction (deferred to a future session): for each voter, define
`p' i` as `p i` with `a` and `c` swapped whenever `p i` ranks `a` above
`c`; this preserves the extremal position of `b` (since `b ≠ a, c`) and
hence preserves every `(a, b)` and `(b, c)` ranking.  Formalising the
swap requires `DecidableEq α` and a case-analysis-heavy injectivity
proof, both of which are out of scope for this pass. -/
theorem exists_modified_profile
    (p : Profile m α) (a b c : α)
    (_hab : a ≠ b) (_hcb : c ≠ b) (_hac : a ≠ c)
    (_hExt : ∀ i : Fin m, (p i).isExtreme b) :
    ∃ p' : Profile m α,
      (∀ i : Fin m, (p' i).pref c a) ∧
      (∀ i : Fin m, (p' i).pref a b ↔ (p i).pref a b) ∧
      (∀ i : Fin m, (p' i).pref b c ↔ (p i).pref b c) := by
  sorry

/-- **Extremal Lemma.**

If `f` satisfies Pareto and IIA, and every voter places `b` extremally
(top or bottom of their personal ranking), then the social preference
also places `b` extremally.

Proof (Geanakoplos): suppose for contradiction `(f p).isExtreme b` fails.
Then society places neither `b` at the top nor at the bottom, so there
exist `a, c ≠ b` with `(f p).pref a b` and `(f p).pref b c`.  These must
be distinct, since `a = c` together with the two preferences would
contradict asymmetry.  Apply `exists_modified_profile` to obtain `p'`
that (i) makes every voter rank `c ≻ a` and (ii) preserves every
voter's `(a, b)` and `(b, c)` rankings.  By IIA, society's rankings of
`(a, b)` and `(b, c)` are the same in `p'` as in `p`; by transitivity of
the social order, `(f p').pref a c`.  By Pareto on `p'`, `(f p').pref
c a`.  Asymmetry then yields `False`. -/
theorem extremalLemma
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (p : Profile m α) (b : α)
    (hAllExtreme : ∀ i : Fin m, (p i).isExtreme b) :
    (f p).isExtreme b :=
  Classical.byContradiction fun hne =>
    let hNotTop : ¬ (f p).isTop b    := fun hT => hne (Or.inl hT)
    let hNotBot : ¬ (f p).isBottom b := fun hB => hne (Or.inr hB)
    let ⟨a, hab, hpAB⟩ := (f p).exists_pref_of_not_isTop b hNotTop
    let ⟨c, hcb, hpBC⟩ := (f p).exists_pref_of_not_isBottom b hNotBot
    let hac : a ≠ c := fun heq =>
      (f p).asym a b hpAB (heq.symm ▸ hpBC)
    let ⟨p', hCA, hABeq, hBCeq⟩ :=
      exists_modified_profile p a b c hab hcb hac hAllExtreme
    let h_fp'_AB : (f p').pref a b := (hIIA p' p a b hABeq).mpr hpAB
    let h_fp'_BC : (f p').pref b c := (hIIA p' p b c hBCeq).mpr hpBC
    let h_fp'_AC : (f p').pref a c := (f p').trans a b c h_fp'_AB h_fp'_BC
    let h_fp'_CA : (f p').pref c a := hPareto p' c a hCA
    (f p').asym a c h_fp'_AC h_fp'_CA

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
