import ArrowCat.Basic
import ArrowCat.Move
import ArrowCat.Geanakoplos
import KanTactics

/-! # Staircase profile and pivotal voter

For a fixed alternative `b`, the *staircase profile* `staircase q b k`
sends each voter `i` to either `moveBToTop (q i) b` (when `i < k`) or
`moveBToBottom (q i) b` (otherwise).  As `k` ranges over `0, 1, ..., m`:

- `staircase q b 0` puts every voter with `b` at the bottom;
- `staircase q b m` puts every voter with `b` at the top;
- every intermediate `staircase q b k` has every voter placing `b`
  extremally, so by `extremalLemma` (in `ArrowCat.Geanakoplos`) society
  also places `b` extremally.

By Pareto, society places `b` at the bottom in `staircase q b 0` and at
the top in `staircase q b m`, so there is a least `k` at which society
flips.  That `k` -- one-indexed into the staircase, or equivalently the
zero-indexed voter `k - 1` who was newly added -- is the *pivotal voter
for `b`*. -/


set_option autoImplicit false

namespace ArrowCat

universe u
variable {m : Nat} {α : Type u}

/-- The staircase profile for parameter `k`.  Voters `0, 1, ..., k-1`
have `b` at the top; voters `k, k+1, ..., m-1` have `b` at the bottom. -/
noncomputable def staircase (q : Profile m α) (b : α) (k : Nat) :
    Profile m α :=
  fun i => if i.val < k then (q i).moveBToTop b else (q i).moveBToBottom b

/-- Every voter in the staircase places `b` extremally. -/
theorem staircase_isExtreme (q : Profile m α) (b : α) (k : Nat) (i : Fin m) :
    (staircase q b k i).isExtreme b :=
  if h : i.val < k then
    have heq : staircase q b k i = (q i).moveBToTop b := if_pos h
    heq ▸ Or.inl ((q i).moveBToTop_isTop b)
  else
    have heq : staircase q b k i = (q i).moveBToBottom b := if_neg h
    heq ▸ Or.inr ((q i).moveBToBottom_isBottom b)

/-- At `k = 0` the staircase puts every voter with `b` at the bottom. -/
theorem staircase_zero_isBottom (q : Profile m α) (b : α) (i : Fin m) :
    (staircase q b 0 i).isBottom b :=
  have heq : staircase q b 0 i = (q i).moveBToBottom b :=
    if_neg (Nat.not_lt_zero i.val)
  heq ▸ (q i).moveBToBottom_isBottom b

/-- At `k = m` the staircase puts every voter with `b` at the top. -/
theorem staircase_max_isTop (q : Profile m α) (b : α) (i : Fin m) :
    (staircase q b m i).isTop b :=
  have heq : staircase q b m i = (q i).moveBToTop b := if_pos i.isLt
  heq ▸ (q i).moveBToTop_isTop b

/-- Society places `b` at the bottom in the all-bottom staircase. -/
theorem swf_staircase_zero_isBottom (f : SWF m α) (hPareto : SWF.Pareto f)
    (q : Profile m α) (b : α) :
    (f (staircase q b 0)).isBottom b :=
  fun x hxb => hPareto _ x b
    (fun i => staircase_zero_isBottom q b i x hxb)

/-- Society places `b` at the top in the all-top staircase. -/
theorem swf_staircase_max_isTop (f : SWF m α) (hPareto : SWF.Pareto f)
    (q : Profile m α) (b : α) :
    (f (staircase q b m)).isTop b :=
  fun x hxb => hPareto _ b x
    (fun i => staircase_max_isTop q b i x hxb)

/-- Society places `b` extremally in every staircase profile.  Requires
the extremal lemma. -/
theorem swf_staircase_isExtreme [DecidableEq α]
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) (b : α) (k : Nat) :
    (f (staircase q b k)).isExtreme b :=
  extremalLemma f hPareto hIIA (staircase q b k) b
    (fun i => staircase_isExtreme q b k i)

/-! ### The pivotal voter

Lean 4 core does not provide `Nat.find` (it lives in Mathlib), so we
state the existence of the pivot index/voter as a theorem and prove it
by a boundary-finding induction on the staircase, then use
`Classical.choose` to extract a witness.  The boundary lemma itself is
plain `Nat` reasoning and is parameterised by an arbitrary decidable
predicate so it can be reused. -/

section Pivot
open Classical

/-- **Nat boundary lemma.**  For any decidable predicate that fails at
`0` and holds at `n`, there is a "flip index" `k ∈ [1, n]` such that
`P k` holds and `P (k - 1)` does not.

Proof: induction on `n`.  Base case `n = 0` is vacuous (`P 0`
contradicts `¬ P 0`).  Step case: if `P n'` holds, the induction
hypothesis gives a boundary in `[1, n']`; otherwise `n' + 1` itself is
the boundary, since `P (n' + 1)` (the hypothesis) and `¬ P n'`. -/
theorem Nat.exists_boundary (P : Nat → Prop) [DecidablePred P]
    (n : Nat) (hP_n : P n) (hP_0 : ¬ P 0) :
    ∃ k, 1 ≤ k ∧ k ≤ n ∧ P k ∧ ¬ P (k - 1) :=
  Nat.rec
    (motive := fun n => P n → ¬ P 0 →
      ∃ k, 1 ≤ k ∧ k ≤ n ∧ P k ∧ ¬ P (k - 1))
    (fun hP0 hnP0 => absurd hP0 hnP0)
    (fun n' ih hPn1 hnP0 =>
      if hPn : P n' then
        let ⟨k, hk1, hkn, hPk, hPnk⟩ := ih hPn hnP0
        ⟨k, hk1, Nat.le_succ_of_le hkn, hPk, hPnk⟩
      else
        ⟨n' + 1, Nat.succ_le_succ (Nat.zero_le _),
         Nat.le_refl _, hPn1, hPn⟩)
    n hP_n hP_0

/-- **Existence of the pivotal voter for `b`.**

Given any `x ≠ b`, there is an index `k : Fin m` (the pivotal voter)
such that the staircase at `k + 1` puts `b` at the top (via society)
while the staircase at `k` puts `b` at the bottom.

Proof outline: apply `Nat.exists_boundary` to the predicate
`P k := (f (staircase q b k)).isTop b`, using `swf_staircase_max_isTop`
as the `n = m` witness and (asymmetry against any `x ≠ b` combined
with) `swf_staircase_zero_isBottom` to rule out `P 0`.  The resulting
flip index `k*` lies in `[1, m]`; the pivotal voter is `k* - 1`. -/
theorem exists_pivotalVoter [DecidableEq α] (_h1 : 0 < m)
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) {b x : α} (hxb : x ≠ b) :
    ∃ k : Fin m,
      (f (staircase q b (k.val + 1))).isTop b ∧
      (f (staircase q b k.val)).isBottom b := by
  -- Set up the boundary predicate
  have hP_m : (f (staircase q b m)).isTop b :=
    swf_staircase_max_isTop f hPareto q b
  have hP_0 : ¬ (f (staircase q b 0)).isTop b := fun hTop =>
    have hBot : (f (staircase q b 0)).isBottom b :=
      swf_staircase_zero_isBottom f hPareto q b
    (f (staircase q b 0)).asym b x (hTop x hxb) (hBot x hxb)
  let ⟨k, hk1, hkm, hPk, hPnk⟩ :=
    Nat.exists_boundary (fun k => (f (staircase q b k)).isTop b) m hP_m hP_0
  -- k ∈ [1, m]. Pivotal voter is k - 1 : Fin m.
  -- k.val + 1 = k after substitution (need k - 1 + 1 = k)
  have hk_pos : 0 < k := hk1
  have hk_pred_lt_m : k - 1 < m :=
    Nat.lt_of_lt_of_le (Nat.sub_lt hk_pos Nat.one_pos) hkm
  have hk_succ_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  kan_refine ⟨⟨k - 1, hk_pred_lt_m⟩, ?_, ?_⟩
  · -- (f (staircase q b (k - 1 + 1))).isTop b  =  (f (staircase q b k)).isTop b
    kan_exact Eq.mpr
      (congrArg (fun n => (f (staircase q b n)).isTop b) hk_succ_eq) hPk
  · -- (f (staircase q b (k - 1))).isBottom b
    -- We have ¬ (f (staircase q b (k - 1))).isTop b (hPnk).
    -- By extremal lemma, society places b extremally.  Not top means bottom.
    kan_exact (swf_staircase_isExtreme f hPareto hIIA q b (k - 1)).resolve_left hPnk

/-- The pivotal voter, as a `Fin m`.  Classical choice on
`exists_pivotalVoter`. -/
noncomputable def pivotalVoter [DecidableEq α] (h1 : 0 < m)
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) {b x : α} (hxb : x ≠ b) : Fin m :=
  (exists_pivotalVoter h1 f hPareto hIIA q hxb).choose

/-- The pivotal voter has the "flip-to-top" property at `+1`. -/
theorem pivotalVoter_succ_isTop [DecidableEq α] (h1 : 0 < m)
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) {b x : α} (hxb : x ≠ b) :
    (f (staircase q b ((pivotalVoter h1 f hPareto hIIA q hxb).val + 1))).isTop b :=
  (exists_pivotalVoter h1 f hPareto hIIA q hxb).choose_spec.1

/-- The pivotal voter has the "isBottom" property at itself. -/
theorem pivotalVoter_isBottom [DecidableEq α] (h1 : 0 < m)
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) {b x : α} (hxb : x ≠ b) :
    (f (staircase q b (pivotalVoter h1 f hPareto hIIA q hxb).val)).isBottom b :=
  (exists_pivotalVoter h1 f hPareto hIIA q hxb).choose_spec.2

end Pivot

/-- From three pairwise-distinct alternatives, at least one of them
differs from any given `b`. -/
theorem AtLeastThree.exists_ne (h3 : AtLeastThree α) (b : α) : ∃ x : α, x ≠ b :=
  let ⟨x, y, _, hxy, _, _⟩ := h3
  Classical.byCases
    (fun (hxb : x = b) => ⟨y, fun heq => hxy (hxb.trans heq.symm)⟩)
    (fun hxb => ⟨x, hxb⟩)

/-! ### Local dictatorship of the pivotal voter

The Geanakoplos argument: starting from the pivotal voter `k` of a
fixed base profile `q`, any input profile `p` with `(p k).pref a c`
(for `a, c ≠ b`) satisfies `(f p).pref a c`.

The proof of the dictator-over-`(a, c)`-when-neither-is-`b` direction
(the conclusion of `pivotalVoterIsLocalDictator`) goes by constructing
an intermediate profile `p'` from `p` that

- preserves every voter's `(a, c)` ranking (so IIA on `(a, c)` keeps the
  social ranking of `(a, c)` unchanged between `p` and `p'`);
- aligns every voter's `b`-position with the staircase profile that
  exhibits the pivotal flip (so the pivotal-voter spec + extremal lemma
  give `(f p').pref a b` and `(f p').pref b c`);
- transitivity of `(f p')` then yields `(f p').pref a c`, which by IIA
  transfers back to `(f p).pref a c`.

That intermediate-profile construction is itself nontrivial and is
left as the inner `sorry` of the proof below; everything around it
(case-splitting on `Nonempty (Profile m α)`, extracting the witness `x
≠ b`, defining `k` via `pivotalVoter`) is in place. -/

/-- **Pivotal voter is a local dictator.**

There exists a voter `k` such that for any two alternatives `a, c`
neither of which is `b`, society's preference always agrees with voter
`k`'s.

When `Profile m α` is empty, the universal `∀ p` is vacuous and any
`k : Fin m` works; when it is nonempty, we pick a base profile `q` via
`Classical.choice` and take `k := pivotalVoter h1 f hPareto hIIA q hxb`.
The proper Geanakoplos dictator-over-`(a, c)` argument is the inner
`sorry`. -/
theorem pivotalVoterIsLocalDictator [DecidableEq α]
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (h1 : 0 < m) (h3 : AtLeastThree α) (b : α) :
    ∃ k : Fin m, ∀ a c : α, a ≠ b → c ≠ b →
      ∀ p : Profile m α, (p k).pref a c → (f p).pref a c :=
  let ⟨x, hxb⟩ := AtLeastThree.exists_ne h3 b
  Classical.byCases
    (fun hNE : Nonempty (Profile m α) =>
      let q := Classical.choice hNE
      let k := pivotalVoter h1 f hPareto hIIA q hxb
      ⟨k, fun _a _c _hab _hcb _p _hpac =>
        -- Inner Geanakoplos construction: build p' from p that preserves
        -- every voter's (a, c) ranking and aligns b-positions with
        -- staircase q b (k.val + 1) for the pivotal flip.  Then apply
        -- IIA + extremalLemma + transitivity.  Deferred.
        sorry⟩)
    (fun hNE : ¬ Nonempty (Profile m α) =>
      -- Profile m α is empty; the inner ∀ p is vacuous.
      ⟨⟨0, h1⟩, fun _ _ _ _ p _ => absurd (Nonempty.intro p) hNE⟩)

/-- **Pivot-voter consistency across choices of `b`.**

The pivotal voter for `b` is also the pivotal voter for any other
alternative `b'`.  Promoted from local to global dictatorship by
applying `pivotalVoterIsLocalDictator` for two different `b` choices
and observing that every pair `(a, c)` avoids at least one of them.

Stub: defers to the local-dictatorship lemma above plus a triangle
argument that recovers `(b, ·)` dictatorship from `(·, b')` results. -/
theorem pivotalVoterUnique [DecidableEq α]
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (h1 : 0 < m) (h3 : AtLeastThree α) (b b' : α) (_hbb' : b ≠ b') :
    ∃ k : Fin m,
      (∀ a c : α, a ≠ b  → c ≠ b  → ∀ p : Profile m α, (p k).pref a c → (f p).pref a c) ∧
      (∀ a c : α, a ≠ b' → c ≠ b' → ∀ p : Profile m α, (p k).pref a c → (f p).pref a c) := by
  sorry

end ArrowCat
