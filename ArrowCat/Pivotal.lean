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

/-- Case lemma: in the "top" branch of the staircase. -/
theorem staircase_lt {q : Profile m α} {b : α} {k : Nat} {i : Fin m}
    (h : i.val < k) :
    staircase q b k i = (q i).moveBToTop b := if_pos h

/-- Case lemma: in the "bottom" branch of the staircase. -/
theorem staircase_ge {q : Profile m α} {b : α} {k : Nat} {i : Fin m}
    (h : ¬ i.val < k) :
    staircase q b k i = (q i).moveBToBottom b := if_neg h

/-- Every voter in the staircase places `b` extremally. -/
theorem staircase_isExtreme (q : Profile m α) (b : α) (k : Nat) (i : Fin m) :
    (staircase q b k i).isExtreme b :=
  if h : i.val < k then
    (staircase_lt h) ▸ Or.inl ((q i).moveBToTop_isTop b)
  else
    (staircase_ge h) ▸ Or.inr ((q i).moveBToBottom_isBottom b)

/-- At `k = 0` the staircase puts every voter with `b` at the bottom. -/
theorem staircase_zero_isBottom (q : Profile m α) (b : α) (i : Fin m) :
    (staircase q b 0 i).isBottom b :=
  (staircase_ge (Nat.not_lt_zero i.val)) ▸ (q i).moveBToBottom_isBottom b

/-- At `k = m` the staircase puts every voter with `b` at the top. -/
theorem staircase_max_isTop (q : Profile m α) (b : α) (i : Fin m) :
    (staircase q b m i).isTop b :=
  (staircase_lt i.isLt) ▸ (q i).moveBToTop_isTop b

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
  have hP_m : (f (staircase q b m)).isTop b :=
    swf_staircase_max_isTop f hPareto q b
  have hP_0 : ¬ (f (staircase q b 0)).isTop b := fun hTop =>
    have hBot : (f (staircase q b 0)).isBottom b :=
      swf_staircase_zero_isBottom f hPareto q b
    (f (staircase q b 0)).asym b x (hTop x hxb) (hBot x hxb)
  let ⟨k, hk1, hkm, hPk, hPnk⟩ :=
    Nat.exists_boundary (fun k => (f (staircase q b k)).isTop b) m hP_m hP_0
  have hk_pos : 0 < k := hk1
  have hk_pred_lt_m : k - 1 < m :=
    Nat.lt_of_lt_of_le (Nat.sub_lt hk_pos Nat.one_pos) hkm
  have hk_succ_eq : k - 1 + 1 = k := Nat.sub_add_cancel hk1
  kan_refine ⟨⟨k - 1, hk_pred_lt_m⟩, ?_, ?_⟩
  · kan_exact Eq.mpr
      (congrArg (fun n => (f (staircase q b n)).isTop b) hk_succ_eq) hPk
  · kan_exact (swf_staircase_isExtreme f hPareto hIIA q b (k - 1)).resolve_left hPnk

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

/-- From three pairwise-distinct alternatives, at least one of them
differs from each of two given alternatives `b, b'`.  (Pigeonhole: at
most one of the three equals `b`, at most one equals `b'`, so at least
`3 - 1 - 1 = 1` avoids both.) -/
theorem AtLeastThree.exists_ne_two (h3 : AtLeastThree α) (b b' : α) (_hbb' : b ≠ b') :
    ∃ a : α, a ≠ b ∧ a ≠ b' :=
  let ⟨a1, a2, a3, h12, h23, h13⟩ := h3
  Classical.byCases
    (fun h1b : a1 = b =>
      Classical.byCases
        (fun h2b' : a2 = b' =>
          ⟨a3, fun heq => h13 (h1b.trans heq.symm),
               fun heq => h23 (h2b'.trans heq.symm)⟩)
        (fun h2b' : a2 ≠ b' =>
          ⟨a2, fun heq => h12 (h1b.trans heq.symm), h2b'⟩))
    (fun h1b : a1 ≠ b =>
      Classical.byCases
        (fun h1b' : a1 = b' =>
          Classical.byCases
            (fun h2b : a2 = b =>
              ⟨a3, fun heq => h23 (h2b.trans heq.symm),
                   fun heq => h13 (h1b'.trans heq.symm)⟩)
            (fun h2b : a2 ≠ b =>
              ⟨a2, h2b, fun heq => h12 (h1b'.trans heq.symm)⟩))
        (fun h1b' : a1 ≠ b' =>
          ⟨a1, h1b, h1b'⟩))

/-! ### Local dictatorship of the pivotal voter

The Geanakoplos construction: build an auxiliary profile `p'` that
preserves every voter's `(a, c)` ranking and aligns the per-voter
`b`-positions with the staircases that exhibit the pivotal flip.
Voter `k`'s ranking is set to `a > b > c` (via two `moveBToTop`
applications) so that `(p' k).pref a b`, `(p' k).pref b c`, and
`(p' k).pref a c` all hold; voters before `k` have `b` at the top
(via `moveBToTop`); voters after have `b` at the bottom (via
`moveBToBottom`). -/

section LocalDictator

variable {a b c : α}

private theorem iff_of_true' {p q : Prop} (hp : p) (hq : q) : p ↔ q :=
  ⟨fun _ => hq, fun _ => hp⟩

private theorem iff_of_false' {p q : Prop} (hnp : ¬ p) (hnq : ¬ q) : p ↔ q :=
  ⟨fun hp => absurd hp hnp, fun hq => absurd hq hnq⟩

/-- The auxiliary profile used in the proof of
`pivotalVoterIsLocalDictator`. -/
noncomputable def localDictAuxProfile (p : Profile m α) (k : Fin m)
    (a b : α) : Profile m α :=
  fun i =>
    if i.val < k.val then (p i).moveBToTop b
    else if i.val = k.val then ((p i).moveBToTop b).moveBToTop a
    else (p i).moveBToBottom b

private theorem localDictAuxProfile_lt {p : Profile m α} {k : Fin m} {i : Fin m}
    (h : i.val < k.val) :
    localDictAuxProfile p k a b i = (p i).moveBToTop b := if_pos h

private theorem localDictAuxProfile_eq {p : Profile m α} {k : Fin m} {i : Fin m}
    (h1 : ¬ i.val < k.val) (h2 : i.val = k.val) :
    localDictAuxProfile p k a b i = ((p i).moveBToTop b).moveBToTop a :=
  (if_neg h1).trans (if_pos h2)

private theorem localDictAuxProfile_gt {p : Profile m α} {k : Fin m} {i : Fin m}
    (h1 : ¬ i.val < k.val) (h2 : ¬ i.val = k.val) :
    localDictAuxProfile p k a b i = (p i).moveBToBottom b :=
  (if_neg h1).trans (if_neg h2)

/-- The auxiliary profile preserves every voter's `(a, c)` ranking. -/
theorem localDictAuxProfile_pref_ac
    {p : Profile m α} {k : Fin m}
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (hpac : (p k).pref a c) (i : Fin m) :
    (localDictAuxProfile p k a b i).pref a c ↔ (p i).pref a c :=
  if h1 : i.val < k.val then
    (Iff.of_eq (congrArg (fun r : StrictPref α => r.pref a c)
      (localDictAuxProfile_lt h1))).trans
      ((p i).moveBToTop_pref_iff_of_ne b hab hcb)
  else if h2 : i.val = k.val then
    have hik : i = k := Fin.ext h2
    have hLHS : (localDictAuxProfile p k a b i).pref a c :=
      Eq.mpr (congrArg (fun r : StrictPref α => r.pref a c)
        (localDictAuxProfile_eq h1 h2))
        (Or.inl ⟨rfl, hac⟩ : (((p i).moveBToTop b).moveBToTop a).pref a c)
    have hRHS : (p i).pref a c :=
      Eq.mpr (congrArg (fun j => (p j).pref a c) hik) hpac
    iff_of_true' hLHS hRHS
  else
    (Iff.of_eq (congrArg (fun r : StrictPref α => r.pref a c)
      (localDictAuxProfile_gt h1 h2))).trans
      ((p i).moveBToBottom_pref_iff_of_ne b hab hcb)

/-- For each voter, the auxiliary profile's `(a, b)` ranking matches the
staircase at parameter `k.val`. -/
theorem localDictAuxProfile_pref_ab_iff_staircase
    {p q : Profile m α} {k : Fin m} (hab : a ≠ b)
    (i : Fin m) :
    (localDictAuxProfile p k a b i).pref a b ↔
        (staircase q b k.val i).pref a b :=
  if h1 : i.val < k.val then
    iff_of_false'
      (fun h_aux => (p i).moveBToTop_not_pref_other_b hab
        (Eq.mp (congrArg (fun r : StrictPref α => r.pref a b)
          (localDictAuxProfile_lt h1)) h_aux))
      (fun h_stair => (q i).moveBToTop_not_pref_other_b hab
        (Eq.mp (congrArg (fun r : StrictPref α => r.pref a b)
          (staircase_lt h1)) h_stair))
  else if h2 : i.val = k.val then
    iff_of_true'
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref a b)
        (localDictAuxProfile_eq h1 h2))
        (Or.inl ⟨rfl, hab⟩ : (((p i).moveBToTop b).moveBToTop a).pref a b))
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref a b)
        (staircase_ge h1))
        ((q i).moveBToBottom_pref_other_b hab))
  else
    iff_of_true'
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref a b)
        (localDictAuxProfile_gt h1 h2))
        ((p i).moveBToBottom_pref_other_b hab))
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref a b)
        (staircase_ge h1))
        ((q i).moveBToBottom_pref_other_b hab))

/-- For each voter, the auxiliary profile's `(b, c)` ranking matches the
staircase at parameter `k.val + 1`. -/
theorem localDictAuxProfile_pref_bc_iff_staircase_succ
    {p q : Profile m α} {k : Fin m}
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (i : Fin m) :
    (localDictAuxProfile p k a b i).pref b c ↔
        (staircase q b (k.val + 1) i).pref b c :=
  if h1 : i.val < k.val then
    have h1' : i.val < k.val + 1 := Nat.lt_succ_of_lt h1
    iff_of_true'
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref b c)
        (localDictAuxProfile_lt h1))
        ((p i).moveBToTop_pref_b_other hcb))
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref b c)
        (staircase_lt h1'))
        ((q i).moveBToTop_pref_b_other hcb))
  else if h2 : i.val = k.val then
    have h_lt : i.val < k.val + 1 :=
      Eq.mpr (congrArg (· < k.val + 1) h2) (Nat.lt_succ_self k.val)
    have hLHS : (((p i).moveBToTop b).moveBToTop a).pref b c :=
      Or.inr ⟨fun heq => hab heq.symm,
              fun heq => hac heq.symm,
              (p i).moveBToTop_pref_b_other hcb⟩
    iff_of_true'
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref b c)
        (localDictAuxProfile_eq h1 h2)) hLHS)
      (Eq.mpr (congrArg (fun r : StrictPref α => r.pref b c)
        (staircase_lt h_lt))
        ((q i).moveBToTop_pref_b_other hcb))
  else
    have h_not_lt : ¬ i.val < k.val + 1 := fun h =>
      h2 (Nat.le_antisymm (Nat.le_of_lt_succ h) (Nat.not_lt.mp h1))
    iff_of_false'
      (fun h_aux => (p i).moveBToBottom_not_pref_b_other hcb
        (Eq.mp (congrArg (fun r : StrictPref α => r.pref b c)
          (localDictAuxProfile_gt h1 h2)) h_aux))
      (fun h_stair => (q i).moveBToBottom_not_pref_b_other hcb
        (Eq.mp (congrArg (fun r : StrictPref α => r.pref b c)
          (staircase_ge h_not_lt)) h_stair))

end LocalDictator

/-- The core local-dictator argument for a fixed base profile `q`.

Given the pivotal voter `k := pivotalVoter h1 f hPareto hIIA q hxb`,
for any pair `(a, c)` with `a, c ≠ b` and any profile `p` with `(p k).pref
a c`, society's preference `(f p).pref a c` holds.  This is the inner
content of `pivotalVoterIsLocalDictator`; extracting it as a separate
lemma lets `pivotalVoterUnique` reuse it without going through the
existential. -/
theorem pivotalVoter_dictates_nonB [DecidableEq α] (h1 : 0 < m)
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) {b x : α} (hxb : x ≠ b)
    (a c : α) (hab : a ≠ b) (hcb : c ≠ b)
    (p : Profile m α) (hpac : (p (pivotalVoter h1 f hPareto hIIA q hxb)).pref a c) :
    (f p).pref a c :=
  Classical.byCases
    (fun heq : a = c =>
      absurd
        (Eq.mpr (congrArg (fun y => (p (pivotalVoter h1 f hPareto hIIA q hxb)).pref a y) heq) hpac)
        ((p (pivotalVoter h1 f hPareto hIIA q hxb)).irrefl a))
    (fun hac : a ≠ c =>
      let k := pivotalVoter h1 f hPareto hIIA q hxb
      let p' := localDictAuxProfile p k a b
      let iff_ac : ∀ i, (p' i).pref a c ↔ (p i).pref a c :=
        fun i => localDictAuxProfile_pref_ac hab hcb hac hpac i
      let iff_ab : ∀ i, (p' i).pref a b ↔ (staircase q b k.val i).pref a b :=
        fun i => localDictAuxProfile_pref_ab_iff_staircase hab i
      let iff_bc : ∀ i, (p' i).pref b c ↔ (staircase q b (k.val + 1) i).pref b c :=
        fun i => localDictAuxProfile_pref_bc_iff_staircase_succ hab hcb hac i
      have fp'_ab : (f p').pref a b :=
        (hIIA p' (staircase q b k.val) a b iff_ab).mpr
          (pivotalVoter_isBottom h1 f hPareto hIIA q hxb a hab)
      have fp'_bc : (f p').pref b c :=
        (hIIA p' (staircase q b (k.val + 1)) b c iff_bc).mpr
          (pivotalVoter_succ_isTop h1 f hPareto hIIA q hxb c hcb)
      have fp'_ac : (f p').pref a c := (f p').trans a b c fp'_ab fp'_bc
      (hIIA p' p a c iff_ac).mp fp'_ac)

/-- **Pivotal voter is a local dictator.**  Thin wrapper around
`pivotalVoter_dictates_nonB` that picks a base profile via `Classical.choice`
in the non-empty case (and falls back to a vacuous proof if `Profile m α`
is empty). -/
theorem pivotalVoterIsLocalDictator [DecidableEq α]
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (h1 : 0 < m) (h3 : AtLeastThree α) (b : α) :
    ∃ k : Fin m, ∀ a c : α, a ≠ b → c ≠ b →
      ∀ p : Profile m α, (p k).pref a c → (f p).pref a c :=
  let ⟨_x, hxb⟩ := AtLeastThree.exists_ne h3 b
  Classical.byCases
    (fun hNE : Nonempty (Profile m α) =>
      let q := Classical.choice hNE
      ⟨pivotalVoter h1 f hPareto hIIA q hxb,
       pivotalVoter_dictates_nonB h1 f hPareto hIIA q hxb⟩)
    (fun hNE : ¬ Nonempty (Profile m α) =>
      ⟨⟨0, h1⟩, fun _ _ _ _ p _ => absurd (Nonempty.intro p) hNE⟩)

/-- **The pivotal voter is the same for any two alternatives.**

If `k_b` and `k_{b'}` are the pivotal voters for `b` and `b'` (in a
shared base profile `q`), then `k_b = k_{b'}`.

Proof: pick an alternative `a` distinct from both `b` and `b'`.  In the
staircase profile `S_low := staircase q b' k_{b'}.val`, society places
`b'` at the bottom, so `(f S_low).pref a b'`; by asymmetry, `(f
S_low).pref b' a` is false.  By contrapositive of `k_b`'s dictatorship
over `(b', a)` (a pair avoiding `b`), voter `k_b`'s `(b', a)` ranking
in `S_low` is also false.  But `S_low` puts `b'` at the top for voter
`k_b` iff `k_b.val < k_{b'}.val`; so we must have `k_b.val ≥ k_{b'}.val`.
The symmetric staircase `staircase q b' (k_{b'}.val + 1)` gives
`k_b.val ≤ k_{b'}.val`, and `Fin.ext` concludes. -/
theorem pivotalVoter_eq_of_different_b [DecidableEq α] (h1 : 0 < m) (h3 : AtLeastThree α)
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (q : Profile m α) {b b' x x' : α} (hbb' : b ≠ b') (hxb : x ≠ b) (hxb' : x' ≠ b') :
    pivotalVoter h1 f hPareto hIIA q hxb = pivotalVoter h1 f hPareto hIIA q hxb' :=
  let k_b := pivotalVoter h1 f hPareto hIIA q hxb
  let k_b' := pivotalVoter h1 f hPareto hIIA q hxb'
  let ⟨a, hab, hab'⟩ := AtLeastThree.exists_ne_two h3 b b' hbb'
  have h_geq : k_b'.val ≤ k_b.val :=
    if h : k_b.val < k_b'.val then
      have hS : staircase q b' k_b'.val k_b = (q k_b).moveBToTop b' := staircase_lt h
      have h_pref : (staircase q b' k_b'.val k_b).pref b' a :=
        Eq.mpr (congrArg (fun r : StrictPref α => r.pref b' a) hS)
          ((q k_b).moveBToTop_pref_b_other hab')
      have h_f : (f (staircase q b' k_b'.val)).pref b' a :=
        pivotalVoter_dictates_nonB h1 f hPareto hIIA q hxb b' a (Ne.symm hbb') hab _ h_pref
      have h_pref_ab : (f (staircase q b' k_b'.val)).pref a b' :=
        pivotalVoter_isBottom h1 f hPareto hIIA q hxb' a hab'
      absurd h_f ((f (staircase q b' k_b'.val)).asym a b' h_pref_ab)
    else
      Nat.le_of_not_lt h
  have h_leq : k_b.val ≤ k_b'.val :=
    if h : k_b'.val < k_b.val then
      have h_ge : k_b'.val + 1 ≤ k_b.val := Nat.succ_le_of_lt h
      have h_not_lt : ¬ k_b.val < k_b'.val + 1 := Nat.not_lt.mpr h_ge
      have hS : staircase q b' (k_b'.val + 1) k_b = (q k_b).moveBToBottom b' :=
        staircase_ge h_not_lt
      have h_pref : (staircase q b' (k_b'.val + 1) k_b).pref a b' :=
        Eq.mpr (congrArg (fun r : StrictPref α => r.pref a b') hS)
          ((q k_b).moveBToBottom_pref_other_b hab')
      have h_f : (f (staircase q b' (k_b'.val + 1))).pref a b' :=
        pivotalVoter_dictates_nonB h1 f hPareto hIIA q hxb a b' hab (Ne.symm hbb') _ h_pref
      have h_pref_b'a : (f (staircase q b' (k_b'.val + 1))).pref b' a :=
        pivotalVoter_succ_isTop h1 f hPareto hIIA q hxb' a hab'
      absurd h_f ((f (staircase q b' (k_b'.val + 1))).asym b' a h_pref_b'a)
    else
      Nat.le_of_not_lt h
  Fin.ext (Nat.le_antisymm h_leq h_geq)

/-- **Pivot-voter consistency across choices of `b`.**

The same voter `k` dictates pairs avoiding `b` and pairs avoiding `b'`.
Concretely, take `k := pivotalVoter h1 f hPareto hIIA q hxb` and use
`pivotalVoter_eq_of_different_b` to identify it with the pivotal voter
for `b'`. -/
theorem pivotalVoterUnique [DecidableEq α]
    (f : SWF m α) (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f)
    (h1 : 0 < m) (h3 : AtLeastThree α) (b b' : α) (hbb' : b ≠ b') :
    ∃ k : Fin m,
      (∀ a c : α, a ≠ b  → c ≠ b  → ∀ p : Profile m α, (p k).pref a c → (f p).pref a c) ∧
      (∀ a c : α, a ≠ b' → c ≠ b' → ∀ p : Profile m α, (p k).pref a c → (f p).pref a c) :=
  Classical.byCases
    (fun hNE : Nonempty (Profile m α) =>
      let q := Classical.choice hNE
      let ⟨_x, hxb⟩ := AtLeastThree.exists_ne h3 b
      let ⟨_x', hxb'⟩ := AtLeastThree.exists_ne h3 b'
      let k_b := pivotalVoter h1 f hPareto hIIA q hxb
      have hk_eq : k_b = pivotalVoter h1 f hPareto hIIA q hxb' :=
        pivotalVoter_eq_of_different_b h1 h3 f hPareto hIIA q hbb' hxb hxb'
      ⟨k_b,
        pivotalVoter_dictates_nonB h1 f hPareto hIIA q hxb,
        fun a c hab' hcb' p hpac =>
          pivotalVoter_dictates_nonB h1 f hPareto hIIA q hxb' a c hab' hcb' p
            (Eq.mp (congrArg (fun k => (p k).pref a c) hk_eq) hpac)⟩)
    (fun hNE : ¬ Nonempty (Profile m α) =>
      ⟨⟨0, h1⟩,
        (fun _ _ _ _ p _ => absurd (Nonempty.intro p) hNE),
        (fun _ _ _ _ p _ => absurd (Nonempty.intro p) hNE)⟩)

end ArrowCat
