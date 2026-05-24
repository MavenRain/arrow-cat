import ArrowCat.Basic
import KanTactics

/-! # `moveBToTop` and `moveBToBottom`

For a `StrictPref` `q` and an alternative `b`, the constructors
`moveBToTop q b` and `moveBToBottom q b` produce new strict total
orders that

- agree with `q` on the relative ordering of any two non-`b` elements,
- place `b` at the top (respectively bottom) of the ordering.

These are the basic building blocks of the Geanakoplos staircase
profile used in `pivotalVoterIsLocalDictator`.

The construction uses propositional case-splits rather than `if-then-
else`; this avoids requiring `DecidableEq α` and keeps the structure
unfolding clean for downstream proofs.  Classical reasoning is needed
for the `total` axiom (to case-split on `x = b`); the definitions are
therefore `noncomputable`. -/


set_option autoImplicit false

namespace ArrowCat
namespace StrictPref

universe u
variable {α : Type u}

/-! ### `moveBToTop` -/

/-- Move `b` to the top: `b` is strictly preferred to every other
element, and any two non-`b` elements retain their relative ranking
from `q`. -/
noncomputable def moveBToTop (q : StrictPref α) (b : α) : StrictPref α where
  pref x y := (x = b ∧ x ≠ y) ∨ (x ≠ b ∧ y ≠ b ∧ q.pref x y)
  asym _ _ h := fun hy =>
    h.elim
      (fun ⟨hxb, hxy⟩ =>
        hy.elim
          (fun ⟨hyb, _⟩ => hxy (hxb.trans hyb.symm))
          (fun ⟨_, hxb', _⟩ => hxb' hxb))
      (fun ⟨_, hyb, hpxy⟩ =>
        hy.elim
          (fun ⟨hyb', _⟩ => hyb hyb')
          (fun ⟨_, _, hpyx⟩ => q.asym _ _ hpxy hpyx))
  trans _ _ z h1 h2 :=
    h1.elim
      (fun ⟨hxb, hxy⟩ =>
        h2.elim
          (fun ⟨hyb, _⟩ => absurd (hxb.trans hyb.symm) hxy)
          (fun ⟨_, hzb, _⟩ =>
            Or.inl ⟨hxb, fun heq => hzb (heq.symm.trans hxb)⟩))
      (fun ⟨hxb, hyb, hpxy⟩ =>
        h2.elim
          (fun ⟨hyb', _⟩ => absurd hyb' hyb)
          (fun ⟨_, hzb, hpyz⟩ =>
            Or.inr ⟨hxb, hzb, q.trans _ _ z hpxy hpyz⟩))
  total x y hxy :=
    Classical.byCases
      (fun hxb : x = b =>
        Or.inl (Or.inl ⟨hxb, hxy⟩))
      (fun hxb : ¬ x = b =>
        Classical.byCases
          (fun hyb : y = b =>
            Or.inr (Or.inl ⟨hyb, fun heq => hxy heq.symm⟩))
          (fun hyb : ¬ y = b =>
            (q.total x y hxy).elim
              (fun hpxy => Or.inl (Or.inr ⟨hxb, hyb, hpxy⟩))
              (fun hpyx => Or.inr (Or.inr ⟨hyb, hxb, hpyx⟩))))

/-- `b` sits at the top of `moveBToTop q b`. -/
theorem moveBToTop_isTop (q : StrictPref α) (b : α) :
    (q.moveBToTop b).isTop b :=
  fun _ hxb => Or.inl ⟨rfl, fun heq => hxb heq.symm⟩

/-- `moveBToTop q b` preserves any preference between two non-`b`
elements. -/
theorem moveBToTop_pref_iff_of_ne (q : StrictPref α) (b : α) {x y : α}
    (hxb : x ≠ b) (hyb : y ≠ b) :
    (q.moveBToTop b).pref x y ↔ q.pref x y :=
  ⟨fun h => h.elim
    (fun ⟨hxb', _⟩ => absurd hxb' hxb)
    (fun ⟨_, _, hp⟩ => hp),
   fun h => Or.inr ⟨hxb, hyb, h⟩⟩

/-! ### `moveBToBottom` -/

/-- Move `b` to the bottom: every other element is strictly preferred
to `b`, and any two non-`b` elements retain their relative ranking from
`q`. -/
noncomputable def moveBToBottom (q : StrictPref α) (b : α) : StrictPref α where
  pref x y := (y = b ∧ x ≠ y) ∨ (x ≠ b ∧ y ≠ b ∧ q.pref x y)
  asym _ _ h := fun hy =>
    h.elim
      (fun ⟨hyb, hxy⟩ =>
        hy.elim
          (fun ⟨hxb, _⟩ => hxy (hxb.trans hyb.symm))
          (fun ⟨hyb', _, _⟩ => hyb' hyb))
      (fun ⟨hxb, _, hpxy⟩ =>
        hy.elim
          (fun ⟨hxb', _⟩ => hxb hxb')
          (fun ⟨_, _, hpyx⟩ => q.asym _ _ hpxy hpyx))
  trans _ _ _ h1 h2 :=
    h1.elim
      (fun ⟨hyb, _hxy⟩ =>
        h2.elim
          (fun ⟨hzb, hyz⟩ => absurd (hyb.trans hzb.symm) hyz)
          (fun ⟨hyb', _, _⟩ => absurd hyb hyb'))
      (fun ⟨hxb, _, hpxy⟩ =>
        h2.elim
          (fun ⟨hzb, _⟩ =>
            Or.inl ⟨hzb, fun heq => hxb (heq.trans hzb)⟩)
          (fun ⟨_, hzb, hpyz⟩ =>
            Or.inr ⟨hxb, hzb, q.trans _ _ _ hpxy hpyz⟩))
  total x y hxy :=
    Classical.byCases
      (fun hxb : x = b =>
        -- x = b. y ≠ b. So pref y x = (x = b ∧ y ≠ x). Or.inr branch.
        Or.inr (Or.inl ⟨hxb, fun heq => hxy heq.symm⟩))
      (fun hxb : ¬ x = b =>
        Classical.byCases
          (fun hyb : y = b =>
            -- y = b. pref x y = (y = b ∧ x ≠ y). Or.inl branch.
            Or.inl (Or.inl ⟨hyb, hxy⟩))
          (fun hyb : ¬ y = b =>
            (q.total x y hxy).elim
              (fun hpxy => Or.inl (Or.inr ⟨hxb, hyb, hpxy⟩))
              (fun hpyx => Or.inr (Or.inr ⟨hyb, hxb, hpyx⟩))))

/-- `b` sits at the bottom of `moveBToBottom q b`. -/
theorem moveBToBottom_isBottom (q : StrictPref α) (b : α) :
    (q.moveBToBottom b).isBottom b :=
  fun _ hxb => Or.inl ⟨rfl, hxb⟩

/-- `moveBToBottom q b` preserves any preference between two non-`b`
elements. -/
theorem moveBToBottom_pref_iff_of_ne (q : StrictPref α) (b : α) {x y : α}
    (hxb : x ≠ b) (hyb : y ≠ b) :
    (q.moveBToBottom b).pref x y ↔ q.pref x y :=
  ⟨fun h => h.elim
    (fun ⟨hyb', _⟩ => absurd hyb' hyb)
    (fun ⟨_, _, hp⟩ => hp),
   fun h => Or.inr ⟨hxb, hyb, h⟩⟩

/-! ### `(a, b)`/`(b, a)` evaluations in `moveBToTop`/`moveBToBottom`

These rules compute the `(·, b)` and `(b, ·)` preferences in the
modified profiles; their values depend only on the modification kind
(`moveBToTop` vs `moveBToBottom`), not on the base profile `q`.  They
are the workhorse for matching the auxiliary profile in the
local-dictator proof against the staircase profile. -/

/-- `moveBToTop` does not prefer any non-`b` element to `b` (since `b`
sits at the top). -/
theorem moveBToTop_not_pref_other_b (q : StrictPref α) {a b : α}
    (hab : a ≠ b) : ¬ (q.moveBToTop b).pref a b :=
  fun h => h.elim (fun ⟨hab', _⟩ => hab hab')
                  (fun ⟨_, hbb, _⟩ => hbb rfl)

/-- `moveBToTop` does prefer `b` to any other element. -/
theorem moveBToTop_pref_b_other (q : StrictPref α) {a b : α}
    (hab : a ≠ b) : (q.moveBToTop b).pref b a :=
  Or.inl ⟨rfl, fun heq => hab heq.symm⟩

/-- `moveBToBottom` prefers any non-`b` element to `b`. -/
theorem moveBToBottom_pref_other_b (q : StrictPref α) {a b : α}
    (hab : a ≠ b) : (q.moveBToBottom b).pref a b :=
  Or.inl ⟨rfl, hab⟩

/-- `moveBToBottom` does not prefer `b` to any other element. -/
theorem moveBToBottom_not_pref_b_other (q : StrictPref α) {a b : α}
    (hab : a ≠ b) : ¬ (q.moveBToBottom b).pref b a :=
  fun h => h.elim (fun ⟨hab', _⟩ => hab hab')
                  (fun ⟨hbb, _, _⟩ => hbb rfl)

end StrictPref
end ArrowCat
