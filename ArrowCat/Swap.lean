import ArrowCat.Basic
import KanTactics

/-! # The `swap` operation on `StrictPref`

A transposition `swapMap a c : α → α` swaps two specific elements of `α`
and fixes the rest.  Lifted pointwise through `StrictPref.swap`, it
produces a strict total order in which the roles of `a` and `c` are
exchanged everywhere they appear.

The key application is `exists_modified_profile` (in
`ArrowCat.Geanakoplos`), where the per-voter modified profile is built
by swapping `a` and `c` exactly when the voter currently ranks `a` above
`c`.  Because every voter places `b` extremally and `b ∉ {a, c}`, the
swap preserves `b`'s extremal position and hence every voter's
`(a, b)` and `(b, c)` rankings.

Requires `DecidableEq α` for the case-analysis function `swapMap`. -/


set_option autoImplicit false

namespace ArrowCat
namespace StrictPref

universe u
variable {α : Type u}

section Swap

variable [DecidableEq α]

/-- The transposition function swapping `a` and `c`; fixes all other
elements.  When `a = c` this is the identity. -/
def swapMap (a c : α) (z : α) : α :=
  if z = a then c
  else if z = c then a
  else z

/-- `swapMap` evaluated at its first swap point yields its second. -/
theorem swapMap_at_a (a c : α) : swapMap a c a = c :=
  if_pos rfl

/-- `swapMap` evaluated at its second swap point yields its first (when
the two are distinct). -/
theorem swapMap_at_c (a c : α) (h : a ≠ c) : swapMap a c c = a :=
  (if_neg (fun heq => h heq.symm)).trans (if_pos rfl)

/-- `swapMap` fixes any element distinct from both swap points. -/
theorem swapMap_other (a c z : α) (h1 : z ≠ a) (h2 : z ≠ c) :
    swapMap a c z = z :=
  (if_neg h1).trans (if_neg h2)

/-- `swapMap` is an involution: applying it twice yields the identity.
Three-way case analysis on `z`'s relation to `{a, c}`, with a sub-case
on `a = c` in the `z = a` branch. -/
theorem swapMap_involution (a c z : α) :
    swapMap a c (swapMap a c z) = z :=
  if hza : z = a then
    have h1 : swapMap a c z = c := if_pos hza
    if hac : a = c then
      have hzc : z = c := hza.trans hac
      have h2 : swapMap a c c = c := if_pos hac.symm
      ((congrArg (swapMap a c) h1).trans h2).trans hzc.symm
    else
      have h2 : swapMap a c c = a := swapMap_at_c a c hac
      ((congrArg (swapMap a c) h1).trans h2).trans hza.symm
  else if hzc : z = c then
    have h1 : swapMap a c z = a := (if_neg hza).trans (if_pos hzc)
    have h2 : swapMap a c a = c := if_pos rfl
    ((congrArg (swapMap a c) h1).trans h2).trans hzc.symm
  else
    have h1 : swapMap a c z = z := swapMap_other a c z hza hzc
    (congrArg (swapMap a c) h1).trans h1

/-- `swapMap` is injective.  Follows from being an involution. -/
theorem swapMap_inj (a c : α) {x y : α}
    (h : swapMap a c x = swapMap a c y) : x = y :=
  (swapMap_involution a c x).symm.trans
    ((congrArg (swapMap a c) h).trans (swapMap_involution a c y))

/-- The lifted `swap` on `StrictPref`: pre-compose the relation with the
transposition of `a` and `c`.  The resulting strict total order swaps the
roles of `a` and `c` everywhere. -/
def swap (p : StrictPref α) (a c : α) : StrictPref α where
  pref x y := p.pref (swapMap a c x) (swapMap a c y)
  asym _ _ h := p.asym _ _ h
  trans _ _ _ h1 h2 := p.trans _ _ _ h1 h2
  total _ _ hxy := p.total _ _ (fun heq => hxy (swapMap_inj a c heq))

/-- A `swap` of two elements preserves any third element's extremal
position.  This is the key fact that makes the modified profile in
`exists_modified_profile` keep `b`'s extremal position when we swap `a`
and `c` (both `≠ b`) inside each voter's preference.

The `Eq.mpr (congrArg ...)` plumbing is required because Lean's `▸`
motive inference defaults to the constant motive here, which leaves the
type unchanged.  Forcing an explicit `congrArg` over the first (resp.
second) argument position of `p.pref` pins down the rewrite we want. -/
theorem swap_isExtreme_of_ne (p : StrictPref α) {a c b : α}
    (hba : b ≠ a) (hbc : b ≠ c) (h : p.isExtreme b) :
    (p.swap a c).isExtreme b :=
  let hbb : swapMap a c b = b := swapMap_other a c b hba hbc
  h.elim
    (fun hTop => Or.inl fun x hxb =>
      -- (p.swap a c).pref b x  def≡  p.pref (swapMap a c b) (swapMap a c x)
      have hsxb : swapMap a c x ≠ b := fun heq =>
        hxb (swapMap_inj a c (heq.trans hbb.symm))
      Eq.mpr (congrArg (fun y => p.pref y (swapMap a c x)) hbb)
        (hTop (swapMap a c x) hsxb))
    (fun hBot => Or.inr fun x hxb =>
      -- (p.swap a c).pref x b  def≡  p.pref (swapMap a c x) (swapMap a c b)
      have hsxb : swapMap a c x ≠ b := fun heq =>
        hxb (swapMap_inj a c (heq.trans hbb.symm))
      Eq.mpr (congrArg (fun y => p.pref (swapMap a c x) y) hbb)
        (hBot (swapMap a c x) hsxb))

/-- Compute the swap-lifted `(c, a)` preference: it is the same as the
original's `(a, c)`, because `swapMap a c c = a` and `swapMap a c a = c`. -/
theorem swap_pref_ca_of_ne (q : StrictPref α) (a c : α) (hac : a ≠ c) :
    (q.swap a c).pref c a = q.pref a c :=
  (congrArg (fun x => q.pref x (swapMap a c a)) (swapMap_at_c a c hac)).trans
    (congrArg (q.pref a) (swapMap_at_a a c))

/-- Compute the swap-lifted `(a, b)` preference for a `b ≠ a, c`: it is
`q.pref c b`. -/
theorem swap_pref_ab_of_ne (q : StrictPref α) {a b c : α}
    (hab : a ≠ b) (hcb : c ≠ b) :
    (q.swap a c).pref a b = q.pref c b :=
  (congrArg (fun x => q.pref x (swapMap a c b)) (swapMap_at_a a c)).trans
    (congrArg (q.pref c) (swapMap_other a c b (Ne.symm hab) (Ne.symm hcb)))

/-- Compute the swap-lifted `(b, c)` preference for a `b ≠ a, c`: it is
`q.pref b a`. -/
theorem swap_pref_bc_of_ne (q : StrictPref α) {a b c : α}
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c) :
    (q.swap a c).pref b c = q.pref b a :=
  (congrArg (fun x => q.pref x (swapMap a c c))
      (swapMap_other a c b (Ne.symm hab) (Ne.symm hcb))).trans
    (congrArg (q.pref b) (swapMap_at_c a c hac))

section ModifyForCA
open Classical

/-- Per-voter modification used in `exists_modified_profile`: if the
voter already ranks `c` above `a`, keep their preference unchanged;
otherwise swap `a` and `c`.  Classical decidability is used to choose
between the two branches; the definition is therefore `noncomputable`. -/
noncomputable def modifyForCA (q : StrictPref α) (a c : α) : StrictPref α :=
  if q.pref c a then q else q.swap a c

/-- When the voter already ranks `c` above `a`, the modification is the
identity. -/
theorem modifyForCA_pos (q : StrictPref α) (a c : α) (h : q.pref c a) :
    modifyForCA q a c = q :=
  if_pos h

/-- When the voter ranks `a` above `c`, the modification is the swap. -/
theorem modifyForCA_neg (q : StrictPref α) (a c : α) (h : ¬ q.pref c a) :
    modifyForCA q a c = q.swap a c :=
  if_neg h

/-- The modified voter ranks `c` strictly above `a`. -/
theorem modifyForCA_pref_ca (q : StrictPref α) (a c : α) (hac : a ≠ c) :
    (modifyForCA q a c).pref c a :=
  if h : q.pref c a then
    Eq.mpr (congrArg (fun r : StrictPref α => r.pref c a) (modifyForCA_pos q a c h)) h
  else
    have hpref_ac : q.pref a c := (q.total a c hac).resolve_right h
    have hSwap : (q.swap a c).pref c a = q.pref a c := swap_pref_ca_of_ne q a c hac
    have hChain : (modifyForCA q a c).pref c a = q.pref a c :=
      (congrArg (fun r : StrictPref α => r.pref c a) (modifyForCA_neg q a c h)).trans hSwap
    Eq.mpr hChain hpref_ac

/-- The modification preserves every voter's `(a, b)` ranking. -/
theorem modifyForCA_pref_ab_iff (q : StrictPref α) {a b c : α}
    (hab : a ≠ b) (hcb : c ≠ b)
    (hExt : q.isExtreme b) :
    (modifyForCA q a c).pref a b ↔ q.pref a b :=
  if h : q.pref c a then
    Iff.of_eq (congrArg (fun r : StrictPref α => r.pref a b) (modifyForCA_pos q a c h))
  else
    let hEq : (modifyForCA q a c).pref a b = q.pref c b :=
      (congrArg (fun r : StrictPref α => r.pref a b)
        (modifyForCA_neg q a c h)).trans (swap_pref_ab_of_ne q hab hcb)
    (Iff.of_eq hEq).trans (pref_left_iff_of_isExtreme q hExt hcb hab)

/-- The modification preserves every voter's `(b, c)` ranking. -/
theorem modifyForCA_pref_bc_iff (q : StrictPref α) {a b c : α}
    (hab : a ≠ b) (hcb : c ≠ b) (hac : a ≠ c)
    (hExt : q.isExtreme b) :
    (modifyForCA q a c).pref b c ↔ q.pref b c :=
  if h : q.pref c a then
    Iff.of_eq (congrArg (fun r : StrictPref α => r.pref b c) (modifyForCA_pos q a c h))
  else
    let hEq : (modifyForCA q a c).pref b c = q.pref b a :=
      (congrArg (fun r : StrictPref α => r.pref b c)
        (modifyForCA_neg q a c h)).trans (swap_pref_bc_of_ne q hab hcb hac)
    (Iff.of_eq hEq).trans (pref_right_iff_of_isExtreme q hExt hab hcb)

end ModifyForCA

end Swap

end StrictPref
end ArrowCat
