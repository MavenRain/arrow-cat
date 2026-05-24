import ArrowCat.Basic
import ArrowCat.Geanakoplos
import ArrowCat.Pivotal
import KanTactics

/-! # Arrow's Impossibility Theorem

The main result, assembled from the lemmas in `ArrowCat.Pivotal` (which
in turn build on `ArrowCat.Geanakoplos`, `ArrowCat.Move`, and
`ArrowCat.Swap`).

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

Proof: pick an anchor alternative `b₀` from `AtLeastThree` and let
`k := pivotalVoter h1 f hPareto hIIA q hxb₀` for a base profile `q` and
witness `x ≠ b₀`.  For any input profile `p` and pair `(a, c)` with
`(p k).pref a c`:

- If `a, c ≠ b₀`: `pivotalVoter_dictates_nonB` directly gives `(f
  p).pref a c`.
- If `a = b₀` or `c = b₀` (and `a ≠ c`, derived from `hpac` and
  irreflexivity): pick a third alternative `b_alt ≠ a, c`; then
  `b_alt ≠ b₀` (since `b₀ ∈ {a, c}`), so
  `pivotalVoter_eq_of_different_b` identifies `k` with the pivotal
  voter `k_alt` for `b_alt`, and `pivotalVoter_dictates_nonB` applied
  with `b_alt` gives `(f p).pref a c`.

When `Profile m α` is empty, the dictator property is vacuous. -/
theorem arrow [DecidableEq α]
    (f : SWF m α) (h1 : 0 < m) (h3 : AtLeastThree α)
    (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f) :
    ∃ k : Fin m, SWF.Dictator f k :=
  Classical.byCases
    (fun hNE : Nonempty (Profile m α) =>
      let q := Classical.choice hNE
      let ⟨b₀, _, _, _, _, _⟩ := h3
      let ⟨_x, hxb₀⟩ := AtLeastThree.exists_ne h3 b₀
      let k := pivotalVoter h1 f hPareto hIIA q hxb₀
      ⟨k, fun p a c hpac =>
        have hac : a ≠ c := fun heq =>
          (p k).irrefl a
            (Eq.mpr (congrArg (fun y => (p k).pref a y) heq) hpac)
        Classical.byCases
          (fun (h_a_eq_b0 : a = b₀) =>
            Classical.byCases
              (fun (h_c_eq_b0 : c = b₀) =>
                absurd (h_a_eq_b0.trans h_c_eq_b0.symm) hac)
              (fun (_h_c_ne_b0 : c ≠ b₀) =>
                -- a = b₀, c ≠ b₀.  Pick a third alt avoiding {a, c}.
                let ⟨b_alt, hb_alt_a, hb_alt_c⟩ :=
                  AtLeastThree.exists_ne_two h3 a c hac
                have hb_alt_b0 : b_alt ≠ b₀ := h_a_eq_b0 ▸ hb_alt_a
                let ⟨_x_alt, hx_alt⟩ := AtLeastThree.exists_ne h3 b_alt
                let k_alt := pivotalVoter h1 f hPareto hIIA q hx_alt
                have hk_eq : k = k_alt :=
                  pivotalVoter_eq_of_different_b h1 h3 f hPareto hIIA q
                    (Ne.symm hb_alt_b0) hxb₀ hx_alt
                have hpac_alt : (p k_alt).pref a c :=
                  Eq.mp (congrArg (fun j : Fin m => (p j).pref a c) hk_eq) hpac
                pivotalVoter_dictates_nonB h1 f hPareto hIIA q hx_alt a c
                  (Ne.symm hb_alt_a) (Ne.symm hb_alt_c) p hpac_alt))
          (fun (h_a_ne_b0 : a ≠ b₀) =>
            Classical.byCases
              (fun (h_c_eq_b0 : c = b₀) =>
                -- c = b₀, a ≠ b₀.  Symmetric: pick a third alt avoiding {a, c}.
                let ⟨b_alt, hb_alt_a, hb_alt_c⟩ :=
                  AtLeastThree.exists_ne_two h3 a c hac
                have hb_alt_b0 : b_alt ≠ b₀ := h_c_eq_b0 ▸ hb_alt_c
                let ⟨_x_alt, hx_alt⟩ := AtLeastThree.exists_ne h3 b_alt
                let k_alt := pivotalVoter h1 f hPareto hIIA q hx_alt
                have hk_eq : k = k_alt :=
                  pivotalVoter_eq_of_different_b h1 h3 f hPareto hIIA q
                    (Ne.symm hb_alt_b0) hxb₀ hx_alt
                have hpac_alt : (p k_alt).pref a c :=
                  Eq.mp (congrArg (fun j : Fin m => (p j).pref a c) hk_eq) hpac
                pivotalVoter_dictates_nonB h1 f hPareto hIIA q hx_alt a c
                  (Ne.symm hb_alt_a) (Ne.symm hb_alt_c) p hpac_alt)
              (fun (h_c_ne_b0 : c ≠ b₀) =>
                -- Both a, c ≠ b₀.  Directly apply pivotalVoter_dictates_nonB.
                pivotalVoter_dictates_nonB h1 f hPareto hIIA q hxb₀ a c
                  h_a_ne_b0 h_c_ne_b0 p hpac))⟩)
    (fun hNE : ¬ Nonempty (Profile m α) =>
      ⟨⟨0, h1⟩, fun p _ _ _ => absurd (Nonempty.intro p) hNE⟩)

/-- **Equivalent contrapositive form.**  No social welfare function on
a sufficiently rich domain satisfies Pareto, IIA, and Non-Dictatorship
simultaneously. -/
theorem arrow_contrapositive [DecidableEq α]
    (f : SWF m α) (h1 : 0 < m) (h3 : AtLeastThree α)
    (hPareto : SWF.Pareto f) (hIIA : SWF.IIA f) :
    ¬ SWF.NonDictator f :=
  fun h => h (arrow f h1 h3 hPareto hIIA)

end ArrowCat
