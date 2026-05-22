# arrow-cat

A Lean 4 formalization of **Arrow's Impossibility Theorem** via the
Geanakoplos pivotal-voter argument, built on
[`kan-tactics`](../kan-tactics).

> No Mathlib dependency.  Social-choice primitives (preferences, profiles,
> social welfare functions) and the axioms (Pareto, Independence of
> Irrelevant Alternatives, Dictator) are developed from scratch.

## Statement

For any social welfare function over a domain with at least three
alternatives and a finite, non-empty set of voters, if the function
satisfies Pareto efficiency and Independence of Irrelevant Alternatives,
then some voter is a dictator:

```lean
theorem arrow {m : Nat} {α : Type u} [DecidableEq α]
    (hm : 1 ≤ m) (h3 : AtLeastThree α)
    (f : SWF m α)
    (hPareto : SWF.Pareto f)
    (hIIA   : SWF.IIA f) :
    ∃ i : Fin m, SWF.Dictator f i
```

## Architecture

```
ArrowCat/
  Basic.lean          StrictPref, Profile, SWF, axioms (Pareto, IIA, Dictator)
  Geanakoplos.lean    Three-lemma proof skeleton:
                        extremalLemma, pivotalVoter, localDictator
  Arrow.lean          The main theorem, assembled from the three lemmas
```

Every tactic block uses **only** kan-tactics (`kan_intros`, `kan_apply`,
`kan_rfl`, `kan_rw`, `kan_cases`, `kan_use`, `kan_exact`, `kan_simp`,
`kan_simp_only`, `kan_refine`, `kan_constructor`, `kan_calc_trans`,
`kan_induction`).  Term-mode proofs are used where they are cleaner than
tactic mode (the no-Mathlib-tactics rule applies to tactic blocks, not to
pure term expressions).

`Option` and `Except` are used wherever a partial function or failable
operation appears.  No `panic!`, `throw`, or `unreachable!` anywhere in
the library.

## Building

```sh
lake build
```

The repository is a [reservoir library](../kan-tactics/README.md) —
downstream projects can depend on it via:

```lean
require «arrow-cat» from ".." / "arrow-cat"
```

or as a git dependency.

## Proof outline (Geanakoplos 2005)

1. **Extremal Lemma.**  If every voter places alternative `b` either at
   the top or the bottom of their ranking, society also places `b`
   strictly at the top or strictly at the bottom.

2. **Pivotal Voter.**  Starting from a profile where every voter has `b`
   at the bottom, move `b` to the top one voter at a time.  By Pareto,
   society's stance on `b` flips from "`b` strictly worst" to "`b`
   strictly best" somewhere in this sequence.  Call the voter where the
   flip occurs the **pivotal voter for `b`**.

3. **Local Dictatorship.**  The pivotal voter for `b` is a dictator over
   every pair of alternatives `(a, c)` with `a, c ≠ b`.

4. **Global Dictatorship.**  Picking a different `b` and re-running the
   argument shows the pivotal voter is the same individual throughout
   and is a dictator over every pair.

## Status

Scaffolding complete; theorem statements compile under `sorry`.  Proofs
are the next milestone.

## License

Dual-licensed under MIT OR Apache-2.0, at your option.
