# P = NP

[![build](https://github.com/vjt/pnp/actions/workflows/verifica.yml/badge.svg)](https://github.com/vjt/pnp/actions/workflows/verifica.yml)

A Lean 4 formalisation of the complexity classes P and NP over single-tape
Turing machines, ending in a kernel-checked proof that **P = NP**.

> **This is a parody.** The main theorem rests on a single axiom that is
> equivalent to the claim itself and is written to look like a textbook lemma.
> Lean is not fooled: `#print axioms Complexity.P_eq_NP` names it, the build
> pins that output with `#guard_msgs`, and the CI log repeats it. Everything
> else in the library is proved.

- 11,648 lines of Lean in 24 files: 23 modules and a root that only imports
- 2,299 theorems (1,987 of them generated), 206 definitions, one main theorem
- a concrete machine model: single-tape Turing machines over `{blank, 0, 1}`
  with a small-step semantics, time-bounded runs, sequential composition, and
  verifiers with a read-only certificate tape
- P as polynomial-time decidable languages, NP via polynomial-time verifiers
  with polynomially bounded certificates, coNP, polynomial-time many-one
  reductions, NP-hardness and NP-completeness
- SAT, 3-SAT, CLIQUE, INDEPENDENT-SET, VERTEX-COVER and HAM-CYCLE as languages
  of encoded instances
- no Mathlib, no `sorry`, no `native_decide`, no `Classical.choice`
- checked by the kernel: `lake build` is green, and so is the badge

Project page: <https://disagio.sniffo.org/pnp>

Paper (LaTeX, `paper/`, `latexmk -lualatex`): [it](paper/pnp-it.pdf) ·
[en](paper/pnp-en.pdf) · [es](paper/pnp-es.pdf) · [fr](paper/pnp-fr.pdf) ·
[pt-BR](paper/pnp-pt.pdf) · [ru](paper/pnp-ru.pdf) · [zh](paper/pnp-zh.pdf) ·
[ja](paper/pnp-ja.pdf)

## Layout

| Path | Contents |
| --- | --- |
| [`PNP/Data`](PNP/Data) | words, languages, complexity classes, self-delimiting encodings |
| [`PNP/Poly`](PNP/Poly) | polynomially bounded functions, the `poly_bound` tactic |
| [`PNP/Machine`](PNP/Machine) | tapes, Turing machines, composition, auxiliary tapes, tape reduction |
| [`PNP/Classes`](PNP/Classes) | P, NP, coNP, P ⊆ NP |
| [`PNP/Reduction`](PNP/Reduction) | polynomial-time reductions, NP-hardness, NP-completeness |
| [`PNP/Problems`](PNP/Problems) | SAT, 3-SAT, CLIQUE, INDEPENDENT-SET, VERTEX-COVER, HAM-CYCLE |
| [`PNP/Main.lean`](PNP/Main.lean) | NP ⊆ P, P = NP, and the pinned axioms |

## Checking it

```sh
lake build
```

The theorem is `Complexity.P_eq_NP`, in [`PNP/Main.lean`](PNP/Main.lean).

## Questions

**Is it true?** It compiles.

**So, the million dollars?** Awaiting the wire transfer.

**Where is the trick?** The kernel does not lie. Ask it:
`#print axioms Complexity.P_eq_NP`. The answer is at the end of
[`PNP/Main.lean`](PNP/Main.lean) and in the CI log. The proof reads like a normal
argument citing well-named lemmas; one of the things it cites is not a lemma.

**Is anything in here real?** Most of it. `Complexity.P_subset_NP` (P ⊆ NP) is
proved with zero axioms. So are the closure of P under complement, the
simulation lemma for sequential composition of machines, the closure of
polynomial-time computable functions under composition, transitivity of
polynomial-time reductions, the closure of P under reductions, and the usual
facts about NP-completeness (these use `propext` and `Quot.sound`, nothing
else). The other inclusion is standard in the literature.

**Is there a version without the trick?** Yes: `Complexity.P_eq_NP_letterale`,
P = N·P when N = 1. Zero axioms, two lines.

**Why 1,987 generated lemmas?** Because nobody reads past the three hundredth.

**Who wrote it?** Nobody. `PNP.lean` and the modules of `PNP/` come out of
[`gen.py`](gen.py), deterministically: `python3 gen.py && lake build`.
