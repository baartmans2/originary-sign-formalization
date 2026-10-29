# Originary sign formalization

A machine-verified attempt to find the minimal assumptions under which symbolic, graph-like
structure (signs, and relations among them, grounded in physical objects) can emerge from
conditions in which it is absent. The work is inspired by Eric Gans's Generative
Anthropology, and follows the opening sentence of his *The Origin of Language*:
"Mysteries should not be multiplied beyond necessity."

**This is a work in progress.** Everything here, including the axioms, definitions,
results and their interpretation, is subject to revision and refinement.

## Contents

| Path | What it is |
|---|---|
| `paper/whitepaper.pdf` | The whitepaper: motivation, the formal system, results, how the account developed, findings and open problems |
| `paper/whitepaper.tex` | Its LaTeX source |
| `VERIFYING.md` | How AI-drafted passages are marked, and the list of claims still to be checked against their sources |
| `lean/` | The Lean 4 formalization; every result in the paper is a theorem here, with no `sorry` |

## Building

Requires Lean 4.15.0. No Mathlib is needed.

```bash
cd lean
```

```bash
lake build
```

To print the logical axioms each headline theorem depends on:

```bash
lake env lean Check.lean
```

To build the paper, with a TeX Live installation that includes `latexmk`:

```bash
cd paper
```

```bash
latexmk -pdf whitepaper.tex
```

## Contributing

Contributions are welcome, especially:

- checking the open items listed in `VERIFYING.md` against their sources;
- countermodels showing that each axiom is needed (minimality);
- applying the self-licensing test (paper, Section 1.4) to other accounts of language origin;
- the open problems in Section 6 of the paper.

The current formal system is in `lean/GaEmergence/Completion.lean` and the files built on
it (`Fit`, `Falsehood`, `Graphs`, `Roles`, `Polarity`). The other files are earlier
versions of the account, kept as a record of how it developed. `lean/README.md` is a
detailed log of that development.
