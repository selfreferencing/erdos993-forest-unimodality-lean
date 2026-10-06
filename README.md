# Erdős Problem #993 in Lean 4: the formal proof of "Unimodality of the independence sequence of a forest"

This package is the Lean 4 formal proof that accompanies the paper *Unimodality of the independence sequence of a forest*,
by Tong Zhang, Wei Li and Kevin Vallier (6 October 2026; the PDF and its LaTeX source will be added to `paper/`). It proves Erdős
Problem #993: **every finite forest has a unimodal independence sequence.**

Lean `v4.28.0` and Mathlib `v4.28.0`. The Lean code is licensed under the Apache License 2.0 (`LICENSE`).

## The theorem

```lean
theorem Erdos993Lean.Analytic.V22.erdos993_v22_final : Erdos993Lean.Erdos993Statement
```

in `Erdos993Lean/Analytic/V22/Final.lean`. It has no premise. Here, as defined in `Erdos993Lean/Statement.lean`:
- a `FiniteForest` is an acyclic `SimpleGraph (Fin n)`;
- `independenceCount F k` counts the independent sets of `F` with `k` vertices;
- `Erdos993Statement` says that, for every finite forest `F`, the sequence `independenceCount F 0, ...,
  independenceCount F α(F)` is (weakly) unimodal.

## What it follows

- **Forests with at least 25 vertices.** The formal proof follows Sections 2 to 5 and Appendix B of the paper, statement by
  statement; a few results are formalized through their constituents rather than as one declaration. Below the starting
  means it checks 779 boxes, which include the 693 boxes that the paper uses.
- **Forests with at most 24 vertices.** The formal proof uses a different method from Section 6 of the paper: 249 exact
  rational certificates of a linear relaxation of the fiber numbers, checked by the Lean kernel
  (`Erdos993Lean.Fiber.floorStatement_25_fiber`).

## Axioms

`lake env lean Audit/AxiomsV22.lean` prints

```
'Erdos993Lean.Analytic.V22.erdos993_v22_final' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
```

`Lean.ofReduceBool` and `Lean.trustCompiler` come from 411 compiled evaluations (`native_decide`) of finite checks in the
part for at least 25 vertices, so the trusted base of this proof includes the Lean compiler. The part for at most 24
vertices uses only `propext`, `Classical.choice` and `Quot.sound`. There is no `sorry` and no added axiom.

## Contents and build

- `Erdos993Lean/`: exactly the import closure of the top theorem, 1,352 modules, listed in `CLOSURE_MODULES.txt`.
- `Audit/AxiomsV22.lean`: the axiom check above.
- `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`: as committed with the proof. The lakefile lists further library
  targets of the full development whose roots are not part of this package; build the module named below.

```bash
lake exe cache get
lake build Erdos993Lean.Analytic.V22.Final
lake env lean Audit/AxiomsV22.lean
```

Some modules need several GB of memory; building one module at a time is safe. Every source file here is byte-identical
to the development commit `d3cf284` (whose Lean sources equal those of commit `63040a09`), which was built from a fresh
clone on 3 October 2026 and again, independently, on another machine on 5 October 2026; both builds printed exactly the
five axioms above.

## Credits

The decomposition relative to a fixed independent set, the binomial mixture and the first proof of the theorem are due to
T. Zhang and W. Li (*Unimodality of Forest Independence Polynomials*, Zenodo, doi:10.5281/zenodo.22999166). The use of AI
systems in this work is described in Section 9 of the paper.
