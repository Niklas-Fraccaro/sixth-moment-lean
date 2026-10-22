# Sixth Moment

This repository contains my Lean formalization of a lower bound for the sixth moment of the Riemann zeta function:

$$
\liminf_{T\to\infty}
\frac{\int_0^T |\zeta(\tfrac12+it)|^6\,dt}
     {(a_3/9!)\,T(\log T)^9}
\mathrel{>} 41.007.
$$

Here $a_3$ is the [arithmetic Euler product](SixthMoment/Arithmetic/Factor/Definitions.lean).

## Assumption

The sole literature input, [`DivisorProof.Watt41`](SixthMoment/Arithmetic/Watt/Statement.lean), comes from Proposition 4.1 (p. 201) of N. Watt, [*Kloosterman Sums and a Mean Value for Dirichlet Polynomials*](https://doi.org/10.1006/jnth.1995.1086), *Journal of Number Theory* **53** (1995), 179–210.

The Lean assumption uses globally smooth weights and makes the uniform derivative bounds and the sufficiently-large-`X` condition explicit. Under the paper's uniform interpretation of its implicit constants, Proposition 4.1 implies this formulation. The source file records the summation and regularity conventions used in this comparison.

The final theorem, [`SixthMoment.fullProof`](SixthMoment/Theorem.lean), has type:

```lean
DivisorProof.Watt41 → SixthMoment.FullGoal
```

I am also working on a Lean proof of the Watt assumption (`DivisorProof.Watt41`). This is a substantial project, and I expect it to take several more weeks.

## Reusable results

For example:

| Result | Module |
|---|---|
| Subpower bounds for divisor counts with a fixed cost per prime | [Divisors/Subpower](SixthMoment/Arithmetic/Divisors/Subpower.lean) |
| Concentration of beta profiles against continuous functions | [Beta/WeakConvergence](SixthMoment/Analysis/Beta/WeakConvergence.lean) |
| Complex differentiation under compact interval integrals | [Integration/ComplexParameter](SixthMoment/Analysis/Integration/ComplexParameter.lean) |

See [CONTENTS.md](CONTENTS.md) for further results and the source layout.

## Reproducibility

Requires Git and elan. Lean 4.34.0 and Mathlib are pinned.

```sh
git clone https://github.com/NiklasFrac/sixth-moment-lean.git
cd sixth-moment-lean
lake exe cache get
lake build
lake env lean SixthMoment/Verification/Final.lean
```

The final command checks the theorem and its axioms.

## License

This project is licensed under the Apache License, Version 2.0. See [LICENSE](LICENSE).

The bundled [Salt](Salt/) code is also licensed under Apache 2.0; its original copyright and attribution notices are retained.
