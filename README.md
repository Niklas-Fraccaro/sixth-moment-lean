# Sixth moment

This repository contains my Lean formalization of a lower bound for the sixth moment of the Riemann zeta function:

$$
\liminf_{T\to\infty}
\frac{\int_0^T |\zeta(\tfrac12+it)|^6\,dt}
     {(a_3/9!)\,T(\log T)^9}
\mathrel{>} 41.007.
$$

Here $a_3$ is the [arithmetic Euler product](Sechstmoment/Arithmetic/Factor/Definitions.lean).

## Assumption

The sole literature input is Watt's Proposition 4.1, stated as [`DivisorProof.Watt41`](Sechstmoment/Arithmetic/Watt/Statement.lean). The final theorem, [`Sechstmoment.fullProof`](Sechstmoment/Theorem.lean), has type:

```lean
DivisorProof.Watt41 → Sechstmoment.FullGoal
```

## Reusable results

For example:

| Result | Module |
|---|---|
| Subpower bounds for divisor counts with a fixed cost per prime | [Divisors/Subpower](Sechstmoment/Arithmetic/Divisors/Subpower.lean) |
| Concentration of beta profiles against continuous functions | [Beta/WeakConvergence](Sechstmoment/Analysis/Beta/WeakConvergence.lean) |
| Complex differentiation under compact interval integrals | [Integration/ComplexParameter](Sechstmoment/Analysis/Integration/ComplexParameter.lean) |

See [CONTENTS.md](CONTENTS.md) for further results and the source layout.

## Reproducibility

Requires Git and elan. Lean 4.34.0 and the Mathlib commit are pinned in the repository.

The full build of this experimental reorganization is still pending.

```sh
git clone https://github.com/NiklasFrac/sechstmoment-lean-experimental.git
cd sechstmoment-lean-experimental
lake exe cache get
lake build
lake env lean Sechstmoment/Verification/Final.lean
```

`lake build` compiles all project modules. The final command checks the exact conclusion and prints its axioms; the check accepts only `propext`, `Classical.choice` and `Quot.sound`. Watt's proposition is an explicit hypothesis.
