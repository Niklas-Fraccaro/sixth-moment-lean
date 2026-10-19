# Sixth moment

This repository contains my Lean formalization of a lower bound for the sixth moment of the Riemann zeta function, using an exact 250-row certificate:

$$
\liminf_{T\to\infty}
\frac{\int_0^T |\zeta(\tfrac12+it)|^6\,dt}
     {(a_3/9!)\,T(\log T)^9}
\ge \frac{1077094746}{26265625}.
$$

Here $a_3$ is the [arithmetic Euler product](Sechstmoment/Arithmetic/Factor/Definitions.lean). See [CONTENTS.md](CONTENTS.md) for the source layout.

## Assumption

The sole literature input is Watt's Proposition 4.1, stated as [`DivisorProof.Watt41`](Sechstmoment/Arithmetic/Watt/Statement.lean). The final theorem, [`Sechstmoment.fullProof`](Sechstmoment/Theorem.lean), has type:

```lean
DivisorProof.Watt41 → Sechstmoment.FullGoal
```

## Reusable results

| Result | Module |
|---|---|
| Convergence and positivity of $a_3$ | [Factor/Convergence](Sechstmoment/Arithmetic/Factor/Convergence.lean) |
| Subpower bounds for divisor counts with a fixed cost per prime | [Divisors/Subpower](Sechstmoment/Arithmetic/Divisors/Subpower.lean) |
| Exact beta integrals | [Beta/Integral](Sechstmoment/Analysis/Beta/Integral.lean) |
| Concentration of beta profiles against continuous functions | [Beta/WeakConvergence](Sechstmoment/Analysis/Beta/WeakConvergence.lean) |
| Complex differentiation under compact interval integrals | [Integration/ComplexParameter](Sechstmoment/Analysis/Integration/ComplexParameter.lean) |

Import individual modules to use these results, for example `import Sechstmoment.Arithmetic.Factor.Convergence`.

## Reproducibility

Requires Linux x86-64 (including WSL), Git, Python 3.10+, and elan. Lean 4.34.0 and the Mathlib commit are pinned in the repository.

**This experimental snapshot has known build and verifier errors.** Once corrected, reproduce the final theorem with:

```sh
git clone https://github.com/NiklasFrac/sechstmoment-lean-experimental.git
cd sechstmoment-lean-experimental
lake exe cache get
lake env python3 verify_full_goal.py --fresh --workers 1 --memory-mb 0
```

The last command recompiles the final theorem's project dependencies and checks its literal type and transitive axioms. Logs are written to `verification_logs/`.
