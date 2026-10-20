# Contents

Paths below are relative to `SixthMoment/`, unless stated otherwise.

## Entry points

| File | Content |
|---|---|
| [Statement.lean](SixthMoment/Statement.lean) | The sixth-moment lower bound and `FullGoal`. |
| [LiteratureAssumption.lean](SixthMoment/LiteratureAssumption.lean) | The Watt assumption and the conditional goal. |
| [Theorem.lean](SixthMoment/Theorem.lean) | Final assembly and `fullProof`. |

## Analysis

- [Beta/](SixthMoment/Analysis/Beta): exact integrals, normalized profiles, concentration and weak convergence.
- [Integration/](SixthMoment/Analysis/Integration), [Measures/](SixthMoment/Analysis/Measures): parameter integrals, differentiation under the integral, Cauchy–Schwarz and measure identities.
- [Complex/](SixthMoment/Analysis/Complex), [Calculus/](SixthMoment/Analysis/Calculus): holomorphy, partial derivatives, complex powers and compact products.
- [Fourier/](SixthMoment/Analysis/Fourier), [Mellin/](SixthMoment/Analysis/Mellin), [Harmonic/](SixthMoment/Analysis/Harmonic): transforms, inversion, contour estimates and harmonic sums.
- [Gaussian/](SixthMoment/Analysis/Gaussian), [Simplex/](SixthMoment/Analysis/Simplex): Gaussian moments and simplex integrals.
- [Alternants/](SixthMoment/Analysis/Alternants): exponential alternants and limits when parameters coincide.
- [Asymptotics/](SixthMoment/Analysis/Asymptotics), [Dyadic/](SixthMoment/Analysis/Dyadic), [Profiles/](SixthMoment/Analysis/Profiles), [Quadrature/](SixthMoment/Analysis/Quadrature): growth estimates, weights, profile classes and exact integration rules.

## Arithmetic

- [Factor/](SixthMoment/Arithmetic/Factor): definition, convergence and positivity of $a_3$.
- [Divisors/](SixthMoment/Arithmetic/Divisors): divisor-growth and logarithmic-frequency bounds.
- [Euler/](SixthMoment/Arithmetic/Euler): local factors, convolutions, residues, remainders and shifted, bivariate and four-L Euler products.
- [Kloosterman/](SixthMoment/Arithmetic/Kloosterman): definitions and estimates for Kloosterman sums.
- [Watt/](SixthMoment/Arithmetic/Watt): Proposition 4.1 and its weight estimates and transformations.
- [QuadraticDivisor/](SixthMoment/Arithmetic/QuadraticDivisor): quadratic-divisor inputs, parameters and estimates; [Reduction/](SixthMoment/Arithmetic/QuadraticDivisor/Reduction) contains the reduction from Watt's proposition.
- [Exact/](SixthMoment/Arithmetic/Exact): exact polynomial arithmetic.

## Zeta

- [SixthMoment.lean](SixthMoment/Zeta/SixthMoment.lean): the moment integral and its normalization.
- [AFE/](SixthMoment/Zeta/AFE): one-sided, two-factor and four-factor approximate functional equations.
- [DirichletL/](SixthMoment/Zeta/DirichletL): character expansions, fourth-power bounds and products of four L-functions.
- [Chi/](SixthMoment/Zeta/Chi), [Gamma/](SixthMoment/Zeta/Gamma): functional-equation factors, gamma ratios and asymptotics.
- [Centering/](SixthMoment/Zeta/Centering): centered derivative and polynomial identities.
- [Bounds/](SixthMoment/Zeta/Bounds), [Moments/](SixthMoment/Zeta/Moments): growth estimates and moment inequalities.
- Other modules define amplifiers, generators, regularized zeta functions and polynomial tests.

## Certificate

- [Data.lean](SixthMoment/Certificate/Data.lean), [Row.lean](SixthMoment/Certificate/Row.lean), [Scale.lean](SixthMoment/Certificate/Scale.lean): the 250 rows, their type and scaling.
- [Tests.lean](SixthMoment/Certificate/Tests.lean), [TestPolynomials.lean](SixthMoment/Certificate/TestPolynomials.lean), [Features.lean](SixthMoment/Certificate/Features.lean): the test functions and their polynomial features.
- [Exact/](SixthMoment/Certificate/Exact), [Bounds.lean](SixthMoment/Certificate/Bounds.lean): exact numerator and denominator calculations and the resulting rational bound.
- [Gram/](SixthMoment/Certificate/Gram), [GramBlocks/](SixthMoment/Certificate/GramBlocks): Gram-matrix assembly and 125 indexed computation blocks.
- [Kernels/](SixthMoment/Certificate/Kernels): balanced and unbalanced certificate kernels.
- [Profiles/](SixthMoment/Certificate/Profiles): profile approximations, concentration and a common admissible stage.

## Numerator

The numerator splits into 220 U rows and 30 V rows.

- [U/Diagonal/](SixthMoment/Numerator/U/Diagonal), [U/MainTerm/](SixthMoment/Numerator/U/MainTerm), [U/ZeroModes/](SixthMoment/Numerator/U/ZeroModes): diagonal terms, main terms and zero-frequency contributions.
- [U/Separation/](SixthMoment/Numerator/U/Separation), [U/Replacement/](SixthMoment/Numerator/U/Replacement), [U/Reconstruction/](SixthMoment/Numerator/U/Reconstruction): separation of variables, replacements and recovery of the original moment.
- [U/Bounds/](SixthMoment/Numerator/U/Bounds), [U/Sources/](SixthMoment/Numerator/U/Sources): error estimates, weights and source bounds.
- [U/CertificateLimit.lean](SixthMoment/Numerator/U/CertificateLimit.lean): the U contribution's certificate limit.
- [V/Arithmetic/](SixthMoment/Numerator/V/Arithmetic), [V/EulerTransfer/](SixthMoment/Numerator/V/EulerTransfer): arithmetic factorization and transfer to Euler products.
- [V/Chi/](SixthMoment/Numerator/V/Chi), [V/Contour/](SixthMoment/Numerator/V/Contour), [V/DP/](SixthMoment/Numerator/V/DP): functional-equation factors, contour arguments and Dirichlet-polynomial estimates.
- [V/Asymptotic/](SixthMoment/Numerator/V/Asymptotic), [V/Profiles/](SixthMoment/Numerator/V/Profiles), [V/CertificateLimit.lean](SixthMoment/Numerator/V/CertificateLimit.lean): the V contribution's asymptotics and certificate limit.
- [Kernels/](SixthMoment/Numerator/Kernels), [Polar/](SixthMoment/Numerator/Polar), [Shared/](SixthMoment/Numerator/Shared): supporting kernel identities, pole contributions and shared lemmas.
- [CertificateStatement.lean](SixthMoment/Numerator/CertificateStatement.lean), [CertificateLimit.lean](SixthMoment/Numerator/CertificateLimit.lean): the combined numerator target and its limit.

## Denominator

- [Balanced/](SixthMoment/Denominator/Balanced), [Unbalanced/](SixthMoment/Denominator/Unbalanced): the two kernel contributions and their moment limits.
- [Measures/](SixthMoment/Denominator/Measures): weighted measures, convergence and integration steps.
- [Gram/](SixthMoment/Denominator/Gram): assembly of the certificate's Gram moment and its asymptotic.

## Final

- [CauchySchwarz.lean](SixthMoment/Final/CauchySchwarz.lean): the inequality connecting the moments to a sixth-moment lower bound.
- [CertificateLimit.lean](SixthMoment/Final/CertificateLimit.lean): the limiting certificate quotient.
- [DyadicScaling.lean](SixthMoment/Final/DyadicScaling.lean), [DyadicLowerBound.lean](SixthMoment/Final/DyadicLowerBound.lean), [DyadicAsymptotic.lean](SixthMoment/Final/DyadicAsymptotic.lean): normalization and finite dyadic assembly.

## Verification and project files

- [Verification/Final.lean](SixthMoment/Verification/Final.lean): checks the final type, explicit moment bound and standard axioms.
- [SixthMoment.lean](SixthMoment.lean), at the repository root: umbrella imports.
- [.github/workflows/full-goal.yml](.github/workflows/full-goal.yml): manual four-hour build stages with checkpoints and a final Lean check.
- Root [certificate_250.tsv](certificate_250.tsv): the exact certificate data.
- Root [Salt/Weil/](Salt/Weil): third-party Weil and Kloosterman results; provenance and license are recorded in [Salt/UPSTREAM.json](Salt/UPSTREAM.json) and [Salt/LICENSE](Salt/LICENSE).
- `lakefile.lean`, `lean-toolchain` and `lake-manifest.json`: build configuration and pinned dependencies.
