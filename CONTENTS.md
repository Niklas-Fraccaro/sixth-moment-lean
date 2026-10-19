# Contents

Paths below are relative to `Sechstmoment/`, unless stated otherwise.

## Entry points

| File | Content |
|---|---|
| [Statement.lean](Sechstmoment/Statement.lean) | The sixth-moment lower bound and `FullGoal`. |
| [LiteratureAssumption.lean](Sechstmoment/LiteratureAssumption.lean) | The Watt assumption and the conditional goal. |
| [Theorem.lean](Sechstmoment/Theorem.lean) | Final assembly and `fullProof`. |

## Analysis

- [Beta/](Sechstmoment/Analysis/Beta): exact integrals, normalized profiles, concentration and weak convergence.
- [Integration/](Sechstmoment/Analysis/Integration), [Measures/](Sechstmoment/Analysis/Measures): parameter integrals, differentiation under the integral, Cauchy–Schwarz and measure identities.
- [Complex/](Sechstmoment/Analysis/Complex), [Calculus/](Sechstmoment/Analysis/Calculus): holomorphy, partial derivatives, complex powers and compact products.
- [Fourier/](Sechstmoment/Analysis/Fourier), [Mellin/](Sechstmoment/Analysis/Mellin), [Harmonic/](Sechstmoment/Analysis/Harmonic): transforms, inversion, contour estimates and harmonic sums.
- [Gaussian/](Sechstmoment/Analysis/Gaussian), [Simplex/](Sechstmoment/Analysis/Simplex): Gaussian moments and simplex integrals.
- [Alternants/](Sechstmoment/Analysis/Alternants): exponential alternants and limits when parameters coincide.
- [Asymptotics/](Sechstmoment/Analysis/Asymptotics), [Dyadic/](Sechstmoment/Analysis/Dyadic), [Profiles/](Sechstmoment/Analysis/Profiles), [Quadrature/](Sechstmoment/Analysis/Quadrature): growth estimates, weights, profile classes and exact integration rules.

## Arithmetic

- [Factor/](Sechstmoment/Arithmetic/Factor): definition, convergence and positivity of $a_3$.
- [Divisors/](Sechstmoment/Arithmetic/Divisors): divisor-growth and logarithmic-frequency bounds.
- [Euler/](Sechstmoment/Arithmetic/Euler): local factors, convolutions, residues, remainders and shifted, bivariate and four-L Euler products.
- [Kloosterman/](Sechstmoment/Arithmetic/Kloosterman): definitions and estimates for Kloosterman sums.
- [Watt/](Sechstmoment/Arithmetic/Watt): Proposition 4.1 and its weight estimates and transformations.
- [QuadraticDivisor/](Sechstmoment/Arithmetic/QuadraticDivisor): quadratic-divisor inputs, parameters and estimates; [Reduction/](Sechstmoment/Arithmetic/QuadraticDivisor/Reduction) contains the reduction from Watt's proposition.
- [Exact/](Sechstmoment/Arithmetic/Exact): exact polynomial arithmetic.

## Zeta

- [SixthMoment.lean](Sechstmoment/Zeta/SixthMoment.lean): the moment integral and its normalization.
- [AFE/](Sechstmoment/Zeta/AFE): one-sided, two-factor and four-factor approximate functional equations.
- [DirichletL/](Sechstmoment/Zeta/DirichletL): character expansions, fourth-power bounds and products of four L-functions.
- [Chi/](Sechstmoment/Zeta/Chi), [Gamma/](Sechstmoment/Zeta/Gamma): functional-equation factors, gamma ratios and asymptotics.
- [Centering/](Sechstmoment/Zeta/Centering): centered derivative and polynomial identities.
- [Bounds/](Sechstmoment/Zeta/Bounds), [Moments/](Sechstmoment/Zeta/Moments): growth estimates and moment inequalities.
- Other modules define amplifiers, generators, regularized zeta functions and polynomial tests.

## Certificate

- [Data.lean](Sechstmoment/Certificate/Data.lean), [Row.lean](Sechstmoment/Certificate/Row.lean), [Scale.lean](Sechstmoment/Certificate/Scale.lean): the 250 rows, their type and scaling.
- [Tests.lean](Sechstmoment/Certificate/Tests.lean), [TestPolynomials.lean](Sechstmoment/Certificate/TestPolynomials.lean), [Features.lean](Sechstmoment/Certificate/Features.lean): the test functions and their polynomial features.
- [Exact/](Sechstmoment/Certificate/Exact), [Bounds.lean](Sechstmoment/Certificate/Bounds.lean): exact numerator and denominator calculations and the resulting rational bound.
- [Gram/](Sechstmoment/Certificate/Gram), [GramBlocks/](Sechstmoment/Certificate/GramBlocks): Gram-matrix assembly and 125 indexed computation blocks.
- [Kernels/](Sechstmoment/Certificate/Kernels): balanced and unbalanced certificate kernels.
- [Profiles/](Sechstmoment/Certificate/Profiles): profile approximations, concentration and a common admissible stage.

## Numerator

The numerator splits into 220 U rows and 30 V rows.

- [U/Diagonal/](Sechstmoment/Numerator/U/Diagonal), [U/MainTerm/](Sechstmoment/Numerator/U/MainTerm), [U/ZeroModes/](Sechstmoment/Numerator/U/ZeroModes): diagonal terms, main terms and zero-frequency contributions.
- [U/Separation/](Sechstmoment/Numerator/U/Separation), [U/Replacement/](Sechstmoment/Numerator/U/Replacement), [U/Reconstruction/](Sechstmoment/Numerator/U/Reconstruction): separation of variables, replacements and recovery of the original moment.
- [U/Bounds/](Sechstmoment/Numerator/U/Bounds), [U/Sources/](Sechstmoment/Numerator/U/Sources): error estimates, weights and source bounds.
- [U/CertificateLimit.lean](Sechstmoment/Numerator/U/CertificateLimit.lean): the U contribution's certificate limit.
- [V/Arithmetic/](Sechstmoment/Numerator/V/Arithmetic), [V/EulerTransfer/](Sechstmoment/Numerator/V/EulerTransfer): arithmetic factorization and transfer to Euler products.
- [V/Chi/](Sechstmoment/Numerator/V/Chi), [V/Contour/](Sechstmoment/Numerator/V/Contour), [V/DP/](Sechstmoment/Numerator/V/DP): functional-equation factors, contour arguments and Dirichlet-polynomial estimates.
- [V/Asymptotic/](Sechstmoment/Numerator/V/Asymptotic), [V/Profiles/](Sechstmoment/Numerator/V/Profiles), [V/CertificateLimit.lean](Sechstmoment/Numerator/V/CertificateLimit.lean): the V contribution's asymptotics and certificate limit.
- [Kernels/](Sechstmoment/Numerator/Kernels), [Polar/](Sechstmoment/Numerator/Polar), [Shared/](Sechstmoment/Numerator/Shared): supporting kernel identities, pole contributions and shared lemmas.
- [CertificateStatement.lean](Sechstmoment/Numerator/CertificateStatement.lean), [CertificateLimit.lean](Sechstmoment/Numerator/CertificateLimit.lean): the combined numerator target and its limit.

## Denominator

- [Balanced/](Sechstmoment/Denominator/Balanced), [Unbalanced/](Sechstmoment/Denominator/Unbalanced): the two kernel contributions and their moment limits.
- [Measures/](Sechstmoment/Denominator/Measures): weighted measures, convergence and integration steps.
- [Gram/](Sechstmoment/Denominator/Gram): assembly of the certificate's Gram moment and its asymptotic.

## Final

- [CauchySchwarz.lean](Sechstmoment/Final/CauchySchwarz.lean): the inequality connecting the moments to a sixth-moment lower bound.
- [CertificateLimit.lean](Sechstmoment/Final/CertificateLimit.lean): the limiting certificate quotient.
- [DyadicScaling.lean](Sechstmoment/Final/DyadicScaling.lean), [DyadicLowerBound.lean](Sechstmoment/Final/DyadicLowerBound.lean), [DyadicAsymptotic.lean](Sechstmoment/Final/DyadicAsymptotic.lean): normalization and finite dyadic assembly.

## Verification and project files

- [Verification/Final.lean](Sechstmoment/Verification/Final.lean): literal theorem-type checks and axiom queries.
- [Sechstmoment.lean](Sechstmoment.lean), at the repository root: umbrella imports.
- Root `verify_*.py` and `compile_full_goal.py`: compilation and axiom-audit runners; `test_*.py` tests their orchestration.
- Root [certificate_250.tsv](certificate_250.tsv): the exact certificate data.
- Root [Salt/Weil/](Salt/Weil): third-party Weil and Kloosterman results; provenance and license are recorded in `SALT-UPSTREAM.json` and `SALT-LICENSE`.
- `lakefile.lean`, `lean-toolchain` and `lake-manifest.json`: build configuration and pinned dependencies.
