import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Certificate.Exact.GramEntries
import SixthMoment.Certificate.Kernels.Balanced.ZeroLink
import SixthMoment.Certificate.Kernels.Unbalanced.DenominatorMinusLink
import SixthMoment.Certificate.Profiles.NumeratorLimit


namespace SixthMoment
open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
set_option maxHeartbeats 2000000

def certificateEndpointProfile (typ : TestType) (a : ℝ) (n : ℕ) : ℝ → ℝ :=
  match typ with
  | .U => uEndpointProfile uNormalizedBump uCertificateHstar a n
  | .V => vEndpointProfile eta a n

def featureRealPolynomial (x : Finite.Feature) : Fin 5 → ℝ :=
  fun r => (Finite.coef x.poly r.val : ℝ)

def featureReflectedRealPolynomial (x : Finite.Feature) : Fin 5 → ℝ :=
  fun r => (Finite.coef (Finite.reflect x.poly) r.val : ℝ)

def certificateGramZeroKernel (x y : Finite.Feature) (z : Fin 4 → ℝ) : ℝ :=
  match x.typ, y.typ with
  | .U, .U =>
      denominatorZeroKernel (featureRealPolynomial x) (featureRealPolynomial y)
        (z 0) (z 3) (z 1) (z 2) +
      denominatorZeroKernel (featureRealPolynomial x) (featureReflectedRealPolynomial y)
        (z 0) (z 2) (z 1) (z 3)
  | .V, .V =>
      denominatorZeroKernel (featureRealPolynomial x) (featureRealPolynomial y)
        (z 0) (z 1) (z 2) (z 3)
  | _, _ => 0

def certificateGramMinusKernel (x y : Finite.Feature) (z : Fin 4 → ℝ) : ℝ :=
  match x.typ, y.typ with
  | .U, .V =>
      denominatorMinusKernel (featureRealPolynomial y) (featureRealPolynomial x)
        (z 1) (z 2) (z 3) (z 0) +
      denominatorMinusKernel (featureRealPolynomial x) (featureReflectedRealPolynomial y)
        (z 0) (z 2) (z 3) (z 1)
  | _, _ => 0

def certificateFeatureEndpoints (x y : Finite.Feature) : Fin 4 → ℝ :=
  ![realEndpoint x.A, realEndpoint x.B, realEndpoint y.A, realEndpoint y.B]

def certificateFeatureProfileIntegral (n : ℕ) (x y : Finite.Feature)
    (F : (Fin 4 → ℝ) → ℝ) : ℝ :=
  ∫ z : (ℝ × ℝ) × (ℝ × ℝ),
    certificateEndpointProfile x.typ (realEndpoint x.A) n z.1.1 *
    certificateEndpointProfile x.typ (realEndpoint x.B) n z.1.2 *
    certificateEndpointProfile y.typ (realEndpoint y.A) n z.2.1 *
    certificateEndpointProfile y.typ (realEndpoint y.B) n z.2.2 *
      F ![z.1.1,z.1.2,z.2.1,z.2.2] ∂((volume.prod volume).prod (volume.prod volume))

def certificateProfileGramZero (n : ℕ) (x y : Finite.Feature) : ℝ :=
  certificateFeatureProfileIntegral n x y (certificateGramZeroKernel x y)

def certificateProfileGramMinus (n : ℕ) (x y : Finite.Feature) : ℝ :=
  certificateFeatureProfileIntegral n x y (certificateGramMinusKernel x y)

def certificateProfileDenominator (n : ℕ) : ℝ :=
  (((Finite.pairs.map fun ij =>
    (if ij.1 = ij.2 then (1:ℝ) else 2) *
      certificateProfileGramZero n (Finite.feature ij.1) (Finite.feature ij.2)).sum) +
   ((Finite.pairs.map fun ij =>
    (if ij.1 = ij.2 then (1:ℝ) else 2) *
      certificateProfileGramMinus n (Finite.feature ij.1) (Finite.feature ij.2)).sum))/2

def certificatePointDenominator : ℝ :=
  (((Finite.pairs.map fun ij =>
    (if ij.1 = ij.2 then (1:ℝ) else 2) *
      certificateGramZeroKernel (Finite.feature ij.1) (Finite.feature ij.2)
        (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2))).sum) +
   ((Finite.pairs.map fun ij =>
    (if ij.1 = ij.2 then (1:ℝ) else 2) *
      certificateGramMinusKernel (Finite.feature ij.1) (Finite.feature ij.2)
        (certificateFeatureEndpoints (Finite.feature ij.1) (Finite.feature ij.2))).sum))/2

theorem certificateGramZeroKernel_endpoints (x y : Finite.Feature) :
    certificateGramZeroKernel x y (certificateFeatureEndpoints x y) =
      (Finite.gramZero x y : ℝ)/((Finite.d0Denominator : ℝ)*(Finite.scale : ℝ)^13) := by
  unfold certificateGramZeroKernel certificateFeatureEndpoints
    featureRealPolynomial featureReflectedRealPolynomial Finite.gramZero
  cases x.typ <;> cases y.typ <;> simp
  all_goals simp_rw [denominatorZeroKernel_eq_integer]
  all_goals ring

theorem certificateGramMinusKernel_endpoints (x y : Finite.Feature) :
    certificateGramMinusKernel x y (certificateFeatureEndpoints x y) =
      (Finite.gramMinus x y : ℝ)/((Finite.dminusDenominator : ℝ)*(Finite.scale : ℝ)^13) := by
  unfold certificateGramMinusKernel certificateFeatureEndpoints
    featureRealPolynomial featureReflectedRealPolynomial Finite.gramMinus
  cases x.typ <;> cases y.typ <;> simp
  all_goals simp_rw [denominatorMinusKernel_eq_integer]
  all_goals ring

end
end SixthMoment
