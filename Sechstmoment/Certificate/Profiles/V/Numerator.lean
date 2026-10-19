import Mathlib.Tactic.ComputeDegree
import Sechstmoment.Certificate.Kernels.Balanced.Lengths
import Sechstmoment.Certificate.Profiles.GeneratorCoefficients
import Sechstmoment.Certificate.Profiles.V.BetaMoment
import Sechstmoment.Certificate.TestPolynomials
import Sechstmoment.Numerator.Kernels.WeightedIntegral
import Sechstmoment.Numerator.U.Reconstruction.RectangularBetaNumeratorConvergence

/-! The actual V-only part of the original 250-row certificate.
The type filter retains the original unscaled coefficients and row order.
No claim concerning the U rows or the full finite numerator is made here. -/
namespace Sechstmoment
open Complex MeasureTheory Set Metric Filter Polynomial
open scoped Topology BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Literal V rows selected from the original Appendix A certificate. -/
def vCertificateRows : List TestDatum := certificate.filter (fun d => decide (d.typ=.V))

theorem mem_vCertificateRows (d : TestDatum) :
    d∈vCertificateRows ↔ d∈certificate ∧ d.typ=.V := by simp [vCertificateRows]

/-- The filter selects exactly 30 of the original 250 rows. -/
theorem vCertificateRows_length : vCertificateRows.length=30 := by decide +kernel

/-- Exact original integer endpoint and degree bounds, checked in the kernel. -/
theorem vCertificate_integer_geometry : ∀ d∈vCertificateRows,
    2106419≤d.A ∧ d.A≤24997500 ∧ 2106419≤d.B ∧ d.B≤24997500 ∧ d.degree≤4 :=
  by decide +kernel

/-- The one shared sharp-DP profile length is the existing `eta=19999/80000`. -/
theorem vCertificate_endpoint_geometry {d : TestDatum} (hd : d∈vCertificateRows) :
    0<(d.A:ℝ)/base ∧ (d.A:ℝ)/base<eta ∧
      0<(d.B:ℝ)/base ∧ (d.B:ℝ)/base<eta ∧ d.degree≤4 := by
  obtain ⟨hAl,hAu,hBl,hBu,hdeg⟩ := vCertificate_integer_geometry d hd
  have hAl' : (2106419:ℝ)≤d.A := by exact_mod_cast hAl
  have hAu' : (d.A:ℝ)≤24997500 := by exact_mod_cast hAu
  have hBl' : (2106419:ℝ)≤d.B := by exact_mod_cast hBl
  have hBu' : (d.B:ℝ)≤24997500 := by exact_mod_cast hBu
  have hbase : (0:ℝ)<base := by norm_num [base]
  have hmax : (24997500:ℝ)/base<eta := by
    convert v_endpoint_lt_eta using 1
    norm_num [base]
  exact ⟨div_pos (by linarith) hbase,
    (div_le_div_of_nonneg_right hAu' hbase.le).trans_lt hmax,
    div_pos (by linarith) hbase,
    (div_le_div_of_nonneg_right hBu' hbase.le).trans_lt hmax,hdeg⟩

/-- Stage 12 is a common stage after which both literal beta endpoint values
vanish for every original V row, including the smallest endpoint. -/
theorem vCertificate_common_beta_stage {n : ℕ} (hn : 12≤n)
    {d : TestDatum} (hd : d∈vCertificateRows) :
    (betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) 0=0 ∧
      betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) eta=0) ∧
    (betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) 0=0 ∧
      betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) eta=0) := by
  obtain ⟨ha,haη,hb,hbη,_⟩ := vCertificate_endpoint_geometry hd
  obtain ⟨hAl,_,hBl,_,_⟩ := vCertificate_integer_geometry d hd
  have hn0 : 0<n := by omega
  have hn' : (12:ℝ)≤n := by exact_mod_cast hn
  have hAl' : (2106419:ℝ)≤d.A := by exact_mod_cast hAl
  have hBl' : (2106419:ℝ)≤d.B := by exact_mod_cast hBl
  have htA : eta≤(n:ℝ)*((d.A:ℝ)/base) := by
    have hh := mul_le_mul hn' hAl' (by norm_num : (0:ℝ)≤2106419) (by positivity : (0:ℝ)≤(n:ℝ))
    norm_num [eta,base] at *
    nlinarith
  have htB : eta≤(n:ℝ)*((d.B:ℝ)/base) := by
    have hh := mul_le_mul hn' hBl' (by norm_num : (0:ℝ)≤2106419) (by positivity : (0:ℝ)≤(n:ℝ))
    norm_num [eta,base] at *
    nlinarith
  exact ⟨betaProfile_endpoints eta_pos ha.le haη hn0 htA,
    betaProfile_endpoints eta_pos hb.le hbη hn0 htB⟩

/-- All five manuscript polynomials obey the same degree-four bound; the
assigned zero value at unsupported indices does too. -/
theorem manuscriptTestPolynomial_natDegree_le_four (m : ℕ) :
    (manuscriptTestPolynomial m).natDegree≤4 := by
  unfold manuscriptTestPolynomial
  split <;> compute_degree!

/-- Exact coefficient agreement between actual zeta-test polynomials and
original integer numerator coefficient lists. -/
theorem manuscriptTestPolynomial_coeff_eq_cheb (m : ℕ) (hm : m≤4) (r : Fin 5) :
    (manuscriptTestPolynomial m).coeff r.val=(Finite.coef (Finite.cheb m) r.val:ℝ) := by
  interval_cases m <;> fin_cases r <;>
    norm_num [manuscriptTestPolynomial,Finite.coef,Finite.cheb,Polynomial.coeff_add,
      Polynomial.coeff_sub,Polynomial.coeff_mul,Polynomial.coeff_X_pow,Polynomial.coeff_one,Polynomial.coeff_X]

/-- The literal raw partial certificate test, retaining its original coefficients. -/
def vCertificateRawZetaTest (n : ℕ) (T t : ℝ) : ℂ :=
  (vCertificateRows.map fun d => (d.coefficient:ℂ)*
    rawZetaTest .V T t (manuscriptTestPolynomial d.degree)
      (vEndpointProfile eta ((d.A:ℝ)/base) n)
      (vEndpointProfile eta ((d.B:ℝ)/base) n)).sum

/-- Actual phase projection of the V-only partial certificate. -/
def vCertificateZetaTest (n : ℕ) (T t : ℝ) : ℂ :=
  phaseProjection (criticalChi t) (vCertificateRawZetaTest n T t)

private theorem v_phaseProjection_list_sum (χ : ℂ) (l : List ℂ) :
    phaseProjection χ l.sum=(l.map (phaseProjection χ)).sum := by
  induction l with
  | nil => simp [phaseProjection]
  | cons x xs ih => simp only [List.sum_cons,List.map_cons,phaseProjection_add,ih]

/-- The actual partial test is exactly the original-row sum of projected V tests. -/
theorem vCertificateZetaTest_eq_sum (n : ℕ) (T t : ℝ) :
    vCertificateZetaTest n T t=(vCertificateRows.map fun d => (d.coefficient:ℂ)*
      projectedZetaTest .V T t (manuscriptTestPolynomial d.degree)
        (vEndpointProfile eta ((d.A:ℝ)/base) n)
        (vEndpointProfile eta ((d.B:ℝ)/base) n)).sum := by
  unfold vCertificateZetaTest vCertificateRawZetaTest
  rw [v_phaseProjection_list_sum,List.map_map]
  congr 2
  funext d
  change phaseProjection (criticalChi t) ((d.coefficient:ℂ)*_)=_
  have hc : (d.coefficient:ℂ)=((d.coefficient:ℝ):ℂ) := by norm_cast
  rw [hc,phaseProjection_real_smul]
  rfl

private theorem v_mixed_list_sum (l : List TestDatum) (F : TestDatum→ℂ) (W : ℂ) :
    W*star ((l.map fun d => (d.coefficient:ℂ)*F d).sum)=
      (l.map fun d => (d.coefficient:ℂ)*(W*star (F d))).sum := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons,star_add,star_mul,star_intCast,mul_add]
    rw [ih]
    ring

private theorem v_list_integrable (l : List TestDatum) (f : TestDatum→ℝ→ℂ)
    (hi : ∀ d∈l, Integrable (f d)) : Integrable (fun t => (l.map fun d => f d t).sum) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (hi d List.mem_cons_self).add (ih (fun e he => hi e (List.mem_cons_of_mem _ he)))

private theorem v_integral_list_sum (l : List TestDatum) (f : TestDatum→ℝ→ℂ)
    (hi : ∀ d∈l, Integrable (f d)) :
    (∫ t : ℝ, (l.map fun d => f d t).sum)=(l.map fun d => ∫ t : ℝ, f d t).sum := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons]
    rw [integral_add (hi d List.mem_cons_self)
      (v_list_integrable ds f (fun e he => hi e (List.mem_cons_of_mem _ he)))]
    rw [ih (fun e he => hi e (List.mem_cons_of_mem _ he))]

/-- Literal actual mixed integral of the V-only raw partial certificate. -/
def vCertificateRawMixedMoment (n : ℕ) (T : ℝ) (Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (vCertificateRawZetaTest n T t)

/-- Literal actual mixed integral of the V-only projected partial certificate. -/
def vCertificateProjectedMixedMoment (n : ℕ) (T : ℝ) (Φ : ℝ→ℝ) : ℂ :=
  ∫ t : ℝ, (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
    star (vCertificateZetaTest n T t)

/-- The actual finite raw test integrand is integrable, proved row by row. -/
theorem vCertificateRawMixedIntegrand_integrable (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (vCertificateRawZetaTest n T t)) := by
  have hi (d : TestDatum) : Integrable (fun t : ℝ => (d.coefficient:ℂ)*
      ((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (rawZetaTest .V T t (manuscriptTestPolynomial d.degree)
          (vEndpointProfile eta ((d.A:ℝ)/base) n)
          (vEndpointProfile eta ((d.B:ℝ)/base) n)))) :=
    (vPolynomialRawMixedIntegrand_integrable hT hL eta eta _ _ _ Φ
      (fun x hx => vEndpointProfile_zero_above eta _ n hx)
      (fun x hx => vEndpointProfile_zero_above eta _ n hx) hΦ).const_mul _
  exact (v_list_integrable vCertificateRows _ (fun d _ => hi d)).congr
    (Eventually.of_forall (fun t => (v_mixed_list_sum vCertificateRows _ _).symm))

/-- Exact finite-sum/integral interchange for the literal original V test. -/
theorem vCertificateRawMixedMoment_eq_sum (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    vCertificateRawMixedMoment n T Φ=(vCertificateRows.map fun d => (d.coefficient:ℂ)*
      vPolynomialRawMixedMoment T (manuscriptTestPolynomial d.degree)
        (vEndpointProfile eta ((d.A:ℝ)/base) n)
        (vEndpointProfile eta ((d.B:ℝ)/base) n) Φ).sum := by
  unfold vCertificateRawMixedMoment vCertificateRawZetaTest
  simp_rw [v_mixed_list_sum]
  rw [v_integral_list_sum _ _ (fun d _ =>
    (vPolynomialRawMixedIntegrand_integrable hT hL eta eta _ _ _ Φ
      (fun x hx => vEndpointProfile_zero_above eta _ n hx)
      (fun x hx => vEndpointProfile_zero_above eta _ n hx) hΦ).const_mul _)]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  rw [integral_const_mul]
  rfl

private theorem vCertificateProjectedMixedIntegrand_eq_real (n : ℕ) (T t : ℝ) (Φ : ℝ→ℝ) :
    (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*star (vCertificateZetaTest n T t)=
      Complex.ofReal (((Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
        star (vCertificateRawZetaTest n T t)).re) := by
  rw [mul_assoc]
  unfold vCertificateZetaTest
  rw [zeta_phaseProjection_mixed_re]
  apply Complex.ext
  · simp [Complex.mul_re,Complex.mul_im]
    ring
  · simp [Complex.mul_re,Complex.mul_im]

/-- Integrability of the actual projected partial certificate integrand. -/
theorem vCertificateProjectedMixedIntegrand_integrable (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Integrable (fun t : ℝ => (Φ (t/T):ℂ)*riemannZeta (criticalLinePoint t)^3*
      star (vCertificateZetaTest n T t)) :=
  ((vCertificateRawMixedIntegrand_integrable n hT hL Φ hΦ).re.ofReal).congr
    (Eventually.of_forall (fun t => (vCertificateProjectedMixedIntegrand_eq_real n T t Φ).symm))

/-- Exact real-part relation for the actual phase-projected V-only moment. -/
theorem vCertificateProjectedMixedMoment_eq_real (n : ℕ) {T : ℝ} (hT : 1<T)
    (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    vCertificateProjectedMixedMoment n T Φ=Complex.ofReal ((vCertificateRawMixedMoment n T Φ).re) := by
  unfold vCertificateProjectedMixedMoment vCertificateRawMixedMoment
  rw [integral_congr_ae (Eventually.of_forall (fun t =>
    vCertificateProjectedMixedIntegrand_eq_real n T t Φ))]
  exact (integral_ofReal (𝕜 := ℂ)).trans
    (congrArg Complex.ofReal (integral_re (vCertificateRawMixedIntegrand_integrable n hT hL Φ hΦ)))

/-- The actual coefficient vector of each original certificate polynomial. -/
def vCertificatePolynomialCoefficients (d : TestDatum) : Fin 5→ℝ :=
  fun r => (manuscriptTestPolynomial d.degree).coeff r.val

/-- The V-only original-row endpoint numerator; the U contribution is separate. -/
def vCertificateNumeratorKernel : ℝ :=
  (vCertificateRows.map fun d => (d.coefficient:ℝ)*
    numeratorPointKernel (vCertificatePolynomialCoefficients d)
      ((d.A:ℝ)/base) (1-(d.B:ℝ)/base)).sum

/-- The actual common-stage double beta kernel for the original V rows. -/
def vCertificateBetaKernel (n : ℕ) : ℝ :=
  (vCertificateRows.map fun d => (d.coefficient:ℝ)*
    (∫ x in (0:ℝ)..eta, ∫ y in (0:ℝ)..eta,
      betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) x*
      betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) y*
      numeratorPointKernel (vCertificatePolynomialCoefficients d) x (1-y))).sum

/-- Literal identification of the partial test with the V-filtered original
250-row expression, retaining the supplied row types. -/
theorem vCertificateRawZetaTest_eq_original_filtered (n : ℕ) (T t : ℝ) :
    vCertificateRawZetaTest n T t=(vCertificateRows.map fun d => (d.coefficient:ℂ)*
      rawZetaTest d.typ T t (manuscriptTestPolynomial d.degree)
        (vEndpointProfile eta ((d.A:ℝ)/base) n)
        (vEndpointProfile eta ((d.B:ℝ)/base) n)).sum := by
  unfold vCertificateRawZetaTest
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  rw [(mem_vCertificateRows d).mp hd |>.2]

/-- The terminal V kernel is precisely the original finite evaluator's V
subsum, not the complete original numerator. -/
theorem vCertificateNumeratorKernel_eq_original_V_feature_subsum :
    vCertificateNumeratorKernel=(vCertificateRows.map fun d =>
      numeratorFeatureKernel (datumFeature d)).sum := by
  unfold vCertificateNumeratorKernel
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  have hmem := (mem_vCertificateRows d).mp hd
  obtain ⟨_,_,_,hBu,_⟩ := vCertificate_integer_geometry d hd
  have hBbase : d.B≤base := by norm_num [base]; omega
  have hfrac : 1-(d.B:ℝ)/base=((base-d.B:ℕ):ℝ)/base := by
    rw [Nat.cast_sub hBbase]
    norm_num [base]
    ring
  have hcoeff : vCertificatePolynomialCoefficients d=
      (fun r : Fin 5 => (Finite.coef (Finite.cheb d.degree) r.val:ℝ)) := by
    funext r
    exact manuscriptTestPolynomial_coeff_eq_cheb d.degree
      (vCertificate_endpoint_geometry hd).2.2.2.2 r
  rw [hcoeff,hfrac,datumFeatureKernel_weighted hmem.1]
  simp [numeratorSecondMass,datumFeature,hmem.2,base,Finite.base]

/-- Actual two-beta concentration of the finite original V-row weighted kernel. -/
theorem vCertificateBetaKernel_tendsto :
    Tendsto vCertificateBetaKernel atTop (𝓝 vCertificateNumeratorKernel) := by
  unfold vCertificateBetaKernel vCertificateNumeratorKernel
  apply tendsto_list_sum
  intro d hd
  obtain ⟨ha,haη,hb,hbη,_⟩ := vCertificate_endpoint_geometry hd
  exact (rectangular_two_beta_numerator_tendsto (vCertificatePolynomialCoefficients d)
    eta_pos eta_lt_quarter ha.le haη.le hb.le hbη.le).const_mul (d.coefficient:ℝ)

private theorem v_beta_weightedPointKernel_eq (d : TestDatum) (n : ℕ) :
    weightedNumeratorPointKernel (vCertificatePolynomialCoefficients d) eta
      (betaProfilePolynomial eta n (betaProfileIndex eta ((d.A:ℝ)/base) n))
      (betaProfilePolynomial eta n (betaProfileIndex eta ((d.B:ℝ)/base) n)) =
    ∫ x in (0:ℝ)..eta, ∫ y in (0:ℝ)..eta,
      betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) x*
      betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) y*
      numeratorPointKernel (vCertificatePolynomialCoefficients d) x (1-y) := by
  unfold weightedNumeratorPointKernel polynomialIntervalProfile
  simp_rw [←betaScaledProfile_eq_polynomial_eval]

private theorem v_list_sum_div (l : List TestDatum) (f : TestDatum→ℂ) (b : ℂ) :
    (l.map f).sum/b=(l.map fun d => f d/b).sum := by
  induction l with
  | nil => simp
  | cons d ds ih => simp only [List.map_cons,List.sum_cons,add_div,ih]

private theorem v_weighted_complex_list_sum (l : List TestDatum) (c : ℂ) (f : TestDatum→ℝ) :
    (l.map fun d => (d.coefficient:ℂ)*(c*Complex.ofReal (f d))).sum=
      c*Complex.ofReal ((l.map fun d => (d.coefficient:ℝ)*f d).sum) := by
  induction l with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons,List.sum_cons,ih,Complex.ofReal_add,Complex.ofReal_mul]
    have hc : (d.coefficient:ℂ)=((d.coefficient:ℝ):ℂ) := by norm_cast
    rw [hc]
    ring

namespace Source

private theorem v_certificate_row_fixed_stage_tendsto (hsource : DPv2SharpInput)
    (d : TestDatum) (hd : d∈vCertificateRows) (n : ℕ) (hn : 0<n)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vPolynomialRawMixedMoment T (manuscriptTestPolynomial d.degree)
      (vEndpointProfile eta ((d.A:ℝ)/base) n)
      (vEndpointProfile eta ((d.B:ℝ)/base) n) Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal
        (∫ x in (0:ℝ)..eta, ∫ y in (0:ℝ)..eta,
          betaScaledProfile eta n (betaProfileIndex eta ((d.A:ℝ)/base) n) x*
          betaScaledProfile eta n (betaProfileIndex eta ((d.B:ℝ)/base) n) y*
          numeratorPointKernel (vCertificatePolynomialCoefficients d) x (1-y)))) := by
  obtain ⟨ha,haη,hb,hbη,_⟩ := vCertificate_endpoint_geometry hd
  have ht := vBetaRawMixedMoment_tendsto 4 hsource eta eta_pos eta_lt_quarter
    ((d.A:ℝ)/base) ((d.B:ℝ)/base) ha.le haη hb.le hbη n n hn hn
    (manuscriptTestPolynomial d.degree) (manuscriptTestPolynomial_natDegree_le_four d.degree) Φ hΦ
  change Tendsto _ _ (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    finiteDifferentialOperator 4 (fun r => (vCertificatePolynomialCoefficients d r:ℂ))
      (vReflectedPolynomialJ eta
        (betaProfilePolynomial eta n (betaProfileIndex eta ((d.A:ℝ)/base) n))
        (betaProfilePolynomial eta n (betaProfileIndex eta ((d.B:ℝ)/base) n))) 0)) at ht
  rw [vReflectedPolynomialJ_operator_eq_weightedNumerator _ eta eta_pos eta_lt_quarter,
    v_beta_weightedPointKernel_eq] at ht
  exact ht

/-- Actual T→∞ limit of the entire original V-only raw test at every fixed
common positive beta stage, with no target test-moment hypothesis. -/
theorem vCertificateRawMixedMoment_fixed_stage_tendsto (hsource : DPv2SharpInput)
    (n : ℕ) (hn : 0<n) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vCertificateRawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n))) := by
  have ht := tendsto_list_sum vCertificateRows (fun d hd =>
    (v_certificate_row_fixed_stage_tendsto hsource d hd n hn Φ hΦ).const_mul (d.coefficient:ℂ))
  rw [v_weighted_complex_list_sum] at ht
  change Tendsto _ _ (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
    Complex.ofReal (vCertificateBetaKernel n))) at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  rw [vCertificateRawMixedMoment_eq_sum n hT hL Φ hΦ,v_list_sum_div]
  apply congrArg List.sum
  apply List.map_congr_left
  intro d _
  ring

/-- Exact normalization/projection identity for the actual finite V-only test. -/
theorem vCertificateProjectedMixedMoment_normalized_eq_real (n : ℕ)
    {T : ℝ} (hT : 1<T) (hL : 16<Real.log T) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    vCertificateProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)=
      Complex.ofReal ((vCertificateRawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)).re) := by
  rw [vCertificateProjectedMixedMoment_eq_real n hT hL Φ hΦ]
  have hden : (T:ℂ)*(Real.log T:ℂ)^9=Complex.ofReal (T*(Real.log T)^9) := by
    push_cast
    rfl
  rw [hden,Complex.div_ofReal_re,Complex.ofReal_div]

/-- Fixed-stage height limit of the actual projected original V-only test.
The main term is real because both the source weight and kernel are real. -/
theorem vCertificateProjectedMixedMoment_fixed_stage_tendsto (hsource : DPv2SharpInput)
    (n : ℕ) (hn : 0<n) (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    Tendsto (fun T : ℝ => vCertificateProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9))
      atTop (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n))) := by
  have ht := vCertificateRawMixedMoment_fixed_stage_tendsto hsource n hn Φ hΦ
  have hr := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)
  have he : Complex.ofReal (((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (vCertificateBetaKernel n)).re)=
      (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n) := by
    have hI : (∫ x : ℝ, (Φ x:ℂ))=Complex.ofReal (∫ x : ℝ, Φ x) := integral_ofReal (𝕜 := ℂ)
    rw [hI]
    simp
  rw [he] at hr
  apply hr.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (16:ℝ))] with T hT hL
  exact (vCertificateProjectedMixedMoment_normalized_eq_real n hT hL Φ hΦ).symm

/-- The literal original V subcertificate numerator is closed in the
manuscript's order: height tends to infinity at each fixed common beta stage,
then beta concentration yields only the original finite V contribution.
The U rows and the complete finite numerator are outside this statement. -/
theorem vCertificate_two_stage_numerator_limit (hsource : DPv2SharpInput)
    (Φ : ℝ→ℝ) (hΦ : SmoothDyadicWeight Φ) :
    (∀ n : ℕ, 12≤n → Tendsto
      (fun T : ℝ => vCertificateRawMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n)))) ∧
    (∀ n : ℕ, 12≤n → Tendsto
      (fun T : ℝ => vCertificateProjectedMixedMoment n T Φ/((T:ℂ)*(Real.log T:ℂ)^9)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal (vCertificateBetaKernel n)))) ∧
    Tendsto (fun n : ℕ => (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*
      Complex.ofReal (vCertificateBetaKernel n)) atTop
      (𝓝 ((arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*Complex.ofReal vCertificateNumeratorKernel)) := by
  refine ⟨fun n hn => vCertificateRawMixedMoment_fixed_stage_tendsto hsource n (by omega) Φ hΦ,
    fun n hn => vCertificateProjectedMixedMoment_fixed_stage_tendsto hsource n (by omega) Φ hΦ,?_⟩
  exact (Complex.continuous_ofReal.continuousAt.tendsto.comp vCertificateBetaKernel_tendsto).const_mul _

end Source
end
end Sechstmoment
