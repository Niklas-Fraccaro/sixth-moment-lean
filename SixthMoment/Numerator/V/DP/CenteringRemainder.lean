import SixthMoment.Arithmetic.QuadraticDivisor.Definitions
import SixthMoment.Numerator.V.DP.DPSmoothUniform
import SixthMoment.Zeta.Moments.CenteringRemainder

namespace SixthMoment
open Complex Filter MeasureTheory Set Polynomial
open scoped BigOperators Topology Interval ComplexConjugate
noncomputable section

private theorem reCLM_norm_le_one : ‖Complex.reCLM‖ ≤ 1 := by
  apply Complex.reCLM.opNorm_le_bound (by norm_num)
  intro v
  simpa using Complex.abs_re_le_norm v

private theorem imCLM_norm_le_one : ‖Complex.imCLM‖ ≤ 1 := by
  apply Complex.imCLM.opNorm_le_bound (by norm_num)
  intro v
  simpa using Complex.abs_im_le_norm v

theorem dpCenteringErrorWeight_complex_split (T : ℝ) (Φ : ℝ → ℝ) (z w : ℂ) (x : ℝ) :
    (dpCenteringErrorWeight T Φ z w Complex.reCLM x : ℂ)+
      Complex.I*(dpCenteringErrorWeight T Φ z w Complex.imCLM x : ℂ) =
      (Real.log T : ℂ)*(Φ x : ℂ)*dpCenteringPairError T (x : ℂ) z w := by
  apply Complex.ext <;> simp [dpCenteringErrorWeight, Complex.mul_re, Complex.mul_im] <;> ring

def dpCenteringRemainderMoment (T η : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, dpCenteringPairError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
    chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ

theorem dpCenteringRemainderMoment_eq_real_weights {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ)
    (hσ : ∀ j, 2*‖σ j‖ < Real.log T) :
    dpCenteringRemainderMoment T η P σ Φ =
      (chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.reCLM)+
      Complex.I*chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.imCLM))/(Real.log T : ℂ) := by
  have hL := Real.log_pos hT
  have hLc : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hraw (j : Fin 4) : |(rawMomentShifts T σ j).re| < 1/2 := by
    calc
      _ ≤ ‖rawMomentShifts T σ j‖ := Complex.abs_re_le_norm _
      _ = ‖σ j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith [hσ j])
  have hr := dpCenteringErrorWeight_smooth hΦ hL (σ 2) (σ 3) (hσ 2) (hσ 3) Complex.reCLM
  have hi := dpCenteringErrorWeight_smooth hΦ hL (σ 2) (σ 3) (hσ 2) (hσ 3) Complex.imCLM
  have hir := chiTwistedFourthIntegrand_integrable hT η (rawMomentShifts T σ)
    _ _ _ hraw (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hr
  have hii := chiTwistedFourthIntegrand_integrable hT η (rawMomentShifts T σ)
    _ _ _ hraw (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hi
  let R : ℝ → ℂ := fun t => chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
    (dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.reCLM)
  let J : ℝ → ℂ := fun t => chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
    (dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.imCLM)
  have he (t : ℝ) : dpCenteringPairError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
      chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ =
      (Real.log T : ℂ)⁻¹*(R t+Complex.I*J t) := by
    have hs := dpCenteringErrorWeight_complex_split T Φ (σ 2) (σ 3) (t/T)
    unfold R J chiTwistedFourthIntegrand
    rw [mul_add]
    have hh : (Real.log T : ℂ)⁻¹ *
        ((dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.reCLM (t/T) : ℂ)+
          I*(dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.imCLM (t/T) : ℂ)) =
        (Φ (t/T) : ℂ)*dpCenteringPairError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3) := by
      rw [hs]
      field_simp
    linear_combination -(shiftedFourthProduct t (rawMomentShifts T σ)*criticalChi t*
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) (1-criticalLinePoint t)*
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) (1-criticalLinePoint t))*hh
  unfold dpCenteringRemainderMoment
  rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul,
    integral_add hir (hii.const_mul Complex.I), integral_const_mul]
  unfold chiTwistedFourthMoment
  ring

private theorem smoothDyadicWeight_integral_norm_le (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) {B : ℝ} (hb : ∀ x, ‖Φ x‖ ≤ B) :
    ‖∫ x : ℝ, (Φ x : ℂ)‖ ≤ 2*B := by
  have hs : Function.support (fun x : ℝ => (Φ x : ℂ)) ⊆ Ioc (0 : ℝ) 2 := by
    intro x hx
    have hx' : x ∈ tsupport Φ := subset_tsupport Φ (by simpa using hx)
    have hm := hΦ.2 hx'
    exact ⟨by linarith [hm.1],hm.2⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hs]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 2) (C := B) (f := fun x : ℝ => (Φ x : ℂ))
    (fun x (_hx : x ∈ Ι (0 : ℝ) 2) => by simpa only [Complex.norm_real] using hb x)
  simpa [mul_comm] using hh


theorem dpCenteringRemainderMoment_uniform_bound (hsource : Source.DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K)
    (hsep : ∀ σ ∈ K, Source.DPSeparated σ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpCenteringRemainderMoment T η P σ Φ‖ ≤ C*T*(Real.log T)^8 := by
  obtain ⟨R,hRpos,hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hR : 0 ≤ R := hRpos.le
  have hCen : 0 ≤ centeringUniformConstant R := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  let BW := 15*B*centeringUniformConstant R
  have hBW : 0 ≤ BW := by dsimp [BW]; positivity
  obtain ⟨C,hC,hSource⟩ := Source.dpActualMoment_uniform_smoothing hsource
    η hη hηu P K hK hsep BW hBW
  obtain ⟨D,hD,hRes⟩ := Source.dpNormalizedFourResidues_compact_bound η P K hK hsep
  let RD := ‖(arithmeticFactor : ℂ)‖*|η|^6*D
  have hRD : 0 ≤ RD := by dsimp [RD]; positivity
  let M := C+6*B*centeringUniformConstant R*RD
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨2*M,by positivity,?_⟩
  filter_upwards [hSource, dpCenteringErrorWeight_uniform_deriv_bound hR hB,
    dpCenteringErrorWeight_uniform_norm_bound hR hB, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (max 1 (2*R)))]
    with T hSource hDeriv hNorm hT hLog
  intro σ hσ Φ hΦ hΦB
  have hLp := Real.log_pos hT
  have hL1 : 1 ≤ Real.log T := ((le_max_left _ _).trans_lt hLog).le
  have hσR (j : Fin 4) : ‖σ j‖ ≤ R := (norm_le_pi_norm σ j).trans (hRK σ hσ)
  have hσstrip (j : Fin 4) : 2*‖σ j‖ < Real.log T :=
    (mul_le_mul_of_nonneg_left (hσR j) (by norm_num)).trans_lt
      ((le_max_right _ _).trans_lt hLog)
  have hDensity : ‖Source.dpLeadingDensity T η P σ‖ ≤ RD*(Real.log T)^9 := by
    unfold Source.dpLeadingDensity
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    calc
      _ ≤ |arithmeticFactor| *(Real.log T)^9*|η|^6*D := by
        gcongr
        exact hRes σ hσ 1 (by norm_num)
      _ = _ := by dsimp [RD]; simp only [Complex.norm_real,Real.norm_eq_abs]; ring
  have hL89 : (Real.log T)^8 ≤ (Real.log T)^9 := by
    calc
      _ = (Real.log T)^8*1 := by ring
      _ ≤ (Real.log T)^8*Real.log T := mul_le_mul_of_nonneg_left hL1 (pow_nonneg hLp.le 8)
      _ = _ := (pow_succ (Real.log T) 8).symm
  have hMoment (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (σ 2) (σ 3) ℓ)‖ ≤ M*T*(Real.log T)^9 := by
    let W := dpCenteringErrorWeight T Φ (σ 2) (σ 3) ℓ
    have hW : SmoothDyadicWeight W := dpCenteringErrorWeight_smooth hΦ hLp
      (σ 2) (σ 3) (hσstrip 2) (hσstrip 3) ℓ
    have hWd : ∀ x, |deriv W x| ≤ BW := by
      intro x
      simpa only [Real.norm_eq_abs] using
        hDeriv Φ hΦ hΦB (σ 2) (σ 3) (hσR 2) (hσR 3) ℓ hℓ x
    have hWn : ‖∫ x : ℝ, (W x : ℂ)‖ ≤ 6*B*centeringUniformConstant R := by
      have hh := smoothDyadicWeight_integral_norm_le W hW
        (hNorm Φ hΦ hΦB (σ 2) (σ 3) (hσR 2) (hσR 3) ℓ hℓ)
      convert hh using 1; ring
    have hb := hSource σ hσ W hW hWd
    calc
      _ ≤ ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) W-
          (T : ℂ)*(∫ x : ℝ, (W x : ℂ))*Source.dpLeadingDensity T η P σ‖+
          ‖(T : ℂ)*(∫ x : ℝ, (W x : ℂ))*Source.dpLeadingDensity T η P σ‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ C*T*(Real.log T)^8+
          T*(6*B*centeringUniformConstant R)*(RD*(Real.log T)^9) := by
        apply add_le_add hb
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hT)]
        gcongr
      _ ≤ C*T*(Real.log T)^9+
          T*(6*B*centeringUniformConstant R)*(RD*(Real.log T)^9) := by gcongr
      _ = _ := by dsimp [M]; ring
  rw [dpCenteringRemainderMoment_eq_real_weights hT η P σ Φ hΦ hσstrip,
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
  calc
    _ ≤ (‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.reCLM)‖+
        ‖Complex.I*chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (σ 2) (σ 3) Complex.imCLM)‖)/Real.log T :=
      div_le_div_of_nonneg_right (norm_add_le _ _) hLp.le
    _ ≤ (M*T*(Real.log T)^9+M*T*(Real.log T)^9)/Real.log T := by
      simp only [norm_mul,Complex.norm_I,one_mul]
      exact div_le_div_of_nonneg_right (add_le_add
        (hMoment Complex.reCLM reCLM_norm_le_one) (hMoment Complex.imCLM imCLM_norm_le_one)) hLp.le
    _ = _ := by field_simp; ring


theorem lowerCenteringFactor_inv_real {T : ℝ} (hL : 0 < Real.log T)
    (x : ℝ) (z : ℂ) (hz : 2*‖z‖ < Real.log T) :
    (lowerCenteringFactor T (x : ℂ) z)⁻¹ =
      centeringFactorAt T (complexHeightPoint T (x : ℂ)) (-z) := by
  let s := complexHeightPoint T (x : ℂ)
  have hs : 0 < s.re ∧ s.re < 1 := by simp [s,complexHeightPoint]; norm_num
  have hp : s = criticalLinePoint (T*x) := by
    unfold s complexHeightPoint criticalLinePoint
    push_cast
    ring
  have hw : 0 < (s-z/(Real.log T : ℂ)).re ∧ (s-z/(Real.log T : ℂ)).re < 1 := by
    have hh := centeringShift_mem_strip hL (T*x) (-z) (by simpa using hz)
    simpa only [← hp,centeringShift,neg_div,sub_eq_add_neg] using hh
  have hbase : zetaChi (1-s) = (zetaChi s)⁻¹ :=
    eq_inv_of_mul_eq_one_left (zetaChi_one_sub_mul hs.1 hs.2)
  have hshift : zetaChi (1-s+z/(Real.log T : ℂ)) =
      (zetaChi (s-z/(Real.log T : ℂ)))⁻¹ := by
    have hh := eq_inv_of_mul_eq_one_left (zetaChi_one_sub_mul hw.1 hw.2)
    convert hh using 1; congr 1; ring
  have hbase0 := zetaChi_ne_zero_strip hs.1 hs.2
  have hshift0 := zetaChi_ne_zero_strip hw.1 hw.2
  have he : lowerCenteringFactor T (x : ℂ) z*
      centeringFactorAt T s (-z) = 1 := by
    unfold lowerCenteringFactor centeringFactorAt
    change (Complex.exp z*zetaChi (1-s+z/(Real.log T : ℂ))/zetaChi (1-s))*
      (Complex.exp (-z)*zetaChi (s+(-z)/(Real.log T : ℂ))/zetaChi s)=1
    rw [hbase,hshift,neg_div,← sub_eq_add_neg,Complex.exp_neg]
    field_simp
  exact inv_eq_of_mul_eq_one_right he

def dpCenteringPairInverseError (T : ℝ) (x z w : ℂ) : ℂ :=
  (lowerCenteringFactor T x z*lowerCenteringFactor T x w)⁻¹-1

theorem dpCenteringPairInverseError_eq_conj {T : ℝ} (hL : 0 < Real.log T)
    (x : ℝ) (z w : ℂ) (hz : 2*‖z‖ < Real.log T) (hw : 2*‖w‖ < Real.log T) :
    dpCenteringPairInverseError T (x : ℂ) z w =
      conj (dpCenteringPairError T (x : ℂ) (-conj z) (-conj w)) := by
  have hz' := lowerCenteringFactor_eq_conj T (x : ℂ) (-conj z)
  have hw' := lowerCenteringFactor_eq_conj T (x : ℂ) (-conj w)
  simp only [map_neg,Complex.conj_conj,Complex.conj_ofReal] at hz' hw'
  have hz'' : centeringFactorAt T (complexHeightPoint T (x : ℂ)) (-z) =
      conj (lowerCenteringFactor T (x : ℂ) (-conj z)) := by
    rw [hz',Complex.conj_conj]
  have hw'' : centeringFactorAt T (complexHeightPoint T (x : ℂ)) (-w) =
      conj (lowerCenteringFactor T (x : ℂ) (-conj w)) := by
    rw [hw',Complex.conj_conj]
  unfold dpCenteringPairInverseError dpCenteringPairError
  rw [mul_inv_rev,lowerCenteringFactor_inv_real hL x w hw,
    lowerCenteringFactor_inv_real hL x z hz,hz'',hw'',map_sub,map_mul,map_one]
  ring

def dpCenteringInverseRemainderMoment (T η : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, dpCenteringPairInverseError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
    chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
      (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ

theorem dpCenteringInverseRemainderMoment_eq_real_weights {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ)
    (hσ : ∀ j, 2*‖σ j‖ < Real.log T) :
    dpCenteringInverseRemainderMoment T η P σ Φ =
      (chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.reCLM)-
      Complex.I*chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.imCLM))/(Real.log T : ℂ) := by
  have hL := Real.log_pos hT
  have hLc : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hraw (j : Fin 4) : |(rawMomentShifts T σ j).re| < 1/2 := by
    calc
      _ ≤ ‖rawMomentShifts T σ j‖ := Complex.abs_re_le_norm _
      _ = ‖σ j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith [hσ j])
  have hr := dpCenteringErrorWeight_smooth hΦ hL (-conj (σ 2)) (-conj (σ 3))
    (by simpa using hσ 2) (by simpa using hσ 3) Complex.reCLM
  have hi := dpCenteringErrorWeight_smooth hΦ hL (-conj (σ 2)) (-conj (σ 3))
    (by simpa using hσ 2) (by simpa using hσ 3) Complex.imCLM
  have hir := chiTwistedFourthIntegrand_integrable hT η (rawMomentShifts T σ)
    _ _ _ hraw (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hr
  have hii := chiTwistedFourthIntegrand_integrable hT η (rawMomentShifts T σ)
    _ _ _ hraw (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hi
  let R : ℝ → ℂ := fun t => chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
    (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.reCLM)
  let J : ℝ → ℂ := fun t => chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
    (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.imCLM)
  have he (t : ℝ) : dpCenteringPairInverseError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
      chiTwistedFourthIntegrand T t (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ =
      (Real.log T : ℂ)⁻¹*(R t-Complex.I*J t) := by
    have hs := congrArg conj (dpCenteringErrorWeight_complex_split T Φ
      (-conj (σ 2)) (-conj (σ 3)) (t/T))
    simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I] at hs
    rw [dpCenteringPairInverseError_eq_conj hL (t/T) (σ 2) (σ 3) (hσ 2) (hσ 3)]
    unfold R J chiTwistedFourthIntegrand
    rw [mul_sub]
    have hh : (Real.log T : ℂ)⁻¹ *
        ((dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.reCLM (t/T) : ℂ)-
          I*(dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.imCLM (t/T) : ℂ)) =
        (Φ (t/T) : ℂ)*conj (dpCenteringPairError T ((t/T : ℝ) : ℂ)
          (-conj (σ 2)) (-conj (σ 3))) := by
      rw [sub_eq_add_neg,← neg_mul,hs]
      field_simp
    linear_combination -(shiftedFourthProduct t (rawMomentShifts T σ)*criticalChi t*
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) (1-criticalLinePoint t)*
      profileDirichletSum T (zeroExtendedPolynomialProfile η P) (1-criticalLinePoint t))*hh
  unfold dpCenteringInverseRemainderMoment
  rw [integral_congr_ae (Filter.Eventually.of_forall he),integral_const_mul,
    integral_sub hir (hii.const_mul Complex.I),integral_const_mul]
  unfold chiTwistedFourthMoment
  ring


theorem dpCenteringInverseRemainderMoment_uniform_bound (hsource : Source.DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K)
    (hsep : ∀ σ ∈ K, Source.DPSeparated σ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpCenteringInverseRemainderMoment T η P σ Φ‖ ≤ C*T*(Real.log T)^8 := by
  obtain ⟨R,hRpos,hRK⟩ := hK.isBounded.exists_pos_norm_le
  have hR : 0 ≤ R := hRpos.le
  have hCen : 0 ≤ centeringUniformConstant R := by
    unfold centeringUniformConstant centeringPhaseComplexBound
    have hp : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  let BW := 15*B*centeringUniformConstant R
  have hBW : 0 ≤ BW := by dsimp [BW]; positivity
  obtain ⟨C,hC,hSource⟩ := Source.dpActualMoment_uniform_smoothing hsource
    η hη hηu P K hK hsep BW hBW
  obtain ⟨D,hD,hRes⟩ := Source.dpNormalizedFourResidues_compact_bound η P K hK hsep
  let RD := ‖(arithmeticFactor : ℂ)‖*|η|^6*D
  have hRD : 0 ≤ RD := by dsimp [RD]; positivity
  let M := C+6*B*centeringUniformConstant R*RD
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨2*M,by positivity,?_⟩
  filter_upwards [hSource, dpCenteringErrorWeight_uniform_deriv_bound hR hB,
    dpCenteringErrorWeight_uniform_norm_bound hR hB, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (max 1 (2*R)))]
    with T hSource hDeriv hNorm hT hLog
  intro σ hσ Φ hΦ hΦB
  have hLp := Real.log_pos hT
  have hL1 : 1 ≤ Real.log T := ((le_max_left _ _).trans_lt hLog).le
  have hσR (j : Fin 4) : ‖σ j‖ ≤ R := (norm_le_pi_norm σ j).trans (hRK σ hσ)
  have hσstrip (j : Fin 4) : 2*‖σ j‖ < Real.log T :=
    (mul_le_mul_of_nonneg_left (hσR j) (by norm_num)).trans_lt
      ((le_max_right _ _).trans_lt hLog)
  have hσR' (j : Fin 4) : ‖-conj (σ j)‖ ≤ R := by simpa using hσR j
  have hσstrip' (j : Fin 4) : 2*‖-conj (σ j)‖ < Real.log T := by simpa using hσstrip j
  have hDensity : ‖Source.dpLeadingDensity T η P σ‖ ≤ RD*(Real.log T)^9 := by
    unfold Source.dpLeadingDensity
    simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
    calc
      _ ≤ |arithmeticFactor| *(Real.log T)^9*|η|^6*D := by
        gcongr
        exact hRes σ hσ 1 (by norm_num)
      _ = _ := by dsimp [RD]; simp only [Complex.norm_real,Real.norm_eq_abs]; ring
  have hL89 : (Real.log T)^8 ≤ (Real.log T)^9 := by
    calc
      _ = (Real.log T)^8*1 := by ring
      _ ≤ (Real.log T)^8*Real.log T := mul_le_mul_of_nonneg_left hL1 (pow_nonneg hLp.le 8)
      _ = _ := (pow_succ (Real.log T) 8).symm
  have hMoment (ℓ : ℂ →L[ℝ] ℝ) (hℓ : ‖ℓ‖ ≤ 1) :
      ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) ℓ)‖ ≤ M*T*(Real.log T)^9 := by
    let W := dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) ℓ
    have hW : SmoothDyadicWeight W := dpCenteringErrorWeight_smooth hΦ hLp
      (-conj (σ 2)) (-conj (σ 3)) (hσstrip' 2) (hσstrip' 3) ℓ
    have hWd : ∀ x, |deriv W x| ≤ BW := by
      intro x
      simpa only [Real.norm_eq_abs] using
        hDeriv Φ hΦ hΦB (-conj (σ 2)) (-conj (σ 3)) (hσR' 2) (hσR' 3) ℓ hℓ x
    have hWn : ‖∫ x : ℝ, (W x : ℂ)‖ ≤ 6*B*centeringUniformConstant R := by
      have hh := smoothDyadicWeight_integral_norm_le W hW
        (hNorm Φ hΦ hΦB (-conj (σ 2)) (-conj (σ 3)) (hσR' 2) (hσR' 3) ℓ hℓ)
      convert hh using 1; ring
    have hb := hSource σ hσ W hW hWd
    calc
      _ ≤ ‖chiTwistedFourthMoment T (rawMomentShifts T σ)
          (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) W-
          (T : ℂ)*(∫ x : ℝ, (W x : ℂ))*Source.dpLeadingDensity T η P σ‖+
          ‖(T : ℂ)*(∫ x : ℝ, (W x : ℂ))*Source.dpLeadingDensity T η P σ‖ :=
        norm_le_norm_sub_add _ _
      _ ≤ C*T*(Real.log T)^8+
          T*(6*B*centeringUniformConstant R)*(RD*(Real.log T)^9) := by
        apply add_le_add hb
        simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (zero_lt_one.trans hT)]
        gcongr
      _ ≤ C*T*(Real.log T)^9+
          T*(6*B*centeringUniformConstant R)*(RD*(Real.log T)^9) := by gcongr
      _ = _ := by dsimp [M]; ring
  rw [dpCenteringInverseRemainderMoment_eq_real_weights hT η P σ Φ hΦ hσstrip,
    norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hLp]
  calc
    _ ≤ (‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.reCLM)‖+
        ‖Complex.I*chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P)
        (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.imCLM)‖)/Real.log T :=
      div_le_div_of_nonneg_right (norm_sub_le _ _) hLp.le
    _ ≤ (M*T*(Real.log T)^9+M*T*(Real.log T)^9)/Real.log T := by
      simp only [norm_mul,Complex.norm_I,one_mul]
      exact div_le_div_of_nonneg_right (add_le_add
        (hMoment Complex.reCLM reCLM_norm_le_one) (hMoment Complex.imCLM imCLM_norm_le_one)) hLp.le
    _ = _ := by field_simp; ring


theorem lowerCenteringFactor_ne_zero_real {T : ℝ} (hL : 0 < Real.log T)
    (x : ℝ) (z : ℂ) (hz : 2*‖z‖ < Real.log T) :
    lowerCenteringFactor T (x : ℂ) z ≠ 0 := by
  have hp : 1-complexHeightPoint T (x : ℂ) = criticalLinePoint (-(T*x)) := by
    unfold complexHeightPoint criticalLinePoint
    push_cast
    ring
  have hw := centeringShift_mem_strip hL (-(T*x)) z hz
  unfold lowerCenteringFactor centeringFactorAt
  rw [hp]
  exact div_ne_zero (mul_ne_zero (Complex.exp_ne_zero _)
    (zetaChi_ne_zero_strip hw.1 hw.2))
    (zetaChi_ne_zero_strip (by norm_num) (by norm_num))

def dpAllPositiveIntegrand (T t : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ) : ℂ :=
  (Φ (t/T) : ℂ)*zetaChi (1-criticalLinePoint t)*
    allPositiveFourthProduct t (rawMomentShifts T σ)*
    profileDirichletSum T f (1-criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)

theorem dpAllPositiveIntegrand_eq_source_and_error {T : ℝ} (hT : 1 < T)
    (t : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ)
    (hσ : ∀ j, 2*‖σ j‖ < Real.log T) :
    dpAllPositiveIntegrand T t σ f g Φ = Complex.exp (σ 2+σ 3)*
      (chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ+
        dpCenteringPairInverseError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
          chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ) := by
  have hL := Real.log_pos hT
  have hT0 : T ≠ 0 := (zero_lt_one.trans hT).ne'
  have hstrip (j : Fin 4) : 0 < (1-criticalLinePoint t+rawMomentShifts T σ j).re ∧
      (1-criticalLinePoint t+rawMomentShifts T σ j).re < 1 := by
    have hh := centeringShift_mem_strip hL (-t) (σ j) (hσ j)
    have he : centeringShift T (-t) (σ j) = 1-criticalLinePoint t+rawMomentShifts T σ j := by
      unfold centeringShift criticalLinePoint rawMomentShifts
      push_cast
      ring
    simpa only [he] using hh
  let C := lowerCenteringFactor T ((t/T : ℝ) : ℂ) (σ 2)*
    lowerCenteringFactor T ((t/T : ℝ) : ℂ) (σ 3)
  have hC0 : C ≠ 0 := mul_ne_zero
    (lowerCenteringFactor_ne_zero_real hL (t/T) (σ 2) (hσ 2))
    (lowerCenteringFactor_ne_zero_real hL (t/T) (σ 3) (hσ 3))
  have hc : Complex.exp (σ 2+σ 3)*dpArchimedeanCorrection t (rawMomentShifts T σ) = C := by
    have hh := dpCenteredArchimedeanCorrection_eq_pair T (t/T) σ
    have ht : T*(t/T)=t := by field_simp
    rw [ht] at hh
    simpa only [dpCenteredArchimedeanCorrection,dpCenteringPairError,C,sub_left_inj] using hh
  have he : Complex.exp (σ 2+σ 3)*
      chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ =
      C*dpAllPositiveIntegrand T t σ f g Φ := by
    rw [chiTwistedFourthIntegrand_functional_equation T t (rawMomentShifts T σ) f g Φ
      (hstrip 2) (hstrip 3)]
    unfold dpAllPositiveIntegrand
    linear_combination ((Φ (t/T) : ℂ)*zetaChi (1-criticalLinePoint t)*
      allPositiveFourthProduct t (rawMomentShifts T σ)*
      profileDirichletSum T f (1-criticalLinePoint t)*
      profileDirichletSum T g (1-criticalLinePoint t))*hc
  change dpAllPositiveIntegrand T t σ f g Φ = Complex.exp (σ 2+σ 3)*
    (chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ+
      (C⁻¹-1)*chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ)
  calc
    _ = C⁻¹*(C*dpAllPositiveIntegrand T t σ f g Φ) := by field_simp
    _ = C⁻¹*(Complex.exp (σ 2+σ 3)*
        chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ) := by rw [← he]
    _ = _ := by ring

private theorem dpCenteringInverseRemainderIntegrand_eq_real_weights {T : ℝ}
    (hL : 0 < Real.log T) (t : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ)
    (hz : 2*‖σ 2‖ < Real.log T) (hw : 2*‖σ 3‖ < Real.log T) :
    dpCenteringPairInverseError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
      chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ =
    (Real.log T : ℂ)⁻¹*(chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g
      (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.reCLM)-
      Complex.I*chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g
      (dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.imCLM)) := by
  have hLc : (Real.log T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hs := congrArg conj (dpCenteringErrorWeight_complex_split T Φ
    (-conj (σ 2)) (-conj (σ 3)) (t/T))
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I] at hs
  rw [dpCenteringPairInverseError_eq_conj hL (t/T) (σ 2) (σ 3) hz hw]
  unfold chiTwistedFourthIntegrand
  rw [mul_sub]
  have hh : (Real.log T : ℂ)⁻¹ *
      ((dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.reCLM (t/T) : ℂ)-
        I*(dpCenteringErrorWeight T Φ (-conj (σ 2)) (-conj (σ 3)) Complex.imCLM (t/T) : ℂ)) =
      (Φ (t/T) : ℂ)*conj (dpCenteringPairError T ((t/T : ℝ) : ℂ)
        (-conj (σ 2)) (-conj (σ 3))) := by
    rw [sub_eq_add_neg,← neg_mul,hs]
    field_simp
  linear_combination -(shiftedFourthProduct t (rawMomentShifts T σ)*criticalChi t*
    profileDirichletSum T f (1-criticalLinePoint t)*profileDirichletSum T g (1-criticalLinePoint t))*hh

theorem dpCenteringInverseRemainderIntegrand_integrable {T : ℝ} (hT : 1 < T)
    (a : ℝ) (σ : MomentShifts) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, a < x → g x=0)
    (hΦ : SmoothDyadicWeight Φ) (hσ : ∀ j, 2*‖σ j‖ < Real.log T) :
    Integrable (fun t : ℝ => dpCenteringPairInverseError T ((t/T : ℝ) : ℂ) (σ 2) (σ 3)*
      chiTwistedFourthIntegrand T t (rawMomentShifts T σ) f g Φ) := by
  have hL := Real.log_pos hT
  have hraw (j : Fin 4) : |(rawMomentShifts T σ j).re| < 1/2 := by
    calc
      _ ≤ ‖rawMomentShifts T σ j‖ := Complex.abs_re_le_norm _
      _ = ‖σ j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith [hσ j])
  have hr := dpCenteringErrorWeight_smooth hΦ hL (-conj (σ 2)) (-conj (σ 3))
    (by simpa using hσ 2) (by simpa using hσ 3) Complex.reCLM
  have hi := dpCenteringErrorWeight_smooth hΦ hL (-conj (σ 2)) (-conj (σ 3))
    (by simpa using hσ 2) (by simpa using hσ 3) Complex.imCLM
  have hir := chiTwistedFourthIntegrand_integrable hT a (rawMomentShifts T σ)
    f g _ hraw hf hg hr
  have hii := chiTwistedFourthIntegrand_integrable hT a (rawMomentShifts T σ)
    f g _ hraw hf hg hi
  have hh := (hir.sub (hii.const_mul Complex.I)).const_mul (Real.log T : ℂ)⁻¹
  exact hh.congr (Filter.Eventually.of_forall (fun t =>
    (dpCenteringInverseRemainderIntegrand_eq_real_weights hL t σ f g Φ (hσ 2) (hσ 3)).symm))

def dpAllPositiveMoment (T η : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (Φ : ℝ → ℝ) : ℂ :=
  ∫ t : ℝ, dpAllPositiveIntegrand T t σ
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ

theorem dpAllPositiveMoment_eq_source_and_error {T : ℝ} (hT : 1 < T)
    (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) (Φ : ℝ → ℝ)
    (hΦ : SmoothDyadicWeight Φ) (hσ : ∀ j, 2*‖σ j‖ < Real.log T) :
    dpAllPositiveMoment T η P σ Φ = Complex.exp (σ 2+σ 3)*
      (chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ+
        dpCenteringInverseRemainderMoment T η P σ Φ) := by
  have hL := Real.log_pos hT
  have hraw (j : Fin 4) : |(rawMomentShifts T σ j).re| < 1/2 := by
    calc
      _ ≤ ‖rawMomentShifts T σ j‖ := Complex.abs_re_le_norm _
      _ = ‖σ j‖/Real.log T := by
        rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL]
      _ < 1/2 := (div_lt_iff₀ hL).mpr (by linarith [hσ j])
  have hir := chiTwistedFourthIntegrand_integrable hT η (rawMomentShifts T σ)
    _ _ Φ hraw (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hΦ
  have hii := dpCenteringInverseRemainderIntegrand_integrable hT η σ _ _ Φ
    (Source.dpProfile_zero_above η P) (Source.dpProfile_zero_above η P) hΦ hσ
  unfold dpAllPositiveMoment chiTwistedFourthMoment dpCenteringInverseRemainderMoment
  rw [← integral_add hir hii,← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t => dpAllPositiveIntegrand_eq_source_and_error hT t σ _ _ Φ hσ)


theorem dpAllPositiveMoment_uniform_smoothing (hsource : Source.DPv2SharpInput)
    (η : ℝ) (hη : 0 < η) (hηu : η < 1/4) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K)
    (hsep : ∀ σ ∈ K, Source.DPSeparated σ) (B : ℝ) (hB : 0 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K,
      ∀ Φ : ℝ → ℝ, SmoothDyadicWeight Φ → WeightSeminormBound 1 B Φ →
      ‖dpAllPositiveMoment T η P σ Φ-Complex.exp (σ 2+σ 3)*
        (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*Source.dpLeadingDensity T η P σ‖ ≤
          C*T*(Real.log T)^8 := by
  obtain ⟨A,hA,hSmooth⟩ := Source.dpActualMoment_uniform_smoothing hsource
    η hη hηu P K hK hsep B hB
  obtain ⟨D,hD,hInv⟩ := dpCenteringInverseRemainderMoment_uniform_bound hsource
    η hη hηu P K hK hsep B hB
  obtain ⟨R,hR,hRK⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨Real.exp (2*R)*(A+D),by positivity,?_⟩
  filter_upwards [hSmooth,hInv,eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (2*R))]
    with T hSmooth hInv hT hL σ hσ Φ hΦ hΦB
  have hσR (j : Fin 4) : ‖σ j‖ ≤ R := (norm_le_pi_norm σ j).trans (hRK σ hσ)
  have hσstrip (j : Fin 4) : 2*‖σ j‖ < Real.log T :=
    (mul_le_mul_of_nonneg_left (hσR j) (by norm_num)).trans_lt hL
  have hder : ∀ x, |deriv Φ x| ≤ B := by intro x; simpa using hΦB 1 (by omega) x
  have hphase : ‖Complex.exp (σ 2+σ 3)‖ ≤ Real.exp (2*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [Complex.add_re]
    have h2 := (le_abs_self (σ 2).re).trans ((Complex.abs_re_le_norm _).trans (hσR 2))
    have h3 := (le_abs_self (σ 3).re).trans ((Complex.abs_re_le_norm _).trans (hσR 3))
    linarith
  rw [dpAllPositiveMoment_eq_source_and_error hT η P σ Φ hΦ hσstrip]
  have he : Complex.exp (σ 2+σ 3)*
      (chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ+
        dpCenteringInverseRemainderMoment T η P σ Φ)-
      Complex.exp (σ 2+σ 3)*(T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*Source.dpLeadingDensity T η P σ =
      Complex.exp (σ 2+σ 3)*
        ((chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
          (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*Source.dpLeadingDensity T η P σ)+
          dpCenteringInverseRemainderMoment T η P σ Φ) := by ring
  rw [he,norm_mul]
  calc
    _ ≤ Real.exp (2*R)*
      (‖chiTwistedFourthMoment T (rawMomentShifts T σ)
        (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η P) Φ-
          (T : ℂ)*(∫ x : ℝ, (Φ x : ℂ))*Source.dpLeadingDensity T η P σ‖+
        ‖dpCenteringInverseRemainderMoment T η P σ Φ‖) := by
      apply mul_le_mul hphase (norm_add_le _ _) (norm_nonneg _)
        (Real.exp_pos _).le
    _ ≤ Real.exp (2*R)*(A*T*(Real.log T)^8+D*T*(Real.log T)^8) :=
      mul_le_mul_of_nonneg_left (add_le_add (hSmooth σ hσ Φ hΦ hder)
        (hInv σ hσ Φ hΦ hΦB)) (Real.exp_pos _).le
    _ = _ := by ring

end
end SixthMoment
