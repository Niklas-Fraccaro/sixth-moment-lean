import SixthMoment.Numerator.V.Asymptotic.CriticalCollision
import SixthMoment.Numerator.V.Asymptotic.VSingleChi
import SixthMoment.Numerator.V.ReflectedKernel


namespace SixthMoment.Source
open Complex Real Set MeasureTheory Filter NoDPHarmonic
open scoped BigOperators Topology ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem polarGeneralBilinearGeneratorContour_last_swap (η : ℝ)
    (P Q : Polynomial ℝ) (z : ℂ) (innerR outerR : ℝ) :
    polarGeneralBilinearGeneratorContour η P Q ![0,0,0,z] innerR outerR =
      polarGeneralBilinearGeneratorContour η P Q ![0,0,z,0] innerR outerR := by
  have hd (u : ℂ) : (∏ j : Fin 4, (u-(![0,0,0,z] : Fin 4 → ℂ) j)) =
      ∏ j : Fin 4, (u-(![0,0,z,0] : Fin 4 → ℂ) j) := by
    simp [Fin.prod_univ_succ,mul_comm]
  have hInverse : ∀ (x : ℝ) (v : ℂ), polarGeneralInverseContour x v ![0,0,0,z] innerR =
      polarGeneralInverseContour x v ![0,0,z,0] innerR := by
    intro x v
    unfold polarGeneralInverseContour
    simp_rw [hd]
  have hp (S : Polynomial ℝ) (v : ℂ) : polarGeneralProfile η S ![0,0,0,z] innerR v =
      polarGeneralProfile η S ![0,0,z,0] innerR v := by
    unfold polarGeneralProfile
    simp_rw [hInverse]
  unfold polarGeneralBilinearGeneratorContour
  simp_rw [hd,hp]
  simp

theorem polarGeneralBilinearGeneratorContour_V_coincident (η : ℝ)
    (P Q : Polynomial ℝ) (z : ℂ) (hz : ‖z‖ < 16) :
    polarGeneralBilinearGeneratorContour η P Q ![0,0,0,z] 16 16 =
      Complex.exp (-z)*polarPolynomialBilinearJ η P Q (-z) := by
  rw [polarGeneralBilinearGeneratorContour_last_swap]
  have hR : ∀ j : Fin 4, ‖(![0,0,z,0] : Fin 4 → ℂ) j‖ < 16 := by
    intro j
    fin_cases j <;> simp [hz]
  have hp := polarGeneralGeneratorContour_coincident η (P+Q) (-z) 16 16
    (by simpa only [norm_neg] using hz) (by simpa only [norm_neg] using hz)
  have hm := polarGeneralGeneratorContour_coincident η (P-Q) (-z) 16 16
    (by simpa only [norm_neg] using hz) (by simpa only [norm_neg] using hz)
  simp only [neg_neg] at hp hm
  rw [polarGeneralBilinearGeneratorContour_polarization η P Q _ 16 16 hR hR,
    hp,hm,polarPolynomialBilinearJ_polarization]
  ring

theorem noDPVSingleChiShifts_mem_polydisc (z : ℂ) (hz : ‖z‖ ≤ 4) :
    noDPVSingleChiShifts z ∈ rectangularClosedPolydisc dpCauchyRadii := by
  intro j
  fin_cases j <;> simp [noDPVSingleChiShifts,dpCauchyRadii]
  linarith

theorem noDPRegularMomentLeading_V (w : ℝ → ℂ) (η : ℝ)
    (P Q : Polynomial ℝ) (z : ℂ) (hz : ‖z‖ < 16) :
    Complex.exp (z/2)*noDPRegularMomentLeading w η P Q (noDPVSingleChiShifts z) z =
      (arithmeticFactor:ℂ)*(∫ x : ℝ, w x)*vReflectedPolynomialJ η P Q z := by
  have hq : (fun j => -(noDPVSingleChiShifts z j)) = (![0,0,0,z] : Fin 4 → ℂ) := by
    funext j
    fin_cases j <;> simp [noDPVSingleChiShifts]
  have he : Complex.exp (z/2)*Complex.exp (-z) = Complex.exp (-z/2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  unfold noDPRegularMomentLeading vReflectedPolynomialJ
  rw [hq,polarGeneralBilinearGeneratorContour_V_coincident η P Q z hz]
  have hs : -(noDPVSingleChiShifts z 2)-noDPVSingleChiShifts z 3-z = 0 := by
    simp [noDPVSingleChiShifts]
  rw [hs,Complex.exp_zero,mul_one]
  calc
    _ = (arithmeticFactor:ℂ)*(∫ x : ℝ, w x)*
        (Complex.exp (z/2)*Complex.exp (-z))*polarPolynomialBilinearJ η P Q (-z) := by ring
    _ = _ := by rw [he]; ring

theorem vPolynomialMixedGenerator_eq_noDPCriticalMoment (T η : ℝ)
    (P Q : Polynomial ℝ) (Φ : ℝ → ℝ) (z : ℂ)
    (hu : ‖z/(Real.log T:ℂ)‖ ≤ 1/8) :
    vPolynomialMixedGenerator T (zeroExtendedPolynomialProfile η P)
      (zeroExtendedPolynomialProfile η Q) Φ z =
      Complex.exp (z/2)*noDPCriticalPolynomialMoment (fun x => (Φ x:ℂ))
        T η P Q (noDPVSingleChiShifts z) z := by
  have hβ : scaledShifts (Real.log T) (noDPVSingleChiShifts z) =
      noDPVSingleChiShifts (z/(Real.log T:ℂ)) := by
    funext j
    fin_cases j <;> simp [scaledShifts,noDPVSingleChiShifts,neg_div]
  rw [vPolynomialMixedGenerator_single_chi T _ _ Φ z hu]
  unfold noDPCriticalPolynomialMoment
  rw [hβ]
  simp only [criticalLinePoint]

theorem noDP_vPolynomialMixedGenerator_uniform_tendsto
    {η : ℝ} (hη : 0 < η) (hηu : η < 1/4) (P Q : Polynomial ℝ)
    (Φ : ℝ → ℝ) (hΦ : SmoothDyadicWeight Φ) :
    ∀ r : ℝ, 0 < r → ∀ᶠ T : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ 4 →
      ‖vPolynomialMixedGenerator T (zeroExtendedPolynomialProfile η P)
        (zeroExtendedPolynomialProfile η Q) Φ z/((T:ℂ)*(Real.log T:ℂ)^9)-
        (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*vReflectedPolynomialJ η P Q z‖ < r := by
  have hΦc : ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ.1
  have hΦs : tsupport (fun x => (Φ x:ℂ)) ⊆ Icc (1:ℝ) 2 :=
    (tsupport_comp_subset Complex.ofReal_zero Φ).trans hΦ.2
  intro r hr
  have he : 0 < Real.exp 2 := Real.exp_pos 2
  filter_upwards [critical_polynomial_collision_uniform_tendsto hΦc hΦs hη hηu P Q
    (r/Real.exp 2) (div_pos hr he),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (32:ℝ))] with T hT hL
  intro z hz
  have hL0 : 0 < Real.log T := by linarith
  have hu : ‖z/(Real.log T:ℂ)‖ ≤ 1/8 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    apply (div_le_iff₀ hL0).mpr
    linarith
  have hphase : ‖Complex.exp (z/2)‖ ≤ Real.exp 2 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hh : (z/2).re ≤ ‖z/2‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
    have hn : ‖z/2‖ = ‖z‖/2 := by simp
    rw [hn] at hh
    linarith
  have hb := hT (noDPVSingleChiShifts z) (noDPVSingleChiShifts_mem_polydisc z hz) z
    (by linarith : ‖z‖ ≤ 8)
  have hmain := noDPRegularMomentLeading_V (fun x => (Φ x:ℂ)) η P Q z (by linarith)
  have hid : vPolynomialMixedGenerator T (zeroExtendedPolynomialProfile η P)
        (zeroExtendedPolynomialProfile η Q) Φ z/((T:ℂ)*(Real.log T:ℂ)^9)-
        (arithmeticFactor:ℂ)*(∫ x : ℝ, (Φ x:ℂ))*vReflectedPolynomialJ η P Q z =
      Complex.exp (z/2)*(noDPCriticalPolynomialMoment (fun x => (Φ x:ℂ))
        T η P Q (noDPVSingleChiShifts z) z/((T:ℂ)*(Real.log T:ℂ)^9)-
        noDPRegularMomentLeading (fun x => (Φ x:ℂ)) η P Q (noDPVSingleChiShifts z) z) := by
    rw [vPolynomialMixedGenerator_eq_noDPCriticalMoment T η P Q Φ z hu,← hmain]
    ring
  rw [hid,norm_mul]
  calc
    _ ≤ Real.exp 2*‖noDPCriticalPolynomialMoment (fun x => (Φ x:ℂ))
        T η P Q (noDPVSingleChiShifts z) z/((T:ℂ)*(Real.log T:ℂ)^9)-
        noDPRegularMomentLeading (fun x => (Φ x:ℂ)) η P Q (noDPVSingleChiShifts z) z‖ :=
      mul_le_mul_of_nonneg_right hphase (norm_nonneg _)
    _ < Real.exp 2*(r/Real.exp 2) := mul_lt_mul_of_pos_left hb he
    _ = r := by field_simp

end
end SixthMoment.Source
