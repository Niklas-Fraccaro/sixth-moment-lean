import Sechstmoment.Numerator.V.Asymptotic.AmplifiedProfileJoin
import Sechstmoment.Numerator.V.Asymptotic.NormalizedPowerErrors
import Sechstmoment.Numerator.V.Asymptotic.SeparatedMainLeading


namespace Sechstmoment.Source
open NoDPGlobalLFactorization NoDPHarmonic Complex Real Set MeasureTheory Polynomial
open scoped BigOperators ContDiff
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def noDPCriticalPolynomialMoment (w : ℝ → ℂ) (T η : ℝ) (P Q : ℝ[X])
    (σ : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ, shiftedChiProfileFactor T (z/(Real.log T:ℂ)) (scaledShifts (Real.log T) σ)
    (zeroExtendedPolynomialProfile η P) (zeroExtendedPolynomialProfile η Q)
    ((1/2:ℂ)+(t:ℂ)*I)*w (t/T)

theorem critical_polynomial_separated_normalized_error {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η R δ ε : ℝ} (hη : 0 < η) (hηu : η < 1/4) (hR : 0 ≤ R)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < 1/2) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 1 < T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R → ∀ z : ℂ, ‖z‖ ≤ R →
      (∀ i j : Fin 4, i ≠ j → δ ≤ ‖σ i-σ j‖) →
      ‖noDPCriticalPolynomialMoment w T η P Q σ z/((T:ℂ)*(Real.log T:ℂ)^9)-
        (2*Real.pi:ℂ)*separatedResidueLeading w η P Q σ z‖ ≤
        C*(T^(1/2+2*η-1:ℝ)+T^(1/2+2*η+ε-1:ℝ)+1/Real.log T) := by
  classical
  obtain ⟨Cχ,hCχ,Hχ⟩ := polynomial_shiftedChi_additive_reduction hw hws hη hηu.le R hR P Q
  obtain ⟨Cp,hCp,Up,hUp,HP⟩ := profileChi_original_main_power_saving
    hw hws hR ε η hε hεu hηu.le
  obtain ⟨Cm,hCm,HM⟩ := separated_profile_main_normalized_error hw.continuous hws hη hR hδ P Q
  obtain ⟨Bp,hBp,HBp⟩ := polynomialProfile_global_norm_bound hη P
  obtain ⟨Bq,hBq,HBq⟩ := polynomialProfile_global_norm_bound hη Q
  let B := Bp+Bq
  let A2 := (2*Real.pi)*Cp*B^2
  let A3 := (2*Real.pi)*Cm
  let C := Cχ+A2+A3+1
  let Dlog := max (4*(2*R+2))
    (max 1 (max ((2*R)*(elementaryPhaseLogBound+1)) (16*R)))
  let U := max Up (max (max 80 (100*Real.pi)) (Real.exp Dlog))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hA2 : 0 ≤ A2 := by dsimp only [A2]; positivity
  have hA3 : 0 ≤ A3 := by dsimp only [A3]; positivity
  have hU : 1 < U := hUp.trans_le (le_max_left _ _)
  refine ⟨C,by dsimp only [C]; positivity,U,hU,?_⟩
  intro T hTU σ hσ z hz hgap
  have hT1 : 1 < T := hU.trans_le hTU
  have hT0 : 0 < T := zero_lt_one.trans hT1
  have hTp : Up ≤ T := (le_max_left _ _).trans hTU
  have hTχ : max 80 (100*Real.pi) ≤ T :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hTU)
  have hTexp : Real.exp Dlog ≤ T :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hTU)
  have hlog : Dlog ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos Dlog) hTexp
  have hlogχ : 4*(2*R+2) ≤ Real.log T := (le_max_left _ _).trans hlog
  have hlogM : max 1 (max ((2*R)*(elementaryPhaseLogBound+1)) (16*R)) ≤ Real.log T :=
    (le_max_right _ _).trans hlog
  let L := Real.log T
  let β := scaledShifts L σ
  let u := z/(L:ℂ)
  let Y := ⌊T^η⌋₊^2
  let f : ℝ → ℂ := fun x => (zeroExtendedPolynomialProfile η P x:ℂ)
  let g : ℝ → ℂ := fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)
  let D : ℂ := (T:ℂ)*(L:ℂ)^9
  let Iχ := noDPCriticalPolynomialMoment w T η P Q σ z
  let A := profileChiAdditiveActual w T u f g L Y β
  let M := profileAdditiveOriginalMain f g L Y (noDPTimeWeight w T u) β (T/(2*Real.pi))
  let K := separatedResidueLeading w η P Q σ z
  let a : ℝ := 1/2+2*η
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlogM
  have hL0 : 0 < L := by linarith
  have hLC : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0.ne'
  have hD : ‖D‖ = T*L^9 := norm_time_log_denominator hT0 hL0 9
  have hDpos : 0 < T*L^9 := by positivity
  have hπ : 0 ≤ 2*Real.pi := by positivity
  have hπnorm : ‖(2*Real.pi:ℂ)‖ = 2*Real.pi := by simp
  have hσi (i : Fin 4) : ‖σ i‖ ≤ R := (norm_le_pi_norm σ i).trans hσ
  have hu : ‖u‖ ≤ R/L := by
    dsimp only [u]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    exact div_le_div_of_nonneg_right hz hL0.le
  have hβ (i : Fin 4) : ‖β i‖ ≤ R/L := by
    dsimp only [β,scaledShifts]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
    exact div_le_div_of_nonneg_right (hσi i) hL0.le
  have hσinj : Function.Injective σ := by
    intro i j he
    by_contra hij
    have H := hgap i j hij
    rw [he,sub_self,norm_zero] at H
    linarith
  have hβinj : Function.Injective β := by
    intro i j he
    apply hσinj
    have H := congrArg (fun v : ℂ => v*(L:ℂ)) he
    simpa [β,scaledShifts,hLC] using H
  have hY : Y ≠ 0 := pow_ne_zero 2
    (Nat.ne_of_gt (Nat.floor_pos.mpr (Real.one_le_rpow hT1.le hη.le)))
  have hYlen : (Y:ℝ) ≤ T^(2*η) := by
    dsimp only [Y]
    rw [Nat.cast_pow]
    calc
      _ ≤ (T^η)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _)
        (Nat.floor_le (Real.rpow_nonneg hT0.le η)) 2
      _ = _ := by rw [pow_two,← Real.rpow_add hT0]; congr 1; ring
  have hf (x : ℝ) : ‖f x‖ ≤ B := (HBp x).trans (by dsimp only [B]; linarith)
  have hg (x : ℝ) : ‖g x‖ ≤ B := (HBq x).trans (by dsimp only [B]; linarith)
  have Hχraw := Hχ T hTχ hlogχ u hu β hβ
  rw [amplifiedAdditiveMain_eq_profileChi hT1 w η P Q u β] at Hχraw
  have Hχ' : ‖Iχ-(2*Real.pi:ℂ)*A‖ ≤ Cχ*T^a*L^4 := Hχraw
  have HPraw : ‖A-M‖ ≤ Cp*B^2*T^(a+ε) :=
    HP T hTp z hz Y hY hYlen f g B hB hf hg β hβinj hβ
  have HMraw : ‖M/D-K‖ ≤ Cm/L := HM T hT0 hlogM σ hσ z hz hgap
  have H1 : ‖(Iχ-(2*Real.pi:ℂ)*A)/D‖ ≤ Cχ*T^(a-1) := by
    rw [norm_div,hD]
    exact (div_le_div_of_nonneg_right Hχ' hDpos.le).trans
      (normalized_power_log_error hT0 hL1 hCχ.le)
  have H2 : ‖((2*Real.pi:ℂ)*(A-M))/D‖ ≤ A2*T^(a+ε-1) := by
    rw [norm_div,norm_mul,hπnorm,hD]
    have Hmul : (2*Real.pi)*‖A-M‖ ≤ A2*T^(a+ε) := by
      exact (mul_le_mul_of_nonneg_left HPraw hπ).trans_eq (by dsimp only [A2]; ring)
    exact (div_le_div_of_nonneg_right Hmul hDpos.le).trans
      (normalized_power_error hT0 hL1 hA2)
  have H3 : ‖(2*Real.pi:ℂ)*(M/D-K)‖ ≤ A3/L := by
    rw [norm_mul,hπnorm]
    exact (mul_le_mul_of_nonneg_left HMraw hπ).trans_eq (by dsimp only [A3]; ring)
  have hid : Iχ/D-(2*Real.pi:ℂ)*K =
      (Iχ-(2*Real.pi:ℂ)*A)/D+((2*Real.pi:ℂ)*(A-M))/D+
        (2*Real.pi:ℂ)*(M/D-K) := by ring
  change ‖Iχ/D-(2*Real.pi:ℂ)*K‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖(Iχ-(2*Real.pi:ℂ)*A)/D‖+‖((2*Real.pi:ℂ)*(A-M))/D‖+
        ‖(2*Real.pi:ℂ)*(M/D-K)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ Cχ*T^(a-1)+A2*T^(a+ε-1)+A3/L := add_le_add (add_le_add H1 H2) H3
    _ = Cχ*T^(a-1)+A2*T^(a+ε-1)+A3*(1/L) := by ring
    _ ≤ C*T^(a-1)+C*T^(a+ε-1)+C*(1/L) := by
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (by positivity)
        · exact mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (by positivity)
      · exact mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (by positivity)
    _ = _ := by ring

end
end Sechstmoment.Source
