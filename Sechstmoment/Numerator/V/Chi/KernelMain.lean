import Sechstmoment.Analysis.Mellin.FourierApproximation
import Sechstmoment.Numerator.V.Chi.LogBandCosine


namespace Sechstmoment.Source
open Complex Real Set MeasureTheory
open scoped FourierTransform
noncomputable section

theorem noDPFourierCutoff_inverse_first_error (h : SchwartzMap ℝ ℂ)
    {T : ℝ} (hT : 0 < T) (x : ℝ) :
    ‖𝓕⁻ (noDPFourierCutoff h (T/(100*Real.pi))) x-𝓕⁻ (h:ℝ → ℂ) x‖ ≤
      (100*Real.pi/T)*(∫ ξ : ℝ, |ξ| * ‖h ξ‖) := by
  have hH : 0 < T/(100*Real.pi) := by positivity
  have H := noDPFourierCutoff_inverse_error h hH 1 x
  simp only [pow_one] at H
  apply (mul_le_mul_iff_of_pos_left hH).mp
  apply H.trans_eq
  field_simp [hT.ne',Real.pi_ne_zero]

theorem noDPChiBandTransform_main_error (h : SchwartzMap ℝ ℂ)
    (hs : tsupport (𝓕⁻ (h:ℝ → ℂ)) ⊆ Icc (1:ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ c : ℝ, 0 < c → |c| ≤ 2 →
      ∀ r : ℝ, 0 < r →
      ‖noDPChiBandTransform h T c r-
        Complex.exp (I*((-2*Real.pi*r:ℝ):ℂ))*𝓕⁻ (h:ℝ → ℂ) (2*Real.pi*r/T)‖ ≤
        C*(1/T+r/T^2) := by
  let J1 := ∫ ξ : ℝ, |ξ| * ‖h ξ‖
  let J2 := ∫ ξ : ℝ, |ξ|^2*‖h ξ‖
  have hJ1 : 0 ≤ J1 := integral_nonneg (fun _ => by positivity)
  have hJ2 : 0 ≤ J2 := integral_nonneg (fun _ => by positivity)
  let A1 := 216*Real.pi*J1
  let A2 := 16*Real.pi^3*J2
  have hA1 : 0 ≤ A1 := by dsimp only [A1]; positivity
  have hA2 : 0 ≤ A2 := by dsimp only [A2]; positivity
  let C := A1+A2+1
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro T hT c hc hc' r hr
  let H := T/(100*Real.pi)
  let q := 2*Real.pi*r
  let x := 2*Real.pi*r/T
  let ψ : ℝ → ℂ := 𝓕⁻ (h:ℝ → ℂ)
  let ψH : ℝ → ℂ := 𝓕⁻ (noDPFourierCutoff h H)
  let B : ℝ → ℂ := fun a => ∫ ξ : ℝ,
    noDPBandPhaseIntegrand h H a c (-2*Real.pi/T) ξ
  let L : ℝ → ℂ := fun a => ∫ ξ : ℝ,
    noDPBandLinearIntegrand h H a (-2*Real.pi/T) ξ
  let E := (8*Real.pi/T)*J1+(q*(2*Real.pi/T)^2)*J2
  let D := (100*Real.pi/T)*J1
  have hq : 0 < q := by dsimp only [q]; positivity
  have hx : 0 < x := by dsimp only [x]; positivity
  have hphase (a : ℝ) : ‖Complex.exp (I*(a:ℂ))‖ = 1 := by simp [Complex.norm_exp]
  have hdelta (y : ℝ) : ‖ψH y-ψ y‖ ≤ D :=
    noDPFourierCutoff_inverse_first_error h hT y
  have hzero : ψ (-x) = 0 := by
    apply Function.notMem_support.mp
    intro hm
    have Hsupp := hs (subset_tsupport _ hm)
    linarith [Hsupp.1]
  have hbplus : ‖B q-L q‖ ≤ E := by
    simpa only [abs_of_pos hq] using noDPBandPhase_time_scale_error h hT q c hc'
  have hbminus : ‖B (-q)-L (-q)‖ ≤ E := by
    simpa only [abs_neg,abs_of_pos hq] using noDPBandPhase_time_scale_error h hT (-q) c hc'
  have hlinplus : L q = Complex.exp (I*(q:ℂ))*ψH (-x) := by
    have he : q*(-2*Real.pi/T)/(2*Real.pi) = -x := by
      dsimp only [q,x]
      field_simp [hT.ne',Real.pi_ne_zero]
    dsimp only [L]
    rw [noDPBandLinear_integral,he]
  have hlinminus : L (-q) = Complex.exp (I*((-q:ℝ):ℂ))*ψH x := by
    have he : (-q)*(-2*Real.pi/T)/(2*Real.pi) = x := by
      dsimp only [q,x]
      field_simp [hT.ne',Real.pi_ne_zero]
    dsimp only [L]
    rw [noDPBandLinear_integral,he]
  have htransform : noDPChiBandTransform h T c r = B q+B (-q) := by
    rw [noDPChiBandTransform_eq_bands h hT hc hr,
      show -2*Real.pi*r = -(2*Real.pi*r) by ring]
  have hnonlin : ‖noDPChiBandTransform h T c r-(L q+L (-q))‖ ≤ 2*E := by
    rw [htransform,show B q+B (-q)-(L q+L (-q)) = (B q-L q)+(B (-q)-L (-q)) by ring]
    apply (norm_add_le _ _).trans
    linarith
  have hlinear : ‖L q+L (-q)-Complex.exp (I*((-q:ℝ):ℂ))*ψ x‖ ≤ 2*D := by
    rw [hlinplus,hlinminus]
    have he : Complex.exp (I*(q:ℂ))*ψH (-x)+Complex.exp (I*((-q:ℝ):ℂ))*ψH x-
        Complex.exp (I*((-q:ℝ):ℂ))*ψ x =
        Complex.exp (I*(q:ℂ))*(ψH (-x)-ψ (-x))+
          Complex.exp (I*((-q:ℝ):ℂ))*(ψH x-ψ x) := by rw [hzero]; ring
    rw [he]
    apply (norm_add_le _ _).trans
    rw [norm_mul,norm_mul,hphase,hphase,one_mul,one_mul]
    linarith [hdelta (-x),hdelta x]
  have herr : ‖noDPChiBandTransform h T c r-Complex.exp (I*((-q:ℝ):ℂ))*ψ x‖ ≤ 2*E+2*D := by
    exact (norm_sub_le_norm_sub_add_norm_sub _ (L q+L (-q)) _).trans
      (add_le_add hnonlin hlinear)
  rw [show -2*Real.pi*r = -(2*Real.pi*r) by ring]
  apply herr.trans
  calc
    _ = A1*(1/T)+A2*(r/T^2) := by
      dsimp only [E,D,A1,A2,q]
      field_simp [hT.ne']
      ring
    _ ≤ C*(1/T)+C*(r/T^2) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp only [C]
        linarith
      · apply mul_le_mul_of_nonneg_right _ (by positivity)
        dsimp only [C]
        linarith
    _ = _ := by ring

end
end Sechstmoment.Source
