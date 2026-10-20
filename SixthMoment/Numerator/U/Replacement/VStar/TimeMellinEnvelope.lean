import SixthMoment.Numerator.U.Replacement.VStar.TimeMellinRepresentation

namespace SixthMoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 700000

theorem a03VStarSmoothedTimeMellin_full_height_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) (cs : ℝ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,∀ Y x : ℝ,0<Y → 0<x →
      ∀ s : ℂ,s.re=cs →
      (1+|s.im|)^N*‖a03VStarSmoothedTimeMellin Φ T σ Y x s‖≤
        C*(1+polarGaussianConstant T σ 1)*a03ZeroModeRatioXEnvelope Y x := by
  obtain ⟨Cp,hCp,hpos⟩ := a03GaussianPositiveTimeMellinIntegral_full_height_decay hΦ hSupp (3-cs) 2 N
  obtain ⟨Cn,hCn,hneg⟩ := a03GaussianPositiveTimeMellinIntegral_full_height_decay hΦ hSupp (-1-cs) (-2) N
  obtain ⟨C₀,hC₀,hplain⟩ := a03PositiveTimeMellin_full_height_decay hΦ hSupp (1-cs) N
  let P : ℝ := (2*Real.pi)^2
  have hP : 0<P := by dsimp [P]; positivity
  let C : ℝ := C₀+P*Cn+Cp/P
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T σ Y x hY hx s hsc
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hheight : 0≤(1+|s.im|)^N := by positivity
  have hbase : 0<(2*Real.pi)^2*x^2/Y^2 := by positivity
  have hexp : Real.exp (a03VStarSpatialLog Y x)=P*(x/Y)^2 := by
    unfold a03VStarSpatialLog
    rw [Real.exp_log hbase]
    dsimp only [P]
    ring
  have hplainarg : (1:ℂ)-s=((1-cs:ℝ):ℂ)+((-s.im:ℝ):ℂ)*I := by
    apply Complex.ext <;> simp [hsc]
  have hpl := hplain (-s.im)
  have hn := hneg T σ (-a03VStarSpatialLog Y x) (-s.im)
  have hp := hpos T σ (a03VStarSpatialLog Y x) (-s.im)
  simp only [abs_neg,neg_neg] at hpl hn hp
  by_cases hxy : x≤Y
  · rw [a03ZeroModeRatioXEnvelope_near hx hxy,mul_one]
    have he : Real.exp (a03VStarSpatialLog Y x)≤P := by
      rw [hexp]
      have hd : 0≤x/Y := div_nonneg hx.le hY.le
      have hd1 : x/Y≤1 := (div_le_iff₀ hY).mpr (by simpa using hxy)
      have hs : (x/Y)^2≤1 := by nlinarith only [hd,hd1]
      exact (mul_le_mul_of_nonneg_left hs hP.le).trans_eq (mul_one _)
    rw [a03VStarSmoothedTimeMellin_eq_reflected hΦ.continuous hSupp hY hx T σ s]
    calc
      _≤(1+|s.im|)^N*(‖mellin Φ (1-s)‖+
        ‖a03GaussianPositiveTimeMellinIntegral Φ T σ (-a03VStarSpatialLog Y x) (-1-s.re) (-2) (-s.im)‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) hheight
      _≤C₀+Cn*polarGaussianConstant T σ 1*P := by
        rw [mul_add,hsc]
        exact add_le_add (by simpa only [hplainarg] using hpl) (hn.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hCn hCG)))
      _≤_ := by dsimp only [C]; nlinarith only [hC₀,hCn,hCp,hCG,hP,div_nonneg hCp hP.le]
  · have hxy' : Y<x := lt_of_not_ge hxy
    rw [a03ZeroModeRatioXEnvelope_far hY.le hxy']
    have he : Real.exp (-a03VStarSpatialLog Y x)=(Y/x)^2/P := by
      rw [Real.exp_neg,hexp]
      dsimp only [P]
      field_simp
    rw [a03VStarSmoothedTimeMellin_eq_positive hΦ.continuous hSupp hY hx T σ s,hsc]
    calc
      _≤Cp*polarGaussianConstant T σ 1*Real.exp (-a03VStarSpatialLog Y x) := hp
      _=(Cp/P)*polarGaussianConstant T σ 1*(Y/x)^2 := by rw [he]; ring
      _≤_ := by
        have hcoef : Cp/P≤C := by dsimp only [C]; linarith only [hC₀,mul_nonneg hP.le hCn]
        have hh : (Cp/P)*polarGaussianConstant T σ 1≤C*(1+polarGaussianConstant T σ 1) := by
          exact (mul_le_mul_of_nonneg_right hcoef hCG).trans
            (mul_le_mul_of_nonneg_left (by linarith only [] : polarGaussianConstant T σ 1≤1+polarGaussianConstant T σ 1) hC)
        exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)

end
end SixthMoment
