import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.ResidualAggregate

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeVerticalIntegral_const_mul (c : ℝ) (C : ℂ) (F : ℂ→ℂ) :
    verticalIntegral c (fun s => C*F s)=C*verticalIntegral c F := by
  unfold verticalIntegral
  rw [integral_const_mul]
  ring

private theorem a03ZeroModeVerticalIntegral_square_height_bound (c : ℝ) (F : ℂ→ℂ)
    (hMeas : Measurable (fun y : ℝ => F ((c:ℂ)+(y:ℂ)*I)))
    {Q : ℝ} (_hQ : 0≤Q) (hb : ∀ y : ℝ,(1+|y|)^2*‖F ((c:ℂ)+(y:ℂ)*I)‖≤Q) :
    Integrable (fun y : ℝ => F ((c:ℂ)+(y:ℂ)*I)) ∧ ‖verticalIntegral c F‖≤Q/2 := by
  have hpoint (y : ℝ) : ‖F ((c:ℂ)+(y:ℂ)*I)‖≤Q*(1+y^2)⁻¹ := by
    have hp : 1+y^2≤(1+|y|)^2 := by nlinarith [sq_abs y,abs_nonneg y]
    have hmul : ‖F ((c:ℂ)+(y:ℂ)*I)‖*(1+y^2)≤Q :=
      ((mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_comm _ _)).trans (hb y)
    simpa only [div_eq_mul_inv] using (le_div_iff₀ (by positivity : 0<1+y^2)).mpr hmul
  have hi := (integrable_inv_one_add_sq.const_mul Q).mono' hMeas.aestronglyMeasurable (ae_of_all _ hpoint)
  refine ⟨hi,?_⟩
  have hn := norm_integral_le_of_norm_le (f := fun y : ℝ => F ((c:ℂ)+(y:ℂ)*I))
    (integrable_inv_one_add_sq.const_mul Q) (ae_of_all _ hpoint)
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hn
  unfold verticalIntegral
  rw [norm_mul]
  have hc : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hc]
  exact (mul_le_mul_of_nonneg_left hn (by positivity)).trans_eq (by field_simp)

theorem a03ZeroModeGCDEtaResidual_chambers_uniform_vertical_bound
    (K : Set MomentShifts) (hK : IsCompact K) {κ η : ℝ}
    (hκ : 0<κ) (hη : 0<η) (hη1 : η≤1/16)
    (hroot : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ dual m n : Bool,
      ∀ g a b : ℕ,0<g → 0<a → 0<b → ∀ A B : ℕ→ℂ,
        let α := rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ)
        Integrable (fun y : ℝ => a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B
          (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)) ∧
        ‖(T:ℂ)*verticalIntegral (1+η/4) (a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B)‖≤
          C*(Real.log T)^56*‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*
            a03ZeroModeRatioPrimitiveResidualPower g a b η := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeGCDEtaResidualX_chambers_uniform_integrated_bound K hK hκ hη hη1 hroot hΦ hSupp
  refine ⟨D/2,by positivity,?_⟩
  filter_upwards [hbnd,eventually_gt_atTop (1:ℝ)] with T hbnd hT
  intro σ hσ dual m n g a b hg ha hb A B
  let α := rawMomentShifts T (Sechstmoment.a03SourceNormalizedChamber dual m n σ)
  let F : ℂ→ℂ := fun s => (T:ℂ)*a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B s
  let Q : ℝ := D*(Real.log T)^56*‖A (g*a)‖*‖B (g*b)‖*T^(1/2+η)*
    a03ZeroModeRatioPrimitiveResidualPower g a b η
  have hp : 0≤a03ZeroModeRatioPrimitiveResidualPower g a b η := by
    unfold a03ZeroModeRatioPrimitiveResidualPower
    positivity
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hFm : Measurable (fun y : ℝ => F (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)) :=
    measurable_const.mul (a03ZeroModeGCDEtaResidualX_measurable_height hΦ hSupp
      (zero_lt_one.trans hT) (by linarith : 0<1+η/4) σ (η/4) α hg ha hb A B)
  have hFb (y : ℝ) : (1+|y|)^2*‖F (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)‖≤Q := by
    have hh := (hbnd σ hσ dual m n g a b hg ha hb A B (((1+η/4:ℝ):ℂ)+(y:ℂ)*I) (by simp)).2
    simp only [add_im,ofReal_im,mul_I_im,ofReal_re,zero_add] at hh
    dsimp [F,Q]
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (zero_lt_one.trans hT).le]
    convert hh using 1
    ring
  obtain ⟨hFi,hFn⟩ := a03ZeroModeVerticalIntegral_square_height_bound (1+η/4) F hFm hQ hFb
  have hTi : IsUnit (T:ℂ) := isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hT).ne')
  have hRi : Integrable (fun y : ℝ => a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B
      (((1+η/4:ℝ):ℂ)+(y:ℂ)*I)) := (integrable_const_mul_iff hTi _).mp hFi
  refine ⟨hRi,?_⟩
  change ‖verticalIntegral (1+η/4) (fun s => (T:ℂ)*a03ZeroModeGCDEtaResidualX Φ T σ (η/4) α g a b A B s)‖≤Q/2 at hFn
  rw [a03ZeroModeVerticalIntegral_const_mul] at hFn
  exact hFn.trans_eq (by dsimp [Q]; ring)

end
end Sechstmoment.Source
