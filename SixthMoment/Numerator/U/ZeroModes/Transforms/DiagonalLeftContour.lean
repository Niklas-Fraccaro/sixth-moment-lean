import SixthMoment.Numerator.U.Replacement.CentralContourShift
import SixthMoment.Numerator.U.ZeroModes.Transforms.DiagonalLeftBounds


namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03Diagonal_endpoint_off_roots {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {c : ℝ} (hc : c= -(1/8:ℝ) ∨ c=1) (v : ℝ) :
    ∀ ij : Fin 2 × Fin 2,(c:ℂ)+(v:ℂ)*I≠purePolarRoot T σ (m,ij) := by
  intro ij he
  have hb := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans
    (purePolarRoot_norm_le_of_rawShifts hα (m,ij))
  rw [←he] at hb
  simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
    sub_zero,add_zero] at hb
  rcases hc with rfl|rfl <;> norm_num at hb

theorem a03DiagonalRemoved_line_continuous {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {t c : ℝ} (ht : 0<t)
    (hc : c= -(1/8:ℝ) ∨ c=1) :
    Continuous (fun v : ℝ => a03DiagonalRemovedNumerator T σ m a b t
      ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) := by
  have hcont := (a03DiagonalRemovedNumerator_differentiableOn σ hα m ha hb ht).continuousOn
  have hz : Continuous (fun v : ℝ => (c:ℂ)+(v:ℂ)*I) := by fun_prop
  apply (hcont.comp_continuous hz (fun v => ?_)).div hz (fun v => ?_)
  · change -(9/64:ℝ)<((c:ℂ)+(v:ℂ)*I).re
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
    rcases hc with rfl|rfl <;> norm_num
  · intro he
    have hr := congrArg Complex.re he
    simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,
      sub_zero,add_zero,zero_re] at hr
    rcases hc with rfl|rfl <;> norm_num at hr

theorem a03DiagonalRemoved_endpoint_integrable {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {t c : ℝ} (ht : 0<t)
    (hρ : ∀ ij : Fin 2 × Fin 2,purePolarRoot T σ (m,ij)≠0)
    (hc : c= -(1/8:ℝ) ∨ c=1) :
    Integrable (fun v : ℝ => a03DiagonalRemovedNumerator T σ m a b t
      ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)) := by
  obtain ⟨C,_hC,hbound⟩ := a03DiagonalEulerKernel_endpoint_majorant
  let Q := C*polarGaussianConstant T σ 1*(t/(2*Real.pi))^(2*c)*
    ((a*b:ℕ):ℝ)^(-(1+c)+1/32)
  apply ((gaussianPolynomialExponential_integrable 48 (4*Real.pi)).const_mul Q).mono'
    (a03DiagonalRemoved_line_continuous σ hα m ha hb ht hc).aestronglyMeasurable
  apply ae_of_all
  intro v
  rw [a03DiagonalRemovedNumerator_eq_kernel σ hα m a b t hρ
    (show -(1/8:ℝ)≤((c:ℂ)+(v:ℂ)*I).re by
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_zero,add_zero]
      rcases hc with rfl|rfl <;> norm_num)
    (a03Diagonal_endpoint_off_roots σ hα m hc v)]
  exact hbound T σ hα m a b ha hb t ht c hc v

theorem a03Diagonal_timePower_strip_bound {y c : ℝ} (hy : 0<y)
    (hc : c∈Icc (-(1/8:ℝ)) 1) : y^(2*c)≤y^2+y^(-(1/4:ℝ)) := by
  by_cases hy1 : 1≤y
  · have h := Real.rpow_le_rpow_of_exponent_le hy1 (show 2*c≤(2:ℝ) by linarith [hc.2])
    rw [Real.rpow_two] at h
    exact h.trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hy.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hy (le_of_not_ge hy1)
      (show -(1/4:ℝ)≤2*c by linarith [hc.1])).trans
      (le_add_of_nonneg_left (sq_nonneg y))

theorem a03DiagonalRemoved_horizontal_tendsto_zero {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) {t : ℝ} (ht : 0<t)
    (hρ : ∀ ij : Fin 2 × Fin 2,purePolarRoot T σ (m,ij)≠0) :
    Tendsto (fun v : ℝ => ∫ c in (-(1/8:ℝ))..1,
      a03DiagonalRemovedNumerator T σ m a b t ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,M,hC,hM,hPure⟩ := polarPureGaussian_horizontal_bound T σ m
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)<1/2)
    (fun ij => (purePolarRoot_norm_le_of_rawShifts hα (m,ij)).trans (by norm_num))
  obtain ⟨E,hE,hArith⟩ := a03DiagonalFiniteArithmetic_uniform_bound
  let y : ℝ := t/(2*Real.pi)
  have hy : 0<y := div_pos ht (by positivity)
  let Q : ℝ := C*(y^2+y^(-(1/4:ℝ)))*(E*((a*b:ℕ):ℝ)^(1/32:ℝ))
  have hlarge : ∀ᶠ v : ℝ in cocompact ℝ,M+1≤|v| := by
    rw [cocompact_eq_atBot_atTop,←comap_abs_atTop]
    exact (eventually_ge_atTop (M+1)).comap _
  have hpoint : ∀ v : ℝ,M+1≤|v| → ∀ c∈Icc (-(1/8:ℝ)) 1,
      ‖a03DiagonalRemovedNumerator T σ m a b t ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤
        Q*((1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2)) := by
    intro v hv c hc
    let z : ℂ := (c:ℂ)+(v:ℂ)*I
    have hv1 : 1≤|v| := by linarith
    have hoff : ∀ ij : Fin 2 × Fin 2,z≠purePolarRoot T σ (m,ij) := by
      intro ij he
      have him := (Complex.abs_im_le_norm (purePolarRoot T σ (m,ij))).trans
        (purePolarRoot_norm_le_of_rawShifts hα (m,ij))
      rw [←he] at him
      simp [z] at him
      linarith
    rw [a03DiagonalRemovedNumerator_eq_kernel σ hα m a b t hρ (by simpa [z] using hc.1) hoff,
      a03DiagonalEulerKernel_eq_pure]
    have hInv : ‖z‖⁻¹≤1 := by
      have hn : (1:ℝ)≤‖z‖ := hv1.trans (by simpa [z] using Complex.abs_im_le_norm z)
      simpa only [inv_one] using inv_anti₀ (by norm_num : (0:ℝ)<1) hn
    have hTime : ‖(t/(2*Real.pi):ℂ)^(2*z)‖≤y^2+y^(-(1/4:ℝ)) := by
      rw [show (t/(2*Real.pi):ℂ)=((y:ℝ):ℂ) by dsimp [y]; push_cast; rfl,
        Complex.norm_cpow_eq_rpow_re_of_pos hy]
      have he : (2*z).re=2*c := by simp [z]
      rw [he]
      exact a03Diagonal_timePower_strip_bound hy hc
    have hAmp : ‖((a*b:ℕ):ℂ)^(-(1+z))‖≤1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (mul_ne_zero ha hb))]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ha hb)
      · simp [z]
        linarith [hc.1]
    have hA := hArith (bblrSixShifts (rawMomentShifts T σ) m)
      (fun j => bblrSixShifts_norm_le _ hα m j) a b ha hb z (by simpa [z] using hc.1)
    have hc' : c∈Icc (-(1/4:ℝ)/2) 1 := by norm_num; exact hc
    have hGZ := hPure v hv c hc'
    rw [norm_mul,norm_mul,norm_mul,norm_div,div_eq_mul_inv]
    calc
      _≤(C*(1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2))*1*
          (y^2+y^(-(1/4:ℝ)))*1*(E*((a*b:ℕ):ℝ)^(1/32:ℝ)) := by gcongr
      _=_ := by dsimp [Q]; ring
  have hnorm : ∀ᶠ v : ℝ in cocompact ℝ,
      ‖∫ c in (-(1/8:ℝ))..1,a03DiagonalRemovedNumerator T σ m a b t
        ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖≤
          (Q*|1-(-(1/8:ℝ))|)*((1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2)) := by
    filter_upwards [hlarge] with v hv
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:= -(1/8:ℝ)) (b:=1) (f:=fun c => a03DiagonalRemovedNumerator T σ m a b t
        ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))
      (C:=Q*((1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2))) (by
        intro c hc
        rw [uIoc_of_le (by norm_num : -(1/8:ℝ)≤1)] at hc
        exact hpoint v hv c ⟨hc.1.le,hc.2⟩)
    exact hi.trans_eq (by ring)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (4*Real.pi)).const_mul
    (Q*|1-(-(1/8:ℝ))|)
  simp only [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hnorm hlim

theorem bblrDiagonalTerm_eq_residue_add_leftIntegral {T : ℝ} (σ : MomentShifts)
    (hα : ∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) (m : Fin 6)
    {a b : ℕ} (ha : a≠0) (hb : b≠0) (hab : a.Coprime b) {t : ℝ} (ht : 0<t)
    (hρ : ∀ ij : Fin 2 × Fin 2,purePolarRoot T σ (m,ij)≠0) :
    bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) a b t=
      ((a*b:ℕ):ℂ)^(-1:ℂ)*
        bblrZArithmetic (bblrSixShifts (rawMomentShifts T σ) m 0)
          (bblrSixShifts (rawMomentShifts T σ) m 1)
          (bblrSixShifts (rawMomentShifts T σ) m 2)
          (bblrSixShifts (rawMomentShifts T σ) m 3) a b+
      verticalIntegral (-(1/8:ℝ))
        (a03DiagonalEulerKernel (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) a b t) := by
  let H := a03DiagonalRemovedNumerator T σ m a b t
  have hshift := mellinRectangle_simplePole_shift H
    (isOpen_lt continuous_const Complex.continuous_re)
    (a03DiagonalRemovedNumerator_differentiableOn σ hα m ha hb ht)
    (by norm_num : -(1/8:ℝ)<0) (by norm_num : (0:ℝ)<1)
    (fun z hz _ => by change -(9/64:ℝ)<z.re; linarith)
    (a03DiagonalRemoved_endpoint_integrable σ hα m ha hb ht hρ (Or.inl rfl))
    (a03DiagonalRemoved_endpoint_integrable σ hα m ha hb ht hρ (Or.inr rfl))
    (a03DiagonalRemoved_horizontal_tendsto_zero σ hα m ha hb ht hρ)
  have heq (c : ℝ) (hc : c= -(1/8:ℝ) ∨ c=1) :
      (fun v : ℝ => H ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I))=
      (fun v : ℝ => a03DiagonalEulerKernel (polarPoleKiller T σ)
        (bblrSixShifts (rawMomentShifts T σ) m) a b t ((c:ℂ)+(v:ℂ)*I)) := by
    funext v
    exact a03DiagonalRemovedNumerator_eq_kernel σ hα m a b t hρ
      (by simp; rcases hc with rfl|rfl <;> norm_num)
      (a03Diagonal_endpoint_off_roots σ hα m hc v)
  rw [heq _ (Or.inl rfl),heq _ (Or.inr rfl)] at hshift
  rw [bblrDiagonalTerm_eq_fixedEulerMellin ha hb hab ht _ _
    (polarPoleKiller_BBLREntireWeight T σ _)
    (fun j => (bblrSixShifts_norm_le _ hα m j).trans (by norm_num))]
  change verticalIntegral 1
    (a03DiagonalEulerKernel (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) a b t)=_
  unfold verticalIntegral
  rw [hshift,mul_add]
  have hp : (2*Real.pi:ℂ)≠0 := mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hc : (1/(2*Real.pi):ℂ)*((2*Real.pi:ℂ)*H 0)=H 0 := by field_simp
  rw [hc]
  dsimp only [H]
  rw [a03DiagonalRemovedNumerator_zero σ hα m ha hb t hρ]
  ring

end
end SixthMoment
