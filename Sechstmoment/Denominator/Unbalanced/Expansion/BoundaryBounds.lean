import Sechstmoment.Denominator.Unbalanced.Expansion.Expansion
import Sechstmoment.Zeta.AFE.OneSided.GammaContourBounds
import Sechstmoment.Zeta.Bounds.LeftStrip

/-! Quantitative bounds for the positive-line tail and the two horizontal
edges of the actual one-sided Mellin rectangle. The resulting error is
`O(T⁻²)`, uniformly in the physical argument window. -/

namespace Sechstmoment
open Complex Real MeasureTheory Filter Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem d04_right_integrand_norm_le {T : ℝ} (hT : 0 < T)
    {s r : ℂ} (hs : 0 ≤ s.re) (hr : 0 ≤ r.re) (v : ℝ) :
    ‖d04OneSidedMellinIntegrand (T^3) s r (d04MellinLine v)‖ ≤
      (T^6*(zetaDirichletMajorant 2)^2)*‖Complex.Gamma (d04MellinLine v)‖ := by
  have hz (w : ℂ) (hw : 0 ≤ w.re) :
      ‖riemannZeta (w+d04MellinLine v)‖ ≤ zetaDirichletMajorant 2 :=
    riemannZeta_norm_le_dirichlet (by norm_num) (by simp; linarith)
  have hpow : ‖((T^3 : ℝ):ℂ)^(d04MellinLine v)‖=T^6 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),d04MellinLine_re]
    norm_cast
    ring
  have hZ : 0 ≤ zetaDirichletMajorant 2 := zetaDirichletMajorant_nonneg 2
  rw [d04OneSidedMellinIntegrand,norm_mul,norm_mul,norm_mul,hpow]
  calc
    _ ≤ ‖Complex.Gamma (d04MellinLine v)‖*T^6*
        (zetaDirichletMajorant 2)*(zetaDirichletMajorant 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hz s hs) (by positivity))
        (hz r hr) (norm_nonneg _) (by positivity)
    _ = _ := by ring

private theorem d04_right_integrand_integrable {T : ℝ} (hT : 0 < T)
    {s r : ℂ} (hs : 0 ≤ s.re) (hr : 0 ≤ r.re) :
    Integrable (fun v : ℝ => d04OneSidedMellinIntegrand (T^3) s r (d04MellinLine v)) := by
  have hz (w : ℂ) (hw : 0 ≤ w.re) :
      Continuous (fun v : ℝ => riemannZeta (w+d04MellinLine v)) := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp (by unfold d04MellinLine; fun_prop)
    intro he
    have h := congrArg Complex.re he
    simp only [Complex.add_re,d04MellinLine_re,Complex.one_re] at h
    linarith
  have hpow : Continuous (fun v : ℝ => ((T^3 : ℝ):ℂ)^(d04MellinLine v)) :=
    Continuous.const_cpow (by unfold d04MellinLine; fun_prop)
      (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  apply (d04Gamma_line_two_integrable.norm.const_mul
    (T^6*(zetaDirichletMajorant 2)^2)).mono'
  · exact ((d04Gamma_line_two_integrable.aestronglyMeasurable.mul
      hpow.aestronglyMeasurable).mul (hz s hs).aestronglyMeasurable).mul
      (hz r hr).aestronglyMeasurable
  · exact Eventually.of_forall (d04_right_integrand_norm_le hT hs hr)

/-- The exact complement of the truncated right vertical line has a
uniform `T⁻²` bound. No finite-sum cutoff or tail hypothesis is assumed. -/
theorem d04OneSidedRightTail_power_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T → ∀ s r : ℂ,
      0 ≤ s.re → 0 ≤ r.re →
      ‖d04OneSidedRightTail (T^3) s r (T/4)‖ ≤ C*T^(-2 : ℝ) := by
  let g : ℝ → ℝ := fun v => (1+|v|)^8*‖Complex.Gamma (d04MellinLine v)‖
  have hg : Integrable g := by
    simpa [g,d04MellinLine] using
      d04Gamma_vertical_polynomial_norm_integrable (c := 2)
        (by norm_num) (by norm_num) (by norm_num) 8
  let M : ℝ := ∫ v : ℝ, g v
  have hM : 0 ≤ M := integral_nonneg (fun v => by dsimp [g]; positivity)
  let Z : ℝ := zetaDirichletMajorant 2
  have hZ : 0 ≤ Z := zetaDirichletMajorant_nonneg 2
  refine ⟨4^8*Z^2*M,by positivity,?_⟩
  intro T hT s r hs hr
  have hT0 : 0 < T := by linarith
  let H : ℝ := T/4
  have hH : 0 < H := by dsimp [H]; positivity
  let F : ℝ → ℂ := fun v => d04OneSidedMellinIntegrand (T^3) s r (d04MellinLine v)
  have hF : Integrable F := d04_right_integrand_integrable hT0 hs hr
  have htail : d04OneSidedRightTail (T^3) s r (T/4)=
      ∫ v in (Ioc (-H) H)ᶜ, F v := by
    rw [setIntegral_compl measurableSet_Ioc hF]
    unfold d04OneSidedRightTail d04OneSidedVerticalTruncated
    rw [intervalIntegral.integral_of_le (by dsimp [H]; linarith : -H≤H)]
    rfl
  let A : ℝ := T^6*Z^2/H^8
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hAg : Integrable (fun v => A*g v) := hg.const_mul A
  have hbound : ∀ᵐ v ∂volume.restrict (Ioc (-H) H)ᶜ, ‖F v‖ ≤ A*g v := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc.compl] with v hv
    have hvH : H ≤ |v| := by
      by_contra he
      have hh := abs_lt.mp (lt_of_not_ge he)
      exact hv ⟨hh.1,hh.2.le⟩
    have hP : H^8 ≤ (1+|v|)^8 :=
      pow_le_pow_left₀ hH.le (by linarith [abs_nonneg v]) 8
    have hΓ : ‖Complex.Gamma (d04MellinLine v)‖ ≤ g v/H^8 := by
      rw [le_div_iff₀ (by positivity : 0 < H^8)]
      exact (mul_le_mul_of_nonneg_left hP (norm_nonneg _)).trans_eq (by dsimp [g]; ring)
    calc
      _ ≤ (T^6*Z^2)*‖Complex.Gamma (d04MellinLine v)‖ :=
        d04_right_integrand_norm_le hT0 hs hr v
      _ ≤ (T^6*Z^2)*(g v/H^8) := by gcongr
      _ = A*g v := by dsimp [A]; ring
  rw [htail]
  calc
    _ ≤ ∫ v in (Ioc (-H) H)ᶜ, A*g v :=
      norm_integral_le_of_norm_le hAg.integrableOn hbound
    _ ≤ ∫ v : ℝ, A*g v := setIntegral_le_integral hAg
      (Eventually.of_forall (fun v => by dsimp [g]; positivity))
    _ = A*M := by rw [integral_const_mul]
    _ = (4^8*Z^2*M)*T^(-2 : ℝ) := by
      dsimp [A,H]
      rw [show (-2 : ℝ)=-(2 : ℝ) by ring,Real.rpow_neg hT0.le,Real.rpow_two]
      field_simp

private theorem d04_horizontal_argument_bound {T c v : ℝ}
    (hT : 4 ≤ T) (hc : -1 ≤ c) (hv : |v|=T/4)
    {s : ℂ} (hsre : 1/4 ≤ s.re) (hslo : 3*T/4 ≤ |s.im|) (hshi : |s.im| ≤ 3*T) :
    -1 ≤ (s+((c : ℂ)+(v : ℂ)*I)).re ∧
      1 ≤ |(s+((c : ℂ)+(v : ℂ)*I)).im| ∧
      1+|(s+((c : ℂ)+(v : ℂ)*I)).im| ≤ 5*T := by
  have hre : (s+((c : ℂ)+(v : ℂ)*I)).re=s.re+c := by simp
  have him : (s+((c : ℂ)+(v : ℂ)*I)).im=s.im+v := by simp
  have ht := abs_add_le (s.im+v) (-v)
  rw [add_neg_cancel_right,abs_neg,hv] at ht
  have hu := abs_add_le s.im v
  rw [hv] at hu
  rw [hre,him]
  exact ⟨by linarith,by linarith,by linarith⟩

/-- Both displaced horizontal edges obey the same stronger `T⁻²` bound,
uniformly for the actual physical argument window. -/
theorem d04OneSidedHorizontal_power_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T a v : ℝ, 4 ≤ T → -1 ≤ a → a ≤ 0 → |v|=T/4 →
      ∀ s r : ℂ, 1/4 ≤ s.re → 1/4 ≤ r.re →
        3*T/4 ≤ |s.im| → |s.im| ≤ 3*T →
        3*T/4 ≤ |r.im| → |r.im| ≤ 3*T →
        ‖d04OneSidedHorizontalIntegral (T^3) s r a v‖ ≤ C*T^(-2 : ℝ) := by
  obtain ⟨G,hG,hGamma⟩ := d04Gamma_horizontal_height_bound 20
  obtain ⟨Z,hZ,hZeta⟩ := d04RiemannZeta_polynomial_halfPlane_high_im
  let D : ℝ := G*4^20*Z^2*5^12
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨3*D,by positivity,?_⟩
  intro T a v hT ha ha0 hv s r hs hr hslo hshi hrlo hrhi
  have hT0 : 0 < T := by linarith
  have hpoint (c : ℝ) (hc : c ∈ uIoc a 2) :
      ‖d04OneSidedMellinIntegrand (T^3) s r ((c : ℂ)+(v : ℂ)*I)‖ ≤ D*T^(-2 : ℝ) := by
    rw [uIoc_of_le (by linarith : a≤(2 : ℝ))] at hc
    have hc0 : -1 ≤ c := ha.trans hc.1.le
    have hΓ := hGamma T c v hT hc0 hc.2 hv
    have hζ (w : ℂ) (hw : 1/4 ≤ w.re) (hwlo : 3*T/4 ≤ |w.im|) (hwhi : |w.im| ≤ 3*T) :
        ‖riemannZeta (w+((c : ℂ)+(v : ℂ)*I))‖ ≤ Z*(5*T)^6 := by
      have hh := d04_horizontal_argument_bound hT hc0 hv hw hwlo hwhi
      exact (hZeta _ hh.1 hh.2.1).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh.2.2 6) hZ)
    have hpow : ‖((T^3 : ℝ):ℂ)^((c : ℂ)+(v : ℂ)*I)‖ ≤ T^6 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      have hre : ((c : ℂ)+(v : ℂ)*I).re=c := by simp
      rw [hre,show (T^3 : ℝ)=T^(3 : ℝ) by norm_cast,← Real.rpow_mul hT0.le]
      calc
        _ ≤ T^(6 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith : 1≤T)
          (show (3 : ℝ)*c≤6 by linarith [hc.2])
        _ = T^6 := by norm_cast
    rw [d04OneSidedMellinIntegrand,norm_mul,norm_mul,norm_mul]
    calc
      _ ≤ (G*4^20/T^20)*T^6*(Z*(5*T)^6)*(Z*(5*T)^6) := by
        gcongr
        · exact hζ s hs hslo hshi
        · exact hζ r hr hrlo hrhi
      _ = D*T^(-2 : ℝ) := by
        dsimp [D]
        rw [show (-2 : ℝ)=-(2 : ℝ) by ring,Real.rpow_neg hT0.le,Real.rpow_two]
        field_simp
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpoint
  unfold d04OneSidedHorizontalIntegral
  calc
    _ ≤ D*T^(-2 : ℝ)*|2-a| := hnorm
    _ ≤ (3*D)*T^(-2 : ℝ) := by
      rw [abs_of_nonneg (by linarith : 0≤(2 : ℝ)-a)]
      have hpos : 0 ≤ D*T^(-2 : ℝ) := by positivity
      have h := mul_le_mul_of_nonneg_left (show 2-a≤3 by linarith) hpos
      convert h using 1
      ring

end
end Sechstmoment
