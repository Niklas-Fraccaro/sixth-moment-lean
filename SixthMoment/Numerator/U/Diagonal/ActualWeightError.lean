import SixthMoment.Numerator.Polar.GammaRemainder
import SixthMoment.Numerator.Polar.PureHorizontal
import SixthMoment.Numerator.U.Replacement.CentralContourShift
import SixthMoment.Numerator.U.Replacement.GaussianTailUniform

set_option maxRecDepth 4000

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section

theorem bblrCentralWeightDifference_gaussian_majorant :
    ∃ D : ℝ, 0 < D ∧ ∀ t x c : ℝ, 0 < t → 0 < x → 0 < c → c ≤ 1 →
      ∀ T : ℝ, ∀ σ α : MomentShifts, (∀ j, ‖α j‖ ≤ 1/4) → ∀ v : ℝ,
      ‖bblrCentralWeightDifference (polarPoleKiller T σ) t α x ((c:ℂ)+(v:ℂ)*I)‖ ≤
        (polarGaussianConstant T σ c/c*Real.pi^(-2*c)*x^(-c)*
          (D*(2+t)^8+(t/2)^(2*c)))*(1+|v|)^56*Real.exp (-v^2) := by
  obtain ⟨D,hD,hΓ⟩ := bblrGammaQuotient_polynomial_positive_strip_bound
  refine ⟨D,hD,?_⟩
  intro t x c ht hx hc hc1 T σ α hα v
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hzn : c ≤ ‖z‖ := by simpa [z,abs_of_pos hc] using Complex.abs_re_le_norm z
  have hg : ‖polarPoleKiller T σ z/z‖ ≤
      polarGaussianConstant T σ c/c*(1+|v|)^48*Real.exp (-v^2) := by
    rw [norm_div]
    calc
      _ ≤ ‖polarPoleKiller T σ z‖/c := div_le_div_of_nonneg_left (norm_nonneg _) hc hzn
      _ ≤ (polarGaussianConstant T σ c*(1+|v|)^48*Real.exp (-v^2))/c := by
        gcongr
        exact polarPoleKiller_vertical_norm_le T σ c v
      _ = _ := by ring
  have htn : ‖(t/2:ℂ)^(2*z)‖ = (t/2)^(2*c) := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<t/2) (2*z)
    simpa [z] using hh
  have hπ : ‖(Real.pi:ℂ)^(-2*z)‖ = Real.pi^(-2*c) := by
    simpa [z] using Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-2*z)
  have hxp : ‖(x:ℂ)^(-z)‖ = x^(-c) := by
    simpa [z] using Complex.norm_cpow_eq_rpow_re_of_pos hx (-z)
  have hpoly : (2+t+|v|)^8 ≤ (2+t)^8*(1+|v|)^8 := by
    rw [← mul_pow]
    gcongr
    nlinarith [abs_nonneg v]
  have hp : 1 ≤ (1+|v|)^8 := by
    exact one_le_pow₀ (by linarith [abs_nonneg v])
  have hdiff : ‖bblrGammaQuotient t α z-(t/2:ℂ)^(2*z)‖ ≤
      (D*(2+t)^8+(t/2)^(2*c))*(1+|v|)^8 := by
    calc
      _ ≤ ‖bblrGammaQuotient t α z‖+‖(t/2:ℂ)^(2*z)‖ := norm_sub_le _ _
      _ ≤ D*((2+t)^8*(1+|v|)^8)+(t/2)^(2*c) := by
        rw [htn]
        gcongr
        exact (hΓ t v c ht.le hc.le hc1 α hα).trans (by gcongr)
      _ ≤ D*((2+t)^8*(1+|v|)^8)+(t/2)^(2*c)*(1+|v|)^8 :=
        add_le_add le_rfl (le_mul_of_one_le_right
          (Real.rpow_nonneg (by positivity : 0≤t/2) (2*c)) hp)
      _ = _ := by ring
  have hCG := polarGaussianConstant_nonneg T σ c
  unfold bblrCentralWeightDifference
  rw [norm_mul,norm_mul,norm_mul,hπ,hxp]
  calc
    _ ≤ (polarGaussianConstant T σ c/c*(1+|v|)^48*Real.exp (-v^2))*
        ((D*(2+t)^8+(t/2)^(2*c))*(1+|v|)^8)*Real.pi^(-2*c)*x^(-c) := by gcongr
    _ = _ := by rw [show (1+|v|)^56=(1+|v|)^48*(1+|v|)^8 by rw [← pow_add]]; ring

def bblrShiftedGaussianDifferenceTail (T : ℝ) (σ α : MomentShifts)
    (t x c R : ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫ v in {v : ℝ | R < |v|},
    bblrCentralWeightDifference (polarPoleKiller T σ) t α x ((c:ℂ)+(v:ℂ)*I)

theorem bblrShiftedGaussianDifferenceTail_norm_le :
    ∃ D : ℝ, 0 < D ∧ ∀ t x c R : ℝ, 0<t → 0<x → 0<c → c≤1 → 0≤R →
      ∀ T : ℝ, ∀ σ α : MomentShifts, (∀ j, ‖α j‖≤1/4) →
      ‖bblrShiftedGaussianDifferenceTail T σ α t x c R‖ ≤
        (polarGaussianConstant T σ c/c*Real.pi^(-2*c)*x^(-c)*
          (D*(2+t)^8+(t/2)^(2*c)))*gaussianTailConstant 56/(2*Real.pi)*
          Real.exp (-(1/2)*R^2) := by
  obtain ⟨D,hD,hbound⟩ := bblrCentralWeightDifference_gaussian_majorant
  refine ⟨D,hD,?_⟩
  intro t x c R ht hx hc hc1 hR T σ α hα
  have hi := bblrCentralWeightDifference_vertical_integrable ht hx hc hc1
    (polarPoleKiller T σ) α (polarPoleKiller_BBLREntireWeight T σ α) hα
  have hCG := polarGaussianConstant_nonneg T σ c
  have htail := gaussian_integral_tail_norm_le
    (fun v : ℝ => bblrCentralWeightDifference (polarPoleKiller T σ) t α x ((c:ℂ)+(v:ℂ)*I))
    hi 56 (by positivity : 0≤polarGaussianConstant T σ c/c*Real.pi^(-2*c)*x^(-c)*
      (D*(2+t)^8+(t/2)^(2*c))) hR (hbound t x c ht hx hc hc1 T σ α hα)
  unfold bblrShiftedGaussianDifferenceTail
  rw [norm_mul]
  have hn : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hn]
  calc
    _ ≤ (1/(2*Real.pi))*
        ((polarGaussianConstant T σ c/c*Real.pi^(-2*c)*x^(-c)*
          (D*(2+t)^8+(t/2)^(2*c)))*gaussianTailConstant 56*Real.exp (-(1/2)*R^2)) :=
      mul_le_mul_of_nonneg_left htail (by positivity)
    _ = _ := by ring

theorem bblrGaussianV_sub_bblrVStar_core_add_tail {t x c R : ℝ}
    (ht : 0<t) (hx : 0<x) (hc : 0<c) (hc1 : c≤1)
    (T : ℝ) (σ α : MomentShifts) (hα : ∀ j, ‖α j‖≤1/4) :
    bblrV (polarPoleKiller T σ) α x t-bblrVStar (polarPoleKiller T σ) (x/t^2) =
      bblrCentralGaussianDifferenceCore T σ α t x c R+
      bblrShiftedGaussianDifferenceTail T σ α t x c R := by
  rw [bblrGaussianV_sub_bblrVStar_eq_shifted_centralWeightDifference ht hx hc hc1 T σ α hα]
  have hi := bblrCentralWeightDifference_vertical_integrable ht hx hc hc1
    (polarPoleKiller T σ) α (polarPoleKiller_BBLREntireWeight T σ α) hα
  have hs : MeasurableSet {v : ℝ | R < |v|} :=
    (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl hs hi
  have hset : {v : ℝ | R < |v|}ᶜ=Icc (-R) R := by
    ext v
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc]
    exact abs_le
  rw [hset] at he
  unfold verticalIntegral bblrCentralGaussianDifferenceCore bblrShiftedGaussianDifferenceTail
  rw [← he]
  ring

private theorem eventually_positive_mul_rpow_lt_id (C : ℝ) (hC : 0<C)
    {e : ℝ} (he : e<1) : ∀ᶠ t : ℝ in atTop, C*t^e<t := by
  have hlim : Tendsto (fun t : ℝ => t^e/t) atTop (𝓝 0) := by
    have hh := tendsto_rpow_neg_atTop (sub_pos.mpr he)
    apply hh.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    rw [show -(1-e)=e-1 by ring,Real.rpow_sub ht,Real.rpow_one]
  filter_upwards [hlim.eventually_lt_const (one_div_pos.mpr hC),
    eventually_gt_atTop (0:ℝ)] with t ht htpos
  rw [div_lt_iff₀ htpos] at ht
  have hh := mul_lt_mul_of_pos_left ht hC
  simpa [mul_assoc,hC.ne'] using hh

theorem bblrCentralGaussian_cutoff_conditions {ε : ℝ} (hε : 0<ε) (hεhalf : ε<1/2) :
    ∀ᶠ t : ℝ in atTop,
      10≤t ∧ 0≤t^ε ∧ 192*((1+t^ε)+(1+t^ε)^2)<t ∧ 6*(1+t^ε)≤t := by
  filter_upwards [eventually_positive_mul_rpow_lt_id 1152 (by norm_num)
      (by linarith : 2*ε<1),
    eventually_positive_mul_rpow_lt_id 12 (by norm_num) (by linarith : ε<1),
    eventually_ge_atTop (10:ℝ)] with t hcentral hphase ht
  have ht1 : 1≤t := by linarith
  have htpos : 0<t := by linarith
  have hR : 1≤t^ε := Real.one_le_rpow ht1 hε.le
  have hpow : (t^ε)^2=t^(2*ε) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul htpos.le]
    congr 1
    ring
  refine ⟨ht,(Real.rpow_pos_of_pos htpos ε).le,?_,?_⟩
  · rw [← hpow] at hcentral
    nlinarith
  · linarith

theorem bblrGaussianV_sub_bblrVStar_uniform_error {c ε : ℝ}
    (hc : 0<c) (hc1 : c≤1) (hε : 0<ε) (hεhalf : ε<1/2) :
    ∃ E : ℝ, 0<E ∧ ∀ᶠ t : ℝ in atTop, ∀ T : ℝ, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ x : ℝ, 0<x →
      ‖bblrV (polarPoleKiller T σ) α x t-bblrVStar (polarPoleKiller T σ) (x/t^2)‖ ≤
        E*polarGaussianConstant T σ c*(t/2)^(2*c)*Real.pi^(-2*c)*x^(-c)/t := by
  obtain ⟨D,hD,hbound⟩ := bblrShiftedGaussianDifferenceTail_norm_le
  let E₀ : ℝ := (2886/(2*Real.pi))*gaussianTailConstant 49
  let E₁ : ℝ := (D*3^8+1)*gaussianTailConstant 56/(2*Real.pi*c)
  have hJ49 := gaussianTailConstant_nonneg 49
  have hJ56 := gaussianTailConstant_nonneg 56
  have hE₀ : 0≤E₀ := by dsimp [E₀]; positivity
  have hE₁ : 0≤E₁ := by dsimp [E₁]; positivity
  refine ⟨E₀+E₁+1,by positivity,?_⟩
  filter_upwards [bblrCentralGaussian_cutoff_conditions hε hεhalf,
    polynomial_gaussian_power_eventually_le hε 8 1] with t hconditions hdec
  intro T σ α hα x hx
  obtain ⟨ht,hR,hcentral,hphase⟩ := hconditions
  have htpos : 0<t := by linarith
  have ht1 : 1≤t := by linarith
  have ht2 : 2≤t := by linarith
  let P : ℝ := (t/2)^(2*c)
  let K : ℝ := polarGaussianConstant T σ c*Real.pi^(-2*c)*x^(-c)
  have hCG := polarGaussianConstant_nonneg T σ c
  have hK : 0≤K := by dsimp [K]; positivity
  have hP : 1≤P := Real.one_le_rpow (by linarith : 1≤t/2) (by positivity : 0≤2*c)
  have hp8 : P≤t^8 := by
    calc
      _ ≤ t^(2*c) := Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
      _ ≤ t^(8:ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
      _ = _ := Real.rpow_natCast t 8
  have ht8 : (2+t)^8≤3^8*t^8 := by
    rw [← mul_pow]
    gcongr
    linarith
  have hcoeff : D*(2+t)^8+P≤(D*3^8+1)*t^8 := by
    nlinarith [mul_le_mul_of_nonneg_left ht8 hD.le]
  have hcore := bblrCentralGaussianDifferenceCore_norm_le ht hx hc hc1 hR hcentral
    hphase T σ α hα
  have hcore' : ‖bblrCentralGaussianDifferenceCore T σ α t x c (t^ε)‖≤E₀*K*P/t := by
    convert hcore using 1
    dsimp [E₀,K,P]
    ring
  have htail := hbound t x c (t^ε) htpos hx hc hc1 hR T σ α hα
  have htail' : ‖bblrShiftedGaussianDifferenceTail T σ α t x c (t^ε)‖≤E₁*K*P/t := by
    calc
      _ ≤ (polarGaussianConstant T σ c/c*Real.pi^(-2*c)*x^(-c)*
          ((D*3^8+1)*t^8))*gaussianTailConstant 56/(2*Real.pi)*
            Real.exp (-(1/2)*(t^ε)^2) := by
        apply htail.trans
        gcongr
      _ = E₁*K*(t^8*Real.exp (-(1/2)*(t^ε)^2)) := by dsimp [E₁,K]; ring
      _ ≤ E₁*K*t^(-1:ℝ) := by
        gcongr
        convert hdec using 1
        exact congrArg (fun q : ℝ => q*Real.exp (-(1/2)*(t^ε)^2))
          (Real.rpow_natCast t 8).symm
      _ = E₁*K/t := by rw [Real.rpow_neg_one]; ring
      _ ≤ E₁*K*P/t := div_le_div_of_nonneg_right
        (le_mul_of_one_le_right (mul_nonneg hE₁ hK) hP) htpos.le
  rw [bblrGaussianV_sub_bblrVStar_core_add_tail (R := t^ε) htpos hx hc hc1 T σ α hα]
  calc
    _ ≤ ‖bblrCentralGaussianDifferenceCore T σ α t x c (t^ε)‖+
        ‖bblrShiftedGaussianDifferenceTail T σ α t x c (t^ε)‖ := norm_add_le _ _
    _ ≤ E₀*K*P/t+E₁*K*P/t := add_le_add hcore' htail'
    _ ≤ (E₀+E₁+1)*K*P/t := by
      rw [← add_div]
      apply (div_le_div_of_nonneg_right ?_ htpos.le)
      nlinarith [mul_nonneg hK (by linarith : 0≤P)]
    _ = _ := by dsimp [K,P]; ring

theorem bblrGaussianV_sub_bblrVStar_scaled_uniform_error {c : ℝ}
    (hc : 0<c) (hc1 : c≤1) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ t : ℝ in atTop, ∀ T : ℝ, ∀ σ α : MomentShifts,
      (∀ j, ‖α j‖≤1/4) → ∀ x : ℝ, 0<x →
      ‖bblrV (polarPoleKiller T σ) α x t-bblrVStar (polarPoleKiller T σ) (x/t^2)‖ ≤
        C*polarGaussianConstant T σ c/t*(x/t^2)^(-c) := by
  obtain ⟨E,hE,hbound⟩ := bblrGaussianV_sub_bblrVStar_uniform_error hc hc1
    (by norm_num : (0:ℝ)<1/4) (by norm_num : (1/4:ℝ)<1/2)
  refine ⟨E*(2*Real.pi)^(-2*c),by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with t hb ht
  intro T σ α hα x hx
  have hidentity := congrArg norm (bblr_main_positive_cpow_identity ht hx (c:ℂ))
  have htn : ‖(t/2:ℂ)^(2*(c:ℂ))‖=(t/2)^(2*c) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<t/2) (2*(c:ℂ))
  have hπ : ‖(Real.pi:ℂ)^(-2*(c:ℂ))‖=Real.pi^(-2*c) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos (-2*(c:ℂ))
  have hxn : ‖(x:ℂ)^(-(c:ℂ))‖=x^(-c) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hx (-(c:ℂ))
  have h2π : ‖(2*Real.pi:ℂ)^(-2*(c:ℂ))‖=(2*Real.pi)^(-2*c) := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<2*Real.pi) (-2*(c:ℂ))
  have hxt : ‖(x/t^2:ℂ)^(-(c:ℂ))‖=(x/t^2)^(-c) := by
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<x/t^2) (-(c:ℂ))
    simpa only [Complex.ofReal_div,Complex.ofReal_pow,Complex.neg_re,Complex.ofReal_re] using hh
  rw [norm_mul,norm_mul,norm_mul,htn,hπ,hxn,h2π,hxt] at hidentity
  calc
    _ ≤ E*polarGaussianConstant T σ c*(t/2)^(2*c)*Real.pi^(-2*c)*x^(-c)/t := hb T σ α hα x hx
    _ = E*polarGaussianConstant T σ c/t*((t/2)^(2*c)*Real.pi^(-2*c)*x^(-c)) := by ring
    _ = _ := by rw [hidentity]; ring

theorem bblrGaussianV_sub_bblrVStar_uniform_raw_error (K : Set MomentShifts)
    (hK : IsCompact K) {δ c : ℝ} (hδ : 0<δ) (hc : 0<c) (hc1 : c≤1)
    (hρ : ∀ σ ∈ K, ∀ k : PurePolarIndex, δ≤‖normalizedPurePolarRoot σ k‖) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ ∈ K, ∀ t ∈ Icc T (2*T),
      ∀ x : ℝ, 0<x →
      ‖bblrV (polarPoleKiller T σ) (rawMomentShifts T σ) x t-
        bblrVStar (polarPoleKiller T σ) (x/t^2)‖ ≤
      C*(Real.log T)^48/T*(x/t^2)^(-c) := by
  obtain ⟨C,hC,hbound⟩ := bblrGaussianV_sub_bblrVStar_scaled_uniform_error hc hc1
  obtain ⟨t₀,ht₀⟩ := eventually_atTop.mp hbound
  let E : ℝ := Real.exp 1*2^48*(1+1/δ^2)^24
  have hE : 0<E := by dsimp [E]; positivity
  refine ⟨C*E,by positivity,?_⟩
  filter_upwards [eventually_ge_atTop t₀,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1:ℝ)),
    compactNormalizedShifts_eventually_norm_small K hK (1/4) (by norm_num)]
    with T hT₀ hT hL hsmall
  intro σ hσ t ht x hx
  have hCG := polarGaussianConstant_nonneg T σ c
  have hCGc : polarGaussianConstant T σ c≤polarGaussianConstant T σ 1 :=
    polarGaussianConstant_le_of_abs_le T σ (by norm_num)
      (by simpa [abs_of_pos hc] using hc1)
  have hgrowth : polarGaussianConstant T σ c≤E*(Real.log T)^48 :=
    hCGc.trans (polarGaussianConstant_log_growth hT hL hδ σ (hρ σ hσ))
  have htpos : 0<t := by linarith [ht.1]
  have hTpos : 0<T := by linarith
  have hb := ht₀ t (hT₀.trans ht.1) T σ (rawMomentShifts T σ) (hsmall σ hσ) x hx
  calc
    _ ≤ C*polarGaussianConstant T σ c/t*(x/t^2)^(-c) := hb
    _ ≤ C*(E*(Real.log T)^48)/T*(x/t^2)^(-c) := by
      gcongr
      exact ht.1
    _ = _ := by dsimp [E]; ring

end
end SixthMoment.Source
