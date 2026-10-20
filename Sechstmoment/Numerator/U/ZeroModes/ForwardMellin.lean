import Mathlib.Analysis.MellinInversion
import Sechstmoment.Numerator.U.Replacement.VStar.Contours
import Sechstmoment.Numerator.U.ZeroModes.Contour.RatioSmooth

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology FourierTransform
noncomputable section
set_option maxHeartbeats 0

theorem a03VStarKernel_eq_ratio_scaled {y : ℝ} (hy : 0<y)
    (G : ℂ→ℂ) (z : ℂ) :
    bblrVStarKernel G y z=a03ZeroModeRatioKernel G ((2*Real.pi)^2*y) z := by
  have hp : 0<2*Real.pi := by positivity
  have hprod : 0<(2*Real.pi)^2*y := by positivity
  have he : (((2*Real.pi:ℝ):ℂ))^(-2*z)*(y:ℂ)^(-z)=
      (((2*Real.pi)^2*y:ℝ):ℂ)^(-z) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'),
      Complex.cpow_def_of_ne_zero (by exact_mod_cast hprod.ne'),
      ←Complex.ofReal_log hp.le,←Complex.ofReal_log hy.le,
      ←Complex.ofReal_log hprod.le,←Complex.exp_add,
      Real.log_mul (pow_ne_zero 2 hp.ne') hy.ne',Real.log_pow]
    congr 1
    push_cast
    ring
  unfold bblrVStarKernel a03ZeroModeRatioKernel
  have he' := he
  push_cast at he'
  rw [mul_assoc,he']
  push_cast
  ring

theorem a03VStar_eq_ratio_scaled {y : ℝ} (hy : 0<y) (G : ℂ→ℂ) :
    bblrVStar G y=a03ZeroModeRatioPartition G ((2*Real.pi)^2*y) := by
  unfold bblrVStar a03ZeroModeRatioPartition
  congr 1
  funext z
  exact a03VStarKernel_eq_ratio_scaled hy G z

theorem a03ZeroModeRatioPartition_positive_contour {x c : ℝ}
    (hx : 0<x) (hc : 0<c) (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    a03ZeroModeRatioPartition G x=verticalIntegral c (a03ZeroModeRatioKernel G x) := by
  have hp : 0<(2*Real.pi)^2 := by positivity
  have hy : 0<x/(2*Real.pi)^2 := div_pos hx hp
  have he : (2*Real.pi)^2*(x/(2*Real.pi)^2)=x := by field_simp
  rw [←he,←a03VStar_eq_ratio_scaled hy G,bblrVStar_positive_contour hy hc G α hG]
  congr 1
  funext z
  exact a03VStarKernel_eq_ratio_scaled hy G z

theorem a03ZeroModeRatioPartition_eq_mellinInv {x c : ℝ}
    (hx : 0<x) (hc : 0<c) (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    a03ZeroModeRatioPartition G x=mellinInv c (fun s => G s/s) x := by
  rw [a03ZeroModeRatioPartition_positive_contour hx hc G α hG]
  unfold verticalIntegral mellinInv
  simp only [Complex.real_smul,smul_eq_mul]
  push_cast
  congr 1
  apply integral_congr_ae
  filter_upwards [] with v
  unfold a03ZeroModeRatioKernel
  ring

theorem a03ZeroModeRatioPartition_power_bound {c : ℝ} (hc : 0<c)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    ∃ C : ℝ,0≤C ∧ ∀ x : ℝ,0<x →
      ‖a03ZeroModeRatioPartition G x‖≤C*x^(-c) := by
  let C := (1/(2*Real.pi))*(∫ v : ℝ,‖G ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro x hx
  rw [a03ZeroModeRatioPartition_positive_contour hx hc G α hG]
  unfold verticalIntegral
  rw [norm_mul]
  have hnorm : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans_eq
  simp_rw [a03ZeroModeRatioKernel,norm_div,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp only [neg_re,add_re,ofReal_re,mul_I_re,ofReal_im,neg_zero,add_zero]
  simp_rw [show ∀ v : ℝ,‖G ((c:ℂ)+(v:ℂ)*I)‖*x^(-c)/‖(c:ℂ)+(v:ℂ)*I‖=
      ‖G ((c:ℂ)+(v:ℂ)*I)/((c:ℂ)+(v:ℂ)*I)‖*x^(-c) by
    intro v; rw [norm_div]; ring]
  rw [integral_mul_const]
  ring

theorem a03ZeroModeRatioPartition_small_bound (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) :
    ∃ C : ℝ,0≤C ∧ ∀ x∈Ioc (0:ℝ) 1,‖a03ZeroModeRatioPartition G x‖≤C := by
  obtain ⟨C,hC,hb⟩ := a03ZeroModeRatioPartition_power_bound (by norm_num : 0<(1:ℝ)) G α hG
  refine ⟨1+C,by positivity,?_⟩
  intro x hx
  have he := a03ZeroModeRatioPartition_identity hx.1 G α hG
  have hi := hb x⁻¹ (inv_pos.mpr hx.1)
  have hpow : (x⁻¹)^(-(1:ℝ))=x := by rw [Real.rpow_neg_one,inv_inv]
  rw [hpow] at hi
  calc
    _=‖1-a03ZeroModeRatioPartition G x⁻¹‖ := by congr 1; linear_combination he
    _≤‖(1:ℂ)‖+‖a03ZeroModeRatioPartition G x⁻¹‖ := norm_sub_le _ _
    _≤1+C*x := by simpa using add_le_add_left hi 1
    _≤1+C := by nlinarith [hx.2]


def a03ZeroModeRatioLogReweighted (G : ℂ→ℂ) (σ u : ℝ) : ℂ :=
  (Real.exp (-σ*u):ℂ)*a03ZeroModeRatioPartition G (Real.exp (-u))

theorem a03ZeroModeRatioLogReweighted_continuous (G : ℂ→ℂ) (α : MomentShifts)
    (hG : BBLREntireWeight G α) (σ : ℝ) :
    Continuous (a03ZeroModeRatioLogReweighted G σ) := by
  unfold a03ZeroModeRatioLogReweighted
  apply Continuous.mul (by fun_prop)
  exact (a03ZeroModeRatioPartition_contDiffOn G α hG).continuousOn.comp_continuous
    (by fun_prop) (fun u => Real.exp_pos (-u))

theorem a03ZeroModeRatioLogReweighted_integrable {σ : ℝ} (hσ : 0<σ)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    Integrable (a03ZeroModeRatioLogReweighted G σ) := by
  obtain ⟨C₀,hC₀,hsmall⟩ := a03ZeroModeRatioPartition_small_bound G α hG
  obtain ⟨C₁,hC₁,hlarge⟩ := a03ZeroModeRatioPartition_power_bound
    (show 0<σ+1 by linarith) G α hG
  have hm : AEStronglyMeasurable (a03ZeroModeRatioLogReweighted G σ) volume :=
    (a03ZeroModeRatioLogReweighted_continuous G α hG σ).aestronglyMeasurable
  have hpos : IntegrableOn (a03ZeroModeRatioLogReweighted G σ) (Ioi 0) := by
    apply ((integrableOn_exp_mul_Ioi (show -σ<0 by linarith) 0).const_mul C₀).mono'
      hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hx : Real.exp (-u)∈Ioc (0:ℝ) 1 :=
      ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu.le)⟩
    unfold a03ZeroModeRatioLogReweighted
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _≤Real.exp (-σ*u)*C₀ := mul_le_mul_of_nonneg_left (hsmall _ hx) (Real.exp_pos _).le
      _=_ := by ring
  have hneg : IntegrableOn (a03ZeroModeRatioLogReweighted G σ) (Iic 0) := by
    apply ((integrableOn_exp_Iic 0).const_mul C₁).mono' hm.restrict
    filter_upwards [ae_restrict_mem measurableSet_Iic] with u _hu
    have hb := hlarge (Real.exp (-u)) (Real.exp_pos _)
    unfold a03ZeroModeRatioLogReweighted
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    calc
      _≤Real.exp (-σ*u)*(C₁*(Real.exp (-u))^(-(σ+1))) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
      _=C₁*Real.exp u := by
        rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
        rw [show Real.exp (-σ*u)*(C₁*Real.exp (-u * -(σ+1)))=
          C₁*(Real.exp (-σ*u)*Real.exp (-u * -(σ+1))) by ring,←Real.exp_add]
        congr 2
        ring
  rw [←integrableOn_univ,←(Iic_union_Ioi (a := (0:ℝ))),integrableOn_union]
  exact ⟨hneg,hpos⟩

theorem a03ZeroModeRatioLogReweighted_eq_fourierInv {σ : ℝ} (hσ : 0<σ)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) (u : ℝ) :
    a03ZeroModeRatioLogReweighted G σ u=
      𝓕⁻ (fun y : ℝ => G ((σ:ℂ)+2*Real.pi*y*I)/((σ:ℂ)+2*Real.pi*y*I)) u := by
  unfold a03ZeroModeRatioLogReweighted
  rw [a03ZeroModeRatioPartition_eq_mellinInv (Real.exp_pos _) hσ G α hG,
    mellinInv_eq_fourierInv σ (fun s => G s/s) (Real.exp_pos _),Real.log_exp,neg_neg]
  simp only [smul_eq_mul]
  have he : (Real.exp (-u):ℂ)^(-(σ:ℂ))=(Real.exp (σ*u):ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (-u)).ne'),
      ←Complex.ofReal_log (Real.exp_pos (-u)).le,Real.log_exp]
    norm_cast
    congr 1
    ring
  rw [he,←mul_assoc,←Complex.ofReal_mul,←Real.exp_add]
  simp only [show -σ*u+σ*u=0 by ring,Real.exp_zero,Complex.ofReal_one,one_mul]

theorem a03ZeroModeRatioPartition_forwardMellin {s : ℂ} (hs : 0<s.re)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    mellin (a03ZeroModeRatioPartition G) s=G s/s := by
  let H : ℝ→ℂ := fun y => G ((s.re:ℂ)+2*Real.pi*y*I)/((s.re:ℂ)+2*Real.pi*y*I)
  have hline : Integrable (fun v : ℝ => G ((s.re:ℂ)+(v:ℂ)*I)/((s.re:ℂ)+(v:ℂ)*I)) := by
    convert a03ZeroModeRatioKernel_line_integrable (by norm_num : 0<(1:ℝ)) hs.ne' G α hG using 1
    funext v
    simp [a03ZeroModeRatioKernel]
  have hH : Integrable H := by
    convert hline.comp_mul_left' (show 2*Real.pi≠0 by positivity) using 1
    funext y
    dsimp [H]
    push_cast
    ring
  have hcont : Continuous H := by
    dsimp [H]
    apply ((Complex.analyticOnNhd_univ_iff_differentiable.mp hG.1).continuous.comp
      (by fun_prop)).div (by fun_prop)
    intro y hy
    have he := congrArg Complex.re hy
    simp at he
    linarith
  have hlog : a03ZeroModeRatioLogReweighted G s.re=𝓕⁻ H := by
    funext u
    exact a03ZeroModeRatioLogReweighted_eq_fourierInv hs G α hG u
  have hFinv : Integrable (𝓕⁻ H) := hlog ▸ a03ZeroModeRatioLogReweighted_integrable hs G α hG
  have hF : Integrable (𝓕 H) := by
    convert hFinv.comp_neg using 1
    funext u
    rw [fourierInv_eq_fourier_neg,neg_neg]
  rw [mellin_eq_fourier]
  change 𝓕 (a03ZeroModeRatioLogReweighted G s.re) (s.im/(2*Real.pi))=_
  rw [hlog,hH.fourier_fourierInv_eq hF hcont.continuousAt]
  dsimp [H]
  push_cast
  rw [mul_div_cancel₀ _ (show (2*Real.pi:ℂ)≠0 by exact_mod_cast (show 2*Real.pi≠0 by positivity))]
  rw [Complex.re_add_im]


theorem a03ZeroModeRatioPartition_mellinConvergent {s : ℂ} (hs : 0<s.re)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    MellinConvergent (a03ZeroModeRatioPartition G) s := by
  have hm : AEStronglyMeasurable (a03ZeroModeRatioPartition G) (volume.restrict (Ioi 0)) :=
    (a03ZeroModeRatioPartition_contDiffOn G α hG).continuousOn.aestronglyMeasurable measurableSet_Ioi
  suffices h : MellinConvergent (a03ZeroModeRatioPartition G) (s.re:ℂ) by
    rw [MellinConvergent,mellin_convergent_iff_norm Subset.rfl measurableSet_Ioi hm] at h ⊢
    simpa only [Complex.ofReal_re] using h
  have himage : (Real.exp ∘ Neg.neg) '' (univ: Set ℝ)=Ioi 0 := by
    rw [Set.image_comp,Set.image_univ_of_surjective neg_surjective,Set.image_univ,Real.range_exp]
  have hderiv : ∀ u∈(univ:Set ℝ),HasDerivWithinAt (Real.exp ∘ Neg.neg)
      (-Real.exp (-u)) univ u := by
    intro u _
    exact (((Real.hasDerivAt_exp (-u)).comp u (hasDerivAt_neg u)).hasDerivWithinAt).congr_deriv (by ring)
  have hinj : (univ:Set ℝ).InjOn (Real.exp ∘ Neg.neg) :=
    Real.exp_injective.injOn.comp neg_injective.injOn (univ.mapsTo_univ _)
  rw [MellinConvergent,←himage,integrableOn_image_iff_integrableOn_abs_deriv_smul
    MeasurableSet.univ hderiv hinj]
  convert (a03ZeroModeRatioLogReweighted_integrable hs G α hG).integrableOn using 1
  funext u
  simp only [Function.comp_apply,abs_neg,abs_of_pos (Real.exp_pos _),
    smul_eq_mul,a03ZeroModeRatioLogReweighted]
  have hp : (Real.exp (-u):ℂ)*((Real.exp (-u):ℂ)^((s.re:ℂ)-1))=
      (Real.exp (-s.re*u):ℂ) := by
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos (-u)).ne'),
      ←Complex.ofReal_log (Real.exp_pos (-u)).le,Real.log_exp]
    simp only [Complex.ofReal_exp]
    rw [←Complex.exp_add]
    congr 1
    push_cast
    ring
  change (Real.exp (-u):ℂ)*((Real.exp (-u):ℂ)^((s.re:ℂ)-1)*_) = _
  rw [←mul_assoc,hp]

theorem a03ZeroModeRatioPartition_hasMellin {s : ℂ} (hs : 0<s.re)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    HasMellin (a03ZeroModeRatioPartition G) s (G s/s) :=
  ⟨a03ZeroModeRatioPartition_mellinConvergent hs G α hG,
    a03ZeroModeRatioPartition_forwardMellin hs G α hG⟩

theorem bblrVStar_forwardMellin {s : ℂ} (hs : 0<s.re)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    mellin (bblrVStar G) s=(2*Real.pi:ℂ)^(-2*s)*(G s/s) := by
  have hp : 0<(2*Real.pi)^2 := by positivity
  have he : mellin (bblrVStar G) s=
      mellin (fun x => a03ZeroModeRatioPartition G ((2*Real.pi)^2*x)) s := by
    unfold mellin
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [a03VStar_eq_ratio_scaled hx G]
  rw [he,mellin_comp_mul_left _ s hp,a03ZeroModeRatioPartition_forwardMellin hs G α hG]
  simp only [smul_eq_mul]
  congr 1
  have hπ : 0<2*Real.pi := by positivity
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hπ.ne'),
    ←Complex.ofReal_log hp.le]
  have heπ : (2*Real.pi:ℂ)=((2*Real.pi:ℝ):ℂ) := by push_cast; rfl
  rw [heπ,←Complex.ofReal_log hπ.le,Real.log_pow]
  congr 1
  push_cast
  ring

theorem bblrVStar_mellinConvergent {s : ℂ} (hs : 0<s.re)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    MellinConvergent (bblrVStar G) s := by
  have hc := (MellinConvergent.comp_mul_left (show 0<(2*Real.pi)^2 by positivity)).mpr
    (a03ZeroModeRatioPartition_mellinConvergent hs G α hG)
  apply hc.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simp only [smul_eq_mul]
  rw [a03VStar_eq_ratio_scaled hx G]

theorem bblrVStar_hasMellin {s : ℂ} (hs : 0<s.re)
    (G : ℂ→ℂ) (α : MomentShifts) (hG : BBLREntireWeight G α) :
    HasMellin (bblrVStar G) s ((2*Real.pi:ℂ)^(-2*s)*(G s/s)) :=
  ⟨bblrVStar_mellinConvergent hs G α hG,bblrVStar_forwardMellin hs G α hG⟩

end
end Sechstmoment.Source
