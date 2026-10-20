import SixthMoment.Numerator.U.Replacement.VStar.PowerTimeFourier
import SixthMoment.Numerator.U.ZeroModes.RatioTimeFourierDecay

namespace SixthMoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def a03VStarPowerXEnvelope (c Y x : ℝ) : ℝ := min 1 ((Y/x)^(2*c))

theorem a03VStarPowerXEnvelope_nonneg {c Y x : ℝ} (hY : 0≤Y) (hx : 0<x) :
    0≤a03VStarPowerXEnvelope c Y x := by
  unfold a03VStarPowerXEnvelope
  exact le_min zero_le_one (Real.rpow_nonneg (div_nonneg hY hx.le) _)

theorem a03VStarPowerXEnvelope_near {c Y x : ℝ} (hc : 0≤c) (hx : 0<x) (hxy : x≤Y) :
    a03VStarPowerXEnvelope c Y x=1 := by
  apply min_eq_left
  exact Real.one_le_rpow (by exact (le_div_iff₀ hx).mpr (by simpa using hxy)) (by positivity)

theorem a03VStarPowerXEnvelope_far {c Y x : ℝ} (hc : 0≤c) (hY : 0≤Y) (hxy : Y<x) :
    a03VStarPowerXEnvelope c Y x=(Y/x)^(2*c) := by
  apply min_eq_right
  exact Real.rpow_le_one (div_nonneg hY (hY.trans hxy.le))
    ((div_le_iff₀ (hY.trans_lt hxy)).mpr (by simpa using hxy.le)) (by positivity)

theorem a03VStarSpatialLog_positive_exp_bound {c Y x : ℝ}
    (hc : 0≤c) (hY : 0<Y) (hx : 0<x) :
    Real.exp (-c*a03VStarSpatialLog Y x)≤(Y/x)^(2*c) := by
  have hP : 1≤(2*Real.pi)^2 := by nlinarith only [Real.pi_gt_three]
  have hbase : 0<(2*Real.pi)^2*x^2/Y^2 := by positivity
  have hratio : 0<(x/Y)^2 := by positivity
  have hlower : (x/Y)^2≤(2*Real.pi)^2*x^2/Y^2 := by
    have hh := mul_le_mul_of_nonneg_right hP (sq_nonneg (x/Y))
    convert hh using 1 <;> ring
  have hlog := Real.log_le_log hratio hlower
  have he : Real.exp (-c*Real.log ((x/Y)^2))=(Y/x)^(2*c) := by
    rw [Real.log_pow,Real.log_div hx.ne' hY.ne',Real.rpow_def_of_pos (by positivity)]
    congr 1
    rw [Real.log_div hY.ne' hx.ne']
    ring
  exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hlog (by linarith))).trans_eq he

theorem a03VStarPowerTimeFourier_uniform_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R : ℝ} (hc : 0<c) (hR : 0≤R) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,∀ Y x ξ : ℝ,0<Y → 0<x →
      ∀ ρ : ℂ,‖ρ‖≤R →
      (1+|ξ|)^N*‖a03VStarPowerTimeFourier Φ T σ Y x ξ ρ‖≤
        C*(1+polarGaussianConstant T σ 1+polarGaussianConstant T σ c)*
          a03VStarPowerXEnvelope c Y x := by
  obtain ⟨Cp,hCp,hpos⟩ := a03RatioTimeFourierContour_uniform_frequency_decay hΦ hSupp hc hR (-2) N
  obtain ⟨Cn,hCn,hneg⟩ := a03RatioTimeFourierContour_uniform_frequency_decay hΦ hSupp
    (c:=1) (by norm_num) hR 2 N
  obtain ⟨C₀,hC₀,hplain⟩ := a03TimePowerProfile_fourier_decay hΦ hSupp hR N
  let P : ℝ := (2*Real.pi)^2
  let D : ℝ := C₀*(1+R)^N
  let C : ℝ := D+Cn*P+Cp
  have hP : 0≤P := by dsimp [P]; positivity
  have hD : 0≤D := by dsimp [D]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro T σ Y x ξ hY hx ρ hρ
  have hCG₁ := polarGaussianConstant_nonneg T σ 1
  have hCGc := polarGaussianConstant_nonneg T σ c
  have hheight : 0≤(1+|ξ|)^N := by positivity
  have hpl := hplain ρ ((Complex.re_le_norm ρ).trans hρ) ξ
  have hpl' : (1+|ξ|)^N*‖profileLaplaceTransform
      (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^ρ)) ((ξ:ℂ)*I)‖≤D := by
    exact hpl.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hρ]) N) hC₀)
  by_cases hxy : x≤Y
  · rw [a03VStarPowerXEnvelope_near hc.le hx hxy,mul_one]
    have he : Real.exp (a03VStarSpatialLog Y x)≤P := by
      unfold a03VStarSpatialLog
      rw [Real.exp_log (by positivity : 0<(2*Real.pi)^2*x^2/Y^2)]
      have hd : 0≤x/Y := by positivity
      have hd1 : x/Y≤1 := (div_le_iff₀ hY).mpr (by simpa using hxy)
      have hs : (x/Y)^2≤1 := by nlinarith only [hd,hd1]
      convert mul_le_mul_of_nonneg_left hs hP using 1 <;> dsimp [P] <;> ring
    have hn := hneg T σ (-a03VStarSpatialLog Y x) ξ ρ hρ
    simp only [neg_mul,one_mul,neg_neg] at hn
    rw [a03VStarPowerTimeFourier_eq_reflected hΦ.continuous hSupp hY hx T σ ξ ρ]
    calc
      _≤(1+|ξ|)^N*(‖profileLaplaceTransform (a03ProfileProduct Φ (fun t : ℝ => (t:ℂ)^ρ)) ((ξ:ℂ)*I)‖+
        ‖a03RatioTimeFourierContour Φ T σ 1 (-a03VStarSpatialLog Y x) 2 ξ ρ‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) hheight
      _≤D+Cn*polarGaussianConstant T σ 1*P := by
        rw [mul_add]
        exact add_le_add hpl' (hn.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hCn hCG₁)))
      _≤_ := by
        dsimp only [C]
        nlinarith only [hD,mul_nonneg hCn hP,hCp,hCG₁,hCGc,
          mul_nonneg hD hCG₁,mul_nonneg hD hCGc,
          mul_nonneg (mul_nonneg hCn hP) hCGc,mul_nonneg hCp hCG₁,mul_nonneg hCp hCGc]
  · have hxy' : Y<x := lt_of_not_ge hxy
    rw [a03VStarPowerXEnvelope_far hc.le hY.le hxy',
      a03VStarPowerTimeFourier_eq_positive hΦ.continuous hSupp hY hx hc T σ ξ ρ]
    have hp := hpos T σ (a03VStarSpatialLog Y x) ξ ρ hρ
    have he := a03VStarSpatialLog_positive_exp_bound hc.le hY hx
    calc
      _≤Cp*polarGaussianConstant T σ c*((Y/x)^(2*c)) :=
        hp.trans (mul_le_mul_of_nonneg_left he (mul_nonneg hCp hCGc))
      _≤_ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
        have hcoef : Cp≤C := by dsimp only [C]; linarith only [hD,mul_nonneg hCn hP]
        exact (mul_le_mul_of_nonneg_right hcoef hCGc).trans
          (mul_le_mul_of_nonneg_left (by linarith only [hCG₁] : polarGaussianConstant T σ c≤1+polarGaussianConstant T σ 1+polarGaussianConstant T σ c) hC)

theorem a03VStarPowerTimeFourier_uniform_log_envelope {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {c R κ : ℝ} (hc : 0<c) (hR : 0≤R) (hκ : 0<κ) (N : ℕ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ Y x ξ : ℝ,0<Y → 0<x → ∀ ρ : ℂ,‖ρ‖≤R →
      (1+|ξ|)^N*‖a03VStarPowerTimeFourier Φ T σ Y x ξ ρ‖≤
        C*(Real.log T)^48*a03VStarPowerXEnvelope c Y x := by
  obtain ⟨D,hD,hbound⟩ := a03VStarPowerTimeFourier_uniform_envelope hΦ hSupp hc hR N
  let B : ℝ := Real.exp 1*2^48*(1+1/κ^2)^24
  let E : ℝ := Real.exp (c^2)*(1+|c|)^48*(1+1/κ^2)^24
  refine ⟨D*(1+B+E),by dsimp [B,E]; positivity,?_⟩
  intro T hT hL σ hroot Y x ξ hY hx ρ hρ
  have h₁ := polarGaussianConstant_log_growth hT hL hκ σ 1 hroot
  have hc' := polarGaussianConstant_log_growth hT hL hκ σ c hroot
  have hLpow : 1≤(Real.log T)^48 := one_le_pow₀ hL
  have hCG : 1+polarGaussianConstant T σ 1+polarGaussianConstant T σ c≤(1+B+E)*(Real.log T)^48 := by
    norm_num only [one_pow,abs_one,one_add_one_eq_two] at h₁
    have h₁' : polarGaussianConstant T σ 1≤B*(Real.log T)^48 := by
      simpa only [B,show (2:ℝ)^48=281474976710656 by norm_num] using h₁
    have hc'' : polarGaussianConstant T σ c≤E*(Real.log T)^48 := hc'
    calc
      _≤(Real.log T)^48+B*(Real.log T)^48+E*(Real.log T)^48 :=
        add_le_add (add_le_add hLpow h₁') hc''
      _=_ := by ring
  exact (hbound T σ Y x ξ hY hx ρ hρ).trans
    ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCG hD)
      (a03VStarPowerXEnvelope_nonneg hY.le hx)).trans_eq (by ring))

end
end SixthMoment
