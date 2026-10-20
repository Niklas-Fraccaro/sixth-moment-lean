import SixthMoment.Numerator.U.ZeroModes.Ratio.FullVStarNative

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

def a03RatioLeadingExponent (dual : Bool) (T : ℝ) (σ : MomentShifts) : ℂ :=
  if dual then -∑ j : Fin 4,rawMomentShifts T σ j else 0

def a03RatioLeadingScalar (dual : Bool) (T : ℝ) (σ : MomentShifts) : ℂ :=
  (T/(2*Real.pi):ℂ)^(a03RatioLeadingExponent dual T σ)

theorem a03PositiveComplexPower_contDiffAt (ρ : ℂ) {t : ℝ} (ht : 0<t) :
    ContDiffAt ℝ ∞ (fun u : ℝ => (u:ℂ)^ρ) t := by
  have he : (fun u : ℝ => (u:ℂ)^ρ)=ᶠ[𝓝 t]
      fun u : ℝ => Complex.exp ((Real.log u:ℂ)*ρ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (show u≠0 from hu.ne')),
      ←Complex.ofReal_log (show 0≤u from hu.le)]
  have hlog : ContDiffAt ℝ ∞ (fun u : ℝ => (Real.log u:ℂ)) t :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp t (Real.contDiffAt_log.mpr ht.ne')
  have hmul : ContDiffAt ℝ ∞ (fun u : ℝ => (Real.log u:ℂ)*ρ) t :=
    hlog.mul contDiffAt_const
  exact (Complex.contDiff_exp.contDiffAt.comp t
    hmul).congr_of_eventuallyEq he

theorem bblrDualLeadingMultiplier_contDiffAt {T : ℝ} (hT : 0<T)
    (σ : MomentShifts) {t : ℝ} (ht : 0<t) :
    ContDiffAt ℝ ∞ (bblrDualLeadingMultiplier T σ) t := by
  have hp : 0<T*t/(2*Real.pi) := by positivity
  have h := (a03PositiveComplexPower_contDiffAt (-∑j : Fin 4,rawMomentShifts T σ j) hp).comp t
    (show ContDiffAt ℝ ∞ (fun u : ℝ => T*u/(2*Real.pi)) t by fun_prop)
  convert h using 1
  funext u
  unfold bblrDualLeadingMultiplier
  simp only [Function.comp_def,Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat]

theorem a03RatioLeadingBranchProfile_contDiff {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts) (dual : Bool) :
    ContDiff ℝ ∞ (a03RatioLeadingBranchProfile dual Φ T σ) := by
  cases dual
  · exact hΦ
  · apply a03_profile_product_contDiff hΦ
    intro t ht
    exact bblrDualLeadingMultiplier_contDiffAt hT σ (zero_lt_one.trans_le (hSupp ht).1)

theorem a03RatioLeadingBranchProfile_eq_scalar_power {Φ : ℝ→ℂ}
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T)
    (σ : MomentShifts) (dual : Bool) :
    a03RatioLeadingBranchProfile dual Φ T σ=fun t : ℝ =>
      a03RatioLeadingScalar dual T σ*a03ProfileProduct Φ
        (fun t : ℝ => (t:ℂ)^(a03RatioLeadingExponent dual T σ)) t := by
  funext t
  cases dual
  · simp [a03RatioLeadingBranchProfile,a03RatioLeadingScalar,a03RatioLeadingExponent,a03ProfileProduct]
  · by_cases ht : Φ t=0
    · simp [a03RatioLeadingBranchProfile,a03ProfileProduct,ht]
    · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
      have hP : 0<T/(2*Real.pi) := by positivity
      have he : (T*t/(2*Real.pi):ℂ)=(T/(2*Real.pi):ℂ)*(t:ℂ) := by ring
      simp only [a03RatioLeadingBranchProfile,ite_true,a03RatioLeadingScalar,a03RatioLeadingExponent,a03ProfileProduct]
      unfold bblrDualLeadingMultiplier
      have hpow := Complex.mul_cpow_ofReal_nonneg hP.le htp.le (-∑j : Fin 4,rawMomentShifts T σ j)
      push_cast at hpow
      rw [he,hpow]
      ring

theorem a03RatioLeadingExponent_uniform_eventually_small (K : Set MomentShifts)
    (hK : IsCompact K) :
    ∀ᶠ T : ℝ in atTop,∀σ∈K,∀dual : Bool,‖a03RatioLeadingExponent dual T σ‖≤1 := by
  obtain ⟨B,hB⟩ := hK.isBounded.exists_norm_le
  let R := max B 0
  have hR : 0≤R := le_max_right _ _
  filter_upwards [rawMomentShifts_uniform_eventually_small hR (by norm_num : (0:ℝ)<1/4)] with T hb
  intro σ hσ dual
  have hσR (j : Fin 4) : ‖σ j‖≤R := ((norm_le_pi_norm σ j).trans (hB σ hσ)).trans (le_max_left _ _)
  have hs := hb σ hσR
  cases dual
  · simp [a03RatioLeadingExponent]
  · simp only [a03RatioLeadingExponent,ite_true,norm_neg]
    calc
      _≤∑j : Fin 4,‖rawMomentShifts T σ j‖ := norm_sum_le _ _
      _≤∑_j : Fin 4,(1/4:ℝ) := Finset.sum_le_sum (fun j _ => hs j)
      _=1 := by norm_num

theorem a03RatioLeadingScalar_uniform_eventually_bound (K : Set MomentShifts)
    (hK : IsCompact K) :
    ∃ D : ℝ,0≤D ∧ ∀ᶠ T : ℝ in atTop,∀σ∈K,∀dual : Bool,
      ‖a03RatioLeadingScalar dual T σ‖≤D := by
  obtain ⟨D,hD,hbound⟩ := bblrDualLeadingMultiplier_uniform_normalized_bound K hK
  refine ⟨max D 1,by positivity,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (0:ℝ)] with T hb hT
  intro σ hσ dual
  cases dual
  · change ‖(T/(2*Real.pi):ℂ)^(0:ℂ)‖≤max D 1
    rw [Complex.cpow_zero,norm_one]
    exact le_max_right _ _
  · have he := hb σ hσ T ⟨le_rfl,by linarith⟩
    have hTT : T/T=(1:ℝ) := div_self hT.ne'
    rw [hTT] at he
    have hbnd : ‖a03RatioLeadingScalar true T σ‖≤D := by
      simpa only [a03RatioLeadingScalar,a03RatioLeadingExponent,ite_true,
        bblrDualLeadingMultiplier,Complex.ofReal_one,mul_one] using he
    exact hbnd.trans (le_max_left _ _)

end
end SixthMoment
