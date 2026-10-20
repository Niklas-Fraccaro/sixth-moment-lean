import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Sechstmoment.Analysis.Profiles.Classes
import Sechstmoment.Analysis.Profiles.Endpoint


namespace Sechstmoment
open Set MeasureTheory Filter
open scoped Topology

noncomputable def uFixedBump : ContDiffBump (1/2 : ℝ) where
  rIn := 1/16
  rOut := 1/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

noncomputable def uNormalizedBump : ℝ → ℝ := uFixedBump.normed volume

theorem uNormalizedBump_contDiff : ContDiff ℝ (⊤ : ℕ∞) uNormalizedBump :=
  uFixedBump.contDiff_normed

theorem uNormalizedBump_nonneg (x : ℝ) : 0 ≤ uNormalizedBump x :=
  uFixedBump.nonneg_normed x

theorem uNormalizedBump_integrable : Integrable uNormalizedBump :=
  uFixedBump.integrable_normed

theorem uNormalizedBump_mass : (∫ x : ℝ, uNormalizedBump x) = 1 :=
  uFixedBump.integral_normed

theorem uNormalizedBump_hasCompactSupport : HasCompactSupport uNormalizedBump :=
  uFixedBump.hasCompactSupport_normed

theorem uNormalizedBump_tsupport : tsupport uNormalizedBump ⊆ Icc (3/8) (5/8) := by
  intro x hx
  rw [uNormalizedBump, uFixedBump.tsupport_normed_eq] at hx
  have hb : |x-(1/2:ℝ)| ≤ 1/8 := by
    simpa [Metric.mem_closedBall, Real.dist_eq, uFixedBump] using hx
  rcases abs_le.mp hb with ⟨hl,hr⟩
  constructor <;> linarith

theorem uNormalizedBump_interior_support :
    tsupport uNormalizedBump ⊆ Ioo (1/4) (3/4) := by
  intro x hx
  rcases uNormalizedBump_tsupport hx with ⟨hl,hr⟩
  constructor <;> linarith

theorem uNormalizedBump_zero_outside {x : ℝ} (hx : x < 3/8 ∨ 5/8 < x) :
    uNormalizedBump x = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro h
  have hb := uNormalizedBump_tsupport h
  rcases hx with hx | hx
  · exact (not_le_of_gt hx) hb.1
  · exact (not_le_of_gt hx) hb.2

theorem uNormalizedBump_zero_nonpos {x : ℝ} (hx : x ≤ 0) :
    uNormalizedBump x = 0 :=
  uNormalizedBump_zero_outside (Or.inl (by linarith))

theorem uEndpointProfile_normalized_contDiff (hstar a : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (uEndpointProfile uNormalizedBump hstar a n) := by
  unfold uEndpointProfile
  exact contDiff_const.mul (uNormalizedBump_contDiff.comp (by fun_prop))

theorem uEndpointProfile_normalized_nonneg {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    0 ≤ uEndpointProfile uNormalizedBump hstar a n x := by
  unfold uEndpointProfile
  exact mul_nonneg (inv_nonneg.mpr (div_nonneg hh.le (by positivity)))
    (uNormalizedBump_nonneg _)

theorem uEndpointProfile_normalized_tsupport {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    tsupport (uEndpointProfile uNormalizedBump hstar a n) ⊆
      Icc (a-5/8*(hstar/n)) (a-3/8*(hstar/n)) := by
  have hpos : 0 < hstar/(n:ℝ) := div_pos hh (by exact_mod_cast hn)
  apply closure_minimal
  · intro x hx
    have hψ : uNormalizedBump ((a-x)/(hstar/n)) ≠ 0 := by
      intro hz
      exact hx (by simp [uEndpointProfile,hz])
    have hb := uNormalizedBump_tsupport (subset_tsupport _ hψ)
    change 3/8 ≤ (a-x)/(hstar/n) ∧ (a-x)/(hstar/n) ≤ 5/8 at hb
    have hl := (le_div_iff₀ hpos).mp hb.1
    have hr := (div_le_iff₀ hpos).mp hb.2
    constructor <;> linarith
  · exact isClosed_Icc

theorem uEndpointProfile_normalized_hasCompactSupport {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    HasCompactSupport (uEndpointProfile uNormalizedBump hstar a n) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (uEndpointProfile_normalized_tsupport hh a hn)

theorem uEndpointProfile_normalized_integrable {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    Integrable (uEndpointProfile uNormalizedBump hstar a n) :=
  (uEndpointProfile_normalized_contDiff hstar a n).continuous.integrable_of_hasCompactSupport
    (uEndpointProfile_normalized_hasCompactSupport hh a hn)

theorem uEndpointProfile_normalized_mass {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, uEndpointProfile uNormalizedBump hstar a n x) = 1 := by
  have hpos : 0 < hstar/(n:ℝ) := div_pos hh (by exact_mod_cast hn)
  unfold uEndpointProfile
  rw [integral_const_mul]
  have hsub := integral_sub_left_eq_self (fun x : ℝ =>
    uNormalizedBump (x/(hstar/n))) volume a
  rw [hsub, Measure.integral_comp_div, abs_of_pos hpos,
    smul_eq_mul, uNormalizedBump_mass, mul_one, inv_mul_cancel₀ hpos.ne']

theorem uEndpointProfile_normalized_interior {hstar a : ℝ} (hh : 0 < hstar)
    (hha : hstar < a) {n : ℕ} (hn : 0 < n) :
    SmoothInteriorProfile a (uEndpointProfile uNormalizedBump hstar a n) := by
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpos : 0 < hstar/(n:ℝ) := div_pos hh (by exact_mod_cast hn)
  have hle : hstar/(n:ℝ) ≤ hstar := by
    exact (div_le_iff₀ (by exact_mod_cast hn)).mpr (by nlinarith)
  refine ⟨uEndpointProfile_normalized_contDiff hstar a n,
    uEndpointProfile_normalized_hasCompactSupport hh a hn, ?_⟩
  intro x hx
  rcases uEndpointProfile_normalized_tsupport hh a hn hx with ⟨hl,hr⟩
  constructor <;> linarith

theorem uEndpointProfile_normalized_test_integral {hstar : ℝ} (hh : 0 < hstar)
    (a : ℝ) {n : ℕ} (hn : 0 < n) (g : ℝ → ℝ) :
    (∫ x : ℝ, g x * uEndpointProfile uNormalizedBump hstar a n x) =
      ∫ u : ℝ, g (a-(hstar/n)*u)*uNormalizedBump u := by
  let h : ℝ := hstar/n
  have hpos : 0 < h := div_pos hh (by exact_mod_cast hn)
  have he (x : ℝ) : g x * uEndpointProfile uNormalizedBump hstar a n x =
      h⁻¹*(g x*uNormalizedBump ((a-x)/h)) := by
    dsimp [uEndpointProfile,h]
    ring
  simp_rw [he]
  rw [integral_const_mul]
  have hr := integral_sub_left_eq_self
    (fun x : ℝ => g (a-x)*uNormalizedBump (x/h)) volume a
  have hc (x : ℝ) : a-(a-x)=x := by ring
  simp_rw [hc] at hr
  rw [hr]
  have hf (x : ℝ) : g (a-x)*uNormalizedBump (x/h) =
      (fun u : ℝ => g (a-h*u)*uNormalizedBump u) (x/h) := by
    congr 2
    field_simp
  simp_rw [hf]
  rw [Measure.integral_comp_div (fun u : ℝ => g (a-h*u)*uNormalizedBump u) h,
    abs_of_pos hpos,smul_eq_mul,
    ← mul_assoc,inv_mul_cancel₀ hpos.ne',one_mul]

theorem uEndpointProfile_normalized_width {hstar : ℝ} (hh : 0 < hstar) (n : ℕ) :
    0 ≤ hstar/(n:ℝ) ∧ hstar/(n:ℝ) ≤ hstar := by
  constructor
  · positivity
  · by_cases hn : n=0
    · simp [hn,hh.le]
    · have hn0 : 0 < n := Nat.pos_of_ne_zero hn
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn0
      exact (div_le_iff₀ (by exact_mod_cast hn0)).mpr (by nlinarith)

theorem uEndpointProfile_normalized_continuous_test_tendsto {hstar : ℝ}
    (hh : 0 < hstar) (a : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      g x*uEndpointProfile uNormalizedBump hstar a n x) atTop (𝓝 (g a)) := by
  have ht : Tendsto (fun n : ℕ => hstar/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn : ContinuousOn g (Icc (a-hstar) a))
  let M := max C 0
  have hbound (n : ℕ) (u : ℝ) :
      ‖g (a-(hstar/n)*u)*uNormalizedBump u‖ ≤ M*uNormalizedBump u := by
    by_cases hu : uNormalizedBump u=0
    · simp [hu]
    · have hb := uNormalizedBump_tsupport (subset_tsupport _ hu)
      have hw := uEndpointProfile_normalized_width hh n
      have hx : a-(hstar/n)*u ∈ Icc (a-hstar) a := by
        constructor <;> nlinarith [hb.1,hb.2,hw.1,hw.2]
      rw [norm_mul,Real.norm_eq_abs (uNormalizedBump u),
        abs_of_nonneg (uNormalizedBump_nonneg u)]
      exact mul_le_mul_of_nonneg_right ((hC _ hx).trans (le_max_left _ _))
        (uNormalizedBump_nonneg u)
  have hF := tendsto_integral_of_dominated_convergence
    (fun u : ℝ => M*uNormalizedBump u)
    (fun n => ((hg.comp (by fun_prop)).mul
      uNormalizedBump_contDiff.continuous).aestronglyMeasurable)
    (uNormalizedBump_integrable.const_mul M)
    (fun n => Filter.Eventually.of_forall (hbound n))
    (Filter.Eventually.of_forall (fun u =>
      ((hg.tendsto a).comp (by simpa using tendsto_const_nhds.sub (ht.mul_const u))).mul
        tendsto_const_nhds))
  have hlimit : (∫ u : ℝ, g a*uNormalizedBump u) = g a := by
    rw [integral_const_mul,uNormalizedBump_mass,mul_one]
  rw [hlimit] at hF
  apply hF.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact (uEndpointProfile_normalized_test_integral hh a hn g).symm

theorem uEndpointProfile_normalized_continuousOn_test_tendsto {hstar a : ℝ}
    (hh : 0 < hstar) (hha : hstar < a) (g : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (0:ℝ) a)) :
    Tendsto (fun n : ℕ => ∫ x : ℝ,
      g x*uEndpointProfile uNormalizedBump hstar a n x) atTop (𝓝 (g a)) := by
  have ha : 0 ≤ a := (hh.trans hha).le
  let G : ℝ → ℝ := fun x => g (min (max x 0) a)
  have hG : Continuous G := hg.comp_continuous
    ((continuous_id.max continuous_const).min continuous_const) (by
      intro x
      exact ⟨le_min (le_max_right _ _) ha,min_le_right _ _⟩)
  have hGa : G a=g a := by simp [G,max_eq_left ha]
  have he (n : ℕ) : (∫ x : ℝ, G x*uEndpointProfile uNormalizedBump hstar a n x) =
      ∫ x : ℝ, g x*uEndpointProfile uNormalizedBump hstar a n x := by
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hn : n=0
    · simp [hn,uEndpointProfile]
    · by_cases hx : uEndpointProfile uNormalizedBump hstar a n x=0
      · simp [hx]
      · have hb := (uEndpointProfile_normalized_interior hh hha
          (Nat.pos_of_ne_zero hn)).2.2 (subset_tsupport _ hx)
        simp [G,max_eq_left hb.1.le,min_eq_left hb.2.le]
  simpa only [he,hGa] using
    uEndpointProfile_normalized_continuous_test_tendsto hh a G hG

end Sechstmoment
