import Mathlib.MeasureTheory.Integral.Prod
import Sechstmoment.Certificate.Profiles.U.Definitions
import Sechstmoment.Numerator.Kernels.WeightedIntegral

/-! Actual two-profile weak concentration for the normalized U family and
its actual numerical numerator kernel. The affine Jacobians and compact
integrability are proved before the dominated-convergence step. -/

namespace Sechstmoment
open MeasureTheory Set Filter
open scoped Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

private theorem u_compact_product_integrable
    (f g : ℝ → ℝ) (F : ℝ × ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hF : Continuous F) (hfc : HasCompactSupport f) (hgc : HasCompactSupport g) :
    Integrable (fun z : ℝ × ℝ => f z.1*g z.2*F z) (volume.prod volume) := by
  have hc : Continuous (fun z : ℝ × ℝ => f z.1*g z.2*F z) :=
    ((hf.comp continuous_fst).mul (hg.comp continuous_snd)).mul hF
  apply hc.integrable_of_hasCompactSupport
  apply (hfc.prod hgc).of_isClosed_subset (isClosed_tsupport _) ?_
  apply closure_minimal
  · intro z hz
    have hfg := (mul_ne_zero_iff.mp hz).1
    exact ⟨subset_tsupport f (mul_ne_zero_iff.mp hfg).1,
      subset_tsupport g (mul_ne_zero_iff.mp hfg).2⟩
  · exact (isClosed_tsupport f).prod (isClosed_tsupport g)

/-- Genuine global integrability of the actual two-profile kernel. -/
theorem uEndpointProfile_normalized_two_test_integrable {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) {n : ℕ} (hn : 0 < n)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Integrable (fun z : ℝ × ℝ => uEndpointProfile uNormalizedBump hstar a n z.1*
      uEndpointProfile uNormalizedBump hstar b n z.2*F z) (volume.prod volume) :=
  u_compact_product_integrable _ _ F
    (uEndpointProfile_normalized_contDiff hstar a n).continuous
    (uEndpointProfile_normalized_contDiff hstar b n).continuous hF
    (uEndpointProfile_normalized_hasCompactSupport hh a hn)
    (uEndpointProfile_normalized_hasCompactSupport hh b hn)

/-- The product integral and the actual iterated integral agree by Fubini. -/
theorem uEndpointProfile_normalized_two_test_fubini {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) {n : ℕ} (hn : 0 < n)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    (∫ z : ℝ × ℝ, uEndpointProfile uNormalizedBump hstar a n z.1*
      uEndpointProfile uNormalizedBump hstar b n z.2*F z ∂(volume.prod volume)) =
      ∫ x : ℝ, ∫ y : ℝ, uEndpointProfile uNormalizedBump hstar a n x*
        uEndpointProfile uNormalizedBump hstar b n y*F (x,y) :=
  integral_prod _ (uEndpointProfile_normalized_two_test_integrable hh a b hn F hF)

/-- The actual affine substitutions have their exact Jacobians on both
coordinates. No identity or integrability of the resulting kernel is assumed. -/
theorem uEndpointProfile_normalized_two_test_affine {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) {n : ℕ} (hn : 0 < n) (F : ℝ × ℝ → ℝ) :
    (∫ x : ℝ, ∫ y : ℝ, uEndpointProfile uNormalizedBump hstar a n x*
      uEndpointProfile uNormalizedBump hstar b n y*F (x,y)) =
      ∫ u : ℝ, ∫ v : ℝ, uNormalizedBump u*uNormalizedBump v*
        F (a-(hstar/n)*u,b-(hstar/n)*v) := by
  have hin (x : ℝ) : (∫ y : ℝ, uEndpointProfile uNormalizedBump hstar a n x*
      uEndpointProfile uNormalizedBump hstar b n y*F (x,y)) =
      uEndpointProfile uNormalizedBump hstar a n x*
        ∫ v : ℝ, F (x,b-(hstar/n)*v)*uNormalizedBump v := by
    have he (y : ℝ) : uEndpointProfile uNormalizedBump hstar a n x*
        uEndpointProfile uNormalizedBump hstar b n y*F (x,y) =
        uEndpointProfile uNormalizedBump hstar a n x*
          (F (x,y)*uEndpointProfile uNormalizedBump hstar b n y) := by ring
    simp_rw [he]
    rw [integral_const_mul, uEndpointProfile_normalized_test_integral hh b hn]
  simp_rw [hin]
  have he (x : ℝ) : uEndpointProfile uNormalizedBump hstar a n x*
      (∫ v : ℝ, F (x,b-(hstar/n)*v)*uNormalizedBump v) =
      (∫ v : ℝ, F (x,b-(hstar/n)*v)*uNormalizedBump v)*
        uEndpointProfile uNormalizedBump hstar a n x := by ring
  simp_rw [he]
  rw [uEndpointProfile_normalized_test_integral hh a hn]
  apply integral_congr_ae
  filter_upwards [] with u
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards [] with v
  ring

private theorem u_two_affine_integrable (hstar a b : ℝ) (n : ℕ)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Integrable (fun z : ℝ × ℝ => uNormalizedBump z.1*uNormalizedBump z.2*
      F (a-(hstar/n)*z.1,b-(hstar/n)*z.2)) (volume.prod volume) :=
  u_compact_product_integrable _ _ _ uNormalizedBump_contDiff.continuous
    uNormalizedBump_contDiff.continuous (hF.comp (by fun_prop))
    uNormalizedBump_hasCompactSupport uNormalizedBump_hasCompactSupport

/-- A common fixed normalized product bump expresses the actual iterated
profile integral as a single product-measure integral. -/
theorem uEndpointProfile_normalized_two_test_affine_prod {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) {n : ℕ} (hn : 0 < n)
    (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    (∫ x : ℝ, ∫ y : ℝ, uEndpointProfile uNormalizedBump hstar a n x*
      uEndpointProfile uNormalizedBump hstar b n y*F (x,y)) =
      ∫ z : ℝ × ℝ, uNormalizedBump z.1*uNormalizedBump z.2*
        F (a-(hstar/n)*z.1,b-(hstar/n)*z.2) ∂(volume.prod volume) := by
  rw [uEndpointProfile_normalized_two_test_affine hh a b hn]
  exact (integral_prod _ (u_two_affine_integrable hstar a b n F hF)).symm

/-- Genuine two-profile concentration follows from the exact affine
substitution and a fixed compact normalized product bump. -/
theorem uEndpointProfile_normalized_two_test_tendsto {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) (F : ℝ × ℝ → ℝ) (hF : Continuous F) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, ∫ y : ℝ,
      uEndpointProfile uNormalizedBump hstar a n x*
      uEndpointProfile uNormalizedBump hstar b n y*F (x,y)) atTop (𝓝 (F (a,b))) := by
  have ht : Tendsto (fun n : ℕ => hstar/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn
    (hF.continuousOn : ContinuousOn F ((Icc (a-hstar) a) ×ˢ (Icc (b-hstar) b)))
  let M : ℝ := max C 0
  have hbound (n : ℕ) (z : ℝ × ℝ) :
      ‖uNormalizedBump z.1*uNormalizedBump z.2*
        F (a-(hstar/n)*z.1,b-(hstar/n)*z.2)‖ ≤
        M*uNormalizedBump z.1*uNormalizedBump z.2 := by
    by_cases hu : uNormalizedBump z.1=0
    · simp [hu]
    by_cases hv : uNormalizedBump z.2=0
    · simp [hv]
    have hbU := uNormalizedBump_tsupport (subset_tsupport _ hu)
    have hbV := uNormalizedBump_tsupport (subset_tsupport _ hv)
    have hw := uEndpointProfile_normalized_width hh n
    have ha : a-(hstar/n)*z.1 ∈ Icc (a-hstar) a := by
      constructor <;> nlinarith [hbU.1,hbU.2,hw.1,hw.2]
    have hb : b-(hstar/n)*z.2 ∈ Icc (b-hstar) b := by
      constructor <;> nlinarith [hbV.1,hbV.2,hw.1,hw.2]
    have hf := (hC (a-(hstar/n)*z.1,b-(hstar/n)*z.2) ⟨ha,hb⟩).trans (le_max_left C 0)
    have hp := mul_nonneg (uNormalizedBump_nonneg z.1) (uNormalizedBump_nonneg z.2)
    rw [norm_mul,norm_mul,Real.norm_eq_abs (uNormalizedBump z.1),
      Real.norm_eq_abs (uNormalizedBump z.2),abs_of_nonneg (uNormalizedBump_nonneg z.1),
      abs_of_nonneg (uNormalizedBump_nonneg z.2)]
    calc
      _ ≤ (uNormalizedBump z.1*uNormalizedBump z.2)*M := mul_le_mul_of_nonneg_left hf hp
      _ = _ := by ring
  have hi : Integrable (fun z : ℝ × ℝ => M*uNormalizedBump z.1*uNormalizedBump z.2)
      (volume.prod volume) := by
    simpa only [mul_assoc] using (uNormalizedBump_integrable.mul_prod
      uNormalizedBump_integrable).const_mul M
  have hm (n : ℕ) : AEStronglyMeasurable (fun z : ℝ × ℝ =>
      uNormalizedBump z.1*uNormalizedBump z.2*
        F (a-(hstar/n)*z.1,b-(hstar/n)*z.2)) (volume.prod volume) := by
    have hf : Continuous (fun z : ℝ × ℝ => F (a-(hstar/n)*z.1,b-(hstar/n)*z.2)) :=
      hF.comp (by fun_prop)
    exact (((uNormalizedBump_contDiff.continuous.comp continuous_fst).mul
      (uNormalizedBump_contDiff.continuous.comp continuous_snd)).mul hf).aestronglyMeasurable
  have hp (z : ℝ × ℝ) : Tendsto (fun n : ℕ =>
      uNormalizedBump z.1*uNormalizedBump z.2*
        F (a-(hstar/n)*z.1,b-(hstar/n)*z.2)) atTop
        (𝓝 (uNormalizedBump z.1*uNormalizedBump z.2*F (a,b))) := by
    have ha : Tendsto (fun n : ℕ => a-(hstar/n)*z.1) atTop (𝓝 a) := by
      simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (ht.mul_const z.1)
    have hb : Tendsto (fun n : ℕ => b-(hstar/n)*z.2) atTop (𝓝 b) := by
      simpa only [zero_mul,sub_zero] using tendsto_const_nhds.sub (ht.mul_const z.2)
    exact tendsto_const_nhds.mul ((hF.tendsto (a,b)).comp (ha.prodMk_nhds hb))
  have hD := tendsto_integral_of_dominated_convergence
    (fun z : ℝ × ℝ => M*uNormalizedBump z.1*uNormalizedBump z.2) hm hi
    (fun n => Filter.Eventually.of_forall (hbound n)) (Filter.Eventually.of_forall hp)
  have hlimit : (∫ z : ℝ × ℝ, uNormalizedBump z.1*uNormalizedBump z.2*F (a,b)
      ∂(volume.prod volume)) = F (a,b) := by
    rw [integral_mul_const,integral_prod_mul,uNormalizedBump_mass]
    ring
  rw [hlimit] at hD
  apply hD.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact (uEndpointProfile_normalized_two_test_affine_prod hh a b hn F hF).symm

/-- Integrability of the actual numerical numerator kernel with both
literal normalized U profiles, including coincident endpoints. -/
theorem u_numerator_profile_integrable (p : Fin 5 → ℝ) {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun z : ℝ × ℝ => uEndpointProfile uNormalizedBump hstar a n z.1*
      uEndpointProfile uNormalizedBump hstar b n z.2*numeratorPointKernel p z.1 z.2)
      (volume.prod volume) :=
  uEndpointProfile_normalized_two_test_integrable hh a b hn _
    (numeratorPointKernel_joint_continuous p)

/-- The actual U two-profile numerator integral has a justified interchange
of its two ordinary Lebesgue integrals. -/
theorem u_numerator_profile_integral_swap (p : Fin 5 → ℝ) {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) {n : ℕ} (hn : 0 < n) :
    (∫ x : ℝ, ∫ y : ℝ, uEndpointProfile uNormalizedBump hstar a n x*
      uEndpointProfile uNormalizedBump hstar b n y*numeratorPointKernel p x y) =
      ∫ y : ℝ, ∫ x : ℝ, uEndpointProfile uNormalizedBump hstar a n x*
        uEndpointProfile uNormalizedBump hstar b n y*numeratorPointKernel p x y :=
  integral_integral_swap (u_numerator_profile_integrable p hh a b hn)

/-- The literal normalized U pair weakly recovers the actual simplex
numerator. Global joint continuity also covers coincident endpoints; for
admissible manuscript profiles one additionally chooses hstar < min a b. -/
theorem u_numerator_profile_tendsto (p : Fin 5 → ℝ) {hstar : ℝ}
    (hh : 0 < hstar) (a b : ℝ) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, ∫ y : ℝ,
      uEndpointProfile uNormalizedBump hstar a n x*
      uEndpointProfile uNormalizedBump hstar b n y*numeratorPointKernel p x y)
      atTop (𝓝 (numeratorPointKernel p a b)) :=
  uEndpointProfile_normalized_two_test_tendsto hh a b _ (numeratorPointKernel_joint_continuous p)

/-- The original certificate rows of U type, with their original weights. -/
def uCertificateRows : List TestDatum :=
  certificate.filter (fun d => decide (d.typ = .U))

theorem mem_uCertificateRows (d : TestDatum) :
    d ∈ uCertificateRows ↔ d ∈ certificate ∧ d.typ = .U := by simp [uCertificateRows]

/-- The actual U numerator subset contains 220 of the 250 original rows. -/
theorem uCertificateRows_length : uCertificateRows.length = 220 := by decide +kernel

/-- The scalar numerator obtained from the actual common normalized profile
family on every original U row. -/
def uCertificateProfileNumerator (n : ℕ) : ℝ :=
  (uCertificateRows.map (fun d => (d.coefficient:ℝ)*
    ∫ x : ℝ, ∫ y : ℝ,
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/(Finite.base:ℝ)) n x*
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/(Finite.base:ℝ)) n y*
      numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val:ℝ)) x y)).sum

/-- The actual endpoint numerator sum for the original U certificate subset. -/
def uCertificatePointNumerator : ℝ :=
  (uCertificateRows.map (fun d => (d.coefficient:ℝ)*
    numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val:ℝ))
      ((d.A:ℝ)/(Finite.base:ℝ)) ((d.B:ℝ)/(Finite.base:ℝ)))).sum

/-- Every one of the original U rows has its actual two-profile limit; no
asymptotic zeta-moment reconstruction is postulated here. -/
theorem certificate_uProfile_numerator_tendsto (d : TestDatum) :
    Tendsto (fun n : ℕ => ∫ x : ℝ, ∫ y : ℝ,
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.A:ℝ)/(Finite.base:ℝ)) n x*
      uEndpointProfile uNormalizedBump uCertificateHstar ((d.B:ℝ)/(Finite.base:ℝ)) n y*
      numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val:ℝ)) x y)
      atTop (𝓝 (numeratorPointKernel (fun r => (Finite.coef (Finite.cheb d.degree) r.val:ℝ))
        ((d.A:ℝ)/(Finite.base:ℝ)) ((d.B:ℝ)/(Finite.base:ℝ)))) :=
  u_numerator_profile_tendsto _ uCertificateHstar_pos _ _

/-- Finite summation closes the actual common-profile numerator limit for
all 220 original U rows, retaining every original coefficient. -/
theorem uCertificateProfileNumerator_tendsto :
    Tendsto uCertificateProfileNumerator atTop (𝓝 uCertificatePointNumerator) := by
  unfold uCertificateProfileNumerator uCertificatePointNumerator
  apply tendsto_list_sum
  intro d _
  exact (certificate_uProfile_numerator_tendsto d).const_mul (d.coefficient:ℝ)

/-- The endpoint sum is exactly the U part of the original certified
feature kernel, with the actual datumFeature conversion. -/
theorem uCertificatePointNumerator_eq_original_subset :
    uCertificatePointNumerator =
      (uCertificateRows.map (fun d => numeratorFeatureKernel (datumFeature d))).sum := by
  apply congrArg List.sum
  apply List.map_congr_left
  intro d hd
  have hm := List.mem_filter.mp hd
  have ht : d.typ = TestType.U := by simpa using hm.2
  rw [datumFeatureKernel_weighted hm.1]
  simp [numeratorSecondMass, datumFeature, ht]

end
end Sechstmoment
