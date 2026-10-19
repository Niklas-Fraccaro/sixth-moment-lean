import Sechstmoment.Numerator.U.Replacement.VStar.PhysicalTimeFubini

/-! The literal finite spectral window and its actual complementary tail
are interchanged with time through a proved absolute product majorant. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03PhysicalLeadingVerticalSet (c T : ℝ) (σ α : MomentShifts) (Q : Fin 4→ℝ)
    (t : ℝ) (S : Set ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ in S,a03PhysicalLeadingTimeAmplitude T σ α Q ((c:ℂ)+(v:ℂ)*I) t

def a03PhysicalLeadingFourierSet (Φ : ℝ→ℂ) (c T : ℝ) (σ α : MomentShifts)
    (Q : Fin 4→ℝ) (ξ : ℝ) (S : Set ℝ) : ℂ :=
  (1/(2*Real.pi):ℂ)*∫v : ℝ in S,∫t : ℝ,a03PhysicalLeadingTimeKernel Φ T σ α Q ξ c v t

theorem a03PhysicalLeadingFourierSet_time_eq {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T c : ℝ} (hT : 0<T) (hc : 0<c)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (ξ : ℝ) (S : Set ℝ) :
    a03PhysicalLeadingFourierSet Φ c T σ α Q ξ S=
      ∫t : ℝ,Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*a03PhysicalLeadingVerticalSet c T σ α Q t S := by
  have hj := a03PhysicalLeadingTimeKernel_joint_integrable hΦ hSupp hT hc σ α Q hQ ξ
  have hjs : Integrable (Function.uncurry (a03PhysicalLeadingTimeKernel Φ T σ α Q ξ c))
      ((volume.restrict S).prod volume) := hj.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  unfold a03PhysicalLeadingFourierSet
  rw [integral_integral_swap hjs,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  unfold a03PhysicalLeadingTimeKernel a03PhysicalLeadingVerticalSet
  rw [integral_const_mul]
  ring

theorem a03PhysicalLeadingFourierTail_norm_le {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T c L : ℝ} (hT : 0<T) (hc : 0<c) (hL : 0≤L)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (ξ : ℝ) :
    ‖a03PhysicalLeadingFourierSet Φ c T σ α Q ξ {v : ℝ | L < |v|}‖≤
      (‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
        (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        (a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c)*Real.exp (-(1/2)*L^2))*
          ∫t : ℝ,‖Φ t‖ := by
  let B : ℝ := ‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
    (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
    (a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c)*Real.exp (-(1/2)*L^2)
  have hP : 0<a03PhysicalQuadProduct Q := Finset.prod_pos (fun j _ => hQ j)
  have hGauss := gaussianTailConstant_nonneg 48
  have hCG := polarGaussianConstant_nonneg T σ c
  have hB : 0≤B := by dsimp [B]; positivity
  have hFK : HasCompactSupport Φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hSupp
  have hFi : Integrable Φ volume := hΦ.integrable_of_hasCompactSupport hFK
  rw [a03PhysicalLeadingFourierSet_time_eq hΦ hSupp hT hc σ α Q hQ ξ]
  have hb : ∀t : ℝ,‖Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*
      a03PhysicalLeadingVerticalSet c T σ α Q t {v : ℝ | L < |v|}‖≤B*‖Φ t‖ := by
    intro t
    by_cases ht : Φ t=0
    · simp [ht]
    · have hts := hSupp (subset_tsupport _ ht)
      have htail := a03PhysicalLeadingVerticalTail_gaussian_bound hT hts hc hL σ α Q hQ
      rw [norm_mul,norm_mul,Complex.norm_exp]
      have hre : ((((-ξ:ℝ):ℂ)*I)*(t:ℂ)).re=0 := by simp
      rw [hre,Real.exp_zero,one_mul]
      exact (mul_le_mul_of_nonneg_left htail (norm_nonneg _)).trans_eq (mul_comm _ _)
  have hm := norm_integral_le_of_norm_le (hFi.norm.const_mul B) (Eventually.of_forall hb)
  exact hm.trans_eq (by rw [integral_const_mul])


theorem a03PhysicalLeadingFourierCore_add_tail {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T c : ℝ} (hT : 0<T) (hc : 0<c)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (ξ L : ℝ) :
    a03PhysicalLeadingFourierSet Φ c T σ α Q ξ (Icc (-L) L)+
      a03PhysicalLeadingFourierSet Φ c T σ α Q ξ {v : ℝ | L < |v|}=
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        ∫t : ℝ,Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2) := by
  have hi := (a03PhysicalLeadingTimeKernel_joint_integrable hΦ hSupp hT hc σ α Q hQ ξ).integral_prod_left
  have hs : MeasurableSet {v : ℝ | L < |v|} := (isOpen_lt continuous_const continuous_abs).measurableSet
  have he := integral_add_compl hs hi
  have hset : {v : ℝ | L < |v|}ᶜ=Icc (-L) L := by
    ext v
    simp only [Set.mem_compl_iff,Set.mem_ofPred_eq,not_lt,Set.mem_Icc]
    exact abs_le
  rw [hset] at he
  simp only [Function.uncurry] at he
  unfold a03PhysicalLeadingFourierSet
  rw [←mul_add,add_comm,he]
  exact a03PhysicalLeadingTimeKernel_vertical_time_eq_VStar hΦ hSupp hT hc σ α Q hQ ξ

theorem a03PhysicalLeadingFourierCore_sub_VStar_norm_le {Φ : ℝ→ℂ} (hΦ : Continuous Φ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T c L : ℝ} (hT : 0<T) (hc : 0<c) (hL : 0≤L)
    (σ α : MomentShifts) (Q : Fin 4→ℝ) (hQ : ∀ j,0<Q j) (ξ : ℝ) :
    ‖a03PhysicalLeadingFourierSet Φ c T σ α Q ξ (Icc (-L) L)-
      (a03ZeroModeRealQuadDenominator α 0 Q)⁻¹*
        (∫t : ℝ,Complex.exp (((-ξ:ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ) (a03PhysicalQuadProduct Q/(T*t)^2))‖≤
      (‖(a03ZeroModeRealQuadDenominator α 0 Q)⁻¹‖*
        (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        (a03PhysicalQuadProduct Q)^(-c)*(2*T)^(2*c)*Real.exp (-(1/2)*L^2))*
          ∫t : ℝ,‖Φ t‖ := by
  have he := a03PhysicalLeadingFourierCore_add_tail hΦ hSupp hT hc σ α Q hQ ξ L
  rw [←he,sub_add_eq_sub_sub,sub_self,zero_sub,norm_neg]
  exact a03PhysicalLeadingFourierTail_norm_le hΦ hSupp hT hc hL σ α Q hQ ξ

end
end Sechstmoment
