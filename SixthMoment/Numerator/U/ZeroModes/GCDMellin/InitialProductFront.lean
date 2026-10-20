import SixthMoment.Numerator.U.ZeroModes.GCDMellin.CountableJoint
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.FrontFubini

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModeGCDInitialKernel_product_eq_initialBlock
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)^3*(∫ p : A03GCDMellinCoordinates,
      a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) ∂a03GCDMellinMeasure)=
      verticalIntegral (1+ε) (fun s => a03ZeroModeRatioDoubleIntegral ε ε (fun u v =>
        ∫x : ℝ in Ioi 0,a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s)) := by
  let F : ℝ×(ℝ×(ℝ×ℝ))→ℂ := fun q => a03ZeroModeGCDInitialKernel Φ T σ α a b A B q.2.1
    ((ε:ℂ)+(q.2.2.1:ℂ)*I) ((ε:ℂ)+(q.2.2.2:ℂ)*I) (((1+ε:ℝ):ℂ)+(q.1:ℂ)*I)
  have hJoint : Integrable F (volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume))) :=
    a03ZeroModeGCDInitialKernel_joint_integrable_s_outer hΦ hSupp hT hε hε1 σ α hα ha hb A B
  have hRotate := a03GCDMellinRotate_measurePreserving.integral_comp' F
  change (∫p : A03GCDMellinCoordinates,a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
      (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) ∂a03GCDMellinMeasure)=
    ∫q : ℝ×(ℝ×(ℝ×ℝ)),F q ∂(volume.prod ((volume.restrict (Ioi 0)).prod (volume.prod volume))) at hRotate
  rw [hRotate]
  unfold verticalIntegral
  calc
    _=(1/(2*Real.pi):ℂ)*(∫y : ℝ,(1/(2*Real.pi):ℂ)^2*
      ∫q : ℝ×(ℝ×ℝ),F (y,q) ∂((volume.restrict (Ioi 0)).prod (volume.prod volume))) := by
      rw [integral_prod _ hJoint,integral_const_mul]
      ring
    _=_ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hJoint.prod_right_ae] with y hy
      have hAfter : Integrable (fun p : ℝ×ℝ => ∫x : ℝ in Ioi 0,
          a03ZeroModeGCDInitialKernel Φ T σ α a b A B x
            ((ε:ℂ)+(p.1:ℂ)*I) ((ε:ℂ)+(p.2:ℂ)*I) (((1+ε:ℝ):ℂ)+(y:ℂ)*I)) (volume.prod volume) :=
        hy.swap.integral_prod_left
      rw [a03ZeroModeRatioDoubleIntegral_eq_product ε ε _ hAfter]
      congr 1
      rw [integral_prod _ hy,integral_integral_swap hy]

theorem a03ZeroModeGCDInitialKernel_finiteProducts_eq_initialFront
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (hε1 : ε<1/8)
    (σ α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) :
    (1/(2*Real.pi):ℂ)^3*(∑a∈Finset.Icc 1 N₁,∑b∈Finset.Icc 1 N₂,
      ∫p : A03GCDMellinCoordinates,a03ZeroModeGCDInitialKernel Φ T σ α a b A B p.1
        (a03GCDMellinU ε p) (a03GCDMellinV ε p) (a03GCDMellinS ε p) ∂a03GCDMellinMeasure)=
      ∑a∈Finset.Icc 1 N₁,∑b∈Finset.Icc 1 N₂,
        verticalIntegral (1+ε) (fun s => a03ZeroModeRatioDoubleIntegral ε ε (fun u v =>
          ∫x : ℝ in Ioi 0,a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s)) := by
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact a03ZeroModeGCDInitialKernel_product_eq_initialBlock hΦ hSupp hT hε hε1 σ α hα
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1) A B

end
end SixthMoment.Source
