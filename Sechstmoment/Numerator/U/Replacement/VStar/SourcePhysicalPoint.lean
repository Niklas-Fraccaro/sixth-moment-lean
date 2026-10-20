import Sechstmoment.Numerator.U.Replacement.VStar.PhysicalTimeWindow

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem a03ZeroModePermutedPhysicalQuad_positive (m n : Bool) (q : QuadraticScales)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    ∀ j,0<a03ZeroModePermutedPhysicalQuad m n q v x j := by
  have hp (j : Fin 5) : 0<(v j:ℝ) := by exact_mod_cast (show 0<v j by have := hv j; omega)
  have hd : 0<(Nat.gcd (v 0*v 2) (v 1*v 3):ℝ) :=
    a03ZeroMode_gcd_pos (by have := hv 0; omega) (by have := hv 1; omega)
      (by have := hv 2; omega) (by have := hv 3; omega)
  have hp0 := hp 0
  have hp1 := hp 1
  have hp2 := hp 2
  have hp3 := hp 3
  have hr1 : 0<(v 1:ℝ)*v 3/(Nat.gcd (v 0*v 2) (v 1*v 3):ℝ)*x :=
    mul_pos (div_pos (mul_pos hp1 hp3) hd) hx
  have hr2 : 0<(v 0:ℝ)*v 2/(Nat.gcd (v 0*v 2) (v 1*v 3):ℝ)*x :=
    mul_pos (div_pos (mul_pos hp0 hp2) hd) hx
  intro j
  cases m <;> cases n <;> fin_cases j <;>
    simp [a03ZeroModePermutedPhysicalQuad,a03ZeroModePhysicalQuad] <;>
    first | exact_mod_cast hp2 | exact_mod_cast hp3 | exact hr1 | exact hr2

theorem a03LeadingLinearTensor_sourceScale_eq_physical_time
    (Φ : ℝ→ℂ) (c : ℝ) (p : A03NearTensorData) (m n : Bool) (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) p.α ((c:ℂ)+(p.v:ℂ)*I)*
      a03LeadingLinearTensorRawKernel Φ c p
        (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))=
      ∫t : ℝ,a03PhysicalLeadingTimeKernel Φ p.T p.σ p.α
        (a03ZeroModePermutedPhysicalQuad m n q v x)
        (a03LinearZeroGap p (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x))) c p.v t := by
  let y := a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)
  let z : ℂ := (c:ℂ)+(p.v:ℂ)*I
  have hscale := a03ZeroMode_scale_mellin_eq_denominator m n q hq p.α z v hv hx
  unfold a03LeadingLinearTensorRawKernel a03GaussianLeadingFrequencyProfile profileLaplaceTransform
  have hphase : -p.T*p.s*p.r*Real.exp (a03SixGapLinear y)= -a03LinearZeroGap p y := by
    unfold a03LinearZeroGap
    ring
  dsimp only [y] at hphase
  rw [hphase]
  simp only [Complex.ofReal_neg]
  change a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) p.α z*
      (a03TensorMellinFactor p.α z y*∫t : ℝ,
        Complex.exp (((-a03LinearZeroGap p y):ℂ)*I*(t:ℂ))*a03GaussianLeadingTimeProfile Φ p.T p.σ p.α z t)=_
  rw [←mul_assoc,hscale,←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  unfold a03PhysicalLeadingTimeKernel a03PhysicalLeadingTimeAmplitude a03GaussianLeadingTimeProfile a03ProfileProduct
  dsimp only [z,y]
  simp only [Complex.ofReal_neg]
  ring

theorem a03LeadingLinearTensor_sourceScale_vertical_eq_VStar
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c : ℝ} (hT : 0<T) (hc : 0<c) (σ α : MomentShifts) (r s : ℝ)
    (m n : Bool) (q : QuadraticScales) (hq : ∀ j,0<q.size j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    (1/(2*Real.pi):ℂ)*(∫w : ℝ,
      a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
        a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩
          (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))=
      (a03ZeroModeRealQuadDenominator α 0 (a03ZeroModePermutedPhysicalQuad m n q v x))⁻¹*
        ∫t : ℝ,Complex.exp (((-(T*s*r*Real.exp (a03SixGapLinear
          (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))):ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ)
            (a03PhysicalQuadProduct (a03ZeroModePermutedPhysicalQuad m n q v x)/(T*t)^2) := by
  let ξ : ℝ := T*s*r*Real.exp (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))
  calc
    _=(1/(2*Real.pi):ℂ)*(∫w : ℝ,∫t : ℝ,a03PhysicalLeadingTimeKernel Φ T σ α
        (a03ZeroModePermutedPhysicalQuad m n q v x) ξ c w t) := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro w
      simpa only [a03LinearZeroGap,ξ] using
        a03LeadingLinearTensor_sourceScale_eq_physical_time Φ c ⟨T,σ,α,w,r,s⟩ m n q hq v hv hx
    _=_ := a03PhysicalLeadingTimeKernel_vertical_time_eq_VStar hΦ hSupp hT hc σ α _
      (a03ZeroModePermutedPhysicalQuad_positive m n q v hv hx) ξ


theorem a03LeadingLinearTensor_sourceScale_set_eq_physicalFourier
    (Φ : ℝ→ℂ) (c T : ℝ) (σ α : MomentShifts) (r s : ℝ)
    (m n : Bool) (q : QuadraticScales) (hq : ∀ j,0<q.size j)
    (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) (S : Set ℝ) :
    (1/(2*Real.pi):ℂ)*(∫w : ℝ in S,
      a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
        a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩
          (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))=
      a03PhysicalLeadingFourierSet Φ c T σ α (a03ZeroModePermutedPhysicalQuad m n q v x)
        (T*s*r*Real.exp (a03SixGapLinear (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))) S := by
  unfold a03PhysicalLeadingFourierSet
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro w
  simpa only [a03LinearZeroGap] using
    a03LeadingLinearTensor_sourceScale_eq_physical_time Φ c ⟨T,σ,α,w,r,s⟩ m n q hq v hv hx

theorem a03LeadingLinearTensor_sourceScale_core_sub_VStar_norm_le
    {Φ : ℝ→ℂ} (hΦ : Continuous Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T c L : ℝ} (hT : 0<T) (hc : 0<c) (hL : 0≤L)
    (σ α : MomentShifts) (r s : ℝ) (m n : Bool) (q : QuadraticScales)
    (hq : ∀ j,0<q.size j) (v : Fin 5→ℕ) (hv : ∀ j,1≤v j) {x : ℝ} (hx : 0<x) :
    ‖(1/(2*Real.pi):ℂ)*(∫w : ℝ in Icc (-L) L,
      a03ZeroModeMellinScaleFactor (phasePairSwapScales m n q) α ((c:ℂ)+(w:ℂ)*I)*
        a03LeadingLinearTensorRawKernel Φ c ⟨T,σ,α,w,r,s⟩
          (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))-
      (a03ZeroModeRealQuadDenominator α 0 (a03ZeroModePermutedPhysicalQuad m n q v x))⁻¹*
        (∫t : ℝ,Complex.exp (((-(T*s*r*Real.exp (a03SixGapLinear
          (a03SixTensorLogPoint (a03SixZeroSourceArguments m n q v x)))):ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ)
            (a03PhysicalQuadProduct (a03ZeroModePermutedPhysicalQuad m n q v x)/(T*t)^2))‖≤
      (‖(a03ZeroModeRealQuadDenominator α 0 (a03ZeroModePermutedPhysicalQuad m n q v x))⁻¹‖*
        (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ c/c*
        (a03PhysicalQuadProduct (a03ZeroModePermutedPhysicalQuad m n q v x))^(-c)*(2*T)^(2*c)*
          Real.exp (-(1/2)*L^2))*∫t : ℝ,‖Φ t‖ := by
  rw [a03LeadingLinearTensor_sourceScale_set_eq_physicalFourier Φ c T σ α r s m n q hq v hv hx]
  exact a03PhysicalLeadingFourierCore_sub_VStar_norm_le hΦ hSupp hT hc hL σ α _
    (a03ZeroModePermutedPhysicalQuad_positive m n q v hv hx) _

end
end Sechstmoment
