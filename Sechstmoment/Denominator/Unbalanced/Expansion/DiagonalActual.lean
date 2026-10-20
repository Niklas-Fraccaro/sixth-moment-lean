import Sechstmoment.Denominator.Unbalanced.Expansion.Diagonal
import Sechstmoment.Denominator.Unbalanced.MomentDefinitions

namespace Sechstmoment
open MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

theorem d04OneSidedShiftWeight_eq_centered_laplace (σ : Fin 2 → ℂ) (y : D01LogSpace) :
    d04OneSidedShiftWeight σ y=Complex.exp ((-σ 0+σ 1)/2)*
      d01ComplexLaplaceWeight ((fun _ => 0),![-σ 0,σ 1,0]) y := by
  rw [d04OneSidedShiftWeight,d01ComplexLaplaceWeight,← Complex.exp_add]
  congr 1
  simp only [Fin.sum_univ_three]
  simp
  ring

theorem d04OneSidedProfileProduct_rowColumnSums (ρ : Fin 4 → ℝ → ℝ) (x : D01EdgeSpace) :
    d04OneSidedProfileProduct (fun i t => (ρ i t : ℂ)) (d01RowColumnSums x)=
      (d04UnbalancedEdgeProfile ρ x : ℂ) := by
  simp [d04OneSidedProfileProduct,d04UnbalancedEdgeProfile]

theorem d04OneSidedDiagonal_edge_integral_identity (ρ : Fin 4 → ℝ → ℝ)
    (σ : Fin 2 → ℂ) :
    (∫ x : D01EdgeSpace,d04OneSidedShiftWeight σ (d01RowColumnSums x)*
      d04OneSidedProfileProduct (fun i t => (ρ i t : ℂ)) (d01RowColumnSums x)
        ∂volume.restrict d01NonnegativeOrthant)=d04UnbalancedShiftedEdgeIntegral ρ σ := by
  unfold d04UnbalancedShiftedEdgeIntegral d01EdgeMeasure
  apply integral_congr_ae
  exact ae_of_all _ (fun x => by
    dsimp only
    rw [d04OneSidedProfileProduct_rowColumnSums]
    unfold d04OneSidedShiftWeight
    ring)

theorem d04OneSidedLogSmoothing_logPoint {T : ℝ} (hT : 1<T) (x : DiagonalSixIndices) :
    d04OneSidedLogSmoothing (Real.log T) (d01LogPoint (Real.log T) x)=
      Real.exp (-((d01RightIndices x 0 : ℝ)*(d01RightIndices x 1 : ℝ))/(T^3)) := by
  have hL : Real.log T≠0 := (Real.log_pos hT).ne'
  have hm : 0<(d01RightIndices x 0 : ℝ) := by exact_mod_cast d01RightIndices_pos x 0
  have hn : 0<(d01RightIndices x 1 : ℝ) := by exact_mod_cast d01RightIndices_pos x 1
  have hexp : Real.exp (Real.log T*((d01LogPoint (Real.log T) x).2 0+
      (d01LogPoint (Real.log T) x).2 1))=
      (d01RightIndices x 0 : ℝ)*(d01RightIndices x 1 : ℝ) := by
    have he : Real.log T*((d01LogPoint (Real.log T) x).2 0+
        (d01LogPoint (Real.log T) x).2 1)=
        Real.log (d01RightIndices x 0 : ℝ)+Real.log (d01RightIndices x 1 : ℝ) := by
      dsimp [d01LogPoint]
      field_simp [hL]
    rw [he,Real.exp_add,Real.exp_log hm,Real.exp_log hn]
  have h3 : Real.exp (3*Real.log T)=T^3 := by
    rw [show (3:ℝ)=(3:ℕ) by norm_num,Real.exp_nat_mul,Real.exp_log (zero_lt_one.trans hT)]
  unfold d04OneSidedLogSmoothing
  rw [Real.exp_sub,hexp,h3]
  congr 1
  ring

def d04OneSidedLiteralDiagonalTerm (T : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (σ : Fin 2 → ℂ) (x : DiagonalSixIndices) : ℂ :=
  Complex.exp ((-σ 0+σ 1)/2)*
    literalDiagonalSixTerm (fun _ => 0)
      ![-σ 0/(Real.log T : ℂ),σ 1/(Real.log T : ℂ),0] x *
    d04OneSidedProfileProduct (fun i t => (ρ i t : ℂ)) (d01LogPoint (Real.log T) x)*
    (Real.exp (-((d01RightIndices x 0 : ℝ)*(d01RightIndices x 1 : ℝ))/(T^3)) : ℂ)

theorem d04OneSidedLiteralDiagonal_measure_identity {T : ℝ} (hT : 1<T)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) :
    (∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)/
      (Real.log T : ℂ)^9=
      ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct (fun i t => (ρ i t : ℂ)) y*
        (d04OneSidedLogSmoothing (Real.log T) y : ℂ)
          ∂d01DiagonalMeasure (Real.log T) := by
  rw [d01DiagonalMeasure_integral (Real.log_pos hT).le,← tsum_div_const]
  apply tsum_congr
  intro x
  rw [Complex.real_smul,d04OneSidedShiftWeight_eq_centered_laplace,
    d04OneSidedLogSmoothing_logPoint hT]
  have hi := d01Atomic_complexLaplace_identity (Real.log T)
    (fun _ => 0) ![-σ 0,σ 1,0] x
  have hs : (fun j : Fin 3 => ![-σ 0,σ 1,0] j/(Real.log T : ℂ))=
      ![-σ 0/(Real.log T : ℂ),σ 1/(Real.log T : ℂ),0] := by
    funext j; fin_cases j <;> simp
  simp only [zero_div] at hi
  rw [hs] at hi
  unfold d04OneSidedLiteralDiagonalTerm
  calc
    _ = Complex.exp ((-σ 0+σ 1)/2)*
      (literalDiagonalSixTerm (fun _ => 0)
        ![-σ 0/(Real.log T : ℂ),σ 1/(Real.log T : ℂ),0] x/(Real.log T : ℂ)^9)*
      d04OneSidedProfileProduct (fun i t => (ρ i t : ℂ)) (d01LogPoint (Real.log T) x)*
      (Real.exp (-((d01RightIndices x 0 : ℝ)*(d01RightIndices x 1 : ℝ))/(T^3)) : ℂ) := by ring
    _ = _ := by rw [← hi]; ring

theorem d04OneSidedLiteralDiagonal_limit
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) :
    Tendsto (fun T : ℝ => (∑' x : DiagonalSixIndices,
      d04OneSidedLiteralDiagonalTerm T ρ σ x)/(Real.log T : ℂ)^9) atTop
      (𝓝 ((arithmeticFactor : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ σ)) := by
  have hcap : ∀ k t,(ρ k t : ℂ)≠0 → t∈Icc 0 (a k) := by
    intro k t ht
    apply hρcap k t
    exact fun h => ht (by rw [h]; simp)
  have hlim := d04DiagonalMeasure_one_sided_smoothed_shifted_height_limit
    (fun k t => (ρ k t : ℂ)) a σ
    (fun k => Complex.continuous_ofReal.comp (hρc k)) hcap ha3 ha
  rw [d04OneSidedDiagonal_edge_integral_identity] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  exact (d04OneSidedLiteralDiagonal_measure_identity hT ρ σ).symm

theorem d04OneSidedLiteralDiagonal_eventually_uniformly_bounded
    (ρ : Fin 4 → ℝ → ℝ) (a : Fin 4 → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) {R : ℝ} (hR : 0≤R) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖(∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)/
        (Real.log T : ℂ)^9‖≤B := by
  have hcap : ∀ k t,(ρ k t : ℂ)≠0 → t∈Icc 0 (a k) := by
    intro k t ht
    apply hρcap k t
    exact fun h => ht (by rw [h]; simp)
  obtain ⟨B,hB,hbound⟩ := d04OneSidedDiagonal_eventually_uniformly_bounded
    (fun k t => (ρ k t : ℂ)) a
    (fun k => Complex.continuous_ofReal.comp (hρc k)) hcap ha3 ha hR
  refine ⟨B,hB,?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually hbound,eventually_gt_atTop (1:ℝ)]
    with T hb hT
  intro σ hσ
  rw [d04OneSidedLiteralDiagonal_measure_identity hT]
  exact hb σ hσ

theorem d04OneSidedLiteralDiagonal_time_mean_identity {T : ℝ} (hT : 0<T)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (Ψ : ℝ → ℂ) :
    (∫ t : ℝ,Ψ (t/T)*∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)/
      ((T : ℂ)*(Real.log T : ℂ)^9)=
      (∫ τ : ℝ,Ψ τ)*
        ((∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)/
          (Real.log T : ℂ)^9) := by
  rw [integral_mul_const,Measure.integral_comp_div Ψ T,abs_of_pos hT,Complex.real_smul]
  have hTc : (T : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hT.ne'
  rw [mul_assoc,mul_div_mul_left _ _ hTc,mul_div_assoc]

theorem d04OneSidedLiteralDiagonal_physical_time_identity {T : ℝ} (hT : 0<T)
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (Φ : ℝ → ℝ) :
    (∫ t : ℝ,(Φ (t/T) : ℂ)*d04CenteringPurePower T t (σ 0)*
      ∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)/
      ((T : ℂ)*(Real.log T : ℂ)^9)=
      (∫ τ : ℝ,(Φ τ : ℂ)*d04CenteringPurePower T (T*τ) (σ 0))*
        ((∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)/
          (Real.log T : ℂ)^9) := by
  have he : (∫ t : ℝ,(Φ (t/T) : ℂ)*d04CenteringPurePower T t (σ 0)*
      ∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x)=
      ∫ t : ℝ,((Φ (t/T) : ℂ)*d04CenteringPurePower T (T*(t/T)) (σ 0))*
        ∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x := by
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by
      dsimp only
      rw [mul_div_cancel₀ t hT.ne'])
  rw [he]
  exact d04OneSidedLiteralDiagonal_time_mean_identity hT ρ σ
    (fun τ => (Φ τ : ℂ)*d04CenteringPurePower T (T*τ) (σ 0))

end
end Sechstmoment
