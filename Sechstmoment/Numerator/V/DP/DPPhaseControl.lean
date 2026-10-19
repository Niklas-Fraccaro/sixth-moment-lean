import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Sechstmoment.Numerator.V.DP.DPResidueContinuity
import Sechstmoment.Numerator.V.DP.DPSharpSource

/-! # Actual outer-phase control for the DP four residues -/
namespace Sechstmoment.Source
open Complex MeasureTheory Set Polynomial Filter
open scoped Topology BigOperators
noncomputable section

def dpResiduePhases (σ : MomentShifts) : Fin 4 → ℂ :=
  ![-σ 0-σ 2-σ 3, -σ 1-σ 2-σ 3, -σ 3, -σ 2]

def dpResidueCoefficients (η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : Fin 4 → ℂ :=
  ![(dpNormalizedTriple η P (σ 1) (σ 2) (σ 3))^2 /
      ((σ 1-σ 0)*(σ 0+σ 2)*(σ 0+σ 3)),
    (dpNormalizedTriple η P (σ 0) (σ 2) (σ 3))^2 /
      ((σ 0-σ 1)*(σ 1+σ 2)*(σ 1+σ 3)),
    (dpNormalizedTriple η P (σ 1) (-σ 0) (σ 3))^2 /
      ((σ 1+σ 2)*(σ 0+σ 2)*(σ 2-σ 3)),
    (dpNormalizedTriple η P (σ 1) (σ 2) (-σ 0))^2 /
      ((σ 1+σ 3)*(σ 3-σ 2)*(σ 0+σ 3))]

theorem dpNormalizedFourResidues_eq_sum (q η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    dpNormalizedFourResidues q η P σ =
      ∑ j : Fin 4, Complex.exp ((q : ℂ)*dpResiduePhases σ j)*dpResidueCoefficients η P σ j := by
  simp [Fin.sum_univ_succ, dpResiduePhases, dpResidueCoefficients, dpNormalizedFourResidues]
  ring

def dpNormalizedFourSlope (q η : ℝ) (P : ℝ[X]) (σ : MomentShifts) : ℂ :=
  ∑ j : Fin 4, Complex.exp ((q : ℂ)*dpResiduePhases σ j)*
    dpResiduePhases σ j*dpResidueCoefficients η P σ j

theorem dpNormalizedFourResidues_hasDerivAt (q η : ℝ) (P : ℝ[X]) (σ : MomentShifts) :
    HasDerivAt (fun q : ℝ => dpNormalizedFourResidues q η P σ)
      (dpNormalizedFourSlope q η P σ) q := by
  have ht (j : Fin 4) : HasDerivAt
      (fun q : ℝ => Complex.exp ((q : ℂ)*dpResiduePhases σ j)*dpResidueCoefficients η P σ j)
      (Complex.exp ((q : ℂ)*dpResiduePhases σ j)*dpResiduePhases σ j*
        dpResidueCoefficients η P σ j) q := by
    simpa only [id_eq, Complex.ofReal_one, one_mul] using
      (((hasDerivAt_id q).ofReal_comp.mul_const (dpResiduePhases σ j)).cexp.mul_const
        (dpResidueCoefficients η P σ j))
  simpa only [dpNormalizedFourSlope, ← dpNormalizedFourResidues_eq_sum] using
    (HasDerivAt.fun_sum fun j (_ : j ∈ Finset.univ) => ht j)

theorem dpNormalizedFour_phase_lipschitz {q C : ℝ} (η : ℝ) (P : ℝ[X]) (σ : MomentShifts)
    (hq : q ∈ Icc (0 : ℝ) 2)
    (hC : ∀ r ∈ Icc (0 : ℝ) 2, ‖dpNormalizedFourSlope r η P σ‖ ≤ C) :
    ‖dpNormalizedFourResidues q η P σ-dpNormalizedFourResidues 1 η P σ‖ ≤ C*|q-1| := by
  simpa only [Real.norm_eq_abs] using
    (convex_Icc (0 : ℝ) 2).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun r _ => (dpNormalizedFourResidues_hasDerivAt r η P σ).hasDerivWithinAt)
      hC (by norm_num : (1 : ℝ) ∈ Icc 0 2) hq

theorem dpResidueCoefficients_continuousOn (η : ℝ) (P : ℝ[X]) (j : Fin 4) :
    ContinuousOn (fun σ : MomentShifts => dpResidueCoefficients η P σ j)
      {σ | DPSeparated σ} := by
  have ht1 : Continuous (fun σ : MomentShifts => dpNormalizedTriple η P (σ 1) (σ 2) (σ 3)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have ht0 : Continuous (fun σ : MomentShifts => dpNormalizedTriple η P (σ 0) (σ 2) (σ 3)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have ht2 : Continuous (fun σ : MomentShifts => dpNormalizedTriple η P (σ 1) (-σ 0) (σ 3)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  have ht3 : Continuous (fun σ : MomentShifts => dpNormalizedTriple η P (σ 1) (σ 2) (-σ 0)) :=
    dpNormalizedTriple_continuous_shifts η P _ _ _ (by fun_prop) (by fun_prop) (by fun_prop)
  fin_cases j
  · exact (ht1.pow 2).continuousOn.div (by fun_prop) (fun σ hσ => (dpSeparated_denominators hσ).1)
  · exact (ht0.pow 2).continuousOn.div (by fun_prop) (fun σ hσ => (dpSeparated_denominators hσ).2.1)
  · exact (ht2.pow 2).continuousOn.div (by fun_prop) (fun σ hσ => (dpSeparated_denominators hσ).2.2.1)
  · exact (ht3.pow 2).continuousOn.div (by fun_prop) (fun σ hσ => (dpSeparated_denominators hσ).2.2.2)

theorem dpNormalizedFourSlope_continuousOn_joint (η : ℝ) (P : ℝ[X]) :
    ContinuousOn (fun p : ℝ × MomentShifts => dpNormalizedFourSlope p.1 η P p.2)
      {p | DPSeparated p.2} := by
  unfold dpNormalizedFourSlope
  apply continuousOn_finsetSum
  intro j _
  have hp : Continuous (fun p : ℝ × MomentShifts =>
      Complex.exp ((p.1 : ℂ)*dpResiduePhases p.2 j)*dpResiduePhases p.2 j) := by
    fin_cases j <;> unfold dpResiduePhases <;> fun_prop
  exact hp.continuousOn.mul ((dpResidueCoefficients_continuousOn η P j).comp
    continuous_snd.continuousOn (fun _ hp => hp))

theorem dpNormalizedFourSlope_compact_bound (η : ℝ) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K) (hsep : ∀ σ ∈ K, DPSeparated σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ K, ∀ q ∈ Icc (0 : ℝ) 2,
      ‖dpNormalizedFourSlope q η P σ‖ ≤ C := by
  have hc : ContinuousOn (fun p : ℝ × MomentShifts => dpNormalizedFourSlope p.1 η P p.2)
      (Icc (0 : ℝ) 2 ×ˢ K) :=
    (dpNormalizedFourSlope_continuousOn_joint η P).mono (fun _ hp => hsep _ hp.2)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro σ hσ q hq
  exact (hC (q,σ) ⟨hq,hσ⟩).trans (le_max_left _ _)

theorem dpNormalizedFourResidues_compact_bound (η : ℝ) (P : ℝ[X])
    (K : Set MomentShifts) (hK : IsCompact K) (hsep : ∀ σ ∈ K, DPSeparated σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ ∈ K, ∀ q ∈ Icc (0 : ℝ) 2,
      ‖dpNormalizedFourResidues q η P σ‖ ≤ C := by
  have hc : ContinuousOn (fun p : ℝ × MomentShifts => dpNormalizedFourResidues p.1 η P p.2)
      (Icc (0 : ℝ) 2 ×ˢ K) :=
    (dpNormalizedFourResidues_continuousOn_joint η P).mono (fun _ hp => hsep _ hp.2)
  obtain ⟨C,hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn hc
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro σ hσ q hq
  exact (hC (q,σ) ⟨hq,hσ⟩).trans (le_max_left _ _)

def dpPhaseWindowConstant : ℝ := Real.log 4+|Real.log (2*Real.pi)|

theorem dpPhaseWindowConstant_nonneg : 0 ≤ dpPhaseWindowConstant := by
  unfold dpPhaseWindowConstant
  positivity

theorem dp_phase_endpoint_bound {T X : ℝ} (hT : 1 < T) (hX : X ∈ Icc (T/4) (2*T)) :
    |Real.log (X/(2*Real.pi))/Real.log T-1| ≤ dpPhaseWindowConstant/Real.log T := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity : 0 < T/4) hX.1
  have hπ : 0 < 2*Real.pi := by positivity
  have hL : 0 < Real.log T := Real.log_pos hT
  have hr0 : 0 < X/T := div_pos hX0 hT0
  have hr : X/T ∈ Icc (1/4 : ℝ) 2 := by
    constructor
    · apply (le_div_iff₀ hT0).mpr
      linarith [hX.1]
    · exact (div_le_iff₀ hT0).mpr hX.2
  have hloglo : -Real.log 4 ≤ Real.log (X/T) := by
    have h := Real.log_le_log (by norm_num : 0 < (1/4 : ℝ)) hr.1
    simpa only [one_div, Real.log_inv] using h
  have hloghi : Real.log (X/T) ≤ Real.log 4 :=
    Real.log_le_log hr0 (hr.2.trans (by norm_num))
  have hlogabs : |Real.log (X/T)| ≤ Real.log 4 := abs_le.mpr ⟨hloglo, hloghi⟩
  have he : Real.log (X/(2*Real.pi))/Real.log T-1 =
      (Real.log (X/T)-Real.log (2*Real.pi))/Real.log T := by
    rw [Real.log_div hX0.ne' hπ.ne', Real.log_div hX0.ne' hT0.ne']
    field_simp
    ring
  rw [he, abs_div, abs_of_pos hL]
  apply div_le_div_of_nonneg_right _ hL.le
  apply (abs_sub _ _).trans
  dsimp [dpPhaseWindowConstant]
  linarith

theorem dp_phase_endpoint_in_window {T X : ℝ} (hT : 1 < T)
    (hL : dpPhaseWindowConstant ≤ Real.log T) (hX : X ∈ Icc (T/4) (2*T)) :
    Real.log (X/(2*Real.pi))/Real.log T ∈ Icc (0 : ℝ) 2 := by
  have h := dp_phase_endpoint_bound hT hX
  have hr : dpPhaseWindowConstant/Real.log T ≤ 1 :=
    (div_le_one (Real.log_pos hT)).mpr hL
  have hh := abs_le.mp (h.trans hr)
  constructor <;> linarith

end
end Sechstmoment.Source
