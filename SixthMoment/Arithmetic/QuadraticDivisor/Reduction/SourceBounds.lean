import Lean.Util.CollectAxioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import SixthMoment.Arithmetic.QuadraticDivisor.Reduction.BlockSums
import Std

namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2200000

def NormalizedAnalyticApplicationEstimates (ρ δ K : ℝ) (bounds : ℕ → ℝ) : Prop :=
  ∃ Q₀ CWeil CWatt : ℝ, 1 ≤ Q₀ ∧ 0 ≤ CWeil ∧ 0 ≤ CWatt ∧
    ∀ (q : QuadraticScales) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ),
      ScaleGeometry ρ K q → (q.A*q.B)^δ ≤ K*q.M*q.N →
      NormalizedWeightData bounds q α β W → Q₀ ≤ q.mass →
      ∀ positive : Bool,
        (∀ d ∈ largeGcdSet q ρ, ∀ x,
          ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
            CWeil*q.mass^(5*ρ)*q.A*poissonLength q ρ d*q.H*
              (q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ)) ∧
        (∀ d ∈ smallGcdSet q ρ, gcdBlockMass positive q ρ α β W d ≤
          CWatt*q.mass^(200*ρ)*wattSummationCoefficient q/(d:ℝ))

def AnalyticApplicationEstimates : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ρ : ℝ, 0 < ρ → ρ ≤ δ/(1000*(1+δ)) →
  ∀ K : ℝ, 1 ≤ K → ∀ bounds : ℕ → ℝ, (∀ j, 0 ≤ bounds j) →
    NormalizedAnalyticApplicationEstimates ρ δ K bounds

theorem normalized_endgame_from_blocks {ρ K CWeil CWatt CError : ℝ}
    {bounds : ℕ → ℝ} {q : QuadraticScales} {α β : ℕ → ℂ}
    {W : Fin 5 → ℝ → ℝ} (h : ScaleGeometry ρ K q) (hK : 1 ≤ K)
    (hρ : 0 < ρ) (hw : NormalizedWeightData bounds q α β W)
    (hCWeil : 0 ≤ CWeil) (hCWatt : 0 ≤ CWatt) (hCError : 0 ≤ CError)
    (positive : Bool)
    (hWeil : ∀ d ∈ largeGcdSet q ρ, ∀ x,
      ‖gcdBlockIntegrand positive q ρ α β W d x‖ ≤
        CWeil*q.mass^(5*ρ)*q.A*poissonLength q ρ d*q.H*
          (q.B*q.N₁)^(1/2:ℝ)*(q.B*q.N₁+q.M₁)*(d:ℝ)^(-5/2:ℝ))
    (hWatt : ∀ d ∈ smallGcdSet q ρ, gcdBlockMass positive q ρ α β W d ≤
      CWatt*q.mass^(200*ρ)*wattSummationCoefficient q/(d:ℝ))
    (hError : ‖normalFormError positive q ρ α β W‖ ≤ CError*q.mass^(2*ρ)*q.H^2) :
    ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
      (CWatt*(1+1/ρ)*K^2+(20/3:ℝ)*K^3*CWeil+CError)*
        q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2) := by
  have hsmall := smallGcdMass_bound_of_integral_estimate h hK hρ hCWatt positive hWatt
  have hlarge := largeGcdMass_bound_of_integral_estimate h hK hρ
    (by positivity : 0 ≤ 2*K*CWeil) positive (by
      intro d hd
      have hdp : 0 < d := (mem_Icc.mp (mem_filter.mp hd).1).1
      exact weil_pointwise_to_block_integral h hK hw hCWeil positive hdp (hWeil d hd))
  have hlarge' : largeGcdMass positive q ρ α β W ≤
      ((20/3:ℝ)*K^3*CWeil)*q.mass^(170*ρ)*E₁ q := by
    convert hlarge using 1; ring
  obtain ⟨hA,hB,hM₁,hM₂,hN₁,hN₂,hH,hQ⟩ := h.pos
  have hQ₁ := (poisson_scale_bounds q h.scales).1
  have hE₀ : 0 ≤ E₀ q := by unfold E₀; positivity
  have hE₁ : 0 ≤ E₁ q := by unfold E₁; positivity
  have hE₂ : 0 ≤ E₂ q := by unfold E₂; positivity
  have hmajor := orientedMajorant_eq q hQ.le hH.le
  have hsmallE : E₀ q+E₂ q ≤ orientedQuadraticMajorant q+q.H^2 := by
    rw [hmajor]
    nlinarith [sq_nonneg q.H]
  have hlargeE : E₁ q ≤ orientedQuadraticMajorant q+q.H^2 := by
    rw [hmajor]
    nlinarith [sq_nonneg q.H]
  have herrorE : q.H^2 ≤ orientedQuadraticMajorant q+q.H^2 := by
    rw [hmajor]
    linarith
  have hs : smallGcdMass positive q ρ α β W ≤
      (CWatt*(1+1/ρ)*K^2)*q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2) :=
    hsmall.trans (by
      gcongr
      norm_num)
  have hl : largeGcdMass positive q ρ α β W ≤
      ((20/3:ℝ)*K^3*CWeil)*q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2) :=
    hlarge'.trans (by
      gcongr
      norm_num)
  have he : ‖normalFormError positive q ρ α β W‖ ≤
      CError*q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2) :=
    hError.trans (by
      gcongr
      norm_num)
  exact (actual_discrepancy_le_block_masses positive q ρ α β W).trans
    ((add_le_add (add_le_add hs hl) he).trans_eq (by ring))

theorem admissible_large_mass_from_analytic_applications {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j)
    (happ : NormalizedAnalyticApplicationEstimates ρ δ K bounds) :
    ∃ Q₀ C : ℝ, 1 ≤ Q₀ ∧ 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ρ δ K bounds q α β W →
      Q₀ ≤ q.mass → ∀ positive : Bool,
        ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
          C*q.mass^(226*ρ)*(orientedQuadraticMajorant q+q.H^2) := by
  obtain ⟨Q₁,CWeil,CWatt,hQ₁,hCWeil,hCWatt,happ⟩ := happ
  obtain ⟨Q₂,CError,hQ₂,hCError,herror⟩ :=
    admissible_normalized_finite_poisson_normal_form hρ hδ hbound hK bounds hb
  let C := CWatt*(1+1/ρ)*K^2+(20/3:ℝ)*K^3*CWeil+CError
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨max Q₁ Q₂,K^2*C,hQ₁.trans (le_max_left _ _),by positivity,?_⟩
  intro q α β W hadm hmass positive
  have hw := admissible_normalized_weight_data hK hadm
  obtain ⟨hWeil,hWatt⟩ := happ q _ _ _ (QuadraticAdmissible.geometry hadm) hadm.2.2.2.2.1 hw
    ((le_max_left _ _).trans hmass) positive
  have hn := normalized_endgame_from_blocks (QuadraticAdmissible.geometry hadm) hK hρ hw hCWeil hCWatt hCError
    positive hWeil hWatt (herror q α β W hadm ((le_max_right _ _).trans hmass) positive)
  change ‖_‖ ≤ C*q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2) at hn
  have hQ : 0 < q.mass := lt_of_lt_of_le (by norm_num) (poisson_scale_bounds q hadm.1).1
  have hAB : 0 < q.A*q.B := lt_of_lt_of_le (by norm_num) (product_AB_le_mass q hadm.1).1
  have hE := orientedMajorant_nonneg q (zero_le_one.trans (hadm.1 0))
    (zero_le_one.trans (hadm.1 1)) hQ.le (zero_le_one.trans (hadm.1 6))
  have hfactor : 0 ≤ K^2*(q.A*q.B)^ρ*q.mass^(5*ρ) := by positivity
  rw [pdf_normalization_identity positive q α β W hadm.1 hK,norm_mul,
    Complex.norm_real,Real.norm_of_nonneg hfactor]
  calc _ ≤ (K^2*(q.A*q.B)^ρ*q.mass^(5*ρ))*
      (C*q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2)) :=
        mul_le_mul_of_nonneg_left hn hfactor
    _ ≤ (K^2*(q.mass^ρ)^6)*(C*q.mass^(220*ρ)*(orientedQuadraticMajorant q+q.H^2)) :=
      mul_le_mul_of_nonneg_right (normalization_factor_le q hadm.1 hρ.le) (by positivity)
    _ = (K^2*C)*((q.mass^ρ)^6*q.mass^(220*ρ))*(orientedQuadraticMajorant q+q.H^2) := by ring
    _ = _ := by rw [final_loss_identity hQ]

theorem admissible_full_bound_from_analytic_applications {ρ δ K : ℝ}
    (hρ : 0 < ρ) (hδ : 0 < δ) (hbound : ρ ≤ δ/(1000*(1+δ)))
    (hK : 1 ≤ K) (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j)
    (happ : NormalizedAnalyticApplicationEstimates ρ δ K bounds) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ), QuadraticAdmissible ρ δ K bounds q α β W →
      ∀ positive : Bool, ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
        C*q.mass^(1000*ρ)*(orientedQuadraticMajorant q+q.H^2) := by
  obtain ⟨Q₀,C,hQ₀,hC,hlarge⟩ := admissible_large_mass_from_analytic_applications
    hρ hδ hbound hK bounds hb happ
  let C₀ := boundedMassConstant bounds K ρ Q₀
  have hC₀ : 0 ≤ C₀ := boundedMassConstant_nonneg hb (by linarith) (by linarith)
  refine ⟨C+C₀,add_nonneg hC hC₀,?_⟩
  intro q α β W hadm positive
  have hQ := (poisson_scale_bounds q hadm.1).1
  have hE := orientedMajorant_nonneg q (zero_le_one.trans (hadm.1 0))
    (zero_le_one.trans (hadm.1 1)) (zero_le_one.trans hQ) (zero_le_one.trans (hadm.1 6))
  by_cases hmass : Q₀ ≤ q.mass
  · calc _ ≤ C*q.mass^(226*ρ)*(orientedQuadraticMajorant q+q.H^2) :=
        hlarge q α β W hadm hmass positive
      _ ≤ C*q.mass^(1000*ρ)*(orientedQuadraticMajorant q+q.H^2) := by
        gcongr
        norm_num
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right hC₀
  · calc _ ≤ C₀*q.mass^(1000*ρ)*(orientedQuadraticMajorant q+q.H^2) :=
        admissible_bounded_mass_target hρ (rho_lt_half hδ hbound).le hK hQ₀ hadm
          (le_of_lt (lt_of_not_ge hmass)) positive
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_left hC

theorem quantifiedDivisorBound_of_analytic_applications
    (happ : AnalyticApplicationEstimates) : QuantifiedDivisorBound := by
  intro δ hδ ρ hρ hbound K hK bounds hb
  exact admissible_full_bound_from_analytic_applications hρ hδ hbound hK bounds hb
    (happ δ hδ ρ hρ hbound K hK bounds hb)

theorem separatedDivisorBound_of_quantified (hquantified : QuantifiedDivisorBound) :
    SeparatedDivisorBound := by
  intro ε hε δ hδ K hK bounds hb
  obtain ⟨hρ,hvalid,hρε⟩ := inputExponent_valid hε hδ
  obtain ⟨C,hC,hbound⟩ := hquantified δ hδ (inputExponent ε δ) hρ hvalid K hK bounds hb
  refine ⟨C,hC,?_⟩
  intro q α β W hadm positive
  have hQ := (poisson_scale_bounds q hadm.1).1
  have hH : 1 ≤ q.H := hadm.1 6
  have hE := orientedMajorant_nonneg q (zero_le_one.trans (hadm.1 0))
    (zero_le_one.trans (hadm.1 1)) (zero_le_one.trans hQ) (zero_le_one.trans hH)
  exact (hbound q α β W hadm positive).trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (separated_majorant_le hQ hH hE hε.le hρε) hC)

theorem separatedDivisorBound_of_analytic_applications (happ : AnalyticApplicationEstimates) :
    SeparatedDivisorBound :=
  separatedDivisorBound_of_quantified (quantifiedDivisorBound_of_analytic_applications happ)

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def reconstructedDivisorError (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (T X : ℝ) : ℂ :=
  ((T/((q.A*q.B)^(1/2:ℝ)*X):ℝ):ℂ)*signedQuadraticDiscrepancy positive q α β W

def sourceReconstructionMajorant (q : QuadraticScales) (X T K : ℝ) : ℝ :=
  2*(K^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)+
    K^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*
      (max q.A q.B)^(1/4:ℝ)*X^(1/2:ℝ))+
    K^2*(q.A*q.B)^(1/2:ℝ)*X/T

theorem actual_source_bound_of_separated (hseparated : SeparatedDivisorBound)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible (inputExponent ε δ) δ K bounds q α β W →
      ∀ positive : Bool, ∀ X T D r K₀ : ℝ,
      0 < X → 0 < T → 0 ≤ D → 0 < K₀ → q.mass = q.A*q.B*X^2 →
      q.mass ≤ D*T^r → q.mass*q.H^2 ≤ D*T^r →
      q.H ≤ K₀*(q.A*q.B)^(1/2:ℝ)*X/T →
      ‖reconstructedDivisorError positive q α β W T X‖ ≤
        C*(D^ε*T^(r*ε))*sourceReconstructionMajorant q X T K₀ := by
  obtain ⟨C,hC,hsource⟩ := hseparated ε hε δ hδ K hK bounds hb
  refine ⟨C,hC,?_⟩
  intro q α β W hadm positive X T D r K₀ hX hT hD hK₀ hmass hmassQ hmassH hH₀
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (hadm.1 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (hadm.1 1)
  have hH : 0 < q.H := lt_of_lt_of_le (by norm_num) (hadm.1 6)
  have hQ : 0 ≤ q.mass := zero_le_one.trans (poisson_scale_bounds q hadm.1).1
  have hE := orientedMajorant_nonneg q hA.le hB.le hQ hH.le
  have hpow₁ := polynomial_mass_loss (mul_nonneg hQ (sq_nonneg _)) hD hT.le hε.le hmassH
  have hpow₂ := polynomial_mass_loss hQ hD hT.le hε.le hmassQ
  have hd : ‖signedQuadraticDiscrepancy positive q α β W‖ ≤
      C*(D^ε*T^(r*ε))*(orientedQuadraticMajorant q+q.H^2) := by
    calc _ ≤ C*((q.mass*q.H^2)^ε*orientedQuadraticMajorant q+q.mass^ε*q.H^2) :=
        hsource q α β W hadm positive
      _ ≤ C*((D^ε*T^(r*ε))*orientedQuadraticMajorant q+(D^ε*T^(r*ε))*q.H^2) := by gcongr
      _ = _ := by ring
  have hF : 0 ≤ T/((q.A*q.B)^(1/2:ℝ)*X) := by positivity
  unfold reconstructedDivisorError
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hF]
  calc _ ≤ (T/((q.A*q.B)^(1/2:ℝ)*X))*
      (C*(D^ε*T^(r*ε))*(orientedQuadraticMajorant q+q.H^2)) :=
        mul_le_mul_of_nonneg_left hd hF
    _ = (C*(D^ε*T^(r*ε)))*
      (T/((q.A*q.B)^(1/2:ℝ)*X)*(orientedQuadraticMajorant q+q.H^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reconstructed_majorant_le q hA hB hX hH hT hK₀ hmass hH₀) (by positivity)

theorem actual_source_bound_of_analytic_applications (happ : AnalyticApplicationEstimates)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : QuadraticScales) (α β : ℕ → ℂ)
      (W : Fin 5 → ℝ → ℝ),
      QuadraticAdmissible (inputExponent ε δ) δ K bounds q α β W →
      ∀ positive : Bool, ∀ X T D r K₀ : ℝ,
      0 < X → 0 < T → 0 ≤ D → 0 < K₀ → q.mass = q.A*q.B*X^2 →
      q.mass ≤ D*T^r → q.mass*q.H^2 ≤ D*T^r →
      q.H ≤ K₀*(q.A*q.B)^(1/2:ℝ)*X/T →
      ‖reconstructedDivisorError positive q α β W T X‖ ≤
        C*(D^ε*T^(r*ε))*sourceReconstructionMajorant q X T K₀ :=
  actual_source_bound_of_separated (separatedDivisorBound_of_analytic_applications happ)
    hε hδ hK bounds hb

theorem integral_superposition_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {c F : Ω → ℂ} {B L : ℝ}
    (hc : Integrable c μ) (hF : AEStronglyMeasurable (fun ω => c ω*F ω) μ)
    (hB : 0 ≤ B) (hbound : ∀ ω, ‖F ω‖ ≤ B)
    (hL : (∫ ω, ‖c ω‖ ∂μ) ≤ L) :
    Integrable (fun ω => c ω*F ω) μ ∧ ‖∫ ω, c ω*F ω ∂μ‖ ≤ L*B := by
  have hdom (ω : Ω) : ‖c ω*F ω‖ ≤ ‖c ω‖*B := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound ω) (norm_nonneg _)
  have hI := (hc.norm.mul_const B).mono' hF (Filter.Eventually.of_forall hdom)
  refine ⟨hI,?_⟩
  calc _ ≤ ∫ ω, ‖c ω*F ω‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, ‖c ω‖*B ∂μ := integral_mono hI.norm (hc.norm.mul_const B) hdom
    _ = (∫ ω, ‖c ω‖ ∂μ)*B := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right hL hB

theorem tensor_actual_source_bound_of_separated (hseparated : SeparatedDivisorBound)
    {ε δ K : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hK : 1 ≤ K)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
      (q : QuadraticScales) (α β : Ω → ℕ → ℂ) (W : Ω → Fin 5 → ℝ → ℝ),
      (∀ j, 1 ≤ q.size j) → (∀ ω, QuadraticAdmissible (inputExponent ε δ) δ K bounds q (α ω) (β ω) (W ω)) →
      ∀ (positive : Bool) (c : Ω → ℂ) (X T D r K₀ L : ℝ),
      0 < X → 0 < T → 0 ≤ D → 0 < K₀ → q.mass = q.A*q.B*X^2 →
      q.mass ≤ D*T^r → q.mass*q.H^2 ≤ D*T^r →
      q.H ≤ K₀*(q.A*q.B)^(1/2:ℝ)*X/T → Integrable c μ →
      AEStronglyMeasurable (fun ω => c ω*reconstructedDivisorError positive q (α ω) (β ω) (W ω) T X) μ →
      (∫ ω, ‖c ω‖ ∂μ) ≤ L →
      Integrable (fun ω => c ω*reconstructedDivisorError positive q (α ω) (β ω) (W ω) T X) μ ∧
      ‖∫ ω, c ω*reconstructedDivisorError positive q (α ω) (β ω) (W ω) T X ∂μ‖ ≤
        L*(C*(D^ε*T^(r*ε))*sourceReconstructionMajorant q X T K₀) := by
  obtain ⟨C,hC,hbound⟩ := actual_source_bound_of_separated hseparated hε hδ hK bounds hb
  refine ⟨C,hC,?_⟩
  intro Ω _ μ q α β W hq hadm positive c X T D r K₀ L hX hT hD hK₀ hmass hmassQ hmassH hH₀ hc hmeas hL
  have hA : 0 < q.A := lt_of_lt_of_le (by norm_num) (hq 0)
  have hB : 0 < q.B := lt_of_lt_of_le (by norm_num) (hq 1)
  have hmajor : 0 ≤ sourceReconstructionMajorant q X T K₀ := by
    dsimp [sourceReconstructionMajorant]
    positivity
  exact integral_superposition_bound hc hmeas (by positivity)
    (fun ω => hbound q (α ω) (β ω) (W ω) (hadm ω) positive X T D r K₀
      hX hT hD hK₀ hmass hmassQ hmassH hH₀) hL

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical Filter Asymptotics
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2200000

def sourceExponent₀ (a b s ε : ℝ) : ℝ := 1/2+a+b+4*ε+s/2
def sourceExponent₁ (a b s u ε : ℝ) : ℝ := 3/4+(3*a+5*b)/8+4*ε+u/4+3*s/4
def sourceExponent₂ (a b s u ε : ℝ) : ℝ := (a+b)/2+4*ε+u/2+2*s

theorem sourceReconstruction_power_bound {a b s u ε D T X K₀ : ℝ}
    {q : QuadraticScales} (hT : 1 ≤ T) (hD : 1 ≤ D) (hX : 0 < X)
    (hK₀ : 0 < K₀) (hA : 0 < q.A) (hB : 0 < q.B) (hab : a ≤ b)
    (hAb : q.A ≤ D*T^a) (hBb : q.B ≤ D*T^b)
    (hXb : X ≤ D*T^(1+u/2)) (hKb : K₀ ≤ D*T^s) :
    T^(4*ε)*sourceReconstructionMajorant q X T K₀ ≤
      D^4*(2*T^(sourceExponent₀ a b s ε)+2*T^(sourceExponent₁ a b s u ε)+
        T^(sourceExponent₂ a b s u ε)) := by
  have hTp : 0 < T := by linarith
  have hDp : 0 < D := by linarith
  have hmaxp : 0 < max q.A q.B := lt_of_lt_of_le hA (le_max_left _ _)
  have hmax : max q.A q.B ≤ D*T^b := max_le
    (hAb.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hab) hDp.le)) hBb
  have hAl := Real.log_le_log hA hAb
  have hBl := Real.log_le_log hB hBb
  have hXl := Real.log_le_log hX hXb
  have hKl := Real.log_le_log hK₀ hKb
  have hMl := Real.log_le_log hmaxp hmax
  have hDl := Real.log_nonneg hD
  simp (disch := positivity) only [Real.log_mul,Real.log_rpow] at hAl hBl hXl hKl hMl
  have h₀ : T^(4*ε)*(K₀^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)) ≤
      D^4*T^(sourceExponent₀ a b s ε) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [sourceExponent₀,Real.log_mul,Real.log_pow,Real.log_rpow]
    nlinarith
  have h₁ : T^(4*ε)*(K₀^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*
      (max q.A q.B)^(1/4:ℝ)*X^(1/2:ℝ)) ≤ D^4*T^(sourceExponent₁ a b s u ε) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [sourceExponent₁,Real.log_mul,Real.log_pow,Real.log_rpow]
    nlinarith
  have h₂ : T^(4*ε)*(K₀^2*(q.A*q.B)^(1/2:ℝ)*X/T) ≤
      D^4*T^(sourceExponent₂ a b s u ε) := by
    apply (Real.log_le_log_iff (by positivity) (by positivity)).mp
    simp (disch := positivity) only [sourceExponent₂,Real.log_mul,Real.log_div,Real.log_pow,Real.log_rpow]
    nlinarith
  unfold sourceReconstructionMajorant
  calc _ = 2*(T^(4*ε)*(K₀^(1/2:ℝ)*T^(1/2:ℝ)*(q.A*q.B)))+
      2*(T^(4*ε)*(K₀^(3/4:ℝ)*T^(1/4:ℝ)*(q.A*q.B)^(3/8:ℝ)*
        (max q.A q.B)^(1/4:ℝ)*X^(1/2:ℝ)))+
      T^(4*ε)*(K₀^2*(q.A*q.B)^(1/2:ℝ)*X/T) := by ring
    _ ≤ 2*(D^4*T^(sourceExponent₀ a b s ε))+
      2*(D^4*T^(sourceExponent₁ a b s u ε))+D^4*T^(sourceExponent₂ a b s u ε) :=
        add_le_add (add_le_add (mul_le_mul_of_nonneg_left h₀ (by norm_num))
          (mul_le_mul_of_nonneg_left h₁ (by norm_num))) h₂
    _ = _ := by ring

theorem source_exponent_majorant_le {a b s u T : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hrange : 3*a+5*b < 2)
    (hs : 0 ≤ s) (hs' : s ≤ sourceGap a b/64)
    (hu : 0 ≤ u) (hu' : u ≤ sourceGap a b/64) (hT : 1 ≤ T) :
    T^(sourceGap a b/64)*
      (2*T^(sourceExponent₀ a b s (sourceGap a b/64))+
        2*T^(sourceExponent₁ a b s u (sourceGap a b/64))+
        T^(sourceExponent₂ a b s u (sourceGap a b/64))) ≤
      5*T^(1-sourceGap a b/2) := by
  have hTp : 0 < T := by linarith
  obtain ⟨h₀,h₁,h₂⟩ := source_exponents_with_margin ha hab hrange hs hs' hu hu'
  have hp₀ : T^(sourceGap a b/64)*T^(sourceExponent₀ a b s (sourceGap a b/64)) ≤
      T^(1-sourceGap a b/2) := by
    rw [← Real.rpow_add hTp]
    apply Real.rpow_le_rpow_of_exponent_le hT
    dsimp [sourceExponent₀]
    linarith
  have hp₁ : T^(sourceGap a b/64)*T^(sourceExponent₁ a b s u (sourceGap a b/64)) ≤
      T^(1-sourceGap a b/2) := by
    rw [← Real.rpow_add hTp]
    apply Real.rpow_le_rpow_of_exponent_le hT
    dsimp [sourceExponent₁]
    linarith
  have hp₂ : T^(sourceGap a b/64)*T^(sourceExponent₂ a b s u (sourceGap a b/64)) ≤
      T^(1-sourceGap a b/2) := by
    rw [← Real.rpow_add hTp]
    apply Real.rpow_le_rpow_of_exponent_le hT
    dsimp [sourceExponent₂]
    linarith
  nlinarith

theorem actual_source_error_isLittleO_of_separated
    (hseparated : SeparatedDivisorBound) {a b s u K D Dmass : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hrange : 3*a+5*b < 2)
    (hs : 0 ≤ s) (hs' : s ≤ sourceGap a b/64)
    (hu : 0 ≤ u) (hu' : u ≤ sourceGap a b/64)
    (hK : 1 ≤ K) (hD : 1 ≤ D) (hDmass : 0 ≤ Dmass)
    (bounds : ℕ → ℝ) (hb : ∀ j, 0 ≤ bounds j)
    (q : ℝ → QuadraticScales) (α β : ℝ → ℕ → ℂ) (W : ℝ → Fin 5 → ℝ → ℝ)
    (X K₀ : ℝ → ℝ) (positive : Bool) (k : ℕ)
    (hdata : ∀ᶠ T : ℝ in atTop,
      QuadraticAdmissible (inputExponent (sourceGap a b/64) 1) 1 K bounds
        (q T) (α T) (β T) (W T) ∧
      0 < X T ∧ 0 < K₀ T ∧ (q T).mass = (q T).A*(q T).B*(X T)^2 ∧
      (q T).mass ≤ Dmass*T^4 ∧ (q T).mass*(q T).H^2 ≤ Dmass*T^4 ∧
      (q T).H ≤ K₀ T*((q T).A*(q T).B)^(1/2:ℝ)*X T/T ∧
      (q T).A ≤ D*T^a ∧ (q T).B ≤ D*T^b ∧
      X T ≤ D*T^(1+u/2) ∧ K₀ T ≤ D*T^s) :
    (fun T : ℝ => ((Real.log T)^k:ℂ)*
      reconstructedDivisorError positive (q T) (α T) (β T) (W T) T (X T)) =o[atTop]
      (fun T : ℝ => T) := by
  have hγ := sourceGap_pos ha hab hrange
  have hε : 0 < sourceGap a b/64 := by positivity
  obtain ⟨C,hC,hsource⟩ := actual_source_bound_of_separated hseparated hε
    (by norm_num : (0:ℝ) < 1) hK bounds hb
  have hlog := (log_pow_isLittleO hε k).bound (by norm_num : (0:ℝ) < 1)
  have hbound : ∀ᶠ T : ℝ in atTop,
      ‖((Real.log T)^k:ℂ)*reconstructedDivisorError positive (q T) (α T) (β T) (W T) T (X T)‖ ≤
        (5*C*Dmass^(sourceGap a b/64)*D^4)*T^(1-sourceGap a b/2) := by
    filter_upwards [hdata,hlog,eventually_ge_atTop (1:ℝ)] with T hdata hlog hT
    obtain ⟨hadm,hX,hK₀,hmass,hmassQ,hmassH,hH₀,hA,hB,hXb,hKb⟩ := hdata
    have hTp : 0 < T := by linarith
    have hAp : 0 < (q T).A := lt_of_lt_of_le (by norm_num) (hadm.1 0)
    have hBp : 0 < (q T).B := lt_of_lt_of_le (by norm_num) (hadm.1 1)
    have hR := hsource (q T) (α T) (β T) (W T) hadm positive (X T) T Dmass 4 (K₀ T)
      hX hTp hDmass hK₀ hmass (by simpa only [Real.rpow_ofNat] using hmassQ)
      (by simpa only [Real.rpow_ofNat] using hmassH) hH₀
    have hP := sourceReconstruction_power_bound hT hD hX hK₀ hAp hBp hab hA hB hXb hKb
      (ε := sourceGap a b/64)
    have hM : 0 ≤ sourceReconstructionMajorant (q T) (X T) T (K₀ T) := by
      dsimp [sourceReconstructionMajorant]
      positivity
    have hlog' : ‖(Real.log T)^k‖ ≤ T^(sourceGap a b/64) := by
      simpa only [one_mul,Real.norm_of_nonneg (Real.rpow_nonneg hTp.le _)] using hlog
    simp only [norm_pow] at hlog'
    simp only [norm_mul,norm_pow,Complex.norm_real]
    calc _ ≤ T^(sourceGap a b/64)*
        (C*(Dmass^(sourceGap a b/64)*T^(4*(sourceGap a b/64)))*
          sourceReconstructionMajorant (q T) (X T) T (K₀ T)) := by gcongr
      _ = (C*Dmass^(sourceGap a b/64))*T^(sourceGap a b/64)*
        (T^(4*(sourceGap a b/64))*sourceReconstructionMajorant (q T) (X T) T (K₀ T)) := by ring
      _ ≤ (C*Dmass^(sourceGap a b/64))*T^(sourceGap a b/64)*
        (D^4*(2*T^(sourceExponent₀ a b s (sourceGap a b/64))+
          2*T^(sourceExponent₁ a b s u (sourceGap a b/64))+
          T^(sourceExponent₂ a b s u (sourceGap a b/64)))) := by gcongr
      _ = (C*Dmass^(sourceGap a b/64)*D^4)*
        (T^(sourceGap a b/64)*(2*T^(sourceExponent₀ a b s (sourceGap a b/64))+
          2*T^(sourceExponent₁ a b s u (sourceGap a b/64))+
          T^(sourceExponent₂ a b s u (sourceGap a b/64)))) := by ring
      _ ≤ (C*Dmass^(sourceGap a b/64)*D^4)*(5*T^(1-sourceGap a b/2)) :=
        mul_le_mul_of_nonneg_left (source_exponent_majorant_le ha hab hrange hs hs' hu hu' hT) (by positivity)
      _ = _ := by ring
  have hbig : (fun T : ℝ => ((Real.log T)^k:ℂ)*
      reconstructedDivisorError positive (q T) (α T) (β T) (W T) T (X T)) =O[atTop]
      (fun T : ℝ => T^(1-sourceGap a b/2)) := by
    apply Asymptotics.IsBigO.of_bound (5*C*Dmass^(sourceGap a b/64)*D^4)
    filter_upwards [hbound,eventually_ge_atTop (1:ℝ)] with T h hT
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ T) _)] using h
  exact hbig.trans_isLittleO (saved_power_isLittleO hγ)

end
end DivisorProof



namespace DivisorProof
open Real MeasureTheory Set Finset Classical
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem sum_piFinset_head {E : Type*} [AddCommMonoid E] {n : ℕ}
    (s : Fin (n+1) → Finset ℕ) (f : (Fin (n+1) → ℕ) → E) :
    (∑ v ∈ Fintype.piFinset s, f v) =
      ∑ a ∈ s 0, ∑ t ∈ Fintype.piFinset (fun i : Fin n => s i.succ), f (Fin.cons a t) := by
  symm
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => Fin.cons p.1 p.2)
  · intro p hp
    obtain ⟨hp₀,hp₁⟩ := mem_product.mp hp
    apply Fintype.mem_piFinset.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hp₀
    · exact Fintype.mem_piFinset.mp hp₁ j
  · intro p _ q _ hpq
    apply Prod.ext
    · exact congrFun hpq 0
    · funext j
      exact congrFun hpq j.succ
  · intro v hv
    refine ⟨(v 0,Fin.tail v),mem_product.mpr ⟨Fintype.mem_piFinset.mp hv 0,?_⟩,Fin.cons_self_tail v⟩
    exact Fintype.mem_piFinset.mpr (fun i => Fintype.mem_piFinset.mp hv i.succ)
  · intro p _
    rfl

theorem sum_piFinset_five {E : Type*} [AddCommMonoid E]
    (sa sb sm sn sk : Finset ℕ) (f : (Fin 5 → ℕ) → E) :
    (∑ v ∈ Fintype.piFinset (fun i => (![sa,sb,sm,sn,sk] : Fin 5 → Finset ℕ) i), f v) =
      ∑ a ∈ sa, ∑ b ∈ sb, ∑ m ∈ sm, ∑ n ∈ sn, ∑ k ∈ sk, f ![a,b,m,n,k] := by
  simp [sum_piFinset_head]
  repeat' (apply Finset.sum_congr rfl; intro _ _)
  congr 1

theorem quadraticMainIndexSet_sum {E : Type*} [AddCommMonoid E]
    (q : QuadraticScales) (f : (Fin 5 → ℕ) → E) :
    (∑ v ∈ quadraticMainIndexSet q, f v) =
      ∑ a ∈ Finset.Icc 1 ⌊2*q.A⌋₊, ∑ b ∈ Finset.Icc 1 ⌊2*q.B⌋₊,
        ∑ m ∈ Finset.Icc 1 ⌊2*q.M₁⌋₊, ∑ n ∈ Finset.Icc 1 ⌊2*q.N₁⌋₊,
          ∑ k ∈ Finset.Icc 1 ⌊2*q.H⌋₊, f ![a,b,m,n,k] := by
  have hsets : (fun j => Finset.Icc 1
      ⌊2*(![q.A,q.B,q.M₁,q.N₁,q.H] : Fin 5 → ℝ) j⌋₊) =
      (![Finset.Icc 1 ⌊2*q.A⌋₊,Finset.Icc 1 ⌊2*q.B⌋₊,
        Finset.Icc 1 ⌊2*q.M₁⌋₊,Finset.Icc 1 ⌊2*q.N₁⌋₊,
        Finset.Icc 1 ⌊2*q.H⌋₊] : Fin 5 → Finset ℕ) := by
    funext j
    fin_cases j <;> rfl
  rw [quadraticMainIndexSet,hsets]
  exact sum_piFinset_five _ _ _ _ _ f

def fixedGcdFourierSum (positive : Bool) (q : QuadraticScales)
    (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) (l : ℤ) (x : ℝ) : ℂ :=
  ∑ n ∈ (quadraticMainIndexSet q).filter (fun n => outerGCD n = d),
    poissonOuterWeight q α β W n*outerPoissonProfile q W n x*
      ePhase (-(l:ℝ)*outerPoissonPhase positive n)

theorem gcdBlockIntegrand_eq_frequency_sum (positive : Bool) (q : QuadraticScales)
    (ρ : ℝ) (α β : ℕ → ℂ) (W : Fin 5 → ℝ → ℝ) (d : ℕ) (x : ℝ) :
    gcdBlockIntegrand positive q ρ α β W d x =
      ∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else
        (sourceCutoff ((l:ℝ)/poissonLength q ρ d):ℂ)*ePhase ((l:ℝ)*x)*
          fixedGcdFourierSum positive q α β W d l x := by
  have heq (n : Fin 5 → ℕ)
      (hn : n ∈ (quadraticMainIndexSet q).filter (fun n => outerGCD n = d)) :
      poissonOuterWeight q α β W n*outerFourierIntegrand positive q ρ W n x =
      ∑ l ∈ frequencySet (2*poissonLength q ρ d), if l = 0 then 0 else
        (sourceCutoff ((l:ℝ)/poissonLength q ρ d):ℂ)*ePhase ((l:ℝ)*x)*
          (poissonOuterWeight q α β W n*outerPoissonProfile q W n x*
            ePhase (-(l:ℝ)*outerPoissonPhase positive n)) := by
    unfold outerFourierIntegrand
    rw [(mem_filter.mp hn).2]
    unfold finitePoissonKernel
    simp_rw [mul_sum]
    apply sum_congr rfl
    intro l _
    by_cases hl : l = 0
    · simp [hl]
    · simp only [ite_eq_right hl]
      ring
  unfold gcdBlockIntegrand
  simp_rw [Finset.sum_congr rfl heq]
  rw [sum_comm]
  apply sum_congr rfl
  intro l _
  by_cases hl : l = 0
  · simp [hl]
  · simp only [ite_eq_right hl,fixedGcdFourierSum,mul_sum]

end
end DivisorProof
