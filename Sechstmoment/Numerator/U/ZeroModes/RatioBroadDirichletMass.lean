import Mathlib.Analysis.PSeries
import Sechstmoment.Numerator.U.ZeroModes.RatioUnitTail

/-! Absolute Dirichlet mass of the actual ratio partition at every positive
spatial scale, uniformly in the normalized root-gap chamber. -/
namespace Sechstmoment.Source
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 2000000

def a03RatioBroadDirichletTerm (T : ℝ) (σ : MomentShifts) (A X : ℝ) (m : ℕ) : ℝ :=
  if m=0 then 0 else (m:ℝ)^(-(1/2:ℝ))*
    ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (Sechstmoment.rawMomentShifts T σ))
      (A*(m:ℝ)^2/X)‖

theorem a03RatioBroadDirichletTerm_nonneg (T : ℝ) (σ : MomentShifts) (A X : ℝ) (m : ℕ) :
    0≤a03RatioBroadDirichletTerm T σ A X m := by
  unfold a03RatioBroadDirichletTerm
  split_ifs <;> positivity

theorem a03RatioBroadPartition_unit_power_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : Sechstmoment.PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) → ∀ x : ℝ,0<x →
      ‖a03ZeroModeRatioPartition (a03ZeroModeRatioWeight (Sechstmoment.rawMomentShifts T σ)) x‖≤
        C*(Real.log T)^4*x^(-1:ℝ) := by
  let J : ℝ := ∫v:ℝ,(1+|v|)^4*Real.exp (-v^2)
  have hJ : 0≤J := integral_nonneg (fun _ => by positivity)
  let C : ℝ := (1/(2*Real.pi))*(Real.exp 1*2^4*(1+1/κ^2)^2)*J
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro T hT hlog σ hroot x hx
  have hg := a03ZeroModeRatioGaussianConstant_log_growth_radius hT hlog hκ σ hroot 1
  norm_num only [one_pow] at hg
  have hb := a03ZeroModeRatioPartition_explicit_power_bound (by norm_num : (0:ℝ)<1)
    (Sechstmoment.rawMomentShifts T σ) hx
  norm_num only [div_one] at hb
  calc
    _≤(1/(2*Real.pi))*((Real.exp 1*2^4*(1+1/κ^2)^2)*(Real.log T)^4)*J*x^(-1:ℝ) := by
      apply hb.trans
      gcongr
      simpa only [show (2:ℝ)^4=16 by norm_num] using hg
    _=_ := by dsimp [C]; ring

theorem a03RatioBroadDirichletMass_uniform_bound {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T → ∀ σ : MomentShifts,
      (∀ k : Sechstmoment.PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      ∀ A X : ℝ,0<A → 0<X →
      Summable (a03RatioBroadDirichletTerm T σ A X) ∧
      (∑'m:ℕ,a03RatioBroadDirichletTerm T σ A X m)≤
        C*(Real.log T)^4*(X/A)*(∑'m:ℕ,(m:ℝ)^(-(5/2:ℝ))) := by
  obtain ⟨C,hC,hpart⟩ := a03RatioBroadPartition_unit_power_bound hκ
  refine ⟨C,hC,?_⟩
  intro T hT hlog σ hroot A X hA hX
  let Q : ℝ := C*(Real.log T)^4*(X/A)
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hs : Summable (fun m : ℕ => (m:ℝ)^(-(5/2:ℝ))) := Real.summable_nat_rpow.mpr (by norm_num)
  have hp (m : ℕ) : a03RatioBroadDirichletTerm T σ A X m≤Q*(m:ℝ)^(-(5/2:ℝ)) := by
    by_cases hm : m=0
    · simp only [a03RatioBroadDirichletTerm,hm,ite_true]
      positivity
    · have hmpos : (0:ℝ)<m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hx : 0<A*(m:ℝ)^2/X := by positivity
      have hb := hpart T hT hlog σ hroot _ hx
      have he : (m:ℝ)^(-(1/2:ℝ))*(A*(m:ℝ)^2/X)^(-1:ℝ)=
          (X/A)*(m:ℝ)^(-(5/2:ℝ)) := by
        have hpow : (m:ℝ)^2*(m:ℝ)^(-(5/2:ℝ))=(m:ℝ)^(-(1/2:ℝ)) := by
          rw [←Real.rpow_two,←Real.rpow_add hmpos]
          norm_num
        rw [←hpow,Real.rpow_neg_one]
        field_simp
      simp only [a03RatioBroadDirichletTerm,hm,ite_false]
      calc
        _≤(m:ℝ)^(-(1/2:ℝ))*(C*(Real.log T)^4*(A*(m:ℝ)^2/X)^(-1:ℝ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
        _=(C*(Real.log T)^4)*((m:ℝ)^(-(1/2:ℝ))*(A*(m:ℝ)^2/X)^(-1:ℝ)) := by ring
        _=Q*(m:ℝ)^(-(5/2:ℝ)) := by rw [he]; dsimp [Q]; ring
  have hmajor := hs.mul_left Q
  have hsum := hmajor.of_nonneg_of_le (a03RatioBroadDirichletTerm_nonneg T σ A X) hp
  refine ⟨hsum,?_⟩
  exact (hsum.tsum_le_tsum hp hmajor).trans_eq (by rw [tsum_mul_left])

end
end Sechstmoment.Source
