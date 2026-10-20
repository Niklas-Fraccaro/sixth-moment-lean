import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Sechstmoment.Numerator.U.Separation.Frequency.SixComposition
import Sechstmoment.Numerator.U.ZeroModes.RatioGlobalLogDerivatives

namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000

def a03RatioLinear (i j : Fin 6) : A03SixTensorSpace→L[ℝ]ℝ :=
  PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 6 => ℝ) i-PiLp.proj (𝕜:=ℝ) 2 (fun _ : Fin 6 => ℝ) j

theorem a03RatioLinear_apply (i j : Fin 6) (y : A03SixTensorSpace) :
    a03RatioLinear i j y=y i-y j := rfl

theorem a03RatioLinear_norm_le (i j : Fin 6) : ‖a03RatioLinear i j‖≤2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [a03RatioLinear_apply]
  have h := norm_sub_le (y i) (y j)
  have hi := PiLp.norm_apply_le y i
  have hj := PiLp.norm_apply_le y j
  linarith

def a03RatioEuclideanFactor (α : MomentShifts) (t : ℝ) (i j : Fin 6)
    (y : A03SixTensorSpace) : ℂ :=
  a03ZeroModeRatioLogDerivative (a03ZeroModeRatioWeight α) 0 (t+a03RatioLinear i j y)

def a03RatioEuclideanMultiplier (α : MomentShifts) (tM tN : ℝ)
    (y : A03SixTensorSpace) : ℂ :=
  a03RatioEuclideanFactor α tM 2 3 y*a03RatioEuclideanFactor α tN 4 5 y

def a03RatioDerivativeBudget (κ : ℝ) (n : ℕ) : ℝ :=
  (1+(gaussianTailConstant (n+4)/(2*Real.pi))*(Real.exp 1*16*(1+1/κ^2)^2))*2^n

def a03RatioMultiplierDerivativeBudget (κ : ℝ) (n : ℕ) : ℝ :=
  ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*a03RatioDerivativeBudget κ i*a03RatioDerivativeBudget κ (n-i)

theorem a03RatioDerivativeBudget_nonneg (κ : ℝ) (n : ℕ) : 0≤a03RatioDerivativeBudget κ n := by
  unfold a03RatioDerivativeBudget
  have h := gaussianTailConstant_nonneg (n+4)
  positivity

theorem a03RatioMultiplierDerivativeBudget_nonneg (κ : ℝ) (n : ℕ) :
    0≤a03RatioMultiplierDerivativeBudget κ n :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (a03RatioDerivativeBudget_nonneg κ i)) (a03RatioDerivativeBudget_nonneg κ (n-i)))

theorem a03RatioEuclideanFactor_contDiff (α : MomentShifts) (t : ℝ) (i j : Fin 6) :
    ContDiff ℝ ∞ (a03RatioEuclideanFactor α t i j) := by
  have h := a03ZeroModeRatioLogDerivative_contDiff _ α (a03ZeroModeRatioWeight_admissible α)
  exact h.comp (contDiff_const.add (a03RatioLinear i j).contDiff)

theorem a03RatioEuclideanMultiplier_contDiff (α : MomentShifts) (tM tN : ℝ) :
    ContDiff ℝ ∞ (a03RatioEuclideanMultiplier α tM tN) :=
  (a03RatioEuclideanFactor_contDiff α tM 2 3).mul (a03RatioEuclideanFactor_contDiff α tN 4 5)

theorem a03RatioEuclideanFactor_uniform_derivative_bound {T κ : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (t : ℝ) (i j : Fin 6) (n : ℕ) (y : A03SixTensorSpace) :
    ‖iteratedFDeriv ℝ n (a03RatioEuclideanFactor (rawMomentShifts T σ) t i j) y‖≤
      a03RatioDerivativeBudget κ n*(Real.log T)^4 := by
  let G := a03ZeroModeRatioWeight (rawMomentShifts T σ)
  let f : ℝ→ℂ := fun w => a03ZeroModeRatioLogDerivative G 0 (t+w)
  have hf : ContDiff ℝ ∞ f := (a03ZeroModeRatioLogDerivative_contDiff G _
    (a03ZeroModeRatioWeight_admissible _)).comp (contDiff_const.add contDiff_id)
  have he : a03RatioEuclideanFactor (rawMomentShifts T σ) t i j=f ∘ a03RatioLinear i j := rfl
  rw [he,(a03RatioLinear i j).iteratedFDeriv_comp_right hf y (by simp)]
  calc
    _≤‖iteratedFDeriv ℝ n f (a03RatioLinear i j y)‖*∏ _r : Fin n,‖a03RatioLinear i j‖ :=
      ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _≤‖iteratedFDeriv ℝ n f (a03RatioLinear i j y)‖*2^n := by
      rw [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (a03RatioLinear_norm_le i j) n) (norm_nonneg _)
    _≤(1+(gaussianTailConstant (n+4)/(2*Real.pi))*(Real.exp 1*16*(1+1/κ^2)^2))*(Real.log T)^4*2^n := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      dsimp only [f]
      rw [iteratedDeriv_comp_const_add,a03ZeroModeRatioLogDerivative_iteratedDeriv G _ (a03ZeroModeRatioWeight_admissible _)]
      exact a03ZeroModeRatioLogDerivative_global_log_growth hT hL hκ σ hρ n _
    _=_ := by unfold a03RatioDerivativeBudget; ring

theorem a03RatioEuclideanMultiplier_uniform_derivative_bound {T κ : ℝ}
    (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (tM tN : ℝ) (n : ℕ) (y : A03SixTensorSpace) :
    ‖iteratedFDeriv ℝ n (a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN) y‖≤
      a03RatioMultiplierDerivativeBudget κ n*(Real.log T)^8 := by
  have hm := norm_iteratedFDeriv_mul_le (a03RatioEuclideanFactor_contDiff (rawMomentShifts T σ) tM 2 3)
    (a03RatioEuclideanFactor_contDiff (rawMomentShifts T σ) tN 4 5) y (n:=n) (by simp)
  apply hm.trans
  calc
    _≤∑ i∈Finset.range (n+1),(n.choose i:ℝ)*(a03RatioDerivativeBudget κ i*(Real.log T)^4)*
        (a03RatioDerivativeBudget κ (n-i)*(Real.log T)^4) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (a03RatioEuclideanFactor_uniform_derivative_bound hT hL hκ σ hρ tM 2 3 i y) (Nat.cast_nonneg _))
        (a03RatioEuclideanFactor_uniform_derivative_bound hT hL hκ σ hρ tN 4 5 (n-i) y)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (a03RatioDerivativeBudget_nonneg κ i) (by positivity)))
    _=_ := by
      unfold a03RatioMultiplierDerivativeBudget
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem a03RatioEuclideanMultiplier_eq_partition (α : MomentShifts) (tM tN : ℝ)
    (y : A03SixTensorSpace) :
    a03RatioEuclideanMultiplier α tM tN y=
      a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) (Real.exp (tM+y 2-y 3))*
        a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) (Real.exp (tN+y 4-y 5)) := by
  simp only [a03ZeroModeRatioPartition_eq_logDerivative _ (Real.exp_pos _),Real.log_exp,
    a03RatioEuclideanMultiplier,a03RatioEuclideanFactor,a03RatioLinear_apply]
  congr 2 <;> ring

def a03RatioNormalizedMultiplier (e T : ℝ) (σ : MomentShifts) (tM tN : ℝ)
    (y : A03SixTensorSpace) : ℂ :=
  (T^(-e)) • a03RatioEuclideanMultiplier (rawMomentShifts T σ) tM tN y

theorem a03RatioNormalizedMultiplier_contDiff (e T : ℝ) (σ : MomentShifts) (tM tN : ℝ) :
    ContDiff ℝ ∞ (a03RatioNormalizedMultiplier e T σ tM tN) := by
  exact (contDiff_const : ContDiff ℝ ∞ (fun _ : A03SixTensorSpace => T^(-e))).smul
    (a03RatioEuclideanMultiplier_contDiff (rawMomentShifts T σ) tM tN)

def a03RatioSubpowerDerivativeBudget (e κ : ℝ) (n : ℕ) : ℝ :=
  a03RatioMultiplierDerivativeBudget κ n*((Nat.factorial 8:ℝ)/e^8*Real.exp e)

theorem a03RatioSubpowerDerivativeBudget_nonneg {e : ℝ} (he : 0<e) (κ : ℝ) (n : ℕ) :
    0≤a03RatioSubpowerDerivativeBudget e κ n := by
  unfold a03RatioSubpowerDerivativeBudget
  exact mul_nonneg (a03RatioMultiplierDerivativeBudget_nonneg κ n) (by positivity)

theorem a03RatioNormalizedMultiplier_uniform_derivative_bound {e T κ : ℝ}
    (he : 0<e) (hT : 1<T) (hL : 1≤Real.log T) (hκ : 0<κ) (σ : MomentShifts)
    (hρ : ∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖)
    (tM tN : ℝ) (n : ℕ) (y : A03SixTensorSpace) :
    ‖iteratedFDeriv ℝ n (a03RatioNormalizedMultiplier e T σ tM tN) y‖≤a03RatioSubpowerDerivativeBudget e κ n := by
  have hTp : 0<T := zero_lt_one.trans hT
  have hpoly : (Real.log T)^8≤((Nat.factorial 8:ℝ)/e^8*Real.exp e)*T^e :=
    (pow_le_pow_left₀ (Real.log_nonneg hT.le) (by linarith : Real.log T≤1+Real.log T) 8).trans
      (logarithmic_power_le_rpow he hT.le 8)
  unfold a03RatioNormalizedMultiplier
  rw [iteratedFDeriv_const_smul_apply' ((a03RatioEuclideanMultiplier_contDiff (rawMomentShifts T σ) tM tN).contDiffAt.of_le (by simp)),
    norm_smul,Real.norm_of_nonneg (Real.rpow_nonneg hTp.le _)]
  calc
    _≤T^(-e)*(a03RatioMultiplierDerivativeBudget κ n*(Real.log T)^8) :=
      mul_le_mul_of_nonneg_left (a03RatioEuclideanMultiplier_uniform_derivative_bound hT hL hκ σ hρ tM tN n y) (Real.rpow_nonneg hTp.le _)
    _≤T^(-e)*(a03RatioMultiplierDerivativeBudget κ n*(((Nat.factorial 8:ℝ)/e^8*Real.exp e)*T^e)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpoly (a03RatioMultiplierDerivativeBudget_nonneg κ n)) (Real.rpow_nonneg hTp.le _)
    _=a03RatioSubpowerDerivativeBudget e κ n := by
      unfold a03RatioSubpowerDerivativeBudget
      have hp : T^(-e)*T^e=1 := by rw [←Real.rpow_add hTp,neg_add_cancel,Real.rpow_zero]
      calc
        _=(a03RatioMultiplierDerivativeBudget κ n*((Nat.factorial 8:ℝ)/e^8*Real.exp e))*(T^(-e)*T^e) := by ring
        _=_ := by rw [hp,mul_one]

end
end Sechstmoment
