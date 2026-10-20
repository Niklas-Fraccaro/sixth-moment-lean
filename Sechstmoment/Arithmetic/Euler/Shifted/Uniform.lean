import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Convergence


namespace Sechstmoment

open Real Complex Filter
open scoped BigOperators Topology

noncomputable section

abbrev PolarShiftSpace := (Fin 3 → ℂ) × (Fin 3 → ℂ)

def polarShiftDomain (δ : ℝ) : Set PolarShiftSpace :=
  {ab | (∀ i : Fin 3, -δ < (ab.1 i).re) ∧ (∀ i : Fin 3, -δ < (ab.2 i).re)}

theorem polarShiftDomain_isOpen (δ : ℝ) : IsOpen (polarShiftDomain δ) := by
  have hf (i : Fin 3) : Continuous (fun ab : PolarShiftSpace => (ab.1 i).re) :=
    Complex.continuous_re.comp ((continuous_apply i).comp continuous_fst)
  have hg (i : Fin 3) : Continuous (fun ab : PolarShiftSpace => (ab.2 i).re) :=
    Complex.continuous_re.comp ((continuous_apply i).comp continuous_snd)
  change IsOpen ({ab : PolarShiftSpace | ∀ i : Fin 3, -δ < (ab.1 i).re} ∩
    {ab : PolarShiftSpace | ∀ i : Fin 3, -δ < (ab.2 i).re})
  simp only [Set.ofPred_forall]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hf i)).inter
    (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hg i))

theorem triplePrimePowerCoefficient_continuous {X : Type*} [TopologicalSpace X]
    (a : X → Fin 3 → ℂ) (ha : ∀ i : Fin 3, Continuous (fun x => a x i)) (m : ℕ) :
    Continuous (fun x => triplePrimePowerCoefficient (a x) m) := by
  unfold triplePrimePowerCoefficient
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact (((ha 0).pow i).mul ((ha 1).pow j)).mul ((ha 2).pow (m-i-j))

theorem primePolarWeights_continuous (p : {n : ℕ // Nat.Prime n}) (i : Fin 3) :
    Continuous (fun a : Fin 3 → ℂ => primePolarWeights p a i) := by
  have hp : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact (continuous_apply i).neg.const_cpow (.inl hp)

theorem shiftedDiagonalPrimeSeries_continuousOn (p : {n : ℕ // Nat.Prime n})
    {δ : ℝ} (hδ : δ < 1/2) :
    ContinuousOn (fun ab : PolarShiftSpace => shiftedDiagonalPrimeSeries p ab.1 ab.2)
      (polarShiftDomain δ) := by
  let r : ℝ := (p.val:ℝ)^δ
  let y : ℝ := r^2*‖1/(p.val:ℂ)‖
  have hr : 0 ≤ r := Real.rpow_nonneg (by positivity) _
  have hy : ‖y‖ < 1 := by
    rw [Real.norm_of_nonneg (by dsimp [y]; positivity)]
    dsimp [y, r]
    rw [primePolarGeometricRadius]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.property.one_lt)
      (by linarith)
  unfold shiftedDiagonalPrimeSeries
  apply continuousOn_tsum (u := fun m : ℕ => (d3PrimePowerCoefficient m:ℝ)^2*y^m)
  · intro m
    have hA : Continuous (fun ab : PolarShiftSpace =>
        triplePrimePowerCoefficient (primePolarWeights p ab.1) m) :=
      triplePrimePowerCoefficient_continuous _
        (fun i => (primePolarWeights_continuous p i).comp continuous_fst) m
    have hB : Continuous (fun ab : PolarShiftSpace =>
        triplePrimePowerCoefficient (primePolarWeights p ab.2) m) :=
      triplePrimePowerCoefficient_continuous _
        (fun i => (primePolarWeights_continuous p i).comp continuous_snd) m
    exact ((hA.mul hB).mul continuous_const).continuousOn
  · exact (hasSum_d3PrimePower_sq hy).summable
  · intro m ab hab
    exact diagonalPrimeTerm_norm_le hr
      (primePolarWeights_norm_le p ab.1 (fun i => (hab.1 i).le))
      (primePolarWeights_norm_le p ab.2 (fun i => (hab.2 i).le)) _ m

theorem shiftedPolarPrimeDivisors_continuous (p : {n : ℕ // Nat.Prime n}) :
    Continuous (fun ab : PolarShiftSpace => shiftedPolarPrimeDivisors p ab.1 ab.2) := by
  unfold shiftedPolarPrimeDivisors
  apply continuous_finsetProd
  intro ij _
  have hp : (p.val:ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  exact continuous_const.sub
    ((continuous_const.add ((continuous_apply ij.1).comp continuous_fst) |>.add
      ((continuous_apply ij.2).comp continuous_snd)).neg.const_cpow (.inl hp))

theorem shiftedPolarPrimeRemainder_continuousOn (p : {n : ℕ // Nat.Prime n})
    {δ : ℝ} (hδ : δ < 1/2) :
    ContinuousOn (fun ab : PolarShiftSpace => shiftedPolarPrimeRemainder p ab.1 ab.2)
      (polarShiftDomain δ) :=
  (shiftedPolarPrimeDivisors_continuous p).continuousOn.mul
    (shiftedDiagonalPrimeSeries_continuousOn p hδ)

theorem shiftedPolarEulerRest_hasProdUniformlyOn {δ : ℝ} (hδ : δ < 1/4)
    {K : Set PolarShiftSpace} (hK : IsCompact K) (hKD : K ⊆ polarShiftDomain δ) :
    HasProdUniformlyOn
      (fun p : {n : ℕ // Nat.Prime n} => fun ab : PolarShiftSpace =>
        shiftedPolarPrimeRemainder p ab.1 ab.2)
      (fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2) K := by
  have h := (shiftedPolarPrimeMajorant_summable hδ).hasProdUniformlyOn_one_add hK
    (f := fun p : {n : ℕ // Nat.Prime n} => fun ab : PolarShiftSpace =>
      shiftedPolarPrimeRemainder p ab.1 ab.2-1)
    (by
      filter_upwards [primePolarGeometricRadius_eventually (by linarith : δ < 1/2)]
        with p hp ab hab
      exact shiftedPolarPrimeRemainder_sub_one_bound p ab.1 ab.2
        (fun i => ((hKD hab).1 i).le) (fun i => ((hKD hab).2 i).le) hp)
    (fun p => ((shiftedPolarPrimeRemainder_continuousOn p
      (by linarith : δ < 1/2)).mono hKD).sub continuousOn_const)
  simpa only [add_sub_cancel, shiftedPolarEulerRest] using h

theorem shiftedPolarEulerRest_hasProdLocallyUniformlyOn {δ : ℝ} (hδ : δ < 1/4) :
    HasProdLocallyUniformlyOn
      (fun p : {n : ℕ // Nat.Prime n} => fun ab : PolarShiftSpace =>
        shiftedPolarPrimeRemainder p ab.1 ab.2)
      (fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2)
      (polarShiftDomain δ) := by
  apply hasProdLocallyUniformlyOn_of_forall_compact (polarShiftDomain_isOpen δ)
  intro K hKD hK
  exact shiftedPolarEulerRest_hasProdUniformlyOn hδ hK hKD

theorem shiftedPolarEulerRest_continuousOn {δ : ℝ} (hδ : δ < 1/4) :
    ContinuousOn (fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2)
      (polarShiftDomain δ) := by
  apply (shiftedPolarEulerRest_hasProdLocallyUniformlyOn hδ).continuousOn
  apply Filter.Frequently.of_forall
  intro s
  apply continuousOn_finsetProd
  intro p _
  exact shiftedPolarPrimeRemainder_continuousOn p (by linarith)

theorem shiftedPolarEulerRest_continuousAt_zero :
    ContinuousAt (fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2)
      ((fun _ => 0), (fun _ => 0)) := by
  apply (shiftedPolarEulerRest_continuousOn (δ := 1/8) (by norm_num)).continuousAt
  apply (polarShiftDomain_isOpen (1/8)).mem_nhds
  constructor <;> intro i <;> norm_num

end

end Sechstmoment
