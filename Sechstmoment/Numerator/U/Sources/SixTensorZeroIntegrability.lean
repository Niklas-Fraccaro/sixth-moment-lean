import Sechstmoment.Numerator.U.Separation.ShapeNormalization
import Sechstmoment.Numerator.U.Separation.SixTensorSource

namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators FourierTransform RealInnerProductSpace Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem phasePairSwapWeights_complexWeight (m n : Bool)
    (W : Fin 5 → ℝ → ℂ) (hW : ∀ i, RectangularComplexWeight (W i)) (i : Fin 5) :
    RectangularComplexWeight (phasePairSwapWeights m n W i) := by
  cases m <;> cases n <;> fin_cases i <;> simp [phasePairSwapWeights] <;> exact hW _

theorem phasePairSwapWeights_norm_le (m n : Bool)
    (W : Fin 5 → ℝ → ℂ) {D : ℝ} (hW : ∀ i x, ‖W i x‖≤D) (i : Fin 5) (x : ℝ) :
    ‖phasePairSwapWeights m n W i x‖≤D := by
  cases m <;> cases n <;> fin_cases i <;> simp [phasePairSwapWeights] <;> exact hW _ _

theorem rectangularZeroArguments_continuous (q : QuadraticScales) (v : Fin 5 → ℕ)
    (i : Fin 5) : Continuous (fun x : ℝ => rectangularZeroArguments q v x i) := by
  fin_cases i <;> simp [rectangularZeroArguments] <;> fun_prop

theorem a03SixTensor_zero_joint_integrable
    (f : SchwartzMap A03SixTensorSpace ℂ) (a : A03SixTensorSpace → ℝ)
    (ham : Measurable a) (hc : Integrable (a03SixTensorCoefficient f a))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (m n : Bool) (q : QuadraticScales) (hB : 0<q.B) (hM₂ : 0<q.M₂)
    (v : Fin 5 → ℕ) (hv : ∀ j, 1≤v j) :
    Integrable (fun p : A03SixTensorSpace × ℝ => a03SixTensorCoefficient f a p.1*
      ((((v 1 : ℝ)/q.B : ℝ) : ℂ)^a03SixTensorExponent p.1 0*
        ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a p.1) i
          (rectangularZeroArguments q v p.2 i)))
      (volume.prod (volume.restrict (Ioi 0))) := by
  let d : ℝ := Nat.gcd (v 0*v 2) (v 1*v 3)
  let P : ℝ := (v 1 : ℝ)*(v 3 : ℝ)
  let L : ℝ := 2*d*q.M₂/P
  have hvpos (j : Fin 5) : 0<(v j : ℝ) := by exact_mod_cast (show 0<v j by have := hv j; omega)
  have hd : 0<d := by
    dsimp [d]
    exact_mod_cast Nat.gcd_pos_of_pos_left (v 1*v 3)
      (mul_pos (show 0<v 0 by have := hv 0; omega) (show 0<v 2 by have := hv 2; omega))
  have hP : 0<P := mul_pos (hvpos 1) (hvpos 3)
  have hden : 0<d*q.M₂ := mul_pos hd hM₂
  have hsW (ν : A03SixTensorSpace) (i : Fin 5) :
      RectangularComplexWeight (phasePairSwapWeights m n (a03SixTensorWeight a ν) i) :=
    phasePairSwapWeights_complexWeight m n _ (a03SixTensorWeight_complexWeight a ν) i
  have hprod_zero (ν : A03SixTensorSpace) (x : ℝ) (hx : x∉Icc 0 L) :
      (∏ i, phasePairSwapWeights m n (a03SixTensorWeight a ν) i
        (rectangularZeroArguments q v x i))=0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ (2 : Fin 5))
    by_contra hn
    have hs := (hsW ν 2).2 (subset_tsupport _ hn)
    have harg : rectangularZeroArguments q v x 2=P*x/(d*q.M₂) := by
      simp [rectangularZeroArguments,P,d]
    rw [harg] at hs
    have hlo := (le_div_iff₀ hden).mp hs.1
    have hhi := (div_le_iff₀ hden).mp hs.2
    apply hx
    constructor
    · by_contra hxneg
      have hneg : P*x<0 := mul_neg_of_pos_of_neg hP (lt_of_not_ge hxneg)
      linarith
    · dsimp [L]
      apply (le_div_iff₀ hP).mpr
      nlinarith only [hhi]
  have hphase : Continuous (fun ν : A03SixTensorSpace =>
      ((((v 1 : ℝ)/q.B : ℝ) : ℂ)^a03SixTensorExponent ν 0)) :=
    (a03SixTensorExponent_continuous 0).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr (div_pos (hvpos 1) hB).ne'))
  have hphase_norm (ν : A03SixTensorSpace) :
      ‖((((v 1 : ℝ)/q.B : ℝ) : ℂ)^a03SixTensorExponent ν 0)‖=1 :=
    a03SixTensor_character_norm ν (div_pos (hvpos 1) hB)
  have hprod_bound (ν : A03SixTensorSpace) (x : ℝ) :
      ‖∏ i, phasePairSwapWeights m n (a03SixTensorWeight a ν) i
        (rectangularZeroArguments q v x i)‖≤D^5 := by
    rw [norm_prod]
    calc
      _ ≤ ∏ _i : Fin 5, D := by
        apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        exact phasePairSwapWeights_norm_le m n _ (hW ν) i _
      _ = _ := by simp
  have hmeas : AEStronglyMeasurable (fun p : A03SixTensorSpace × ℝ =>
      a03SixTensorCoefficient f a p.1*
        ((((v 1 : ℝ)/q.B : ℝ) : ℂ)^a03SixTensorExponent p.1 0*
          ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a p.1) i
            (rectangularZeroArguments q v p.2 i)))
      (volume.prod (volume.restrict (Ioi 0))) := by
    have hswap (i : Fin 5) : ∃ j : Fin 5, ∀ ν,
        phasePairSwapWeights m n (a03SixTensorWeight a ν) i=a03SixTensorWeight a ν j := by
      cases m <;> cases n <;> fin_cases i <;>
        dsimp [phasePairSwapWeights] <;> exact ⟨_,fun _ => rfl⟩
    have hcont (ν : A03SixTensorSpace) : Continuous (fun x : ℝ =>
        ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a ν) i
          (rectangularZeroArguments q v x i)) := by
      apply continuous_finsetProd
      intro i _
      obtain ⟨j,hj⟩ := hswap i
      simp_rw [hj]
      exact ((a03SixTensorWeight_complexWeight a ν j).1.continuous).comp
        (rectangularZeroArguments_continuous q v i)
    have hmeas (x : ℝ) : Measurable (fun ν : A03SixTensorSpace =>
        ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a ν) i
          (rectangularZeroArguments q v x i)) := by
      apply Finset.measurable_fun_prod
      intro i _
      obtain ⟨j,hj⟩ := hswap i
      simp_rw [hj]
      exact a03SixTensorWeight_measurable a ham j _
    have hprod_meas : Measurable (fun p : A03SixTensorSpace × ℝ =>
        ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a p.1) i
          (rectangularZeroArguments q v p.2 i)) :=
      (measurable_uncurry_of_continuous_of_measurable hcont hmeas).comp measurable_swap
    exact ((a03SixTensorCoefficient_measurable f a ham).comp measurable_fst |>.mul
      ((hphase.measurable.comp measurable_fst).mul hprod_meas)).aestronglyMeasurable
  have hind : Integrable (fun x : ℝ => (Icc 0 L).indicator (fun _ => D^5) x)
      (volume.restrict (Ioi 0)) := by
    apply Integrable.restrict
    exact (integrable_indicator_iff measurableSet_Icc).mpr
      (integrableOn_const (measure_Icc_lt_top.ne))
  have hmajor := hc.norm.mul_prod hind
  apply hmajor.mono hmeas
  apply ae_of_all
  intro p
  by_cases hx : p.2∈Icc 0 L
  · simp only [Set.indicator_of_mem hx]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hD 5))]
    rw [norm_mul,norm_mul,hphase_norm,one_mul]
    exact mul_le_mul_of_nonneg_left (hprod_bound p.1 p.2) (norm_nonneg _)
  · simp only [Set.indicator_of_notMem hx,hprod_zero p.1 p.2 hx,mul_zero,norm_zero]
    exact le_rfl

theorem a03SixTensor_zero_inner_integrable
    (f : SchwartzMap A03SixTensorSpace ℂ) (a : A03SixTensorSpace → ℝ)
    (ham : Measurable a) (hc : Integrable (a03SixTensorCoefficient f a))
    {D : ℝ} (hD : 0≤D) (hW : ∀ ν i x, ‖a03SixTensorWeight a ν i x‖≤D)
    (m n : Bool) (q : QuadraticScales) (hB : 0<q.B) (hM₂ : 0<q.M₂)
    (v : Fin 5 → ℕ) (hv : ∀ j, 1≤v j) :
    Integrable (fun ν : A03SixTensorSpace => ∫ x : ℝ in Ioi 0,
      a03SixTensorCoefficient f a ν*
        ((((v 1 : ℝ)/q.B : ℝ) : ℂ)^a03SixTensorExponent ν 0*
          ∏ i, phasePairSwapWeights m n (a03SixTensorWeight a ν) i
            (rectangularZeroArguments q v x i))) :=
  (a03SixTensor_zero_joint_integrable f a ham hc hD hW m n q hB hM₂ v hv).integral_prod_left

end
end Sechstmoment
