import Sechstmoment.Denominator.Unbalanced.Expansion.DiagonalActual
import Sechstmoment.Denominator.Unbalanced.FiniteMainTerm

/-! The actual one-sided profile/pair expansion has exactly the original
D01 diagonal, with an explicit positive-index bijection. -/
namespace Sechstmoment
open Complex Real Set Filter MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 1500000

abbrev D04PositiveDiagonal := {u : (Fin 4 → ℕ) × (ℕ × ℕ) //
  d04OneSidedModelDiagonal u.1 u.2}

def d04DiagonalToD01 (u : D04PositiveDiagonal) : DiagonalSixIndices :=
  ⟨((u.val.1 0+1,u.val.1 1+1,u.val.1 2+1),
    (u.val.2.1+1,u.val.2.2+1,u.val.1 3+1)),by
      constructor
      · have h := u.property
        unfold d04OneSidedModelDiagonal d04ProfileH d04ProfileK at h
        simpa only [mul_assoc] using h.symm
      · positivity⟩

def d04DiagonalFromD01 (x : DiagonalSixIndices) : D04PositiveDiagonal :=
  ⟨(![d01LeftIndices x 0-1,d01LeftIndices x 1-1,d01LeftIndices x 2-1,
      d01RightIndices x 2-1],(d01RightIndices x 0-1,d01RightIndices x 1-1)),by
    have hl (i : Fin 3) : d01LeftIndices x i-1+1=d01LeftIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x i))
    have hr (i : Fin 3) : d01RightIndices x i-1+1=d01RightIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x i))
    change (d01RightIndices x 0-1+1)*(d01RightIndices x 1-1+1)*
      (d01RightIndices x 2-1+1)=
      (d01LeftIndices x 0-1+1)*(d01LeftIndices x 1-1+1)*(d01LeftIndices x 2-1+1)
    simp_rw [hl,hr]
    simpa [d01LeftIndices,d01RightIndices,mul_assoc] using x.property.1.symm⟩

def d04PositiveDiagonalEquiv : D04PositiveDiagonal ≃ DiagonalSixIndices where
  toFun := d04DiagonalToD01
  invFun := d04DiagonalFromD01
  left_inv u := by
    apply Subtype.ext
    apply Prod.ext
    · funext j
      fin_cases j <;> simp [d04DiagonalToD01,d04DiagonalFromD01,d01LeftIndices,d01RightIndices]
    · simp [d04DiagonalToD01,d04DiagonalFromD01,d01RightIndices]
  right_inv x := by
    apply Subtype.ext
    have hl (i : Fin 3) : d01LeftIndices x i-1+1=d01LeftIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01LeftIndices_pos x i))
    have hr (i : Fin 3) : d01RightIndices x i-1+1=d01RightIndices x i :=
      Nat.sub_add_cancel (Nat.succ_le_iff.2 (d01RightIndices_pos x i))
    change ((d01LeftIndices x 0-1+1,d01LeftIndices x 1-1+1,d01LeftIndices x 2-1+1),
      (d01RightIndices x 0-1+1,d01RightIndices x 1-1+1,d01RightIndices x 2-1+1))=x.val
    simp_rw [hl,hr]
    rfl

private def d04DiagonalToD02 (u : D04PositiveDiagonal) : D02PositiveDiagonal :=
  ⟨![u.val.1 1,u.val.1 2,u.val.2.2,u.val.1 3,u.val.1 0,u.val.2.1],by
    have h := u.property
    unfold d04OneSidedModelDiagonal d04ProfileH d04ProfileK at h
    simpa [d02SixIsDiagonal,d02SixIndexH,d02SixIndexK,d02SixIndexM,d02SixIndexN,
      mul_comm,mul_left_comm,mul_assoc] using h.symm⟩

private theorem d04DiagonalToD02_toD01 (u : D04PositiveDiagonal) :
    d02DiagonalToD01 (d04DiagonalToD02 u)=d04DiagonalToD01 u := rfl

theorem d04_diagonal_half_coefficient (u : D04PositiveDiagonal) :
    ((∏ j : Fin 4,(u.val.1 j+1 : ℂ)^(-(1/2 : ℂ)))*
      (u.val.2.1+1 : ℂ)^(-(1/2 : ℂ)))*
        (u.val.2.2+1 : ℂ)^(-(1/2 : ℂ))=
      1/(d01CommonProduct (d04DiagonalToD01 u) : ℂ) := by
  have h := d02_diagonal_half_coefficient_eq_one_div (d04DiagonalToD02 u)
  rw [d04DiagonalToD02_toD01] at h
  rw [← h]
  simp only [Fin.prod_univ_four,Fin.prod_univ_six]
  change (((((u.val.1 0+1 : ℂ)^(-(1/2 : ℂ)) *
    (u.val.1 1+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.1 2+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.1 3+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.2.1+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.2.2+1 : ℂ)^(-(1/2 : ℂ)) =
    (((((u.val.1 1+1 : ℂ)^(-(1/2 : ℂ)) *
    (u.val.1 2+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.2.2+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.1 3+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.1 0+1 : ℂ)^(-(1/2 : ℂ))) *
    (u.val.2.1+1 : ℂ)^(-(1/2 : ℂ))
  ring

theorem d04OneSidedProfileMultiplier_diagonal_logPoint
    (T : ℝ) (ρ : Fin 4 → ℝ → ℝ) (u : D04PositiveDiagonal) :
    (∏ j : Fin 4,(ρ j (Real.log (u.val.1 j+1 : ℝ)/Real.log T) : ℂ))=
      d04OneSidedProfileProduct (fun j t => (ρ j t : ℂ))
        (d01LogPoint (Real.log T) (d04DiagonalToD01 u)) := by
  simp [Fin.prod_univ_four,d04OneSidedProfileProduct,d01LogPoint,
    d01LeftIndices,d01RightIndices,d04DiagonalToD01]

theorem d04OneSidedModelCoefficient_diagonal_identity
    (T : ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (u : D04PositiveDiagonal) :
    d04OneSidedModelCoefficient T ρ σ u.val.1 u.val.2=
      d04OneSidedLiteralDiagonalTerm T ρ σ (d04DiagonalToD01 u) := by
  have hm0 : (u.val.2.1+1 : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero u.val.2.1
  have hn0 : (u.val.2.2+1 : ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero u.val.2.2
  have hm : (u.val.2.1+1 : ℂ)^(-d04NegativeZetaArguments T 0 σ 0)=
      (u.val.2.1+1 : ℂ)^(-(1/2 : ℂ))*
        (u.val.2.1+1 : ℂ)^(σ 0/(Real.log T : ℂ)) := by
    have he : -d04NegativeZetaArguments T 0 σ 0=
      -(1/2 : ℂ)+σ 0/(Real.log T : ℂ) := by
      simp [d04NegativeZetaArguments,criticalLinePoint]
      ring
    rw [he,Complex.cpow_add _ _ hm0]
  have hn : (u.val.2.2+1 : ℂ)^(-d04NegativeZetaArguments T 0 σ 1)=
      (u.val.2.2+1 : ℂ)^(-(1/2 : ℂ))*
        (u.val.2.2+1 : ℂ)^(-(σ 1/(Real.log T : ℂ))) := by
    have he : -d04NegativeZetaArguments T 0 σ 1=
      -(1/2 : ℂ)+(-(σ 1/(Real.log T : ℂ))) := by
      simp [d04NegativeZetaArguments,criticalLinePoint]
      ring
    rw [he,Complex.cpow_add _ _ hn0]
  have hlit : literalDiagonalSixTerm (fun _ => 0)
      ![-σ 0/(Real.log T : ℂ),σ 1/(Real.log T : ℂ),0] (d04DiagonalToD01 u)=
      ((u.val.2.1+1 : ℂ)^(σ 0/(Real.log T : ℂ))*
        (u.val.2.2+1 : ℂ)^(-(σ 1/(Real.log T : ℂ))))*
        (1/(d01CommonProduct (d04DiagonalToD01 u) : ℂ)) := by
    simp [literalDiagonalSixTerm,literalTripleDirichletTerm,shiftedPowerArithmetic,
      d04DiagonalToD01,d01CommonProduct,neg_div,Complex.cpow_neg_one,one_div]
  rw [d04OneSidedLiteralDiagonalTerm,hlit,
    ← d04_diagonal_half_coefficient,← d04OneSidedProfileMultiplier_diagonal_logPoint]
  unfold d04OneSidedModelCoefficient d04ProfileCoefficient d04OneSidedPairCoefficient
    d04OneSidedRawSummand
  rw [Finset.prod_mul_distrib,hm,hn]
  have hmidx : d01RightIndices (d04DiagonalToD01 u) 0=u.val.2.1+1 := rfl
  have hnidx : d01RightIndices (d04DiagonalToD01 u) 1=u.val.2.2+1 := rfl
  rw [hmidx,hnidx]
  simp only [Nat.cast_add,Nat.cast_one]
  ring

theorem d04_positive_diagonal_coefficient_tsum (T : ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (σ : Fin 2 → ℂ) :
    (∑' u : D04PositiveDiagonal,d04OneSidedModelCoefficient T ρ σ u.val.1 u.val.2)=
      ∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x := by
  calc
    _ = ∑' u : D04PositiveDiagonal,
      d04OneSidedLiteralDiagonalTerm T ρ σ (d04PositiveDiagonalEquiv u) := by
        apply tsum_congr
        exact fun u => d04OneSidedModelCoefficient_diagonal_identity T ρ σ u
    _ = _ := d04PositiveDiagonalEquiv.tsum_eq _

def d04OneSidedModelDiagonalSum (T : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (σ : Fin 2 → ℂ) : ℂ :=
  ∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
    if d04OneSidedModelDiagonal h n then d04OneSidedModelCoefficient T ρ σ h n else 0

/-- The finite profile cut is merely the exact support of the original
profiles; after selecting the arithmetic diagonal it is the full D01 sum. -/
theorem d04OneSidedModel_diagonal_sum_identity {T : ℝ} (hT : 1<T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ)
    (hcap : ∀ j t,a j<t → ρ j t=0)
    (hs : Summable (fun u : (Fin 4 → ℕ) × (ℕ × ℕ) =>
      ‖d04OneSidedModelCoefficient T ρ σ u.1 u.2‖)) :
    (∑ h∈d04ProfileBox T a,∑' n : ℕ × ℕ,
      if d04OneSidedModelDiagonal h n then d04OneSidedModelCoefficient T ρ σ h n else 0)=
      ∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x := by
  classical
  let f := fun u : (Fin 4 → ℕ) × (ℕ × ℕ) =>
    if d04OneSidedModelDiagonal u.1 u.2 then d04OneSidedModelCoefficient T ρ σ u.1 u.2 else 0
  have hf : Summable f := by
    apply Summable.of_norm_bounded hs
    intro u
    dsimp [f]
    split_ifs <;> simp
  calc
    _ = ∑' h : Fin 4 → ℕ,∑' n : ℕ × ℕ,f (h,n) := by
      symm
      apply tsum_eq_sum
      intro h hh
      have hz := d04ProfileCoefficient_zero_outside_box hT a ρ hcap h hh
      simp [f,d04OneSidedModelCoefficient,hz]
    _ = ∑' u : (Fin 4 → ℕ) × (ℕ × ℕ),f u := hf.tsum_prod.symm
    _ = ∑' u : D04PositiveDiagonal,d04OneSidedModelCoefficient T ρ σ u.val.1 u.val.2 := by
      have he := tsum_subtype
        {u : (Fin 4 → ℕ) × (ℕ × ℕ) | d04OneSidedModelDiagonal u.1 u.2}
        (fun u => d04OneSidedModelCoefficient T ρ σ u.1 u.2)
      apply Eq.trans _ he.symm
      apply tsum_congr
      intro u
      by_cases hu : d04OneSidedModelDiagonal u.1 u.2 <;> simp [f,hu]
    _ = _ := d04_positive_diagonal_coefficient_tsum T ρ σ

theorem d04OneSidedModel_diagonal_sum_identity_actual {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ)
    (hcap : ∀ j t,a j<t → ρ j t=0) (hσ : ∀ i,‖σ i‖≤R) :
    d04OneSidedModelDiagonalSum T a ρ σ=
      ∑' x : DiagonalSixIndices,d04OneSidedLiteralDiagonalTerm T ρ σ x :=
  d04OneSidedModel_diagonal_sum_identity hT a ρ σ hcap
    (d04_oneSided_model_coefficient_norm_summable hT hR (Real.log_pos hT) hRL
      a ρ hcap σ hσ)

theorem d04OneSidedModel_diagonal_measure_identity {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ)
    (hcap : ∀ j t,a j<t → ρ j t=0) (hσ : ∀ i,‖σ i‖≤R) :
    d04OneSidedModelDiagonalSum T a ρ σ/(Real.log T : ℂ)^9=
      ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct (fun i t => (ρ i t : ℂ)) y*
        (d04OneSidedLogSmoothing (Real.log T) y : ℂ)
          ∂d01DiagonalMeasure (Real.log T) := by
  rw [d04OneSidedModel_diagonal_sum_identity_actual hT hR hRL a ρ σ hcap hσ]
  exact d04OneSidedLiteralDiagonal_measure_identity hT ρ σ

/-- Closed diagonal convergence for the actual finite profile expansion,
with absolute summability proved from its literal coefficients. -/
theorem d04OneSidedModel_diagonal_limit
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ i,Continuous (ρ i))
    (hρcap : ∀ i t,ρ i t≠0 → t∈Icc 0 (a i))
    (ha3 : 0≤a 3) (ha : (∑ i,a i)<1) :
    Tendsto (fun T : ℝ => d04OneSidedModelDiagonalSum T a ρ σ/(Real.log T : ℂ)^9)
      atTop (𝓝 ((arithmeticFactor : ℂ)*d04UnbalancedShiftedEdgeIntegral ρ σ)) := by
  let R := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := by dsimp [R]; positivity
  have hσ : ∀ i,‖σ i‖≤R := by
    intro i; fin_cases i <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  have hcap : ∀ i t,a i<t → ρ i t=0 := by
    intro i t ht
    by_contra hn
    exact (not_lt_of_ge (hρcap i t hn).2) ht
  apply (d04OneSidedLiteralDiagonal_limit ρ a σ hρc hρcap ha3 ha).congr'
  filter_upwards [eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*R))] with T hT hRL
  rw [d04OneSidedModel_diagonal_sum_identity_actual hT hR hRL a ρ σ hcap hσ]

theorem d04OneSidedModel_diagonal_eventually_uniformly_bounded
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρc : ∀ i,Continuous (ρ i))
    (hρcap : ∀ i t,ρ i t≠0 → t∈Icc 0 (a i))
    (ha3 : 0≤a 3) (ha : (∑ i,a i)<1) {R : ℝ} (hR : 0≤R) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ T : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖d04OneSidedModelDiagonalSum T a ρ σ/(Real.log T : ℂ)^9‖≤B := by
  obtain ⟨B,hB,hbound⟩ := d04OneSidedLiteralDiagonal_eventually_uniformly_bounded
    ρ a hρc hρcap ha3 ha hR
  have hcap : ∀ i t,a i<t → ρ i t=0 := by
    intro i t ht
    by_contra hn
    exact (not_lt_of_ge (hρcap i t hn).2) ht
  refine ⟨B,hB,?_⟩
  filter_upwards [hbound,eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop (2*R))] with T hb hT hRL
  intro σ hσ
  rw [d04OneSidedModel_diagonal_sum_identity_actual hT hR hRL a ρ σ hcap hσ]
  exact hb σ hσ

theorem d04OneSidedModel_diagonal_physical_time_identity {T R : ℝ}
    (hT : 1<T) (hR : 0≤R) (hRL : 2*R≤Real.log T)
    (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) (Φ : ℝ → ℝ)
    (hcap : ∀ j t,a j<t → ρ j t=0) (hσ : ∀ i,‖σ i‖≤R) :
    (∫ t : ℝ,(Φ (t/T) : ℂ)*d04CenteringPurePower T t (σ 0)*
      d04OneSidedModelDiagonalSum T a ρ σ)/((T : ℂ)*(Real.log T : ℂ)^9)=
      (∫ τ : ℝ,(Φ τ : ℂ)*d04CenteringPurePower T (T*τ) (σ 0))*
        (d04OneSidedModelDiagonalSum T a ρ σ/(Real.log T : ℂ)^9) := by
  rw [d04OneSidedModel_diagonal_sum_identity_actual hT hR hRL a ρ σ hcap hσ]
  exact d04OneSidedLiteralDiagonal_physical_time_identity (zero_lt_one.trans hT) ρ σ Φ

end
end Sechstmoment
