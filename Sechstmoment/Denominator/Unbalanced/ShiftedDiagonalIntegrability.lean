import Sechstmoment.Denominator.Balanced.ShiftedDiagonalIntegrability
import Sechstmoment.Denominator.Unbalanced.ProfileDisintegration

/-! The original unbalanced shift integral has a compact edge support and
an integrable envelope uniform on bounded complex shift contours. -/
namespace Sechstmoment
open MeasureTheory Set Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def d04UnbalancedWeightedEdgeIntegrand (ρ : Fin 4 → ℝ → ℝ) (w : D01LogSpace → ℂ) :
    D01EdgeSpace → ℂ :=
  d01NonnegativeOrthant.indicator (fun x => (d04UnbalancedEdgeProfile ρ x : ℂ)*w (d01RowColumnSums x))

def d04UnbalancedCompactEdgeSet (A : Fin 4 → ℝ) : Set D01EdgeSpace :=
  d01NonnegativeOrthant∩Icc (fun _ => (0:ℝ)) (fun _ => d04UnbalancedEdgeBound A)

theorem d04UnbalancedCompactEdgeSet_compact (A : Fin 4 → ℝ) :
    IsCompact (d04UnbalancedCompactEdgeSet A) :=
  isCompact_Icc.inter_left d04UnbalancedOrthant_closed

theorem d04UnbalancedWeightedEdgeIntegral_eq_compactIntegral
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    (∫ x : D01EdgeSpace, d04UnbalancedWeightedEdgeIntegrand ρ w x) =
      ∫ x in d04UnbalancedCompactEdgeSet A,
        (d04UnbalancedEdgeProfile ρ x : ℂ)*w (d01RowColumnSums x) := by
  classical
  rw [← integral_indicator (d04UnbalancedCompactEdgeSet_compact A).measurableSet]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x∈d01NonnegativeOrthant
  · by_cases hp : d04UnbalancedEdgeProfile ρ x=0
    · simp [d04UnbalancedWeightedEdgeIntegrand,d04UnbalancedCompactEdgeSet,
        Set.indicator_apply,hx,hp]
    · have hK := d04UnbalancedEdge_profile_nonzero_bounded ρ A hρcap hx hp
      simp [d04UnbalancedWeightedEdgeIntegrand,d04UnbalancedCompactEdgeSet,hx,hK]
  · simp [d04UnbalancedWeightedEdgeIntegrand,d04UnbalancedCompactEdgeSet,hx]

theorem d04UnbalancedWeightedEdgeIntegrand_integrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) (hw : Continuous w) :
    Integrable (d04UnbalancedWeightedEdgeIntegrand ρ w) := by
  classical
  let E := d04UnbalancedCompactEdgeSet A
  let g := fun x : D01EdgeSpace => (d04UnbalancedEdgeProfile ρ x : ℂ)*w (d01RowColumnSums x)
  have hg : Continuous g :=
    (Complex.continuous_ofReal.comp (d04UnbalancedEdgeProfile_continuous ρ hρc)).mul
      (hw.comp d01RowColumnSums_continuous)
  have hE : IsCompact E := d04UnbalancedCompactEdgeSet_compact A
  have hi := (hg.continuousOn.integrableOn_compact (μ := volume) hE).integrable_indicator
    hE.measurableSet
  convert hi using 1
  funext x
  change d01NonnegativeOrthant.indicator g x = E.indicator g x
  by_cases hx : x∈d01NonnegativeOrthant
  · rw [indicator_of_mem hx]
    by_cases hn : g x=0
    · simp [Set.indicator_apply,hn]
    · have hp : d04UnbalancedEdgeProfile ρ x≠0 := by
        intro hz
        exact hn (by simp [g,hz])
      have hK := d04UnbalancedEdge_profile_nonzero_bounded ρ A hρcap hx hp
      rw [indicator_of_mem (show x∈E from ⟨hx,hK⟩)]
  · rw [indicator_of_notMem hx,indicator_of_notMem (show x∉E from fun he => hx he.1)]

def d04UnbalancedLogExponentialWeight (σ : Fin 2 → ℂ) (y : D01LogSpace) : ℂ :=
  Complex.exp (σ 0*((y.2 0:ℂ)-1/2)+σ 1*(1/2-(y.2 1:ℂ)))

theorem d04UnbalancedLogExponentialWeight_continuous (σ : Fin 2 → ℂ) :
    Continuous (d04UnbalancedLogExponentialWeight σ) := by
  unfold d04UnbalancedLogExponentialWeight
  fun_prop

theorem d04UnbalancedShiftedEdgeIntegral_eq_weighted
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) :
    d04UnbalancedShiftedEdgeIntegral ρ σ =
      ∫ x : D01EdgeSpace, d04UnbalancedWeightedEdgeIntegrand ρ
        (d04UnbalancedLogExponentialWeight σ) x := by
  unfold d04UnbalancedShiftedEdgeIntegral d01EdgeMeasure d04UnbalancedWeightedEdgeIntegrand
  rw [integral_indicator d01NonnegativeOrthant_measurable]
  rfl

theorem d04UnbalancedShiftedEdgeIntegrand_integrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Integrable (d04UnbalancedWeightedEdgeIntegrand ρ (d04UnbalancedLogExponentialWeight σ)) :=
  d04UnbalancedWeightedEdgeIntegrand_integrable ρ A _ hρc hρcap
    (d04UnbalancedLogExponentialWeight_continuous σ)

theorem d04UnbalancedEdge_columns_lt_one
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (hA : (∑ i, A i)<1)
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    {x : D01EdgeSpace} (hx : x∈d01NonnegativeOrthant)
    (hp : d04UnbalancedEdgeProfile ρ x≠0) (j : Fin 3) :
    0≤(d01RowColumnSums x).2 j ∧ (d01RowColumnSums x).2 j<1 := by
  have hpos := d01RowColumnSums_nonnegative hx
  have hbounds (i : Fin 4) : d04UnbalancedProfileCoordinates x i≤A i := by
    have hp' : (∏ i, ρ i (d04UnbalancedProfileCoordinates x i))≠0 := by
      simpa only [← d04UnbalancedEdgeProfile_eq_prod] using hp
    exact (hρcap i _ ((Finset.prod_ne_zero_iff.mp hp') i (Finset.mem_univ i))).2
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hbounds i)
  have htot := d01RowColumnSums_total x
  have hcol := Finset.single_le_sum (fun i (_ : i∈Finset.univ) => hpos.2 i)
    (Finset.mem_univ j)
  have hlast := hpos.2 2
  have hsum' : (∑ i : Fin 3, (d01RowColumnSums x).1 i)+
      (d01RowColumnSums x).2 2≤∑ i, A i := by
    convert hsum using 1
    simp [d04UnbalancedProfileCoordinates,Fin.sum_univ_succ]
    ring
  exact ⟨hpos.2 j, by linarith⟩

theorem d04UnbalancedShiftedEdgeIntegrand_localized_norm_le
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hA : (∑ i, A i)<1) (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    {R : ℝ} (hR : 0≤R) (hσ : ∀ j, ‖σ j‖≤R) (x : D01EdgeSpace) :
    ‖d04UnbalancedWeightedEdgeIntegrand ρ (d04UnbalancedLogExponentialWeight σ) x‖≤
      ‖d04UnbalancedWeightedEdgeIntegrand ρ (fun _ => 1) x‖*Real.exp R := by
  by_cases hx : x∈d01NonnegativeOrthant
  · by_cases hp : d04UnbalancedEdgeProfile ρ x=0
    · simp [d04UnbalancedWeightedEdgeIntegrand,hx,hp]
    · have h₀ := d04UnbalancedEdge_columns_lt_one ρ A hA hρcap hx hp 0
      have h₁ := d04UnbalancedEdge_columns_lt_one ρ A hA hρcap hx hp 1
      have ha : |(d01RowColumnSums x).2 0-1/2|≤1/2 :=
        abs_le.mpr ⟨by linarith,by linarith⟩
      have hb : |1/2-(d01RowColumnSums x).2 1|≤1/2 :=
        abs_le.mpr ⟨by linarith,by linarith⟩
      have he := d02CenteredExponent_norm_le σ hR hσ ha hb
      have hcast (s : ℝ) : (s:ℂ)-1/2=((s-1/2:ℝ):ℂ) := by push_cast; rfl
      have hcast' (s : ℝ) : 1/2-(s:ℂ)=((1/2-s:ℝ):ℂ) := by push_cast; rfl
      simp only [d04UnbalancedWeightedEdgeIntegrand,indicator_of_mem hx,norm_mul,mul_one]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [d04UnbalancedLogExponentialWeight,hcast,hcast'] using he
  · simp [d04UnbalancedWeightedEdgeIntegrand,indicator_of_notMem hx]

theorem d04UnbalancedShiftedEdgeIntegrand_dominator_integrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (R : ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Integrable (fun x : D01EdgeSpace =>
      ‖d04UnbalancedWeightedEdgeIntegrand ρ (fun _ => 1) x‖*Real.exp R) :=
  (d04UnbalancedWeightedEdgeIntegrand_integrable ρ A _ hρc hρcap continuous_const).norm.mul_const _


theorem d04UnbalancedShiftedEdgeIntegral_continuous
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Continuous (d04UnbalancedShiftedEdgeIntegral ρ) := by
  change Continuous (fun σ : Fin 2 → ℂ => d04UnbalancedShiftedEdgeIntegral ρ σ)
  simp_rw [d04UnbalancedShiftedEdgeIntegral_eq_weighted,
    d04UnbalancedWeightedEdgeIntegral_eq_compactIntegral ρ A _ hρcap]
  have hF : Continuous (fun y : (Fin 2 → ℂ) × D01EdgeSpace =>
      (d04UnbalancedEdgeProfile ρ y.2 : ℂ)*
        d04UnbalancedLogExponentialWeight y.1 (d01RowColumnSums y.2)) := by
    have hp := d04UnbalancedEdgeProfile_continuous ρ hρc
    have hs := d01RowColumnSums_continuous
    unfold d04UnbalancedLogExponentialWeight
    fun_prop
  exact continuous_parametric_integral_of_continuous hF
    (d04UnbalancedCompactEdgeSet_compact A)

theorem d04UnbalancedShiftedEdgeIntegral_bounded
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ)
    (hA : (∑ i, A i)<1) (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i))
    {R : ℝ} (hR : 0≤R) :
    ∃ C : ℝ, 0≤C ∧ ∀ σ : Fin 2 → ℂ, (∀ j, ‖σ j‖≤R) →
      ‖d04UnbalancedShiftedEdgeIntegral ρ σ‖≤C := by
  let g := fun x : D01EdgeSpace =>
    ‖d04UnbalancedWeightedEdgeIntegrand ρ (fun _ => 1) x‖*Real.exp R
  have hg : Integrable g :=
    d04UnbalancedShiftedEdgeIntegrand_dominator_integrable ρ A R hρc hρcap
  refine ⟨∫ x, g x, integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le), ?_⟩
  intro σ hσ
  rw [d04UnbalancedShiftedEdgeIntegral_eq_weighted]
  apply norm_integral_le_of_norm_le hg
  exact ae_of_all _ (d04UnbalancedShiftedEdgeIntegrand_localized_norm_le ρ A σ hA hρcap hR hσ)

end
end Sechstmoment
