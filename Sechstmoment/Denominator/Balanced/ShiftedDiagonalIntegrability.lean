import Sechstmoment.Denominator.Balanced.ProfileDisintegration
import Sechstmoment.Denominator.Balanced.SharpLogCutoff


namespace Sechstmoment
open MeasureTheory Set Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def d02BalancedWeightedEdgeIntegrand (ρ : Fin 4 → ℝ → ℝ) (w : D01LogSpace → ℂ) :
    D01EdgeSpace → ℂ :=
  d02BalancedEdgeCut.indicator (fun x => (d02BalancedEdgeProfile ρ x : ℂ)*w (d01RowColumnSums x))

theorem d02BalancedWeightedEdgeIntegrand_integrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) (hw : Continuous w) :
    Integrable (d02BalancedWeightedEdgeIntegrand ρ w) := by
  classical
  let K := Icc (fun _ : Fin 3 × Fin 3 => (0:ℝ)) (fun _ => d02BalancedEdgeBound A)
  let E := d02BalancedEdgeCut∩K
  let g := fun x : D01EdgeSpace => (d02BalancedEdgeProfile ρ x : ℂ)*w (d01RowColumnSums x)
  have hg : Continuous g :=
    (Complex.continuous_ofReal.comp (d02BalancedEdgeProfile_continuous ρ hρc)).mul
      (hw.comp d01RowColumnSums_continuous)
  have hE : IsCompact E := (isCompact_Icc : IsCompact K).inter_left d02BalancedEdgeCut_closed
  have hi := (hg.continuousOn.integrableOn_compact (μ := volume) hE).integrable_indicator
    hE.measurableSet
  convert hi using 1
  funext x
  change d02BalancedEdgeCut.indicator g x = E.indicator g x
  by_cases hx : x∈d02BalancedEdgeCut
  · rw [indicator_of_mem hx]
    by_cases hn : g x=0
    · simp [Set.indicator_apply,hn]
    · have hprofile : d02BalancedEdgeProfile ρ x≠0 := by
        intro hz
        exact hn (by simp [g,hz])
      have hK : x∈K := d02BalancedEdge_profile_nonzero_bounded ρ A hρcap hx hprofile
      rw [indicator_of_mem (show x∈E from ⟨hx,hK⟩)]
  · have hnot : x∉E := fun he => hx he.1
    rw [indicator_of_notMem hx,indicator_of_notMem hnot]

def d02BalancedLogExponentialWeight (σ : Fin 2 → ℂ) (y : D01LogSpace) : ℂ :=
  Complex.exp (σ 0*(1/2-(y.1 0 : ℂ))+σ 1*(1/2-(y.2 0 : ℂ)))+
    Complex.exp (σ 0*((y.2 0 : ℂ)-1/2)+σ 1*((y.1 0 : ℂ)-1/2))

theorem d02BalancedLogExponentialWeight_continuous (σ : Fin 2 → ℂ) :
    Continuous (d02BalancedLogExponentialWeight σ) := by
  unfold d02BalancedLogExponentialWeight
  fun_prop

theorem d02CenteredExponent_norm_le (σ : Fin 2 → ℂ) {R u v : ℝ}
    (hR : 0≤R) (hσ : ∀ j, ‖σ j‖≤R) (hu : |u|≤1/2) (hv : |v|≤1/2) :
    ‖Complex.exp (σ 0*(u : ℂ)+σ 1*(v : ℂ))‖≤Real.exp R := by
  have hz : ‖σ 0*(u : ℂ)+σ 1*(v : ℂ)‖≤R := by
    calc
      _ ≤ ‖σ 0‖*|u|+‖σ 1‖*|v| := by
        simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs] using
          norm_add_le (σ 0*(u : ℂ)) (σ 1*(v : ℂ))
      _ ≤ R*(1/2)+R*(1/2) := add_le_add
        (mul_le_mul (hσ 0) hu (abs_nonneg u) hR)
        (mul_le_mul (hσ 1) hv (abs_nonneg v) hR)
      _ = R := by ring
  rw [Complex.norm_exp]
  exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hz)

theorem d02BalancedLogExponentialWeight_norm_le (σ : Fin 2 → ℂ) {R : ℝ}
    (hR : 0≤R) (hσ : ∀ j, ‖σ j‖≤R) {y : D01LogSpace}
    (hy : y∈d01PositiveOrthant) (hcut : y∈d02SharpLogRegion) :
    ‖d02BalancedLogExponentialWeight σ y‖≤2*Real.exp R := by
  have ha := hy.1 0
  have hb := hy.2 0
  have hc : y.1 0+y.2 0≤1 := hcut
  have h₁ : |1/2-y.1 0|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h₂ : |1/2-y.2 0|≤1/2 := abs_le.mpr ⟨by linarith,by linarith⟩
  have h₃ : |y.1 0-1/2|≤1/2 := by rw [abs_sub_comm]; exact h₁
  have h₄ : |y.2 0-1/2|≤1/2 := by rw [abs_sub_comm]; exact h₂
  have hd := d02CenteredExponent_norm_le σ hR hσ h₁ h₂
  have he := d02CenteredExponent_norm_le σ hR hσ h₄ h₃
  unfold d02BalancedLogExponentialWeight
  have hcast (t : ℝ) : (1/2-(t : ℂ)) = ((1/2-t : ℝ) : ℂ) := by push_cast; rfl
  have hcast' (t : ℝ) : ((t : ℂ)-1/2) = ((t-1/2 : ℝ) : ℂ) := by push_cast; rfl
  simp_rw [hcast,hcast']
  exact (norm_add_le _ _).trans ((add_le_add hd he).trans_eq (by ring))

theorem d02BalancedShiftedEdgeIntegrand_integrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Integrable (d02BalancedWeightedEdgeIntegrand ρ (d02BalancedLogExponentialWeight σ)) :=
  d02BalancedWeightedEdgeIntegrand_integrable ρ A _ hρc hρcap
    (d02BalancedLogExponentialWeight_continuous σ)

theorem d02BalancedShiftedEdgeIntegrand_uniform_norm_le
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) {R : ℝ}
    (hR : 0≤R) (hσ : ∀ j, ‖σ j‖≤R) (x : D01EdgeSpace) :
    ‖d02BalancedWeightedEdgeIntegrand ρ (d02BalancedLogExponentialWeight σ) x‖≤
      |d02BalancedEdgeProfile ρ x| * (2*Real.exp R) := by
  by_cases hx : x∈d02BalancedEdgeCut
  · rw [d02BalancedWeightedEdgeIntegrand,indicator_of_mem hx,norm_mul]
    have hy : d01RowColumnSums x∈d01PositiveOrthant := d01RowColumnSums_nonnegative hx.1
    have hc : d01RowColumnSums x∈d02SharpLogRegion := hx.2
    simpa only [Complex.norm_real,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_left (d02BalancedLogExponentialWeight_norm_le σ hR hσ hy hc)
        (norm_nonneg (d02BalancedEdgeProfile ρ x : ℂ))
  · simp only [d02BalancedWeightedEdgeIntegrand,indicator_of_notMem hx,norm_zero]
    exact mul_nonneg (abs_nonneg _) (by positivity)

theorem d02BalancedShiftedEdgeIntegrand_localized_norm_le
    (ρ : Fin 4 → ℝ → ℝ) (σ : Fin 2 → ℂ) {R : ℝ}
    (hR : 0≤R) (hσ : ∀ j, ‖σ j‖≤R) (x : D01EdgeSpace) :
    ‖d02BalancedWeightedEdgeIntegrand ρ (d02BalancedLogExponentialWeight σ) x‖≤
      ‖d02BalancedWeightedEdgeIntegrand ρ (fun _ => 1) x‖*(2*Real.exp R) := by
  by_cases hx : x∈d02BalancedEdgeCut
  · simpa only [d02BalancedWeightedEdgeIntegrand,indicator_of_mem hx,mul_one,
      Complex.norm_real,Real.norm_eq_abs] using
      d02BalancedShiftedEdgeIntegrand_uniform_norm_le ρ σ hR hσ x
  · simp [d02BalancedWeightedEdgeIntegrand,indicator_of_notMem hx]

theorem d02BalancedShiftedEdgeIntegrand_dominator_integrable
    (ρ : Fin 4 → ℝ → ℝ) (A : Fin 4 → ℝ) (R : ℝ)
    (hρc : ∀ i, Continuous (ρ i))
    (hρcap : ∀ i t, ρ i t≠0 → t∈Icc 0 (A i)) :
    Integrable (fun x : D01EdgeSpace =>
      ‖d02BalancedWeightedEdgeIntegrand ρ (fun _ => 1) x‖*(2*Real.exp R)) :=
  (d02BalancedWeightedEdgeIntegrand_integrable ρ A _ hρc hρcap continuous_const).norm.mul_const _

end
end Sechstmoment
