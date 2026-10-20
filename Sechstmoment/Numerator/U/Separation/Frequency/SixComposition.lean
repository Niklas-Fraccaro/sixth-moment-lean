import Sechstmoment.Numerator.U.Separation.Frequency.FrequencyComposition
import Sechstmoment.Numerator.U.Separation.Frequency.GammaProfile
import Sechstmoment.Numerator.U.Separation.Frequency.LogSymbol
import Sechstmoment.Numerator.U.Separation.Tensor.SixFourier

namespace Sechstmoment
open Complex Real Source Set MeasureTheory
open scoped BigOperators ContDiff Topology
noncomputable section
set_option maxHeartbeats 2000000

def a03SixGapLinear : A03SixTensorSpace →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 6 => ℝ) 1-PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 6 => ℝ) 0-
    PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 6 => ℝ) 4-PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 6 => ℝ) 5

theorem a03SixGapLinear_apply (y : A03SixTensorSpace) :
    a03SixGapLinear y=y 1-y 0-y 4-y 5 := by
  rfl

theorem a03SixGapLinear_norm_le : ‖a03SixGapLinear‖≤4 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [a03SixGapLinear_apply]
  have h := norm_sub_le (y 1-y 0-y 4) (y 5)
  have h' := norm_sub_le (y 1-y 0) (y 4)
  have h'' := norm_sub_le (y 1) (y 0)
  have h0 := PiLp.norm_apply_le y (0 : Fin 6)
  have h1 := PiLp.norm_apply_le y (1 : Fin 6)
  have h4 := PiLp.norm_apply_le y (4 : Fin 6)
  have h5 := PiLp.norm_apply_le y (5 : Fin 6)
  linarith

def a03SixGapDomain : Set A03SixTensorSpace := a03SixGapLinear ⁻¹'Ioo (-4) 2

theorem a03SixGapDomain_isOpen : IsOpen a03SixGapDomain :=
  isOpen_Ioo.preimage a03SixGapLinear.continuous

theorem a03SixGapDomain_contains_log_box {y : A03SixTensorSpace}
    (hy : ∀ j, y j∈Icc (-1/10 : ℝ) (11/10)) : y∈a03SixGapDomain := by
  change a03SixGapLinear y∈Ioo (-4) 2
  rw [a03SixGapLinear_apply]
  have h0 := hy 0
  have h1 := hy 1
  have h4 := hy 4
  have h5 := hy 5
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2,h4.1,h4.2,h5.1,h5.2]

def a03LogSymbolBudget (n : ℕ) : ℝ := (n.factorial : ℝ)*10^n*100
def a03FrequencySixBudget (C : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  ((n.factorial : ℝ)*(2^n*200^n*phaseFrequencyCompositionBudget C n)*
    (phaseSymbolCompositionBudget a03LogSymbolBudget n)^n)*4^n

theorem a03LogSymbolBudget_nonneg (n : ℕ) : 0≤a03LogSymbolBudget n := by
  unfold a03LogSymbolBudget
  positivity

theorem a03FrequencySixBudget_nonneg (C : ℕ → ℕ → ℝ) (hC : ∀ i j, 0≤C i j) (n : ℕ) :
    0≤a03FrequencySixBudget C n := by
  have hb : 0≤phaseFrequencyCompositionBudget C n := by
    unfold phaseFrequencyCompositionBudget
    exact Finset.sum_nonneg (fun i _ => add_nonneg (hC i 0) (hC i n))
  have hs : 0≤phaseSymbolCompositionBudget a03LogSymbolBudget n := by
    unfold phaseSymbolCompositionBudget
    exact add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => a03LogSymbolBudget_nonneg i))
  unfold a03FrequencySixBudget
  positivity

theorem a03_log_gap_symbol_contDiffOn {T r s : ℝ}
    (hr : 0≤r) (hr1 : r≤1/100) (hs : |s|≤1) :
    ContDiffOn ℝ ∞ (a03RealLogGapSymbol T r s) (Ioo (-4) 2) := by
  intro x hx
  exact (a03_log_gap_symbol_real_contDiffAt (T := T) hr hr1 hs
    (a03_log_box_exponential_range ⟨hx.1.le,hx.2.le⟩).2).contDiffWithinAt

theorem a03_log_gap_symbol_within_bound {T r s : ℝ}
    (hT : 0≤T) (hr : 0≤r) (hr1 : r≤1/100) (hs : |s|≤1)
    {x : ℝ} (hx : x∈Ioo (-4) 2) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (a03RealLogGapSymbol T r s) (Ioo (-4) 2) x‖≤
      a03LogSymbolBudget n*(1+T*r) := by
  have hexp := (a03_log_box_exponential_range ⟨hx.1.le,hx.2.le⟩).2
  have hcd := a03_log_gap_symbol_real_contDiffAt (T := T) hr hr1 hs hexp
  rw [iteratedFDerivWithin_eq_iteratedFDeriv isOpen_Ioo.uniqueDiffOn (hcd.of_le (by simp)) hx,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := a03_log_gap_symbol_real_derivative_bound hT hr hr1 hs hexp n
  change ‖iteratedDeriv n (a03RealLogGapSymbol T r s) x‖≤_
  calc
    _ ≤ a03LogSymbolBudget n*(T*r) := by simpa only [a03LogSymbolBudget,mul_assoc] using h
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (a03LogSymbolBudget_nonneg n)

theorem a03_log_frequency_composition_contDiffOn
    {T r s : ℝ} (hr : 0≤r) (hr1 : r≤1/100) (hs : |s|≤1)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) :
    ContDiffOn ℝ ∞ (g ∘ a03RealLogGapSymbol T r s) (Ioo (-4) 2) :=
  hg.comp_contDiffOn (a03_log_gap_symbol_contDiffOn (T := T) hr hr1 hs)

theorem a03_log_frequency_composition_bound
    {T r s D : ℝ} (hT : 0≤T) (hr : 0≤r) (hr1 : r≤1/100) (hs : |s|=1)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hD : 0≤D)
    (C : ℕ → ℕ → ℝ) (hC : ∀ i j, 0≤C i j)
    (hdecay : ∀ i j ξ, |ξ|^j*‖iteratedDeriv i g ξ‖≤C i j*D)
    {x : ℝ} (hx : x∈Ioo (-4) 2) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n (g ∘ a03RealLogGapSymbol T r s) (Ioo (-4) 2) x‖≤
      ((n.factorial : ℝ)*(2^n*200^n*phaseFrequencyCompositionBudget C n)*
        (phaseSymbolCompositionBudget a03LogSymbolBudget n)^n)*D := by
  have hexp := a03_log_box_exponential_range ⟨hx.1.le,hx.2.le⟩
  exact phase_frequency_composition_bound
    (a03_log_gap_symbol_contDiffOn (T := T) hr hr1 hs.le) hg isOpen_Ioo.uniqueDiffOn hx C hC
    a03LogSymbolBudget a03LogSymbolBudget_nonneg hD (by nlinarith) (by norm_num)
    (a03_log_gap_symbol_one_add_frequency_lower hT hr hr1 hs hexp.1 hexp.2)
    (fun i j => hdecay i j _) (fun i _ => a03_log_gap_symbol_within_bound hT hr hr1 hs.le hx i) n

theorem a03_six_linear_composition_bound
    {T r s D : ℝ} (hT : 0≤T) (hr : 0≤r) (hr1 : r≤1/100) (hs : |s|=1)
    (g : ℝ → ℂ) (hg : ContDiff ℝ ∞ g) (hD : 0≤D)
    (C : ℕ → ℕ → ℝ) (hC : ∀ i j, 0≤C i j)
    (hdecay : ∀ i j ξ, |ξ|^j*‖iteratedDeriv i g ξ‖≤C i j*D)
    {y : A03SixTensorSpace} (hy : y∈a03SixGapDomain) (n : ℕ) :
    ‖iteratedFDeriv ℝ n ((g ∘ a03RealLogGapSymbol T r s) ∘ a03SixGapLinear) y‖≤
      a03FrequencySixBudget C n*D := by
  have hcomp := a03_log_frequency_composition_contDiffOn (T := T) hr hr1 hs.le g hg
  have hys : a03SixGapLinear y∈Ioo (-4) 2 := hy
  have hcd : ContDiffAt ℝ ∞ ((g ∘ a03RealLogGapSymbol T r s) ∘ a03SixGapLinear) y :=
    ((hcomp.comp_continuousLinearMap a03SixGapLinear) y hy).contDiffAt
      (a03SixGapDomain_isOpen.mem_nhds hy)
  rw [←iteratedFDerivWithin_eq_iteratedFDeriv a03SixGapDomain_isOpen.uniqueDiffOn
    (hcd.of_le (by simp)) hy]
  unfold a03SixGapDomain
  rw [a03SixGapLinear.iteratedFDerivWithin_comp_right hcomp isOpen_Ioo.uniqueDiffOn
    a03SixGapDomain_isOpen.uniqueDiffOn hys (by simp)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDerivWithin ℝ n (g ∘ a03RealLogGapSymbol T r s) (Ioo (-4) 2) (a03SixGapLinear y))
    (fun _ : Fin n => a03SixGapLinear)
  calc
    _ ≤ ‖iteratedFDerivWithin ℝ n (g ∘ a03RealLogGapSymbol T r s) (Ioo (-4) 2)
        (a03SixGapLinear y)‖*∏ _i : Fin n, ‖a03SixGapLinear‖ := hb
    _ ≤ (((n.factorial : ℝ)*(2^n*200^n*phaseFrequencyCompositionBudget C n)*
        (phaseSymbolCompositionBudget a03LogSymbolBudget n)^n)*D)*4^n := by
      apply mul_le_mul
      · exact a03_log_frequency_composition_bound hT hr hr1 hs g hg hD C hC hdecay hys n
      · simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        exact pow_le_pow_left₀ (norm_nonneg _) a03SixGapLinear_norm_le n
      · exact Finset.prod_nonneg (fun _ _ => norm_nonneg _)
      · have hp : 0≤phaseFrequencyCompositionBudget C n := by
          unfold phaseFrequencyCompositionBudget
          exact Finset.sum_nonneg (fun i _ => add_nonneg (hC i 0) (hC i n))
        have hq : 0≤phaseSymbolCompositionBudget a03LogSymbolBudget n := by
          unfold phaseSymbolCompositionBudget
          exact add_nonneg (by norm_num) (Finset.sum_nonneg (fun i _ => a03LogSymbolBudget_nonneg i))
        positivity
    _ = _ := by unfold a03FrequencySixBudget; ring

def a03SixGaussianFrequencyKernel (Φ : ℝ → ℂ) (T : ℝ) (σ α : MomentShifts)
    (z : ℂ) (r s : ℝ) (y : A03SixTensorSpace) : ℂ :=
  a03GaussianFrequencyProfile Φ T σ α z (-a03RealLogGapSymbol T r s (a03SixGapLinear y))

theorem a03_reflected_frequency_derivative_norm (g : ℝ → ℂ) (n : ℕ) (ξ : ℝ) :
    ‖iteratedDeriv n (fun x => g (-x)) ξ‖=‖iteratedDeriv n g (-ξ)‖ := by
  rw [iteratedDeriv_comp_neg]
  simp only [norm_smul,norm_pow,norm_neg,norm_one,one_pow,one_mul]

theorem a03_six_gaussian_frequency_uniform_bounds
    {Φ : ℝ → ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {c ε κ θ A : ℝ} (hc : 0<c) (hc1 : c≤1) (hε : 2*c<ε) (hκ : 0<κ)
    (hθ : 0≤θ) (hA : 0≤A) :
    ∃ E : ℕ → ℝ, (∀ n, 0≤E n) ∧ ∀ᶠ T : ℝ in Filter.atTop,
      ∀ σ α : MomentShifts, (∀ j, ‖α j‖≤A) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v r s : ℝ, |v|≤θ*Real.log T → 0≤r → r≤1/100 → |s|=1 →
      ContDiffOn ℝ ∞ (a03SixGaussianFrequencyKernel Φ T σ α ((c : ℂ)+(v : ℂ)*I) r s)
        a03SixGapDomain ∧ ∀ n : ℕ, ∀ y∈a03SixGapDomain,
      ‖iteratedFDeriv ℝ n (a03SixGaussianFrequencyKernel Φ T σ α ((c : ℂ)+(v : ℂ)*I) r s) y‖≤
        E n*T^ε := by
  obtain ⟨C,hC,hdec⟩ := a03_gaussian_frequency_logarithmic_uniform_derivative_bounds
    hΦ hΦs hc hc1 hε hκ hθ hA
  refine ⟨a03FrequencySixBudget C, a03FrequencySixBudget_nonneg C hC,?_⟩
  filter_upwards [hdec,Filter.eventually_ge_atTop (0 : ℝ)] with T ht hT
  intro σ α hα hroot v r s hv hr hr1 hs
  have hg := (ht σ α hα hroot v hv).1
  have hd := (ht σ α hα hroot v hv).2
  have hgr : ContDiff ℝ ∞ (fun ξ => a03GaussianFrequencyProfile Φ T σ α
      ((c : ℂ)+(v : ℂ)*I) (-ξ)) := hg.comp contDiff_id.neg
  have hdr : ∀ i j ξ, |ξ|^j*‖iteratedDeriv i
      (fun x => a03GaussianFrequencyProfile Φ T σ α ((c : ℂ)+(v : ℂ)*I) (-x)) ξ‖≤C i j*T^ε := by
    intro i j ξ
    rw [a03_reflected_frequency_derivative_norm]
    simpa only [abs_neg] using hd i j (-ξ)
  constructor
  · exact (a03_log_frequency_composition_contDiffOn (T := T) hr hr1 hs.le _ hgr).comp_continuousLinearMap
      a03SixGapLinear
  · intro n y hy
    exact a03_six_linear_composition_bound hT hr hr1 hs _ hgr (Real.rpow_nonneg hT _)
      C hC hdr hy n

end
end Sechstmoment
