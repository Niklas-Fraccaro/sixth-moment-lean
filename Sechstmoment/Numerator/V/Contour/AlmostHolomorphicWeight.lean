import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.RealDeriv
import Sechstmoment.Zeta.Bounds.ZetaPolynomialBound


namespace Sechstmoment.Source
open Complex Real Set
open scoped Topology BigOperators ContDiff
noncomputable section

def almostHolomorphicCoefficient (T u : ℝ) (j : ℕ) : ℂ :=
  (-I*((u : ℂ)-1/2)/(T : ℂ))^j/(j.factorial : ℂ)

def almostHolomorphicWeight (w : ℝ → ℂ) (K : ℕ) (T u t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (K+1), almostHolomorphicCoefficient T u j*iteratedDeriv j w (t/T)

theorem almostHolomorphicWeight_succ (w : ℝ → ℂ) (K : ℕ) (T u t : ℝ) :
    almostHolomorphicWeight w (K+1) T u t = almostHolomorphicWeight w K T u t+
      almostHolomorphicCoefficient T u (K+1)*iteratedDeriv (K+1) w (t/T) := by
  exact Finset.sum_range_succ _ _

theorem almostHolomorphicWeight_left_boundary (w : ℝ → ℂ) (K : ℕ) (T t : ℝ) :
    almostHolomorphicWeight w K T (1/2) t = w (t/T) := by
  simp [almostHolomorphicWeight,almostHolomorphicCoefficient,Finset.sum_range_succ',
    iteratedDeriv_zero]

theorem almostHolomorphicCoefficient_hasDerivAt (T u : ℝ) (j : ℕ) :
    HasDerivAt (fun v => almostHolomorphicCoefficient T v (j+1))
      ((-I/(T : ℂ))*almostHolomorphicCoefficient T u j) u := by
  have hbase : HasDerivAt (fun v : ℝ => -I*((v : ℂ)-1/2)/(T : ℂ))
      (-I/(T : ℂ)) u := by
    simpa only [id_eq,mul_one] using
      ((((hasDerivAt_id (u : ℂ)).comp_ofReal.sub_const (1/2)).const_mul (-I)).div_const (T : ℂ))
  have h := (hbase.pow (j+1)).div_const ((j+1).factorial : ℂ)
  have he : ((j+1 : ℕ) : ℂ)*(-I*((u : ℂ)-1/2)/(T : ℂ))^(j+1-1)*(-I/(T : ℂ))/
      ((j+1).factorial : ℂ) = (-I/(T : ℂ))*almostHolomorphicCoefficient T u j := by
    dsimp only [almostHolomorphicCoefficient]
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    simp only [Nat.add_sub_cancel]
    have hj : (j : ℂ)+1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    have hf : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
    field_simp
  rw [he] at h
  exact h

theorem almostHolomorphicWeight_hasDerivAt_real (w : ℝ → ℂ) (K : ℕ) (T u t : ℝ) :
    HasDerivAt (fun v => almostHolomorphicWeight w K T v t)
      ((-I/(T : ℂ))*
        ∑ j ∈ Finset.range K, almostHolomorphicCoefficient T u j*iteratedDeriv (j+1) w (t/T)) u := by
  induction K with
  | zero =>
    simpa [almostHolomorphicWeight,almostHolomorphicCoefficient] using
      (hasDerivAt_const u (w (t/T)))
  | succ K ih =>
    have h := ih.add ((almostHolomorphicCoefficient_hasDerivAt T u K).mul_const
      (iteratedDeriv (K+1) w (t/T)))
    convert h using 1
    · ext v
      exact almostHolomorphicWeight_succ w K T v t
    · rw [Finset.sum_range_succ,mul_add]
      ring

theorem almostHolomorphicWeight_hasDerivAt_imag {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (K : ℕ) (T u t : ℝ) :
    HasDerivAt (fun v => almostHolomorphicWeight w K T u v)
      ((1/(T : ℂ))*
        ∑ j ∈ Finset.range (K+1), almostHolomorphicCoefficient T u j*iteratedDeriv (j+1) w (t/T)) t := by
  have h (j : ℕ) : HasDerivAt (fun v : ℝ => iteratedDeriv j w (v/T))
      ((1/(T : ℂ))*iteratedDeriv (j+1) w (t/T)) t := by
    have hd := (hw.differentiable_iteratedDeriv j
      (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)) (t/T)).hasDerivAt
    rw [← iteratedDeriv_succ] at hd
    simpa only [Function.comp_def,id_eq,one_div,Complex.real_smul,Complex.ofReal_inv] using
      hd.scomp t ((hasDerivAt_id t).div_const T)
  have hs := HasDerivAt.fun_sum (u := Finset.range (K+1))
    (fun j _ => (h j).const_mul (almostHolomorphicCoefficient T u j))
  convert hs using 1
  · rfl
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring

theorem almostHolomorphicWeight_cauchyRiemann_defect {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (K : ℕ) (T u t : ℝ) :
    deriv (fun v => almostHolomorphicWeight w K T v t) u+
      I*deriv (fun v => almostHolomorphicWeight w K T u v) t =
      (I/(T : ℂ))*almostHolomorphicCoefficient T u K*iteratedDeriv (K+1) w (t/T) := by
  rw [(almostHolomorphicWeight_hasDerivAt_real w K T u t).deriv,
    (almostHolomorphicWeight_hasDerivAt_imag hw K T u t).deriv,Finset.sum_range_succ]
  ring

theorem iteratedDeriv_tsupport_subset (w : ℝ → ℂ) (j : ℕ) :
    tsupport (iteratedDeriv j w) ⊆ tsupport w := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]; exact Subset.rfl
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem almostHolomorphicWeight_eq_zero_of_notMem_tsupport (w : ℝ → ℂ)
    (K : ℕ) (T u t : ℝ) (ht : t/T ∉ tsupport w) :
    almostHolomorphicWeight w K T u t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  have hz : iteratedDeriv j w (t/T) = 0 := by
    by_contra h
    exact ht (iteratedDeriv_tsupport_subset w j (subset_tsupport _ (Function.mem_support.mpr h)))
  rw [hz,mul_zero]

theorem almostHolomorphicWeight_eq_zero_outside_dyadic {w : ℝ → ℂ}
    (hw : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) {T : ℝ} (hT : 0 < T)
    (u t : ℝ) (ht : t ∉ Icc T (2*T)) : almostHolomorphicWeight w K T u t = 0 := by
  apply almostHolomorphicWeight_eq_zero_of_notMem_tsupport
  intro h
  have hs := hw h
  exact ht ⟨by simpa using (le_div_iff₀ hT).mp hs.1,(div_le_iff₀ hT).mp hs.2⟩

theorem almostHolomorphicCoefficient_norm (T u : ℝ) (j : ℕ) :
    ‖almostHolomorphicCoefficient T u j‖ = (|u-1/2|/|T|)^j/(j.factorial : ℝ) := by
  have hr : ‖(u : ℂ)-1/2‖ = |u-1/2| := by
    rw [show (u : ℂ)-1/2 = ((u-1/2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real,Real.norm_eq_abs]
  simp only [almostHolomorphicCoefficient,norm_div,norm_pow,norm_mul,norm_neg,norm_I,
    one_mul,Complex.norm_natCast,Complex.norm_real,Real.norm_eq_abs,hr]

theorem almostHolomorphicWeight_defect_norm {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (K : ℕ) {T : ℝ} (hT : 0 < T) (u t : ℝ) :
    ‖deriv (fun v => almostHolomorphicWeight w K T v t) u+
      I*deriv (fun v => almostHolomorphicWeight w K T u v) t‖ =
      (|u-1/2|^K/((K.factorial : ℝ)*T^(K+1)))*‖iteratedDeriv (K+1) w (t/T)‖ := by
  rw [almostHolomorphicWeight_cauchyRiemann_defect hw,norm_mul,norm_mul,norm_div,norm_I,
    Complex.norm_real,Real.norm_of_nonneg hT.le,almostHolomorphicCoefficient_norm,abs_of_pos hT,
    div_pow,pow_succ]
  have hf : (K.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero K
  field_simp

theorem smooth_compact_weight_derivative_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, ‖iteratedDeriv j w x‖ ≤ C := by
  have hc : HasCompactSupport (iteratedDeriv j w) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      ((iteratedDeriv_tsupport_subset w j).trans hws)
  obtain ⟨C,hC⟩ := hc.exists_bound_of_continuous
    (hw.continuous_iteratedDeriv j (WithTop.coe_le_coe.mpr le_top))
  refine ⟨max 1 C,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x
  exact (hC x).trans (le_max_right _ _)

theorem smooth_compact_weight_jet_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, j ≤ K → ∀ x : ℝ, ‖iteratedDeriv j w x‖ ≤ C := by
  induction K with
  | zero =>
    obtain ⟨C,hC,hb⟩ := smooth_compact_weight_derivative_bound hw hws 0
    refine ⟨C,hC,?_⟩
    intro j hj x
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    exact hb x
  | succ K ih =>
    obtain ⟨C,hC,hb⟩ := ih
    obtain ⟨D,hD,hd⟩ := smooth_compact_weight_derivative_bound hw hws (K+1)
    refine ⟨max C D,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
    intro j hj x
    by_cases hj' : j ≤ K
    · exact (hb j hj' x).trans (le_max_left _ _)
    · have he : j = K+1 := by omega
      subst j
      exact (hd x).trans (le_max_right _ _)

theorem almostHolomorphicWeight_defect_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → ∀ u t : ℝ, |u-1/2| ≤ 1 →
      ‖deriv (fun v => almostHolomorphicWeight w K T v t) u+
        I*deriv (fun v => almostHolomorphicWeight w K T u v) t‖ ≤ C/T^(K+1) := by
  obtain ⟨D,hD,hbound⟩ := smooth_compact_weight_derivative_bound hw hws (K+1)
  refine ⟨D,hD,?_⟩
  intro T hT u t hu
  rw [almostHolomorphicWeight_defect_norm hw K hT]
  have hpow : |u-1/2|^K ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
  have hfact : (1 : ℝ) ≤ K.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero K)
  have hratio : |u-1/2|^K/((K.factorial : ℝ)*T^(K+1)) ≤ 1/T^(K+1) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [pow_pos hT (K+1)]
  calc
    _ ≤ (1/T^(K+1))*D := mul_le_mul hratio (hbound (t/T)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem almostHolomorphicCoefficient_le_inverse_scale {T u : ℝ} (hT : 1 ≤ T)
    (hu : |u-1/2| ≤ 1) {j : ℕ} (hj : 1 ≤ j) :
    ‖almostHolomorphicCoefficient T u j‖ ≤ 1/T := by
  have hTpos : 0 < T := by linarith
  have hfact : (1 : ℝ) ≤ j.factorial := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
  have hnum : |u-1/2|^j ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
  have hden : T ≤ T^j := by simpa using pow_le_pow_right₀ hT hj
  rw [almostHolomorphicCoefficient_norm,abs_of_pos hTpos,div_pow,div_div]
  apply (div_le_div_iff₀ (by positivity) hTpos).mpr
  calc
    _ ≤ 1*T := mul_le_mul_of_nonneg_right hnum hTpos.le
    _ ≤ T^j := by simpa using hden
    _ ≤ _ := by simpa using le_mul_of_one_le_right (pow_nonneg hTpos.le j) hfact

theorem almostHolomorphicWeight_sub_original (w : ℝ → ℂ) (K : ℕ) (T u t : ℝ) :
    almostHolomorphicWeight w K T u t-w (t/T) =
      ∑ j ∈ Finset.range K, almostHolomorphicCoefficient T u (j+1)*iteratedDeriv (j+1) w (t/T) := by
  simp only [almostHolomorphicWeight,Finset.sum_range_succ',almostHolomorphicCoefficient,
    pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,iteratedDeriv_zero,one_mul,add_sub_cancel_right]

theorem almostHolomorphicWeight_sub_original_bound {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 1 ≤ T → ∀ u t : ℝ, |u-1/2| ≤ 1 →
      ‖almostHolomorphicWeight w K T u t-w (t/T)‖ ≤ C/T := by
  obtain ⟨D,hD,hjets⟩ := smooth_compact_weight_jet_bound hw hws K
  refine ⟨((K : ℝ)+1)*D,by positivity,?_⟩
  intro T hT u t hu
  have hTpos : 0 < T := by linarith
  rw [almostHolomorphicWeight_sub_original]
  calc
    _ ≤ ∑ j ∈ Finset.range K,
        ‖almostHolomorphicCoefficient T u (j+1)*iteratedDeriv (j+1) w (t/T)‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range K, (1/T)*D := by
      apply Finset.sum_le_sum
      intro j hj
      rw [norm_mul]
      exact mul_le_mul (almostHolomorphicCoefficient_le_inverse_scale hT hu (by omega))
        (hjets (j+1) (by simp only [Finset.mem_range] at hj; omega) (t/T))
        (norm_nonneg _) (by positivity)
    _ = (K : ℝ)*((1/T)*D) := by simp
    _ ≤ _ := by
      have hpos : 0 ≤ D/T := by positivity
      calc
        _ = (K : ℝ)*(D/T) := by ring
        _ ≤ ((K : ℝ)+1)*(D/T) := by nlinarith
        _ = _ := by ring

end
end Sechstmoment.Source
