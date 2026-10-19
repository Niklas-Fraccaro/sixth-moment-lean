import Mathlib.Analysis.Normed.Group.Bounded
import Sechstmoment.Denominator.Balanced.GaussianSharpTilt

/-! The original D01 arithmetic diagonal with three row profiles and one
column profile. The three compact row profiles bound the entire diagonal;
no product-length cutoff or dual Gaussian half is needed. -/
namespace Sechstmoment
open MeasureTheory Filter Set
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def d04OneSidedProfileProduct (ρ : Fin 4 → ℝ → ℂ) (y : D01LogSpace) : ℂ :=
  ρ 0 (y.1 0)*ρ 1 (y.1 1)*ρ 2 (y.1 2)*ρ 3 (y.2 2)

def d04OneSidedShiftWeight (σ : Fin 2 → ℂ) (y : D01LogSpace) : ℂ :=
  Complex.exp (σ 0*((y.2 0 : ℂ)-1/2)+σ 1*(1/2-(y.2 1 : ℂ)))

@[fun_prop] theorem d04OneSidedProfileProduct_continuous
    (ρ : Fin 4 → ℝ → ℂ) (hρ : ∀ i, Continuous (ρ i)) :
    Continuous (d04OneSidedProfileProduct ρ) := by
  unfold d04OneSidedProfileProduct
  fun_prop

@[fun_prop] theorem d04OneSidedShiftWeight_continuous (σ : Fin 2 → ℂ) :
    Continuous (d04OneSidedShiftWeight σ) := by
  unfold d04OneSidedShiftWeight
  fun_prop

theorem d04LogPoint_equal_totals (L : ℝ) (x : DiagonalSixIndices) :
    (∑ i, (d01LogPoint L x).1 i) = ∑ j, (d01LogPoint L x).2 j := by
  have hl (i : Fin 3) : (d01LeftIndices x i : ℝ) ≠ 0 := by
    exact_mod_cast (d01LeftIndices_pos x i).ne'
  have hr (i : Fin 3) : (d01RightIndices x i : ℝ) ≠ 0 := by
    exact_mod_cast (d01RightIndices_pos x i).ne'
  have hp : (d01LeftIndices x 0 : ℝ)*
      ((d01LeftIndices x 1 : ℝ)*(d01LeftIndices x 2 : ℝ)) =
      (d01RightIndices x 0 : ℝ)*
        ((d01RightIndices x 1 : ℝ)*(d01RightIndices x 2 : ℝ)) := by
    exact_mod_cast x.property.1
  have hlog := congrArg Real.log hp
  rw [Real.log_mul (hl 0) (mul_ne_zero (hl 1) (hl 2)),
    Real.log_mul (hl 1) (hl 2),
    Real.log_mul (hr 0) (mul_ne_zero (hr 1) (hr 2)),
    Real.log_mul (hr 1) (hr 2)] at hlog
  simp only [d01LogPoint, Fin.sum_univ_three]
  calc
    _ = (Real.log (d01LeftIndices x 0 : ℝ)+
      (Real.log (d01LeftIndices x 1 : ℝ)+Real.log (d01LeftIndices x 2 : ℝ)))/L := by ring
    _ = _ := by rw [hlog]; ring

theorem d04DiagonalMeasure_ae_equal_totals (L : ℝ) :
    ∀ᵐ y ∂d01DiagonalMeasure L, (∑ i, y.1 i) = ∑ j, y.2 j := by
  rw [d01DiagonalMeasure, Measure.ae_sum_iff]
  intro x
  apply Measure.ae_smul_measure
  exact (ae_dirac_iff
    (isClosed_eq (by fun_prop) (by fun_prop)).measurableSet).mpr
      (d04LogPoint_equal_totals L x)

theorem d04OneSidedProfileProduct_row_total_lt_one
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρcap : ∀ k t, ρ k t ≠ 0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k, a k)<1)
    {y : D01LogSpace} (hy : d04OneSidedProfileProduct ρ y ≠ 0) :
    (∑ i, y.1 i)<1 := by
  have h0 : ρ 0 (y.1 0) ≠ 0 := by
    intro h; exact hy (by simp [d04OneSidedProfileProduct,h])
  have h1 : ρ 1 (y.1 1) ≠ 0 := by
    intro h; exact hy (by simp [d04OneSidedProfileProduct,h])
  have h2 : ρ 2 (y.1 2) ≠ 0 := by
    intro h; exact hy (by simp [d04OneSidedProfileProduct,h])
  have hc0 := (hρcap 0 _ h0).2
  have hc1 := (hρcap 1 _ h1).2
  have hc2 := (hρcap 2 _ h2).2
  simp only [Fin.sum_univ_four] at ha
  simp only [Fin.sum_univ_three]
  linarith

theorem d04OneSidedProfileProduct_column_bounds
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρcap : ∀ k t, ρ k t ≠ 0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k, a k)<1)
    {y : D01LogSpace} (hy : y∈d01PositiveOrthant)
    (hbalance : (∑ i, y.1 i) = ∑ j, y.2 j)
    (hn : d04OneSidedProfileProduct ρ y ≠ 0) :
    (∀ j, y.2 j∈Icc (0:ℝ) 1) ∧ y.2 0+y.2 1≤1 ∧ d01LogTotal y≤2 := by
  have ht := d04OneSidedProfileProduct_row_total_lt_one ρ a hρcap ha3 ha hn
  have ht' : (∑ j, y.2 j)<1 := by rw [← hbalance]; exact ht
  simp only [Fin.sum_univ_three] at ht ht' hbalance
  have h0 := hy.2 0; have h1 := hy.2 1; have h2 := hy.2 2
  refine ⟨?_,?_,?_⟩
  · intro j
    fin_cases j
    · change y.2 0∈Icc (0:ℝ) 1
      exact ⟨h0,by linarith⟩
    · change y.2 1∈Icc (0:ℝ) 1
      exact ⟨h1,by linarith⟩
    · change y.2 2∈Icc (0:ℝ) 1
      exact ⟨h2,by linarith⟩
  · linarith
  · simp only [d01LogTotal,Fin.sum_univ_three]
    linarith

private def d04ColumnLocalization (t : ℝ) : ℝ :=
  max 0 (min 1 (t+1))*max 0 (min 1 (2-t))

private theorem d04ColumnLocalization_continuous : Continuous d04ColumnLocalization := by
  unfold d04ColumnLocalization
  fun_prop

private theorem d04ColumnLocalization_eq_one {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    d04ColumnLocalization t=1 := by
  have h1 : (1:ℝ)≤t+1 := by linarith [ht.1]
  have h2 : (1:ℝ)≤2-t := by linarith [ht.2]
  simp [d04ColumnLocalization,min_eq_left h1,min_eq_left h2]

private theorem d04ColumnLocalization_support {t : ℝ}
    (ht : d04ColumnLocalization t≠0) : t∈Icc (-1:ℝ) 2 := by
  constructor
  · by_contra h
    have hz : min (1:ℝ) (t+1)≤0 := (min_le_right _ _).trans (by linarith)
    exact ht (by simp [d04ColumnLocalization,max_eq_left hz])
  · by_contra h
    have hz : min (1:ℝ) (2-t)≤0 := (min_le_right _ _).trans (by linarith)
    exact ht (by simp [d04ColumnLocalization,max_eq_left hz])

def d04LocalizedOneSidedProfile (ρ : Fin 4 → ℝ → ℂ) (y : D01LogSpace) : ℂ :=
  (d04ColumnLocalization (y.2 0) : ℂ)*
    (d04ColumnLocalization (y.2 1) : ℂ)*d04OneSidedProfileProduct ρ y

theorem d04LocalizedOneSidedProfile_continuous
    (ρ : Fin 4 → ℝ → ℂ) (hρ : ∀ i, Continuous (ρ i)) :
    Continuous (d04LocalizedOneSidedProfile ρ) := by
  have h0 : Continuous (fun y : D01LogSpace => d04ColumnLocalization (y.2 0)) :=
    d04ColumnLocalization_continuous.comp ((continuous_apply 0).comp continuous_snd)
  have h1 : Continuous (fun y : D01LogSpace => d04ColumnLocalization (y.2 1)) :=
    d04ColumnLocalization_continuous.comp ((continuous_apply 1).comp continuous_snd)
  exact ((Complex.continuous_ofReal.comp h0).mul
    (Complex.continuous_ofReal.comp h1)).mul (d04OneSidedProfileProduct_continuous ρ hρ)

theorem d04LocalizedOneSidedProfile_compact_support
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρcap : ∀ k t, ρ k t≠0 → t∈Icc 0 (a k)) :
    HasCompactSupport (d04LocalizedOneSidedProfile ρ) := by
  let lo : D01LogSpace := (![0,0,0],![-1,-1,0])
  let hi : D01LogSpace := (![a 0,a 1,a 2],![2,2,a 3])
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=lo) (b:=hi))
  intro y hy
  change d04LocalizedOneSidedProfile ρ y≠0 at hy
  have h0 : ρ 0 (y.1 0)≠0 := by
    intro h; exact hy (by simp [d04LocalizedOneSidedProfile,d04OneSidedProfileProduct,h])
  have h1 : ρ 1 (y.1 1)≠0 := by
    intro h; exact hy (by simp [d04LocalizedOneSidedProfile,d04OneSidedProfileProduct,h])
  have h2 : ρ 2 (y.1 2)≠0 := by
    intro h; exact hy (by simp [d04LocalizedOneSidedProfile,d04OneSidedProfileProduct,h])
  have h3 : ρ 3 (y.2 2)≠0 := by
    intro h; exact hy (by simp [d04LocalizedOneSidedProfile,d04OneSidedProfileProduct,h])
  have hc0 : d04ColumnLocalization (y.2 0)≠0 := by
    intro h; exact hy (by simp [d04LocalizedOneSidedProfile,h])
  have hc1 : d04ColumnLocalization (y.2 1)≠0 := by
    intro h; exact hy (by simp [d04LocalizedOneSidedProfile,h])
  have hp0 := hρcap 0 _ h0; have hp1 := hρcap 1 _ h1
  have hp2 := hρcap 2 _ h2; have hp3 := hρcap 3 _ h3
  have hz0 := d04ColumnLocalization_support hc0
  have hz1 := d04ColumnLocalization_support hc1
  refine ⟨⟨?_,?_⟩,⟨?_,?_⟩⟩
  · intro i; fin_cases i <;> simp [lo] <;> linarith [hp0.1,hp1.1,hp2.1]
  · intro i; fin_cases i <;> simp [lo] <;> linarith [hz0.1,hz1.1,hp3.1]
  · intro i; fin_cases i <;> simp [hi] <;> linarith [hp0.2,hp1.2,hp2.2]
  · intro i; fin_cases i <;> simp [hi] <;> linarith [hz0.2,hz1.2,hp3.2]

theorem d04LocalizedOneSidedProfile_eq
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρcap : ∀ k t, ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k, a k)<1)
    {y : D01LogSpace} (hy : y∈d01PositiveOrthant)
    (hbalance : (∑ i,y.1 i)=∑ j,y.2 j) :
    d04LocalizedOneSidedProfile ρ y=d04OneSidedProfileProduct ρ y := by
  by_cases hn : d04OneSidedProfileProduct ρ y=0
  · simp [d04LocalizedOneSidedProfile,hn]
  have hb := d04OneSidedProfileProduct_column_bounds ρ a hρcap ha3 ha hy hbalance hn
  simp [d04LocalizedOneSidedProfile,d04ColumnLocalization_eq_one (hb.1 0),
    d04ColumnLocalization_eq_one (hb.1 1)]

/-- Actual arithmetic D01 convergence for the unbalanced four profiles. -/
theorem d04DiagonalMeasure_one_sided_profile_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (w : D01LogSpace → ℂ)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) (hw : Continuous w) :
    Tendsto (fun L : ℝ => ∫ y,w y*d04OneSidedProfileProduct ρ y
      ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ)*∫ x : D01EdgeSpace,
        w (d01RowColumnSums x)*d04OneSidedProfileProduct ρ (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant)) := by
  have hfc := d04LocalizedOneSidedProfile_continuous ρ hρc
  have hK := d04LocalizedOneSidedProfile_compact_support ρ a hρcap
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuous hfc
  have hlim := d01DiagonalMeasure_complex_weighted_limit
    (d04LocalizedOneSidedProfile ρ) w hfc.measurable
    (ae_of_all _ (fun _ => hfc.continuousAt)) hK hC hw
  have hright : (∫ x : D01EdgeSpace,
      w (d01RowColumnSums x)*d04LocalizedOneSidedProfile ρ (d01RowColumnSums x)
        ∂volume.restrict d01NonnegativeOrthant) =
      ∫ x : D01EdgeSpace,
        w (d01RowColumnSums x)*d04OneSidedProfileProduct ρ (d01RowColumnSums x)
          ∂volume.restrict d01NonnegativeOrthant := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem d01NonnegativeOrthant_measurable] with x hx
    rw [d04LocalizedOneSidedProfile_eq ρ a hρcap ha3 ha
      (d01RowColumnSums_nonnegative hx) (d01RowColumnSums_total x)]
  rw [hright] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with L hL
  apply integral_congr_ae
  filter_upwards [d01DiagonalMeasure_ae_orthant hL,
    d04DiagonalMeasure_ae_equal_totals L] with y hy hb
  rw [d04LocalizedOneSidedProfile_eq ρ a hρcap ha3 ha hy hb]

theorem d04DiagonalMeasure_one_sided_shifted_height_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ k, Continuous (ρ k))
    (hρcap : ∀ k t, ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) :
    Tendsto (fun T : ℝ => ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
      ∂d01DiagonalMeasure (Real.log T)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*∫ x : D01EdgeSpace,
        d04OneSidedShiftWeight σ (d01RowColumnSums x)*
          d04OneSidedProfileProduct ρ (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  (d04DiagonalMeasure_one_sided_profile_limit ρ a (d04OneSidedShiftWeight σ)
    hρc hρcap ha3 ha (d04OneSidedShiftWeight_continuous σ)).comp Real.tendsto_log_atTop

theorem d04TiltedDiagonalMeasure_ae_equal_totals {L : ℝ} (hL : 0<L) :
    ∀ᵐ y ∂d02TiltedDiagonalMeasure L, (∑ i,y.1 i)=∑ j,y.2 j := by
  unfold d02TiltedDiagonalMeasure
  rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL]
  exact (d04DiagonalMeasure_ae_equal_totals L).filter_mono
    (withDensity_absolutelyContinuous (d01DiagonalMeasure L)
      (fun y => ENNReal.ofReal (Real.exp (-d01LogTotal y)))).ae_le

theorem d04OneSidedProfileProduct_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (b : Fin 4 → ℝ)
    (hb0 : ∀ k,0≤b k) (hb : ∀ k t,‖ρ k t‖≤b k) (y : D01LogSpace) :
    ‖d04OneSidedProfileProduct ρ y‖≤b 0*b 1*b 2*b 3 := by
  simp only [d04OneSidedProfileProduct,norm_mul]
  have h01 := mul_le_mul (hb 0 (y.1 0)) (hb 1 (y.1 1)) (norm_nonneg _) (hb0 0)
  have h012 := mul_le_mul h01 (hb 2 (y.1 2)) (norm_nonneg _)
    (mul_nonneg (hb0 0) (hb0 1))
  exact mul_le_mul h012 (hb 3 (y.2 2)) (norm_nonneg _)
    (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2))

theorem d04OneSidedShiftWeight_norm_bound (σ : Fin 2 → ℂ) {R : ℝ} (hR : 0≤R)
    (hσ : ∀ i,‖σ i‖≤R) {y : D01LogSpace}
    (hy0 : y.2 0∈Icc (0:ℝ) 1) (hy1 : y.2 1∈Icc (0:ℝ) 1) :
    ‖d04OneSidedShiftWeight σ y‖≤Real.exp (2*R) := by
  have hz : |(σ 0).re|≤R := (Complex.abs_re_le_norm _).trans (hσ 0)
  have hw : |(σ 1).re|≤R := (Complex.abs_re_le_norm _).trans (hσ 1)
  have ht0 : |y.2 0-1/2|≤1 := abs_le.mpr ⟨by linarith [hy0.1],by linarith [hy0.2]⟩
  have ht1 : |1/2-y.2 1|≤1 := abs_le.mpr ⟨by linarith [hy1.2],by linarith [hy1.1]⟩
  have he0 : (σ 0).re*(y.2 0-1/2)≤R := by
    calc
      _ ≤ |(σ 0).re*(y.2 0-1/2)| := le_abs_self _
      _ = |(σ 0).re| *|y.2 0-1/2| := abs_mul _ _
      _ ≤ R*1 := mul_le_mul hz ht0 (abs_nonneg _) hR
      _ = R := mul_one _
  have he1 : (σ 1).re*(1/2-y.2 1)≤R := by
    calc
      _ ≤ |(σ 1).re*(1/2-y.2 1)| := le_abs_self _
      _ = |(σ 1).re| *|1/2-y.2 1| := abs_mul _ _
      _ ≤ R*1 := mul_le_mul hw ht1 (abs_nonneg _) hR
      _ = R := mul_one _
  rw [d04OneSidedShiftWeight,Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simp only [Complex.add_re,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,
    Complex.div_re]
  norm_num
  linarith

def d04OneSidedDiagonalBound (b : Fin 4 → ℝ) (R : ℝ) : ℝ :=
  b 0*b 1*b 2*b 3*Real.exp (2*R+2)

theorem d04OneSidedDiagonalBound_nonneg (b : Fin 4 → ℝ) (R : ℝ)
    (hb0 : ∀ k,0≤b k) : 0≤d04OneSidedDiagonalBound b R := by
  unfold d04OneSidedDiagonalBound
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2))
    (hb0 3)) (Real.exp_pos _).le

theorem d04OneSidedDiagonal_untilted_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ)
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1)
    (hb0 : ∀ k,0≤b k) (hb : ∀ k t,‖ρ k t‖≤b k)
    (σ : Fin 2 → ℂ) {R : ℝ} (hR : 0≤R) (hσ : ∀ i,‖σ i‖≤R)
    {y : D01LogSpace} (hy : y∈d01PositiveOrthant)
    (hbalance : (∑ i,y.1 i)=∑ j,y.2 j) :
    ‖(Real.exp (d01LogTotal y) : ℂ)*
      (d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y)‖≤
        d04OneSidedDiagonalBound b R := by
  by_cases hn : d04OneSidedProfileProduct ρ y=0
  · simp only [hn,mul_zero,norm_zero]
    exact d04OneSidedDiagonalBound_nonneg b R hb0
  have hbox := d04OneSidedProfileProduct_column_bounds ρ a hρcap ha3 ha hy hbalance hn
  have hW := d04OneSidedShiftWeight_norm_bound σ hR hσ (hbox.1 0) (hbox.1 1)
  have hP := d04OneSidedProfileProduct_norm_bound ρ b hb0 hb y
  have hprod0 : 0≤b 0*b 1*b 2*b 3 :=
    mul_nonneg (mul_nonneg (mul_nonneg (hb0 0) (hb0 1)) (hb0 2)) (hb0 3)
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (Real.exp_pos _).le,norm_mul]
  calc
    _ ≤ Real.exp 2*(Real.exp (2*R)*(b 0*b 1*b 2*b 3)) :=
      mul_le_mul (Real.exp_le_exp.mpr hbox.2.2)
        (mul_le_mul hW hP (norm_nonneg _) (Real.exp_pos _).le)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
    _ = _ := by unfold d04OneSidedDiagonalBound; rw [Real.exp_add]; ring

def d04OneSidedLogSmoothing (L : ℝ) (y : D01LogSpace) : ℝ :=
  Real.exp (-Real.exp (L*(y.2 0+y.2 1)-3*L))

@[fun_prop] theorem d04OneSidedLogSmoothing_continuous (L : ℝ) :
    Continuous (d04OneSidedLogSmoothing L) := by
  unfold d04OneSidedLogSmoothing
  fun_prop

theorem d04OneSidedLogSmoothing_nonneg (L : ℝ) (y : D01LogSpace) :
    0≤d04OneSidedLogSmoothing L y := (Real.exp_pos _).le

theorem d04OneSidedLogSmoothing_le_one (L : ℝ) (y : D01LogSpace) :
    d04OneSidedLogSmoothing L y≤1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)

theorem d04OneSidedLogSmoothing_sub_one_bound {L : ℝ} (hL : 0≤L)
    {y : D01LogSpace} (hy : y.2 0+y.2 1≤1) :
    |d04OneSidedLogSmoothing L y-1|≤Real.exp (-2*L) := by
  have hs := d04OneSidedLogSmoothing_le_one L y
  rw [abs_of_nonpos (by linarith : d04OneSidedLogSmoothing L y-1≤0)]
  have he := Real.one_sub_le_exp_neg (Real.exp (L*(y.2 0+y.2 1)-3*L))
  have hd : Real.exp (L*(y.2 0+y.2 1)-3*L)≤Real.exp (-2*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  unfold d04OneSidedLogSmoothing at *
  linarith

theorem d04OneSidedDiagonal_smoothing_difference_bound
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1)
    (hb0 : ∀ k,0≤b k) (hb : ∀ k t,‖ρ k t‖≤b k)
    (σ : Fin 2 → ℂ) {R L : ℝ} (hR : 0≤R) (hσ : ∀ i,‖σ i‖≤R) (hL : 0<L) :
    ‖(∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
        (d04OneSidedLogSmoothing L y : ℂ) ∂d01DiagonalMeasure L)-
      ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
        ∂d01DiagonalMeasure L‖≤
      d04OneSidedDiagonalBound b R*Real.exp (-2*L)*
        (∫ _y : D01LogSpace,(1:ℝ) ∂d02TiltedDiagonalMeasure L) := by
  let f := fun y : D01LogSpace => d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
  let g := fun y : D01LogSpace => (Real.exp (d01LogTotal y) : ℂ)*f y
  let s := fun y : D01LogSpace => (d04OneSidedLogSmoothing L y : ℂ)
  let K := d04OneSidedDiagonalBound b R
  have hK : 0≤K := d04OneSidedDiagonalBound_nonneg b R hb0
  have hgm : Measurable g := by
    dsimp [g,f]
    fun_prop
  have hsm : Measurable s := Complex.measurable_ofReal.comp
    (d04OneSidedLogSmoothing_continuous L).measurable
  have hgB : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,‖g y‖≤K := by
    filter_upwards [d02TiltedDiagonalMeasure_ae_orthant hL,
      d04TiltedDiagonalMeasure_ae_equal_totals hL] with y hy heq
    exact d04OneSidedDiagonal_untilted_norm_bound ρ a b hρcap ha3 ha hb0 hb
      σ hR hσ hy heq
  have hgi : Integrable g (d02TiltedDiagonalMeasure L) :=
    (integrable_const K).mono' hgm.aestronglyMeasurable hgB
  have hgsB : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,‖g y*s y‖≤K := by
    filter_upwards [hgB] with y hy
    rw [norm_mul]
    have hs : ‖s y‖≤1 := by
      dsimp [s]
      rw [Complex.norm_real,Real.norm_of_nonneg (d04OneSidedLogSmoothing_nonneg L y)]
      exact d04OneSidedLogSmoothing_le_one L y
    exact (mul_le_of_le_one_right (norm_nonneg _) hs).trans hy
  have hgsi : Integrable (fun y => g y*s y) (d02TiltedDiagonalMeasure L) :=
    (integrable_const K).mono' (hgm.mul hsm).aestronglyMeasurable hgsB
  have he1 : (∫ y,g y*s y ∂d02TiltedDiagonalMeasure L)=
      ∫ y,f y*s y ∂d01DiagonalMeasure L := by
    unfold d02TiltedDiagonalMeasure
    rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL]
    have hgseq : (fun y => g y*s y)=fun y =>
        (Real.exp (d01LogTotal y) : ℂ)*(f y*s y) := by
      funext y; dsimp [g]; ring
    rw [hgseq]
    exact d01_integral_remove_exponential_tilt _ _ d01LogTotal_continuous.measurable _
  have he2 : (∫ y,g y ∂d02TiltedDiagonalMeasure L)=∫ y,f y ∂d01DiagonalMeasure L := by
    unfold d02TiltedDiagonalMeasure
    rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL]
    exact d01_integral_remove_exponential_tilt _ _ d01LogTotal_continuous.measurable _
  change ‖(∫ y,f y*s y ∂d01DiagonalMeasure L)-∫ y,f y ∂d01DiagonalMeasure L‖≤_
  rw [← he1,← he2,← integral_sub hgsi hgi]
  have herr : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,
      ‖g y*s y-g y‖≤K*Real.exp (-2*L) := by
    filter_upwards [hgB,d02TiltedDiagonalMeasure_ae_orthant hL,
      d04TiltedDiagonalMeasure_ae_equal_totals hL] with y hgy hy heq
    by_cases hn : d04OneSidedProfileProduct ρ y=0
    · have hgzero : g y=0 := by simp [g,f,hn]
      rw [hgzero,zero_mul,sub_self,norm_zero]
      exact mul_nonneg hK (Real.exp_pos _).le
    have hbnd := d04OneSidedProfileProduct_column_bounds ρ a hρcap ha3 ha hy heq hn
    rw [show g y*s y-g y=g y*(s y-1) by ring,norm_mul]
    have hs : ‖s y-1‖≤Real.exp (-2*L) := by
      dsimp [s]
      rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      exact d04OneSidedLogSmoothing_sub_one_bound hL.le hbnd.2.1
    exact mul_le_mul hgy hs (norm_nonneg _) hK
  calc
    _ ≤ ∫ _y : D01LogSpace,K*Real.exp (-2*L) ∂d02TiltedDiagonalMeasure L :=
      norm_integral_le_of_norm_le (integrable_const _) herr
    _ = _ := by
      simpa [K] using (integral_const_mul (μ:=d02TiltedDiagonalMeasure L)
        (K*Real.exp (-2*L)) (fun _y : D01LogSpace => (1:ℝ)))

theorem d04OneSidedDiagonal_norm_bound
    (ρ : Fin 4 → ℝ → ℂ) (a b : Fin 4 → ℝ)
    (_hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1)
    (hb0 : ∀ k,0≤b k) (hb : ∀ k t,‖ρ k t‖≤b k)
    (σ : Fin 2 → ℂ) {R L : ℝ} (hR : 0≤R) (hσ : ∀ i,‖σ i‖≤R) (hL : 0<L) :
    ‖∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
      ∂d01DiagonalMeasure L‖≤d04OneSidedDiagonalBound b R*
        (∫ _y : D01LogSpace,(1:ℝ) ∂d02TiltedDiagonalMeasure L) := by
  let f := fun y : D01LogSpace => d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
  have he : (∫ y,(Real.exp (d01LogTotal y) : ℂ)*f y
      ∂d02TiltedDiagonalMeasure L)=∫ y,f y ∂d01DiagonalMeasure L := by
    unfold d02TiltedDiagonalMeasure
    rw [d01TiltedDiagonalFiniteMeasure_toMeasure hL]
    exact d01_integral_remove_exponential_tilt _ _ d01LogTotal_continuous.measurable _
  rw [← he]
  have hbound : ∀ᵐ y ∂d02TiltedDiagonalMeasure L,
      ‖(Real.exp (d01LogTotal y) : ℂ)*f y‖≤d04OneSidedDiagonalBound b R := by
    filter_upwards [d02TiltedDiagonalMeasure_ae_orthant hL,
      d04TiltedDiagonalMeasure_ae_equal_totals hL] with y hy hbal
    exact d04OneSidedDiagonal_untilted_norm_bound ρ a b hρcap ha3 ha hb0 hb σ hR hσ hy hbal
  calc
    _ ≤ ∫ _y : D01LogSpace,d04OneSidedDiagonalBound b R ∂d02TiltedDiagonalMeasure L :=
      norm_integral_le_of_norm_le (integrable_const _) hbound
    _ = _ := by
      simpa using (integral_const_mul (μ:=d02TiltedDiagonalMeasure L)
        (d04OneSidedDiagonalBound b R) (fun _y : D01LogSpace => (1:ℝ)))

/-- Uniform removal of the actual exponential smoothing on every bounded
complex shift box. The majorant is the actual convergent D01 tilted mass. -/
theorem d04OneSidedDiagonal_smoothing_uniform
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) {R : ℝ} (hR : 0≤R)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ L : ℝ in atTop,∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
      ‖(∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
          (d04OneSidedLogSmoothing L y : ℂ) ∂d01DiagonalMeasure L)-
        ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
          ∂d01DiagonalMeasure L‖<ε := by
  have hρK : ∀ k,HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=0) (b:=a k))
    exact fun t ht => hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k,0≤b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let A := ∫ _y : D01LogSpace,(1:ℝ) ∂d02TiltedLimitMeasure
  let M := A+1
  have hA : 0≤A := integral_nonneg (fun _ => by norm_num)
  have hM : 0<M := by dsimp [M]; linarith
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace,(1:ℝ) ∂d02TiltedLimitMeasure)<M by
      dsimp [M,A]; linarith)
  have hdecay : Tendsto (fun L : ℝ =>
      d04OneSidedDiagonalBound b R*Real.exp (-2*L)*M) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : (-2:ℝ)<0))
    simpa using (he.const_mul (d04OneSidedDiagonalBound b R)).mul_const M
  filter_upwards [hmass,hdecay.eventually_lt_const hε,eventually_gt_atTop (0:ℝ)]
    with L hmass hsmall hL
  intro σ hσ
  have hbound := d04OneSidedDiagonal_smoothing_difference_bound
    ρ a b hρc hρcap ha3 ha hb0 hb σ hR hσ hL
  have hmassbound := mul_le_mul_of_nonneg_left hmass.le
    (mul_nonneg (d04OneSidedDiagonalBound_nonneg b R hb0) (Real.exp_pos (-2*L)).le)
  exact hbound.trans_lt (hmassbound.trans_lt hsmall)

/-- The smoothed arithmetic diagonal converges to the same original
nine-edge integral. Smoothing and measure convergence are proved separately. -/
theorem d04DiagonalMeasure_one_sided_smoothed_shifted_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) :
    Tendsto (fun L : ℝ => ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
      (d04OneSidedLogSmoothing L y : ℂ) ∂d01DiagonalMeasure L) atTop
      (𝓝 ((arithmeticFactor : ℂ)*∫ x : D01EdgeSpace,
        d04OneSidedShiftWeight σ (d01RowColumnSums x)*
          d04OneSidedProfileProduct ρ (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) := by
  let R := ‖σ 0‖+‖σ 1‖
  have hR : 0≤R := by dsimp [R]; positivity
  have hσ : ∀ i,‖σ i‖≤R := by
    intro i; fin_cases i <;> dsimp [R] <;> linarith [norm_nonneg (σ 0),norm_nonneg (σ 1)]
  have herr : Tendsto (fun L : ℝ =>
      (∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
        (d04OneSidedLogSmoothing L y : ℂ) ∂d01DiagonalMeasure L)-
      ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y
        ∂d01DiagonalMeasure L) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [d04OneSidedDiagonal_smoothing_uniform ρ a hρc hρcap ha3 ha hR hε]
      with L hL
    simpa only [dist_zero_right] using hL σ hσ
  have hmain := d04DiagonalMeasure_one_sided_profile_limit ρ a
    (d04OneSidedShiftWeight σ) hρc hρcap ha3 ha (d04OneSidedShiftWeight_continuous σ)
  simpa only [sub_add_cancel,zero_add] using herr.add hmain

theorem d04DiagonalMeasure_one_sided_smoothed_shifted_height_limit
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ) (σ : Fin 2 → ℂ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) :
    Tendsto (fun T : ℝ => ∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
      (d04OneSidedLogSmoothing (Real.log T) y : ℂ) ∂d01DiagonalMeasure (Real.log T)) atTop
      (𝓝 ((arithmeticFactor : ℂ)*∫ x : D01EdgeSpace,
        d04OneSidedShiftWeight σ (d01RowColumnSums x)*
          d04OneSidedProfileProduct ρ (d01RowColumnSums x)
            ∂volume.restrict d01NonnegativeOrthant)) :=
  (d04DiagonalMeasure_one_sided_smoothed_shifted_limit ρ a σ hρc hρcap ha3 ha).comp
    Real.tendsto_log_atTop

theorem d04OneSidedDiagonal_eventually_uniformly_bounded
    (ρ : Fin 4 → ℝ → ℂ) (a : Fin 4 → ℝ)
    (hρc : ∀ k,Continuous (ρ k))
    (hρcap : ∀ k t,ρ k t≠0 → t∈Icc 0 (a k))
    (ha3 : 0≤a 3) (ha : (∑ k,a k)<1) {R : ℝ} (hR : 0≤R) :
    ∃ B : ℝ,0<B ∧ ∀ᶠ L : ℝ in atTop,
      ∀ σ : Fin 2 → ℂ,(∀ i,‖σ i‖≤R) →
        ‖∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
          (d04OneSidedLogSmoothing L y : ℂ) ∂d01DiagonalMeasure L‖≤B := by
  have hρK : ∀ k,HasCompactSupport (ρ k) := by
    intro k
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=0) (b:=a k))
    exact fun t ht => hρcap k t ht
  choose b hb using fun k => (hρK k).exists_bound_of_continuous (hρc k)
  have hb0 : ∀ k,0≤b k := fun k => (norm_nonneg (ρ k 0)).trans (hb k 0)
  let A := ∫ _y : D01LogSpace,(1:ℝ) ∂d02TiltedLimitMeasure
  let M := A+1
  have hA : 0≤A := integral_nonneg (fun _ => by norm_num)
  have hM : 0<M := by dsimp [M]; linarith
  let B := d04OneSidedDiagonalBound b R*M+1
  have hB : 0<B := by
    dsimp [B]
    have := mul_nonneg (d04OneSidedDiagonalBound_nonneg b R hb0) hM.le
    linarith
  refine ⟨B,hB,?_⟩
  have hmass := d02TiltedDiagonalMeasure_mass_tendsto.eventually_lt_const
    (show (∫ _y : D01LogSpace,(1:ℝ) ∂d02TiltedLimitMeasure)<M by
      dsimp [M,A]; linarith)
  filter_upwards [hmass,eventually_gt_atTop (0:ℝ),
    d04OneSidedDiagonal_smoothing_uniform ρ a hρc hρcap ha3 ha hR (by norm_num : (0:ℝ)<1)]
    with L hmass hL herr
  intro σ hσ
  have hmain := (d04OneSidedDiagonal_norm_bound ρ a b hρc hρcap ha3 ha hb0 hb
    σ hR hσ hL).trans (mul_le_mul_of_nonneg_left hmass.le
      (d04OneSidedDiagonalBound_nonneg b R hb0))
  have herror := herr σ hσ
  have htri := norm_le_insert' (∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y*
      (d04OneSidedLogSmoothing L y : ℂ) ∂d01DiagonalMeasure L)
    (∫ y,d04OneSidedShiftWeight σ y*d04OneSidedProfileProduct ρ y ∂d01DiagonalMeasure L)
  dsimp [B]
  linarith

end
end Sechstmoment
