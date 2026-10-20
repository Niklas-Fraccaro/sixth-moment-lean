import Sechstmoment.Denominator.Balanced.FiniteGaussianMomentDecomposition
import Sechstmoment.Denominator.Balanced.GaussianDualDiagonal
import Sechstmoment.Denominator.Balanced.ShiftedEndpoint

namespace Sechstmoment
open Complex Real Source MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1000000

theorem d02FiniteGaussianDiagonal_weighted_physical_identity {T : ℝ} (hT : 1<T)
    (δ : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : SecondMomentShifts)
    (Φ : ℝ → ℝ) (χ : ℝ → ℂ) :
    (∫ t : ℝ,(Φ (t/T):ℂ)*χ t*
      ∑ q∈(d02ActualSixCut T δ a).filter d02SixIsDiagonal,
        d02SixRawGaussianTerm T t ρ (rawSecondMomentShifts T σ) q)/
          (T*(Real.log T)^9:ℂ)=
    (∫ t : ℝ,(Φ (t/T):ℂ)*χ t*
      (∫ y,d01ComplexLaplaceWeight (![σ 0,0,0],![σ 1,0,0]) y*
        d02GaussianTruncatedFourProfile δ (fun j x => (ρ j x:ℂ)) y*
        (d02GaussianV0 (2*Real.pi*Real.exp (Real.log T*d02LogCutCoordinate y)/t):ℂ)
          ∂d01DiagonalMeasure (Real.log T)))/(T:ℂ) := by
  classical
  rw [show (T*(Real.log T)^9:ℂ)=(Real.log T:ℂ)^9*(T:ℂ) by ring,
    div_mul_eq_div_div,←integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_div_assoc]
  exact congrArg (fun z : ℂ => (Φ (t/T):ℂ)*χ t*z)
    (d02_actual_finite_gaussian_diagonal_measure_identity hT δ t a ρ hcap σ)

theorem d02FiniteGaussianDiagonal_direct_physical_identity {T : ℝ} (hT : 1<T)
    (δ : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : SecondMomentShifts) (Φ : ℝ → ℝ) :
    d02FiniteGaussianTimeSum T σ ρ Φ 0 ((d02ActualSixCut T δ a).filter d02SixIsDiagonal)/
      (T*(Real.log T)^9:ℂ)=
    d02GaussianTruncatedDiagonalPhysicalHeightMean δ T (fun j x => (ρ j x:ℂ))
      (![σ 0,0,0],![σ 1,0,0]) Φ := by
  unfold d02FiniteGaussianTimeSum d02ActualSixCut rawSecondMomentShifts
  simpa only [Complex.cpow_zero,mul_one]
    using d02_actual_finite_gaussian_diagonal_time_mean_identity hT δ a ρ hcap σ Φ

theorem d02FiniteGaussianDiagonal_dual_physical_identity {T : ℝ} (hT : 1<T)
    (δ : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : SecondMomentShifts)
    (Φ : ℝ → ℝ) (hΦs : tsupport Φ⊆Icc 1 2) :
    (secondDualPower T (rawSecondMomentShifts T σ)*
      d02FiniteGaussianTimeSum T (d02DualSecondMomentShifts σ) ρ Φ
        (-(σ 0+σ 1)/(Real.log T:ℂ))
        ((d02ActualSixCut T δ a).filter d02SixIsDiagonal))/(T*(Real.log T)^9:ℂ)=
    d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T (fun j x => (ρ j x:ℂ))
      (![-σ 1,0,0],![-σ 0,0,0]) σ Φ := by
  classical
  have hTp : 0<T := zero_lt_one.trans hT
  let s := (d02ActualSixCut T δ a).filter d02SixIsDiagonal
  let theta : ℂ := -(σ 0+σ 1)/(Real.log T:ℂ)
  have he : (fun t : ℝ => secondDualPower T (rawSecondMomentShifts T σ)*
      ((Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^theta*
        ∑ q∈s,d02SixRawGaussianTerm T t ρ
          (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) q))=
    fun t : ℝ => (Φ (t/T):ℂ)*secondDualPower t (rawSecondMomentShifts T σ)*
      ∑ q∈s,d02SixRawGaussianTerm T t ρ
        (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) q := by
    funext t
    by_cases hz : Φ (t/T)=0
    · simp [hz]
    have hy : t/T∈Icc (1:ℝ) 2 := hΦs (subset_tsupport Φ hz)
    have hty : 0<t/T := zero_lt_one.trans_le hy.1
    have hfac := secondDualPower_dyadic_factorization hTp hty σ
    rw [show T*(t/T)=t by field_simp [hTp.ne']] at hfac
    rw [hfac]
    dsimp only [theta]
    ring
  calc
    _ = (∫ t : ℝ,secondDualPower T (rawSecondMomentShifts T σ)*
        ((Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^theta*
          ∑ q∈s,d02SixRawGaussianTerm T t ρ
            (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) q))/
              (T*(Real.log T)^9:ℂ) := by rw [integral_const_mul]; rfl
    _ = (∫ t : ℝ,(Φ (t/T):ℂ)*secondDualPower t (rawSecondMomentShifts T σ)*
        ∑ q∈s,d02SixRawGaussianTerm T t ρ
          (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) q)/
            (T*(Real.log T)^9:ℂ) := by rw [he]
    _ = _ := d02FiniteGaussianDiagonal_weighted_physical_identity hT δ a ρ hcap
      (d02DualSecondMomentShifts σ) Φ (fun t => secondDualPower t (rawSecondMomentShifts T σ))

theorem d02GaussianFiniteDiagonalMoment_physical_identity {T : ℝ} (hT : 1<T)
    (δ : ℝ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (σ : SecondMomentShifts)
    (Φ : ℝ → ℝ) (hΦs : tsupport Φ⊆Icc 1 2) :
    d02GaussianFiniteDiagonalMoment T σ ρ Φ a δ/(T*(Real.log T)^9:ℂ)=
      Complex.exp ((σ 0+σ 1)/2)*
        (d02GaussianTruncatedDiagonalPhysicalHeightMean δ T (fun j x => (ρ j x:ℂ))
          (![σ 0,0,0],![σ 1,0,0]) Φ+
        d02GaussianTruncatedDualDiagonalPhysicalHeightMean δ T (fun j x => (ρ j x:ℂ))
          (![-σ 1,0,0],![-σ 0,0,0]) σ Φ) := by
  classical
  unfold d02GaussianFiniteDiagonalMoment d02FiniteGaussianHeightPiece
  rw [mul_div_assoc]
  apply congrArg (fun z : ℂ => Complex.exp ((σ 0+σ 1)/2)*z)
  rw [add_div,
    d02FiniteGaussianDiagonal_direct_physical_identity hT δ a ρ hcap σ Φ,
    d02FiniteGaussianDiagonal_dual_physical_identity hT δ a ρ hcap σ Φ hΦs]

theorem d02SingleBalancedShift_re_lower {R C : ℝ} (hRC : R≤C) (hC : 0≤C)
    (z : ℂ) (hz : ‖z‖≤R) : ∀ i : Fin 3,-C≤(![z,0,0] i).re := by
  have hzR : -R≤z.re := (abs_le.mp ((Complex.abs_re_le_norm z).trans hz)).1
  intro i
  fin_cases i
  · change -C≤z.re
    exact (neg_le_neg hRC).trans hzR
  · change -C≤(0:ℝ)
    exact neg_nonpos.mpr hC
  · change -C≤(0:ℝ)
    exact neg_nonpos.mpr hC

theorem d02GaussianFiniteDiagonalMoment_normalized_tendsto {R δ : ℝ}
    (hR : 0≤R) (hδ : 0≤δ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ j,Continuous (ρ j)) (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (σ : SecondMomentShifts) (hσ : ∀ j,‖σ j‖≤R) :
    Tendsto (fun T : ℝ => d02GaussianFiniteDiagonalMoment T σ ρ Φ a δ/
      (T*(Real.log T)^9:ℂ)) atTop
      (𝓝 (((arithmeticFactor*(∫ t : ℝ,Φ t):ℝ):ℂ)*d02BalancedShiftedEdgeIntegral ρ σ)) := by
  let C : ℝ := max R (|Real.log (2*Real.pi)|+Real.log 2)
  have hRC : R≤C := le_max_left _ _
  have hC : 0≤C := hR.trans hRC
  have hOffset : |Real.log (2*Real.pi)|+Real.log 2≤C := le_max_right _ _
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs j (subset_tsupport (ρ j) hn)).2
  have hρcap : ∀ j x,ρ j x≠0 → x∈Icc 0 (a j) :=
    fun j x hx => hρs j (subset_tsupport (ρ j) hx)
  have hρCcap : ∀ j x,(ρ j x:ℂ)≠0 → x∈Icc 0 (a j) := by
    intro j x hx
    exact hρcap j x (Complex.ofReal_ne_zero.mp hx)
  have hρCc : ∀ j,Continuous (fun x => (ρ j x:ℂ)) :=
    fun j => Complex.continuous_ofReal.comp (hρ j)
  have hrep := d02GaussianTruncatedDualDiagonalPhysicalHeightMean_replacement_tendsto
    hδ hR hC hOffset (fun j x => (ρ j x:ℂ)) a Φ hρCc hρCcap hΦ hΦs
    σ (![-σ 1,0,0],![-σ 0,0,0]) hσ
    (d02SingleBalancedShift_re_lower hRC hC (-σ 1) (by simpa only [norm_neg] using hσ 1))
    (d02SingleBalancedShift_re_lower hRC hC (-σ 0) (by simpa only [norm_neg] using hσ 0))
  have hmain := d02BalancedShiftedTruncatedPhysicalHeightMean_limit
    hδ ρ a σ Φ hρ hρcap hΦ hΦs
  have h := hmain.add (hrep.const_mul (Complex.exp ((σ 0+σ 1)/2)))
  simp only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  rw [d02GaussianFiniteDiagonalMoment_physical_identity hT δ a ρ hcap σ Φ hΦs]
  dsimp only [d02BalancedDirectShift,d02BalancedDualShift]
  ring

theorem d02GaussianFiniteDiagonalMoment_normalized_uniform_bound {R δ : ℝ}
    (hR : 0≤R) (hδ : 0≤δ) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hρ : ∀ j,Continuous (ρ j)) (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : Continuous Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∃ B : ℝ,0≤B ∧ ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
      ‖d02GaussianFiniteDiagonalMoment T σ ρ Φ a δ/(T*(Real.log T)^9:ℂ)‖≤B := by
  let C : ℝ := max R (|Real.log (2*Real.pi)|+Real.log 2)
  have hRC : R≤C := le_max_left _ _
  have hC : 0≤C := hR.trans hRC
  have hOffset : |Real.log (2*Real.pi)|+Real.log 2≤C := le_max_right _ _
  have hcap : ∀ j x,a j<x → ρ j x=0 := by
    intro j x hx
    by_contra hn
    exact (not_le_of_gt hx) (hρs j (subset_tsupport (ρ j) hn)).2
  have hρCcap : ∀ j x,(ρ j x:ℂ)≠0 → x∈Icc 0 (a j) :=
    fun j x hx => hρs j (subset_tsupport (ρ j) (Complex.ofReal_ne_zero.mp hx))
  have hρCc : ∀ j,Continuous (fun x => (ρ j x:ℂ)) :=
    fun j => Complex.continuous_ofReal.comp (hρ j)
  obtain ⟨B,hB,hb⟩ := d02GaussianTruncatedDiagonalPhysicalHeightMean_eventually_uniform_norm_bound
    hδ (fun j x => (ρ j x:ℂ)) a Φ hC hOffset hρCc hρCcap hΦ hΦs
  obtain ⟨D,hD,hd⟩ := d02GaussianTruncatedDualDiagonalPhysicalHeightMean_eventually_uniform_norm_bound
    hδ hR hC hOffset (fun j x => (ρ j x:ℂ)) a Φ hρCc hρCcap hΦ hΦs
  refine ⟨Real.exp R*(B+D),by positivity,?_⟩
  filter_upwards [hb,hd,eventually_gt_atTop (1:ℝ)] with T hb hd hT
  intro σ hσ
  have hb' := (hb (![σ 0,0,0],![σ 1,0,0])
    (d02SingleBalancedShift_re_lower hRC hC (σ 0) (hσ 0))
    (d02SingleBalancedShift_re_lower hRC hC (σ 1) (hσ 1))).2
  have hd' := (hd σ (![-σ 1,0,0],![-σ 0,0,0]) hσ
    (d02SingleBalancedShift_re_lower hRC hC (-σ 1) (by simpa only [norm_neg] using hσ 1))
    (d02SingleBalancedShift_re_lower hRC hC (-σ 0) (by simpa only [norm_neg] using hσ 0))).2
  rw [d02GaussianFiniteDiagonalMoment_physical_identity hT δ a ρ hcap σ Φ hΦs,norm_mul]
  exact mul_le_mul (d02ZetaCentering_norm_le σ hσ)
    ((norm_add_le _ _).trans (add_le_add hb' hd')) (norm_nonneg _) (by positivity)

end
end Sechstmoment
