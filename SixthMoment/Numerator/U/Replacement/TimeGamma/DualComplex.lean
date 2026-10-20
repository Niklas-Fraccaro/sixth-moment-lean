import SixthMoment.Numerator.U.Replacement.TimeGamma.LogStrip
import SixthMoment.Zeta.AFE.Four.DualBound

namespace SixthMoment.Source
open SixthMoment Complex Set Metric Filter
open scoped BigOperators Topology ContDiff ComplexConjugate
noncomputable section
set_option maxHeartbeats 1000000

def bblrTimeDualBase (T : ℝ) (y : ℂ) (j : Fin 4) : ℂ :=
  if j.val < 2 then complexHeightPoint T y else 1-complexHeightPoint T y

def bblrTimeDualMultiplier (T : ℝ) (σ : MomentShifts) (y : ℂ) : ℂ :=
  ∏ j : Fin 4, zetaChi (bblrTimeDualBase T y j+σ j/(Real.log T : ℂ))

theorem bblrTimeDualMultiplier_ofReal (T : ℝ) (σ : MomentShifts) (y : ℝ) :
    bblrTimeDualMultiplier T σ (y : ℂ) = bblrDualMultiplier (T*y) (rawMomentShifts T σ) := by
  unfold bblrTimeDualMultiplier bblrDualMultiplier
  apply Finset.prod_congr rfl
  intro j _
  have he : bblrTimeDualBase T (y : ℂ) j = sourceZetaPoints (T*y) j := by
    fin_cases j <;> simp [bblrTimeDualBase,complexHeightPoint,sourceZetaPoints,
      criticalLinePoint]
  rw [he]
  rfl

theorem zetaChi_shift_eq_centeringFactorAt (T : ℝ) (s z : ℂ)
    (hs : zetaChi s ≠ 0) :
    zetaChi (s+z/(Real.log T : ℂ)) =
      Complex.exp (-z)*zetaChi s*centeringFactorAt T s z := by
  unfold centeringFactorAt
  rw [Complex.exp_neg]
  field_simp

theorem bblrTimeDualMultiplier_centering_eq {T : ℝ} (σ : MomentShifts) {y : ℂ}
    (hpoint : (complexHeightPoint T y).im ≠ 0) :
    bblrTimeDualMultiplier T σ y =
      Complex.exp (-∑ j : Fin 4, σ j)*
        ∏ j : Fin 4, centeringFactorAt T (bblrTimeDualBase T y j) (σ j) := by
  have hb (j : Fin 4) : (bblrTimeDualBase T y j).im ≠ 0 := by
    unfold bblrTimeDualBase
    split_ifs
    · exact hpoint
    · simpa only [Complex.sub_im,Complex.one_im,zero_sub,neg_ne_zero] using hpoint
  have hc : zetaChi (complexHeightPoint T y)*zetaChi (1-complexHeightPoint T y)=1 := by
    unfold zetaChi
    have hg := gammaReal_ne_zero_nonreal hpoint
    have hg' := gammaReal_ne_zero_nonreal (s := 1-complexHeightPoint T y) (by simpa using hpoint)
    rw [show 1-(1-complexHeightPoint T y) = complexHeightPoint T y by ring]
    field_simp
  have hprod : (∏ j : Fin 4, zetaChi (bblrTimeDualBase T y j))=1 := by
    rw [Fin.prod_univ_four]
    norm_num [bblrTimeDualBase]
    rw [show zetaChi (complexHeightPoint T y)*zetaChi (complexHeightPoint T y)*
      zetaChi (1-complexHeightPoint T y)*zetaChi (1-complexHeightPoint T y) =
      (zetaChi (complexHeightPoint T y)*zetaChi (1-complexHeightPoint T y))^2 by ring,hc]
    norm_num
  unfold bblrTimeDualMultiplier
  simp_rw [zetaChi_shift_eq_centeringFactorAt T _ _ (zetaChi_ne_zero_nonreal (hb _))]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib,hprod,mul_one,
    ← Complex.exp_sum,Finset.sum_neg_distrib]

end
end SixthMoment.Source
