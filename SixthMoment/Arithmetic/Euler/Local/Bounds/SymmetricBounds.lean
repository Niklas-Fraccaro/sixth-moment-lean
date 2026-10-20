import SixthMoment.Arithmetic.Euler.Local.Bounds.DenominatorNorm


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem e1_norm_le (a b c d : ℂ) : ‖e1 a b c d‖≤‖a‖+‖b‖+‖c‖+‖d‖ := by
  unfold e1
  calc
    _ ≤ ‖a+b+c‖+‖d‖ := norm_add_le _ _
    _ ≤ (‖a+b‖+‖c‖)+‖d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem e2_norm_le (a b c d : ℂ) :
    ‖e2 a b c d‖≤‖a*b‖+‖a*c‖+‖a*d‖+‖b*c‖+‖b*d‖+‖c*d‖ := by
  unfold e2
  calc
    _ ≤ ‖a*b+a*c+a*d+b*c+b*d‖+‖c*d‖ := norm_add_le _ _
    _ ≤ (‖a*b+a*c+a*d+b*c‖+‖b*d‖)+‖c*d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((‖a*b+a*c+a*d‖+‖b*c‖)+‖b*d‖)+‖c*d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖a*b+a*c‖+‖a*d‖)+‖b*c‖)+‖b*d‖)+‖c*d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem e3_norm_le (a b c d : ℂ) :
    ‖e3 a b c d‖≤‖a*b*c‖+‖a*b*d‖+‖a*c*d‖+‖b*c*d‖ := by
  unfold e3
  calc
    _ ≤ ‖a*b*c+a*b*d+a*c*d‖+‖b*c*d‖ := norm_add_le _ _
    _ ≤ (‖a*b*c+a*b*d‖+‖a*c*d‖)+‖b*c*d‖ := by gcongr; exact norm_add_le _ _
    _ ≤ _ := by gcongr; exact norm_add_le _ _

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem e4_norm_eq (a b c d : ℂ) : ‖e4 a b c d‖=‖a‖*‖b‖*‖c‖*‖d‖ := by simp [e4]

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem q0_norm_le (a b c d : ℂ) (r : ℝ) (hr : 0≤r)
    (ha : ‖a‖≤r) (hb : ‖b‖≤r) (hc : ‖c‖≤r) (hd : ‖d‖≤r) (h : ℕ) :
    ‖q0 a b c d h‖≤((h:ℝ)+1)*((h:ℝ)+2)*((h:ℝ)+3)/6*r^h :=
  norm_coeff4_closed a b c d r hr ha hb hc hd h

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem q1_norm_le (a b c d : ℂ) (h : ℕ) :
    ‖q1 a b c d h‖≤‖coeff4 a b c d (h+1)‖+‖e1 a b c d‖*‖coeff4 a b c d h‖ := by
  simpa [q1,norm_mul] using norm_sub_le (coeff4 a b c d (h+1)) (e1 a b c d*coeff4 a b c d h)

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem q2_norm_le (a b c d : ℂ) (h : ℕ) :
    ‖q2 a b c d h‖≤‖coeff4 a b c d (h+2)‖+‖e1 a b c d‖*‖coeff4 a b c d (h+1)‖+
      ‖e2 a b c d‖*‖coeff4 a b c d h‖ := by
  unfold q2
  calc
    _ ≤ ‖coeff4 a b c d (h+2)-e1 a b c d*coeff4 a b c d (h+1)‖+‖e2 a b c d*coeff4 a b c d h‖ := norm_add_le _ _
    _ ≤ _ := by
      simpa only [norm_mul] using
        add_le_add (norm_sub_le (coeff4 a b c d (h+2))
          (e1 a b c d*coeff4 a b c d (h+1)))
          (le_refl ‖e2 a b c d*coeff4 a b c d h‖)

end SixthMoment.Source.NoDPLocal


namespace SixthMoment.Source.NoDPLocal

open Finset
open scoped BigOperators

theorem q3_norm_succ (a b c d : ℂ) (h : ℕ) :
    ‖q3 a b c d (h+1)‖=‖a‖*‖b‖*‖c‖*‖d‖*‖coeff4 a b c d h‖ := by
  rw [q3_succ,norm_mul,norm_neg,e4_norm_eq]

end SixthMoment.Source.NoDPLocal
