import Mathlib.Data.Nat.GCD.Basic
import Mathlib.NumberTheory.LSeries.Dirichlet
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.EtaArithmetic


namespace Sechstmoment
open ArithmeticFunction Nat Complex
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 0

def a03GCDDirichletTerm (a b : ℕ) (w z s : ℂ) (x : ℕ × ℕ) : ℂ :=
  ((Nat.gcd (a*x.1) (b*x.2):ℕ):ℂ)^(1-s)*
    shiftedPowerArithmetic (1+w) x.1*shiftedPowerArithmetic (1+z) x.2

def a03GCDDirichlet (a b : ℕ) (w z s : ℂ) : ℂ :=
  ∑' x : ℕ × ℕ, a03GCDDirichletTerm a b w z s x

theorem a03GCDDirichletTerm_apply (a b : ℕ) (w z s : ℂ)
    {m n : ℕ} (hm : m≠0) (hn : n≠0) :
    a03GCDDirichletTerm a b w z s (m,n)=
      (Nat.gcd (a*m) (b*n):ℂ)^(1-s)*(m:ℂ)^(-(1+w))*(n:ℂ)^(-(1+z)) := by
  simp only [a03GCDDirichletTerm,shiftedPowerArithmetic_apply _ hm,
    shiftedPowerArithmetic_apply _ hn]

theorem a03GCDDirichletTerm_zero_left (a b : ℕ) (w z s : ℂ) (n : ℕ) :
    a03GCDDirichletTerm a b w z s (0,n)=0 := by simp [a03GCDDirichletTerm]

theorem a03GCDDirichletTerm_zero_right (a b : ℕ) (w z s : ℂ) (m : ℕ) :
    a03GCDDirichletTerm a b w z s (m,0)=0 := by simp [a03GCDDirichletTerm]

theorem shiftedPowerArithmetic_norm_summable {t : ℂ} (ht : 1<t.re) :
    Summable (fun n : ℕ => ‖shiftedPowerArithmetic t n‖) := by
  have h := summable_norm_iff.mpr (LSeriesSummable_zeta_iff.mpr ht)
  apply h.congr
  intro n
  change ‖LSeries.term (fun n => (ArithmeticFunction.zeta n:ℂ)) t n‖ = _
  rw [LSeries.term_def]
  by_cases hn : n=0
  · simp [hn]
  · simp only [hn,ite_false,ArithmeticFunction.zeta_apply_ne hn,
      shiftedPowerArithmetic_apply _ hn,Nat.cast_one,one_div,Complex.cpow_neg]

theorem a03GCDDirichlet_norm_summable {a b : ℕ} (ha : a≠0) (_hb : b≠0)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (hs : 1<s.re) :
    Summable (fun x : ℕ × ℕ => ‖a03GCDDirichletTerm a b w z s x‖) := by
  have hwm : Summable (fun n : ℕ => ‖shiftedPowerArithmetic (1+w) n‖) :=
    shiftedPowerArithmetic_norm_summable (by simp only [add_re,one_re]; linarith)
  have hzn : Summable (fun n : ℕ => ‖shiftedPowerArithmetic (1+z) n‖) :=
    shiftedPowerArithmetic_norm_summable (by simp only [add_re,one_re]; linarith)
  have hprod := @Summable.mul_of_nonneg ℕ ℕ
    (fun n => ‖shiftedPowerArithmetic (1+w) n‖)
    (fun n => ‖shiftedPowerArithmetic (1+z) n‖) hwm hzn
    (fun n => norm_nonneg _) (fun n => norm_nonneg _)
  apply hprod.of_nonneg_of_le (fun _ => norm_nonneg _)
  rintro ⟨m,n⟩
  by_cases hm : m=0
  · simp [hm,a03GCDDirichletTerm]
  by_cases hn : n=0
  · simp [hn,a03GCDDirichletTerm]
  have hd : 0<Nat.gcd (a*m) (b*n) :=
    Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero (mul_ne_zero ha hm))
  have hd1 : (1:ℝ)≤Nat.gcd (a*m) (b*n) := by exact_mod_cast hd
  have hdpow : ‖(Nat.gcd (a*m) (b*n):ℂ)^(1-s)‖≤1 := by
    rw [Complex.norm_natCast_cpow_of_pos hd]
    exact Real.rpow_le_one_of_one_le_of_nonpos hd1
      (by simp only [sub_re,one_re]; linarith)
  simp only [a03GCDDirichletTerm,norm_mul]
  calc
    _ ≤ 1*‖shiftedPowerArithmetic (1+w) m‖*‖shiftedPowerArithmetic (1+z) n‖ := by
      gcongr
    _ = _ := by ring

theorem a03GCDDirichlet_summable {a b : ℕ} (ha : a≠0) (hb : b≠0)
    {w z s : ℂ} (hw : 0<w.re) (hz : 0<z.re) (hs : 1<s.re) :
    Summable (a03GCDDirichletTerm a b w z s) :=
  (a03GCDDirichlet_norm_summable ha hb hw hz hs).of_norm

end
end Sechstmoment
