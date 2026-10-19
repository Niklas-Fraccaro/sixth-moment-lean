import Mathlib.Data.Fin.VecNotation
import Mathlib.MeasureTheory.Integral.Pi

namespace Sechstmoment
open MeasureTheory

noncomputable def finiteIteratedIntegral : (n : Nat) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, f => f Fin.elim0
  | n+1, f => ∫ x, finiteIteratedIntegral n (fun v => f (Fin.cons x v))

theorem integral_pi_eq_iterated (n : Nat) (f : (Fin n → ℝ) → ℝ)
    (hf : Integrable f) :
    (∫ v, f v) = finiteIteratedIntegral n f := by
  induction n with
  | zero =>
      rw [Measure.volume_pi_eq_dirac (x := Fin.elim0)]
      simp [finiteIteratedIntegral]
  | succ n ih =>
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
      have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm
      have hp : Integrable (fun z : ℝ × (Fin n → ℝ) => f (Fin.cons z.1 z.2)) := by
        have ht := (hm.integrable_comp_emb e.symm.measurableEmbedding).2 hf
        simpa [Function.comp_def, MeasurableEquiv.piFinSuccAbove_symm_apply,
          Fin.insertNthEquiv] using ht
      calc
        (∫ v, f v) = ∫ z : ℝ × (Fin n → ℝ), f (Fin.cons z.1 z.2) := by
          simpa [MeasurableEquiv.piFinSuccAbove_symm_apply,
            Fin.insertNthEquiv] using (hm.integral_comp' f).symm
        _ = ∫ x, ∫ v, f (Fin.cons x v) := integral_prod _ hp
        _ = ∫ x, finiteIteratedIntegral n (fun v => f (Fin.cons x v)) := by
          apply integral_congr_ae
          filter_upwards [hp.prod_right_ae] with x hx
          exact ih _ hx
        _ = _ := rfl

theorem integral_fin_four (f : (Fin 4 → ℝ) → ℝ) (hf : Integrable f) :
    (∫ w, f w) = ∫ t, ∫ r, ∫ s, ∫ x, f ![t,r,s,x] := by
  rw [integral_pi_eq_iterated 4 f hf]
  simp only [finiteIteratedIntegral]
  rfl

end Sechstmoment
