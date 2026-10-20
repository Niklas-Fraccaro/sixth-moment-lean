import Sechstmoment.Arithmetic.Euler.Convolution.SeriesConvolution
import Sechstmoment.Arithmetic.Euler.Convolution.TripleSeries

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
namespace Sechstmoment.Source.NoDPGlobalConvolution
open NoDPLocal NoDPResidues NoDPLocalClosure NoDPGlobalRest
open scoped BigOperators
noncomputable section

def originalTerm (s : Fin 4 → ℂ) (u v : ℂ) (q : ℕ × ℕ) : ℂ :=
  originalCoeff s q.1 q.2 * (q.1:ℂ)^(-u) * (q.2:ℂ)^(-v)

def originalDirichlet (s : Fin 4 → ℂ) (u v : ℂ) : ℂ := ∑' q, originalTerm s u v q

theorem originalCoeff_pairConv (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) :
    (fun q : ℕ × ℕ => originalCoeff s q.1 q.2) =
      pairConv (gamma s) (fun q => tripleCoeff s q.1 * tripleCoeff s q.2) := by
  funext q
  simpa only [pairConv,mul_assoc] using originalCoeff_convolution s ρ hρ0 hρ hs q.1 q.2

theorem triplePair_hasSum (s : Fin 4 → ℂ) (ρ : ℝ) (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ)
    (hu : ρ < u.re) (hv : ρ < v.re) :
    HasSum (pairWeight u v (fun q => tripleCoeff s q.1 * tripleCoeff s q.2))
      (tripleZeta s u * tripleZeta s v) := by
  have H := (tripleTerm_uniform_hasSum s ρ hs u hu).mul
    (tripleTerm_uniform_hasSum s ρ hs v hv)
    (summable_mul_of_summable_norm (tripleTerm_absolute s ρ hs u hu)
      (tripleTerm_absolute s ρ hs v hv))
  convert H using 1
  funext q
  simp only [pairWeight,tripleTerm]
  ring

theorem originalTerm_hasSum (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ) (hu : ρ < u.re) (hv : ρ < v.re) :
    HasSum (originalTerm s u v)
      (restDirichlet s u v * (tripleZeta s u * tripleZeta s v)) := by
  have HG : HasSum (pairWeight u v (gamma s)) (restDirichlet s u v) :=
    (restDirichlet_absolute s ρ hρ0 hρ hs u v (by linarith) (by linarith)).of_norm.hasSum
  have HT := pairConv_hasSum _ _ _ _ HG (triplePair_hasSum s ρ hs u v hu hv)
    (fun n => by simp [pairWeight,gamma_zero_left])
    (fun n => by simp [pairWeight,gamma_zero_right])
    (fun n => by simp [pairWeight]) (fun n => by simp [pairWeight])
  rw [← pairWeight_convolution, ← originalCoeff_pairConv s ρ hρ0 hρ hs] at HT
  exact HT

theorem originalTerm_absolute (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ) (hu : ρ < u.re) (hv : ρ < v.re) :
    Summable (fun q => ‖originalTerm s u v q‖) :=
  (originalTerm_hasSum s ρ hρ0 hρ hs u v hu hv).summable.norm

theorem originalDirichlet_six_zeta (s : Fin 4 → ℂ) (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1/4)
    (hs : ∀ j, ‖s j‖ ≤ ρ) (u v : ℂ) (hu : ρ < u.re) (hv : ρ < v.re) :
    originalDirichlet s u v = restDirichlet s u v *
      (riemannZeta (1+u+s 1) * (riemannZeta (1+u+s 2) * riemannZeta (1+u+s 3)) *
       (riemannZeta (1+v+s 1) * (riemannZeta (1+v+s 2) * riemannZeta (1+v+s 3)))) :=
  (originalTerm_hasSum s ρ hρ0 hρ hs u v hu hv).tsum_eq

end
end Sechstmoment.Source.NoDPGlobalConvolution
