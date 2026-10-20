import Sechstmoment.Arithmetic.QuadraticDivisor.Reduction.WeilBounds
import Sechstmoment.Arithmetic.Watt.Statement


namespace DivisorProof
namespace Watt41
open Real MeasureTheory Set Finset Classical
open scoped BigOperators ContDiff FourierTransform SchwartzMap
noncomputable section
set_option maxHeartbeats 2000000

def fourierCoefficient (g : ℝ → ℂ) (c : ℕ) (l : ℤ) : ℂ :=
  ∫ x : ℝ, g ((c : ℝ)*x)*ePhase ((l : ℝ)*x)

theorem fourierCoefficient_eq_fourier (g : ℝ → ℂ) (c : ℕ) (l : ℤ) :
    fourierCoefficient g c l = 𝓕 (fun x : ℝ => g ((c : ℝ)*x)) (-l) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [smul_eq_mul, ePhase]
  push_cast
  ring_nf

def scaledSchwartz {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) : 𝓢(ℝ, ℂ) := by
  have hs' : HasCompactSupport (fun x : ℝ => g ((c : ℝ)*x)) := by
    simpa only [smul_eq_mul] using hs.comp_smul
      (c := (c : ℝ)) (by exact_mod_cast hc.ne')
  exact hs'.toSchwartzMap (hg.comp (contDiff_const.mul contDiff_id))

theorem fourierCoefficient_summable {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) :
    Summable (fourierCoefficient g c) := by
  let f := scaledSchwartz hg hs hc
  have hfcoe : (f : ℝ → ℂ) = fun x : ℝ => g ((c : ℝ)*x) := rfl
  have hf : Summable (fun n : ℤ => (𝓕 f) (n : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 f).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  apply (hf.comp_injective (Equiv.neg ℤ).injective).congr
  intro l
  change (𝓕 f) ((-l : ℤ) : ℝ) = fourierCoefficient g c l
  rw [SchwartzMap.fourier_coe, hfcoe, fourierCoefficient_eq_fourier]
  simp only [Int.cast_neg]

theorem fourierCoefficient_norm_summable {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) :
    Summable (fun l : ℤ => ‖fourierCoefficient g c l‖) :=
  (fourierCoefficient_summable hg hs hc).norm

theorem fourierSeries_summable {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) (t : ℝ) :
    Summable (fun l : ℤ => fourierCoefficient g c l*ePhase (-(l : ℝ)*t)) := by
  apply summable_norm_iff.mp
  simpa only [norm_mul, norm_ePhase, mul_one] using
    fourierCoefficient_norm_summable hg hs hc

theorem lattice_poisson {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) (a : ℝ) :
    (∑' j : ℤ, g (a+(c : ℝ)*j)) =
      ∑' l : ℤ, fourierCoefficient g c l*ePhase (-(l : ℝ)*(a/c)) := by
  let f := scaledSchwartz hg hs hc
  have hfcoe : (f : ℝ → ℂ) = fun x : ℝ => g ((c : ℝ)*x) := rfl
  have hcp : (0 : ℝ) < c := by exact_mod_cast hc
  have heq (j : ℤ) : g (a+(c : ℝ)*j) = f (a/c+j) := by
    change g (a+(c : ℝ)*j) = g ((c : ℝ)*(a/c+j))
    congr 1
    field_simp
  simp_rw [heq]
  rw [f.tsum_eq_tsum_fourier (a/c), ← (Equiv.neg ℤ).tsum_eq]
  apply tsum_congr
  intro l
  simp only [Equiv.neg_apply, SchwartzMap.fourier_coe, hfcoe, Int.cast_neg]
  rw [fourierCoefficient_eq_fourier, fourier_eq_ePhase]
  congr 2
  push_cast
  ring

def completedSum (g : ℝ → ℂ) (c : ℕ) (k : ℤ) : ℂ :=
  ∑ a ∈ (range c).filter (fun a => a.Coprime c),
    ePhase ((k : ℝ)*(inverseRepresentative a c : ℝ)/(c : ℝ))*
      ∑' j : ℤ, g ((a : ℝ)+(c : ℝ)*j)

theorem completedSum_eq_fourier {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) (k : ℤ) :
    completedSum g c k =
      ∑' l : ℤ, fourierCoefficient g c l*kloostermanSum c (-l) k := by
  unfold completedSum
  simp_rw [lattice_poisson hg hs hc, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun (a : ℕ) _ =>
    (fourierSeries_summable hg hs hc ((a : ℝ)/c)).mul_left
      (ePhase ((k : ℝ)*(inverseRepresentative a c : ℝ)/(c : ℝ))))]
  apply tsum_congr
  intro l
  unfold kloostermanSum
  rw [mul_sum]
  apply sum_congr rfl
  intro a _
  calc _ = fourierCoefficient g c l*
      (ePhase ((k : ℝ)*(inverseRepresentative a c : ℝ)/(c : ℝ))*
        ePhase (-(l : ℝ)*((a : ℝ)/c))) := by ring
    _ = fourierCoefficient g c l*ePhase
        ((k : ℝ)*(inverseRepresentative a c : ℝ)/(c : ℝ)-(l : ℝ)*((a : ℝ)/c)) := by
      rw [← ePhase_add]
      congr 2
      ring
    _ = _ := by
      congr 2
      push_cast
      ring

theorem completedSum_eq_classical {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) {c : ℕ} (hc : 0 < c) (k : ℤ) :
    completedSum g c k =
      ∑' l : ℤ, fourierCoefficient g c l*classicalKloostermanSum k (-l) c :=
  completedSum_eq_fourier hg hs hc k

end
end Watt41
end DivisorProof
