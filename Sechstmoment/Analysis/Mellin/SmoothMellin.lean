import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.MellinInversion
import Sechstmoment.Analysis.Gaussian.Integrability

/-! Mellin transforms of the literal fixed smooth dyadic weights.
The logarithmic pullback is compactly supported and smooth; its Fourier
transform is Schwartz. In particular every fixed polynomial height cost
is integrable. No Mellin-decay hypothesis is added to the weight.
-/

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set
open scoped Topology ContDiff FourierTransform
noncomputable section

def logarithmicMellinWeight (w : ℝ → ℂ) (κ u : ℝ) : ℂ :=
  (Real.exp (-κ*u) : ℂ)*w (Real.exp (-u))

theorem logarithmicMellinWeight_contDiff {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (κ : ℝ) :
    ContDiff ℝ ∞ (logarithmicMellinWeight w κ) := by
  unfold logarithmicMellinWeight
  have hreal : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-κ*u)) := by fun_prop
  exact (Complex.ofRealCLM.contDiff.comp hreal).mul (hw.comp (by fun_prop))

theorem logarithmicMellinWeight_tsupport {w : ℝ → ℂ}
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (κ : ℝ) :
    tsupport (logarithmicMellinWeight w κ) ⊆ Icc (-Real.log 2) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro u hu
  have hwu : w (Real.exp (-u)) ≠ 0 := by
    intro hz
    exact hu (by simp [logarithmicMellinWeight,hz])
  have hpoint := hws (subset_tsupport w (Function.mem_support.mpr hwu))
  have hlow := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hpoint.1
  have hhigh := Real.log_le_log (Real.exp_pos (-u)) hpoint.2
  rw [Real.log_one,Real.log_exp] at hlow
  rw [Real.log_exp] at hhigh
  exact ⟨by linarith,by linarith⟩

def logarithmicMellinSchwartz {w : ℝ → ℂ} (hw : ContDiff ℝ ∞ w)
    (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (κ : ℝ) : SchwartzMap ℝ ℂ :=
  (show HasCompactSupport (logarithmicMellinWeight w κ) from
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (logarithmicMellinWeight_tsupport hws κ)).toSchwartzMap
    (logarithmicMellinWeight_contDiff hw κ)

theorem smooth_mellin_eq_schwartz_fourier {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1 : ℝ) 2)
    (κ v : ℝ) :
    mellin w ((κ : ℂ)+(v : ℂ)*I) =
      (𝓕 (logarithmicMellinSchwartz hw hws κ)) (v/(2*Real.pi)) := by
  rw [mellin_eq_fourier]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,
    neg_zero,add_zero,Complex.add_im,Complex.mul_I_im,zero_add]
  rfl

theorem smooth_mellin_line_continuous {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1 : ℝ) 2) (κ : ℝ) :
    Continuous (fun v : ℝ => mellin w ((κ : ℂ)+(v : ℂ)*I)) := by
  have he : (fun v : ℝ => mellin w ((κ : ℂ)+(v : ℂ)*I)) =
      fun v => (𝓕 (logarithmicMellinSchwartz hw hws κ)) (v/(2*Real.pi)) :=
    funext (smooth_mellin_eq_schwartz_fourier hw hws κ)
  rw [he]
  exact (𝓕 (logarithmicMellinSchwartz hw hws κ)).continuous.comp (by fun_prop)

theorem schwartz_one_add_abs_pow_integrable (f : SchwartzMap ℝ ℂ) (k : ℕ) :
    Integrable (fun v : ℝ => (1+|v|)^k*‖f v‖) := by
  have h0 : Integrable (fun v : ℝ => ‖f v‖) := f.integrable.norm
  have hk := f.integrable_pow_mul volume k
  have hsum : Integrable (fun v : ℝ => (1+|v|^k)*‖f v‖) := by
    convert h0.add hk using 1
    ext v
    simp only [Pi.add_apply,Real.norm_eq_abs]
    ring
  apply (hsum.const_mul ((2 : ℝ)^k)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2^k*(1+|v|^k))*‖f v‖ :=
      mul_le_mul_of_nonneg_right (one_add_abs_pow_le k v) (norm_nonneg _)
    _ = _ := by ring

/-- Every fixed polynomial height loss is integrable against the actual
Mellin transform of a fixed smooth dyadic weight. -/
theorem smooth_mellin_weighted_integrable {w : ℝ → ℂ}
    (hw : ContDiff ℝ ∞ w) (hws : tsupport w ⊆ Icc (1 : ℝ) 2)
    (κ : ℝ) (k : ℕ) :
    Integrable (fun v : ℝ => (1+|v|)^k*‖mellin w ((κ : ℂ)+(v : ℂ)*I)‖) := by
  let f := 𝓕 (logarithmicMellinSchwartz hw hws κ)
  have hπ : 0 < 2*Real.pi := by positivity
  have hπ1 : 1 ≤ 2*Real.pi := by linarith [Real.two_le_pi]
  have hf := (schwartz_one_add_abs_pow_integrable f k).comp_div hπ.ne'
  have hcont := smooth_mellin_line_continuous hw hws κ
  apply (hf.const_mul ((2*Real.pi)^k)).mono' (by fun_prop)
  apply Filter.Eventually.of_forall
  intro v
  rw [Real.norm_of_nonneg (by positivity),smooth_mellin_eq_schwartz_fourier hw hws κ]
  have hv : |v| = (2*Real.pi)*|v/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos hπ]
    field_simp
  have hscale : 1+|v| ≤ (2*Real.pi)*(1+|v/(2*Real.pi)|) := by
    rw [hv]
    nlinarith
  calc
    _ ≤ ((2*Real.pi)*(1+|v/(2*Real.pi)|))^k*‖f (v/(2*Real.pi))‖ := by
      gcongr
    _ = _ := by rw [mul_pow]; ring

end
end Sechstmoment.Source
