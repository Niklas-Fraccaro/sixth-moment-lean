import Sechstmoment.Analysis.Harmonic.ExponentialKernel

/-! Quantitative stability of continuous and literal harmonic Volterra operators.
All constants are uniform in the complex shift on a closed norm ball. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

def continuousStep (ν : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x in 0..t, f (t-x)*expKernel ν x

def discreteStep (L : ℝ) (ν : ℂ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  strictHarmonicQuadrature L t (fun x => f (t-x)*expKernel ν x)

def stepError (η R B D : ℝ) : ℝ :=
  kernelBound η R * (4*B+η*(D+B*R))

theorem stepError_nonneg {η R B D : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) : 0 ≤ stepError η R B D := by
  unfold stepError
  exact mul_nonneg (kernelBound_pos η R).le (by positivity)

theorem discreteStep_error {η R B D L : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hL : 0 < L) (hR : 0 ≤ R)
    {ν : ℂ} (hν : ‖ν‖ ≤ R) {t : ℝ} (ht : t ∈ Icc 0 η) :
    ‖discreteStep L ν f t-continuousStep ν f t‖ ≤ stepError η R B D/L := by
  have hs := regularProfile_section hf hR hν ht
  apply (strictHarmonicQuadrature_error hL ht.1 hs.bound_nonneg hs.lip_nonneg
    hs.continuous hs.norm_le hs.norm_sub_le).trans
  apply div_le_div_of_nonneg_right _ hL.le
  unfold stepError
  have hB := hf.bound_nonneg
  have hD := hf.lip_nonneg
  have hE := (kernelBound_pos η R).le
  nlinarith [mul_le_mul_of_nonneg_left ht.2 (by positivity : 0 ≤ kernelBound η R*(D+B*R))]

theorem continuousStep_norm {η R B D : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hR : 0 ≤ R) {ν : ℂ} (hν : ‖ν‖ ≤ R)
    {t : ℝ} (ht : t ∈ Icc 0 η) :
    ‖continuousStep ν f t‖ ≤ B*kernelBound η R*η := by
  have hs := regularProfile_section hf hR hν ht
  apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := B*kernelBound η R) ?_).trans
  · rw [sub_zero,abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left ht.2 hs.bound_nonneg
  · intro x hx
    rw [uIoc_of_le ht.1] at hx
    exact hs.norm_le x ⟨hx.1.le,hx.2⟩

theorem continuousStep_norm_sub_of_le {η R B D : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hR : 0 ≤ R) {ν : ℂ} (hν : ‖ν‖ ≤ R)
    {s t : ℝ} (hs : s ∈ Icc 0 η) (ht : t ∈ Icc 0 η) (hst : s ≤ t) :
    ‖continuousStep ν f t-continuousStep ν f s‖ ≤
      (kernelBound η R*(B+D*η))*(t-s) := by
  let Ft : ℝ → ℂ := fun x => f (t-x)*expKernel ν x
  let Fs : ℝ → ℂ := fun x => f (s-x)*expKernel ν x
  have hr := regularProfile_section hf hR hν ht
  have hsreg := regularProfile_section hf hR hν hs
  have hi0 : IntervalIntegrable Ft volume 0 s :=
    (hr.continuous.mono (Icc_subset_Icc le_rfl hst)).intervalIntegrable_of_Icc hs.1
  have hi1 : IntervalIntegrable Ft volume s t :=
    (hr.continuous.mono (Icc_subset_Icc hs.1 le_rfl)).intervalIntegrable_of_Icc hst
  have his : IntervalIntegrable Fs volume 0 s := hsreg.continuous.intervalIntegrable_of_Icc hs.1
  have hid : continuousStep ν f t-continuousStep ν f s =
      (∫ x in 0..s, Ft x-Fs x) + ∫ x in s..t, Ft x := by
    rw [intervalIntegral.integral_sub hi0 his]
    change (∫ x in 0..t, Ft x) - (∫ x in 0..s, Fs x) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
    ring
  have hB := hf.bound_nonneg
  have hD := hf.lip_nonneg
  have hη : 0 ≤ η := hs.1.trans hs.2
  have hE := (kernelBound_pos η R).le
  have hover : ‖∫ x in 0..s, Ft x-Fs x‖ ≤ D*(t-s)*kernelBound η R*η := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := D*(t-s)*kernelBound η R) ?_).trans
    · rw [sub_zero,abs_of_nonneg hs.1]
      exact mul_le_mul_of_nonneg_left hs.2 (by positivity)
    · intro x hx
      rw [uIoc_of_le hs.1] at hx
      have htx : t-x ∈ Icc 0 η := ⟨by linarith [hx.2],by linarith [hx.1,ht.2]⟩
      have hsx : s-x ∈ Icc 0 η := ⟨by linarith [hx.2],by linarith [hx.1,hs.2]⟩
      have hxy : |(t-x)-(s-x)| = t-s := by
        rw [show (t-x)-(s-x) = t-s by ring,abs_of_nonneg (sub_nonneg.mpr hst)]
      change ‖f (t-x)*expKernel ν x-f (s-x)*expKernel ν x‖ ≤ _
      rw [← sub_mul,norm_mul]
      have hh := hf.norm_sub_le _ htx _ hsx
      rw [hxy] at hh
      exact mul_le_mul hh (expKernel_norm hR hν ⟨hx.1.le,hx.2.trans hs.2⟩)
        (norm_nonneg _) (by positivity)
  have htail : ‖∫ x in s..t, Ft x‖ ≤ B*kernelBound η R*(t-s) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := B*kernelBound η R) ?_).trans_eq
      (by rw [abs_of_nonneg (sub_nonneg.mpr hst)])
    intro x hx
    rw [uIoc_of_le hst] at hx
    exact hr.norm_le _ ⟨hs.1.trans hx.1.le,hx.2⟩
  rw [hid]
  exact (norm_add_le _ _).trans ((add_le_add hover htail).trans_eq (by ring))

theorem continuousStep_regular {η R B D : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hη : 0 ≤ η) (hR : 0 ≤ R)
    {ν : ℂ} (hν : ‖ν‖ ≤ R) :
    RegularProfile η (continuousStep ν f) (B*kernelBound η R*η)
      (kernelBound η R*(B+D*η)) := by
  have hB := hf.bound_nonneg
  have hD := hf.lip_nonneg
  have hE := (kernelBound_pos η R).le
  apply regularProfile_of_bounds (by positivity) (by positivity)
  · exact fun t ht => continuousStep_norm hf hR hν ht
  · intro s hs t ht
    rcases le_total s t with hst | hts
    · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hst)]
      simpa only [neg_sub] using continuousStep_norm_sub_of_le hf hR hν hs ht hst
    · rw [abs_of_nonneg (sub_nonneg.mpr hts)]
      exact continuousStep_norm_sub_of_le hf hR hν ht hs hts

theorem discreteStep_stability {η R L A : ℝ} {f g : ℝ → ℂ}
    (hL : 0 < L) (hR : 0 ≤ R) (hA : 0 ≤ A) {ν : ℂ} (hν : ‖ν‖ ≤ R)
    (hfg : ∀ x ∈ Icc 0 η, ‖f x-g x‖ ≤ A) {t : ℝ} (ht : t ∈ Icc 0 η) :
    ‖discreteStep L ν f t-discreteStep L ν g t‖ ≤
      A*kernelBound η R*(η+1/L) := by
  have hid : discreteStep L ν f t-discreteStep L ν g t =
      strictHarmonicQuadrature L t (fun x => (f (t-x)-g (t-x))*expKernel ν x) := by
    unfold discreteStep strictHarmonicQuadrature
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring
  rw [hid]
  have hE := (kernelBound_pos η R).le
  apply (strictHarmonicQuadrature_norm hL ht.1 (by positivity : 0 ≤ A*kernelBound η R) ?_).trans
  · exact mul_le_mul_of_nonneg_left (by linarith [ht.2]) (by positivity)
  · intro x hx
    rw [norm_mul]
    exact mul_le_mul (hfg (t-x) ⟨by linarith [hx.2],by linarith [hx.1,ht.2]⟩)
      (expKernel_norm hR hν ⟨hx.1,hx.2.trans ht.2⟩) (norm_nonneg _) hA

end
end Sechstmoment.Source.NoDPHarmonic
