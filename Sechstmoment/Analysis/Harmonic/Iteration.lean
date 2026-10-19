import Sechstmoment.Analysis.Harmonic.Volterra

/-! Iterating the harmonic quadrature on a simplex. The constants depend only
on the support, the shift bound, and the initial profile bounds. -/

namespace Sechstmoment.Source.NoDPHarmonic
open Real Complex MeasureTheory Set
open scoped BigOperators Topology
noncomputable section

def continuousIter : List ℂ → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | ν::νs, f => continuousStep ν (continuousIter νs f)

def discreteIter (L : ℝ) : List ℂ → (ℝ → ℂ) → ℝ → ℂ
  | [], f => f
  | ν::νs, f => discreteStep L ν (discreteIter L νs f)

def iterBounds (η R B D : ℝ) : ℕ → ℝ × ℝ
  | 0 => (B,D)
  | n+1 => let b := iterBounds η R B D n
    (b.1*kernelBound η R*η, kernelBound η R*(b.1+b.2*η))

def iterError (η R B D : ℝ) : ℕ → ℝ
  | 0 => 0
  | n+1 => iterError η R B D n*kernelBound η R*(η+1) +
      stepError η R (iterBounds η R B D n).1 (iterBounds η R B D n).2

theorem iterBounds_nonneg {η R B D : ℝ} (hη : 0 ≤ η) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (n : ℕ) : 0 ≤ (iterBounds η R B D n).1 ∧ 0 ≤ (iterBounds η R B D n).2 := by
  induction n with
  | zero => exact ⟨hB,hD⟩
  | succ n ih =>
    obtain ⟨hb,hd⟩ := ih
    have hE := (kernelBound_pos η R).le
    change 0 ≤ (iterBounds η R B D n).1*kernelBound η R*η ∧
      0 ≤ kernelBound η R*((iterBounds η R B D n).1+(iterBounds η R B D n).2*η)
    constructor <;> positivity

theorem iterError_nonneg {η R B D : ℝ} (hη : 0 ≤ η) (hR : 0 ≤ R)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (n : ℕ) : 0 ≤ iterError η R B D n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    have hb := iterBounds_nonneg (R := R) hη hB hD n
    have he := stepError_nonneg hη hR hb.1 hb.2
    have hE := (kernelBound_pos η R).le
    change 0 ≤ iterError η R B D n*kernelBound η R*(η+1)+_
    positivity

theorem continuousIter_regular {η R B D : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hη : 0 ≤ η) (hR : 0 ≤ R)
    (νs : List ℂ) (hν : ∀ ν ∈ νs, ‖ν‖ ≤ R) :
    RegularProfile η (continuousIter νs f)
      (iterBounds η R B D νs.length).1 (iterBounds η R B D νs.length).2 := by
  induction νs with
  | nil => exact hf
  | cons ν νs ih =>
    exact continuousStep_regular (ih (fun z hz => hν z (List.mem_cons_of_mem _ hz)))
      hη hR (hν ν (List.mem_cons_self))

theorem discreteIter_error {η R B D L : ℝ} {f : ℝ → ℂ}
    (hf : RegularProfile η f B D) (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (νs : List ℂ) (hν : ∀ ν ∈ νs, ‖ν‖ ≤ R) {t : ℝ} (ht : t ∈ Icc 0 η) :
    ‖discreteIter L νs f t-continuousIter νs f t‖ ≤ iterError η R B D νs.length/L := by
  have hL0 : 0 < L := by linarith
  have hLinv : 1/L ≤ 1 := (div_le_one hL0).mpr hL
  induction νs generalizing t with
  | nil => simp only [discreteIter,continuousIter,sub_self,norm_zero,List.length_nil,iterError,zero_div,le_refl]
  | cons ν νs ih =>
    have hνs : ∀ z ∈ νs, ‖z‖ ≤ R := fun z hz => hν z (List.mem_cons_of_mem _ hz)
    have hν0 : ‖ν‖ ≤ R := hν ν (List.mem_cons_self)
    have hr := continuousIter_regular hf hη hR νs hνs
    have hC := iterError_nonneg hη hR hf.bound_nonneg hf.lip_nonneg νs.length
    have hE := (kernelBound_pos η R).le
    have hs := discreteStep_stability hL0 hR (div_nonneg hC hL0.le) hν0
      (fun x hx => ih hνs hx) ht
    have he := discreteStep_error hr hL0 hR hν0 ht
    have htri := norm_add_le
      (discreteStep L ν (discreteIter L νs f) t-discreteStep L ν (continuousIter νs f) t)
      (discreteStep L ν (continuousIter νs f) t-continuousStep ν (continuousIter νs f) t)
    rw [sub_add_sub_cancel] at htri
    apply htri.trans
    apply (add_le_add hs he).trans
    change iterError η R B D νs.length/L*kernelBound η R*(η+1/L)+_ ≤
      (iterError η R B D νs.length*kernelBound η R*(η+1)+_)/L
    calc
      _ ≤ iterError η R B D νs.length/L*kernelBound η R*(η+1) +
          stepError η R (iterBounds η R B D νs.length).1 (iterBounds η R B D νs.length).2/L := by
        gcongr
      _ = _ := by ring

theorem discreteIter_norm {η R B L : ℝ} {f : ℝ → ℂ}
    (hB : 0 ≤ B) (hf : ∀ x ∈ Icc 0 η, ‖f x‖ ≤ B)
    (hη : 0 ≤ η) (hR : 0 ≤ R) (hL : 1 ≤ L)
    (νs : List ℂ) (hν : ∀ ν ∈ νs, ‖ν‖ ≤ R) {t : ℝ} (ht : t ∈ Icc 0 η) :
    ‖discreteIter L νs f t‖ ≤ B*(kernelBound η R*(η+1))^νs.length := by
  have hL0 : 0 < L := by linarith
  have hLinv : 1/L ≤ 1 := (div_le_one hL0).mpr hL
  have hE := (kernelBound_pos η R).le
  induction νs generalizing t with
  | nil => simpa only [discreteIter,List.length_nil,pow_zero,mul_one] using hf t ht
  | cons ν νs ih =>
    have hνs : ∀ z ∈ νs, ‖z‖ ≤ R := fun z hz => hν z (List.mem_cons_of_mem _ hz)
    have hbound (x : ℝ) (hx : x ∈ Icc 0 t) :
        ‖discreteIter L νs f (t-x)*expKernel ν x‖ ≤
          (B*(kernelBound η R*(η+1))^νs.length)*kernelBound η R := by
      rw [norm_mul]
      exact mul_le_mul (ih hνs ⟨by linarith [hx.2],by linarith [hx.1,ht.2]⟩)
        (expKernel_norm hR (hν ν (List.mem_cons_self)) ⟨hx.1,hx.2.trans ht.2⟩)
        (norm_nonneg _) (by positivity)
    apply (strictHarmonicQuadrature_norm hL0 ht.1 (by positivity) hbound).trans
    change _ ≤ B*(kernelBound η R*(η+1))^(νs.length+1)
    rw [pow_succ]
    calc
      _ ≤ (B*(kernelBound η R*(η+1))^νs.length)*kernelBound η R*(η+1) := by
        gcongr
        exact ht.2
      _ = _ := by ring

end
end Sechstmoment.Source.NoDPHarmonic
