import SixthMoment.Numerator.Shared.MomentHolomorphy

namespace SixthMoment
open Complex Metric MeasureTheory Set
open scoped BigOperators Topology ComplexConjugate
noncomputable section
set_option maxHeartbeats 1000000

def twistedMomentAmplitude (T : ℝ) (f g Φ : ℝ→ℝ) (t : ℝ) : ℂ :=
  (Φ (t/T):ℂ)*profileDirichletSum T f (criticalLinePoint t)*
    profileDirichletSum T g (1-criticalLinePoint t)

theorem twistedMomentAmplitude_continuous {T : ℝ} (hT : 1<T)
    (a b : ℝ) (f g Φ : ℝ→ℝ)
    (hf : ∀x,a<x→f x=0) (hg : ∀x,b<x→g x=0) (hΦ : Continuous Φ) :
    Continuous (twistedMomentAmplitude T f g Φ) := by
  have hsplus : Continuous (fun t:ℝ=>criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  have hsminus : Continuous (fun t:ℝ=>1-criticalLinePoint t) := by
    unfold criticalLinePoint
    fun_prop
  exact ((by fun_prop : Continuous (fun t:ℝ=>(Φ (t/T):ℂ))).mul
    ((profileDirichletSum_continuous hT a f hf).comp hsplus)).mul
    ((profileDirichletSum_continuous hT b g hg).comp hsminus)

noncomputable def twistedMomentFamily {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : Continuous Φ) :
    ComplexIntegralFamily momentRawShiftDomain Unit :=
  ((shiftedFourthFamily.mulAux (twistedMomentAmplitude T f g Φ)
    (twistedMomentAmplitude_continuous hT a b f g Φ hf hg hΦ)).reindexAux
      (fun p : Unit × ℝ => p.2) continuous_snd).intervalIntegral
        momentRawShiftDomain_isOpen T (2*T) (by linarith)

theorem twistedFourthMoment_eq_interval {T : ℝ} (hT : 0 < T)
    (α : MomentShifts) (f g Φ : ℝ → ℝ) (hΦ : tsupport Φ ⊆ Icc 1 2) :
    twistedFourthMoment T α f g Φ =
      ∫ t in T..2*T, twistedFourthIntegrand T t α f g Φ := by
  unfold twistedFourthMoment
  rw [intervalIntegral.integral_of_le (by linarith : T ≤ 2*T),← integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_integral_of_forall_compl_eq_zero ?_).symm
  intro t ht
  have hx : t/T ∉ Icc (1:ℝ) 2 := by
    intro hx
    apply ht
    constructor
    · have h := (le_div_iff₀ hT).mp hx.1
      linarith
    · have h := (div_le_iff₀ hT).mp hx.2
      linarith
  have hzero : Φ (t/T)=0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hΦ h))
  simp only [twistedFourthIntegrand,hzero,Complex.ofReal_zero,zero_mul]

theorem twistedMomentFamily_value {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ)
    (α : MomentShifts) :
    (twistedMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).value α () =
      twistedFourthMoment T α f g Φ := by
  rw [twistedFourthMoment_eq_interval (zero_lt_one.trans hT) α f g Φ hΦ.2]
  change (∫ t in T..2*T, twistedMomentAmplitude T f g Φ t*shiftedFourthExtended (α,(t:ℂ))) = _
  apply intervalIntegral.integral_congr
  intro t _
  unfold twistedMomentAmplitude shiftedFourthExtended twistedFourthIntegrand shiftedFourthProduct
    criticalLinePoint
  ring

attribute [irreducible] twistedMomentFamily

theorem twistedFourthMoment_differentiableOn_raw {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun α => twistedFourthMoment T α f g Φ) momentRawShiftDomain := by
  intro α hα
  have h := ((twistedMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).hasFDerivAt α hα ()).differentiableAt
  have heq : (fun α => (twistedMomentFamily hT a b f g Φ hf hg hΦ.1.continuous).value α ()) =
      (fun α => twistedFourthMoment T α f g Φ) :=
    funext (fun α => twistedMomentFamily_value hT a b f g Φ hf hg hΦ α)
  rw [heq] at h
  exact h.differentiableWithinAt

theorem twistedFourthMoment_differentiableOn_normalized {T : ℝ} (hT : 1 < T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => twistedFourthMoment T (rawMomentShifts T σ) f g Φ)
      (momentNormalizedShiftDomain T) :=
  (twistedFourthMoment_differentiableOn_raw hT a b f g Φ hf hg hΦ).comp
    (rawMomentShifts_differentiable T).differentiableOn (fun _ h => h)

theorem twistedFourthMoment_differentiableOn_polydisc {T : ℝ} (hT : 1 < T)
    (R : Fin 4 → ℝ) (hR : ∀ j, 2*R j < Real.log T)
    (a b : ℝ) (f g Φ : ℝ → ℝ)
    (hf : ∀ x, a < x → f x=0) (hg : ∀ x, b < x → g x=0) (hΦ : SmoothDyadicWeight Φ) :
    DifferentiableOn ℂ (fun σ => twistedFourthMoment T (rawMomentShifts T σ) f g Φ)
      (rectangularClosedPolydisc R) :=
  (twistedFourthMoment_differentiableOn_normalized hT a b f g Φ hf hg hΦ).mono
    (closedPolydisc_subset_momentNormalizedShiftDomain hT R hR)

def twistedConjugateSwapShifts (α : MomentShifts) : MomentShifts :=
  ![conj (α 2),conj (α 3),conj (α 0),conj (α 1)]

theorem twistedFourthIntegrand_conj_swap (T t : ℝ) (α : MomentShifts)
    (f g Φ : ℝ→ℝ) :
    conj (twistedFourthIntegrand T t α f g Φ) =
      twistedFourthIntegrand T t (twistedConjugateSwapShifts α) g f Φ := by
  have hcs : conj (criticalLinePoint t) = 1-criticalLinePoint t :=
    (criticalLinePoint_one_sub t).symm
  have hcms : conj (1-criticalLinePoint t) = criticalLinePoint t := by
    rw [criticalLinePoint_one_sub]
    change conj (conj _) = _
    exact conj_conj _
  have hp (j : Fin 4) : conj (riemannZeta (criticalLinePoint t+α j)) =
      riemannZeta (1-criticalLinePoint t+conj (α j)) := by
    rw [←riemannZeta_conj,map_add,hcs]
  have hm (j : Fin 4) : conj (riemannZeta (1-criticalLinePoint t+α j)) =
      riemannZeta (criticalLinePoint t+conj (α j)) := by
    rw [←riemannZeta_conj,map_add,hcms]
  have hf : conj (profileDirichletSum T f (criticalLinePoint t)) =
      profileDirichletSum T f (1-criticalLinePoint t) := by
    rw [←profileDirichletSum_conj,hcs]
  have hg : conj (profileDirichletSum T g (1-criticalLinePoint t)) =
      profileDirichletSum T g (criticalLinePoint t) := by
    rw [←profileDirichletSum_conj,hcms]
  simp only [twistedFourthIntegrand,shiftedFourthProduct,map_mul,conj_ofReal,
    hp,hm,hf,hg]
  simp [twistedConjugateSwapShifts]
  ring

theorem twistedFourthMoment_conj_swap (T : ℝ) (α : MomentShifts)
    (f g Φ : ℝ→ℝ) :
    conj (twistedFourthMoment T α f g Φ) =
      twistedFourthMoment T (twistedConjugateSwapShifts α) g f Φ := by
  unfold twistedFourthMoment
  rw [←integral_conj]
  simp_rw [twistedFourthIntegrand_conj_swap]

end
end SixthMoment
