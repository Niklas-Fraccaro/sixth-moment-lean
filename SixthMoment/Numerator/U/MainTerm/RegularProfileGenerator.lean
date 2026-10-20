import Mathlib.MeasureTheory.Integral.Prod
import SixthMoment.Arithmetic.Factor.Definitions
import SixthMoment.Numerator.Kernels.Holomorphy
import SixthMoment.Numerator.Kernels.ReflectionGenerator


namespace SixthMoment
open Complex MeasureTheory Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

def actualRegularProfileKernel (σ : Fin 4 → ℂ) (A B : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..min A B,
    exponentialAlternantRegularized (polarSourceKnots σ)
      (numeratorRho (A-t) (B-t))

def actualRegularProfileGenerator (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (σ : Fin 4 → ℂ) : ℂ :=
  (arithmeticFactor:ℂ) * (∫ x, (Φ x:ℂ)) *
    ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
      f A * g B * actualRegularProfileKernel σ A B

theorem actualRegularProfileKernel_eq_raw_of_injective
    (σ : Fin 4 → ℂ) (hσ : Function.Injective (polarSourceKnots σ)) (A B : ℝ) :
    actualRegularProfileKernel σ A B =
      ∫ t in (0:ℝ)..min A B,
        exponentialAlternant (polarSourceKnots σ) (numeratorRho (A-t) (B-t)) := by
  unfold actualRegularProfileKernel
  simp_rw [exponentialAlternantRegularized_eq_raw _ _ hσ]

theorem actualRegularProfileGenerator_eq_raw_of_injective
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (σ : Fin 4 → ℂ) (hσ : Function.Injective (polarSourceKnots σ)) :
    actualRegularProfileGenerator a b f g Φ σ =
      (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
        ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b, f A*g B*
          (∫ t in (0:ℝ)..min A B,
            exponentialAlternant (polarSourceKnots σ) (numeratorRho (A-t) (B-t))) := by
  unfold actualRegularProfileGenerator
  simp_rw [actualRegularProfileKernel_eq_raw_of_injective _ hσ]

theorem actualRegularProfileKernel_continuous_joint :
    Continuous (fun p : (Fin 4 → ℂ) × (ℝ × ℝ) =>
      actualRegularProfileKernel p.1 p.2.1 p.2.2) := by
  unfold actualRegularProfileKernel
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact exponentialAlternantRegularized_continuous_joint.comp
      (by unfold polarSourceKnots numeratorRho; fun_prop : Continuous (fun p : ((Fin 4 → ℂ) × (ℝ × ℝ)) × ℝ =>
        (polarSourceKnots p.1.1, numeratorRho (p.1.2.1-p.2) (p.1.2.2-p.2))))
  · fun_prop

theorem actualRegularProfileKernel_rescale (σ : Fin 4 → ℂ) (A B : ℝ) :
    actualRegularProfileKernel σ A B = ((min A B:ℝ):ℂ) *
      ∫ s in (0:ℝ)..1,
        exponentialAlternantRegularized (polarSourceKnots σ)
          (numeratorRho (A-min A B*s) (B-min A B*s)) := by
  symm
  simpa only [actualRegularProfileKernel, Complex.real_smul, mul_zero, mul_one] using
    intervalIntegral.smul_integral_comp_mul_left
      (fun t => exponentialAlternantRegularized (polarSourceKnots σ)
        (numeratorRho (A-t) (B-t))) (a := (0:ℝ)) (b := 1) (min A B)

theorem actualRegularProfileGenerator_continuous
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (actualRegularProfileGenerator a b f g Φ) := by
  unfold actualRegularProfileGenerator
  apply Continuous.const_mul
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact ((hf.comp (by fun_prop : Continuous
    (fun p : ((Fin 4 → ℂ) × ℝ) × ℝ => p.1.2))).mul
      (hg.comp continuous_snd)).mul
    (actualRegularProfileKernel_continuous_joint.comp
      (by fun_prop : Continuous (fun p : ((Fin 4 → ℂ) × ℝ) × ℝ =>
        (p.1.1,(p.1.2,p.2)))))

private def actualRegularAlternantFamily :
    ComplexIntegralFamily (univ : Set (Fin 4 → ℂ)) ((ℝ × ℝ) × ℝ) :=
  ComplexIntegralFamily.ofContDiff
    (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) =>
      exponentialAlternantRegularized (polarSourceKnots p.1) p.2)
    (exponentialAlternantRegularized_contDiff_joint.comp
      (by
        apply ContDiff.prodMk
        · apply contDiff_pi.mpr
          intro j
          fin_cases j <;> norm_num [polarSourceKnots] <;> fun_prop
        · fun_prop
        : ContDiff ℂ 1
        (fun p : (Fin 4 → ℂ) × (Fin 4 → ℂ) => (polarSourceKnots p.1,p.2))))
    (fun p : (ℝ × ℝ) × ℝ => numeratorRho (p.1.1-p.2) (p.1.2-p.2))
    (by unfold numeratorRho; fun_prop)

private def actualRegularProfileKernelFamily :
    ComplexIntegralFamily (univ : Set (Fin 4 → ℂ)) (ℝ × ℝ) :=
  actualRegularAlternantFamily.variableIntervalIntegral (fun _ => 0)
    (fun p => min p.1 p.2) continuous_const (by fun_prop)

private theorem actualRegularProfileKernelFamily_value (σ : Fin 4 → ℂ) (A B : ℝ) :
    actualRegularProfileKernelFamily.value σ (A,B) = actualRegularProfileKernel σ A B := by
  unfold actualRegularProfileKernelFamily
  rw [ComplexIntegralFamily.variableIntervalIntegral_value]
  rfl

private def actualRegularProfileFamily (a b : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) :
    ComplexIntegralFamily (univ : Set (Fin 4 → ℂ)) Unit :=
  ((((actualRegularProfileKernelFamily.mulAux (fun p => f p.1*g p.2)
      ((hf.comp continuous_fst).mul (hg.comp continuous_snd))).variableIntervalIntegral
        (fun _ => 0) (fun _ => b) continuous_const continuous_const).reindexAux
          (fun p : Unit × ℝ => p.2) continuous_snd).variableIntervalIntegral
            (fun _ => 0) (fun _ => a) continuous_const continuous_const)

private theorem actualRegularProfileFamily_value (a b : ℝ) (f g : ℝ → ℂ)
    (hf : Continuous f) (hg : Continuous g) (σ : Fin 4 → ℂ) :
    (actualRegularProfileFamily a b f g hf hg).value σ () =
      ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
        f A*g B*actualRegularProfileKernel σ A B := by
  unfold actualRegularProfileFamily
  rw [ComplexIntegralFamily.variableIntervalIntegral_value]
  change (∫ A in (0:ℝ)..a,
    ((actualRegularProfileKernelFamily.mulAux (fun p => f p.1*g p.2)
      ((hf.comp continuous_fst).mul (hg.comp continuous_snd))).variableIntervalIntegral
        (fun _ => 0) (fun _ => b) continuous_const continuous_const).value σ A) = _
  simp_rw [ComplexIntegralFamily.variableIntervalIntegral_value]
  change (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
    f A*g B*actualRegularProfileKernelFamily.value σ (A,B)) = _
  simp_rw [actualRegularProfileKernelFamily_value]

theorem actualRegularProfileGenerator_contDiff
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    ContDiff ℂ 1 (actualRegularProfileGenerator a b f g Φ) := by
  have h := ((actualRegularProfileFamily a b f g hf hg).mulAux
    (fun _ => ((arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ)))) continuous_const).contDiff_value ()
  change ContDiff ℂ 1 (fun σ =>
    ((arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ)))*
      (actualRegularProfileFamily a b f g hf hg).value σ ()) at h
  have heq : (fun σ => ((arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ)))*
      (actualRegularProfileFamily a b f g hf hg).value σ ()) =
      actualRegularProfileGenerator a b f g Φ := by
    funext σ
    rw [actualRegularProfileFamily_value]
    rfl
  rw [heq] at h
  exact h

theorem actualRegularProfileGenerator_differentiable
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Differentiable ℂ (actualRegularProfileGenerator a b f g Φ) :=
  (actualRegularProfileGenerator_contDiff a b f g Φ hf hg).differentiable (by norm_num)

theorem actualRegularProfileKernel_centered_u_slice (A B : ℝ) (z : ℂ) :
    Complex.exp (z/2)*actualRegularProfileKernel (![0,0,z,0]) B A =
      numeratorExpGenerator A B z := by
  have hknots : polarSourceKnots (![0,0,z,0] : Fin 4 → ℂ) = ![0,0,z,0] := by
    funext j
    fin_cases j <;> simp [polarSourceKnots]
  unfold actualRegularProfileKernel numeratorExpGenerator
  simp_rw [hknots, min_comm B A]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  change Complex.exp (z/2)*
    exponentialAlternantRegularized ![0,0,z,0] (numeratorRho (B-t) (A-t)) =
      (numeratorP (B-t) (A-t):ℂ)*simplexExpGenerator (numeratorExpNodes A B t) z
  rw [numeratorRho_regularized_u_slice]
  have hnodes : (fun j => numeratorRho (B-t) (A-t) j+(1/2:ℂ)) =
      numeratorExpNodes A B t := by
    funext j
    fin_cases j <;> norm_num [numeratorRho, numeratorExpNodes] <;> ring
  have htrans := simplexExpGenerator_translate (numeratorRho (B-t) (A-t)) z (1/2)
  rw [hnodes] at htrans
  have he : z*(1/2:ℂ) = z/2 := by ring
  rw [he] at htrans
  rw [htrans]
  ring

theorem actualRegularProfileGenerator_swap_integrals
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (σ : Fin 4 → ℂ) :
    actualRegularProfileGenerator b a g f Φ σ =
      (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
        ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
          f A*g B*actualRegularProfileKernel σ B A := by
  unfold actualRegularProfileGenerator
  congr 1
  have hc : Continuous (fun p : ℝ × ℝ =>
      g p.1*f p.2*actualRegularProfileKernel σ p.1 p.2) :=
    ((hg.comp continuous_fst).mul (hf.comp continuous_snd)).mul
      (actualRegularProfileKernel_continuous_joint.comp
        (by fun_prop : Continuous (fun p : ℝ × ℝ => (σ,p))))
  have hi : IntegrableOn (fun p : ℝ × ℝ =>
      g p.1*f p.2*actualRegularProfileKernel σ p.1 p.2)
        (uIoc (0:ℝ) b ×ˢ uIoc (0:ℝ) a) :=
    (hc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
      (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
  have hi' : IntegrableOn
      (Function.uncurry (fun B A => g B*f A*actualRegularProfileKernel σ B A))
      (uIoc (0:ℝ) b ×ˢ uIoc (0:ℝ) a) := hi
  rw [intervalIntegral_intervalIntegral_swap
    (F := fun B A => g B*f A*actualRegularProfileKernel σ B A) hi']
  congr 1
  funext A
  congr 1
  funext B
  rw [mul_comm (g B) (f A)]

theorem actualRegularProfileGenerator_centered_u_slice
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (z : ℂ) :
    Complex.exp (z/2)*actualRegularProfileGenerator b a g f Φ (![0,0,z,0]) =
      (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
        ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
          f A*g B*numeratorExpGenerator A B z := by
  rw [actualRegularProfileGenerator_swap_integrals a b f g Φ hf hg]
  have hi : Complex.exp (z/2)*
      (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
        f A*g B*actualRegularProfileKernel (![0,0,z,0]) B A) =
      ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
        f A*g B*numeratorExpGenerator A B z := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro A _
    change Complex.exp (z/2)*
      (∫ B in (0:ℝ)..b, f A*g B*actualRegularProfileKernel (![0,0,z,0]) B A) =
        ∫ B in (0:ℝ)..b, f A*g B*numeratorExpGenerator A B z
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro B _
    change Complex.exp (z/2)*(f A*g B*actualRegularProfileKernel (![0,0,z,0]) B A) =
      f A*g B*numeratorExpGenerator A B z
    rw [← actualRegularProfileKernel_centered_u_slice]
    ring
  calc
    _ = ((arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ)))*
        (Complex.exp (z/2)*
          (∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
            f A*g B*actualRegularProfileKernel (![0,0,z,0]) B A)) := by ring
    _ = _ := by rw [hi]

def actualCenteredNumeratorProfileGenerator (a b : ℝ) (f g : ℝ → ℂ)
    (Φ : ℝ → ℝ) (z : ℂ) : ℂ :=
  (arithmeticFactor:ℂ)*(∫ x, (Φ x:ℂ))*
    ∫ A in (0:ℝ)..a, ∫ B in (0:ℝ)..b,
      f A*g B*numeratorExpGenerator A B z

theorem actualCenteredNumeratorProfileGenerator_eq_regular_u_slice
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) (z : ℂ) :
    actualCenteredNumeratorProfileGenerator a b f g Φ z =
      Complex.exp (z/2)*actualRegularProfileGenerator b a g f Φ (![0,0,z,0]) :=
  (actualRegularProfileGenerator_centered_u_slice a b f g Φ hf hg z).symm

theorem actualCenteredNumeratorProfileGenerator_differentiable
    (a b : ℝ) (f g : ℝ → ℂ) (Φ : ℝ → ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Differentiable ℂ (actualCenteredNumeratorProfileGenerator a b f g Φ) := by
  have heq : actualCenteredNumeratorProfileGenerator a b f g Φ =
      fun z => Complex.exp (z/2)*
        actualRegularProfileGenerator b a g f Φ (![0,0,z,0]) :=
    funext (actualCenteredNumeratorProfileGenerator_eq_regular_u_slice a b f g Φ hf hg)
  rw [heq]
  exact (by fun_prop : Differentiable ℂ (fun z : ℂ => Complex.exp (z/2))).mul
    ((actualRegularProfileGenerator_differentiable b a g f Φ hg hf).comp
      (by
        apply differentiable_pi.mpr
        intro j
        fin_cases j <;> norm_num
        : Differentiable ℂ (fun z : ℂ => (![0,0,z,0] : Fin 4 → ℂ))))

end
end SixthMoment
