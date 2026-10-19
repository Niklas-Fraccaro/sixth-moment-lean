import Mathlib.Tactic
import Sechstmoment.Arithmetic.Euler.Shifted.Bounded
import Sechstmoment.Arithmetic.Euler.Shifted.Holomorphic
import Sechstmoment.Numerator.Polar.PureHorizontal

/-!
# The literal arithmetic and five entangled factors on the Mellin strip

The triples retain the actual amplifier variables and the four source shifts.
Both the genuine Euler rest and all five entangled zeta factors have bounds
independent of every imaginary contour coordinate. The four remaining pure
factors are controlled separately by the actual pole-killing Gaussian.
-/

namespace Sechstmoment

open Real Complex MeasureTheory Filter Set
open scoped BigOperators Topology

noncomputable section

def polarMellinLeftTriple (α : MomentShifts) (u z : ℂ) : Fin 3 → ℂ :=
  ![u,z+α 0,z+α 1]

def polarMellinRightTriple (α : MomentShifts) (v z : ℂ) : Fin 3 → ℂ :=
  ![v,z+α 2,z+α 3]

def polarEntangledZetaArguments (α : MomentShifts) (u v z : ℂ) : Fin 5 → ℂ :=
  ![1+u+v,1+u+z+α 2,1+u+z+α 3,1+v+z+α 0,1+v+z+α 1]

def polarEntangledZetaProduct (α : MomentShifts) (u v z : ℂ) : ℂ :=
  ∏ i : Fin 5, riemannZeta (polarEntangledZetaArguments α u v z i)

def polarArithmeticEntangledFactor (α : MomentShifts) (u v z : ℂ) : ℂ :=
  shiftedPolarEulerRest (polarMellinLeftTriple α u z) (polarMellinRightTriple α v z)*
    polarEntangledZetaProduct α u v z

def polarArithmeticEntangledMajorant (δ : ℝ) : ℝ :=
  Real.exp (∑' p : {n : ℕ // Nat.Prime n}, shiftedPolarPrimeUniformMajorant δ p)*
    (zetaDirichletMajorant (1+δ/4))^5

theorem polarArithmeticEntangledMajorant_nonneg (δ : ℝ) :
    0 ≤ polarArithmeticEntangledMajorant δ := by
  unfold polarArithmeticEntangledMajorant
  exact mul_nonneg (Real.exp_pos _).le
    (pow_nonneg (zetaDirichletMajorant_nonneg _) _)

theorem polarMellinTriples_re_lower_bound {α : MomentShifts} {δ : ℝ} {u v z : ℂ}
    (hδ : 0 < δ) (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hz : -δ/2 ≤ z.re) :
    (∀ i : Fin 3, -δ < (polarMellinLeftTriple α u z i).re) ∧
    (∀ i : Fin 3, -δ < (polarMellinRightTriple α v z i).re) := by
  have hre (j : Fin 4) : -(δ/4) ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  constructor <;> intro i <;> fin_cases i <;>
    simp [polarMellinLeftTriple, polarMellinRightTriple] <;>
    linarith [hre 0,hre 1,hre 2,hre 3]

theorem polarEntangledZetaArguments_re_lower_bound {α : MomentShifts}
    {δ : ℝ} {u v z : ℂ} (hδ : 0 < δ)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hz : -δ/2 ≤ z.re) (i : Fin 5) :
    1+δ/4 ≤ (polarEntangledZetaArguments α u v z i).re := by
  have hre (j : Fin 4) : -(δ/4) ≤ (α j).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans (hα j))).1
  fin_cases i <;>
    simp [polarEntangledZetaArguments, add_re] <;>
    linarith [hre 0,hre 1,hre 2,hre 3]

theorem polarArithmeticEntangledFactor_norm_bound {α : MomentShifts}
    {δ : ℝ} {u v z : ℂ} (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hz : -δ/2 ≤ z.re) :
    ‖polarArithmeticEntangledFactor α u v z‖ ≤
      polarArithmeticEntangledMajorant δ := by
  obtain ⟨ha,hb⟩ := polarMellinTriples_re_lower_bound hδ hα hu hv hz
  have hA := shiftedPolarEulerRest_norm_uniform_bound _ _ hδ1
    (fun i => (ha i).le) (fun i => (hb i).le)
  have hZ := finiteRiemannZetaProduct_norm_le_dirichlet Finset.univ
    (polarEntangledZetaArguments α u v z) (by linarith : 1 < 1+δ/4)
    (fun i _ => polarEntangledZetaArguments_re_lower_bound hδ hα hu hv hz i)
  simp only [Finset.card_univ, Fintype.card_fin] at hZ
  unfold polarArithmeticEntangledFactor polarArithmeticEntangledMajorant
  rw [norm_mul]
  exact mul_le_mul hA hZ (norm_nonneg _) (Real.exp_pos _).le

theorem polarArithmeticEntangledFactor_vertical_continuous {α : MomentShifts}
    {δ c : ℝ} {u v : ℂ} (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖α j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) (hc : -δ/2 ≤ c) :
    Continuous (fun y : ℝ =>
      polarArithmeticEntangledFactor α u v ((c:ℂ)+(y:ℂ)*I)) := by
  rw [continuous_iff_continuousAt]
  intro y
  let z : ℂ := (c:ℂ)+(y:ℂ)*I
  have hz : -δ/2 ≤ z.re := by simpa [z] using hc
  obtain ⟨ha,hb⟩ := polarMellinTriples_re_lower_bound hδ hα hu hv hz
  have hdomain : (polarMellinLeftTriple α u z,polarMellinRightTriple α v z) ∈
      polarShiftDomain δ := ⟨ha,hb⟩
  have hmap : Continuous (fun y : ℝ =>
      (polarMellinLeftTriple α u ((c:ℂ)+(y:ℂ)*I),
        polarMellinRightTriple α v ((c:ℂ)+(y:ℂ)*I))) := by
    unfold polarMellinLeftTriple polarMellinRightTriple
    fun_prop
  have hA : ContinuousAt (fun y : ℝ =>
      shiftedPolarEulerRest (polarMellinLeftTriple α u ((c:ℂ)+(y:ℂ)*I))
        (polarMellinRightTriple α v ((c:ℂ)+(y:ℂ)*I))) y :=
    ContinuousAt.comp (f := fun y : ℝ =>
      (polarMellinLeftTriple α u ((c:ℂ)+(y:ℂ)*I),
        polarMellinRightTriple α v ((c:ℂ)+(y:ℂ)*I)))
      (g := fun ab : PolarShiftSpace => shiftedPolarEulerRest ab.1 ab.2)
      ((shiftedPolarEulerRest_continuousOn hδ1).continuousAt
        ((polarShiftDomain_isOpen δ).mem_nhds hdomain)) hmap.continuousAt
  have hZ : ContinuousAt (fun y : ℝ =>
      polarEntangledZetaProduct α u v ((c:ℂ)+(y:ℂ)*I)) y := by
    unfold polarEntangledZetaProduct
    apply tendsto_finsetProd
    intro i _
    have hne : polarEntangledZetaArguments α u v z i ≠ 1 := by
      intro he
      have hr := polarEntangledZetaArguments_re_lower_bound hδ hα hu hv hz i
      rw [he,one_re] at hr
      linarith
    have hzi : ContinuousAt (fun y : ℝ =>
        polarEntangledZetaArguments α u v ((c:ℂ)+(y:ℂ)*I) i) y := by
      unfold polarEntangledZetaArguments
      fin_cases i <;> fun_prop
    exact ContinuousAt.comp (f := fun y : ℝ =>
      polarEntangledZetaArguments α u v ((c:ℂ)+(y:ℂ)*I) i) (g := riemannZeta)
      (differentiableAt_riemannZeta hne).continuousAt hzi
  exact hA.mul hZ

def polarMellinArithmeticKernel (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (u v z : ℂ) : ℂ :=
  polarArithmeticEntangledFactor (Source.bblrSixShifts (rawMomentShifts T σ) m) u v z*
    (polarPoleKiller T σ z*purePolarZetaProduct T σ m z)

theorem purePolarZetaProduct_eq_mellin_subproduct
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (u v z : ℂ) :
    purePolarZetaProduct T σ m z =
      ∏ ij : Fin 2 × Fin 2, riemannZeta (1+
        polarMellinLeftTriple (Source.bblrSixShifts (rawMomentShifts T σ) m) u z ij.1.succ+
        polarMellinRightTriple (Source.bblrSixShifts (rawMomentShifts T σ) m) v z ij.2.succ) := by
  unfold purePolarZetaProduct
  apply Finset.prod_congr rfl
  intro ij _
  rw [purePolarZetaArgument_eq_source]
  congr 1
  rcases ij with ⟨i,j⟩
  fin_cases i <;> fin_cases j <;>
    simp [polarMellinLeftTriple,polarMellinRightTriple,purePolarLeft,purePolarRight] <;> ring

theorem polarNineZetaProduct_eq_entangled_mul_pure
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (u v z : ℂ) :
    (∏ ij : Fin 3 × Fin 3, riemannZeta (1+
      polarMellinLeftTriple (Source.bblrSixShifts (rawMomentShifts T σ) m) u z ij.1+
      polarMellinRightTriple (Source.bblrSixShifts (rawMomentShifts T σ) m) v z ij.2)) =
      polarEntangledZetaProduct (Source.bblrSixShifts (rawMomentShifts T σ) m) u v z*
        purePolarZetaProduct T σ m z := by
  rw [purePolarZetaProduct_eq_mellin_subproduct T σ m u v z]
  simp only [Fintype.prod_prod_type,Fin.prod_univ_succ,Fin.prod_univ_zero,
    mul_one]
  simp [polarEntangledZetaProduct,polarEntangledZetaArguments,polarMellinLeftTriple,
    polarMellinRightTriple,Fin.prod_univ_succ,add_assoc]
  ring

theorem purePolarRoot_norm_le_of_rawShifts {T : ℝ} {σ : MomentShifts} {R : ℝ}
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ R) (k : PurePolarIndex) :
    ‖purePolarRoot T σ k‖ ≤ R := by
  unfold purePolarRoot
  rw [norm_div,norm_neg]
  norm_num only [Complex.norm_ofNat]
  have h1 := bblrSixShifts_norm_le (rawMomentShifts T σ) hα k.1 (purePolarLeft k.2.1)
  have h2 := bblrSixShifts_norm_le (rawMomentShifts T σ) hα k.1 (purePolarRight k.2.2)
  have hs := norm_add_le
    (Source.bblrSixShifts (rawMomentShifts T σ) k.1 (purePolarLeft k.2.1))
    (Source.bblrSixShifts (rawMomentShifts T σ) k.1 (purePolarRight k.2.2))
  linarith

theorem polarMellinArithmeticKernel_left_integrable (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) {δ : ℝ} {u v : ℂ} (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    Integrable (fun y : ℝ => polarMellinArithmeticKernel T σ m u v
      ((-δ/2:ℝ)+(y:ℂ)*I)) := by
  have hρ (ij : Fin 2 × Fin 2) : ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (m,ij)
  have hshift (j : Fin 4) :
      ‖Source.bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hcont := polarArithmeticEntangledFactor_vertical_continuous hδ hδ1 hshift hu hv
    (le_refl (-δ/2))
  have hpure := polarPureLeftContour_integrable T σ m hδ (by linarith) hρ
  exact hpure.bdd_mul hcont.aestronglyMeasurable
    (Eventually.of_forall (fun y => polarArithmeticEntangledFactor_norm_bound
      hδ hδ1 hshift hu hv (by simp)))

theorem polarMellinArithmeticKernel_horizontal_bound (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ y : ℝ, M+1 ≤ |y| →
      ∀ u v : ℂ, δ ≤ u.re → δ ≤ v.re → ∀ c ∈ Icc (-δ/2) 1,
        ‖polarMellinArithmeticKernel T σ m u v ((c:ℂ)+(y:ℂ)*I)‖ ≤
          C*(1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2) := by
  have hρ (ij : Fin 2 × Fin 2) : ‖purePolarRoot T σ (m,ij)‖ ≤ δ/4 :=
    purePolarRoot_norm_le_of_rawShifts hα (m,ij)
  obtain ⟨C,M,hC0,hM0,hpure⟩ := polarPureGaussian_horizontal_bound T σ m
    hδ (by linarith) hρ
  refine ⟨polarArithmeticEntangledMajorant δ*C,M,
    mul_nonneg (polarArithmeticEntangledMajorant_nonneg δ) hC0,hM0,?_⟩
  intro y hy u v hu hv c hc
  have hshift (j : Fin 4) :
      ‖Source.bblrSixShifts (rawMomentShifts T σ) m j‖ ≤ δ/4 :=
    bblrSixShifts_norm_le _ hα m j
  have hA := polarArithmeticEntangledFactor_norm_bound hδ hδ1 hshift hu hv
    (show -δ/2 ≤ ((c:ℂ)+(y:ℂ)*I).re by simpa using hc.1)
  unfold polarMellinArithmeticKernel
  rw [norm_mul]
  calc
    _ ≤ polarArithmeticEntangledMajorant δ*
        (C*(1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2)) :=
      mul_le_mul hA (hpure y hy c hc) (norm_nonneg _)
        (polarArithmeticEntangledMajorant_nonneg δ)
    _ = _ := by ac_rfl

theorem polarMellinArithmeticKernel_horizontal_integral_tendsto_zero
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) {δ : ℝ} {u v : ℂ}
    (hδ : 0 < δ) (hδ1 : δ < 1/4)
    (hα : ∀ j : Fin 4, ‖rawMomentShifts T σ j‖ ≤ δ/4)
    (hu : δ ≤ u.re) (hv : δ ≤ v.re) :
    Tendsto (fun y : ℝ => ∫ c in (-δ/2)..1,
      polarMellinArithmeticKernel T σ m u v ((c:ℂ)+(y:ℂ)*I))
      (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C,M,_hC0,_hM0,hbound⟩ :=
    polarMellinArithmeticKernel_horizontal_bound T σ m hδ hδ1 hα
  have hlarge : ∀ᶠ y : ℝ in cocompact ℝ, M+1 ≤ |y| := by
    rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]
    exact (eventually_ge_atTop (M+1)).comap _
  have hnorm : ∀ᶠ y : ℝ in cocompact ℝ,
      ‖∫ c in (-δ/2)..1, polarMellinArithmeticKernel T σ m u v ((c:ℂ)+(y:ℂ)*I)‖ ≤
      (C*|1-(-δ/2)|)*((1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2)) := by
    filter_upwards [hlarge] with y hy
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -δ/2) (b := 1)
      (f := fun c => polarMellinArithmeticKernel T σ m u v ((c:ℂ)+(y:ℂ)*I))
      (C := C*(1+|y|)^48*Real.exp (4*Real.pi*|y|-y^2))
      (by
        intro c hc
        rw [uIoc_of_le (by linarith : -δ/2 ≤ (1:ℝ))] at hc
        exact hbound y hy u v hu hv c ⟨hc.1.le,hc.2⟩)
    exact hb.trans_eq (by ac_rfl)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hlim := (gaussianPolynomialExponential_tendsto_zero 48 (4*Real.pi)).const_mul
    (C*|1-(-δ/2)|)
  simp only [mul_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) hnorm hlim

end

end Sechstmoment
