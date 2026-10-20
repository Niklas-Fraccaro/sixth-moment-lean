import SixthMoment.Numerator.Polar.General.BilinearDP
import SixthMoment.Numerator.V.Asymptotic.CriticalHolomorphy
import SixthMoment.Numerator.V.DP.DPPolydiscBoundary


namespace SixthMoment.Source
open Complex Real Set MeasureTheory
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def noDPRegularMomentLeading (w : ℝ → ℂ) (η : ℝ) (P Q : Polynomial ℝ)
    (σ : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  (arithmeticFactor:ℂ)*(∫ x : ℝ, w x)*Complex.exp (-σ 2-σ 3-z)*
    polarGeneralBilinearGeneratorContour η P Q (fun j => -σ j) 16 16

theorem polarSourceKnots_noDPAllPositiveSigns (σ : Fin 4 → ℂ) :
    polarSourceKnots (noDPAllPositiveSigns σ) = fun j => -σ j := by
  funext j
  fin_cases j <;> simp [polarSourceKnots,noDPAllPositiveSigns]

theorem separatedResidueLeading_eq_regular {η : ℝ} (hη : 0 < η)
    (w : ℝ → ℂ) (P Q : Polynomial ℝ) (σ : Fin 4 → ℂ) (z : ℂ)
    (hσ : Function.Injective σ) (hR : ∀ j, ‖σ j‖ < 16) :
    (2*Real.pi:ℂ)*separatedResidueLeading w η P Q σ z =
      noDPRegularMomentLeading w η P Q σ z := by
  have hi : Function.Injective (polarSourceKnots (noDPAllPositiveSigns σ)) := by
    rw [polarSourceKnots_noDPAllPositiveSigns]
    intro i j hij
    exact hσ (neg_injective hij)
  have hr : ∀ j, ‖polarSourceKnots (noDPAllPositiveSigns σ) j‖ < 16 := by
    simpa only [polarSourceKnots_noDPAllPositiveSigns,norm_neg] using hR
  have hc := polarGeneralBilinearGeneratorContour_eq_dpNormalizedBilinearFourResidues
    hη P Q (noDPAllPositiveSigns σ) 16 16 hi hr hr
  rw [polarSourceKnots_noDPAllPositiveSigns] at hc
  unfold noDPRegularMomentLeading
  rw [hc]
  have h0 : (Finset.univ : Finset (Fin 4)).erase 0 = {1,2,3} := by decide
  have h1 : (Finset.univ : Finset (Fin 4)).erase 1 = {0,2,3} := by decide
  have h2 : (Finset.univ : Finset (Fin 4)).erase 2 = {0,1,3} := by decide
  have h3 : (Finset.univ : Finset (Fin 4)).erase 3 = {0,1,2} := by decide
  let D0 := (σ 1-σ 0)*(σ 0-σ 2)*(σ 0-σ 3)
  let D1 := (σ 0-σ 1)*(σ 1-σ 2)*(σ 1-σ 3)
  let D2 := (σ 1-σ 2)*(σ 0-σ 2)*(σ 3-σ 2)
  let D3 := (σ 1-σ 3)*(σ 2-σ 3)*(σ 0-σ 3)
  let F0 := dpNormalizedTriple η P (σ 1) (-σ 2) (-σ 3)*
    dpNormalizedTriple η Q (σ 1) (-σ 2) (-σ 3)
  let F1 := dpNormalizedTriple η P (σ 0) (-σ 2) (-σ 3)*
    dpNormalizedTriple η Q (σ 0) (-σ 2) (-σ 3)
  let F2 := dpNormalizedTriple η P (σ 1) (-σ 0) (-σ 3)*
    dpNormalizedTriple η Q (σ 1) (-σ 0) (-σ 3)
  let F3 := dpNormalizedTriple η P (σ 1) (-σ 2) (-σ 0)*
    dpNormalizedTriple η Q (σ 1) (-σ 2) (-σ 0)
  have hz0 : residueZetaLeading 0 σ = D0⁻¹ := by
    dsimp only [D0]
    simp [residueZetaLeading,h0,mul_assoc]
    rw [show σ 0-σ 2 = -(σ 2-σ 0) by ring,
      show σ 0-σ 3 = -(σ 3-σ 0) by ring]
    simp only [inv_neg]
    ring
  have hz1 : residueZetaLeading 1 σ = D1⁻¹ := by
    dsimp only [D1]
    simp [residueZetaLeading,h1,mul_assoc]
    rw [show σ 1-σ 2 = -(σ 2-σ 1) by ring,
      show σ 1-σ 3 = -(σ 3-σ 1) by ring]
    simp only [inv_neg]
    ring
  have hz2 : residueZetaLeading 2 σ = D2⁻¹ := by
    simp [residueZetaLeading,h2,D2,mul_comm,mul_left_comm,mul_assoc]
  have hz3 : residueZetaLeading 3 σ = D3⁻¹ := by
    simp [residueZetaLeading,h3,D3,mul_comm]
  have hp0 : residueProfileLeading η P Q 0 σ = (arithmeticFactor:ℂ)*(η:ℂ)^6*F0 := by
    simp [residueProfileLeading,F0]
  have hp1 : residueProfileLeading η P Q 1 σ = (arithmeticFactor:ℂ)*(η:ℂ)^6*F1 := by
    simp [residueProfileLeading,F1,Equiv.swap_apply_def]
  have hp2 : residueProfileLeading η P Q 2 σ = (arithmeticFactor:ℂ)*(η:ℂ)^6*F2 := by
    simp [residueProfileLeading,F2,Equiv.swap_apply_def]
  have hp3 : residueProfileLeading η P Q 3 σ = (arithmeticFactor:ℂ)*(η:ℂ)^6*F3 := by
    simp [residueProfileLeading,F3,Equiv.swap_apply_def]
  have hdp : dpNormalizedBilinearFourResidues 1 η P Q (noDPAllPositiveSigns σ) =
      Complex.exp (-σ 0+σ 2+σ 3)*F0/D0+
      Complex.exp (-σ 1+σ 2+σ 3)*F1/D1+
      Complex.exp (σ 3)*F2/D2+Complex.exp (σ 2)*F3/D3 := by
    simp [dpNormalizedBilinearFourResidues,noDPAllPositiveSigns,F0,F1,F2,F3,D0,D1,D2,D3,
      sub_eq_add_neg,add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc]
  have he0 : Complex.exp (-(σ 0+z)) =
      Complex.exp (-σ 2-σ 3-z)*Complex.exp (-σ 0+σ 2+σ 3) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have he1 : Complex.exp (-(σ 1+z)) =
      Complex.exp (-σ 2-σ 3-z)*Complex.exp (-σ 1+σ 2+σ 3) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have he2 : Complex.exp (-(σ 2+z)) =
      Complex.exp (-σ 2-σ 3-z)*Complex.exp (σ 3) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have he3 : Complex.exp (-(σ 3+z)) =
      Complex.exp (-σ 2-σ 3-z)*Complex.exp (σ 2) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hπ : (2*Real.pi:ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hπc : (2*Real.pi:ℂ)*(1/(2*Real.pi):ℂ) = 1 := by
    simpa only [one_div] using mul_inv_cancel₀ hπ
  let M : ℂ := (arithmeticFactor:ℂ)*(∫ x : ℝ, w x)*Complex.exp (-σ 2-σ 3-z)*
    ((η:ℂ)^6*dpNormalizedBilinearFourResidues 1 η P Q (noDPAllPositiveSigns σ))
  change (2*Real.pi:ℂ)*separatedResidueLeading w η P Q σ z = M
  calc
    _ = ((2*Real.pi:ℂ)*(1/(2*Real.pi):ℂ))*M := by
      dsimp only [M]
      rw [hdp]
      simp only [separatedResidueLeading,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
        Fin.reduceSucc]
      rw [hz0,hz1,hz2,hz3,hp0,hp1,hp2,hp3]
      simp only [residueTimeLeading]
      rw [he0,he1,he2,he3]
      simp only [div_eq_mul_inv]
      ring
    _ = M := by rw [hπc,one_mul]

theorem noDPRegularMomentLeading_differentiableOn {η : ℝ} (hη : 0 ≤ η)
    (w : ℝ → ℂ) (P Q : Polynomial ℝ) (z : ℂ) :
    DifferentiableOn ℂ (fun σ => noDPRegularMomentLeading w η P Q σ z)
      (rectangularClosedPolydisc dpCauchyRadii) := by
  have hn : Differentiable ℂ (fun σ : Fin 4 → ℂ => fun j => -σ j) := by
    fun_prop
  have hp := (polarGeneralBilinearGeneratorContour_differentiableOn η P Q 16 16 hη).comp
    hn.differentiableOn (show Set.MapsTo (fun σ : Fin 4 → ℂ => fun j => -σ j)
      (rectangularClosedPolydisc dpCauchyRadii) (polarCircleDomain 16 16) from by
        intro σ hσ j
        have hr : dpCauchyRadii j ≤ (8:ℝ) := by fin_cases j <;> norm_num [dpCauchyRadii]
        have hj : ‖-σ j‖ < 16 := by rw [norm_neg]; linarith [hσ j]
        exact ⟨hj,hj⟩)
  exact (by fun_prop : DifferentiableOn ℂ (fun σ : Fin 4 → ℂ =>
    (arithmeticFactor:ℂ)*(∫ x : ℝ, w x)*Complex.exp (-σ 2-σ 3-z))
      (rectangularClosedPolydisc dpCauchyRadii)).mul hp

end
end SixthMoment.Source
