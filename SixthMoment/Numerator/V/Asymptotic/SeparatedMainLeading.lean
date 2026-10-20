import SixthMoment.Numerator.V.Asymptotic.ProfileMainFactorization
import SixthMoment.Numerator.V.Asymptotic.ResidueProductError
import SixthMoment.Numerator.V.Asymptotic.ResidueProfileLeading
import SixthMoment.Numerator.V.Asymptotic.ResidueZetaLeading
import SixthMoment.Numerator.V.Asymptotic.TimeResidueLeading


namespace SixthMoment.Source
open NoDPGlobalLFactorization NoDPHarmonic Complex Real Set MeasureTheory Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

def residueZetaLeading (i : Fin 4) (σ : Fin 4 → ℂ) : ℂ :=
  ∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, (σ j-σ i)⁻¹

def residueZetaScaled (L : ℝ) (i : Fin 4) (σ : Fin 4 → ℂ) : ℂ :=
  (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
    riemannZeta (1+(σ j-σ i)/(L:ℂ)))/(L:ℂ)^3

def residueTimeLeading (w : ℝ → ℂ) (σ : Fin 4 → ℂ) (z : ℂ) (i : Fin 4) : ℂ :=
  (1/(2*Real.pi):ℂ)*Complex.exp (-(σ i+z))*(∫ x : ℝ, w x)

def separatedResidueLeading (w : ℝ → ℂ) (η : ℝ) (P Q : ℝ[X])
    (σ : Fin 4 → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin 4, residueTimeLeading w σ z i*
    (residueZetaLeading i σ*residueProfileLeading η P Q i σ)

theorem residueZetaLeading_norm_bound {δ : ℝ} (hδ : 0 < δ)
    (σ : Fin 4 → ℂ) (i : Fin 4) (hgap : ∀ j, j ≠ i → δ ≤ ‖σ j-σ i‖) :
    ‖residueZetaLeading i σ‖ ≤ (1/δ)^3 := by
  classical
  rw [residueZetaLeading,norm_prod]
  calc
    _ ≤ ∏ _j ∈ (Finset.univ : Finset (Fin 4)).erase i, (1/δ) := by
      apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
      intro j hj
      rw [norm_inv,← one_div]
      exact one_div_le_one_div_of_le hδ (hgap j (Finset.mem_erase.mp hj).1)
    _ = _ := by simp

theorem residueZeta_scaled_uniform_error (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ R L : ℝ, 1 ≤ L → 2*R ≤ L →
      ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R → ∀ i : Fin 4,
      (∀ j, j ≠ i → δ ≤ ‖σ j-σ i‖) →
      ‖residueZetaScaled L i σ-residueZetaLeading i σ‖ ≤ C/L := by
  obtain ⟨C,hC,HC⟩ := residueZeta_complement_uniform_error δ hδ
  refine ⟨C,hC,?_⟩
  intro R L hL hLR σ hσ i hgap
  have hL0 : 0 < L := by linarith
  have hLC : (L:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL0.ne'
  have H := HC R L hL hLR σ hσ i hgap
  have hid : residueZetaScaled L i σ-residueZetaLeading i σ =
      ((∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i,
          riemannZeta (1+(σ j-σ i)/(L:ℂ)))-
        (L:ℂ)^3*residueZetaLeading i σ)/(L:ℂ)^3 := by
    unfold residueZetaScaled
    field_simp [hLC]
  rw [hid,norm_div,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hL0]
  apply (div_le_div_iff₀ (pow_pos hL0 3) hL0).mpr
  calc
    _ ≤ (C*L^2)*L := mul_le_mul_of_nonneg_right H hL0.le
    _ = _ := by ring

theorem separated_profile_main_normalized_error {w : ℝ → ℂ}
    (hw : Continuous w) (hws : tsupport w ⊆ Icc (1:ℝ) 2)
    {η R δ : ℝ} (hη : 0 < η) (hR : 0 ≤ R) (hδ : 0 < δ) (P Q : ℝ[X]) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T →
      max 1 (max ((2*R)*(elementaryPhaseLogBound+1)) (16*R)) ≤ Real.log T →
      ∀ σ : Fin 4 → ℂ, ‖σ‖ ≤ R → ∀ z : ℂ, ‖z‖ ≤ R →
      (∀ i j : Fin 4, i ≠ j → δ ≤ ‖σ i-σ j‖) →
      ‖profileAdditiveOriginalMain
          (fun x => (zeroExtendedPolynomialProfile η P x:ℂ))
          (fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)) (Real.log T) (⌊T^η⌋₊^2)
          (noDPTimeWeight w T (z/(Real.log T:ℂ))) (scaledShifts (Real.log T) σ)
          (T/(2*Real.pi))/((T:ℂ)*(Real.log T:ℂ)^9)-
        separatedResidueLeading w η P Q σ z‖ ≤ C/Real.log T := by
  classical
  obtain ⟨Ct,hCt,HT⟩ := timeWeight_residue_leading_uniform hw hws R hR
  obtain ⟨Cz,hCz,HZ⟩ := residueZeta_scaled_uniform_error δ hδ
  obtain ⟨Ch,hCh,HH⟩ := residueProfile_scaled_uniform_error hη hR P Q
  obtain ⟨Bh,hBh,HB⟩ := residueProfileLeading_uniform_bound η P Q R
  let Bt := ‖(1/(2*Real.pi):ℂ)‖*Real.exp (2*R)*‖∫ x : ℝ, w x‖
  let Bz := (1/δ)^3
  let B := Bt+Bz+Bh
  let E := Ct+Cz+Ch
  let Cp := 3*(B+E)^2*E
  have hBt : 0 ≤ Bt := by dsimp only [Bt]; positivity
  have hBz : 0 ≤ Bz := by dsimp only [Bz]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  refine ⟨4*Cp+1,by positivity,?_⟩
  intro T hT hlog σ hσ z hz hgap
  let L := Real.log T
  let β := scaledShifts L σ
  let wt := noDPTimeWeight w T (z/(L:ℂ))
  let X := T/(2*Real.pi)
  let a0 (i : Fin 4) := mellin wt (1-β i)*(X:ℂ)^(1-β i)/(T:ℂ)
  let a1 (i : Fin 4) := residueZetaScaled L i σ
  let a2 (i : Fin 4) := originalProfileSum η L i β P Q/(L:ℂ)^6
  let a (i : Fin 4) : Fin 3 → ℂ := ![a0 i,a1 i,a2 i]
  let b (i : Fin 4) : Fin 3 → ℂ :=
    ![residueTimeLeading w σ z i,residueZetaLeading i σ,residueProfileLeading η P Q i σ]
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hlog
  have hL0 : 0 < L := by linarith
  have hbig : 16*R ≤ L :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlog)
  have hLZ : 2*R ≤ L := by linarith
  have hLH : 2*R ≤ (1/8)*L := by linarith
  have hLT : max 1 ((2*R)*(elementaryPhaseLogBound+1)) ≤ L :=
    max_le hL1 ((le_max_left _ _).trans ((le_max_right _ _).trans hlog))
  have hσi (i : Fin 4) : ‖σ i‖ ≤ R := (norm_le_pi_norm σ i).trans hσ
  have hb0 (i : Fin 4) : ‖residueTimeLeading w σ z i‖ ≤ Bt := by
    have hν : ‖σ i+z‖ ≤ 2*R := (norm_add_le _ _).trans (by linarith [hσi i])
    have he : ‖Complex.exp (-(σ i+z))‖ ≤ Real.exp (2*R) := by
      rw [Complex.norm_exp]
      apply Real.exp_le_exp.mpr
      exact (Complex.re_le_norm (-(σ i+z))).trans (by simpa only [norm_neg] using hν)
    rw [residueTimeLeading,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (norm_nonneg _)) (norm_nonneg _)
  have hb (i : Fin 4) (j : Fin 3) : ‖b i j‖ ≤ B := by
    fin_cases j
    · change ‖residueTimeLeading w σ z i‖ ≤ B
      exact (hb0 i).trans (by dsimp only [B]; linarith)
    · change ‖residueZetaLeading i σ‖ ≤ B
      exact (residueZetaLeading_norm_bound hδ σ i (fun j hj => hgap j i hj)).trans
        (by dsimp only [B,Bz]; linarith)
    · change ‖residueProfileLeading η P Q i σ‖ ≤ B
      exact (HB σ hσ i).trans (by dsimp only [B]; linarith)
  have he (i : Fin 4) (j : Fin 3) : ‖a i j-b i j‖ ≤ E/L := by
    fin_cases j
    · change ‖a0 i-residueTimeLeading w σ z i‖ ≤ E/L
      have H := HT T hT hLT (σ i) z (hσi i) hz
      have H' : ‖a0 i-residueTimeLeading w σ z i‖ ≤ Ct/L := H
      exact H'.trans (div_le_div_of_nonneg_right (by dsimp only [E]; linarith) hL0.le)
    · change ‖a1 i-residueZetaLeading i σ‖ ≤ E/L
      exact (HZ R L hL1 hLZ σ hσ i (fun j hj => hgap j i hj)).trans
        (div_le_div_of_nonneg_right (by dsimp only [E]; linarith) hL0.le)
    · change ‖a2 i-residueProfileLeading η P Q i σ‖ ≤ E/L
      exact (HH L hL1 hLH σ hσ i).trans
        (div_le_div_of_nonneg_right (by dsimp only [E]; linarith) hL0.le)
  have hentry (i : Fin 4) :
      ‖a i 0*(a i 1*a i 2)-b i 0*(b i 1*b i 2)‖ ≤ Cp/L :=
    norm_triple_product_inverse_scale_error (a i) (b i) hB hE hL1 (hb i) (he i)
  have hzeta (i : Fin 4) :
      (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i))/(L:ℂ)^3 = a1 i := by
    unfold a1 residueZetaScaled
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    congr 1
    dsimp only [β,scaledShifts]
    ring
  have hfloor : ⌊Real.exp (L*η)⌋₊ = ⌊T^η⌋₊ := by rw [Real.rpow_def_of_pos hT]
  have hid : profileAdditiveOriginalMain
      (fun x => (zeroExtendedPolynomialProfile η P x:ℂ))
      (fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)) L (⌊T^η⌋₊^2) wt β X/
      ((T:ℂ)*(L:ℂ)^9) = ∑ i : Fin 4, a i 0*(a i 1*a i 2) := by
    rw [← hfloor,profileAdditiveOriginalMain_factorization hL0 wt β P Q X,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    change (mellin wt (1-β i)*(X:ℂ)^(1-β i)*originalProfileSum η L i β P Q*
      (∏ j ∈ (Finset.univ : Finset (Fin 4)).erase i, riemannZeta (1+β j-β i)))/
      ((T:ℂ)*(L:ℂ)^9) = a0 i*(a1 i*a2 i)
    rw [← hzeta]
    dsimp only [a0,a2]
    simp only [div_eq_mul_inv,mul_inv]
    ring
  have hleading : separatedResidueLeading w η P Q σ z =
      ∑ i : Fin 4, b i 0*(b i 1*b i 2) := rfl
  rw [hid,hleading,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _i : Fin 4, Cp/L :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => hentry i))
    _ = (4*Cp)/L := by simp; ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith) hL0.le

end
end SixthMoment.Source
