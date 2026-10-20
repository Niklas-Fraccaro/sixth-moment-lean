import Sechstmoment.Numerator.U.ZeroModes.Transforms.DiagonalLeftAnalytic


namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03DiagonalFiniteArithmetic (α : MomentShifts) (a b : ℕ) (z : ℂ) : ℂ :=
  (riemannZeta (a03DiagonalEulerDenominatorArgument α z))⁻¹*
    bblrBFactorAt (α 0) (α 1) (α 2) (α 3) z a*
    bblrBFactorAt (α 2) (α 3) (α 0) (α 1) z b

theorem a03DiagonalEulerKernel_eq_pure (T : ℝ) (σ : MomentShifts) (m : Fin 6)
    (a b : ℕ) (t : ℝ) (z : ℂ) :
    a03DiagonalEulerKernel (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) a b t z=
      (polarPoleKiller T σ z*purePolarZetaProduct T σ m z)/z*
        (t/(2*Real.pi):ℂ)^(2*z)*((a*b:ℕ):ℂ)^(-(1+z))*
          a03DiagonalFiniteArithmetic (bblrSixShifts (rawMomentShifts T σ) m) a b z := by
  unfold a03DiagonalEulerKernel a03DiagonalFiniteArithmetic
  rw [a03DiagonalArithmetic_eq_pureQuotient]
  ring

theorem a03DiagonalFiniteArithmetic_uniform_bound :
    ∃ E : ℝ,0≤E ∧ ∀ α : MomentShifts,(∀ j : Fin 4,‖α j‖≤1/64) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ z : ℂ,-(1/8:ℝ)≤z.re →
        ‖a03DiagonalFiniteArithmetic α a b z‖≤E*((a*b:ℕ):ℝ)^(1/32:ℝ) := by
  obtain ⟨D,hD,hB⟩ := bblrBFactorAt_uniform_subpower_bound
  let Z := zetaDirichletMajorant (7/5)
  have hZ0 : 0≤Z := zetaDirichletMajorant_nonneg _
  refine ⟨Z*D^2,by dsimp [Z]; exact mul_nonneg (zetaDirichletMajorant_nonneg _) (sq_nonneg D),?_⟩
  intro α hα a b ha hb z hz
  have hZ : ‖(riemannZeta (a03DiagonalEulerDenominatorArgument α z))⁻¹‖≤Z :=
    riemannZeta_inv_norm_le_dirichlet (by norm_num) (a03DiagonalEulerDenominator_re_lower hα hz)
  have hA := hB (α 0) (α 1) (α 2) (α 3) z a ha (hα 0) (hα 1) (hα 2) (hα 3) hz
  have hB' := hB (α 2) (α 3) (α 0) (α 1) z b hb (hα 2) (hα 3) (hα 0) (hα 1) hz
  unfold a03DiagonalFiniteArithmetic
  rw [norm_mul,norm_mul]
  calc
    _≤Z*(D*(a:ℝ)^(1/32:ℝ))*(D*(b:ℝ)^(1/32:ℝ)) := by gcongr
    _=_ := by
      rw [Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)]
      ring

theorem a03DiagonalPureZeta_endpoint_bound :
    ∃ D : ℝ,0≤D ∧ ∀ T : ℝ,∀ σ : MomentShifts,
      (∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) → ∀ m : Fin 6,
      ∀ c : ℝ,c= -(1/8:ℝ) ∨ c=1 → ∀ v : ℝ,
        ‖purePolarZetaProduct T σ m ((c:ℂ)+(v:ℂ)*I)‖≤D*Real.exp (4*Real.pi*|v|) := by
  obtain ⟨C,hC,hZ⟩ := riemannZeta_norm_le_exp_halfPlane
    (by norm_num : (0:ℝ)<1/2) (by norm_num : (0:ℝ)<1/8)
  refine ⟨C^4*Real.exp (Real.pi/16),by positivity,?_⟩
  intro T σ hα m c hc v
  have hρ (ij : Fin 2 × Fin 2) : ‖purePolarRoot T σ (m,ij)‖≤1/64 :=
    purePolarRoot_norm_le_of_rawShifts hα (m,ij)
  have hf (ij : Fin 2 × Fin 2) :
      ‖riemannZeta (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖≤
        C*Real.exp (Real.pi*(|v|+1/64)) := by
    have hre := (Complex.abs_re_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have him := (Complex.abs_im_le_norm (purePolarRoot T σ (m,ij))).trans (hρ ij)
    have he : (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re=
        1+2*(c-(purePolarRoot T σ (m,ij)).re) := by simp
    have harg : (1/2:ℝ)≤(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).re := by
      rw [he]
      rcases hc with rfl|rfl <;> linarith [(abs_le.mp hre).2]
    have hsep : (1/8:ℝ)≤‖1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ := by
      have he' : (1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))).re=
          -2*(c-(purePolarRoot T σ (m,ij)).re) := by simp
      have hl := Complex.re_le_norm
        (1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))))
      have hr := Complex.re_le_norm
        (-(1-(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))))
      rw [he'] at hl
      simp only [neg_re,norm_neg] at hr
      rw [he'] at hr
      rcases hc with rfl|rfl
      · linarith [(abs_le.mp hre).1]
      · linarith [(abs_le.mp hre).2]
    have hi : |(1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).im|≤2*(|v|+1/64) := by
      have hi' : (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij))).im=
          2*(v-(purePolarRoot T σ (m,ij)).im) := by simp
      rw [hi',abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
      exact mul_le_mul_of_nonneg_left ((abs_sub v _).trans (add_le_add le_rfl him)) (by norm_num)
    exact (hZ _ harg hsep).trans (by gcongr; nlinarith [Real.pi_pos])
  unfold purePolarZetaProduct
  calc
    _≤∏ ij : Fin 2 × Fin 2,‖riemannZeta (1+2*(((c:ℂ)+(v:ℂ)*I)-purePolarRoot T σ (m,ij)))‖ :=
      Finset.norm_prod_le _ _
    _≤∏ _ij : Fin 2 × Fin 2,C*Real.exp (Real.pi*(|v|+1/64)) :=
      Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun ij _ => hf ij)
    _=_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
      norm_num only
      rw [mul_pow,←Real.exp_nat_mul]
      norm_num only [Nat.cast_ofNat]
      rw [mul_assoc,←Real.exp_add]
      congr 2
      ring

theorem a03DiagonalEulerKernel_endpoint_majorant :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,∀ σ : MomentShifts,
      (∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) → ∀ m : Fin 6,
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ t : ℝ,0<t →
      ∀ c : ℝ,c= -(1/8:ℝ) ∨ c=1 → ∀ v : ℝ,
        ‖a03DiagonalEulerKernel (polarPoleKiller T σ)
          (bblrSixShifts (rawMomentShifts T σ) m) a b t ((c:ℂ)+(v:ℂ)*I)‖≤
            C*polarGaussianConstant T σ 1*(t/(2*Real.pi))^(2*c)*
              ((a*b:ℕ):ℝ)^(-(1+c)+1/32)*
                ((1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2)) := by
  obtain ⟨D,hD,hZ⟩ := a03DiagonalPureZeta_endpoint_bound
  obtain ⟨E,hE,hA⟩ := a03DiagonalFiniteArithmetic_uniform_bound
  refine ⟨8*D*E,by positivity,?_⟩
  intro T σ hα m a b ha hb t ht c hc v
  let z : ℂ := (c:ℂ)+(v:ℂ)*I
  have hcstrip : -(1/8:ℝ)≤c := by rcases hc with rfl|rfl <;> norm_num
  have hcabs : |c|≤1 := by rcases hc with rfl|rfl <;> norm_num
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hG : ‖polarPoleKiller T σ z‖≤polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2) :=
    (polarPoleKiller_vertical_norm_le T σ c v).trans (by
      gcongr
      exact polarGaussianConstant_le_of_abs_le T σ (by norm_num) hcabs)
  have hZ' := hZ T σ hα m c hc v
  have hA' := hA (bblrSixShifts (rawMomentShifts T σ) m)
    (fun j => bblrSixShifts_norm_le _ hα m j) a b ha hb z (by simpa [z] using hcstrip)
  have hznorm : (1/8:ℝ)≤‖z‖ := by
    have hn := Complex.abs_re_le_norm z
    have hzre : z.re=c := by simp [z]
    rw [hzre] at hn
    rcases hc with rfl|rfl <;> norm_num at hn ⊢ <;> linarith
  have hinv : ‖z‖⁻¹≤8 := by
    convert inv_anti₀ (by norm_num : (0:ℝ)<1/8) hznorm using 1
    norm_num
  have htime : ‖(t/(2*Real.pi):ℂ)^(2*z)‖=(t/(2*Real.pi))^(2*c) := by
    rw [show (t/(2*Real.pi):ℂ)=((t/(2*Real.pi):ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (div_pos ht (by positivity))]
    simp [z]
  have habpos : (0:ℝ)<(a*b:ℕ) := by exact_mod_cast Nat.pos_of_ne_zero (mul_ne_zero ha hb)
  have hamp : ‖((a*b:ℕ):ℂ)^(-(1+z))‖=((a*b:ℕ):ℝ)^(-(1+c)) := by
    rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero (mul_ne_zero ha hb))]
    simp [z]
  rw [a03DiagonalEulerKernel_eq_pure]
  rw [norm_mul,norm_mul,norm_mul,norm_div,norm_mul,div_eq_mul_inv,htime,hamp]
  calc
    _≤(polarGaussianConstant T σ 1*(1+|v|)^48*Real.exp (-v^2))*
        (D*Real.exp (4*Real.pi*|v|))*8*(t/(2*Real.pi))^(2*c)*
        ((a*b:ℕ):ℝ)^(-(1+c))*(E*((a*b:ℕ):ℝ)^(1/32:ℝ)) := by gcongr
    _=_ := by
      rw [Real.rpow_add habpos,Real.exp_sub,Real.exp_neg]
      ring

end
end Sechstmoment
