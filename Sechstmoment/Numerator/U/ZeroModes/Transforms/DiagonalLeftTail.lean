import Sechstmoment.Numerator.U.Replacement.GaussianTailUniform
import Sechstmoment.Numerator.U.ZeroModes.Transforms.DiagonalLeftContour

namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem a03Diagonal_coprime_uniform_log_tail {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T →
      ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) → ∀ m : Fin 6,
      ∀ a b : ℕ,a≠0 → b≠0 → a.Coprime b → ∀ t : ℝ,0<t →
      ‖bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) a b t-
        ((a*b:ℕ):ℂ)^(-1:ℂ)*
          bblrZArithmetic (bblrSixShifts (rawMomentShifts T σ) m 0)
            (bblrSixShifts (rawMomentShifts T σ) m 1)
            (bblrSixShifts (rawMomentShifts T σ) m 2)
            (bblrSixShifts (rawMomentShifts T σ) m 3) a b‖≤
        C*(Real.log T)^48*t^(-(1/4:ℝ))*((a*b:ℕ):ℝ)^(-(27/32:ℝ)) := by
  obtain ⟨B,hB,hbound⟩ := a03DiagonalEulerKernel_endpoint_majorant
  let P : ℝ := Real.exp 1*2^48*(1+1/κ^2)^24
  let J : ℝ := ∫ v : ℝ,(1+|v|)^48*Real.exp (4*Real.pi*|v|-v^2)
  have hP : 0≤P := by dsimp [P]; positivity
  have hJ : 0≤J := integral_nonneg (fun _ => by positivity)
  refine ⟨(1/(2*Real.pi))*B*P*(2*Real.pi)^(1/4:ℝ)*J,by positivity,?_⟩
  intro T hT hL σ hgap hα m a b ha hb hab t ht
  have hρ (ij : Fin 2 × Fin 2) : purePolarRoot T σ (m,ij)≠0 := by
    rw [Source.purePolarRoot_normalized]
    exact div_ne_zero (norm_pos_iff.mp (hκ.trans_le (hgap (m,ij))))
      (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  rw [bblrDiagonalTerm_eq_residue_add_leftIntegral σ hα m ha hb hab ht hρ,add_sub_cancel_left]
  let Q : ℝ := B*polarGaussianConstant T σ 1*(t/(2*Real.pi))^(-(1/4:ℝ))*
    ((a*b:ℕ):ℝ)^(-(27/32:ℝ))
  have hN := norm_integral_le_of_norm_le
    ((gaussianPolynomialExponential_integrable 48 (4*Real.pi)).const_mul Q)
    (ae_of_all _ (fun v : ℝ => by
      have hh := hbound T σ hα m a b ha hb t ht (-(1/8:ℝ)) (Or.inl rfl) v
      norm_num only at hh
      exact hh))
  rw [integral_const_mul] at hN
  have hp : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    rw [norm_div,norm_one,norm_mul]
    norm_num only [Complex.norm_ofNat]
    rw [Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
  unfold verticalIntegral
  rw [norm_mul,hp]
  have hg : polarGaussianConstant T σ 1≤P*(Real.log T)^48 :=
    Source.polarGaussianConstant_log_growth hT hL hκ σ hgap
  have htime : (t/(2*Real.pi))^(-(1/4:ℝ))=t^(-(1/4:ℝ))*(2*Real.pi)^(1/4:ℝ) := by
    rw [Real.div_rpow ht.le (by positivity),Real.rpow_neg (by positivity : 0≤2*Real.pi),div_inv_eq_mul]
  calc
    _≤(1/(2*Real.pi))*(Q*J) := mul_le_mul_of_nonneg_left hN (by positivity)
    _≤(1/(2*Real.pi))*(B*(P*(Real.log T)^48)*
        (t/(2*Real.pi))^(-(1/4:ℝ))*((a*b:ℕ):ℝ)^(-(27/32:ℝ))*J) := by
      dsimp [Q]
      gcongr
    _=_ := by rw [htime]; ring

theorem bblrDiagonalTerm_commonAmplifier (G : ℂ→ℂ) (α : MomentShifts)
    {g a b : ℕ} (hg : g≠0) (ha : a≠0) (hb : b≠0) (t : ℝ) :
    bblrDiagonalTerm G α (g*a) (g*b) t=(g:ℂ)^(-1:ℂ)*bblrDiagonalTerm G α a b t := by
  have hden : (((g*a)*(g*b):ℕ):ℂ)^(1/2:ℂ)=
      (g:ℂ)*((a*b:ℕ):ℂ)^(1/2:ℂ) := by
    rw [show (g*a)*(g*b)=g^2*(a*b) by ring,Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
    have hh := Complex.natCast_cpow_natCast_mul g 2 (1/2:ℂ)
    norm_num at hh
    rw [Nat.cast_pow,←hh]
  have hgC : (g:ℂ)≠0 := Nat.cast_ne_zero.mpr hg
  unfold bblrDiagonalTerm
  rw [←tsum_mul_left]
  apply tsum_congr
  intro n
  have hrel : diagonalQuadRelation (g*a) (g*b) n↔diagonalQuadRelation a b n := by
    unfold diagonalQuadRelation
    convert (Nat.mul_left_cancel_iff (Nat.pos_of_ne_zero hg)) using 1
    ring_nf
  simp only [hrel]
  split_ifs
  · unfold bblrDiagonalSummand
    rw [hden,Complex.cpow_neg_one]
    field_simp
  · simp

def a03DiagonalNativeArithmetic (α : MomentShifts) (a b : ℕ) : ℂ :=
  (Nat.gcd a b:ℂ)^(-1:ℂ)*(((a/Nat.gcd a b)*(b/Nat.gcd a b):ℕ):ℂ)^(-1:ℂ)*
    bblrZArithmetic (α 0) (α 1) (α 2) (α 3) (a/Nat.gcd a b) (b/Nat.gcd a b)

theorem a03Diagonal_native_uniform_log_tail {κ : ℝ} (hκ : 0<κ) :
    ∃ C : ℝ,0≤C ∧ ∀ T : ℝ,1<T → 1≤Real.log T →
      ∀ σ : MomentShifts,
      (∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) →
      (∀ j : Fin 4,‖rawMomentShifts T σ j‖≤1/64) → ∀ m : Fin 6,
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ t : ℝ,0<t →
      ‖bblrDiagonalTerm (polarPoleKiller T σ) (bblrSixShifts (rawMomentShifts T σ) m) a b t-
        a03DiagonalNativeArithmetic (bblrSixShifts (rawMomentShifts T σ) m) a b‖≤
        C*(Real.log T)^48*t^(-(1/4:ℝ))*((a*b:ℕ):ℝ)^(-(1/2:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := a03Diagonal_coprime_uniform_log_tail hκ
  refine ⟨C,hC,?_⟩
  intro T hT hL σ hgap hα m a b ha hb t ht
  let g := Nat.gcd a b
  let a' := a/g
  let b' := b/g
  have hg : 0<g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero ha)
  have ha' : 0<a' := Nat.div_pos (Nat.gcd_le_left _ (Nat.pos_of_ne_zero ha)) hg
  have hb' : 0<b' := Nat.div_pos (Nat.gcd_le_right _ (Nat.pos_of_ne_zero hb)) hg
  have hga : g*a'=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hgb : g*b'=b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hcop : a'.Coprime b' := Nat.coprime_div_gcd_div_gcd hg
  have hD := bblrDiagonalTerm_commonAmplifier (polarPoleKiller T σ)
    (bblrSixShifts (rawMomentShifts T σ) m) hg.ne' ha'.ne' hb'.ne' t
  rw [hga,hgb] at hD
  rw [hD]
  unfold a03DiagonalNativeArithmetic
  rw [mul_assoc]
  change ‖(g:ℂ)^(-1:ℂ)*bblrDiagonalTerm _ _ a' b' t-
    (g:ℂ)^(-1:ℂ)*(((a'*b':ℕ):ℂ)^(-1:ℂ)*bblrZArithmetic _ _ _ _ a' b')‖≤_
  rw [←mul_sub,norm_mul,Complex.norm_natCast_cpow_of_pos hg]
  norm_num only [Complex.neg_re,Complex.one_re]
  have hbound' := hbound T hT hL σ hgap hα m a' b' ha'.ne' hb'.ne' hcop t ht
  have hpow : ((a'*b':ℕ):ℝ)^(-(27/32:ℝ))≤((a'*b':ℕ):ℝ)^(-(1/2:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (mul_ne_zero ha'.ne' hb'.ne')) (by norm_num)
  have he : (g:ℝ)^(-1:ℝ)*((a'*b':ℕ):ℝ)^(-(1/2:ℝ))=
      ((a*b:ℕ):ℝ)^(-(1/2:ℝ)) := by
    rw [show a*b=g^2*(a'*b') by rw [←hga,←hgb]; ring]
    simp only [Nat.cast_mul,Nat.cast_pow]
    rw [Real.mul_rpow (sq_nonneg (g:ℝ))
      (mul_nonneg (Nat.cast_nonneg a') (Nat.cast_nonneg b'))]
    rw [←Real.rpow_two,←Real.rpow_mul (Nat.cast_nonneg g)]
    norm_num
  calc
    _≤(g:ℝ)^(-1:ℝ)*(C*(Real.log T)^48*t^(-(1/4:ℝ))*((a'*b':ℕ):ℝ)^(-(27/32:ℝ))) := by
      gcongr
    _≤(C*(Real.log T)^48*t^(-(1/4:ℝ)))*
        ((g:ℝ)^(-1:ℝ)*((a'*b':ℕ):ℝ)^(-(1/2:ℝ))) := by
      rw [show (g:ℝ)^(-1:ℝ)*(C*(Real.log T)^48*t^(-(1/4:ℝ))*((a'*b':ℕ):ℝ)^(-(27/32:ℝ)))=
        (C*(Real.log T)^48*t^(-(1/4:ℝ)))*((g:ℝ)^(-1:ℝ)*((a'*b':ℕ):ℝ)^(-(27/32:ℝ))) by ring]
      gcongr
    _=_ := by rw [he]

end
end Sechstmoment
