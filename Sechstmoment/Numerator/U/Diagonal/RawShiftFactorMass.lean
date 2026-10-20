import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Sechstmoment.Numerator.U.Diagonal.ActualNearAmplifierMass
import Sechstmoment.Numerator.U.Separation.Frequency.ActualFarKernel


namespace Sechstmoment.Source
open Complex Real Filter
open scoped BigOperators Topology
noncomputable section

theorem bblrAFEDenominatorInv_norm_eq (α : MomentShifts) (n : Fin 4 → ℕ) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹‖ =
      ∏ j : Fin 4, (n j+1 : ℝ)^(-(1/2+(α j).re)) := by
  rw [norm_inv,norm_prod,← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  have hn : 0 < (n j+1 : ℝ) := by positivity
  rw [show (n j+1 : ℂ) = ((n j+1 : ℝ) : ℂ) by push_cast; rfl,
    Complex.norm_cpow_eq_rpow_re_of_pos hn]
  have he : (1/2+α j : ℂ).re = 1/2+(α j).re := by simp
  rw [he,Real.rpow_neg hn.le]

theorem bblrAFEDenominatorInv_norm_le_product_rpow (α : MomentShifts)
    (n : Fin 4 → ℕ) {r : ℝ} (hα : ∀ j, -r ≤ (α j).re) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹‖ ≤
      (positiveQuadProduct n : ℝ)^r/Real.sqrt (positiveQuadProduct n : ℝ) := by
  have hn (j : Fin 4) : 0 < (n j+1 : ℝ) := by positivity
  have hprod : (∏ j : Fin 4, (n j+1 : ℝ)) = (positiveQuadProduct n : ℝ) := by
    rw [positiveQuadProduct_eq_prod]
    push_cast
    rfl
  have hx : 0 < (positiveQuadProduct n : ℝ) := by unfold positiveQuadProduct; positivity
  calc
    _ = ∏ j : Fin 4, (n j+1 : ℝ)^(-(1/2+(α j).re)) :=
      bblrAFEDenominatorInv_norm_eq α n
    _ ≤ ∏ j : Fin 4, (n j+1 : ℝ)^(r-1/2) := by
      apply Finset.prod_le_prod₀ (fun j _ => by positivity)
      intro j _
      apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n j)) : (1:ℝ)≤n j+1)
      linarith [hα j]
    _ = (positiveQuadProduct n : ℝ)^(r-1/2) := by
      rw [Real.finsetProd_rpow Finset.univ (fun j => (n j+1 : ℝ))
        (fun j _ => (hn j).le) (r-1/2),hprod]
    _ = _ := by rw [Real.rpow_sub hx,← Real.sqrt_eq_rpow]

theorem bblrAFEDenominatorInv_norm_le_of_norm (α : MomentShifts)
    (n : Fin 4 → ℕ) {r : ℝ} (hα : ∀ j, ‖α j‖ ≤ r) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹‖ ≤
      (positiveQuadProduct n : ℝ)^r/Real.sqrt (positiveQuadProduct n : ℝ) := by
  apply bblrAFEDenominatorInv_norm_le_product_rpow
  intro j
  have hj := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
  exact hj

theorem bblrRawShift_product_rpow_le {T C κ R x : ℝ}
    (hT : 0 < T) (hlog : 1 ≤ Real.log T) (hC : 1 ≤ C) (hR : 0 ≤ R)
    (hx : 0 < x) (hcut : x ≤ C*T^κ) :
    x^(R/Real.log T) ≤ Real.exp (R*(Real.log C+κ)) := by
  have hL : 0 < Real.log T := zero_lt_one.trans_le hlog
  have hCp : 0 < C := zero_lt_one.trans_le hC
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlogx : Real.log x ≤ Real.log C+κ*Real.log T := by
    have hb := Real.log_le_log hx hcut
    rw [Real.log_mul hCp.ne' (Real.rpow_pos_of_pos hT κ).ne',Real.log_rpow hT] at hb
    simpa [mul_comm] using hb
  rw [Real.rpow_def_of_pos hx]
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ (Real.log C+κ*Real.log T)*(R/Real.log T) :=
      mul_le_mul_of_nonneg_right hlogx (div_nonneg hR hL.le)
    _ = R*(Real.log C/Real.log T+κ) := by field_simp
    _ ≤ R*(Real.log C+κ) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact add_le_add (div_le_self hlogC hlog) le_rfl

theorem bblrAFEDenominatorInv_raw_norm_le_of_product_cutoff
    {T C κ R : ℝ} (hT : 0 < T) (hlog : 1 ≤ Real.log T)
    (hC : 1 ≤ C) (hR : 0 ≤ R) (σ : MomentShifts)
    (hσ : ∀ j, ‖σ j‖ ≤ R) (n : Fin 4 → ℕ)
    (hcut : (positiveQuadProduct n : ℝ) ≤ C*T^κ) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+rawMomentShifts T σ j))⁻¹‖ ≤
      Real.exp (R*(Real.log C+κ))/Real.sqrt (positiveQuadProduct n : ℝ) := by
  have hL : 0 < Real.log T := zero_lt_one.trans_le hlog
  have hraw (j : Fin 4) : ‖rawMomentShifts T σ j‖ ≤ R/Real.log T := by
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hL.le]
    exact div_le_div_of_nonneg_right (hσ j) hL.le
  have hx : 0 < (positiveQuadProduct n : ℝ) := by unfold positiveQuadProduct; positivity
  calc
    _ ≤ (positiveQuadProduct n : ℝ)^(R/Real.log T)/
        Real.sqrt (positiveQuadProduct n : ℝ) :=
      bblrAFEDenominatorInv_norm_le_of_norm _ n hraw
    _ ≤ _ := div_le_div_of_nonneg_right
      (bblrRawShift_product_rpow_le hT hlog hC hR hx hcut) (Real.sqrt_nonneg _)

theorem bblrAFEDenominatorInv_six_raw_norm_le_of_product_cutoff
    {T C κ R : ℝ} (hT : 0 < T) (hlog : 1 ≤ Real.log T)
    (hC : 1 ≤ C) (hR : 0 ≤ R) (σ : MomentShifts)
    (hσ : ∀ j, ‖σ j‖ ≤ R) (k : Fin 6) (n : Fin 4 → ℕ)
    (hcut : (positiveQuadProduct n : ℝ) ≤ C*T^κ) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+bblrSixShifts (rawMomentShifts T σ) k j))⁻¹‖ ≤
      Real.exp (R*(Real.log C+κ))/Real.sqrt (positiveQuadProduct n : ℝ) := by
  have hs : ∀ j, ‖bblrSixShifts σ k j‖ ≤ R := by
    intro j
    fin_cases k <;> fin_cases j <;> simp [bblrSixShifts] <;>
      first | exact hσ 0 | exact hσ 1 | exact hσ 2 | exact hσ 3
  simpa only [rawMomentShifts,bblrSixShifts_raw] using
    bblrAFEDenominatorInv_raw_norm_le_of_product_cutoff hT hlog hC hR
      (bblrSixShifts σ k) hs n hcut

theorem bblrAFEDenominatorInv_vertical_norm_le (α : MomentShifts)
    (n : Fin 4 → ℕ) (z : ℂ) (hz : 0≤z.re) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j+z))⁻¹‖ ≤
      ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+α j))⁻¹‖ := by
  simp_rw [add_assoc]
  rw [bblrAFEDenominatorInv_norm_eq (fun j => α j+z),
    bblrAFEDenominatorInv_norm_eq α]
  apply Finset.prod_le_prod₀ (fun j _ => by positivity)
  intro j _
  apply Real.rpow_le_rpow_of_exponent_le
    (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (n j)) : (1:ℝ)≤n j+1)
  simp only [Complex.add_re]
  linarith

end
end Sechstmoment.Source

namespace Sechstmoment
open Source Real Complex
open scoped BigOperators
noncomputable section

theorem actualNearAmplifierAFE_raw_weight_le
    {T C κ R : ℝ} (hT : 0 < T) (hlog : 1 ≤ Real.log T)
    (hC : 1 ≤ C) (hR : 0 ≤ R) (A B : ℝ) (f g : ℝ → ℝ)
    {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∀ x, ‖f x‖ ≤ F) (hg : ∀ x, ‖g x‖ ≤ G)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R) (k : Fin 6)
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (n : Fin 4 → ℕ)
    (hcut : (positiveQuadProduct n : ℝ) ≤ C*T^κ) :
    ‖phaseActualAmplifierCoefficient T f A u‖*
      ‖phaseActualAmplifierCoefficient T g B v‖*
      ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+bblrSixShifts (rawMomentShifts T σ) k j))⁻¹‖ ≤
      Real.exp (R*(Real.log C+κ))*F*G*
        positiveNearFactorWeight u v (bblrAFEFactorPairs n) := by
  calc
    _ ≤ ‖phaseActualAmplifierCoefficient T f A u‖*
        ‖phaseActualAmplifierCoefficient T g B v‖*
        (Real.exp (R*(Real.log C+κ))/Real.sqrt (positiveQuadProduct n : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (bblrAFEDenominatorInv_six_raw_norm_le_of_product_cutoff
          hT hlog hC hR σ hσ k n hcut) (by positivity)
    _ = Real.exp (R*(Real.log C+κ))*
        (‖phaseActualAmplifierCoefficient T f A u‖*
          ‖phaseActualAmplifierCoefficient T g B v‖/
            Real.sqrt (positiveQuadProduct n : ℝ)) := by ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left
        (actualNearAmplifierAFE_weight_le T A B f g hF hG hf hg hu hv n)
        (Real.exp_pos (R*(Real.log C+κ))).le using 1
      ring

theorem actualAmplifiedNearAFE_raw_mass_le_harmonic
    {T C κ R : ℝ} (hT : 0 < T) (hlog : 1 ≤ Real.log T)
    (hC : 1 ≤ C) (hR : 0 ≤ R) (A B : ℝ) (f g : ℝ → ℝ)
    {F G : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G)
    (hf : ∀ x, ‖f x‖ ≤ F) (hg : ∀ x, ‖g x‖ ≤ G)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R) (k : Fin 6)
    {U Umax V Vmax L P J Q H K : ℕ}
    (hU : 0<U) (hV : 0<V) (hL : 0<L) (hJ : 0<J) (hQ : Q≤K^2)
    (s : ℕ → ℕ → Finset (Fin 4 → ℕ))
    (hs : ∀ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
      ∀ n∈s uv.1 uv.2,
        bblrAFEFactorPairs n ∈ positiveNearFactorBlock L P J Q uv.1 uv.2 H)
    (hcut : ∀ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
      ∀ n∈s uv.1 uv.2, (positiveQuadProduct n : ℝ) ≤ C*T^κ) :
    (∑ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
      ∑ n∈s uv.1 uv.2,
        ‖phaseActualAmplifierCoefficient T f A uv.1‖*
          ‖phaseActualAmplifierCoefficient T g B uv.2‖*
          ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+
              bblrSixShifts (rawMomentShifts T σ) k j))⁻¹‖) ≤
      Real.exp (R*(Real.log C+κ))*
        (F*G*(((Umax+1-U)*(Vmax+1-V) : ℕ):ℝ)*(P:ℝ)*(harmonic P : ℝ)*
          (2*(2*(H:ℝ)/(V:ℝ)+1)*(harmonic K : ℝ)+2*K)/
            Real.sqrt ((U:ℝ)*V*L*J)) := by
  calc
    _ ≤ ∑ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
        ∑ n∈s uv.1 uv.2,
          Real.exp (R*(Real.log C+κ))*
            (‖phaseActualAmplifierCoefficient T f A uv.1‖*
              ‖phaseActualAmplifierCoefficient T g B uv.2‖/
                Real.sqrt (positiveQuadProduct n : ℝ)) := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro n hn
      calc
        _ ≤ ‖phaseActualAmplifierCoefficient T f A uv.1‖*
            ‖phaseActualAmplifierCoefficient T g B uv.2‖*
            (Real.exp (R*(Real.log C+κ))/Real.sqrt (positiveQuadProduct n : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (bblrAFEDenominatorInv_six_raw_norm_le_of_product_cutoff
              hT hlog hC hR σ hσ k n (hcut uv huv n hn)) (by positivity)
        _ = _ := by ring
    _ = Real.exp (R*(Real.log C+κ))*
        (∑ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
          ∑ n∈s uv.1 uv.2,
            ‖phaseActualAmplifierCoefficient T f A uv.1‖*
              ‖phaseActualAmplifierCoefficient T g B uv.2‖/
                Real.sqrt (positiveQuadProduct n : ℝ)) := by simp_rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (actualAmplifiedNearAFE_mass_le_harmonic T A B f g hF hG hf hg
        hU hV hL hJ hQ s hs) (Real.exp_pos (R*(Real.log C+κ))).le

theorem bblrAFEDenominatorInv_raw_grid_norm_le
    {T R ε : ℝ} (hT : 0 < T) (hlog : 1 ≤ Real.log T) (hR : 0 ≤ R)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖ ≤ R) (m : Fin 6)
    (k n : Fin 4 → ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+ε)))
    (hw : rectangularAFESmoothWeight k n≠0) :
    ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+bblrSixShifts (rawMomentShifts T σ) m j))⁻¹‖ ≤
      Real.exp (R*(Real.log 16+(2+ε)))/Real.sqrt (positiveQuadProduct n : ℝ) :=
  bblrAFEDenominatorInv_six_raw_norm_le_of_product_cutoff hT hlog (by norm_num) hR
    σ hσ m n (rectangular_AFE_smooth_grid_integer_product_le k n hk hw)

theorem bblrAFEDenominatorInv_raw_grid_uniform_norm_le
    {R : ℝ} (hR : 0 ≤ R) (ε : ℝ) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ σ : MomentShifts,
      (∀ j, ‖σ j‖ ≤ R) → ∀ m : Fin 6, ∀ k n : Fin 4 → ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+ε)) → rectangularAFESmoothWeight k n≠0 →
      ‖(∏ j : Fin 4, (n j+1 : ℂ)^(1/2+bblrSixShifts (rawMomentShifts T σ) m j))⁻¹‖ ≤
        Real.exp (R*(Real.log 16+(2+ε)))/Real.sqrt (positiveQuadProduct n : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop (0:ℝ),
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1:ℝ))] with T hT hlog
  intro σ hσ m k n hk hw
  exact bblrAFEDenominatorInv_raw_grid_norm_le hT hlog hR σ hσ m k n hk hw

theorem phaseActualAmplifierPairConstant_norm_le_reciprocal_sqrt
    (T : ℝ) (f g : ℝ → ℝ) {F G : ℝ} (hF : 0≤F) (_hG : 0≤G)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G) (u w : ℕ) :
    ‖phaseActualAmplifierPairConstant T f g u w‖ ≤
      F*G/(Real.sqrt (u+1:ℝ)*Real.sqrt (w+1:ℝ)) := by
  have hp (a : ℕ) : ‖(a+1:ℂ)^(-(1/2:ℂ))‖=1/Real.sqrt (a+1:ℝ) := by
    rw [show (a+1:ℂ)=((a+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    norm_num
    rw [Real.rpow_neg (by positivity : (0:ℝ)≤a+1),← Real.sqrt_eq_rpow]
  unfold phaseActualAmplifierPairConstant
  simp only [norm_mul,Complex.norm_real,hp]
  calc
    _ ≤ F*G*(1/Real.sqrt (u+1:ℝ))*(1/Real.sqrt (w+1:ℝ)) := by
      gcongr
      · exact hf _
      · exact hg _
    _ = _ := by ring

theorem a03ActualMellinStaticFactor_raw_grid_norm_le
    {T R η c : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hR : 0≤R) (hc : 0≤c)
    (f g : ℝ → ℝ) {F G : ℝ} (hF : 0≤F) (hG : 0≤G)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R) (m : Fin 6)
    (k n : Fin 4 → ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+η)))
    (hw : rectangularAFESmoothWeight k n≠0) (u w : ℕ) (v : ℝ) :
    ‖a03ActualMellinStaticFactor T f g (bblrSixShifts (rawMomentShifts T σ) m)
        u w n ((c:ℂ)+(v:ℂ)*I)‖ ≤
      F*G*Real.exp (R*(Real.log 16+(2+η)))*
        positiveNearFactorWeight (u+1) (w+1) (bblrAFEFactorPairs n) := by
  have hden : Real.sqrt ((u+1:ℝ)*(w+1)*((n 0+1)*(n 1+1) : ℕ)*
      ((n 2+1)*(n 3+1) : ℕ))=
      Real.sqrt (u+1:ℝ)*Real.sqrt (w+1:ℝ)*Real.sqrt (positiveQuadProduct n : ℝ) := by
    rw [← Real.sqrt_mul (by positivity : (0:ℝ)≤u+1),
      ← Real.sqrt_mul (by positivity : (0:ℝ)≤(u+1:ℝ)*(w+1))]
    congr 1
    simp only [positiveQuadProduct,Nat.cast_mul]
    ring
  have hvertical := bblrAFEDenominatorInv_vertical_norm_le
    (bblrSixShifts (rawMomentShifts T σ) m) n ((c:ℂ)+(v:ℂ)*I) (by simpa using hc)
  have hraw := bblrAFEDenominatorInv_raw_grid_norm_le hT hlog hR σ hσ m k n hk hw
  unfold a03ActualMellinStaticFactor
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (F*G/(Real.sqrt (u+1:ℝ)*Real.sqrt (w+1:ℝ)))*
        (Real.exp (R*(Real.log 16+(2+η)))/Real.sqrt (positiveQuadProduct n : ℝ)) :=
      mul_le_mul
        (phaseActualAmplifierPairConstant_norm_le_reciprocal_sqrt T f g hF hG hf hg u w)
        (hvertical.trans hraw) (by positivity) (by positivity)
    _ = _ := by
      unfold positiveNearFactorWeight bblrAFEFactorPairs
      simp only [Nat.cast_add,Nat.cast_one]
      rw [hden]
      ring

end
end Sechstmoment
