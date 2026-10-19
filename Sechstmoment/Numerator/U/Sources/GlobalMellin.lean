import Sechstmoment.Numerator.U.Diagonal.RawShiftFactorMass
import Sechstmoment.Numerator.U.Sources.GlobalSupport

/-! The actual scale-only Mellin factor preserves the four reciprocal
square-root AFE lengths uniformly on bounded normalized shifts. -/
namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

def a03SourceMellinScaleFactor (c v : ℝ) (α : MomentShifts) (k : Fin 4 → ℕ) : ℂ :=
  ∏ j : Fin 4, (rectangularAFESmoothScale (k j):ℂ)^(-(1/2+α j+((c:ℂ)+(v:ℂ)*I)))

theorem a03_source_scaled_real_power_bound {x r R c : ℝ}
    (hx : 2/3≤x) (_hr : 0≤r) (hrR : r≤R) (hc : 0≤c) (hc1 : c≤1)
    (α : ℂ) (hα : ‖α‖≤r) :
    x^(-(1/2+α.re+c))≤(3/2:ℝ)^(3/2+R)*((3/2)*x)^(r-1/2) := by
  have hxp : 0<x := by linarith
  have hy : 1≤(3/2)*x := by linarith
  have hαre := abs_le.mp ((Complex.abs_re_le_norm α).trans hα)
  have he : x^(-(1/2+α.re+c))=
      ((3/2:ℝ)*x)^(-(1/2+α.re+c))*(3/2:ℝ)^(1/2+α.re+c) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤3/2) hxp.le]
    symm
    calc
      _=((3/2:ℝ)^(-(1/2+α.re+c))*(3/2:ℝ)^(1/2+α.re+c))*x^(-(1/2+α.re+c)) := by ring
      _=_ := by
        rw [←Real.rpow_add (by norm_num : (0:ℝ)<3/2),show -(1/2+α.re+c)+(1/2+α.re+c)=(0:ℝ) by ring]
        simp
  rw [he]
  calc
    _≤((3/2:ℝ)*x)^(r-1/2)*(3/2:ℝ)^(3/2+R) := mul_le_mul
      (Real.rpow_le_rpow_of_exponent_le hy (by linarith))
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤3/2) (by linarith))
      (by positivity) (by positivity)
    _=_ := by ring

/-- The displayed scale factor has exactly the reciprocal square-root
AFE length.  Integer-one scale blocks are included in the fixed constant. -/
theorem a03SourceMellinScaleFactor_raw_norm_le
    {T R c u : ℝ} (hT : 0<T) (hlog : 1≤Real.log T) (hR : 0≤R)
    (hc : 0≤c) (hc1 : c≤1) (σ : MomentShifts) (hσ : ∀ j, ‖σ j‖≤R)
    (m : Fin 6) (k : Fin 4 → ℕ) (hk : k∈rectangularAFEProductScaleGrid (T^(2+u))) (v : ℝ) :
    ‖a03SourceMellinScaleFactor c v (bblrSixShifts (rawMomentShifts T σ) m) k‖≤
      (((3/2:ℝ)^(3/2+R))^4*Real.exp (R*(Real.log ((3/2:ℝ)^4)+(2+u))))/
        Real.sqrt ((phaseActualScales 1 1 1 k).M*(phaseActualScales 1 1 1 k).N) := by
  let q := phaseActualScales 1 1 1 k
  let x : Fin 4 → ℝ := fun j => rectangularAFESmoothScale (k j)
  let y : Fin 4 → ℝ := fun j => (3/2)*x j
  let r := R/Real.log T
  have hL : 0<Real.log T := zero_lt_one.trans_le hlog
  have hr : 0≤r := div_nonneg hR hL.le
  have hrR : r≤R := div_le_self hR hlog
  have hx (j : Fin 4) : 2/3≤x j := by
    unfold x rectangularAFESmoothScale
    apply (le_div_iff₀ (by norm_num : (0:ℝ)<3/2)).mpr
    norm_num
    exact one_le_pow₀ (by norm_num)
  have hxp (j : Fin 4) : 0<x j := by linarith [hx j]
  have hy (j : Fin 4) : 1≤y j := by dsimp [y]; linarith [hx j]
  have hyp : 0<(∏ j : Fin 4, y j) := Finset.prod_pos (fun j _ => zero_lt_one.trans_le (hy j))
  have hraw : ∀ j, ‖bblrSixShifts (rawMomentShifts T σ) m j‖≤r := by
    apply bblrSixShifts_norm_le
    intro j
    rw [rawMomentShifts,norm_div,Complex.norm_real,Real.norm_of_nonneg hL.le]
    exact div_le_div_of_nonneg_right (hσ j) hL.le
  have hprodX : (∏ j : Fin 4, x j)=q.M*q.N := by
    simp [x,q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
  have hprodY : (∏ j : Fin 4, y j)=(3/2:ℝ)^4*(q.M*q.N) := by
    simp only [y,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,hprodX]
  have hcut : (∏ j : Fin 4, y j)≤(3/2:ℝ)^4*T^(2+u) := by
    rw [hprodY]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
      using (Finset.mem_filter.mp hk).2
  have hpow := bblrRawShift_product_rpow_le hT hlog
    (show (1:ℝ)≤(3/2:ℝ)^4 by norm_num) hR hyp hcut
  have hden : Real.sqrt (q.M*q.N)≤Real.sqrt (∏ j : Fin 4, y j) := by
    apply Real.sqrt_le_sqrt
    rw [hprodY]
    have hMN0 : 0≤q.M*q.N := by rw [←hprodX]; exact Finset.prod_nonneg (fun j _ => (hxp j).le)
    nlinarith
  have hdenpos : 0<Real.sqrt (q.M*q.N) := by
    apply Real.sqrt_pos.mpr
    rw [←hprodX]
    exact Finset.prod_pos (fun j _ => hxp j)
  unfold a03SourceMellinScaleFactor
  rw [norm_prod]
  calc
    _≤∏ j : Fin 4, (3/2:ℝ)^(3/2+R)*(y j)^(r-1/2) := by
      apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
      intro j _
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (hxp j)]
      have he : (-(1/2+bblrSixShifts (rawMomentShifts T σ) m j+((c:ℂ)+(v:ℂ)*I)):ℂ).re=
          -(1/2+(bblrSixShifts (rawMomentShifts T σ) m j).re+c) := by simp
      rw [he]
      exact a03_source_scaled_real_power_bound (hx j) hr hrR hc hc1 _ (hraw j)
    _=((3/2:ℝ)^(3/2+R))^4*(∏ j : Fin 4, y j)^(r-1/2) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        Real.finsetProd_rpow Finset.univ y (fun j _ => (zero_lt_one.trans_le (hy j)).le)]
    _=((3/2:ℝ)^(3/2+R))^4*((∏ j : Fin 4, y j)^r/Real.sqrt (∏ j : Fin 4, y j)) := by
      rw [Real.rpow_sub hyp,←Real.sqrt_eq_rpow]
    _≤((3/2:ℝ)^(3/2+R))^4*(Real.exp (R*(Real.log ((3/2:ℝ)^4)+(2+u)))/Real.sqrt (q.M*q.N)) :=
      mul_le_mul_of_nonneg_left (div_le_div₀ (by positivity) hpow hdenpos hden) (by positivity)
    _=_ := by ring

end
end Sechstmoment
