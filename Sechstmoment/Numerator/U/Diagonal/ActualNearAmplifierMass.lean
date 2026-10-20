import Sechstmoment.Numerator.U.Diagonal.ActualNearFactorMass
import Sechstmoment.Numerator.U.Separation.ActualAmplifierCoefficients


namespace Sechstmoment
open Complex Real Source
open scoped BigOperators
open Classical
noncomputable section

theorem phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt
    (T A : ℝ) (f : ℝ → ℝ) {F : ℝ} (_hF : 0≤F)
    (hf : ∀ x, ‖f x‖≤F) {u : ℕ} (hu : 0<u) :
    ‖phaseActualAmplifierCoefficient T f A u‖≤F/Real.sqrt (u:ℝ) := by
  have hup : (0:ℝ)<u := by exact_mod_cast hu
  have hp : ‖(u:ℂ)^(-(1/2:ℂ))‖=1/Real.sqrt (u:ℝ) := by
    have hp0 : ‖(u:ℂ)^(-(1/2:ℂ))‖=(u:ℝ)^(-(1/2:ℝ)) := by
      simpa using Complex.norm_cpow_eq_rpow_re_of_pos hup (-(1/2:ℂ))
    rw [hp0]
    rw [Real.rpow_neg hup.le,← Real.sqrt_eq_rpow,one_div]
  unfold phaseActualAmplifierCoefficient
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real]
  rw [Real.norm_eq_abs,abs_of_nonneg (rectangularSmoothBlockWeight_nonneg _),hp]
  calc
    _ ≤ (1*F)*(1/Real.sqrt (u:ℝ)) := by
      gcongr
      · exact rectangularSmoothBlockWeight_le_one _
      · exact hf (Real.log (u:ℝ)/Real.log T)
    _ = _ := by ring

theorem actualNearAmplifierAFE_weight_le (T A B : ℝ) (f g : ℝ → ℝ)
    {F G : ℝ} (hF : 0≤F) (hG : 0≤G)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    {u v : ℕ} (hu : 0<u) (hv : 0<v) (n : Fin 4 → ℕ) :
    ‖phaseActualAmplifierCoefficient T f A u‖*
      ‖phaseActualAmplifierCoefficient T g B v‖/Real.sqrt (positiveQuadProduct n : ℝ)≤
        F*G*positiveNearFactorWeight u v (bblrAFEFactorPairs n) := by
  have hden : Real.sqrt ((u:ℝ)*v*((n 0+1)*(n 1+1) : ℕ)*
      ((n 2+1)*(n 3+1) : ℕ))=
      Real.sqrt (u:ℝ)*Real.sqrt (v:ℝ)*Real.sqrt (positiveQuadProduct n : ℝ) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg u),
      ← Real.sqrt_mul (mul_nonneg (Nat.cast_nonneg u) (Nat.cast_nonneg v))]
    congr 1
    simp only [positiveQuadProduct,Nat.cast_mul]
    ring
  calc
    _ ≤ (F/Real.sqrt (u:ℝ))*(G/Real.sqrt (v:ℝ))/
        Real.sqrt (positiveQuadProduct n : ℝ) := by
      gcongr
      · exact phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T A f hF hf hu
      · exact phaseActualAmplifierCoefficient_norm_le_reciprocal_sqrt T B g hG hg hv
    _ = _ := by unfold positiveNearFactorWeight bblrAFEFactorPairs; rw [hden]; ring

theorem actualAmplifiedNearAFE_mass_le_harmonic
    (T A B : ℝ) (f g : ℝ → ℝ) {F G : ℝ} (hF : 0≤F) (hG : 0≤G)
    (hf : ∀ x, ‖f x‖≤F) (hg : ∀ x, ‖g x‖≤G)
    {U Umax V Vmax L P J Q H K : ℕ}
    (hU : 0<U) (hV : 0<V) (hL : 0<L) (hJ : 0<J) (hQ : Q≤K^2)
    (s : ℕ → ℕ → Finset (Fin 4 → ℕ))
    (hs : ∀ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
      ∀ n∈s uv.1 uv.2,
        bblrAFEFactorPairs n ∈ positiveNearFactorBlock L P J Q uv.1 uv.2 H) :
    (∑ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
      ∑ n∈s uv.1 uv.2,
        ‖phaseActualAmplifierCoefficient T f A uv.1‖*
          ‖phaseActualAmplifierCoefficient T g B uv.2‖/
            Real.sqrt (positiveQuadProduct n : ℝ))≤
      F*G*(((Umax+1-U)*(Vmax+1-V) : ℕ):ℝ)*(P:ℝ)*(harmonic P : ℝ)*
        (2*(2*(H:ℝ)/(V:ℝ)+1)*(harmonic K : ℝ)+2*K)/
          Real.sqrt ((U:ℝ)*V*L*J) := by
  have hFG : 0≤F*G := mul_nonneg hF hG
  calc
    _ ≤ ∑ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
        F*G*(∑ pq∈positiveNearFactorBlock L P J Q uv.1 uv.2 H,
          positiveNearFactorWeight uv.1 uv.2 pq) := by
      apply Finset.sum_le_sum
      intro uv huv
      obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
      have hup : 0<uv.1 := hU.trans_le (Finset.mem_Icc.mp hu).1
      have hvp : 0<uv.2 := hV.trans_le (Finset.mem_Icc.mp hv).1
      have hsub : (s uv.1 uv.2).image bblrAFEFactorPairs ⊆
          positiveNearFactorBlock L P J Q uv.1 uv.2 H := by
        intro pq hpq
        obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hpq
        exact hs uv huv n hn
      calc
        _ ≤ ∑ n∈s uv.1 uv.2,
            F*G*positiveNearFactorWeight uv.1 uv.2 (bblrAFEFactorPairs n) :=
          Finset.sum_le_sum (fun n _ => actualNearAmplifierAFE_weight_le T A B f g
            hF hG hf hg hup hvp n)
        _ = F*G*(∑ pq∈(s uv.1 uv.2).image bblrAFEFactorPairs,
            positiveNearFactorWeight uv.1 uv.2 pq) := by
          rw [Finset.mul_sum,Finset.sum_image]
          exact fun _ _ _ _ h => bblrAFEFactorPairs_injective h
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub
            (fun pq _ _ => positiveNearFactorWeight_nonneg uv.1 uv.2 pq)) hFG
    _ = F*G*(∑ uv∈(Finset.Icc U Umax) ×ˢ (Finset.Icc V Vmax),
        ∑ pq∈positiveNearFactorBlock L P J Q uv.1 uv.2 H,
          positiveNearFactorWeight uv.1 uv.2 pq) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left
        (amplifiedPositiveNearFactorBlock_mass_le_harmonic hU hV hL hJ hQ) hFG using 1
      ring

end
end Sechstmoment
