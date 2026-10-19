import Sechstmoment.Numerator.U.Separation.Frequency.ActualDualFarKernel
import Sechstmoment.Numerator.U.Separation.SmallContour.GridBounds

/-! Literal finite original and dual amplified far contributions have a
uniform arbitrary-power budget after the true time integration. -/
namespace Sechstmoment
open Complex Source Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 1500000

theorem a03ActualMellinStaticFactor_norm_le
    {F G c : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hc : 0 ≤ c)
    (T : ℝ) (f g : ℝ → ℝ) (hf : ∀ x, ‖f x‖ ≤ F) (hg : ∀ x, ‖g x‖ ≤ G)
    (α : MomentShifts) (hα : ∀ j, ‖α j‖ ≤ 1/4)
    (u w : ℕ) (n : Fin 4 → ℕ) (v : ℝ) :
    ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖ ≤ F*G := by
  have hn (j : Fin 4) : 1 ≤ (n j+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) (n j)]
  have hcp (j : Fin 4) : ‖(n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖ =
      (n j+1:ℝ)^(1/2+(α j).re+c) := by
    rw [show (n j+1:ℂ) = ((n j+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le (hn j))]
    congr 1
    simp
  have hden : 1 ≤ ‖∏ j : Fin 4, (n j+1:ℂ)^(1/2+α j+((c:ℂ)+(v:ℂ)*I))‖ := by
    rw [norm_prod]
    simp_rw [hcp]
    have hh := Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin 4 => (1:ℝ))
      (g := fun j => (n j+1:ℝ)^(1/2+(α j).re+c)) (fun _ _ => zero_le_one) (fun j _ => by
        have ha := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
        exact Real.one_le_rpow (hn j) (by linarith))
    simpa only [Finset.prod_const_one] using hh
  have hp (m : ℕ) : ‖(m+1:ℂ)^(-(1/2:ℂ))‖ ≤ 1 := by
    rw [show (m+1:ℂ) = ((m+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Nat.cast_nonneg (α := ℝ) m]) (by norm_num)
  have hpair : ‖phaseActualAmplifierPairConstant T f g u w‖ ≤ F*G := by
    unfold phaseActualAmplifierPairConstant
    simp only [norm_mul,Complex.norm_real]
    calc
      _ ≤ (F*G)*1*1 := by
        gcongr
        · exact hf _
        · exact hg _
        · exact hp u
        · exact hp w
      _ = _ := by ring
  unfold a03ActualMellinStaticFactor
  rw [norm_div]
  exact (div_le_div_of_nonneg_right hpair (zero_lt_one.trans_le hden).le).trans
    (div_le_self (mul_nonneg hF hG) hden)

def a03ActualFarSelection (T ρ : ℝ) (positive : Bool)
    (u w : ℕ) (n : Fin 4 → ℕ) : Prop :=
  (if positive then rectangularPositiveQuadGap (u+1) (w+1) n
    else rectangularNegativeQuadGap (u+1) (w+1) n) ∧
  T^(ρ-1)*Real.sqrt ((u+1:ℝ)*(w+1)*(n 0+1)*(n 1+1)*(n 2+1)*(n 3+1)) ≤
    (rectangularAFEGap positive (u+1) (w+1) n:ℝ)

def a03ActualFarFiniteMellinGrid (dual positive : Bool) (c T a b ε ρ v : ℝ)
    (f g Φ : ℝ → ℝ) (σ α : MomentShifts) : ℂ :=
  ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k,
      if a03ActualFarSelection T ρ positive u w n then
        (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
          rectangularMomentPairWeight T f g Φ u w t*
          (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
          rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I))
      else 0

theorem a03_finite_amplifier_grid_norm_le_card
    (T a b ε : ℝ) (q : ℕ → ℕ → (Fin 4 → ℕ) → (Fin 4 → ℕ) → ℂ)
    {B : ℝ} (_hB : 0 ≤ B) (hq : ∀ u w k n, ‖q u w k n‖ ≤ B) :
    ‖∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
      ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k,
        q u w k n‖ ≤ B*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*
          (∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ((rectangularAFESmoothBox k).card:ℝ)) := by
  calc
    _ ≤ ∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k,
          ‖q u w k n‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro u _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro w _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => norm_sum_le _ _))
    _ ≤ ∑ _u∈Finset.range ⌊T^a⌋₊, ∑ _w∈Finset.range ⌊T^b⌋₊,
        ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ _n∈rectangularAFESmoothBox k, B := by
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro w _
      apply Finset.sum_le_sum
      intro k _
      exact Finset.sum_le_sum (fun n _ => hq u w k n)
    _ = _ := by simp [Finset.mul_sum,mul_comm,mul_left_comm,mul_assoc]


theorem a03_actual_far_finite_grid_uniform_rapid
    {a b c ε κ θ R ρ : ℝ} {f g Φ : ℝ → ℝ}
    (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g)
    (hΦ : SmoothDyadicWeight Φ) (hc : 0<c) (hc1 : c≤1) (hε : 0<ε)
    (hκ : 0<κ) (hθ : 0≤θ) (hR : 0≤R) (hρ : 0<ρ) (hρ1 : ρ≤1) (M : ℝ) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ T : ℝ in atTop, ∀ σ α : MomentShifts,
      (∀ j, ‖σ j‖≤R) → (∀ j, ‖α j‖≤1/4) →
      (∀ j : PurePolarIndex, κ≤‖normalizedPurePolarRoot σ j‖) →
      ∀ v : ℝ, |v|≤θ*Real.log T → ∀ dual positive : Bool,
      ‖a03ActualFarFiniteMellinGrid dual positive c T a b ε ρ v f g Φ σ α‖≤C*T^(-M) := by
  obtain ⟨F,hF,hfb⟩ := rectangular_supported_profile_bounded f hf
  obtain ⟨G,hG,hgb⟩ := rectangular_supported_profile_bounded g hg
  let Q : ℝ := M+a+b+3+ε
  obtain ⟨C₀,hC₀,hb₀⟩ := a03_actual_amplified_all_far_kernel_uniform_rapid
    hΦ hc hc1 (show 2*c<2*c+1 by linarith) hκ hθ (show (0:ℝ)≤1/4 by norm_num) hρ hρ1 Q
  obtain ⟨C₁,hC₁,hb₁⟩ := a03_actual_amplified_all_far_dual_kernel_uniform_rapid
    hΦ hc hc1 (show 2*c<2*c+1 by linarith) hκ hθ (show (0:ℝ)≤1/4 by norm_num) hR hρ hρ1 Q
  obtain ⟨D,hD,hcard⟩ := rectangular_small_contour_grid_uniform_polynomial_card hε
  let L : ℝ := F*G*(C₀+C₁)
  have hL : 0≤L := by dsimp [L]; positivity
  refine ⟨L*D,mul_nonneg hL hD,?_⟩
  filter_upwards [hb₀,hb₁,hcard,eventually_ge_atTop (1:ℝ)] with T hb₀ hb₁ hcard hT
  intro σ α hσ hα hroot v hv dual positive
  have ht0 : 0<T := zero_lt_one.trans_le hT
  have hkernel (u w : ℕ) (n : Fin 4 → ℕ) (hs : a03ActualFarSelection T ρ positive u w n) :
      ‖∫ t : ℝ, rectangularMomentPairWeight T f g Φ u w t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)‖≤L*T^(-Q) := by
    have hstatic := a03ActualMellinStaticFactor_norm_le hF hG hc.le T f g hfb hgb α hα u w n v
    have hb : ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*
        (C₀+C₁)*T^(-Q)≤L*T^(-Q) := by
      dsimp only [L]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hstatic (by positivity))
        (by positivity)
    cases dual
    · simp only [Bool.false_eq_true,ite_false,mul_one]
      exact (hb₀ σ α hα hroot v hv f g positive u w n hs.1 hs.2).trans
        ((by gcongr; linarith :
          ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C₀*T^(-Q)≤
          ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*(C₀+C₁)*T^(-Q)).trans hb)
    · simp only [ite_true]
      exact (hb₁ σ α hσ hα hroot v hv f g positive u w n hs.1 hs.2).trans
        ((by gcongr; linarith :
          ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*C₁*T^(-Q)≤
          ‖a03ActualMellinStaticFactor T f g α u w n ((c:ℂ)+(v:ℂ)*I)‖*(C₀+C₁)*T^(-Q)).trans hb)
  let q := fun (u w : ℕ) (k n : Fin 4 → ℕ) =>
    if a03ActualFarSelection T ρ positive u w n then
      (rectangularAFESmoothWeight k n:ℂ)*(∫ t : ℝ,
        rectangularMomentPairWeight T f g Φ u w t*
        (if dual then bblrDualMultiplier t (rawMomentShifts T σ) else 1)*
        rectangularAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I)) else 0
  have hq (u w : ℕ) (k n : Fin 4 → ℕ) : ‖q u w k n‖≤L*T^(-Q) := by
    dsimp only [q]
    by_cases hs : a03ActualFarSelection T ρ positive u w n
    · rw [ite_eq_left hs,norm_mul,Complex.norm_real,Real.norm_of_nonneg (rectangular_AFE_smooth_weight_nonneg k n)]
      calc
        _ ≤ rectangularAFESmoothWeight k n*(L*T^(-Q)) := mul_le_mul_of_nonneg_left
          (hkernel u w n hs) (rectangular_AFE_smooth_weight_nonneg k n)
        _ ≤ L*T^(-Q) := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right
            (rectangular_small_contour_smooth_weight_le_one k n) (by positivity : 0≤L*T^(-Q))
    · rw [ite_eq_right hs,norm_zero]
      positivity
  change ‖∑ u∈Finset.range ⌊T^a⌋₊, ∑ w∈Finset.range ⌊T^b⌋₊,
    ∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ∑ n∈rectangularAFESmoothBox k,
      q u w k n‖≤(L*D)*T^(-M)
  calc
    _ ≤ (L*T^(-Q))*(⌊T^a⌋₊:ℝ)*(⌊T^b⌋₊:ℝ)*
        (∑ k∈rectangularAFEProductScaleGrid (T^(2+ε)), ((rectangularAFESmoothBox k).card:ℝ)) :=
      a03_finite_amplifier_grid_norm_le_card T a b ε q (by positivity) hq
    _ ≤ (L*T^(-Q))*T^a*T^b*(D*T^(3+ε)) := by
      have hna : (⌊T^a⌋₊:ℝ)≤T^a := Nat.floor_le (Real.rpow_nonneg ht0.le _)
      have hnb : (⌊T^b⌋₊:ℝ)≤T^b := Nat.floor_le (Real.rpow_nonneg ht0.le _)
      have hp : 0≤L*T^(-Q) := mul_nonneg hL (Real.rpow_nonneg ht0.le _)
      have hpa : (L*T^(-Q))*(⌊T^a⌋₊:ℝ)≤(L*T^(-Q))*T^a :=
        mul_le_mul_of_nonneg_left hna hp
      have hpab := mul_le_mul hpa hnb (Nat.cast_nonneg ⌊T^b⌋₊)
        (mul_nonneg hp (Real.rpow_nonneg ht0.le a))
      exact mul_le_mul hpab hcard (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
        (mul_nonneg (mul_nonneg hp (Real.rpow_nonneg ht0.le a)) (Real.rpow_nonneg ht0.le b))
    _ = (L*D)*T^((-Q+a+b)+(3+ε)) := by
      rw [Real.rpow_add ht0 (-Q+a+b) (3+ε),Real.rpow_add ht0 (-Q+a) b,
        Real.rpow_add ht0 (-Q) a]
      ring
    _ = _ := by congr 2; dsimp [Q]; ring

end
