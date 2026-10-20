import SixthMoment.Numerator.U.ZeroModes.Ratio.GeometricTails
import SixthMoment.Numerator.U.ZeroModes.Ratio.SourceErrorAggregate

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem a03_actual_ratio_bad_source_geometric_power {a b s εsource : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (_hs0 : 0≤s) (hs : s≤1/2)
    (hε : 0<εsource) (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ γ A : ℝ,0<γ ∧ 0<A ∧ ∀ᶠ T : ℝ in atTop,
      ∀ i : (Fin 3→ℕ)×(Fin 4→ℕ),
      phaseActualActiveNearBlock T (rectangularAFESmoothScale (i.1 0))
        (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) (T^(s-1)) f g i.2 →
      ¬a03ActualRatioSourceGoodBlock T s εsource f g i →
      ∀ n : Fin 4→ℕ,rectangularAFESmoothWeight i.2 n≠0 →
        A*T^γ≤(n 0+1:ℝ)/(n 1+1:ℝ) ∨ A*T^γ≤(n 2+1:ℝ)/(n 3+1:ℝ) := by
  have hb : b<1/2 := by nlinarith
  let εinput := DivisorProof.inputExponent εsource 1
  have hεinput : 0<εinput := DivisorProof.inputExponent_pos hε (by norm_num : (0:ℝ)<1)
  let γ := min εinput (1/2-b)
  let C := (1/144:ℝ)^εinput/64
  let A := min C (1/4:ℝ)
  have hγ : 0<γ := lt_min hεinput (by linarith)
  have hC : 0<C := div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by norm_num)
  have hA : 0<A := lt_min hC (by norm_num)
  have hη : ∀ᶠ T : ℝ in atTop,T^(s-1)≤1/2 :=
    ((tendsto_order.1 (tendsto_rpow_neg_atTop (by linarith : 0<1-s))).2
      (1/2) (by norm_num)).mono (fun _ h => by simpa only [neg_sub] using h.le)
  refine ⟨γ,A,hγ,hA,?_⟩
  filter_upwards [hη,eventually_gt_atTop (1:ℝ)] with T hη hT
  have ht : 0<T := zero_lt_one.trans hT
  intro i hactive hbad n hn
  let native := phaseActualScales (rectangularAFESmoothScale (i.1 0))
    (rectangularAFESmoothScale (i.1 1)) (rectangularAFESmoothScale (i.1 2)) i.2
  let q := boundaryEmbeddedScales (boundaryActualFlags i.2) native
  have hm := a03_actual_near_embedded_mass_power_lower ht (boundaryActual_scale_pos _)
    (boundaryActual_scale_pos _) (boundaryActual_scale_ge_two_thirds _) f g i.2 hactive
  have hmp : 0≤q.mass := (by positivity : (0:ℝ)≤(1/144)*T^(2-2*s)).trans hm
  have hpow : C*T^εinput≤q.mass^εinput/64 := by
    have hh := Real.rpow_le_rpow (by positivity : (0:ℝ)≤(1/144)*T^(2-2*s)) hm hεinput.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤1/144) (Real.rpow_nonneg ht.le _),←Real.rpow_mul ht.le] at hh
    have hg := Real.rpow_le_rpow_of_exponent_le hT.le (show εinput≤(2-2*s)*εinput by nlinarith)
    have hc := mul_le_mul_of_nonneg_left hg (Real.rpow_nonneg (by norm_num : (0:ℝ)≤1/144) εinput)
    have he := div_le_div_of_nonneg_right (hc.trans hh) (by norm_num : (0:ℝ)≤64)
    simpa only [C,mul_div_assoc,div_mul_eq_mul_div] using he
  have hsmall : A*T^γ≤q.mass^εinput/64 := by
    apply le_trans ?_ hpow
    exact mul_le_mul (min_le_left _ _) (Real.rpow_le_rpow_of_exponent_le hT.le (min_le_left _ _))
      (Real.rpow_nonneg ht.le _) hC.le
  by_cases hM : q.M₁≤q.M₂*q.mass^εinput
  · by_cases hN : q.N₁≤q.N₂*q.mass^εinput
    · have hunit := a03_actual_near_integrated_unit_ratio_lower hT (boundaryActual_scale_pos _)
        (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) (Real.rpow_pos_of_pos ht _) hη f g hf hg i.2 n hactive hn
      have hscale (d : ℝ) (hd : d≤b) : A*T^γ≤1/(4*T^(s-1)*T^d) := by
        have he : 1/(4*T^(s-1)*T^d)=(1/4:ℝ)*T^(1-s-d) := by
          rw [mul_assoc,←Real.rpow_add ht]
          calc
            _=(1/4:ℝ)*(T^(s-1+d))⁻¹ := by ring
            _=(1/4:ℝ)*T^(-(s-1+d)) := by rw [Real.rpow_neg ht.le]
            _=_ := by congr 1; congr 1; ring
        rw [he]
        exact mul_le_mul (min_le_right _ _) (Real.rpow_le_rpow_of_exponent_le hT.le
          ((min_le_right _ _).trans (by linarith : (1/2:ℝ)-b≤1-s-d)))
          (Real.rpow_nonneg ht.le _) (by norm_num : (0:ℝ)≤1/4)
      by_cases hk1 : i.2 1=0
      · exact Or.inl ((hscale a hab).trans (hunit.1 hk1))
      · by_cases hk3 : i.2 3=0
        · exact Or.inr ((hscale b le_rfl).trans (hunit.2 hk3))
        · exact False.elim (hbad ⟨hactive,hM,hN,hk1,hk3⟩)
    · exact Or.inr (hsmall.trans (a03_actual_bad_soft_N_ratio (boundaryActual_scale_pos _)
        (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) i.2 n hn hN))
  · exact Or.inl (hsmall.trans (a03_actual_bad_soft_M_ratio (boundaryActual_scale_pos _)
      (boundaryActual_scale_pos _) (boundaryActual_scale_pos _) i.2 n hn hM))

end
end SixthMoment
