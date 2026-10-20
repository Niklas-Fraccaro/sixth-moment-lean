import Sechstmoment.Numerator.U.Sources.GlobalMajorant

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem phaseActualActiveNearBlock_mono {T A B H η ρ : ℝ} (f g : ℝ → ℝ)
    (k : Fin 4 → ℕ) (hηρ : η≤ρ)
    (h : phaseActualActiveNearBlock T A B H η f g k) :
    phaseActualActiveNearBlock T A B H ρ f g k := by
  rcases h with ⟨p,q,h,n,positive,hp,hq,hw,hh,hrel,hnear⟩
  refine ⟨p,q,h,n,positive,hp,hq,hw,hh,hrel,?_⟩
  exact hnear.trans (mul_le_mul_of_nonneg_right hηρ (Real.sqrt_nonneg _))

theorem rectangularAFEProductScaleGrid_mono {X Y : ℝ} (hX : 0<X) (hY : 0<Y)
    (hXY : X≤Y) : rectangularAFEProductScaleGrid X⊆rectangularAFEProductScaleGrid Y := by
  intro k hk
  apply (rectangular_AFE_product_scale_grid_mem_iff hY k).mpr
  exact ((rectangular_AFE_product_scale_grid_mem_iff hX k).mp hk).trans hXY

theorem phase_actual_near_source_scale_budget {a b s u : ℝ}
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      let q := phaseActualScales A B H k
      A≤T^a ∧ B≤T^b ∧ q.M*q.N≤T^(2+u) ∧
      q.mass≤T^(a+b+2+u) ∧
      H≤(8*T^s)*(A*B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)/T ∧
      H≤8*T^((a+b)/2+s+u/2) := by
  obtain ⟨ν,_hν,hfν⟩ := phase_actual_nonzero_amplifier_lengths f hf
  obtain ⟨μ,_hμ,hgμ⟩ := phase_actual_nonzero_amplifier_lengths g hg
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  intro A B H hA hB hH k hk hactive
  let q := phaseActualScales A B H k
  obtain ⟨p,q0,h,n,positive,hp,hq0,hw,hh,hrel,hnear⟩ := hactive
  have hAe := (hfν T A hT hA p hp).2
  have hBe := (hgμ T B hT hB q0 hq0).2
  have hTp : 0<T := zero_lt_one.trans hT
  have hqp := boundaryActual_scales_pos A B H k hA hB hH
  have hMN : q.M*q.N≤T^(2+u) := by
    have h := (Finset.mem_filter.mp hk).2
    simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc] using h
  have hMN0 : 0≤q.M*q.N := by
    unfold q phaseActualScales QuadraticScales.M QuadraticScales.N
    have h0 := boundaryActual_scale_pos (k 0); have h1 := boundaryActual_scale_pos (k 1)
    have h2 := boundaryActual_scale_pos (k 2); have h3 := boundaryActual_scale_pos (k 3)
    positivity
  have hAB : A*B≤T^(a+b) := by
    have h := mul_le_mul hAe hBe hB.le (Real.rpow_nonneg hTp.le a)
    rwa [←Real.rpow_add hTp] at h
  have hmass : q.mass≤T^(a+b+2+u) := by
    have h := mul_le_mul hAB hMN hMN0 (Real.rpow_nonneg hTp.le (a+b))
    rw [←Real.rpow_add hTp] at h
    simpa [q,phaseActualScales,QuadraticScales.mass,mul_assoc,add_assoc] using h
  have htuple := phase_actual_source_tuple_support T A B H f g hA hB hH k n p q0 h hp hq0 hw hh
  have hgap := phase_active_near_gap_scale_bound q (fun j => (hqp j).le)
    (rectangularAFESourceTuple p q0 n h) htuple (Real.rpow_nonneg hTp.le (s-1)) hnear
  have hroot : Real.sqrt q.mass=Real.sqrt (A*B)*Real.sqrt (q.M*q.N) := by
    unfold QuadraticScales.mass
    change Real.sqrt (A*B*q.M*q.N)=_
    rw [show A*B*q.M*q.N=(A*B)*(q.M*q.N) by ring,Real.sqrt_mul (mul_pos hA hB).le]
  have hH0 : H≤(8*T^s)*(A*B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)/T := by
    have hgap0 := hgap
    change H≤_ at hgap0
    rw [hroot,Real.rpow_sub hTp,Real.rpow_one,Real.sqrt_eq_rpow] at hgap0
    convert hgap0 using 1
    ring
  have hmass0 : 0≤q.mass := by
    change 0≤A*B*q.M*q.N
    nlinarith [mul_nonneg (mul_nonneg hA.le hB.le) hMN0]
  have hrootmass : Real.sqrt q.mass≤T^((a+b+2+u)/2) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _≤(T^(a+b+2+u))^(1/2:ℝ) := Real.rpow_le_rpow hmass0 hmass (by norm_num)
      _=_ := by rw [←Real.rpow_mul hTp.le]; congr 1; ring
  have hHend : H≤8*T^((a+b)/2+s+u/2) := by
    calc
      H≤8*T^(s-1)*Real.sqrt q.mass := hgap
      _≤8*T^(s-1)*T^((a+b+2+u)/2) := mul_le_mul_of_nonneg_left hrootmass (by positivity)
      _=_ := by rw [mul_assoc,←Real.rpow_add hTp]; congr 2; ring
  exact ⟨hAe,hBe,hMN,hmass,hH0,hHend⟩

end
end Sechstmoment
