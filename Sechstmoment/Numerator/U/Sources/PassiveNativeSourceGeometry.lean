import Sechstmoment.Numerator.U.Sources.PassiveNativeSourceWitness

/-! Source geometry from actual continuous native-zero support and a low
integer gap. No discrete active-near witness is required. -/
namespace Sechstmoment
open Complex Real Source Set Filter MeasureTheory
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem A03PassiveNativeZeroWitness.scale_comparability {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) :
    let q := phaseActualScales A B H k
    q.A*q.M≤8*(q.B*q.N) ∧ q.B*q.N≤8*(q.A*q.M) := by
  constructor
  · simpa only [phaseActualScales, QuadraticScales.M, QuadraticScales.N, mul_assoc] using
      (p.left_product_bounds hA hB).1.trans (p.right_product_bounds hA hB).2
  · simpa only [phaseActualScales, QuadraticScales.M, QuadraticScales.N, mul_assoc] using
      (p.right_product_bounds hA hB).1.trans (p.left_product_bounds hA hB).2

theorem A03PassiveNativeZeroWitness.mass_product_bound {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) :
    p.X^2≤64*(phaseActualScales A B H k).mass := by
  have hl := (p.left_product_bounds hA hB).2
  have hr := (p.right_product_bounds hA hB).2
  have hm := mul_le_mul hl hr p.X_pos.le (p.X_pos.le.trans hl)
  calc
    p.X^2 = p.X*p.X := by ring
    _ ≤ (8*A*(rectangularAFESmoothScale (k 0)*rectangularAFESmoothScale (k 1))) *
      (8*B*(rectangularAFESmoothScale (k 2)*rectangularAFESmoothScale (k 3))) := hm
    _ = 64*(phaseActualScales A B H k).mass := by
      simp only [phaseActualScales, QuadraticScales.mass, QuadraticScales.M, QuadraticScales.N]
      ring

theorem A03PassiveNativeZeroWitness.gap_scale_bound {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B) (hH : 0<H) :
    H≤8*η*Real.sqrt (phaseActualScales A B H k).mass := by
  have hx := Real.sqrt_le_sqrt (p.mass_product_bound hA hB)
  rw [Real.sqrt_sq_eq_abs,abs_of_pos p.X_pos,Real.sqrt_mul (by norm_num : (0:ℝ)≤64),
    show Real.sqrt (64:ℝ)=8 by norm_num] at hx
  exact ((p.gap_support hH).1.trans p.low_gap).trans
    ((mul_le_mul_of_nonneg_left hx p.eta_pos.le).trans_eq (by ring))

theorem A03PassiveNativeZeroWitness.nontrivial_range {T A B H η : ℝ} {f g : ℝ→ℝ} {k : Fin 4→ℕ}
    (p : A03PassiveNativeZeroWitness T A B H η f g k) (hA : 0<A) (hB : 0<B)
    (hsmall : 8*η*(A*B)≤1) :
    A*B≤(phaseActualScales A B H k).M*(phaseActualScales A B H k).N := by
  have hx := p.mass_product_bound hA hB
  have hgap := p.gap_ge_one.trans p.low_gap
  have hAX : 8*(A*B)≤p.X := by nlinarith [p.eta_pos]
  have hsquare := mul_self_le_mul_self (by positivity : 0≤8*(A*B)) hAX
  have hAB := mul_pos hA hB
  change p.X^2≤64*(A*B*(phaseActualScales A B H k).M*(phaseActualScales A B H k).N) at hx
  by_contra h
  have hstrict := mul_pos hAB (sub_pos.mpr (lt_of_not_ge h))
  nlinarith

theorem a03_passive_native_source_nontrivial_uniform {d s : ℝ} (hexp : d+s<1) :
    ∀ᶠ T : ℝ in atTop,∀ A B H : ℝ,0<A → 0<B →
      A*B≤T^d → ∀ f g : ℝ→ℝ,∀ k : Fin 4→ℕ,
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      A*B≤(phaseActualScales A B H k).M*(phaseActualScales A B H k).N := by
  have ht : Tendsto (fun T : ℝ => T^(d+s-1)) atTop (nhds 0) := by
    simpa only [neg_neg] using tendsto_rpow_neg_atTop (show 0 < -(d+s-1) by linarith)
  have hsmall : ∀ᶠ T : ℝ in atTop,T^(d+s-1)≤1/8 :=
    ((tendsto_order.1 ht).2 (1/8) (by norm_num)).mono (fun _ h => h.le)
  filter_upwards [hsmall,eventually_gt_atTop (0:ℝ)] with T ht hT
  intro A B H hA hB hAB f g k hp
  rcases hp with ⟨p⟩
  apply p.nontrivial_range hA hB
  have hmul := mul_le_mul_of_nonneg_left hAB (Real.rpow_nonneg hT.le (s-1))
  have he : T^(s-1)*T^d=T^(d+s-1) := by rw [←Real.rpow_add hT]; congr 1; ring
  rw [he] at hmul
  nlinarith

theorem a03_passive_native_source_H_from_product_cutoff {T ρ ε s u : ℝ} (hT : 1≤T)
    (hε : 0≤ε) (hexp : s+u/2≤ρ*ε) (A B H : ℝ) (hA : 0<A) (hB : 0<B) (hH : 0<H)
    (hAB : T^ρ≤A*B) (k : Fin 4→ℕ)
    (hMN : (phaseActualScales A B H k).M*(phaseActualScales A B H k).N≤T^(2+u))
    (f g : ℝ→ℝ) (hp : A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k) :
    H≤8*(A*B)^(1/2+ε) := by
  rcases hp with ⟨p⟩
  have hTp : 0<T := zero_lt_one.trans_le hT
  let q := phaseActualScales A B H k
  have hMN0 : 0≤q.M*q.N := by
    unfold q phaseActualScales QuadraticScales.M QuadraticScales.N
    exact (mul_pos (mul_pos (boundaryActual_scale_pos _) (boundaryActual_scale_pos _))
      (mul_pos (boundaryActual_scale_pos _) (boundaryActual_scale_pos _))).le
  have hs : Real.sqrt (q.M*q.N)≤T^(1+u/2) := by
    rw [Real.sqrt_eq_rpow]
    apply (Real.rpow_le_rpow hMN0 hMN (by norm_num : (0:ℝ)≤1/2)).trans_eq
    rw [←Real.rpow_mul hTp.le]
    congr 1
    ring
  have he : T^(s-1)*Real.sqrt (q.M*q.N)≤(A*B)^ε := by
    calc
      _≤T^(s-1)*T^(1+u/2) := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hTp.le _)
      _=T^(s+u/2) := by rw [←Real.rpow_add hTp]; congr 1; ring
      _≤T^(ρ*ε) := Real.rpow_le_rpow_of_exponent_le hT hexp
      _=(T^ρ)^ε := Real.rpow_mul hTp.le _ _
      _≤(A*B)^ε := Real.rpow_le_rpow (Real.rpow_nonneg hTp.le _) hAB hε
  have hgap := p.gap_scale_bound hA hB hH
  have hmass : Real.sqrt q.mass=Real.sqrt (A*B)*Real.sqrt (q.M*q.N) := by
    change Real.sqrt (A*B*q.M*q.N)=_
    rw [show A*B*q.M*q.N=(A*B)*(q.M*q.N) by ring,Real.sqrt_mul (mul_pos hA hB).le]
  rw [hmass] at hgap
  calc
    _≤8*T^(s-1)*(Real.sqrt (A*B)*Real.sqrt (q.M*q.N)) := hgap
    _=8*Real.sqrt (A*B)*(T^(s-1)*Real.sqrt (q.M*q.N)) := by ring
    _≤8*Real.sqrt (A*B)*(A*B)^ε := mul_le_mul_of_nonneg_left he (by positivity)
    _=8*(A*B)^(1/2+ε) := by rw [Real.sqrt_eq_rpow,mul_assoc,←Real.rpow_add (mul_pos hA hB)]

theorem a03_actual_passive_power_near_soft_source_geometry {a b ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hε : 0<ε)
    (f g : ℝ→ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∃ s u : ℝ,0<s ∧ s<1/2 ∧ 0<u ∧ ∀ᶠ T : ℝ in atTop,
      ∀ A B H : ℝ,2/3≤A → 2/3≤B → 2/3≤H → ∀ k : Fin 4→ℕ,
      k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
      q.M₁≤q.M₂*q.mass^ε → q.N₁≤q.N₂*q.mass^ε →
      phaseSourceGeometry ε 32 (a03SoftSourceOrientedScales q) := by
  obtain ⟨ρ,hρ,hρT⟩ := phase_actual_amplifier_product_lengths f g hf hg
  obtain ⟨s,u,hs,hs2,hu,hsu,hslen⟩ := phase_source_auxiliary_exponents ha hab hlen hρ hε
  refine ⟨s,u,hs,hs2,hu,?_⟩
  filter_upwards [hρT,a03_passive_native_source_nontrivial_uniform hslen,eventually_ge_atTop (1:ℝ)]
    with T hρT hnontrivial hT
  intro A B H hA hB hH k hk hpassive
  dsimp only
  intro hmsoft hnsoft
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  obtain ⟨p⟩ := hpassive
  have hAB := hρT A B hAp hBp (p.w 0) (p.w 1) p.alpha_nonzero p.beta_nonzero
  let q := phaseActualScales A B H k
  have hMN : q.M*q.N≤T^(2+u) := by
    simpa [q,phaseActualScales,QuadraticScales.M,QuadraticScales.N,Fin.prod_univ_four,mul_assoc]
      using (Finset.mem_filter.mp hk).2
  have hgapshape := a03_passive_native_source_H_from_product_cutoff hT hε.le hsu.le A B H hAp hBp hHp
    hAB.1 k hMN f g ⟨p⟩
  have hnontriv := hnontrivial A B H hAp hBp hAB.2 f g k ⟨p⟩
  have hcompare := p.scale_comparability hAp hBp
  let q' := boundaryEmbeddedScales (boundaryActualFlags k) q
  have hq' : ∀ j,1≤q'.size j := boundaryActual_embedded_lower_bounds A B H k hA hB hH
  have hH' : q'.H≤32*(q'.A*q'.B)^(1/2+ε) := by
    simpa only [show (4:ℝ)*8=32 by norm_num] using boundaryEmbedded_gap_shape (boundaryActualFlags k) q
      (by norm_num : (0:ℝ)≤8) hε.le (mul_pos hAp hBp) hgapshape
  have hn' : q'.A*q'.B≤32*q'.M*q'.N := by
    have h := boundaryEmbedded_nontrivial_range (boundaryActualFlags k) q hnontriv
    have hp : 0≤q'.M*q'.N := by
      unfold QuadraticScales.M QuadraticScales.N
      exact mul_nonneg (mul_nonneg (zero_le_one.trans (hq' 2)) (zero_le_one.trans (hq' 3)))
        (mul_nonneg (zero_le_one.trans (hq' 4)) (zero_le_one.trans (hq' 5)))
    exact h.trans (by nlinarith)
  have hcomp' := boundaryEmbedded_comparability (boundaryActualFlags k) q hcompare.1 hcompare.2
  have hleft0 : 0≤q'.A*q'.M := by
    unfold QuadraticScales.M
    exact mul_nonneg (zero_le_one.trans (hq' 0))
      (mul_nonneg (zero_le_one.trans (hq' 2)) (zero_le_one.trans (hq' 3)))
  have hright0 : 0≤q'.B*q'.N := by
    unfold QuadraticScales.N
    exact mul_nonneg (zero_le_one.trans (hq' 1))
      (mul_nonneg (zero_le_one.trans (hq' 4)) (zero_le_one.trans (hq' 5)))
  exact a03_soft_source_oriented_geometry q' hq' hmsoft hnsoft hH' hn'
    (by nlinarith [hcomp'.1] : q'.A*q'.M≤32*q'.B*q'.N)
    (by nlinarith [hcomp'.2] : q'.B*q'.N≤32*q'.A*q'.M)

end
end Sechstmoment
