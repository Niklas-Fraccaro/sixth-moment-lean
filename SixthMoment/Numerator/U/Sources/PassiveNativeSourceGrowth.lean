import SixthMoment.Numerator.U.Sources.PassiveNativeSourceGeometry

namespace SixthMoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_passive_source_scale_budget {a b s u : ℝ}
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
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
  obtain ⟨p⟩ := hactive
  have hAe := (hfν T A hT hA (p.w 0) p.alpha_nonzero).2
  have hBe := (hgμ T B hT hB (p.w 1) p.beta_nonzero).2
  have hTp : 0<T := zero_lt_one.trans hT
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
  have hgap := p.gap_scale_bound hA hB hH
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


theorem a03_actual_passive_source_embedded_growth {a b s u : ℝ}
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
      q.A≤32*T^a ∧ q.B≤32*T^b ∧ Real.sqrt (q.M*q.N)≤4*T^(1+u/2) ∧
      q.mass≤1024*T^(a+b+2+u) ∧
      q.mass*q.H^2≤67108864*T^(2*(a+b)+2+2*s+2*u) ∧
      q.H≤(8*T^s)*(q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)/T := by
  filter_upwards [a03_actual_passive_source_scale_budget f g hf hg,eventually_ge_atTop (1:ℝ)]
    with T hb hT
  intro A B H hA hB hH k hk hactive
  let native := phaseActualScales A B H k
  let flags := boundaryActualFlags k
  let q := boundaryEmbeddedScales flags native
  have hnative := boundaryActual_scales_pos A B H k hA hB hH
  obtain ⟨hAe,hBe,hMN,hmass,hH0,hHend⟩ := hb A B H hA hB hH k hk hactive
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hnativeMN : 0≤native.M*native.N := by
    unfold native phaseActualScales QuadraticScales.M QuadraticScales.N
    have h0 := boundaryActual_scale_pos (k 0); have h1 := boundaryActual_scale_pos (k 1)
    have h2 := boundaryActual_scale_pos (k 2); have h3 := boundaryActual_scale_pos (k 3)
    positivity
  have hnativeMass : 0≤native.mass := by
    change 0≤A*B*native.M*native.N
    nlinarith [mul_nonneg (mul_nonneg hA.le hB.le) hnativeMN]
  have hp := boundaryProductFactor_bounds flags
  have hmassid : q.mass=4*(boundaryProductFactor flags)^2*native.mass := by
    simpa [q,boundaryProductFactor,Nat.cast_mul] using boundaryEmbedded_mass flags native
  have hqmass : q.mass≤1024*T^(a+b+2+u) := by
    rw [hmassid]
    have hp2 : (boundaryProductFactor flags)^2≤256 := by nlinarith
    calc
      _≤(4*256)*native.mass := mul_le_mul_of_nonneg_right (by linarith) hnativeMass
      _≤1024*T^(a+b+2+u) := by simpa only [show (4:ℝ)*256=1024 by norm_num] using mul_le_mul_of_nonneg_left hmass (by norm_num : (0:ℝ)≤1024)
  have hqH : q.H≤32*H := (boundaryEmbedded_size_bounds flags native (fun j => (hnative j).le) 6).2
  have hqHend : q.H≤256*T^((a+b)/2+s+u/2) := by
    calc
      _≤32*H := hqH
      _≤32*(8*T^((a+b)/2+s+u/2)) := mul_le_mul_of_nonneg_left hHend (by norm_num)
      _=_ := by ring
  have hqHp : 0≤q.H := by dsimp only [q]; rw [boundaryEmbedded_H]; have := hp.1; positivity
  have hqHsq : q.H^2≤65536*T^(a+b+2*s+u) := by
    have hh := pow_le_pow_left₀ hqHp hqHend 2
    calc
      _≤(256*T^((a+b)/2+s+u/2))^2 := hh
      _=_ := by rw [mul_pow,←Real.rpow_natCast (T^((a+b)/2+s+u/2)) 2,←Real.rpow_mul hTp.le]; norm_num; congr 1; ring
  have hmassH : q.mass*q.H^2≤67108864*T^(2*(a+b)+2+2*s+2*u) := by
    calc
      _≤(1024*T^(a+b+2+u))*(65536*T^(a+b+2*s+u)) :=
        mul_le_mul hqmass hqHsq (sq_nonneg _) (by positivity)
      _=_ := by rw [mul_mul_mul_comm,←Real.rpow_add hTp]; norm_num; congr 1; ring
  have hqA : q.A≤32*T^a := by
    exact ((boundaryEmbedded_size_bounds flags native (fun j => (hnative j).le) 0).2).trans
      (mul_le_mul_of_nonneg_left hAe (by norm_num))
  have hqB : q.B≤32*T^b := by
    exact ((boundaryEmbedded_size_bounds flags native (fun j => (hnative j).le) 1).2).trans
      (mul_le_mul_of_nonneg_left hBe (by norm_num))
  have hqX : Real.sqrt (q.M*q.N)≤4*T^(1+u/2) := by
    have he := (boundaryEmbedded_MN_upper flags native hnativeMN).trans
      (mul_le_mul_of_nonneg_left hMN (by norm_num))
    calc
      _≤Real.sqrt (16*T^(2+u)) := Real.sqrt_le_sqrt he
      _=4*T^(1+u/2) := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤16),show Real.sqrt (16:ℝ)=4 by norm_num,Real.sqrt_eq_rpow,←Real.rpow_mul hTp.le]
        congr 1
        ring
  have hqH0 : q.H≤(8*T^s)*(q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)/T := by
    dsimp only [q]
    rw [boundaryEmbedded_H]
    have he := boundaryEmbedded_sqrt_product flags native (mul_nonneg hA.le hB.le) hnativeMN
    change ((boundaryEmbeddedScales flags native).A*(boundaryEmbeddedScales flags native).B)^(1/2:ℝ)*
      Real.sqrt ((boundaryEmbeddedScales flags native).M*(boundaryEmbeddedScales flags native).N)=
        2*boundaryProductFactor flags*(A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N) at he
    calc
      _≤2*boundaryProductFactor flags*((8*T^s)*(A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N)/T) :=
        mul_le_mul_of_nonneg_left hH0 (by have := hp.1; positivity)
      _=(8*T^s)*(((boundaryEmbeddedScales flags native).A*(boundaryEmbeddedScales flags native).B)^(1/2:ℝ)*
        Real.sqrt ((boundaryEmbeddedScales flags native).M*(boundaryEmbeddedScales flags native).N))/T := by
          rw [he]
          ring
      _=_ := by ring
  exact ⟨hqA,hqB,hqX,hqmass,hmassH,hqH0⟩


theorem a03_actual_passive_source_embedded_growth_four {a b s u : ℝ}
    (_ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s≤1/8) (hu : u≤1/8)
    (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 0<A → 0<B → 0<H →
      ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      A03ActualPassiveNearZeroBlock T A B H (T^(s-1)) f g k →
      let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
      q.A≤32*T^a ∧ q.B≤32*T^b ∧ Real.sqrt (q.M*q.N)≤4*T^(1+u/2) ∧
      q.mass≤67108864*T^4 ∧ q.mass*q.H^2≤67108864*T^4 ∧
      q.H≤(8*T^s)*(q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)/T := by
  have hab' : a+b<1/2 := by linarith
  filter_upwards [a03_actual_passive_source_embedded_growth f g hf hg,eventually_ge_atTop (1:ℝ)]
    with T hb hT
  intro A B H hA hB hH k hk hactive
  obtain ⟨hAe,hBe,hXe,hmass,hmassH,hH0⟩ := hb A B H hA hB hH k hk hactive
  refine ⟨hAe,hBe,hXe,?_,?_,hH0⟩
  · calc
      _≤1024*T^(a+b+2+u) := hmass
      _≤1024*T^(4:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) (by norm_num)
      _≤67108864*T^4 := by rw [Real.rpow_ofNat]; nlinarith [pow_nonneg (zero_le_one.trans hT) 4]
  · calc
      _≤67108864*T^(2*(a+b)+2+2*s+2*u) := hmassH
      _≤67108864*T^(4:ℝ) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hT (by linarith)) (by norm_num)
      _=67108864*T^4 := Real.rpow_ofNat T 4 |> congrArg (fun z : ℝ => 67108864*z)

end
end SixthMoment
