import Sechstmoment.Numerator.U.Sources.GlobalPower
import Sechstmoment.Numerator.U.Sources.SoftSourceGlobalMajorant

namespace Sechstmoment
open Complex Real Source Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 3000000

theorem a03_actual_near_soft_source_majorant_power_bound {a b s u ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s≤1/8) (hu : u≤1/8)
    (hε : 0≤ε) (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
      ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
      T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*phaseSourceMajorant ε (a03SoftSourceOrientedScales q)≤
        (65536*(67108864:ℝ)^ε)*
          (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := by
  filter_upwards [phase_actual_near_source_embedded_growth_four ha hab hlen hs hu f g hf hg,
    eventually_ge_atTop (1:ℝ)] with T hb hT
  intro A B H hA hB hH k hk hactive
  dsimp only
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  let q := boundaryEmbeddedScales (boundaryActualFlags k) (phaseActualScales A B H k)
  obtain ⟨hAe,hBe,hXe,hmass,hmassH,hH0⟩ := hb A B H hAp hBp hHp k hk hactive
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hq1 := boundaryActual_embedded_lower_bounds A B H k hA hB hH
  have hqp : ∀ j, 0<q.size j := fun j => zero_lt_one.trans_le (hq1 j)
  have hAM : 0<q.A := hqp 0
  have hBM : 0<q.B := hqp 1
  have hHM : 0<q.H := hqp 6
  have hM : 0<q.M := by unfold QuadraticScales.M; exact mul_pos (hqp 2) (hqp 3)
  have hN : 0<q.N := by unfold QuadraticScales.N; exact mul_pos (hqp 4) (hqp 5)
  have hX : 0<Real.sqrt (q.M*q.N) := Real.sqrt_pos.mpr (mul_pos hM hN)
  have hmassid : q.mass=q.A*q.B*(Real.sqrt (q.M*q.N))^2 := by
    rw [Real.sq_sqrt (mul_pos hM hN).le]
    unfold QuadraticScales.mass
    ring
  have hsource := a03_soft_source_majorant_rectangular_bound (r:=4) q (fun j => (hqp j).le)
    (by norm_num : (0:ℝ)≤67108864) hTp.le hε hX.le hmassid
    (by simpa only [q,Real.rpow_ofNat] using hmass) (by simpa only [q,Real.rpow_ofNat] using hmassH)
  have hQ0 : 0≤rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H := by
    unfold rectangularQuadraticMajorant
    positivity
  have hE : ‖(rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H : ℂ)‖≤
      1*rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H := by
    rw [Complex.norm_real,Real.norm_of_nonneg hQ0,one_mul]
  have hquad := rectangular_error_endpoint (rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H : ℂ)
    hTp hAM hBM hX (hqp 6) (by positivity : 0<8*T^s) (by norm_num : (0:ℝ)≤1)
    (by norm_num : (0:ℝ)≤4) (Real.rpow_nonneg hTp.le (1+u/2)) hAe hBe
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hT hab) (by norm_num : (0:ℝ)≤32))
    hXe hH0 hE
  have hweight : 0≤T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)) := by positivity
  rw [norm_mul,Complex.norm_real,Complex.norm_real,Real.norm_of_nonneg hweight,
    Real.norm_of_nonneg hQ0,one_mul] at hquad
  have hpoisson := rectangular_poisson_back_transfer hTp (mul_pos hAM hBM) hX
    (hqp 6).le (by positivity : 0<8*T^s) hH0
  have hAB : q.A*q.B≤(32*T^a)*(32*T^b) := mul_le_mul hAe hBe hBM.le (by positivity)
  have hp : T^((a+b)/2+2*s+u/2)≤T^(1/2+a+b+s/2) :=
    Real.rpow_le_rpow_of_exponent_le hT (by linarith)
  have hk1 : (8:ℝ)^(1/2:ℝ)≤8 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8) (by norm_num : (1/2:ℝ)≤1)).trans_eq (Real.rpow_one 8)
  have hk2 : (8:ℝ)^(3/4:ℝ)≤8 := by
    exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤8) (by norm_num : (3/4:ℝ)≤1)).trans_eq (Real.rpow_one 8)
  rw [show (4:ℝ)^(1/2:ℝ)=2 by rw [←Real.sqrt_eq_rpow]; norm_num] at hquad
  have hquad' : T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H≤
      8192*T^(1/2+a+b+s/2)+512*T^(3/4+3*a/8+5*b/8+3*s/4+u/4) := by
    have hsecond := a03_source_second_power_identity hTp a b s u
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤4) (Real.rpow_nonneg hTp.le (1+u/2)),
      show (4:ℝ)^(1/2:ℝ)=2 by rw [←Real.sqrt_eq_rpow]; norm_num] at hsecond
    have hfirst := a03_source_first_power_identity hTp a b s
    simp only [mul_assoc] at hfirst hsecond hquad
    rw [hfirst,hsecond] at hquad
    have hquadnorm : T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H≤
        (1024*8^(1/2:ℝ))*T^(1/2+a+b+s/2)+(64*8^(3/4:ℝ))*T^(3/4+3*a/8+5*b/8+3*s/4+u/4) := by
      simpa only [mul_assoc] using hquad
    exact hquadnorm.trans (add_le_add
      (mul_le_mul_of_nonneg_right (by nlinarith : (1024:ℝ)*8^(1/2:ℝ)≤8192) (by positivity))
      (mul_le_mul_of_nonneg_right (by nlinarith : (64:ℝ)*8^(3/4:ℝ)≤512) (by positivity)))
  have hpoisson' : T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*q.H^2≤8192*T^(1/2+a+b+s/2) := by
    calc
      _≤(8*T^s)^2*(q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)/T := hpoisson
      _≤(8*T^s)^2*((32*T^a)*(32*T^b))^(1/2:ℝ)*(4*T^(1+u/2))/T := by gcongr
      _=8192*T^((a+b)/2+2*s+u/2) := a03_source_poisson_power_identity hTp a b s u
      _≤8192*T^(1/2+a+b+s/2) := mul_le_mul_of_nonneg_left hp (by norm_num)
  calc
    _≤(67108864:ℝ)^ε*T^(4*ε)*(2*(8192*T^(1/2+a+b+s/2)+512*T^(3/4+3*a/8+5*b/8+3*s/4+u/4))+
        8192*T^(1/2+a+b+s/2)) := by
      have he := mul_le_mul_of_nonneg_left hsource hweight
      calc
        _≤T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*
            ((67108864:ℝ)^ε*T^(4*ε)*(2*rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H+q.H^2)) := he
        _=(67108864:ℝ)^ε*T^(4*ε)*(2*(T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*
            rectangularQuadraticMajorant q.A q.B (Real.sqrt (q.M*q.N)) q.H)+
              T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*q.H^2) := by ring
        _≤_ := by gcongr
    _≤(65536*(67108864:ℝ)^ε)*(T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := by
      have he1 : T^(4*ε)*T^(1/2+a+b+s/2)=T^(1/2+a+b+s/2+4*ε) := by rw [←Real.rpow_add hTp]; congr 1; ring
      have he2 : T^(4*ε)*T^(3/4+3*a/8+5*b/8+3*s/4+u/4)=T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε) := by rw [←Real.rpow_add hTp]; congr 1; ring
      have hpow1 := Real.rpow_nonneg hTp.le (1/2+a+b+s/2)
      have hpow2 := Real.rpow_nonneg hTp.le (3/4+3*a/8+5*b/8+3*s/4+u/4)
      calc
        _≤(67108864:ℝ)^ε*T^(4*ε)*(65536*(T^(1/2+a+b+s/2)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4))) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        _=(65536*(67108864:ℝ)^ε)*(T^(4*ε)*T^(1/2+a+b+s/2)+T^(4*ε)*T^(3/4+3*a/8+5*b/8+3*s/4+u/4)) := by ring
        _=_ := by rw [he1,he2]


theorem a03_actual_near_soft_source_native_majorant_power_bound {a b s u ε : ℝ}
    (ha : 0≤a) (hab : a≤b) (hlen : 3*a+5*b<2) (hs : s≤1/8) (hu : u≤1/8)
    (hε : 0≤ε) (f g : ℝ → ℝ) (hf : SmoothInteriorProfile a f) (hg : SmoothInteriorProfile b g) :
    ∀ᶠ T : ℝ in atTop, ∀ A B H : ℝ, 2/3≤A → 2/3≤B → 2/3≤H →
      ∀ k : Fin 4 → ℕ, k∈rectangularAFEProductScaleGrid (T^(2+u)) →
      phaseActualActiveNearBlock T A B H (T^(s-1)) f g k →
      let native := phaseActualScales A B H k
      let q := boundaryEmbeddedScales (boundaryActualFlags k) native
      T/((A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N))*phaseSourceMajorant ε (a03SoftSourceOrientedScales q)≤
        (2097152*(67108864:ℝ)^ε)*
          (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε)) := by
  filter_upwards [a03_actual_near_soft_source_majorant_power_bound ha hab hlen hs hu hε f g hf hg,
    eventually_ge_atTop (1:ℝ)] with T hb hT
  intro A B H hA hB hH k hk hactive
  dsimp only
  let native := phaseActualScales A B H k
  let flags := boundaryActualFlags k
  let q := boundaryEmbeddedScales flags native
  have hAp : 0<A := by linarith
  have hBp : 0<B := by linarith
  have hHp : 0<H := by linarith
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hn := boundaryActual_scales_pos A B H k hAp hBp hHp
  have hMN : 0<native.M*native.N := by
    unfold QuadraticScales.M QuadraticScales.N
    exact mul_pos (mul_pos (hn 2) (hn 3)) (mul_pos (hn 4) (hn 5))
  have hp := boundaryProductFactor_bounds flags
  have hden : 0<(A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N) := by positivity
  have hd := boundaryEmbedded_sqrt_product flags native (mul_nonneg hAp.le hBp.le) hMN.le
  change (q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N)=
    2*boundaryProductFactor flags*(A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N) at hd
  have hweq : T/((A*B)^(1/2:ℝ)*Real.sqrt (native.M*native.N))=
      (2*boundaryProductFactor flags)*(T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))) := by
    rw [hd]
    have hp0 : boundaryProductFactor flags≠0 := by linarith [hp.1]
    have hab0 : (A*B)^(1/2:ℝ)≠0 := (Real.rpow_pos_of_pos (mul_pos hAp hBp) _).ne'
    have hmn0 : Real.sqrt (native.M*native.N)≠0 := (Real.sqrt_pos.mpr hMN).ne'
    field_simp [hp0,hab0,hmn0]
  have hq1 := boundaryActual_embedded_lower_bounds A B H k hA hB hH
  have hnormalized := a03_soft_source_lower_bounds q hq1
  have hmajor : 0≤phaseSourceMajorant ε (a03SoftSourceOrientedScales q) :=
    phase_source_majorant_nonneg _ _ (fun j => zero_le_one.trans (hnormalized j))
  have hqAB : 0<q.A*q.B := mul_pos (zero_lt_one.trans_le (hq1 0)) (zero_lt_one.trans_le (hq1 1))
  have hqMN : 0<q.M*q.N := by
    unfold QuadraticScales.M QuadraticScales.N
    exact mul_pos (mul_pos (zero_lt_one.trans_le (hq1 2)) (zero_lt_one.trans_le (hq1 3)))
      (mul_pos (zero_lt_one.trans_le (hq1 4)) (zero_lt_one.trans_le (hq1 5)))
  have hbound := hb A B H hA hB hH k hk hactive
  rw [hweq]
  calc
    _=(2*boundaryProductFactor flags)*(T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*
      phaseSourceMajorant ε (a03SoftSourceOrientedScales q)) := by ring
    _≤32*(T/((q.A*q.B)^(1/2:ℝ)*Real.sqrt (q.M*q.N))*
      phaseSourceMajorant ε (a03SoftSourceOrientedScales q)) := mul_le_mul_of_nonneg_right
        (by linarith : 2*boundaryProductFactor flags≤32) (by positivity)
    _≤32*((65536*(67108864:ℝ)^ε)*
      (T^(1/2+a+b+s/2+4*ε)+T^(3/4+3*a/8+5*b/8+3*s/4+u/4+4*ε))) :=
        mul_le_mul_of_nonneg_left hbound (by norm_num)
    _=_ := by ring

end
end Sechstmoment
