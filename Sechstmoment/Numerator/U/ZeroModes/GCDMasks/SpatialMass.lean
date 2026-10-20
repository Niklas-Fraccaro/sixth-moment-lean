import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalScaleAlgebra

namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03NativeGCDSpatialEnvelope (Y x : ℝ) : ℝ := min 1 ((Y/x)^10)

theorem a03NativeGCDSpatialEnvelope_nonneg (Y x : ℝ) :
    0≤a03NativeGCDSpatialEnvelope Y x := by
  unfold a03NativeGCDSpatialEnvelope
  positivity

theorem a03NativeGCDSpatialEnvelope_near {Y x : ℝ} (hx : 0<x) (hxy : x≤Y) :
    a03NativeGCDSpatialEnvelope Y x=1 := by
  have hdiv : 1≤Y/x := (le_div_iff₀ hx).mpr (by simpa using hxy)
  exact min_eq_left (by simpa using pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) hdiv 10)

theorem a03NativeGCDSpatialEnvelope_far {Y x : ℝ} (hY : 0≤Y) (hx : Y<x) :
    a03NativeGCDSpatialEnvelope Y x=(Y/x)^10 := by
  have hxp : 0<x := lt_of_le_of_lt hY hx
  have hdiv : Y/x≤1 := (div_le_iff₀ hxp).mpr (by simpa using hx.le)
  have hdiv0 : 0≤Y/x := div_nonneg hY hxp.le
  exact min_eq_right (by simpa using pow_le_pow_left₀ hdiv0 hdiv 10)

theorem a03NativeGCDSpatialEnvelope_weight_far {Y x r : ℝ} (hY : 0≤Y) (hx : Y<x) :
    x^(r-1)*a03NativeGCDSpatialEnvelope Y x=Y^10*x^(r-11) := by
  have hxp : 0<x := lt_of_le_of_lt hY hx
  rw [a03NativeGCDSpatialEnvelope_far hY hx,div_pow,
    show r-11=(r-1)-10 by ring,Real.rpow_sub hxp (r-1) 10,Real.rpow_ofNat]
  ring

theorem a03NativeGCDSpatialEnvelope_weight_integrable {Y r : ℝ}
    (hY : 0<Y) (hr : 0<r) (hr2 : r<10) :
    IntegrableOn (fun x : ℝ => x^(r-1)*a03NativeGCDSpatialEnvelope Y x) (Ioi 0) := by
  have hnear : IntegrableOn (fun x : ℝ => x^(r-1)*a03NativeGCDSpatialEnvelope Y x) (Ioc 0 Y) := by
    have hi : IntegrableOn (fun x : ℝ => x^(r-1)) (Ioc 0 Y) := by
      apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hY.le).mp
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    apply hi.congr_fun _ measurableSet_Ioc
    intro x hx
    change x^(r-1)=x^(r-1)*a03NativeGCDSpatialEnvelope Y x
    rw [a03NativeGCDSpatialEnvelope_near hx.1 hx.2,mul_one]
  have hfar : IntegrableOn (fun x : ℝ => x^(r-1)*a03NativeGCDSpatialEnvelope Y x) (Ioi Y) := by
    have hi : IntegrableOn (fun x : ℝ => Y^10*x^(r-11)) (Ioi Y) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith : r-11< -1) hY).const_mul (Y^10)
    apply hi.congr_fun _ measurableSet_Ioi
    intro x hx
    exact (a03NativeGCDSpatialEnvelope_weight_far hY.le hx).symm
  have he : Ioc (0:ℝ) Y∪Ioi Y=Ioi 0 := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (hx|hx)
      · exact hx.1
      · exact hY.trans hx
    · intro hx
      rcases le_or_gt x Y with hxy|hxy
      · exact Or.inl ⟨hx,hxy⟩
      · exact Or.inr hxy
  rw [←he]
  exact hnear.union hfar

theorem a03NativeGCDSpatialEnvelope_weight_integral {Y r : ℝ}
    (hY : 0<Y) (hr : 0<r) (hr2 : r<10) :
    (∫ x in Ioi (0:ℝ),x^(r-1)*a03NativeGCDSpatialEnvelope Y x)=
      Y^r*(1/r+1/(10-r)) := by
  have hi := a03NativeGCDSpatialEnvelope_weight_integrable hY hr hr2
  have hnear : (∫ x in Ioc (0:ℝ) Y,x^(r-1)*a03NativeGCDSpatialEnvelope Y x)=Y^r/r := by
    calc
      _=∫ x in Ioc (0:ℝ) Y,x^(r-1) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        change x^(r-1)*a03NativeGCDSpatialEnvelope Y x=x^(r-1)
        rw [a03NativeGCDSpatialEnvelope_near hx.1 hx.2,mul_one]
      _=∫ x in (0:ℝ)..Y,x^(r-1) := (intervalIntegral.integral_of_le hY.le).symm
      _=_ := by
        rw [integral_rpow (Or.inl (by linarith : -1<r-1))]
        simp [Real.zero_rpow hr.ne']
  have hfar : (∫ x in Ioi Y,x^(r-1)*a03NativeGCDSpatialEnvelope Y x)=Y^r/(10-r) := by
    calc
      _=∫ x in Ioi Y,Y^10*x^(r-11) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        exact a03NativeGCDSpatialEnvelope_weight_far hY.le hx
      _=Y^10*(-Y^(r-10)/(r-10)) := by
        rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : r-11< -1) hY]
        rw [show r-11+1=r-10 by ring]
      _=Y^r/(10-r) := by
        rw [show Y^10*(-Y^(r-10)/(r-10))=-(Y^10*Y^(r-10))/(r-10) by ring,
          ←Real.rpow_ofNat,←Real.rpow_add hY,show 10+(r-10)=r by ring]
        rw [show r-10=-(10-r) by ring,div_neg]
        ring
  have he : Ioc (0:ℝ) Y∪Ioi Y=Ioi 0 := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (hx|hx)
      · exact hx.1
      · exact hY.trans hx
    · intro hx
      rcases le_or_gt x Y with hxy|hxy
      · exact Or.inl ⟨hx,hxy⟩
      · exact Or.inr hxy
  have hdis : Disjoint (Ioc (0:ℝ) Y) (Ioi Y) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.2) hy
  rw [←he,setIntegral_union hdis measurableSet_Ioi
    (hi.mono_set (by intro x hx; exact hx.1))
    (hi.mono_set (by intro x hx; exact hY.trans hx)),hnear,hfar]
  ring

end
end Sechstmoment.Source
