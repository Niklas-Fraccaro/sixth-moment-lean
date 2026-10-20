import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace Sechstmoment.Source
open Real Set MeasureTheory
noncomputable section
set_option maxHeartbeats 400000

theorem a03NativeGCDSpatialPower_far {Y X p r : ℝ}
    (hY : 0<Y) (hX : Y≤X) (hp : 0≤p) :
    X^(r-1)*min 1 ((Y/X)^p)=Y^p*X^(r-p-1) := by
  have hXp : 0<X := hY.trans_le hX
  have hd : Y/X≤1 := (div_le_iff₀ hXp).mpr (by simpa using hX)
  rw [min_eq_right (Real.rpow_le_one (by positivity) hd hp),
    Real.div_rpow hY.le hXp.le]
  have he : r-p-1=(r-1)-p := by ring
  rw [he,Real.rpow_sub hXp (r-1) p]
  ring

theorem a03NativeGCDSpatialPower_tail_integrable {Y R p r : ℝ}
    (hY : 0<Y) (hYR : Y≤R) (hp : 0≤p) (hrp : r<p) :
    IntegrableOn (fun X : ℝ => X^(r-1)*min 1 ((Y/X)^p)) (Ioi R) := by
  have hR : 0<R := hY.trans_le hYR
  have hi : IntegrableOn (fun X : ℝ => Y^p*X^(r-p-1)) (Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : r-p-1< -1) hR).const_mul (Y^p)
  apply hi.congr_fun _ measurableSet_Ioi
  intro X hX
  exact (a03NativeGCDSpatialPower_far hY (hYR.trans hX.le) hp).symm

theorem a03NativeGCDSpatialPower_tail_integral {Y R p r : ℝ}
    (hY : 0<Y) (hYR : Y≤R) (hp : 0≤p) (hrp : r<p) :
    (∫ X : ℝ in Ioi R,X^(r-1)*min 1 ((Y/X)^p))=
      Y^p*R^(r-p)/(p-r) := by
  have hR : 0<R := hY.trans_le hYR
  calc
    _=∫ X : ℝ in Ioi R,Y^p*X^(r-p-1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro X hX
      exact a03NativeGCDSpatialPower_far hY (hYR.trans hX.le) hp
    _=Y^p*(-R^(r-p)/(r-p)) := by
      rw [integral_const_mul,integral_Ioi_rpow_of_lt (by linarith : r-p-1< -1) hR]
      rw [show r-p-1+1=r-p by ring]
    _=_ := by
      have he : -(1/(r-p))=1/(p-r) := by
        rw [show r-p=-(p-r) by ring,div_neg]
        ring
      calc
        _=Y^p*R^(r-p)*(-(1/(r-p))) := by ring
        _=_ := by rw [he]; ring

theorem a03NativeGCDSpatialPower_scaled_tail_integral {Y T δ p r : ℝ}
    (hY : 0<Y) (hT : 1≤T) (hδ : 0≤δ) (hp : 0≤p) (hrp : r<p) :
    (∫ X : ℝ in Ioi (Y*T^δ),X^(r-1)*min 1 ((Y/X)^p))=
      Y^r*T^(δ*(r-p))/(p-r) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have ht : 1≤T^δ := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hT hδ
  have hYR : Y≤Y*T^δ := by nlinarith only [ht,hY]
  rw [a03NativeGCDSpatialPower_tail_integral hY hYR hp hrp,
    Real.mul_rpow hY.le (Real.rpow_pos_of_pos hTp δ).le,
    ←Real.rpow_mul hTp.le]
  have he : Y^p*Y^(r-p)=Y^r := by
    rw [←Real.rpow_add hY,show p+(r-p)=r by ring]
  rw [show Y^p*(Y^(r-p)*T^(δ*(r-p)))=(Y^p*Y^(r-p))*T^(δ*(r-p)) by ring,he]

theorem a03NativeGCDSpatialPower_tail_uniform_rapid {q r δ : ℝ}
    (hq : 0≤q) (hr : 0<r) (hδ : 0<δ) (N : ℝ) :
    ∃ p C : ℝ,r<p ∧ 0≤C ∧ ∀ T Y : ℝ,1≤T → 0<Y → Y≤T^q →
      IntegrableOn (fun X : ℝ => X^(r-1)*min 1 ((Y/X)^p)) (Ioi (Y*T^δ)) ∧
      (∫ X : ℝ in Ioi (Y*T^δ),X^(r-1)*min 1 ((Y/X)^p))≤C*T^(-N) := by
  let p : ℝ := r+(q*r+max N 0+1)/δ
  have hd : 0<q*r+max N 0+1 := by
    have hqr := mul_nonneg hq hr.le
    have hN := le_max_right N 0
    linarith only [hqr,hN]
  have hrp : r<p := by dsimp [p]; exact lt_add_of_pos_right _ (div_pos hd hδ)
  have hp : 0≤p := hr.le.trans hrp.le
  refine ⟨p,1/(p-r),hrp,by positivity,?_⟩
  intro T Y hT hY hYupper
  have hTp : 0<T := zero_lt_one.trans_le hT
  have ht : 1≤T^δ := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_le hT hδ.le
  have hYR : Y≤Y*T^δ := by nlinarith only [ht,hY]
  refine ⟨a03NativeGCDSpatialPower_tail_integrable hY hYR hp hrp,?_⟩
  rw [a03NativeGCDSpatialPower_scaled_tail_integral hY hT hδ.le hp hrp]
  have hYr : Y^r≤T^(q*r) := by
    rw [Real.rpow_mul hTp.le]
    exact Real.rpow_le_rpow hY.le hYupper hr.le
  have hexp : q*r+δ*(r-p)=-(max N 0+1) := by
    dsimp [p]
    field_simp
    ring
  calc
    _≤(T^(q*r)*T^(δ*(r-p)))/(p-r) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hYr (Real.rpow_nonneg hTp.le _)) (sub_pos.mpr hrp).le
    _=T^(-(max N 0+1))/(p-r) := by rw [←Real.rpow_add hTp,hexp]
    _≤T^(-N)/(p-r) :=
      div_le_div_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hT (by linarith only [le_max_left N 0]))
        (sub_pos.mpr hrp).le
    _=(1/(p-r))*T^(-N) := by ring

theorem a03NativeGCDSpatialPower_tail_pointwise_saving {T Y X δ p k M : ℝ}
    (hT : 1≤T) (hY : 0<Y) (hδ : 0≤δ) (hX : Y*T^δ≤X)
    (hk : 0≤k) (hkp : k≤p) (hsave : M≤δ*(p-k)) :
    min 1 ((Y/X)^p)≤T^(-M)*min 1 ((Y/X)^k) := by
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hXp : 0<X := (mul_pos hY (Real.rpow_pos_of_pos hTp δ)).trans_le hX
  have hz : 0<Y/X := div_pos hY hXp
  have he : T^δ*T^(-δ)=1 := by
    rw [←Real.rpow_add hTp,add_neg_cancel,Real.rpow_zero]
  have hratio : Y/X≤T^(-δ) := by
    apply (div_le_iff₀ hXp).mpr
    calc
      Y=Y*T^δ*T^(-δ) := by rw [mul_assoc,he,mul_one]
      _≤X*T^(-δ) := mul_le_mul_of_nonneg_right hX (Real.rpow_nonneg hTp.le _)
      _=T^(-δ)*X := by ring
  have hz1 : Y/X≤1 := hratio.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hT (neg_nonpos.mpr hδ))
  rw [min_eq_right (Real.rpow_le_one hz.le hz1 (hk.trans hkp)),
    min_eq_right (Real.rpow_le_one hz.le hz1 hk)]
  have hpow := Real.rpow_le_rpow hz.le hratio (sub_nonneg.mpr hkp)
  rw [←Real.rpow_mul hTp.le] at hpow
  calc
    (Y/X)^p=(Y/X)^(p-k)*(Y/X)^k := by
      rw [←Real.rpow_add hz,show p-k+k=p by ring]
    _≤T^((-δ)*(p-k))*(Y/X)^k :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hz.le _)
    _≤T^(-M)*(Y/X)^k :=
      mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le hT (by nlinarith only [hsave]))
        (Real.rpow_nonneg hz.le _)

end
end Sechstmoment.Source
