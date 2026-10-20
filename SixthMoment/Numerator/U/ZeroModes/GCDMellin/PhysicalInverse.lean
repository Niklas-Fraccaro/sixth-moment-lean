import SixthMoment.Numerator.U.Separation.NativeGapSigns
import SixthMoment.Numerator.U.ZeroModes.GCDMellin.InitialKernel
import SixthMoment.Numerator.U.ZeroModes.Ratio.ChamberWeight

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 0

private theorem gcdIntegral_threeFactors (C : ℂ) (F G H : ℝ→ℂ) :
    (∫p : ℝ×(ℝ×ℝ),C*F p.1*G p.2.1*H p.2.2 ∂(volume.prod (volume.prod volume)))=
      C*(∫y : ℝ,F y)*(∫y : ℝ,G y)*(∫y : ℝ,H y) := by
  rw [show (fun p : ℝ×(ℝ×ℝ) => C*F p.1*G p.2.1*H p.2.2)=
    (fun p : ℝ×(ℝ×ℝ) => C*(F p.1*(G p.2.1*H p.2.2))) by funext p; ring,
    integral_const_mul,integral_prod_mul F (fun p : ℝ×ℝ => G p.1*H p.2),integral_prod_mul G H]
  ring

def a03ZeroModeGCDPhysicalCoefficient (α : MomentShifts) (a b m n : ℕ)
    (A B : ℕ→ℂ) (x : ℝ) : ℂ :=
  A a*B b*(Nat.gcd (a*m) (b*n):ℂ)*(a:ℂ)^(-1+α 1)*(b:ℂ)^(-1+α 3)*
    (m:ℂ)^(-1-α 0+α 1)*(n:ℂ)^(-1-α 2+α 3)*(x:ℂ)^(-1-α 1-α 3)

def a03ZeroModeGCDPhysicalCosineDensity (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (a b m n h : ℕ) (A B : ℕ→ℂ) (x : ℝ) : ℂ :=
  2*a03ZeroModeGCDPhysicalCoefficient α a b m n A B x*
    a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) ((a:ℝ)*(m:ℝ)^2/x)*
    a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) ((b:ℝ)*(n:ℝ)^2/x)*
    a03SmoothedCosine (a03ZeroModeVStarTimeProfile Φ T σ 1 a b x)
      (T*(Nat.gcd (a*m) (b*n):ℝ)*(h:ℝ)/x)

def a03ZeroModeGCDPhysicalSignDensity (positive : Bool) (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (a b m n h : ℕ) (A B : ℕ→ℂ) (x : ℝ) : ℂ :=
  a03ZeroModeGCDPhysicalCoefficient α a b m n A B x*
    a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) ((a:ℝ)*(m:ℝ)^2/x)*
    a03ZeroModeRatioPartition (a03ZeroModeRatioWeight α) ((b:ℝ)*(n:ℝ)^2/x)*
    ∫t : ℝ,Complex.exp (((-(T*rectangularGapSign positive*
      (Nat.gcd (a*m) (b*n):ℝ)*(h:ℝ)/x):ℝ):ℂ)*I*(t:ℂ))*Φ t*
        bblrVStar (polarPoleKiller T σ) (x^2/((a:ℝ)*(b:ℝ)*(T*t)^2))

theorem a03ZeroModeGCDPhysicalSigns_eq_cosineDensity (Φ : ℝ→ℂ) (T : ℝ)
    (σ α : MomentShifts) (a b m n h : ℕ) (A B : ℕ→ℂ) (x : ℝ) :
    (∑positive : Bool,a03ZeroModeGCDPhysicalSignDensity positive Φ T σ α a b m n h A B x)=
      a03ZeroModeGCDPhysicalCosineDensity Φ T σ α a b m n h A B x := by
  have hTime (positive : Bool) :
      (∫t : ℝ,Complex.exp (((-(T*rectangularGapSign positive*
        (Nat.gcd (a*m) (b*n):ℝ)*(h:ℝ)/x):ℝ):ℂ)*I*(t:ℂ))*Φ t*
          bblrVStar (polarPoleKiller T σ) (x^2/((a:ℝ)*(b:ℝ)*(T*t)^2)))=
      ∫t : ℝ,Complex.exp (((-((T*(Nat.gcd (a*m) (b*n):ℝ)*(h:ℝ)/x)*
        rectangularGapSign positive):ℝ):ℂ)*I*(t:ℂ))*a03ZeroModeVStarTimeProfile Φ T σ 1 a b x t := by
    apply integral_congr_ae
    apply ae_of_all
    intro t
    dsimp only []
    have hd : (T*(1:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)))^2*t^2=(a:ℝ)*(b:ℝ)*(T*t)^2 := by
      rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
      ring
    have he : T*rectangularGapSign positive*(Nat.gcd (a*m) (b*n):ℝ)*(h:ℝ)/x=
        (T*(Nat.gcd (a*m) (b*n):ℝ)*(h:ℝ)/x)*rectangularGapSign positive := by ring
    unfold a03ZeroModeVStarTimeProfile a03ProfileProduct a03ZeroModeVStarTimeAmplitude
    rw [he,Nat.cast_one,hd]
    ring
  unfold a03ZeroModeGCDPhysicalSignDensity
  simp_rw [hTime]
  rw [←Finset.mul_sum,SixthMoment.a03NativeGapSigns_eq_two_cosine]
  unfold a03ZeroModeGCDPhysicalCosineDensity
  ring

private theorem gcdPositiveRatioPower {a m : ℕ} (ha : 0<a) (hm : 0<m)
    {x : ℝ} (hx : 0<x) (u : ℂ) :
    (((a:ℝ)*(m:ℝ)^2/x:ℝ):ℂ)^(-u)=
      (a:ℂ)^(-u)*(m:ℂ)^(-2*u)*(x:ℂ)^u := by
  have haR : 0<(a:ℝ) := by exact_mod_cast ha
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (by positivity) hx.le,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg haR.le (sq_nonneg _),Complex.ofReal_pow]
  simp only [Complex.ofReal_natCast]
  rw [←Complex.natCast_cpow_natCast_mul m 2 (-u),Complex.cpow_neg (x:ℂ),div_inv_eq_mul]
  congr 2
  congr 1
  ring

theorem a03ZeroModeNativePositiveGap_inverse_Mellin
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts)
    {a b d h : ℕ} (ha : 0<a) (hb : 0<b) (hd : 0<d) (hh : 0<h)
    {x cs : ℝ} (hx : 0<x) (hcs : 0<cs) :
    a03SmoothedCosine (a03ZeroModeVStarTimeProfile Φ T σ 1 a b x) (T*(d:ℝ)*(h:ℝ)/x)=
      verticalIntegral cs (fun s => (d:ℂ)^(-s)*(h:ℂ)^(-s)*
        a03ZeroModeGCDArchKernel Φ T σ 1 a b x s) := by
  have hdR : 0<(d:ℝ) := by exact_mod_cast hd
  have hhR : 0<(h:ℝ) := by exact_mod_cast hh
  have hF := a03ZeroModeVStarTimeProfile_contDiff hΦ hSupp hT σ Nat.zero_lt_one ha hb hx
  have hFs := (a03ZeroModeVStarTimeProfile_support Φ T σ 1 a b x).trans hSupp
  rw [show T*(d:ℝ)*(h:ℝ)/x=T*((d:ℝ)*(h:ℝ))/x by ring,
    a03SmoothedCosine_inverse_Mellin hF hFs hcs (div_pos (mul_pos hT (mul_pos hdR hhR)) hx)]
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  apply ae_of_all
  intro y
  dsimp only []
  rw [a03NativeGap_inversePower_factor hT (mul_pos hdR hhR) hx,
    Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hdR.le hhR.le,
    a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ Nat.zero_lt_one ha hb hx (by simpa using hcs)]
  unfold a03ZeroModeGCDArchTimeKernel
  rw [a03PositiveTime_inversePowerIntegral_eq_mellin hFs]
  simp only [Complex.ofReal_natCast]
  ring

theorem a03ZeroModeGCDInitialMNHKernel_eq_physical_inverse_product
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    {a b m n h : ℕ} (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hh : 0<h)
    (A B : ℕ→ℂ) {x : ℝ} (hx : 0<x) (u v s : ℂ) :
    a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B x u v s ((m,n),h)=
      a03ZeroModeGCDPhysicalCoefficient α a b m n A B x*
        a03ZeroModeRatioKernel (a03ZeroModeRatioWeight α) ((a:ℝ)*(m:ℝ)^2/x) u*
        a03ZeroModeRatioKernel (a03ZeroModeRatioWeight α) ((b:ℝ)*(n:ℝ)^2/x) v*
        ((Nat.gcd (a*m) (b*n):ℂ)^(-s)*(h:ℂ)^(-s)*
          a03ZeroModeGCDArchKernel Φ T σ 1 a b x s) := by
  have hd : 0<Nat.gcd (a*m) (b*n) := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha hm)
  have ha0 : (a:ℂ)≠0 := Nat.cast_ne_zero.mpr ha.ne'
  have hb0 : (b:ℂ)≠0 := Nat.cast_ne_zero.mpr hb.ne'
  have hm0 : (m:ℂ)≠0 := Nat.cast_ne_zero.mpr hm.ne'
  have hn0 : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn.ne'
  have hd0 : (Nat.gcd (a*m) (b*n):ℂ)≠0 := Nat.cast_ne_zero.mpr hd.ne'
  have hx0 : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hpa : (a:ℂ)^(-1+α 1)*(a:ℂ)^(-u)=(a:ℂ)^(-1+α 1-u) := by
    rw [←Complex.cpow_add _ _ ha0]
    congr 1
  have hpb : (b:ℂ)^(-1+α 3)*(b:ℂ)^(-v)=(b:ℂ)^(-1+α 3-v) := by
    rw [←Complex.cpow_add _ _ hb0]
    congr 1
  have hpm : (m:ℂ)^(-1-α 0+α 1)*(m:ℂ)^(-2*u)=(m:ℂ)^(-1-α 0+α 1-2*u) := by
    rw [←Complex.cpow_add _ _ hm0]
    congr 1
    ring
  have hpn : (n:ℂ)^(-1-α 2+α 3)*(n:ℂ)^(-2*v)=(n:ℂ)^(-1-α 2+α 3-2*v) := by
    rw [←Complex.cpow_add _ _ hn0]
    congr 1
    ring
  have hpx : (x:ℂ)^(-1-α 1-α 3)*(x:ℂ)^u*(x:ℂ)^v=(x:ℂ)^(-1-α 1-α 3+u+v) := by
    rw [←Complex.cpow_add _ _ hx0,←Complex.cpow_add _ _ hx0]
  have hpd : (Nat.gcd (a*m) (b*n):ℂ)*(Nat.gcd (a*m) (b*n):ℂ)^(-s)=
      (Nat.gcd (a*m) (b*n):ℂ)^(1-s) := by
    nth_rw 1 [←Complex.cpow_one (Nat.gcd (a*m) (b*n):ℂ)]
    rw [←Complex.cpow_add _ _ hd0]
    congr 1
  rw [a03ZeroModeGCDInitialMNHKernel_apply Φ T σ α a b A B x u v s hm.ne' hn.ne' hh.ne']
  unfold a03ZeroModeGCDInitialBase a03ZeroModeGCDPhysicalCoefficient a03ZeroModeRatioKernel
  rw [gcdPositiveRatioPower ha hm hx,gcdPositiveRatioPower hb hn hx]
  symm
  calc
    _=(A a*B b)*
      ((Nat.gcd (a*m) (b*n):ℂ)*(Nat.gcd (a*m) (b*n):ℂ)^(-s))*
      ((a:ℂ)^(-1+α 1)*(a:ℂ)^(-u))*((b:ℂ)^(-1+α 3)*(b:ℂ)^(-v))*
      ((m:ℂ)^(-1-α 0+α 1)*(m:ℂ)^(-2*u))*((n:ℂ)^(-1-α 2+α 3)*(n:ℂ)^(-2*v))*
      ((x:ℂ)^(-1-α 1-α 3)*(x:ℂ)^u*(x:ℂ)^v)*
      (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*(h:ℂ)^(-s)*
      a03ZeroModeGCDArchKernel Φ T σ 1 a b x s := by ring
    _=_ := by rw [hpd,hpa,hpb,hpm,hpn,hpx]; ring

theorem a03ZeroModeGCDPhysicalCosineDensity_eq_initial_product
    {Φ : ℝ→ℂ} (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T ε : ℝ} (hT : 0<T) (hε : 0<ε) (σ α : MomentShifts)
    {a b m n h : ℕ} (ha : 0<a) (hb : 0<b) (hm : 0<m) (hn : 0<n) (hh : 0<h)
    (A B : ℕ→ℂ) {x : ℝ} (hx : 0<x) :
    a03ZeroModeGCDPhysicalCosineDensity Φ T σ α a b m n h A B x=
      2*(1/(2*Real.pi):ℂ)^3*∫p : ℝ×(ℝ×ℝ),
        a03ZeroModeGCDInitialMNHKernel Φ T σ α a b A B x
          ((ε:ℂ)+(p.1:ℂ)*I) ((ε:ℂ)+(p.2.1:ℂ)*I) (((1+ε:ℝ):ℂ)+(p.2.2:ℂ)*I) ((m,n),h)
        ∂(volume.prod (volume.prod volume)) := by
  have hd : 0<Nat.gcd (a*m) (b*n) := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos ha hm)
  have haR : 0<(a:ℝ) := by exact_mod_cast ha
  have hbR : 0<(b:ℝ) := by exact_mod_cast hb
  have hmR : 0<(m:ℝ) := by exact_mod_cast hm
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  unfold a03ZeroModeGCDPhysicalCosineDensity
  rw [a03ZeroModeRatioPartition_positive_contour (div_pos (mul_pos haR (sq_pos_of_pos hmR)) hx)
      hε _ α (a03ZeroModeRatioWeight_admissible α),
    a03ZeroModeRatioPartition_positive_contour (div_pos (mul_pos hbR (sq_pos_of_pos hnR)) hx)
      hε _ α (a03ZeroModeRatioWeight_admissible α),
    a03ZeroModeNativePositiveGap_inverse_Mellin hΦ hSupp hT σ ha hb hd hh hx (by linarith : 0<1+ε)]
  simp_rw [a03ZeroModeGCDInitialMNHKernel_eq_physical_inverse_product Φ T σ α ha hb hm hn hh A B hx]
  rw [gcdIntegral_threeFactors (a03ZeroModeGCDPhysicalCoefficient α a b m n A B x)
    (fun y : ℝ => a03ZeroModeRatioKernel (a03ZeroModeRatioWeight α) ((a:ℝ)*(m:ℝ)^2/x) ((ε:ℂ)+(y:ℂ)*I))
    (fun y : ℝ => a03ZeroModeRatioKernel (a03ZeroModeRatioWeight α) ((b:ℝ)*(n:ℝ)^2/x) ((ε:ℂ)+(y:ℂ)*I))
    (fun y : ℝ => (Nat.gcd (a*m) (b*n):ℂ)^(-(((1+ε:ℝ):ℂ)+(y:ℂ)*I))*(h:ℂ)^(-(((1+ε:ℝ):ℂ)+(y:ℂ)*I))*
      a03ZeroModeGCDArchKernel Φ T σ 1 a b x (((1+ε:ℝ):ℂ)+(y:ℂ)*I))]
  unfold verticalIntegral
  ring

end
end SixthMoment.Source
