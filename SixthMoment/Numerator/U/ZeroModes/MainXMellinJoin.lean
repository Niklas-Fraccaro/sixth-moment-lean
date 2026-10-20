import SixthMoment.Numerator.U.ZeroModes.GCDMellin.FrontReconstruction
import SixthMoment.Numerator.U.ZeroModes.MainTimeFubini
import SixthMoment.Numerator.U.ZeroModes.MellinAffineContour
import SixthMoment.Numerator.U.ZeroModes.StaticEtaNormalization

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 1000000

private theorem mainPositiveXPowers (β δ s : ℂ) {x : ℝ} (hx : 0<x) :
    (x:ℂ)⁻¹*(x:ℂ)^s*(x:ℂ)^(-β-δ)=(x:ℂ)^((s-β-δ)-1) := by
  rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne'),
    ←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')]
  congr 1
  ring

theorem a03ZeroModeGCDEtaMainX_eq_xTimeMellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {s : ℂ} (hs : 0<s.re) (hq : 0<(s-α 1-α 3).re) :
    a03ZeroModeGCDEtaMainX Φ T σ α g a b A B s=
      (T:ℂ)^(-s)*Complex.Gamma s*Complex.cos (Real.pi*s/2)*
      (2*Real.pi:ℂ)^(-(s-α 1-α 3))*
      (polarPoleKiller T σ ((s-α 1-α 3)/2)/(s-α 1-α 3))*
      (∫t : ℝ,Φ t*(t:ℂ)^(-α 1-α 3))*
      (A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*
        (b:ℂ)^(-1+α 3)*
        ((T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)):ℝ):ℂ)^(s-α 1-α 3)*
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s) := by
  let Y : ℝ := T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ))
  have hY : 0<Y := by
    have hgr : 0<(g:ℝ) := by exact_mod_cast hg
    have har : 0<(a:ℝ) := by exact_mod_cast ha
    have hbr : 0<(b:ℝ) := by exact_mod_cast hb
    dsimp [Y]
    positivity
  let C : ℂ := (T:ℂ)^(-s)*Complex.Gamma s*Complex.cos (Real.pi*s/2)*
    A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*
      (b:ℂ)^(-1+α 3)*a03ZeroModeRatioArithmeticNumerator α a b 0 0 s
  have he : a03ZeroModeGCDEtaMainX Φ T σ α g a b A B s=
      C*(∫x : ℝ in Ioi 0,∫t : ℝ,a03VStarSquareTimeDensity (polarPoleKiller T σ) Φ Y
        (s-α 1-α 3) s x t) := by
    unfold a03ZeroModeGCDEtaMainX
    rw [←integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [a03ZeroModeGCDArchKernel_eq_time hΦ hSupp hT σ hg ha hb hx hs]
    unfold a03ZeroModeGCDArchTimeKernel a03ZeroModeRatioPhysicalPrefactor
    unfold a03VStarSquareTimeDensity
    rw [show (fun t : ℝ => (x:ℂ)^((s-α 1-α 3)-1)*bblrVStar (polarPoleKiller T σ)
      (x^2/(Y^2*t^2))*Φ t*(t:ℂ)^(-s))=
      (fun t : ℝ => (x:ℂ)^((s-α 1-α 3)-1)*
        (a03ZeroModeVStarTimeProfile Φ T σ g a b x t*(t:ℂ)^(-s))) by
          funext t; dsimp [a03ZeroModeVStarTimeProfile,SixthMoment.a03ProfileProduct,a03ZeroModeVStarTimeAmplitude,Y]; ring]
    rw [integral_const_mul]
    dsimp only [C]
    have hp := mainPositiveXPowers (α 1) (α 3) s hx
    calc
      _=((x:ℂ)⁻¹*(x:ℂ)^s*(x:ℂ)^(-α 1-α 3))*
        ((T:ℂ)^(-s)*Complex.Gamma s*Complex.cos (Real.pi*s/2)*
          (∫t : ℝ,a03ZeroModeVStarTimeProfile Φ T σ g a b x t*(t:ℂ)^(-s))*
          A (g*a)*B (g*b)*(g:ℂ)^(-1+α 1+α 3-s)*(a:ℂ)^(-1+α 1)*
            (b:ℂ)^(-1+α 3)*a03ZeroModeRatioArithmeticNumerator α a b 0 0 s) := by ring
      _=_ := by rw [hp]; ring
  rw [he,a03VStarSquareTimeDensity_x_time_eq hΦ hSupp hY hq s _ (rawMomentShifts T σ)
    (polarPoleKiller_BBLREntireWeight T σ _)]
  have ht : s-α 1-α 3-s=-α 1-α 3 := by ring
  rw [ht]
  dsimp only [C,Y]
  ring

def a03ZeroModeTimeMoment (Φ : ℝ→ℂ) (T : ℝ) (α : MomentShifts) : ℂ :=
  ((T/(2*Real.pi):ℝ):ℂ)^(-α 1-α 3)*∫t : ℝ,Φ t*(t:ℂ)^(-α 1-α 3)

theorem a03ZeroModeTimeMoment_eq_integral (Φ : ℝ→ℂ)
    (hSupp : tsupport Φ⊆Icc (1:ℝ) 2) {T : ℝ} (hT : 0<T) (α : MomentShifts) :
    a03ZeroModeTimeMoment Φ T α=∫t : ℝ,Φ t*((T*t/(2*Real.pi):ℝ):ℂ)^(-α 1-α 3) := by
  unfold a03ZeroModeTimeMoment
  rw [←integral_const_mul]
  apply integral_congr_ae
  apply ae_of_all
  intro t
  dsimp only
  by_cases ht : Φ t=0
  · simp [ht]
  · have htp : 0<t := zero_lt_one.trans_le (hSupp (subset_tsupport _ ht)).1
    have hscale : 0<T/(2*Real.pi) := div_pos hT (mul_pos (by norm_num) Real.pi_pos)
    rw [show T*t/(2*Real.pi)=T/(2*Real.pi)*t by ring,
      Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg hscale.le htp.le]
    ring

private theorem mainTimeScalePowers {T : ℝ} (hT : 0<T) (β δ s : ℂ) :
    (T:ℂ)^(-s)*(2*Real.pi:ℂ)^(-(s-β-δ))*(T:ℂ)^(s-β-δ)=
      ((T/(2*Real.pi):ℝ):ℂ)^(-β-δ)*(2*Real.pi:ℂ)^(-s) := by
  have hπ : 0<2*Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hT.le hπ.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  have heT : (T:ℂ)^(-s)*(T:ℂ)^(s-β-δ)=(T:ℂ)^(-β-δ) := by
    rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hT.ne')]
    congr 1
    ring
  have heπ : (2*Real.pi:ℂ)^(-(s-β-δ))*(2*Real.pi:ℂ)^(-β-δ)=(2*Real.pi:ℂ)^(-s) := by
    rw [←Complex.cpow_add _ _ (by exact_mod_cast hπ.ne' : (2*Real.pi:ℂ)≠0)]
    congr 1
    ring
  have hπpow : (2*Real.pi:ℂ)^(-β-δ)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hπ.ne'))
  apply (mul_right_cancel₀ hπpow)
  calc
    _=((T:ℂ)^(-s)*(T:ℂ)^(s-β-δ))*
      ((2*Real.pi:ℂ)^(-(s-β-δ))*(2*Real.pi:ℂ)^(-β-δ)) := by ring
    _=(T:ℂ)^(-β-δ)*(2*Real.pi:ℂ)^(-s) := by rw [heT,heπ]
    _=_ := by field_simp


def a03ZeroModeGCDEtaMainAtS (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) (s : ℂ) : ℂ :=
  ∑g∈Finset.Icc 1 (min N₁ N₂),∑a∈Finset.Icc 1 (N₁/g),∑b∈Finset.Icc 1 (N₂/g),
    if a.Coprime b then a03ZeroModeGCDEtaMainX Φ T σ α g a b A B s else 0

theorem a03ZeroModeGCDEtaMainAtS_eq_AfterXMellin {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ α : MomentShifts)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) {s : ℂ} (hs : 0<s.re)
    (hq : 0<(s-α 1-α 3).re) :
    2*a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B s=
      a03ZeroModeTimeMoment Φ T α*a03ZeroModeContourPrefactor α*
        a03ZeroModeAfterXMellin N₁ N₂ A B α (polarPoleKiller T σ) s := by
  let q : ℂ := s-α 1-α 3
  let D : ℂ := (T:ℂ)^(-s)*Complex.Gamma s*Complex.cos (Real.pi*s/2)*
    (2*Real.pi:ℂ)^(-q)*(polarPoleKiller T σ (q/2)/q)*
    (∫t : ℝ,Φ t*(t:ℂ)^(-α 1-α 3))*a03ZeroModeContourPrefactor α*
    riemannZeta s*riemannZeta (1+α 0-α 1+α 2-α 3+s)
  have hNum (a b : ℕ) : a03ZeroModeRatioArithmeticNumerator α a b 0 0 s=
      a03ZeroModeContourPrefactor α*riemannZeta s*
        riemannZeta (1+α 0-α 1+α 2-α 3+s)*a03ZeroModeRatioEtaPair α a b 0 0 s := by
    unfold a03ZeroModeRatioArithmeticNumerator
    rw [a03ZeroModeRatioRemovedPair_zero α hρ]
    unfold a03ZeroModeRatioEulerArgument a03ZeroModeContourPrefactor
    simp only [mul_zero,add_zero]
    rw [show 2+α 0-α 1+α 2-α 3-1+s=1+α 0-α 1+α 2-α 3+s by ring]
    ring
  have hSum : a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B s=
      D*a03ZeroModeStaticEtaXMellinArithmetic N₁ N₂ A B α T s := by
    unfold a03ZeroModeGCDEtaMainAtS a03ZeroModeStaticEtaXMellinArithmetic
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g hg
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    split_ifs
    · rw [a03ZeroModeGCDEtaMainX_eq_xTimeMellin hΦ hSupp hT σ α
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hg).1)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
        (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1) A B hs hq,hNum]
      dsimp only [D,q]
      ring
    · exact (mul_zero D).symm
  rw [hSum,a03ZeroModeStaticEtaXMellinArithmetic_eq_MArithmetic N₁ N₂ A B α hT s]
  dsimp only [D,q]
  have hP := mainTimeScalePowers hT (α 1) (α 3) s
  unfold a03ZeroModeTimeMoment a03ZeroModeAfterXMellin a03ZeroModeGammaCosFactor
  calc
    _=((T:ℂ)^(-s)*(2*Real.pi:ℂ)^(-(s-α 1-α 3))*(T:ℂ)^(s-α 1-α 3))*
      (2*Complex.Gamma s*Complex.cos (Real.pi*s/2)*
        (polarPoleKiller T σ ((s-α 1-α 3)/2)/(s-α 1-α 3))*
        (∫t : ℝ,Φ t*(t:ℂ)^(-α 1-α 3))*a03ZeroModeContourPrefactor α*
        riemannZeta s*riemannZeta (1+α 0-α 1+α 2-α 3+s)*
        a03EtaMainArithmetic N₁ N₂ A B (α 0) (α 1) (α 2) (α 3) ((s-α 1-α 3)/2)) := by ring
    _=_ := by rw [hP]; ring

theorem a03ZeroModeGCDEtaMainAtS_vertical_eq_M {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ α : MomentShifts)
    (hα : ∀ j : Fin 4,‖α j‖≤1/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) {cs : ℝ} (hcs : 1<cs) :
    2*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B)=
      a03ZeroModeTimeMoment Φ T α*a03ZeroModeContourPrefactor α*
        verticalIntegral ((cs-(α 1+α 3).re)/2)
          (fun w => polarPoleKiller T σ w/w*a03EtaMainFunction N₁ N₂ A B α w) := by
  have hp (v : ℝ) :
      2*a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B ((cs:ℂ)+(v:ℂ)*I)=
      a03ZeroModeTimeMoment Φ T α*a03ZeroModeContourPrefactor α*
        a03ZeroModeAfterXMellin N₁ N₂ A B α (polarPoleKiller T σ) ((cs:ℂ)+(v:ℂ)*I) := by
    apply a03ZeroModeGCDEtaMainAtS_eq_AfterXMellin hΦ hSupp hT σ α hρ N₁ N₂ A B
    · simpa using zero_lt_one.trans hcs
    · have h₁ := (Complex.re_le_norm (α 1)).trans (hα 1)
      have h₃ := (Complex.re_le_norm (α 3)).trans (hα 3)
      simp only [Complex.sub_re,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,Complex.ofReal_im,neg_zero,add_zero]
      linarith
  have he : 2*verticalIntegral cs (a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B)=
      a03ZeroModeTimeMoment Φ T α*a03ZeroModeContourPrefactor α*
        verticalIntegral cs (a03ZeroModeAfterXMellin N₁ N₂ A B α (polarPoleKiller T σ)) := by
    unfold verticalIntegral
    rw [show (2:ℂ)*((1/(2*Real.pi):ℂ)*
      (∫v : ℝ,a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B ((cs:ℂ)+(v:ℂ)*I)))=
      (1/(2*Real.pi):ℂ)*
      (2*(∫v : ℝ,a03ZeroModeGCDEtaMainAtS Φ T σ α N₁ N₂ A B ((cs:ℂ)+(v:ℂ)*I))) by ring,
      ←integral_const_mul]
    simp_rw [hp]
    rw [integral_const_mul]
    ring
  rw [he,a03ZeroModeAfterXMellin_vertical_eq_M N₁ N₂ A B α (polarPoleKiller T σ) hcs]

end
end SixthMoment.Source
