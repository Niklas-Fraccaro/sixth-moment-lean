import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.FrontFubini
import Sechstmoment.Numerator.U.ZeroModes.GCDMellin.InitialKernel

/-! Exact identification of the original GCD Mellin density with the literal
eta front.  The common amplifier gcd, all powers, and the original coefficient
arguments are preserved. -/
namespace Sechstmoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 500000

theorem a03ZeroModeGCDArchKernel_commonAmplifier (Φ : ℝ→ℂ) (T : ℝ)
    (σ : MomentShifts) (g a b : ℕ) (x : ℝ) (s : ℂ) :
    a03ZeroModeGCDArchKernel Φ T σ 1 (g*a) (g*b) x s=
      a03ZeroModeGCDArchKernel Φ T σ g a b x s := by
  have hscale : T*(1:ℝ)*Real.sqrt (((g*a:ℕ):ℝ)*((g*b:ℕ):ℝ))=
      T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)) := by
    rw [Nat.cast_mul,Nat.cast_mul]
    have he : (g:ℝ)*(a:ℝ)*((g:ℝ)*(b:ℝ))=(g:ℝ)^2*((a:ℝ)*(b:ℝ)) := by ring
    rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg g)]
    ring
  have hAmplitude : a03ZeroModeVStarTimeAmplitude T σ 1 (g*a) (g*b) x=
      a03ZeroModeVStarTimeAmplitude T σ g a b x := by
    funext t
    unfold a03ZeroModeVStarTimeAmplitude
    rw [Nat.cast_one,hscale]
  simp only [a03ZeroModeGCDArchKernel,a03ZeroModeVStarTimeProfile,hAmplitude]

theorem a03ZeroModeRatioArithmeticKernel_eq_gcdDirichlet
    (α : MomentShifts) {a b : ℕ} (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    (u v s : ℂ) (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    a03ZeroModeRatioArithmeticKernel α a b u v s=
      (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*
        riemannZeta s*a03GCDDirichlet a b (α 0-α 1+2*u) (α 2-α 3+2*v) s := by
  have hrootU : u≠a03ZeroModeRatioRoot α 0 := by
    intro he
    have hz : α 0-α 1+2*a03ZeroModeRatioRoot α 0=0 := by
      norm_num [a03ZeroModeRatioRoot]
      ring
    rw [he,hz] at hu
    exact lt_irrefl _ hu
  have hrootV : v≠a03ZeroModeRatioRoot α 1 := by
    intro he
    have hz : α 2-α 3+2*a03ZeroModeRatioRoot α 1=0 := by
      norm_num [a03ZeroModeRatioRoot]
      ring
    rw [he,hz] at hv
    exact lt_irrefl _ hv
  unfold a03ZeroModeRatioArithmeticKernel
  rw [a03ZeroModeRatioArithmeticNumerator_eq α a b s hρ hrootU hrootV,
    a03_source_gcdDirichlet_eq_ratioEta ha hb hab α u v s hu hv hs]
  unfold a03GCDZetaQuotient
  rw [show 1+(α 0-α 1+2*u)+(α 2-α 3+2*v)+s=
      1+α 0-α 1+α 2-α 3+2*u+2*v+s by ring,
    show 1+(α 0-α 1+2*u)=1+α 0-α 1+2*u by ring,
    show 1+(α 2-α 3+2*v)=1+α 2-α 3+2*v by ring,
    show 2+(α 0-α 1+2*u)+(α 2-α 3+2*v)=
      2+α 0-α 1+α 2-α 3+2*u+2*v by ring]
  ring

theorem a03ZeroModeGCDInitialKernel_commonAmplifier_eq_etaDensity
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (hab : a.Coprime b)
    (A B : ℕ→ℂ) {x : ℝ} (hx : 0<x) (u v s : ℂ)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    a03ZeroModeGCDInitialKernel Φ T σ α (g*a) (g*b) A B x u v s=
      a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x u v s := by
  have hx0 : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hg0 : (g:ℂ)≠0 := Nat.cast_ne_zero.mpr hg.ne'
  have hxpow : (x:ℂ)^(-1-α 1-α 3+u+v)=
      (x:ℂ)⁻¹*(x:ℂ)^(-α 1-α 3+u+v) := by
    rw [←Complex.cpow_neg_one,←Complex.cpow_add _ _ hx0]
    congr 1
    ring
  have hgpow : (g:ℂ)^(-1+α 1-u)*(g:ℂ)^(-1+α 3-v)*(g:ℂ)^(1-s)=
      (g:ℂ)^(-1+α 1+α 3-u-v-s) := by
    rw [←Complex.cpow_add _ _ hg0,←Complex.cpow_add _ _ hg0]
    congr 1
    ring
  unfold a03ZeroModeGCDInitialKernel a03ZeroModeGCDInitialBase
  rw [a03GCDDirichlet_commonAmplifier,a03ZeroModeGCDArchKernel_commonAmplifier,
    Nat.cast_mul,Nat.cast_mul,Complex.natCast_mul_natCast_cpow,
    Complex.natCast_mul_natCast_cpow,hxpow]
  unfold a03ZeroModeGCDInitialDensity a03ZeroModeRatioPhysicalKernel
  rw [a03ZeroModeRatioArithmeticKernel_eq_gcdDirichlet α ha hb hab u v s hρ hu hv hs]
  calc
    _=((g:ℂ)^(-1+α 1-u)*(g:ℂ)^(-1+α 3-v)*(g:ℂ)^(1-s))*
      (A (g*a)*B (g*b)*(a:ℂ)^(-1+α 1-u)*(b:ℂ)^(-1+α 3-v)*
        (x:ℂ)⁻¹*(x:ℂ)^(-α 1-α 3+u+v)*
        (a03ZeroModeRatioWeight α u/u)*(a03ZeroModeRatioWeight α v/v)*
        a03ZeroModeGCDArchKernel Φ T σ g a b x s*riemannZeta s*
        a03GCDDirichlet a b (α 0-α 1+2*u) (α 2-α 3+2*v) s) := by ring
    _=_ := by rw [hgpow]; ring

theorem a03ZeroModeGCDInitialKernel_eq_commonAmplifier_etaDensity
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    {a b : ℕ} (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {x : ℝ} (hx : 0<x) (u v s : ℂ)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s=
      a03ZeroModeGCDInitialDensity Φ T σ α (Nat.gcd a b)
        (a/Nat.gcd a b) (b/Nat.gcd a b) A B x u v s := by
  have hg : 0<Nat.gcd a b := Nat.gcd_pos_of_pos_left _ ha
  have ha' : 0<a/Nat.gcd a b := Nat.div_pos (Nat.gcd_le_left _ ha) hg
  have hb' : 0<b/Nat.gcd a b := Nat.div_pos (Nat.gcd_le_right _ hb) hg
  convert a03ZeroModeGCDInitialKernel_commonAmplifier_eq_etaDensity Φ T σ α
    hg ha' hb' (Nat.coprime_div_gcd_div_gcd hg) A B hx u v s hρ hu hv hs using 1
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left a b),Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)]

theorem a03ZeroModeGCDInitialKernel_finiteAmplifiers_eq_etaDensity
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) {x : ℝ} (hx : 0<x) (u v s : ℂ)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    (hu : 0<(α 0-α 1+2*u).re) (hv : 0<(α 2-α 3+2*v).re) (hs : 1<s.re) :
    (∑a∈Finset.Icc 1 N₁,∑b∈Finset.Icc 1 N₂,
      a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s)=
      ∑g∈Finset.Icc 1 (min N₁ N₂),∑a∈Finset.Icc 1 (N₁/g),∑b∈Finset.Icc 1 (N₂/g),
        if a.Coprime b then a03ZeroModeGCDInitialDensity Φ T σ α g a b A B x u v s else 0 := by
  rw [a03FiniteAmplifier_gcd_reindex]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  exact a03ZeroModeGCDInitialKernel_eq_commonAmplifier_etaDensity Φ T σ α
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1)
    (lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1) A B hx u v s hρ hu hv hs

def a03ZeroModeGCDInitialFront (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) (cu cv cs : ℝ) : ℂ :=
  ∑a∈Finset.Icc 1 N₁,∑b∈Finset.Icc 1 N₂,verticalIntegral cs (fun s =>
    a03ZeroModeRatioDoubleIntegral cu cv (fun u v =>
      ∫x : ℝ in Ioi 0,a03ZeroModeGCDInitialKernel Φ T σ α a b A B x u v s))

theorem a03ZeroModeGCDInitialFront_eq_etaFront
    (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) {ε : ℝ} (hε : 0<ε)
    (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) :
    a03ZeroModeGCDInitialFront Φ T σ α N₁ N₂ A B ε ε (1+ε)=
      a03ZeroModeGCDEtaFront Φ T σ α N₁ N₂ A B ε ε (1+ε) := by
  unfold a03ZeroModeGCDInitialFront a03ZeroModeGCDEtaFront
  have hReindex := a03FiniteAmplifier_gcd_reindex N₁ N₂
    (fun g a b => verticalIntegral (1+ε) (fun s => a03ZeroModeRatioDoubleIntegral ε ε
      (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v s)))
  conv_rhs => rw [hReindex]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha' : 0<a := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp ha).1
  have hb' : 0<b := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hb).1
  have hre (j : Fin 4) : |(α j).re|≤ε/8 := (Complex.abs_re_le_norm _).trans (hα j)
  unfold verticalIntegral
  apply congrArg (fun z : ℂ => (1/(2*Real.pi):ℂ)*z)
  apply integral_congr_ae
  apply ae_of_all
  intro sy
  dsimp only
  unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
  apply congrArg (fun z : ℂ => (1/(2*Real.pi):ℂ)*z)
  apply integral_congr_ae
  apply ae_of_all
  intro uy
  dsimp only
  apply congrArg (fun z : ℂ => (1/(2*Real.pi):ℂ)*z)
  apply integral_congr_ae
  apply ae_of_all
  intro vy
  dsimp only
  unfold a03ZeroModeGCDEtaFrontBlock
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  apply a03ZeroModeGCDInitialKernel_eq_commonAmplifier_etaDensity Φ T σ α ha' hb' A B hx _ _ _ hρ
  · norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    linarith [(abs_le.mp (hre 0)).1,(abs_le.mp (hre 1)).2]
  · norm_num [Complex.add_re,Complex.sub_re,Complex.mul_re]
    linarith [(abs_le.mp (hre 2)).1,(abs_le.mp (hre 3)).2]
  · norm_num [Complex.add_re,Complex.mul_re]
    linarith

end
end Sechstmoment.Source
