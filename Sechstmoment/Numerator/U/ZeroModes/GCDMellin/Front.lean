import Sechstmoment.Analysis.Fourier.ProfileProduct
import Sechstmoment.Numerator.U.ZeroModes.Arithmetic.GCDDirichletEta
import Sechstmoment.Numerator.U.ZeroModes.Ratio.PhysicalPowers
import Sechstmoment.Numerator.U.ZeroModes.Transforms.SmoothedCosineGamma
import Sechstmoment.Numerator.U.ZeroModes.VStarMellin

namespace Sechstmoment.Source
open Complex Real Set MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 400000

def a03ZeroModeVStarTimeAmplitude (T : ℝ) (σ : MomentShifts) (g a b : ℕ)
    (x t : ℝ) : ℂ :=
  bblrVStar (polarPoleKiller T σ) (x^2/((T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)))^2*t^2))

def a03ZeroModeVStarTimeProfile (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (g a b : ℕ) (x : ℝ) : ℝ→ℂ :=
  a03ProfileProduct Φ (a03ZeroModeVStarTimeAmplitude T σ g a b x)

theorem a03ZeroModeVStarTimeAmplitude_contDiffAt {T : ℝ} (hT : 0<T)
    (σ : MomentShifts) {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b)
    {x t : ℝ} (hx : 0<x) (ht : 0<t) :
    ContDiffAt ℝ ∞ (a03ZeroModeVStarTimeAmplitude T σ g a b x) t := by
  let y : ℝ→ℝ := fun t => (2*Real.pi)^2*(x^2/((T*(g:ℝ)*Real.sqrt ((a:ℝ)*(b:ℝ)))^2*t^2))
  have hy : 0<y t := by
    dsimp [y]
    have hga : 0<(g:ℝ) := by exact_mod_cast hg
    have haa : 0<(a:ℝ) := by exact_mod_cast ha
    have hbb : 0<(b:ℝ) := by exact_mod_cast hb
    positivity
  have hyn : ContDiffAt ℝ ∞ y t := by
    dsimp [y]
    apply contDiffAt_const.mul
    apply contDiffAt_const.div (by fun_prop)
    have hga : 0<(g:ℝ) := by exact_mod_cast hg
    have haa : 0<(a:ℝ) := by exact_mod_cast ha
    have hbb : 0<(b:ℝ) := by exact_mod_cast hb
    positivity
  have hr := (a03ZeroModeRatioPartition_contDiffOn _ (rawMomentShifts T σ)
    (polarPoleKiller_BBLREntireWeight T σ _)).contDiffAt (Ioi_mem_nhds hy)
  apply (hr.comp t hyn).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with u hu
  exact a03VStar_eq_ratio_scaled (by
    have hga : 0<(g:ℝ) := by exact_mod_cast hg
    have haa : 0<(a:ℝ) := by exact_mod_cast ha
    have hbb : 0<(b:ℝ) := by exact_mod_cast hb
    have hup : 0<u := hu
    positivity) _

theorem a03ZeroModeVStarTimeProfile_contDiff {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts) {g a b : ℕ}
    (hg : 0<g) (ha : 0<a) (hb : 0<b) {x : ℝ} (hx : 0<x) :
    ContDiff ℝ ∞ (a03ZeroModeVStarTimeProfile Φ T σ g a b x) := by
  exact a03_profile_product_contDiff hΦ (fun t ht =>
    a03ZeroModeVStarTimeAmplitude_contDiffAt hT σ hg ha hb hx (zero_lt_one.trans_le (hSupp ht).1))

theorem a03ZeroModeVStarTimeProfile_support (Φ : ℝ→ℂ) (T : ℝ)
    (σ : MomentShifts) (g a b : ℕ) (x : ℝ) :
    tsupport (a03ZeroModeVStarTimeProfile Φ T σ g a b x)⊆tsupport Φ :=
  a03_profile_product_tsupport _ _

def a03ZeroModeGCDArchKernel (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (g a b : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  (x:ℂ)^s*mellin (fun u : ℝ => a03SmoothedCosine
    (a03ZeroModeVStarTimeProfile Φ T σ g a b x) (T*u)) s

def a03ZeroModeGCDArchTimeKernel (Φ : ℝ→ℂ) (T : ℝ) (σ : MomentShifts)
    (g a b : ℕ) (x : ℝ) (s : ℂ) : ℂ :=
  (x:ℂ)^s*(T:ℂ)^(-s)*Complex.Gamma s*Complex.cos (Real.pi*s/2)*
    ∫t : ℝ,a03ZeroModeVStarTimeProfile Φ T σ g a b x t*(t:ℂ)^(-s)

theorem a03ZeroModeGCDArchKernel_eq_time {Φ : ℝ→ℂ}
    (hΦ : ContDiff ℝ ∞ Φ) (hSupp : tsupport Φ⊆Icc (1:ℝ) 2)
    {T : ℝ} (hT : 0<T) (σ : MomentShifts) {g a b : ℕ}
    (hg : 0<g) (ha : 0<a) (hb : 0<b) {x : ℝ} (hx : 0<x)
    {s : ℂ} (hs : 0<s.re) :
    a03ZeroModeGCDArchKernel Φ T σ g a b x s=
      a03ZeroModeGCDArchTimeKernel Φ T σ g a b x s := by
  have hF := a03ZeroModeVStarTimeProfile_contDiff hΦ hSupp hT σ hg ha hb hx
  have hFs := (a03ZeroModeVStarTimeProfile_support Φ T σ g a b x).trans hSupp
  have he := (a03SmoothedCosine_scaled_hasMellin_gamma hF hFs hs hT).2
  unfold a03ZeroModeGCDArchKernel a03ZeroModeGCDArchTimeKernel
  rw [he]
  ring

def a03ZeroModeGCDEtaFrontBlock (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (g a b : ℕ) (A B : ℕ→ℂ) (u v s : ℂ) : ℂ :=
  ∫x : ℝ in Ioi 0,(x:ℂ)⁻¹*a03ZeroModeGCDArchKernel Φ T σ g a b x s*
    a03ZeroModeRatioPhysicalKernel α g a b A B x u v s

def a03ZeroModeGCDEtaFront (Φ : ℝ→ℂ) (T : ℝ) (σ α : MomentShifts)
    (N₁ N₂ : ℕ) (A B : ℕ→ℂ) (cu cv cs : ℝ) : ℂ :=
  ∑g∈Finset.Icc 1 (min N₁ N₂),∑a∈Finset.Icc 1 (N₁/g),∑b∈Finset.Icc 1 (N₂/g),
    if a.Coprime b then verticalIntegral cs (fun s =>
      a03ZeroModeRatioDoubleIntegral cu cv
        (fun u v => a03ZeroModeGCDEtaFrontBlock Φ T σ α g a b A B u v s)) else 0

end
end Sechstmoment.Source
