import SixthMoment.Numerator.U.ZeroModes.Ratio.ResidualUniform

namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioPhysicalResidual (ε : ℝ) (α : MomentShifts) (g a b : ℕ)
    (A B : ℕ→ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*
    a03ZeroModeRatioResidual (a03ZeroModeRatioPhysicalLogLeft g a x)
      (a03ZeroModeRatioPhysicalLogRight g b x) ε α a b s

theorem a03ZeroModeRatioPhysicalKernel_eq_main_add_residual
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (α : MomentShifts) (hα : ∀ j : Fin 4,‖α j‖≤ε/8)
    (hρ : ∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {x : ℝ} (hx : 0<x) {s : ℂ} (hs : 1+ε≤s.re) :
    a03ZeroModeRatioDoubleIntegral ε ε (fun u v => a03ZeroModeRatioPhysicalKernel α g a b A B x u v s)=
      a03ZeroModeRatioPhysicalPrefactor α g a b A B x s*
        a03ZeroModeRatioArithmeticNumerator α a b 0 0 s+
      a03ZeroModeRatioPhysicalResidual ε α g a b A B x s := by
  simp_rw [a03ZeroModeRatioPhysicalKernel_eq_weighted α hg ha hb A B hx]
  rw [a03ZeroModeRatioDoubleIntegral_const_mul,
    a03ZeroModeRatioWeightedKernel_double_shift _ _ hε hε1 hδ α hα hρ ha.ne' hb.ne' hs]
  unfold a03ZeroModeRatioPhysicalResidual a03ZeroModeRatioResidual
  ring

theorem a03ZeroModeRatioPhysicalPrefactor_norm (α : MomentShifts)
    {g a b : ℕ} (hg : 0<g) (ha : 0<a) (hb : 0<b) (A B : ℕ→ℂ)
    {x : ℝ} (hx : 0<x) (s : ℂ) :
    ‖a03ZeroModeRatioPhysicalPrefactor α g a b A B x s‖=
      ‖A (g*a)‖*‖B (g*b)‖*(g:ℝ)^(-1+(α 1).re+(α 3).re-s.re)*
        (a:ℝ)^(-1+(α 1).re)*(b:ℝ)^(-1+(α 3).re)*x^(-(α 1).re-(α 3).re) := by
  unfold a03ZeroModeRatioPhysicalPrefactor
  simp only [norm_mul,Complex.norm_natCast_cpow_of_pos hg,
    Complex.norm_natCast_cpow_of_pos ha,Complex.norm_natCast_cpow_of_pos hb,
    Complex.norm_cpow_eq_rpow_re_of_pos hx,sub_re,add_re,neg_re,one_re]

theorem a03ZeroModeRatioPhysicalLogLeft_exp {g a : ℕ} (hg : 0<g) (ha : 0<a)
    {x : ℝ} (hx : 0<x) (c : ℝ) :
    Real.exp (a03ZeroModeRatioPhysicalLogLeft g a x*c)=(x/(g*a:ℕ))^c := by
  unfold a03ZeroModeRatioPhysicalLogLeft
  rw [Real.rpow_def_of_pos (div_pos hx (by exact_mod_cast Nat.mul_pos hg ha))]

theorem a03ZeroModeRatioPhysicalLogRight_exp {g b : ℕ} (hg : 0<g) (hb : 0<b)
    {x : ℝ} (hx : 0<x) (c : ℝ) :
    Real.exp (a03ZeroModeRatioPhysicalLogRight g b x*c)=(x/(g*b:ℕ))^c :=
  a03ZeroModeRatioPhysicalLogLeft_exp hg hb hx c

theorem a03ZeroModeRatioPhysicalLogPair_exp {g a b : ℕ}
    (hg : 0<g) (ha : 0<a) (hb : 0<b) {x : ℝ} (hx : 0<x) (c : ℝ) :
    Real.exp ((a03ZeroModeRatioPhysicalLogLeft g a x+a03ZeroModeRatioPhysicalLogRight g b x)*c)=
      (x/(g*a:ℕ))^c*(x/(g*b:ℕ))^c := by
  rw [add_mul,Real.exp_add,a03ZeroModeRatioPhysicalLogLeft_exp hg ha hx,
    a03ZeroModeRatioPhysicalLogRight_exp hg hb hx]

theorem a03ZeroModeRatioPhysicalResidual_uniform_log_bound (K : Set MomentShifts) (hK : IsCompact K)
    {κ ε δ : ℝ} (hκ : 0<κ) (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ)
    (hρ : ∀ σ∈K,∀ k : PurePolarIndex,κ≤‖normalizedPurePolarRoot σ k‖) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ∈K,∀ g a b : ℕ,0<g → 0<a → 0<b →
      ∀ A B : ℕ→ℂ,∀ x : ℝ,0<x → ∀ s : ℂ,1+ε≤s.re →
      ‖a03ZeroModeRatioPhysicalResidual ε (rawMomentShifts T σ) g a b A B x s‖≤
        C*(Real.log T)^8*‖a03ZeroModeRatioPhysicalPrefactor (rawMomentShifts T σ) g a b A B x s‖*
          (a:ℝ)^δ*(b:ℝ)^δ*
          ((x/(g*a:ℕ))^(a03ZeroModeRatioPrimaryLine ε)*(x/(g*b:ℕ))^(a03ZeroModeRatioPrimaryLine ε)+
           (x/(g*b:ℕ))^(a03ZeroModeRatioSecondaryLine ε)+
           (x/(g*a:ℕ))^(a03ZeroModeRatioSecondaryLine ε)) := by
  obtain ⟨C,hC,hbound⟩ := a03ZeroModeRatioResidual_uniform_log_bound K hK hκ hε hε1 hδ hρ
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound] with T hbnd
  intro σ hσ g a b hg ha hb A B x hx s hs
  have hh := hbnd σ hσ a b ha.ne' hb.ne'
    (a03ZeroModeRatioPhysicalLogLeft g a x) (a03ZeroModeRatioPhysicalLogRight g b x) s hs
  rw [a03ZeroModeRatioPhysicalLogPair_exp hg ha hb hx,
    a03ZeroModeRatioPhysicalLogRight_exp hg hb hx,
    a03ZeroModeRatioPhysicalLogLeft_exp hg ha hx] at hh
  unfold a03ZeroModeRatioPhysicalResidual
  rw [norm_mul]
  exact (mul_le_mul_of_nonneg_left hh (norm_nonneg _)).trans_eq (by ring)

end
end SixthMoment.Source
