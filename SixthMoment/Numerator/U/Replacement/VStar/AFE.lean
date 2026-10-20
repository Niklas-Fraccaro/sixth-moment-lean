import SixthMoment.Numerator.U.Diagonal.ActualDiagonalTime
import SixthMoment.Numerator.U.Replacement.VStar.Definitions

namespace SixthMoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 2000000

theorem rectangular_VStar_Mellin_kernel_eq_diagonal (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) (z : ℂ) :
    rectangularVStarAFEMellinKernel G α t n z=
      rectangularAFEOscillation t n*actualDiagonalMellinKernel G α 1 1 t n z := by
  unfold rectangularVStarAFEMellinKernel bblrVStarKernel
  rw [actualDiagonal_quad_power_factorization t n z]
  unfold actualDiagonalMellinKernel actualDiagonalMellinFactor actualDiagonalQuadDirichletTerm
  norm_num only [Nat.one_mul,Nat.cast_one,Complex.one_cpow,div_one]
  have hp := rectangular_AFE_Mellin_powers α n z
  rw [div_eq_mul_inv] at hp
  simp only [one_div] at hp
  simp only [div_eq_mul_inv,one_mul]
  rw [←hp]
  ring

theorem bblrVStarAFESummand_eq_Mellin (G : ℂ → ℂ) (α : MomentShifts)
    (t : ℝ) (n : Fin 4 → ℕ) :
    bblrVStarAFESummand G α t n=verticalIntegral 1 (rectangularVStarAFEMellinKernel G α t n) := by
  unfold bblrVStarAFESummand bblrVStar verticalIntegral rectangularVStarAFEMellinKernel bblrVStarKernel
  dsimp only
  rw [integral_div,integral_const_mul]
  ring

theorem rectangular_actual_vstar_core_summand_Mellin (c T : ℝ)
    (σ α : MomentShifts) (t R : ℝ) (n : Fin 4 → ℕ) :
    bblrGaussianVStarCoreSummand c T σ α t R n=(1/(2*Real.pi):ℂ)*
      ∫ v in Icc (-R) R,
        rectangularVStarAFEMellinKernel (polarPoleKiller T σ) α t n ((c:ℂ)+(v:ℂ)*I) := by
  unfold bblrGaussianVStarCoreSummand bblrGaussianVStarCore rectangularVStarAFEMellinKernel
  rw [integral_div,integral_const_mul]
  ring

theorem actualDiagonalMellinKernel_joint_continuous_positive_line {c : ℝ} (hc : 0<c)
    (G : ℂ → ℂ) (hG : Continuous G) (α : MomentShifts) (n : Fin 4 → ℕ) :
    Continuous (fun p : ℝ×ℝ => actualDiagonalMellinKernel G α 1 1 p.1 n ((c:ℂ)+(p.2:ℂ)*I)) := by
  have htp : Continuous (fun p : ℝ×ℝ => ((p.1^2:ℝ):ℂ)^((c:ℂ)+(p.2:ℂ)*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hsq : 0≤(Complex.ofReal (p.1^2)).re := sq_nonneg p.1
    have hcre : 0<((c:ℂ)+(p.2:ℂ)*I).re := by simpa using hc
    have hh := Complex.continuousAt_cpow_of_re_pos
      (p := (Complex.ofReal (p.1^2),(c:ℂ)+(p.2:ℂ)*I)) (Or.inl hsq) hcre
    exact hh.comp₂ (g := fun q : ℝ×ℝ => Complex.ofReal (q.1^2))
      (h := fun q : ℝ×ℝ => (c:ℂ)+(q.2:ℂ)*I) (by fun_prop) (by fun_prop)
  unfold actualDiagonalMellinKernel actualDiagonalMellinFactor actualDiagonalQuadDirichletTerm
  norm_num only [Nat.one_mul,Nat.cast_one,Complex.one_cpow,div_one]
  apply Continuous.mul
  · apply Continuous.mul
    · apply Continuous.mul
      · apply Continuous.div
        · exact hG.comp (by fun_prop)
        · fun_prop
        · intro p hp
          have he := congrArg Complex.re hp
          have hc0 := hc.ne'
          simp at he
          exact hc0 he
      · apply Continuous.const_cpow (by fun_prop)
        exact Or.inl (by exact_mod_cast (show (2*Real.pi:ℝ)≠0 by positivity))
    · exact htp
  · apply Continuous.div continuous_const
    · apply continuous_finsetProd
      intro j _
      apply Continuous.const_cpow (by fun_prop)
      exact Or.inl (by exact_mod_cast Nat.succ_ne_zero (n j))
    · intro p
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      exact Complex.natCast_add_one_cpow_ne_zero (n j) _

theorem rectangularAFEOscillation_continuous (n : Fin 4 → ℕ) :
    Continuous (fun t : ℝ => rectangularAFEOscillation t n) := by
  unfold rectangularAFEOscillation
  apply Continuous.const_cpow (by fun_prop)
  apply Or.inl
  have h₁ : (((n 0+1)*(n 1+1):ℕ):ℂ)≠0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 0)) (Nat.succ_ne_zero (n 1))
  have h₂ : (((n 2+1)*(n 3+1):ℕ):ℂ)≠0 := by
    exact_mod_cast Nat.mul_ne_zero (Nat.succ_ne_zero (n 2)) (Nat.succ_ne_zero (n 3))
  exact div_ne_zero h₁ h₂

theorem rectangular_VStar_Mellin_kernel_joint_continuous {c : ℝ} (hc : 0<c)
    (G : ℂ → ℂ) (hG : Continuous G) (α : MomentShifts) (n : Fin 4 → ℕ) :
    Continuous (fun p : ℝ×ℝ => rectangularVStarAFEMellinKernel G α p.1 n ((c:ℂ)+(p.2:ℂ)*I)) := by
  simp only [rectangular_VStar_Mellin_kernel_eq_diagonal]
  exact ((rectangularAFEOscillation_continuous n).comp continuous_fst).mul
    (actualDiagonalMellinKernel_joint_continuous_positive_line hc G hG α n)

theorem bblrVStarAFESummand_time_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) (n : Fin 4 → ℕ) :
    StronglyMeasurable (fun t : ℝ => bblrVStarAFESummand G α t n) := by
  simp only [bblrVStarAFESummand_eq_Mellin,verticalIntegral]
  have hm := (rectangular_VStar_Mellin_kernel_joint_continuous (by norm_num : (0:ℝ)<1)
    G hG α n).stronglyMeasurable
  exact hm.integral_prod_right'.const_mul (1/(2*Real.pi):ℂ)

theorem bblrGaussianVStarCoreSummand_time_stronglyMeasurable {c : ℝ} (hc : 0<c)
    (T : ℝ) (σ α : MomentShifts) (R : ℝ) (n : Fin 4 → ℕ) :
    StronglyMeasurable (fun t : ℝ => bblrGaussianVStarCoreSummand c T σ α t R n) := by
  simp only [rectangular_actual_vstar_core_summand_Mellin]
  have hm := (rectangular_VStar_Mellin_kernel_joint_continuous hc
    (polarPoleKiller T σ) (polarPoleKiller_differentiable T σ).continuous α n).stronglyMeasurable
  exact (hm.integral_prod_right' (ν := volume.restrict (Icc (-R) R))).const_mul (1/(2*Real.pi):ℂ)

theorem bblrVStarAFESum_time_stronglyMeasurable (G : ℂ → ℂ) (hG : Continuous G)
    (α : MomentShifts) : StronglyMeasurable (bblrVStarAFESum G α) :=
  StronglyMeasurable.tsum (fun n => bblrVStarAFESummand_time_stronglyMeasurable G hG α n)

theorem bblrVStarAFESummand_large_line_norm_le (r : ℕ) (G : ℂ → ℂ) (α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) {B : ℝ} (hB : 0≤B)
    (hV : ∀ x : ℝ, 0<x → ‖bblrVStar G (x/t^2)‖≤B*x^(-(1+2*(r:ℝ))))
    (n : Fin 4 → ℕ) :
    ‖bblrVStarAFESummand G α t n‖≤
      (B*(positiveQuadProduct n:ℝ)^(-2*(r:ℝ)))*bblrGaussianAFEQuadMajorant n := by
  have hn (j : Fin 4) : 0<(n j+1:ℝ) := by positivity
  have hx : 0<(positiveQuadProduct n:ℝ) := by unfold positiveQuadProduct; positivity
  have hden : 0<∏ j : Fin 4, (n j+1:ℝ)^(1/2+(α j).re) :=
    Finset.prod_pos (fun j _ => Real.rpow_pos_of_pos (hn j) _)
  have he : ∏ j : Fin 4, (n j+1:ℝ)^(3/2+(α j).re)=
      (positiveQuadProduct n:ℝ)*∏ j : Fin 4, (n j+1:ℝ)^(1/2+(α j).re) := by
    have he' (j : Fin 4) : (n j+1:ℝ)^(3/2+(α j).re)=
        (n j+1:ℝ)*(n j+1:ℝ)^(1/2+(α j).re) := by
      rw [show (3/2:ℝ)+(α j).re=1+(1/2+(α j).re) by ring,
        Real.rpow_add (hn j),Real.rpow_one]
    simp_rw [he']
    rw [Finset.prod_mul_distrib,positiveQuadProduct_eq_prod]
    push_cast
    rfl
  have hcp (j : Fin 4) : ‖(n j+1:ℂ)^(1/2+α j)‖=(n j+1:ℝ)^(1/2+(α j).re) := by
    rw [show (n j+1:ℂ)=((n j+1:ℝ):ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (hn j)]
    congr 1
    simp
  have hp (j : Fin 4) : 1/(n j+1:ℝ)^(3/2+(α j).re)≤1/(n j+1:ℝ)^(5/4:ℝ) := by
    have har := (abs_le.mp ((Complex.abs_re_le_norm (α j)).trans (hα j))).1
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (hn j) _)
    exact Real.rpow_le_rpow_of_exponent_le (by norm_cast; omega) (by linarith)
  have hpow : (positiveQuadProduct n:ℝ)^(-(1+2*(r:ℝ)))=
      (positiveQuadProduct n:ℝ)^(-2*(r:ℝ))/(positiveQuadProduct n:ℝ) := by
    rw [show -(1+2*(r:ℝ))=(-2*(r:ℝ))-1 by ring,Real.rpow_sub hx,Real.rpow_one]
  unfold bblrVStarAFESummand
  have hosc : ‖rectangularAFEOscillation t n‖=1 := by
    simpa only [rectangularAFEOscillation] using bblrAFE_oscillation_norm_one n t
  rw [norm_div,norm_mul,hosc,one_mul,norm_prod]
  simp_rw [hcp]
  calc
    _ ≤ (B*((positiveQuadProduct n:ℝ)^(-2*(r:ℝ))/(positiveQuadProduct n:ℝ)))/
        (∏ j : Fin 4, (n j+1:ℝ)^(1/2+(α j).re)) := by
      rw [←hpow]
      exact div_le_div_of_nonneg_right (hV _ hx) hden.le
    _ = (B*(positiveQuadProduct n:ℝ)^(-2*(r:ℝ)))*
        ∏ j : Fin 4, 1/(n j+1:ℝ)^(3/2+(α j).re) := by
      rw [Finset.prod_div_distrib,Finset.prod_const_one,he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun j _ => hp j)) (by positivity)

theorem bblrVStar_zero (G : ℂ → ℂ) : bblrVStar G 0=0 := by
  unfold bblrVStar verticalIntegral
  have he : (fun v : ℝ => G ((1:ℂ)+(v:ℂ)*I)/((1:ℂ)+(v:ℂ)*I)*
      (2*Real.pi:ℂ)^(-2*((1:ℂ)+(v:ℂ)*I))*(0:ℂ)^(-((1:ℂ)+(v:ℂ)*I)))=0 := by
    funext v
    have hn : -((1:ℂ)+(v:ℂ)*I)≠0 := by intro h; have := congrArg Complex.re h; simp at this
    change _=(0:ℂ)
    rw [Complex.zero_cpow hn,mul_zero]
  simp only [Complex.ofReal_one,Complex.ofReal_zero]
  rw [he]
  simp

theorem bblrGaussianVStarAFESummand_norm_le (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) (n : Fin 4 → ℕ) :
    ‖bblrVStarAFESummand (polarPoleKiller T σ) α t n‖≤
      ((gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ 1*t^2)*
        bblrGaussianAFEQuadMajorant n := by
  by_cases ht : t=0
  · subst t
    simp [bblrVStarAFESummand,bblrVStar_zero]
  · have hCG := polarGaussianConstant_nonneg T σ 1
    have hJ := gaussianTailConstant_nonneg 48
    have hv : ∀ x : ℝ, 0<x → ‖bblrVStar (polarPoleKiller T σ) (x/t^2)‖≤
        ((gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ 1*t^2)*x^(-1:ℝ) := by
      intro x hx
      have h := bblrGaussianVStar_norm_le (div_pos hx (sq_pos_of_ne_zero ht))
        (by norm_num : (0:ℝ)<1) T σ
      convert h using 1
      norm_num only [div_one,Real.rpow_neg_one]
      field_simp
    simpa using bblrVStarAFESummand_large_line_norm_le 0 (polarPoleKiller T σ) α hα t
      (B := (gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ 1*t^2)
      (by positivity) (by simpa using hv) n

theorem bblrGaussianVStarAFE_norm_summable (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) :
    Summable (fun n : Fin 4 → ℕ => ‖bblrVStarAFESummand (polarPoleKiller T σ) α t n‖) := by
  have hCG := polarGaussianConstant_nonneg T σ 1
  have hJ := gaussianTailConstant_nonneg 48
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (bblrGaussianVStarAFESummand_norm_le T σ α hα t)
    (bblrGaussianAFEQuadMajorant_summable.mul_left _)

theorem bblrGaussianVStarAFE_summable (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) :
    Summable (bblrVStarAFESummand (polarPoleKiller T σ) α t) :=
  (bblrGaussianVStarAFE_norm_summable T σ α hα t).of_norm

theorem bblrGaussianVStarAFESum_norm_le (T : ℝ) (σ α : MomentShifts)
    (hα : ∀ j, ‖α j‖≤1/4) (t : ℝ) :
    ‖bblrVStarAFESum (polarPoleKiller T σ) α t‖≤
      ((gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ 1*t^2)*
        (∑' n : Fin 4 → ℕ, bblrGaussianAFEQuadMajorant n) := by
  have hs := bblrGaussianVStarAFE_norm_summable T σ α hα t
  unfold bblrVStarAFESum
  calc
    _ ≤ ∑' n, ‖bblrVStarAFESummand (polarPoleKiller T σ) α t n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n, ((gaussianTailConstant 48/(2*Real.pi))*polarGaussianConstant T σ 1*t^2)*
        bblrGaussianAFEQuadMajorant n := hs.tsum_le_tsum
      (bblrGaussianVStarAFESummand_norm_le T σ α hα t) (bblrGaussianAFEQuadMajorant_summable.mul_left _)
    _ = _ := tsum_mul_left

end
end SixthMoment
