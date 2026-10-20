import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import SixthMoment.Zeta.Bounds.MellinZetaNegativeStripGrowth
import SixthMoment.Zeta.Gamma.VerticalDecay


namespace SixthMoment
open Complex Real MeasureTheory Filter Set Asymptotics
open scoped Topology
noncomputable section
set_option maxHeartbeats 1000000

private theorem d04Complex_cos_norm_le_exp_abs_im (z : ℂ) :
    ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos,norm_div]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  calc
    _ ≤ ‖Complex.exp (z*I)‖+‖Complex.exp (-z*I)‖ := norm_add_le _ _
    _ = Real.exp (-z.im)+Real.exp z.im := by
      rw [Complex.norm_exp,Complex.norm_exp]
      simp
    _ ≤ Real.exp |z.im|+Real.exp |z.im| :=
      add_le_add (Real.exp_le_exp.mpr (neg_le_abs _))
        (Real.exp_le_exp.mpr (le_abs_self _))
    _ = _ := by ring

theorem d04GammaCos_sharp_positive_strip {s : ℂ}
    (hs : s.re ∈ Icc (1 : ℝ) 2) (him : 128 ≤ |s.im|) :
    ‖Complex.Gamma s*Complex.cos ((Real.pi : ℂ)*s/2)‖ ≤
      (2*(2*Real.pi+1))*(1+|s.im|)^(s.re-1/2) := by
  let b : ℂ := (1/2 : ℂ)+(s.im : ℂ)*I
  let u : ℂ := ((s.re-1/2 : ℝ):ℂ)
  let R : ℂ := (Complex.Gamma (b+u)/Complex.Gamma b)/b^u
  have he : b+u=s := by apply Complex.ext <;> simp [b,u]
  have hu : ‖u‖ ≤ 3/2 := by
    dsimp [u]
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
  have hbi : b.im=s.im := by simp [b]
  have hbr : b.re=1/2 := by simp [b]
  have herr : ‖R-1‖ ≤ 1/2 := by
    have h := gammaRatio_normalized_error_vertical b u
      (by rw [hbr]; norm_num) (by rw [hbi]; linarith)
      (by rw [hbi]; nlinarith [norm_nonneg u,sq_nonneg ‖u‖])
    apply h.trans
    rw [hbi,div_le_iff₀ (by linarith : 0 < |s.im|)]
    nlinarith [norm_nonneg u,sq_nonneg ‖u‖]
  have hR : ‖R‖ ≤ 2 := by
    have h := norm_add_le (R-1) (1 : ℂ)
    rw [sub_add_cancel,norm_one] at h
    linarith
  have hb0 : b≠0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [hbr] at hr
  have hΓ0 := Complex.Gamma_ne_zero_of_re_pos (by rw [hbr]; norm_num)
  have hp0 : b^u≠0 := by simp [hb0]
  have hΓ : Complex.Gamma (b+u)=R*b^u*Complex.Gamma b := by
    dsimp [R]
    field_simp
  have hbP : ‖b‖ ≤ 1+|s.im| := by
    dsimp [b]
    exact (norm_add_le _ _).trans (by simp; linarith [abs_nonneg s.im])
  have hp : ‖b^u‖ ≤ (1+|s.im|)^(s.re-1/2) := by
    rw [show ‖b^u‖=‖b‖^(s.re-1/2) by
      dsimp [u]; exact Complex.norm_cpow_real _ _]
    exact Real.rpow_le_rpow (norm_nonneg _) hbP (by linarith [hs.1])
  have hrelative : ‖Complex.Gamma s‖ ≤
      2*(1+|s.im|)^(s.re-1/2)*‖Complex.Gamma b‖ := by
    have hΓs : Complex.Gamma s = R*b^u*Complex.Gamma b := by rwa [he] at hΓ
    rw [hΓs,norm_mul,norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hR hp (norm_nonneg _) (by norm_num)) (norm_nonneg _)
  have hhalf : ‖Complex.Gamma b‖*Real.exp (Real.pi*|s.im|/2) ≤ 2*Real.pi+1 :=
    (Source.gamma_half_weighted_norm_bounds s.im).2
  have hcos : ‖Complex.cos ((Real.pi : ℂ)*s/2)‖ ≤
      Real.exp (Real.pi*|s.im|/2) := by
    have h := d04Complex_cos_norm_le_exp_abs_im ((Real.pi : ℂ)*s/2)
    have hi : |(((Real.pi : ℂ)*s/2).im)|=Real.pi*|s.im|/2 := by
      simp only [Complex.div_ofNat_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,add_zero,abs_div,abs_mul,abs_of_pos Real.pi_pos]
      norm_num
    rwa [hi] at h
  rw [norm_mul]
  calc
    _ ≤ ‖Complex.Gamma s‖*Real.exp (Real.pi*|s.im|/2) := by gcongr
    _ ≤ (2*(1+|s.im|)^(s.re-1/2)*‖Complex.Gamma b‖)*
        Real.exp (Real.pi*|s.im|/2) := by gcongr
    _ = (2*(1+|s.im|)^(s.re-1/2))*(‖Complex.Gamma b‖*
        Real.exp (Real.pi*|s.im|/2)) := by ring
    _ ≤ (2*(1+|s.im|)^(s.re-1/2))*(2*Real.pi+1) := by gcongr
    _ = _ := by ring

theorem d04RiemannZeta_sharp_left_strip {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → s.re ≤ -ε →
      128 ≤ |s.im| → ‖riemannZeta s‖ ≤ C*(1+|s.im|)^(1/2-s.re) := by
  let Z := zetaDirichletMajorant (1+ε)
  have hZ : 0 ≤ Z := zetaDirichletMajorant_nonneg _
  let K : ℝ := 2*(2*Real.pi+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨2*K*Z,by positivity,?_⟩
  intro s hs0 hsε him
  let u : ℂ := 1-s
  have hu : u.re=1-s.re := by simp [u]
  have hui : |u.im|=|s.im| := by simp [u]
  have hus : u.re ∈ Icc (1 : ℝ) 2 := by rw [hu]; constructor <;> linarith
  have hFE := riemannZeta_one_sub (s := u) (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [hu,Complex.neg_re,Complex.natCast_re] at h
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith) (by
      intro he
      have h := congrArg Complex.re he
      simp only [hu,Complex.one_re] at h
      linarith)
  have hGC := d04GammaCos_sharp_positive_strip hus (by rwa [hui])
  have hexp : u.re-1/2=1/2-s.re := by rw [hu]; ring
  rw [hui,hexp] at hGC
  have hζ : ‖riemannZeta u‖ ≤ Z :=
    riemannZeta_norm_le_dirichlet (by linarith) (by rw [hu]; linarith)
  have hpower : ‖(2*(Real.pi : ℂ))^(-u)‖ ≤ 1 := by
    have he : 2*(Real.pi : ℂ)=((2*Real.pi : ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),Complex.neg_re]
    simpa using Real.rpow_le_rpow_of_exponent_le
      (by linarith [Real.two_le_pi] : 1 ≤ 2*Real.pi) (show -u.re ≤ 0 by linarith [hus.1])
  have he : 1-u=s := by dsimp [u]; ring
  rw [he] at hFE
  rw [hFE,show 2*(2*(Real.pi : ℂ))^(-u)*Complex.Gamma u*
    Complex.cos ((Real.pi : ℂ)*u/2)*riemannZeta u =
    (2*(2*(Real.pi : ℂ))^(-u))*(Complex.Gamma u*
      Complex.cos ((Real.pi : ℂ)*u/2))*riemannZeta u by ring,
    norm_mul,norm_mul,norm_mul,Complex.norm_ofNat]
  calc
    _ ≤ (2*1)*(K*(1+|s.im|)^(1/2-s.re))*Z := by gcongr
    _ = _ := by ring

private theorem d04Zeta_left_boundary_high :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = -1 → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^5 := by
  obtain ⟨C,hC,hGamma⟩ := d04Gamma_vertical_strip_norm_le
  let Z := zetaDirichletMajorant 2
  have hZ : 0 ≤ Z := zetaDirichletMajorant_nonneg 2
  refine ⟨2*(2*Real.pi)^(-2 : ℝ)*C*Z,by positivity,?_⟩
  intro s hs him
  let u : ℂ := 1-s
  have hu : u.re=2 := by norm_num [u,hs]
  have hui : |u.im|=|s.im| := by simp [u]
  have hFE := riemannZeta_one_sub (s := u) (by
    intro n hn
    have h := congrArg Complex.re hn
    simp only [hu,Complex.neg_re,Complex.natCast_re] at h
    have hn0 : (0:ℝ)≤n := Nat.cast_nonneg n
    linarith) (by
      intro he
      have h := congrArg Complex.re he
      norm_num [hu] at h)
  have hΓ := hGamma u (by rw [hu]; norm_num) (by rw [hu]) (by rwa [hui])
  have hcos : ‖Complex.cos ((Real.pi : ℂ)*u/2)‖ ≤
      Real.exp (Real.pi*|s.im|/2) := by
    have h := d04Complex_cos_norm_le_exp_abs_im ((Real.pi : ℂ)*u/2)
    have he : |(((Real.pi : ℂ)*u/2).im)|=Real.pi*|s.im|/2 := by
      simp only [Complex.div_ofNat_im,Complex.mul_im,Complex.ofReal_re,
        Complex.ofReal_im,zero_mul,add_zero,abs_div,abs_mul,
        abs_of_pos Real.pi_pos]
      rw [hui]
      norm_num
    rwa [he] at h
  have hZeta : ‖riemannZeta u‖ ≤ Z :=
    riemannZeta_norm_le_dirichlet (by norm_num) (by rw [hu])
  have hpower : ‖(2*(Real.pi : ℂ))^(-u)‖ = (2*Real.pi)^(-2 : ℝ) := by
    have he : 2*(Real.pi : ℂ)=((2*Real.pi : ℝ):ℂ) := by push_cast; rfl
    rw [he,Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp [hu]
  have hGC : ‖Complex.Gamma u*Complex.cos ((Real.pi : ℂ)*u/2)‖ ≤
      C*(1+|s.im|)^5 := by
    rw [norm_mul]
    calc
      _ ≤ (C*(1+|s.im|)^5*Real.exp (-(Real.pi*|s.im|/2)))*
          Real.exp (Real.pi*|s.im|/2) := by rw [hui] at hΓ; gcongr
      _ = _ := by rw [mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one]
  have he : 1-u=s := by dsimp [u]; ring
  rw [he] at hFE
  rw [hFE,show 2*(2*(Real.pi : ℂ))^(-u)*Complex.Gamma u*
    Complex.cos ((Real.pi : ℂ)*u/2)*riemannZeta u =
    (2*(2*(Real.pi : ℂ))^(-u))*(Complex.Gamma u*
      Complex.cos ((Real.pi : ℂ)*u/2))*riemannZeta u by ring,
    norm_mul,norm_mul,norm_mul,Complex.norm_ofNat,hpower]
  calc
    _ ≤ (2*(2*Real.pi)^(-2 : ℝ))*(C*(1+|s.im|)^5)*Z := by gcongr
    _ = _ := by ring

private theorem d04Zeta_left_boundary :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, s.re = -1 →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^5 := by
  obtain ⟨C,hC,hhigh⟩ := d04Zeta_left_boundary_high
  let f : ℝ → ℂ := fun v => riemannZeta (-1+(v : ℂ)*I)
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro v
    apply (differentiableAt_riemannZeta ?_).continuousAt.comp
      (by fun_prop)
    intro he
    have h := congrArg Complex.re he
    norm_num at h
  obtain ⟨D,hD⟩ := isCompact_Icc.bddAbove_image (hf.norm.continuousOn :
    ContinuousOn (fun v => ‖f v‖) (Icc (-1 : ℝ) 1))
  let K : ℝ := max C (max 0 D)
  have hK : 0 ≤ K := hC.trans (le_max_left _ _)
  refine ⟨K,hK,?_⟩
  intro s hs
  by_cases hi : 1 ≤ |s.im|
  · exact (hhigh s hs hi).trans (mul_le_mul_of_nonneg_right
      (le_max_left _ _) (by positivity))
  · have he : -1+(s.im : ℂ)*I=s := by apply Complex.ext <;> simp [hs]
    have h := hD (mem_image_of_mem (fun v => ‖f v‖)
      (abs_le.mp (le_of_lt (lt_of_not_ge hi))))
    dsimp [f] at h
    rw [he] at h
    calc
      _ ≤ D := h
      _ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
      _ ≤ K*(1+|s.im|)^5 := le_mul_of_one_le_right hK
        (one_le_pow₀ (by linarith [abs_nonneg s.im]))

def d04PoleRemovedZeta (s : ℂ) : ℂ :=
  (Real.pi : ℂ)^(s/2)*(1/Complex.Gamma (s/2+1))*
    (s*(s-1)*completedRiemannZeta₀ s+1)/2

theorem d04PoleRemovedZeta_differentiable : Differentiable ℂ d04PoleRemovedZeta := by
  have hπ : Differentiable ℂ (fun s : ℂ => (Real.pi : ℂ)^(s/2)) :=
    (differentiable_id.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hΓ : Differentiable ℂ (fun s : ℂ => 1/Complex.Gamma (s/2+1)) := by
    simp only [one_div]
    exact Complex.differentiable_one_div_Gamma.comp
      ((differentiable_id.div_const (2 : ℂ)).add_const 1)
  exact ((hπ.mul hΓ).mul (((differentiable_id.mul
    (differentiable_id.sub_const 1)).mul differentiable_completedZeta₀).add_const 1)).div_const 2

theorem d04PoleRemovedZeta_eq {s : ℂ} (hs : -1 ≤ s.re) (hs1 : s ≠ 1) :
    d04PoleRemovedZeta s = (s-1)*riemannZeta s := by
  have hπ : (Real.pi : ℂ)^(s/2) ≠ 0 := by
    simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  have hΓ : Complex.Gamma (s/2+1) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [Complex.add_re,
      Complex.div_ofNat_re,Complex.one_re]; linarith)
  have h1 : 1-s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  rw [riemannZeta_eq_mul_completedRiemannZeta₀]
  unfold d04PoleRemovedZeta
  rw [show -s/2=-(s/2) by ring,Complex.cpow_neg]
  field_simp
  ring

private def d04ZetaStripNormalized (s : ℂ) : ℂ := d04PoleRemovedZeta s/(s+3)^6

private theorem d04ZetaStrip_den_norm {s : ℂ} (hs : -1 ≤ s.re) :
    2 ≤ ‖s+3‖ := by
  have h := Complex.re_le_norm (s+3)
  simp only [Complex.add_re] at h
  norm_num at h
  linarith

private theorem d04ZetaStripNormalized_diffContOnCl :
    DiffContOnCl ℂ d04ZetaStripNormalized (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) := by
  have hd : DifferentiableOn ℂ d04ZetaStripNormalized
      (Complex.re ⁻¹' Icc (-1 : ℝ) 2) := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply (d04PoleRemovedZeta_differentiable s).div
      (((differentiableAt_id.add_const 3).pow 6))
    exact pow_ne_zero 6 (norm_pos_iff.mp
      (lt_of_lt_of_le (by norm_num) (d04ZetaStrip_den_norm hs.1)))
  have hcl : closure (Complex.re ⁻¹' Ioo (-1 : ℝ) 2) ⊆
      Complex.re ⁻¹' Icc (-1 : ℝ) 2 :=
    closure_minimal (preimage_mono Ioo_subset_Icc_self)
      (isClosed_Icc.preimage Complex.continuous_re)
  exact ⟨hd.mono (preimage_mono Ioo_subset_Icc_self),hd.continuousOn.mono hcl⟩

private theorem d04ZetaStripNormalized_boundary :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ s : ℂ, s.re = -1 → ‖d04ZetaStripNormalized s‖ ≤ C) ∧
      (∀ s : ℂ, s.re = 2 → ‖d04ZetaStripNormalized s‖ ≤ C) := by
  obtain ⟨K,hK,hleft⟩ := d04Zeta_left_boundary
  let Z := zetaDirichletMajorant 2
  have hZ : 0 ≤ Z := zetaDirichletMajorant_nonneg 2
  let C : ℝ := 2^7*max K Z
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hb (s : ℂ) (hs : s.re=-1 ∨ s.re=2) :
      ‖d04ZetaStripNormalized s‖ ≤ C := by
    have hlo : -1 ≤ s.re := by rcases hs with h|h <;> linarith
    have hs1 : s≠1 := by
      intro he
      have h := congrArg Complex.re he
      rcases hs with h'|h' <;> norm_num [h'] at h
    have hz : ‖riemannZeta s‖ ≤ max K Z*(1+|s.im|)^5 := by
      rcases hs with h|h
      · exact (hleft s h).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
      · have hz0 : ‖riemannZeta s‖ ≤ Z :=
          riemannZeta_norm_le_dirichlet (by norm_num) (by rw [h])
        have hmax : 0 ≤ max K Z := hK.trans (le_max_left _ _)
        exact hz0.trans ((le_max_right _ _).trans
          (le_mul_of_one_le_right hmax (one_le_pow₀ (by linarith [abs_nonneg s.im]))))
    have hsm : ‖s-1‖ ≤ 2*(1+|s.im|) := by
      have he : s-1=((s.re-1 : ℝ):ℂ)+(s.im : ℂ)*I := by apply Complex.ext <;> simp
      rw [he]
      apply (norm_add_le _ _).trans
      simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
      rcases hs with h|h <;> rw [h] <;> norm_num <;> linarith [abs_nonneg s.im]
    have hd := d04ZetaStrip_den_norm hlo
    have him : |s.im| ≤ ‖s+3‖ := by simpa using Complex.abs_im_le_norm (s+3)
    have hP : 1+|s.im| ≤ 2*‖s+3‖ := by linarith
    have hn : 0 < ‖s+3‖^6 := by positivity
    rw [d04ZetaStripNormalized,norm_div,norm_pow,d04PoleRemovedZeta_eq hlo hs1,norm_mul,
      div_le_iff₀ hn]
    calc
      _ ≤ (2*(1+|s.im|))*(max K Z*(1+|s.im|)^5) := by gcongr
      _ = (2*max K Z)*(1+|s.im|)^6 := by ring
      _ ≤ (2*max K Z)*(2*‖s+3‖)^6 := by gcongr
      _ = C*‖s+3‖^6 := by dsimp [C]; ring
  exact ⟨C,hC,fun s hs => hb s (Or.inl hs),fun s hs => hb s (Or.inr hs)⟩

private theorem d04ZetaStripNormalized_growth :
    ∃ c < Real.pi/(2-(-1 : ℝ)), ∃ B,
      d04ZetaStripNormalized =O[comap (_root_.abs ∘ Complex.im) atTop ⊓
        𝓟 (Complex.re ⁻¹' Ioo (-1 : ℝ) 2)]
        (fun s : ℂ => Real.exp (B*Real.exp (c*|s.im|))) := by
  obtain ⟨K,hK,hZeta⟩ := riemannZeta_norm_le_exp_halfPlane_high_im (-1)
  let c : ℝ := Real.pi/6
  have hc : 0 < c := by dsimp [c]; positivity
  let B : ℝ := (1+Real.pi/2)/c
  refine ⟨c,by dsimp [c]; nlinarith [Real.pi_pos],B,?_⟩
  apply Asymptotics.IsBigO.of_bound (4*K)
  simp only [eventually_inf_principal,eventually_comap,Function.comp_def,mem_preimage,mem_Ioo]
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy s hsi hs
  have him : 1 ≤ |s.im| := by rw [hsi]; exact hy
  have hlo : -1 ≤ s.re := hs.1.le
  have hs1 : s≠1 := by intro he; norm_num [he] at him
  have hden : 1 ≤ ‖(s+3)^6‖ := by
    rw [norm_pow]
    exact one_le_pow₀ (by linarith [d04ZetaStrip_den_norm hlo])
  have hnorm : ‖d04ZetaStripNormalized s‖ ≤ ‖d04PoleRemovedZeta s‖ := by
    rw [d04ZetaStripNormalized,norm_div]
    exact div_le_self (norm_nonneg _) hden
  have hsm : ‖s-1‖ ≤ 4*(1+|s.im|) := by
    have he : s-1=((s.re-1 : ℝ):ℂ)+(s.im : ℂ)*I := by apply Complex.ext <;> simp
    rw [he]
    apply (norm_add_le _ _).trans
    simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
    have habs : |s.re-1| ≤ 2 := abs_le.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    linarith [abs_nonneg s.im]
  have hexp : (1+|s.im|)*Real.exp (Real.pi*|s.im|/2) ≤
      Real.exp (B*Real.exp (c*|s.im|)) := by
    have hP : 1+|s.im| ≤ Real.exp |s.im| := by
      simpa only [add_comm] using Real.add_one_le_exp |s.im|
    have hcP : c*|s.im| ≤ Real.exp (c*|s.im|) := by
      linarith [Real.add_one_le_exp (c*|s.im|)]
    have hlinear : |s.im| ≤ Real.exp (c*|s.im|)/c :=
      (le_div_iff₀ hc).mpr (by simpa only [mul_comm] using hcP)
    calc
      _ ≤ Real.exp |s.im| * Real.exp (Real.pi*|s.im|/2) := by gcongr
      _ = Real.exp ((1+Real.pi/2)*|s.im|) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        dsimp [B]
        have h := mul_le_mul_of_nonneg_left hlinear
          (by positivity : 0 ≤ 1+Real.pi/2)
        convert h using 1
        ring
  simp only [Real.norm_eq_abs,Real.abs_exp]
  calc
    _ ≤ ‖d04PoleRemovedZeta s‖ := hnorm
    _ = ‖s-1‖*‖riemannZeta s‖ := by rw [d04PoleRemovedZeta_eq hlo hs1,norm_mul]
    _ ≤ (4*(1+|s.im|))*(K*Real.exp (Real.pi*|s.im|/2)) := by gcongr; exact hZeta s hlo him
    _ = (4*K)*((1+|s.im|)*Real.exp (Real.pi*|s.im|/2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)

theorem d04RiemannZeta_polynomial_halfPlane_high_im :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, -1 ≤ s.re → 1 ≤ |s.im| →
      ‖riemannZeta s‖ ≤ C*(1+|s.im|)^6 := by
  obtain ⟨K,hK,hleft,hright⟩ := d04ZetaStripNormalized_boundary
  have hstrip (s : ℂ) (hs0 : -1 ≤ s.re) (hs2 : s.re ≤ 2) :
      ‖d04ZetaStripNormalized s‖ ≤ K :=
    PhragmenLindelof.vertical_strip d04ZetaStripNormalized_diffContOnCl
      d04ZetaStripNormalized_growth hleft hright hs0 hs2
  let Z := zetaDirichletMajorant 2
  have hZ : 0 ≤ Z := zetaDirichletMajorant_nonneg 2
  refine ⟨max (K*5^6) Z,by positivity,?_⟩
  intro s hs0 him
  by_cases hs2 : s.re ≤ 2
  · have hs1 : s≠1 := by intro he; norm_num [he] at him
    have h := hstrip s hs0 hs2
    have hden : 0 < ‖s+3‖^6 := by
      have hd := d04ZetaStrip_den_norm hs0
      positivity
    rw [d04ZetaStripNormalized,norm_div,norm_pow,div_le_iff₀ hden,
      d04PoleRemovedZeta_eq hs0 hs1,norm_mul] at h
    have hsn : 1 ≤ ‖s-1‖ := him.trans (by simpa using Complex.abs_im_le_norm (s-1))
    have hζ : ‖riemannZeta s‖ ≤ K*‖s+3‖^6 :=
      (le_mul_of_one_le_left (norm_nonneg _) hsn).trans h
    have hsp : ‖s+3‖ ≤ 5*(1+|s.im|) := by
      have he : s+3=((s.re+3 : ℝ):ℂ)+(s.im : ℂ)*I := by apply Complex.ext <;> simp
      rw [he]
      apply (norm_add_le _ _).trans
      simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,mul_one]
      rw [abs_of_nonneg (by linarith : 0 ≤ s.re+3)]
      linarith [abs_nonneg s.im]
    calc
      _ ≤ K*‖s+3‖^6 := hζ
      _ ≤ K*(5*(1+|s.im|))^6 := by gcongr
      _ = (K*5^6)*(1+|s.im|)^6 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hζ : ‖riemannZeta s‖ ≤ Z :=
      riemannZeta_norm_le_dirichlet (by norm_num) (le_of_not_ge hs2)
    calc
      _ ≤ Z := hζ
      _ ≤ Z*(1+|s.im|)^6 := le_mul_of_one_le_right hZ
        (one_le_pow₀ (by linarith [abs_nonneg s.im]))
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

end
end SixthMoment
