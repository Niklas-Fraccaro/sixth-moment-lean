import SixthMoment.Zeta.Bounds.MellinZetaHalfPlaneGrowth

namespace SixthMoment
open Complex Real MeasureTheory Set
open scoped Topology
noncomputable section

theorem gamma_inv_reflection_left {s : ℂ} (hs1 : s.re<1)
    (hΓ : Complex.Gamma s≠0) :
    (Complex.Gamma s)⁻¹=Complex.Gamma (1-s)*Complex.sin ((Real.pi:ℂ)*s)/Real.pi := by
  have hΓ' : Complex.Gamma (1-s)≠0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp only [sub_re,one_re]; linarith)
  have hSin : Complex.sin ((Real.pi:ℂ)*s)≠0 := by
    intro h
    have he := Complex.Gamma_mul_Gamma_one_sub s
    rw [h,div_zero] at he
    exact mul_ne_zero hΓ hΓ' he
  apply mul_left_cancel₀ hΓ
  rw [mul_inv_cancel₀ hΓ,←mul_div_assoc,←mul_assoc,Complex.Gamma_mul_Gamma_one_sub]
  field_simp

theorem gamma_ne_zero_of_im_ne_zero {s : ℂ} (hs : s.im≠0) : Complex.Gamma s≠0 := by
  apply Complex.Gamma_ne_zero
  intro n hn
  have hi := congrArg Complex.im hn
  simp only [neg_im,natCast_im] at hi
  exact hs (by simpa using hi)

theorem riemannZeta_norm_le_exp_strip_high_im {a b : ℝ} (hb : b<2) :
    ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,a≤s.re → s.re≤b → 1≤|s.im| →
      ‖riemannZeta s‖≤C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨K,hK0,hK⟩ := completedRiemannZeta₀_norm_bounded_on_strip a b
  obtain ⟨J,hJ0,hJ⟩ := realGamma_norm_bounded_on_positive_interval
    (a := 1-b/2) (b := 1-a/2) (by linarith)
  let C := (K+2)*(Real.pi^(b/2))*J/Real.pi
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro s hsa hsb hi
  have him : s.im≠0 := by intro he; norm_num [he] at hi
  have hs0 : s≠0 := by intro he; norm_num [he] at him
  have hsn : 1≤‖s‖ := hi.trans (Complex.abs_im_le_norm s)
  have htn : 1≤‖1-s‖ := by
    have hh := Complex.abs_im_le_norm (1-s)
    simp only [sub_im,one_im,zero_sub,abs_neg] at hh
    exact hi.trans hh
  have h1 : ‖1/s‖≤1 := by
    rw [norm_div,norm_one]
    exact (one_div_le_one_div_of_le zero_lt_one hsn).trans_eq (by norm_num)
  have h2 : ‖1/(1-s)‖≤1 := by
    rw [norm_div,norm_one]
    exact (one_div_le_one_div_of_le zero_lt_one htn).trans_eq (by norm_num)
  have hN : ‖completedRiemannZeta₀ s-1/s-1/(1-s)‖≤K+2 := by
    have hn := (norm_sub_le _ _).trans
      (add_le_add ((norm_sub_le _ _).trans (add_le_add (hK s hsa hsb) h1)) h2)
    linarith
  have hΓ : ‖(Complex.Gamma (s/2))⁻¹‖≤J*Real.exp (Real.pi*|s.im|/2)/Real.pi := by
    have hsre : (s/2).re<1 := by simp only [div_ofNat_re]; linarith
    have hsΓ : Complex.Gamma (s/2)≠0 := gamma_ne_zero_of_im_ne_zero
      (by simp only [div_ofNat_im]; exact div_ne_zero him (by norm_num))
    rw [gamma_inv_reflection_left hsre hsΓ,norm_div,norm_mul,
      Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
    have hj := hJ (1-(s/2).re)
      (by simp only [div_ofNat_re]; constructor <;> linarith)
    have hg := gamma_norm_le_realGamma_re (s := 1-s/2)
      (by simp only [sub_re,one_re]; linarith)
    have hc := complex_sin_norm_le_exp_abs_im ((Real.pi:ℂ)*(s/2))
    have hi' : |(((Real.pi:ℂ)*(s/2)).im)|=Real.pi*|s.im|/2 := by
      simp only [mul_im,ofReal_re,ofReal_im,zero_mul,add_zero,div_ofNat_im,
        abs_mul,abs_div,abs_of_pos Real.pi_pos]
      norm_num
      ring
    rw [hi'] at hc
    apply div_le_div_of_nonneg_right _ Real.pi_pos.le
    exact mul_le_mul (hg.trans (by simpa only [sub_re,one_re] using hj)) hc
      (norm_nonneg _) hJ0
  have hPi : ‖((Real.pi:ℂ)^(-s/2))⁻¹‖≤Real.pi^(b/2) := by
    rw [←Complex.cpow_neg,show -(-s/2)=s/2 by ring,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,div_ofNat_re]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.two_le_pi]) (by linarith)
  rw [riemannZeta_eq_completedRiemannZeta₀ hs0,div_eq_mul_inv,mul_inv_rev,norm_mul,norm_mul]
  calc
    _≤(K+2)*(J*Real.exp (Real.pi*|s.im|/2)/Real.pi*Real.pi^(b/2)) := by gcongr
    _=C*Real.exp (Real.pi*|s.im|/2) := by dsimp [C]; ring

theorem riemannZeta_norm_le_exp_halfPlane_high_im (a : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ s : ℂ,a≤s.re → 1≤|s.im| →
      ‖riemannZeta s‖≤C*Real.exp (Real.pi*|s.im|/2) := by
  obtain ⟨K,hK0,hK⟩ := riemannZeta_norm_le_exp_strip_high_im (a := a) (b := 3/2) (by norm_num)
  let Z := zetaDirichletMajorant (3/2)
  have hZ : 0≤Z := zetaDirichletMajorant_nonneg _
  refine ⟨max K Z,hK0.trans (le_max_left _ _),?_⟩
  intro s hs hi
  by_cases hb : s.re≤3/2
  · exact (hK s hs hb hi).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  · have he : 1≤Real.exp (Real.pi*|s.im|/2) := Real.one_le_exp (by positivity)
    calc
      _≤Z := riemannZeta_norm_le_dirichlet (by norm_num : (1:ℝ)<3/2) (le_of_not_ge hb)
      _≤Z*Real.exp (Real.pi*|s.im|/2) := by nlinarith
      _≤_ := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
end
end SixthMoment
