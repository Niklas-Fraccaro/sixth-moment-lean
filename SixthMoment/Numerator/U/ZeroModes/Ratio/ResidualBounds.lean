import SixthMoment.Numerator.U.ZeroModes.Ratio.PhysicalPowers


namespace SixthMoment.Source
open Complex Real MeasureTheory Set Filter
open scoped BigOperators Topology
open Classical
noncomputable section
set_option maxHeartbeats 0

def a03ZeroModeRatioGaussianMass : ℝ :=
  ∫ y : ℝ,(1+|y|)^4*Real.exp (Real.pi*|y|-y^2)

theorem a03ZeroModeRatioGaussianMass_nonneg : 0≤a03ZeroModeRatioGaussianMass :=
  integral_nonneg (fun _ => by positivity)

theorem a03ZeroModeRatioGaussianConstant_sideSwap (α : MomentShifts) (R : ℝ) :
    a03ZeroModeRatioGaussianConstant (a03ZeroModeRatioSideSwap α) R=
      a03ZeroModeRatioGaussianConstant α R := by
  unfold a03ZeroModeRatioGaussianConstant
  rw [a03ZeroModeRatioRoot_sideSwap_zero,a03ZeroModeRatioRoot_sideSwap_one]
  ring

theorem a03ZeroModeRatioVerticalIntegral_gaussian_norm_bound (c : ℝ) (F : ℂ→ℂ)
    (hF : Integrable (fun y : ℝ => F ((c:ℂ)+(y:ℂ)*I)))
    {Q : ℝ} (_hQ : 0≤Q)
    (hb : ∀ y : ℝ,‖F ((c:ℂ)+(y:ℂ)*I)‖≤Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2))) :
    ‖verticalIntegral c F‖≤(1/(2*Real.pi))*Q*a03ZeroModeRatioGaussianMass := by
  have hg := SixthMoment.gaussianPolynomialExponential_integrable 4 Real.pi
  have hc : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  unfold verticalIntegral
  rw [norm_mul,hc]
  apply (mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)).trans
  calc
    _ ≤ (1/(2*Real.pi))*(∫ y : ℝ,Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact integral_mono hF.norm (hg.const_mul Q) hb
    _ = _ := by rw [integral_const_mul]; dsimp [a03ZeroModeRatioGaussianMass]; ring

theorem a03ZeroModeRatioDoubleIntegral_gaussian_norm_bound (c d : ℝ) (F : ℂ→ℂ→ℂ)
    (hF : Integrable (fun p : ℝ×ℝ => F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I))
      (volume.prod volume))
    {Q : ℝ} (_hQ : 0≤Q)
    (hb : ∀ y z : ℝ,‖F ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I)‖≤
      Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2))*((1+|z|)^4*Real.exp (Real.pi*|z|-z^2))) :
    ‖a03ZeroModeRatioDoubleIntegral c d F‖≤
      (1/(2*Real.pi))^2*Q*a03ZeroModeRatioGaussianMass^2 := by
  have hg := SixthMoment.gaussianPolynomialExponential_integrable 4 Real.pi
  have hmass : ‖∫ p : ℝ×ℝ,F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) ∂volume.prod volume‖≤
      Q*a03ZeroModeRatioGaussianMass^2 := by
    apply (norm_integral_le_integral_norm _).trans
    calc
      _ ≤ ∫ p : ℝ×ℝ,Q*((1+|p.1|)^4*Real.exp (Real.pi*|p.1|-p.1^2))*
          ((1+|p.2|)^4*Real.exp (Real.pi*|p.2|-p.2^2)) ∂volume.prod volume := by
        apply integral_mono hF.norm
          (by convert (hg.mul_prod hg).const_mul Q using 1; funext p; ring)
        intro p
        exact hb p.1 p.2
      _ = _ := by
        calc
          _ = Q*(∫ p : ℝ×ℝ,((1+|p.1|)^4*Real.exp (Real.pi*|p.1|-p.1^2))*
              ((1+|p.2|)^4*Real.exp (Real.pi*|p.2|-p.2^2)) ∂volume.prod volume) := by
            rw [←integral_const_mul]
            apply integral_congr_ae
            exact Eventually.of_forall (fun _ => by ring)
          _ = _ := by
            rw [integral_prod_mul (fun y : ℝ => (1+|y|)^4*Real.exp (Real.pi*|y|-y^2))
              (fun z : ℝ => (1+|z|)^4*Real.exp (Real.pi*|z|-z^2))]
            dsimp [a03ZeroModeRatioGaussianMass]
            ring
  have he : a03ZeroModeRatioDoubleIntegral c d F=
      (1/(2*Real.pi):ℂ)*(1/(2*Real.pi):ℂ)*
        (∫ p : ℝ×ℝ,F ((c:ℂ)+(p.1:ℂ)*I) ((d:ℂ)+(p.2:ℂ)*I) ∂volume.prod volume) := by
    unfold a03ZeroModeRatioDoubleIntegral verticalIntegral
    rw [integral_const_mul,integral_prod _ hF]
    ring
  have hc : ‖(1/(2*Real.pi):ℂ)‖=1/(2*Real.pi) := by
    simp [Complex.norm_real,abs_of_pos Real.pi_pos]
  rw [he,norm_mul,norm_mul,hc]
  exact (mul_le_mul_of_nonneg_left hmass (by positivity)).trans_eq (by ring)

theorem a03ZeroModeRatioWeightedKernel_boundary_uniform_majorant
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ) :
    ∃ C : ℝ,0≤C ∧ ∀ L M : ℝ,∀ α : MomentShifts,
      (∀ j : Fin 4,‖α j‖≤ε/8) → (∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ s : ℂ,1+ε≤s.re → ∀ c d : ℝ,
      a03ZeroModeRatioPrimaryLine ε≤c → a03ZeroModeRatioPrimaryLine ε≤d →
      |c|≤1 → |d|≤1 → ε≤|c| → ε≤|d| → ∀ y z : ℝ,
      ‖a03ZeroModeRatioWeightedKernel L M α a b ((c:ℂ)+(y:ℂ)*I) ((d:ℂ)+(z:ℂ)*I) s‖≤
        C*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*Real.exp (L*c+M*d)*
          ((1+|y|)^4*Real.exp (Real.pi*|y|-y^2))*((1+|z|)^4*Real.exp (Real.pi*|z|-z^2)) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioArithmeticKernel_gaussian_majorant hε hδ
  refine ⟨D*ε⁻¹*ε⁻¹,by positivity,?_⟩
  intro L M α hα hρ a b ha hb s hs c d hc hd hcabs hdabs hcsep hdsep y z
  let u : ℂ := (c:ℂ)+(y:ℂ)*I
  let v : ℂ := (d:ℂ)+(z:ℂ)*I
  have hreg := a03ZeroModeRatio_primary_rectangle_region hε
    (by linarith) (u := u) (v := v) (by simpa [u] using hc) (by simpa [v] using hd)
  have hiu : ‖u‖⁻¹≤ε⁻¹ := inv_anti₀ hε
    (hcsep.trans (by simpa [u] using Complex.abs_re_le_norm u))
  have hiv : ‖v‖⁻¹≤ε⁻¹ := inv_anti₀ hε
    (hdsep.trans (by simpa [v] using Complex.abs_re_le_norm v))
  have hm := hbnd α hα hρ a b ha hb u v s hs (by simpa [u] using hcabs)
    (by simpa [v] using hdabs) hreg
    (a03ZeroModeRatioDifferenceArgument_line_separation hε hα hcsep y 0)
    (a03ZeroModeRatioDifferenceArgument_line_separation hε hα hdsep z 1)
  have hi := mul_le_mul hiu hiv (inv_nonneg.mpr (norm_nonneg _)) (inv_nonneg.mpr hε.le)
  have hmi : ‖a03ZeroModeRatioArithmeticKernel α a b u v s‖≤
      D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*ε⁻¹*
        (1+|u.im|)^4*(1+|v.im|)^4*Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2) := by
    apply hm.trans
    convert mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hi
      (show 0≤D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ by positivity))
      (show 0≤(1+|u.im|)^4*(1+|v.im|)^4*
        Real.exp (Real.pi*(|u.im|+|v.im|)-u.im^2-v.im^2) by positivity) using 1 <;> ring
  unfold a03ZeroModeRatioWeightedKernel
  rw [norm_mul,a03ZeroModeRatioExponential_norm]
  apply (mul_le_mul_of_nonneg_left hmi (Real.exp_pos _).le).trans_eq
  simp only [u,v,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,sub_zero,add_zero,
    add_im,mul_im,mul_one,zero_add]
  rw [show Real.pi*(|y|+|z|)-y^2-z^2=(Real.pi*|y|-y^2)+(Real.pi*|z|-z^2) by ring,
    Real.exp_add (Real.pi*|y|-y^2) (Real.pi*|z|-z^2)]
  ring

theorem a03ZeroModeRatioWeightedKernel_double_residual_norm_bound
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ) :
    ∃ C : ℝ,0≤C ∧ ∀ L M : ℝ,∀ α : MomentShifts,
      (∀ j : Fin 4,‖α j‖≤ε/8) → (∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ s : ℂ,1+ε≤s.re →
      ‖a03ZeroModeRatioDoubleIntegral (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
        (fun u v => a03ZeroModeRatioWeightedKernel L M α a b u v s)‖≤
      C*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*
        Real.exp ((L+M)*a03ZeroModeRatioPrimaryLine ε) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioWeightedKernel_boundary_uniform_majorant hε hε1 hδ
  refine ⟨(1/(2*Real.pi))^2*D*a03ZeroModeRatioGaussianMass^2,by positivity,?_⟩
  intro L M α hα hρ a b ha hb s hs
  have hpabs := (a03ZeroModeRatioLine_abs_bounds hε hε1 1).2
  have hpsep := (a03ZeroModeRatioLine_abs_bounds hε hε1 1).1
  have hF := a03ZeroModeRatioWeightedKernel_joint_integrable_primary L M hε hε1 hδ α hα hρ
    ha hb hs le_rfl le_rfl hpabs hpabs hpsep hpsep
  have h := a03ZeroModeRatioDoubleIntegral_gaussian_norm_bound
    (a03ZeroModeRatioPrimaryLine ε) (a03ZeroModeRatioPrimaryLine ε)
    (fun u v => a03ZeroModeRatioWeightedKernel L M α a b u v s) hF
    (show 0≤D*(a03ZeroModeRatioGaussianConstant α 1)^2*(a:ℝ)^δ*(b:ℝ)^δ*
      Real.exp (L*a03ZeroModeRatioPrimaryLine ε+M*a03ZeroModeRatioPrimaryLine ε) by positivity)
    (hbnd L M α hα hρ a b ha hb s hs _ _ le_rfl le_rfl hpabs hpabs hpsep hpsep)
  apply h.trans_eq
  rw [show L*a03ZeroModeRatioPrimaryLine ε+M*a03ZeroModeRatioPrimaryLine ε=
    (L+M)*a03ZeroModeRatioPrimaryLine ε by ring]
  ring

theorem a03ZeroModeRatioWeightedLeftResidue_norm_bound
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ) :
    ∃ C : ℝ,0≤C ∧ ∀ L M : ℝ,∀ α : MomentShifts,
      (∀ j : Fin 4,‖α j‖≤ε/8) → (∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ s : ℂ,1+ε≤s.re →
      ‖verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedLeftResidue L M α a b s)‖≤
        C*‖riemannZeta (1+α 0-α 1)‖*a03ZeroModeRatioGaussianConstant α 1*
          (a:ℝ)^δ*(b:ℝ)^δ*Real.exp (M*a03ZeroModeRatioSecondaryLine ε) := by
  obtain ⟨D,hD,hbnd⟩ := a03ZeroModeRatioLeftResidueKernel_uniform_gaussian_majorant hε hε1 hδ
  have hmass := a03ZeroModeRatioGaussianMass_nonneg
  refine ⟨(1/(2*Real.pi))*D*ε⁻¹*a03ZeroModeRatioGaussianMass,by positivity,?_⟩
  intro L M α hα hρ a b ha hb s hs
  have hB := a03ZeroModeRatioGaussianConstant_nonneg α 1
  let q : ℝ := a03ZeroModeRatioSecondaryLine ε
  have hqabs : |q|≤1 := by
    simpa [q,a03ZeroModeRatioLine] using (a03ZeroModeRatioLine_abs_bounds hε hε1 2).2
  have hqsep : ε≤|q| := by
    simpa [q,a03ZeroModeRatioLine] using (a03ZeroModeRatioLine_abs_bounds hε hε1 2).1
  have hF := a03ZeroModeRatioWeightedLeftResidue_line_integrable L M hε hε1 hδ α hα hρ
    ha hb hs (c := q) le_rfl hqabs hqsep
  let Q : ℝ := D*‖riemannZeta (1+α 0-α 1)‖*a03ZeroModeRatioGaussianConstant α 1*
    (a:ℝ)^δ*(b:ℝ)^δ*ε⁻¹*Real.exp (M*q)
  have hQ : 0≤Q := by dsimp [Q]; positivity
  have hpoint (y : ℝ) : ‖a03ZeroModeRatioWeightedLeftResidue L M α a b s ((q:ℂ)+(y:ℂ)*I)‖≤
      Q*((1+|y|)^4*Real.exp (Real.pi*|y|-y^2)) := by
    have hi : ‖(q:ℂ)+(y:ℂ)*I‖⁻¹≤ε⁻¹ := inv_anti₀ hε
      (hqsep.trans (by simpa using Complex.abs_re_le_norm ((q:ℂ)+(y:ℂ)*I)))
    have hm := hbnd α hα hρ a b ha hb ((q:ℂ)+(y:ℂ)*I) s hs
      (by simpa using hqabs) (by simp [q])
      (a03ZeroModeRatioDifferenceArgument_line_separation hε hα
        hqsep y 1)
    unfold a03ZeroModeRatioWeightedLeftResidue
    rw [norm_mul,Complex.norm_exp]
    have hre : ((M:ℂ)*((q:ℂ)+(y:ℂ)*I)).re=M*q := by simp
    rw [hre]
    apply (mul_le_mul_of_nonneg_left hm (Real.exp_pos _).le).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_re,I_im,mul_zero,mul_one,zero_add,add_zero]
    dsimp [Q]
    convert mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hi (show 0≤Real.exp (M*q)*D*‖riemannZeta (1+α 0-α 1)‖*
        a03ZeroModeRatioGaussianConstant α 1*(a:ℝ)^δ*(b:ℝ)^δ by positivity))
      (show 0≤(1+|y|)^4*Real.exp (Real.pi*|y|-y^2) by positivity) using 1 <;> ring
  exact (a03ZeroModeRatioVerticalIntegral_gaussian_norm_bound q _ hF hQ hpoint).trans_eq
    (by dsimp [Q,q]; ring)

theorem a03ZeroModeRatioWeightedRightResidue_norm_bound
    {ε δ : ℝ} (hε : 0<ε) (hε1 : ε<1/8) (hδ : 0<δ) :
    ∃ C : ℝ,0≤C ∧ ∀ L M : ℝ,∀ α : MomentShifts,
      (∀ j : Fin 4,‖α j‖≤ε/8) → (∀ j : Fin 2,a03ZeroModeRatioRoot α j≠0) →
      ∀ a b : ℕ,a≠0 → b≠0 → ∀ s : ℂ,1+ε≤s.re →
      ‖verticalIntegral (a03ZeroModeRatioSecondaryLine ε) (a03ZeroModeRatioWeightedRightResidue L M α a b s)‖≤
        C*‖riemannZeta (1+α 2-α 3)‖*a03ZeroModeRatioGaussianConstant α 1*
          (a:ℝ)^δ*(b:ℝ)^δ*Real.exp (L*a03ZeroModeRatioSecondaryLine ε) := by
  obtain ⟨C,hC,hbnd⟩ := a03ZeroModeRatioWeightedLeftResidue_norm_bound hε hε1 hδ
  refine ⟨C,hC,?_⟩
  intro L M α hα hρ a b ha hb s hs
  have he : a03ZeroModeRatioWeightedLeftResidue M L (a03ZeroModeRatioSideSwap α) b a s=
      a03ZeroModeRatioWeightedRightResidue L M α a b s := by
    funext u
    exact a03ZeroModeRatioWeightedLeftResidue_sideSwap L M α a b s u
  have h := hbnd M L (a03ZeroModeRatioSideSwap α) (a03ZeroModeRatioSideSwap_small hα)
    (a03ZeroModeRatioSideSwap_roots_nonzero hρ) b a hb ha s hs
  rw [he,a03ZeroModeRatioGaussianConstant_sideSwap] at h
  have hz : 1+a03ZeroModeRatioSideSwap α 0-a03ZeroModeRatioSideSwap α 1=1+α 2-α 3 := rfl
  rw [hz] at h
  exact h.trans_eq (by ring)

end
end SixthMoment.Source
