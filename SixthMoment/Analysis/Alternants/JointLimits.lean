import Mathlib.Analysis.Asymptotics.Lemmas
import SixthMoment.Analysis.Alternants.Limits


namespace SixthMoment
open Filter
open scoped Topology

set_option maxHeartbeats 0

theorem strictDeriv_tendsto_twoPointSlope {f : ℂ → ℂ} {d a : ℂ}
    (hd : HasStrictDerivAt f d a) :
    Tendsto (fun p : ℂ × ℂ => slope f p.1 p.2)
      (𝓝[{p : ℂ × ℂ | p.2 ≠ p.1}] (a,a)) (𝓝 d) := by
  have ho := (hasDerivAtFilter_iff_isLittleO.mp hd).tendsto_div_nhds_zero
  have ht := (ho.mono_left (nhdsWithin_le_nhds (s :=
    {p : ℂ × ℂ | p.2 ≠ p.1}))).add_const d
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  rw [slope_def_field]
  simp only [smul_eq_mul]
  field_simp
  ring

theorem expFirstSlope_tendsto_twoPointSlope (q : ℂ) :
    Tendsto (fun p : ℂ × ℂ => slope (expFirstSlope q) p.1 p.2)
      (𝓝[{p : ℂ × ℂ | p.2 ≠ p.1}] (0,0)) (𝓝 (q^2/2)) := by
  have hp := (expScaled_powerSeries q).has_fpower_series_dslope_fslope
  have hd := hp.analyticAt.hasStrictDerivAt
  have hv : deriv (expFirstSlope q) 0 = q^2/2 := by
    simpa only [expSecondSlope, dslope_same] using expSecondSlope_zero q
  exact strictDeriv_tendsto_twoPointSlope (hd.congr_deriv hv)

theorem determinant_row_three_add_mul {R : Type*} [CommRing R]
    (a b c d : Fin 4 → R) (t s : R) :
    (Matrix.of ![a,b,c, (fun j => a j+t*b j+s*d j)]).det =
      s * (Matrix.of ![a,b,c,d]).det := by
  rw [determinant_four_six_minors, determinant_four_six_minors]
  norm_num [matrixMinorTwo, Matrix.of_apply]
  ring

noncomputable def jointSlopeExpMatrix (q : Fin 4 → ℂ) (e z w : ℂ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  ![(fun _ => 1), (fun j => expFirstSlope (q j) e),
    (fun j => Complex.exp (z*q j)),
    (fun j => slope (expFirstSlope (q j)) e w)]

theorem exponentialAlternant_joint_regular (q : Fin 4 → ℂ) (e z w : ℂ)
    (he : e ≠ 0) (hw : w ≠ 0) (hwe : w ≠ e) :
    exponentialAlternant (![0,e,z,w]) q =
      Complex.exp e * (jointSlopeExpMatrix q e z w).det /
        (z*(z-e)*(w-z)) := by
  rw [exponentialAlternant_first_regular q e z w he]
  have hexp (j : Fin 4) : Complex.exp (w*q j) =
      1+w*expFirstSlope (q j) e+
        (w*(w-e))*slope (expFirstSlope (q j)) e w := by
    rw [slope_def_field, expFirstSlope_of_ne _ _ hw]
    field_simp
    ring
  have hmat : firstSlopeExpMatrix q e z w =
      Matrix.of ![(fun _ => 1), (fun j => expFirstSlope (q j) e),
        (fun j => Complex.exp (z*q j)),
        (fun j => 1+w*expFirstSlope (q j) e+
          (w*(w-e))*slope (expFirstSlope (q j)) e w)] := by
    ext i j
    fin_cases i <;> simp [firstSlopeExpMatrix, hexp]
  rw [hmat, determinant_row_three_add_mul]
  change _ = Complex.exp e * (Matrix.of _).det / _
  rw [show z*w*(z-e)*(w-e)*(w-z) =
    (w*(w-e))*(z*(z-e)*(w-z)) by ring]
  rw [show Complex.exp e * ((w*(w-e))*(Matrix.of _).det) =
    (w*(w-e))*(Complex.exp e*(Matrix.of _).det) by ring]
  exact mul_div_mul_left _ _ (mul_ne_zero hw (sub_ne_zero.mpr hwe))

theorem jointSlopeExpMatrix_tendsto (q : Fin 4 → ℂ) (z : ℂ) :
    Tendsto (fun p : ℂ × ℂ => jointSlopeExpMatrix q p.1 z p.2)
      (𝓝[{p : ℂ × ℂ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1}] (0,0))
      (𝓝 (secondSlopeExpMatrix q z 0)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  fin_cases i
  all_goals simp only [jointSlopeExpMatrix, secondSlopeExpMatrix,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Fin.reduceFinMk]
  · exact tendsto_const_nhds
  · have hf : Tendsto (fun p : ℂ × ℂ => p.1)
        (𝓝[{p : ℂ × ℂ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1}] (0,0)) (𝓝 0) :=
        continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have ht := ((expFirstSlope_continuous (q j)).tendsto 0).comp hf
    simpa only [expFirstSlope_zero, Function.comp_def] using ht
  · exact tendsto_const_nhds
  · simpa only [expSecondSlope_zero] using
      (expFirstSlope_tendsto_twoPointSlope (q j)).mono_left
        (nhdsWithin_mono _ (fun _ hp => hp.2.2))

theorem exponentialAlternant_joint_zero_limit (q : Fin 4 → ℂ) (z : ℂ)
    (hz : z ≠ 0) :
    Tendsto (fun p : ℂ × ℂ => exponentialAlternant (![0,p.1,z,p.2]) q)
      (𝓝[{p : ℂ × ℂ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1}] (0,0))
      (𝓝 (confluentExpGenerator q z)) := by
  let L := 𝓝[{p : ℂ × ℂ | p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ p.2 ≠ p.1}] (0,0)
  have hfst : Tendsto (fun p : ℂ × ℂ => p.1) L (𝓝 0) :=
    continuous_fst.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hsnd : Tendsto (fun p : ℂ × ℂ => p.2) L (𝓝 0) :=
    continuous_snd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hmat := jointSlopeExpMatrix_tendsto q z
  have hdet : Tendsto (fun p : ℂ × ℂ => (jointSlopeExpMatrix q p.1 z p.2).det)
      L (𝓝 (secondSlopeExpMatrix q z 0).det) :=
    (continuous_id.matrix_det : Continuous
      (fun M : Matrix (Fin 4) (Fin 4) ℂ => M.det)).continuousAt.tendsto.comp hmat
  have hexp : Tendsto (fun p : ℂ × ℂ => Complex.exp p.1) L (𝓝 1) := by
    simpa only [Complex.exp_zero, Function.comp_def] using
      (Complex.continuous_exp.tendsto 0).comp hfst
  have hden : Tendsto (fun p : ℂ × ℂ => z*(z-p.1)*(p.2-z))
      L (𝓝 (z*(z-0)*(0-z))) :=
    (tendsto_const_nhds.mul (tendsto_const_nhds.sub hfst)).mul
      (hsnd.sub tendsto_const_nhds)
  have hd : z*(z-0)*(0-z) ≠ 0 := by
    simpa only [sub_zero, zero_sub] using mul_ne_zero (mul_ne_zero hz hz) (neg_ne_zero.mpr hz)
  have ht := (hexp.mul hdet).div hden hd
  simp only [one_mul] at ht
  have hv : (secondSlopeExpMatrix q z 0).det / (z*(z-0)*(0-z)) =
      confluentExpGenerator q z := by
    rw [secondSlopeExpMatrix_det_zero, confluentExpGenerator]
    field_simp
    ring
  rw [hv] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with p hp
  exact (exponentialAlternant_joint_regular q p.1 z p.2 hp.1 hp.2.1 hp.2.2).symm

end SixthMoment
