import SixthMoment.Denominator.Balanced.ActualGaussianConnector
import SixthMoment.Denominator.Balanced.GaussianMomentTruncation

namespace SixthMoment
open Complex Real Source MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
noncomputable section
set_option maxHeartbeats 1200000

def d02FiniteGaussianTimeSum (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (τ : ℂ)
    (s : Finset (Fin 6 → ℕ)) : ℂ :=
  ∫ t : ℝ,(Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^τ*
    ∑ q∈s,d02SixRawGaussianTerm T t ρ (rawSecondMomentShifts T σ) q

def d02FiniteGaussianHeightPiece (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (s : Finset (Fin 6 → ℕ)) : ℂ :=
  Complex.exp ((σ 0+σ 1)/2)*
    (d02FiniteGaussianTimeSum T σ ρ Φ 0 s+
      secondDualPower T (rawSecondMomentShifts T σ)*
        d02FiniteGaussianTimeSum T (d02DualSecondMomentShifts σ) ρ Φ
          (-(σ 0+σ 1)/(Real.log T:ℂ)) s)

def d02ActualSixCut (T δ : ℝ) (a : Fin 4 → ℝ) : Finset (Fin 6 → ℕ) :=
  d02SixMainDomain (fun j => ⌊T^(a j)⌋₊) (d02ActualPairCut (T^(1+δ)))

def d02GaussianFiniteDiagonalMoment (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (a : Fin 4 → ℝ) (δ : ℝ) : ℂ := by
  classical
  exact d02FiniteGaussianHeightPiece T σ ρ Φ ((d02ActualSixCut T δ a).filter d02SixIsDiagonal)

def d02GaussianFiniteOffDiagonalMoment (T : ℝ) (σ : SecondMomentShifts)
    (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ) (a : Fin 4 → ℝ) (δ : ℝ) : ℂ := by
  classical
  exact d02FiniteGaussianHeightPiece T σ ρ Φ
    ((d02ActualSixCut T δ a).filter (fun q => ¬d02SixIsDiagonal q))

theorem d02Phi_complex_contDiff {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ) :
    ContDiff ℝ ∞ (fun x => (Φ x:ℂ)) := Complex.ofRealCLM.contDiff.comp hΦ

theorem d02Phi_complex_tsupport {Φ : ℝ → ℝ} (hΦ : tsupport Φ⊆Icc (1:ℝ) 2) :
    tsupport (fun x => (Φ x:ℂ))⊆Icc (1:ℝ) 2 := by
  have he : Function.support (fun x => (Φ x:ℂ))=Function.support Φ := by
    ext x
    simp [Function.mem_support]
  simpa only [tsupport,he] using hΦ

theorem d02FiniteGaussianTimeSum_partition {T : ℝ} (hT : 0<T)
    (σ : SecondMomentShifts) (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (τ : ℂ) (s : Finset (Fin 6 → ℕ)) :
    d02FiniteGaussianTimeSum T σ ρ Φ τ s=
      d02FiniteGaussianTimeSum T σ ρ Φ τ (s.filter d02SixIsDiagonal)+
        d02FiniteGaussianTimeSum T σ ρ Φ τ (s.filter (fun q => ¬d02SixIsDiagonal q)) := by
  classical
  have hd := d02SixRawGaussianTerm_finite_time_integrable hT
    (d02Phi_complex_contDiff hΦ) (d02Phi_complex_tsupport hΦs) ρ σ τ
    (s.filter d02SixIsDiagonal)
  have ho := d02SixRawGaussianTerm_finite_time_integrable hT
    (d02Phi_complex_contDiff hΦ) (d02Phi_complex_tsupport hΦs) ρ σ τ
    (s.filter (fun q => ¬d02SixIsDiagonal q))
  change Integrable (fun t : ℝ => (Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^τ*
    ∑ q∈s.filter d02SixIsDiagonal,
      d02SixRawGaussianTerm T t ρ (rawSecondMomentShifts T σ) q) at hd
  change Integrable (fun t : ℝ => (Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^τ*
    ∑ q∈s.filter (fun q => ¬d02SixIsDiagonal q),
      d02SixRawGaussianTerm T t ρ (rawSecondMomentShifts T σ) q) at ho
  unfold d02FiniteGaussianTimeSum
  rw [←integral_add hd ho]
  apply integral_congr_ae
  filter_upwards [] with t
  rw [←mul_add,d02SixMain_diagonal_add_offDiagonal]

theorem d02FiniteGaussianHeightPiece_partition {T : ℝ} (hT : 0<T)
    (σ : SecondMomentShifts) (ρ : Fin 4 → ℝ → ℝ) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (s : Finset (Fin 6 → ℕ)) :
    d02FiniteGaussianHeightPiece T σ ρ Φ s=
      d02FiniteGaussianHeightPiece T σ ρ Φ (s.filter d02SixIsDiagonal)+
        d02FiniteGaussianHeightPiece T σ ρ Φ (s.filter (fun q => ¬d02SixIsDiagonal q)) := by
  classical
  unfold d02FiniteGaussianHeightPiece
  rw [d02FiniteGaussianTimeSum_partition hT σ ρ Φ hΦ hΦs,
    d02FiniteGaussianTimeSum_partition hT (d02DualSecondMomentShifts σ) ρ Φ hΦ hΦs]
  ring

theorem d02BalancedGaussianFiniteMoment_eq_height_piece {T : ℝ} (hT : 1<T)
    (σ : SecondMomentShifts) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2) (δ : ℝ) :
    d02BalancedGaussianFiniteMoment T σ ρ Φ δ=
      d02FiniteGaussianHeightPiece T σ ρ Φ (d02ActualSixCut T δ a) := by
  have hTp : 0<T := zero_lt_one.trans hT
  let s := d02ActualSixCut T δ a
  let theta : ℂ := -(σ 0+σ 1)/(Real.log T:ℂ)
  have hd := d02SixRawGaussianTerm_finite_time_integrable hTp
    (d02Phi_complex_contDiff hΦ) (d02Phi_complex_tsupport hΦs) ρ σ 0 s
  have hu := (d02SixRawGaussianTerm_finite_time_integrable hTp
    (d02Phi_complex_contDiff hΦ) (d02Phi_complex_tsupport hΦs) ρ
    (d02DualSecondMomentShifts σ) theta s).const_mul
      (secondDualPower T (rawSecondMomentShifts T σ))
  change Integrable (fun t : ℝ => (Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^(0:ℂ)*
    ∑ q∈s,d02SixRawGaussianTerm T t ρ (rawSecondMomentShifts T σ) q) at hd
  change Integrable (fun t : ℝ => secondDualPower T (rawSecondMomentShifts T σ)*
    ((Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^theta*
      ∑ q∈s,d02SixRawGaussianTerm T t ρ
        (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) q)) at hu
  have he : (fun t : ℝ => (Φ (t/T):ℂ)*d02BalancedAmplifier T t ρ*
      d02CenteredGaussianFinitePair T t σ (T^(1+δ)))=
    fun t : ℝ => Complex.exp ((σ 0+σ 1)/2)*
      ((Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^(0:ℂ)*
        ∑ q∈s,d02SixRawGaussianTerm T t ρ (rawSecondMomentShifts T σ) q+
      secondDualPower T (rawSecondMomentShifts T σ)*
        ((Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^theta*
          ∑ q∈s,d02SixRawGaussianTerm T t ρ
            (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) q)) := by
    funext t
    by_cases hz : Φ (t/T)=0
    · simp [hz]
    have hy : t/T∈Icc (1:ℝ) 2 := hΦs (subset_tsupport Φ hz)
    have hty : 0<t/T := zero_lt_one.trans_le hy.1
    have hfac := secondDualPower_dyadic_factorization hTp hty σ
    rw [show T*(t/T)=t by field_simp [hTp.ne']] at hfac
    have hdir := d02_actual_four_profiles_gaussian_finite_identity hT t a ρ hcap
      (rawSecondMomentShifts T σ) (d02ActualPairCut (T^(1+δ)))
    have hdual := d02_actual_four_profiles_gaussian_finite_identity hT t a ρ hcap
      (rawSecondMomentShifts T (d02DualSecondMomentShifts σ))
      (d02ActualPairCut (T^(1+δ)))
    change d02BalancedAmplifier T t ρ*d02ActualGaussianFinitePair t
      (rawSecondMomentShifts T σ) (T^(1+δ))=_ at hdir
    change d02BalancedAmplifier T t ρ*d02ActualGaussianFinitePair t
      (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) (T^(1+δ))=_ at hdual
    unfold d02CenteredGaussianFinitePair
    rw [d02DualSecondMomentShifts_raw_commute,hfac,Complex.cpow_zero]
    dsimp only [theta,s,d02ActualSixCut] at hdir hdual ⊢
    calc
      _ = Complex.exp ((σ 0+σ 1)/2)*
        ((Φ (t/T):ℂ)*(d02BalancedAmplifier T t ρ*
          d02ActualGaussianFinitePair t (rawSecondMomentShifts T σ) (T^(1+δ)))+
          secondDualPower T (rawSecondMomentShifts T σ)*
            ((Φ (t/T):ℂ)*((t/T:ℝ):ℂ)^(-(σ 0+σ 1)/(Real.log T:ℂ))*
              (d02BalancedAmplifier T t ρ*d02ActualGaussianFinitePair t
                (rawSecondMomentShifts T (d02DualSecondMomentShifts σ)) (T^(1+δ))))) := by ring
      _ = _ := by rw [hdir,hdual]; ring
  unfold d02BalancedGaussianFiniteMoment
  rw [he,integral_const_mul,integral_add hd hu,integral_const_mul]
  rfl

theorem d02BalancedGaussianFiniteMoment_diagonal_add_offDiagonal {T : ℝ} (hT : 1<T)
    (σ : SecondMomentShifts) (a : Fin 4 → ℝ) (ρ : Fin 4 → ℝ → ℝ)
    (hcap : ∀ j x,a j<x → ρ j x=0) (Φ : ℝ → ℝ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2) (δ : ℝ) :
    d02BalancedGaussianFiniteMoment T σ ρ Φ δ=
      d02GaussianFiniteDiagonalMoment T σ ρ Φ a δ+
        d02GaussianFiniteOffDiagonalMoment T σ ρ Φ a δ := by
  rw [d02BalancedGaussianFiniteMoment_eq_height_piece hT σ a ρ hcap Φ hΦ hΦs δ]
  exact d02FiniteGaussianHeightPiece_partition (zero_lt_one.trans hT) σ ρ Φ hΦ hΦs _

theorem d02GaussianFiniteOffDiagonalMoment_uniform_bound {R δ : ℝ}
    (hR : 0≤R) (a : Fin 4 → ℝ) (hδ : δ<1-∑ j,a j)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2) :
    ∃ C : ℝ,0≤C ∧ ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,
      (∀ j,‖σ j‖≤R) →
      ‖d02GaussianFiniteOffDiagonalMoment T σ ρ Φ a δ‖≤C*T^(-2:ℝ) := by
  have hρK : ∀ j,HasCompactSupport (ρ j) := fun j =>
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (hρs j)
  obtain ⟨D,hD,hDb⟩ := d02_four_profile_gaussian_finite_offDiagonal_uniform_power_bound
    (d02Phi_complex_contDiff hΦ) (d02Phi_complex_tsupport hΦs) ρ hρ hρK a
    hδ hR (by positivity : 0≤2*R) 2
  have hbox : 0≤secondDualBoxConstant R := by unfold secondDualBoxConstant; positivity
  refine ⟨Real.exp R*(D+secondDualBoxConstant R*D),by positivity,?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ),Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (1:ℝ)),secondDualPower_base_uniform_normalized_norm_le hR] with T hT hL hp
  intro σ hσ
  have hTp : 0<T := zero_lt_one.trans_le hT
  have hcut : ∀ p∈d02ActualPairCut (T^(1+δ)),d02PositivePairProduct p≤T^(1+δ) :=
    fun p h => (d02ActualPairCut_mem_iff (Real.rpow_pos_of_pos hTp _) p).mp h
  have hd := hDb T hT hL (d02ActualPairCut (T^(1+δ))) σ 0 hcut hσ
    (by simpa only [norm_zero] using (show 0≤2*R by positivity))
  have hu := hDb T hT hL (d02ActualPairCut (T^(1+δ)))
    (d02DualSecondMomentShifts σ) (-(σ 0+σ 1)/(Real.log T:ℂ)) hcut
    (d02DualSecondMomentShifts_norm_le hσ)
    (secondDualTimeExponent_normalized_box_norm_le hL σ hσ)
  unfold d02GaussianFiniteOffDiagonalMoment d02FiniteGaussianHeightPiece
  change ‖Complex.exp ((σ 0+σ 1)/2)*
    (d02FiniteGaussianTimeSum T σ ρ Φ 0 _+
      secondDualPower T (rawSecondMomentShifts T σ)*
        d02FiniteGaussianTimeSum T (d02DualSecondMomentShifts σ) ρ Φ
          (-(σ 0+σ 1)/(Real.log T:ℂ)) _)‖≤_
  rw [norm_mul]
  calc
    _ ≤ Real.exp R*(D*T^(-2:ℝ)+secondDualBoxConstant R*(D*T^(-2:ℝ))) := by
      apply mul_le_mul (d02ZetaCentering_norm_le σ hσ) _ (norm_nonneg _) (by positivity)
      apply (norm_add_le _ _).trans
      apply add_le_add hd
      rw [norm_mul]
      exact mul_le_mul (hp σ hσ) hu (norm_nonneg _) hbox
    _ = _ := by ring

theorem d02GaussianFiniteOffDiagonalMoment_normalized_uniform_small {R δ : ℝ}
    (hR : 0≤R) (a : Fin 4 → ℝ) (hδ : δ<1-∑ j,a j)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    {η : ℝ} (hη : 0<η) :
    ∀ᶠ T : ℝ in atTop,∀ σ : SecondMomentShifts,(∀ j,‖σ j‖≤R) →
      ‖d02GaussianFiniteOffDiagonalMoment T σ ρ Φ a δ/(T*(Real.log T)^9:ℂ)‖<η := by
  obtain ⟨C,_hC,hb⟩ := d02GaussianFiniteOffDiagonalMoment_uniform_bound
    hR a hδ ρ hρ hρs Φ hΦ hΦs
  exact d02PowerHeight_normalized_uniform_small
    (fun T σ => d02GaussianFiniteOffDiagonalMoment T σ ρ Φ a δ)
    (fun σ => ∀ j,‖σ j‖≤R) (by norm_num : (-2:ℝ)<1) hb hη

theorem d02GaussianFiniteOffDiagonalMoment_normalized_tendsto {R δ : ℝ}
    (hR : 0≤R) (a : Fin 4 → ℝ) (hδ : δ<1-∑ j,a j)
    (ρ : Fin 4 → ℝ → ℝ) (hρ : ∀ j,Continuous (ρ j))
    (hρs : ∀ j,tsupport (ρ j)⊆Icc 0 (a j))
    (Φ : ℝ → ℝ) (hΦ : ContDiff ℝ ∞ Φ) (hΦs : tsupport Φ⊆Icc 1 2)
    (σ : SecondMomentShifts) (hσ : ∀ j,‖σ j‖≤R) :
    Tendsto (fun T : ℝ => d02GaussianFiniteOffDiagonalMoment T σ ρ Φ a δ/
      (T*(Real.log T)^9:ℂ)) atTop (𝓝 0) := by
  obtain ⟨C,_hC,hb⟩ := d02GaussianFiniteOffDiagonalMoment_uniform_bound
    hR a hδ ρ hρ hρs Φ hΦ hΦs
  exact d02PowerHeight_normalized_tendsto _ (by norm_num : (-2:ℝ)<1)
    (hb.mono (fun T hT => hT σ hσ))

end
end SixthMoment
