import Sechstmoment.Arithmetic.Euler.Shifted.ScaledLimit
import Sechstmoment.Numerator.Polar.Mellin.ContourUniform
import Sechstmoment.Numerator.U.MainTerm.PrincipalProfileRescaling


namespace Sechstmoment
open Complex Real Source MeasureTheory Set Filter
open scoped BigOperators Topology ContDiff
open Classical
noncomputable section
set_option maxHeartbeats 0

theorem bblrSixShifts_rawMomentShifts (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) (j : Fin 4) :
    bblrSixShifts (rawMomentShifts T σ) m j = bblrSixShifts σ m j/(Real.log T:ℂ) := by
  fin_cases m <;> fin_cases j <;> simp [bblrSixShifts,rawMomentShifts,neg_div]

private theorem actualPrincipalLeftTriple_scaled (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) (u : ℂ) :
    polarMellinLeftTriple (bblrSixShifts (rawMomentShifts T σ) m) (u/(Real.log T:ℂ)) 0 =
      fun i => polarLeftArguments u 0 (bblrSixShifts σ m) i/(Real.log T:ℂ) := by
  funext i
  fin_cases i <;> simp [polarMellinLeftTriple,polarLeftArguments,bblrSixShifts_rawMomentShifts]

private theorem actualPrincipalRightTriple_scaled (T : ℝ) (σ : MomentShifts)
    (m : Fin 6) (v : ℂ) :
    polarMellinRightTriple (bblrSixShifts (rawMomentShifts T σ) m) (v/(Real.log T:ℂ)) 0 =
      fun i => polarRightArguments v 0 (bblrSixShifts σ m) i/(Real.log T:ℂ) := by
  funext i
  fin_cases i <;> simp [polarMellinRightTriple,polarRightArguments,bblrSixShifts_rawMomentShifts]

theorem polarMellinRemovedKernel_principal_scaled_identity
    (T : ℝ) (σ : MomentShifts) (m : Fin 6) (u v : ℂ)
    (hρ : ∀ ij : Fin 2 × Fin 2, purePolarRoot T σ (m,ij) ≠ 0) :
    polarMellinRemovedKernel T σ m (u/(Real.log T:ℂ)) (v/(Real.log T:ℂ)) 0 /
        (Real.log T:ℂ)^9 =
      shiftedPolarEulerRest
        (fun i => polarLeftArguments u 0 (bblrSixShifts σ m) i/(Real.log T:ℂ))
        (fun i => polarRightArguments v 0 (bblrSixShifts σ m) i/(Real.log T:ℂ))*
        ninePolarZetaFactor (Real.log T) u v 0 (bblrSixShifts σ m) := by
  rw [polarMellinRemovedKernel_zero T σ m _ _ hρ]
  unfold polarArithmeticEntangledFactor
  rw [mul_assoc,← polarNineZetaProduct_eq_entangled_mul_pure,
    actualPrincipalLeftTriple_scaled,actualPrincipalRightTriple_scaled]
  unfold ninePolarZetaFactor ninePolarArgument
  have harg (ij : Fin 3 × Fin 3) :
      1+polarLeftArguments u 0 (bblrSixShifts σ m) ij.1/(Real.log T:ℂ)+
        polarRightArguments v 0 (bblrSixShifts σ m) ij.2/(Real.log T:ℂ) =
      1+(polarLeftArguments u 0 (bblrSixShifts σ m) ij.1+
        polarRightArguments v 0 (bblrSixShifts σ m) ij.2)/(Real.log T:ℂ) := by ring
  simp_rw [harg]
  rw [Finset.prod_div_distrib]
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin]
  norm_num only [Nat.reduceMul]
  ring

def actualPrincipalPolarLimitKernel (σ : MomentShifts) (m : Fin 6)
    (f g : ℝ → ℂ) (c d : ℝ) (y : ℝ × ℝ) : ℂ :=
  (profileLaplaceTransform f ((c:ℂ)+(y.1:ℂ)*I)*
    profileLaplaceTransform g ((d:ℂ)+(y.2:ℂ)*I))*
    ((arithmeticFactor:ℂ)*ninePolarRationalFactor ((c:ℂ)+(y.1:ℂ)*I)
      ((d:ℂ)+(y.2:ℂ)*I) 0 (bblrSixShifts σ m))

theorem actualPrincipalProfileRescaledKernel_polar_point_limit
    (σ : MomentShifts) (m : Fin 6) (f g : ℝ → ℂ) (c d : ℝ) (y : ℝ × ℝ)
    (hρ : ∀ ij : Fin 2 × Fin 2, normalizedPurePolarRoot σ (m,ij) ≠ 0)
    (hsep : ∀ ij : Fin 3 × Fin 3,
      ninePolarArgument ((c:ℂ)+(y.1:ℂ)*I) ((d:ℂ)+(y.2:ℂ)*I) 0
        (bblrSixShifts σ m) ij ≠ 0) :
    Tendsto (fun T : ℝ => actualPrincipalProfileRescaledKernel T σ m f g
      (Real.log T) c d y/(Real.log T:ℂ)^9) atTop
      (𝓝 (actualPrincipalPolarLimitKernel σ m f g c d y)) := by
  let u : ℂ := (c:ℂ)+(y.1:ℂ)*I
  let v : ℂ := (d:ℂ)+(y.2:ℂ)*I
  let ab : PolarShiftSpace :=
    (polarLeftArguments u 0 (bblrSixShifts σ m),polarRightArguments v 0 (bblrSixShifts σ m))
  have hA := (shiftedPolarEulerRest_scaled_tendsto ab).comp Real.tendsto_log_atTop
  have hZ := (ninePolarZetaFactor_tendsto u v 0 (bblrSixShifts σ m) hsep).comp
    Real.tendsto_log_atTop
  have ht := (hA.mul hZ).const_mul
    (profileLaplaceTransform f u*profileLaplaceTransform g v)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have hroot (ij : Fin 2 × Fin 2) : purePolarRoot T σ (m,ij) ≠ 0 := by
    rw [purePolarRoot_normalized]
    exact div_ne_zero (hρ ij) (Complex.ofReal_ne_zero.mpr (Real.log_pos hT).ne')
  have hleft : (scaledPolarShifts (Real.log T) ab).1 =
      fun i => polarLeftArguments u 0 (bblrSixShifts σ m) i/(Real.log T:ℂ) := by
    funext i
    exact scaledPolarShifts_fst (Real.log T) ab i
  have hright : (scaledPolarShifts (Real.log T) ab).2 =
      fun i => polarRightArguments v 0 (bblrSixShifts σ m) i/(Real.log T:ℂ) := by
    funext i
    exact scaledPolarShifts_snd (Real.log T) ab i
  simp only [Function.comp_apply]
  rw [hleft,hright]
  change (profileLaplaceTransform f u*profileLaplaceTransform g v)*
      (shiftedPolarEulerRest _ _*ninePolarZetaFactor (Real.log T) u v 0 (bblrSixShifts σ m)) =
    ((profileLaplaceTransform f u*profileLaplaceTransform g v)*
      polarMellinRemovedKernel T σ m (u/(Real.log T:ℂ)) (v/(Real.log T:ℂ)) 0)/
      (Real.log T:ℂ)^9
  rw [mul_div_assoc,polarMellinRemovedKernel_principal_scaled_identity T σ m _ _ hroot]

end
end Sechstmoment
