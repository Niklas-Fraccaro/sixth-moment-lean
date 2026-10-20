import Sechstmoment.Numerator.V.Arithmetic.Additive.ChiOriginal
import Sechstmoment.Numerator.V.Asymptotic.ProfileOriginalCoefficients
import Sechstmoment.Numerator.V.Contour.PolynomialAdditiveReduction


namespace Sechstmoment.Source.NoDPGlobalLFactorization
open NoDPHarmonic Real Complex Polynomial
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem sum_range_add_one_Icc (M : ℕ) (F : ℕ → ℂ) :
    (∑ a ∈ Finset.range M, F (a+1)) = ∑ a ∈ Finset.Icc 1 M, F a := by
  induction M with
  | zero => simp
  | succ M ih => rw [Finset.sum_range_succ,Finset.sum_Icc_succ_top (by omega),ih]

theorem profileCoefficient_eval_square (M : ℕ) (L : ℝ) (f g : ℝ → ℂ) (H : ℕ → ℂ)
    (hf : ∀ n : ℕ, M < n → f (Real.log n/L) = 0)
    (hg : ∀ n : ℕ, M < n → g (Real.log n/L) = 0) :
    (∑ N ∈ Finset.Icc 1 (M^2), profileCoefficient f g L N*H N) =
      ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M,
        f (Real.log a/L)*g (Real.log b/L)*H (a*b) := by
  classical
  let F (a b : ℕ) := f (Real.log a/L)*g (Real.log b/L)*H (a*b)
  have hpoint (N : ℕ) : profileCoefficient f g L N*H N =
      ∑ d ∈ N.divisors, F d (N/d) := by
    rw [profileCoefficient,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    dsimp only [F]
    rw [Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)]
  simp_rw [hpoint]
  exact sum_divisors_square_reindex M F
    (fun a b ha => by dsimp only [F]; rw [hf a ha,zero_mul,zero_mul])
    (fun a b hb => by dsimp only [F]; rw [hg b hb,mul_zero,zero_mul])

theorem amplifiedAdditiveMain_eq_profileChi {T : ℝ} (hT : 1 < T)
    (w : ℝ → ℂ) (η : ℝ) (P Q : ℝ[X]) (u : ℂ) (β : Fin 4 → ℂ) :
    noDPAmplifiedAdditiveMain w T η (zeroExtendedPolynomialProfile η P)
      (zeroExtendedPolynomialProfile η Q) u β =
    profileChiAdditiveActual w T u
      (fun x => (zeroExtendedPolynomialProfile η P x:ℂ))
      (fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)) (Real.log T) (⌊T^η⌋₊^2) β := by
  classical
  let M := ⌊T^η⌋₊
  let f : ℝ → ℂ := fun x => (zeroExtendedPolynomialProfile η P x:ℂ)
  let g : ℝ → ℂ := fun x => (zeroExtendedPolynomialProfile η Q x:ℂ)
  let H (n : ℕ) := (n:ℂ)⁻¹*(∑' m : ℕ+, noDPAdditiveChiTerm w T (n:ℝ) u β m)
  let F (a b : ℕ) := f (Real.log a/Real.log T)*g (Real.log b/Real.log T)*H (a*b)
  have hL : 0 < Real.log T := Real.log_pos hT
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hM : ⌊Real.exp (Real.log T*η)⌋₊ = M := by
    dsimp only [M]
    rw [Real.rpow_def_of_pos hT0]
  have hf (n : ℕ) (hn : M < n) : f (Real.log n/Real.log T) = 0 := by
    exact profileWeight_zero_of_lt hL P (by simpa only [hM] using hn)
  have hg (n : ℕ) (hn : M < n) : g (Real.log n/Real.log T) = 0 := by
    exact profileWeight_zero_of_lt hL Q (by simpa only [hM] using hn)
  have hterm (a b : ℕ) :
      noDPAmplifierPairWeight T (zeroExtendedPolynomialProfile η P)
          (zeroExtendedPolynomialProfile η Q) a b*
        (∑' m : ℕ+, noDPAdditiveChiTerm w T ((a+1:ℝ)*(b+1:ℝ)) u β m) =
          F (a+1) (b+1) := by
    dsimp only [noDPAmplifierPairWeight,F,f,g,H]
    push_cast
    simp only [div_eq_mul_inv]
    ring
  have hamplified : noDPAmplifiedAdditiveMain w T η (zeroExtendedPolynomialProfile η P)
      (zeroExtendedPolynomialProfile η Q) u β =
        ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, F a b := by
    unfold noDPAmplifiedAdditiveMain
    simp_rw [hterm]
    rw [sum_range_add_one_Icc M (fun a => ∑ b ∈ Finset.range M, F a (b+1))]
    apply Finset.sum_congr rfl
    intro a _
    exact sum_range_add_one_Icc M (F a)
  have hgrouped : profileChiAdditiveActual w T u f g (Real.log T) (M^2) β =
      ∑ a ∈ Finset.Icc 1 M, ∑ b ∈ Finset.Icc 1 M, F a b := by
    unfold profileChiAdditiveActual
    calc
      _ = ∑ N : Finset.Icc 1 (M^2), profileCoefficient f g (Real.log T) N.val*H N.val := by
        apply Finset.sum_congr rfl
        intro N _
        dsimp only [H]
        ring
      _ = ∑ N ∈ Finset.Icc 1 (M^2), profileCoefficient f g (Real.log T) N*H N :=
        Finset.sum_coe_sort _ (fun N => profileCoefficient f g (Real.log T) N*H N)
      _ = _ := profileCoefficient_eval_square M (Real.log T) f g H hf hg
  exact hamplified.trans hgrouped.symm

end
end Sechstmoment.Source.NoDPGlobalLFactorization
