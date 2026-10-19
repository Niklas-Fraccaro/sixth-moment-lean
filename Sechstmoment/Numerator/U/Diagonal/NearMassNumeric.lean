import Sechstmoment.Numerator.U.Diagonal.ActualNearAmplifierMass

/-! An explicit numerical consequence of the genuine hyperbola count.
Product orientation is chosen freely; no near-comparability assumption enters.
-/
namespace Sechstmoment
open Real
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 2000000

theorem nearFactorHarmonicBudget_le {u v L P J Q K H : ℕ} {D R : ℝ}
    (hu : 0<u) (hv : 0<v) (hL : 0<L) (hJ : 0<J) (hP : 0<P) (hQ : 0<Q)
    (hPQ : P≤Q) (hPL : P≤8*L) (hQJ : Q≤8*J)
    (hK : (K:ℝ)≤2*Real.sqrt (Q:ℝ))
    (hH : (H:ℝ)≤D*Real.sqrt ((u:ℝ)*v*P*Q))
    (hD : 0≤D) (hR : 1≤R) (hHP : (harmonic P : ℝ)≤R) (hHK : (harmonic K : ℝ)≤R) :
    (P:ℝ)*(harmonic P : ℝ)*
      (2*(2*(H:ℝ)/(v:ℝ)+1)*(harmonic K : ℝ)+2*K)/
        Real.sqrt ((u:ℝ)*v*L*J) ≤
      80*R^2*(D*Real.sqrt ((P:ℝ)*Q)+Real.sqrt (P:ℝ)) := by
  have hur : (1:ℝ)≤u := by exact_mod_cast hu
  have hvr : (1:ℝ)≤v := by exact_mod_cast hv
  have hlr : (0:ℝ)<L := by exact_mod_cast hL
  have hjr : (0:ℝ)<J := by exact_mod_cast hJ
  have hpr : (1:ℝ)≤P := by exact_mod_cast hP
  have hqr : (1:ℝ)≤Q := by exact_mod_cast hQ
  have hpqr : (P:ℝ)≤Q := by exact_mod_cast hPQ
  have hplr : (P:ℝ)≤8*L := by exact_mod_cast hPL
  have hqjr : (Q:ℝ)≤8*J := by exact_mod_cast hQJ
  have hR0 : 0≤R := by linarith
  have hHP0 : 0≤(harmonic P : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  have hHK0 : 0≤(harmonic K : ℝ) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]
    exact Finset.sum_nonneg (fun _ _ => by positivity)
  let S := Real.sqrt ((u:ℝ)*v)
  let E := Real.sqrt ((u:ℝ)*v*L*J)
  have hSpos : 0<S := by dsimp [S]; positivity
  have hEpos : 0<E := by dsimp [E]; positivity
  have hS1 : 1≤S := by
    dsimp [S]
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hp1 : 1≤Real.sqrt (P:ℝ) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hpq : (P:ℝ)≤Real.sqrt ((P:ℝ)*Q) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  have hPLQJ : (P:ℝ)*Q≤64*(L:ℝ)*J := by
    nlinarith [mul_le_mul hplr hqjr (by positivity : (0:ℝ)≤Q) (by positivity : (0:ℝ)≤8*L)]
  have hden : S*Real.sqrt (P:ℝ)*Real.sqrt (Q:ℝ)≤8*E := by
    have hroot : Real.sqrt ((P:ℝ)*Q)≤8*Real.sqrt ((L:ℝ)*J) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by positivity,?_⟩
      rw [mul_pow,Real.sq_sqrt (by positivity)]
      nlinarith
    have he : E=S*Real.sqrt ((L:ℝ)*J) := by
      dsimp [E,S]
      rw [← Real.sqrt_mul (by positivity : (0:ℝ)≤(u:ℝ)*v)]
      congr 1
      ring
    rw [he]
    rw [mul_assoc,← Real.sqrt_mul (by positivity : (0:ℝ)≤P)]
    simpa [mul_assoc,mul_comm,mul_left_comm] using mul_le_mul_of_nonneg_left hroot hSpos.le
  have hratio : (P:ℝ)/E≤8/S := by
    apply (div_le_div_iff₀ hEpos hSpos).mpr
    have hsqrt : Real.sqrt (P:ℝ)≤Real.sqrt (Q:ℝ) := Real.sqrt_le_sqrt hpqr
    have hsq := Real.sq_sqrt (by positivity : (0:ℝ)≤P)
    have hmult := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg hSpos.le (Real.sqrt_nonneg (P:ℝ)))
    nlinarith
  have hend : (P:ℝ)*(K:ℝ)/E≤16*Real.sqrt (P:ℝ) := by
    apply (div_le_iff₀ hEpos).mpr
    have hsq := Real.sq_sqrt (by positivity : (0:ℝ)≤P)
    have hmult := mul_le_mul_of_nonneg_left hden (Real.sqrt_nonneg (P:ℝ))
    have hkp := mul_le_mul_of_nonneg_left hK (by positivity : (0:ℝ)≤P)
    have hSprod := mul_le_mul_of_nonneg_left hS1
      (mul_nonneg (Nat.cast_nonneg P) (Real.sqrt_nonneg (Q:ℝ)))
    nlinarith
  have hHdiv : (H:ℝ)/(v:ℝ)≤H := div_le_self (Nat.cast_nonneg H) hvr
  have hHnorm : (H:ℝ)/S≤D*Real.sqrt ((P:ℝ)*Q) := by
    have he : Real.sqrt ((u:ℝ)*v*P*Q)=S*Real.sqrt ((P:ℝ)*Q) := by
      dsimp [S]
      rw [← Real.sqrt_mul (by positivity : (0:ℝ)≤(u:ℝ)*v)]
      congr 1
      ring
    apply (div_le_iff₀ hSpos).mpr
    rw [he] at hH
    nlinarith
  have hmain : (P:ℝ)/E*(4*((H:ℝ)/(v:ℝ))+2)≤
      32*D*Real.sqrt ((P:ℝ)*Q)+16*Real.sqrt (P:ℝ) := by
    calc
      _≤(8/S)*(4*(H:ℝ)+2) := mul_le_mul hratio
        (by nlinarith) (by positivity) (by positivity)
      _=32*((H:ℝ)/S)+16/S := by ring
      _≤32*(D*Real.sqrt ((P:ℝ)*Q))+16*Real.sqrt (P:ℝ) := by
        have hi : 1/S≤Real.sqrt (P:ℝ) := by
          calc
            1/S≤1 := by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) hS1
            _≤Real.sqrt (P:ℝ) := hp1
        rw [show 16/S=16*(1/S) by ring]
        linarith
      _=_ := by ring
  calc
    _≤(P:ℝ)*R*(2*(2*(H:ℝ)/(v:ℝ)+1)*R+2*K)/E := by
      dsimp [E]
      gcongr
    _=R^2*((P:ℝ)/E*(4*((H:ℝ)/(v:ℝ))+2))+2*R*((P:ℝ)*K/E) := by ring
    _≤R^2*(32*D*Real.sqrt ((P:ℝ)*Q)+16*Real.sqrt (P:ℝ))+
        2*R*(16*Real.sqrt (P:ℝ)) := by gcongr
    _≤80*R^2*(D*Real.sqrt ((P:ℝ)*Q)+Real.sqrt (P:ℝ)) := by
      have hh : R≤R^2 := by nlinarith
      have hpq0 : 0≤D*Real.sqrt ((P:ℝ)*Q) := by positivity
      have hp0 : 0≤Real.sqrt (P:ℝ) := Real.sqrt_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right hh hp0]

/-- Exact product orientation gives the smaller-product endpoint for the
actual four-index mass, including diagonal tuples. -/
theorem positiveNearFactorBlock_mass_le_symmetric
    {u v L P J Q Kp Kq H : ℕ} {D R : ℝ}
    (hu : 0<u) (hv : 0<v) (hL : 0<L) (hJ : 0<J) (hP : 0<P) (hQ : 0<Q)
    (hPL : P≤8*L) (hQJ : Q≤8*J)
    (hKp2 : P≤Kp^2) (hKq2 : Q≤Kq^2)
    (hKp : (Kp:ℝ)≤2*Real.sqrt (P:ℝ)) (hKq : (Kq:ℝ)≤2*Real.sqrt (Q:ℝ))
    (hH : (H:ℝ)≤D*Real.sqrt ((u:ℝ)*v*P*Q))
    (hD : 0≤D) (hR : 1≤R)
    (hHP : (harmonic P : ℝ)≤R) (hHQ : (harmonic Q : ℝ)≤R)
    (hHKp : (harmonic Kp : ℝ)≤R) (hHKq : (harmonic Kq : ℝ)≤R) :
    (∑ pq∈positiveNearFactorBlock L P J Q u v H,positiveNearFactorWeight u v pq)≤
      80*R^2*(D*Real.sqrt ((P:ℝ)*Q)+Real.sqrt ((min P Q:ℕ):ℝ)) := by
  rcases le_total P Q with hPQ | hQP
  · rw [min_eq_left hPQ]
    exact (positiveNearFactorBlock_mass_le_harmonic hu hv hL hJ hKq2).trans
      (nearFactorHarmonicBudget_le hu hv hL hJ hP hQ hPQ hPL hQJ hKq hH hD hR hHP hHKq)
  · rw [min_eq_right hQP,←positiveNearFactorBlock_mass_swap L P J Q u v H]
    have hH' : (H:ℝ)≤D*Real.sqrt ((v:ℝ)*u*Q*P) := by
      have he : (v:ℝ)*u*Q*P=(u:ℝ)*v*P*Q := by ring
      rw [he]
      exact hH
    have hh := (positiveNearFactorBlock_mass_le_harmonic hv hu hJ hL hKp2).trans
      (nearFactorHarmonicBudget_le hv hu hJ hL hQ hP hQP hQJ hPL hKp hH' hD hR hHQ hHKp)
    simpa [mul_comm] using hh

end
end Sechstmoment
