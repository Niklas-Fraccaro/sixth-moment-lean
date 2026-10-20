import SixthMoment.Analysis.Quadrature.PiecewisePolynomial
import SixthMoment.Certificate.Kernels.Balanced.DensityBridge

namespace SixthMoment
open scoped BigOperators

def DenominatorKnots (a b c d : ℝ) : List ℝ := [a,b,c,d,a+c,a+d,b+c,b+d]

def AvoidsDenominatorKnots (a b c d l u : ℝ) : Prop :=
  ∀ k ∈ DenominatorKnots a b c d, k ≤ l ∨ u ≤ k

theorem density_corner_0_polynomial (a b c d l u : ℝ)
    (_hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (min a t-(min c t)) 0) l u := by
  rcases hk a (by simp [DenominatorKnots]) with hx | hx
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (a-c) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh])
    · apply (polynomialOn_hinge_left (a) l u (hk (a) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh])
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_right (c) l u (hk (c) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh])
    · apply ((polynomialOn_const (max (0) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh]
        ring)

theorem density_corner_1_polynomial (a b c d l u : ℝ)
    (hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (min a t+min c t-t) 0) l u := by
  rcases hk a (by simp [DenominatorKnots]) with hx | hx
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_left (a+c) l u (hk (a+c) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh])
    · apply ((polynomialOn_const (max (a) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh]
        ring)
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (c) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh]
        ring)
    · apply (polynomialOn_hinge_right (0) l u (Or.inl hl)).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_hh]
        ring)

theorem density_corner_2_polynomial (a b c d l u : ℝ)
    (hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (max 0 (t-b)-(min c t)) 0) l u := by
  rcases hk b (by simp [DenominatorKnots]) with hx | hx
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_right (b+c) l u (hk (b+c) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)
    · apply ((polynomialOn_const (max (-b) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (-c) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)
    · apply (polynomialOn_hinge_left (0) l u (Or.inl hl)).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh])

theorem density_corner_3_polynomial (a b c d l u : ℝ)
    (_hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (max 0 (t-b)+min c t-t) 0) l u := by
  rcases hk b (by simp [DenominatorKnots]) with hx | hx
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (-b+c) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)
    · apply (polynomialOn_hinge_right (b) l u (hk (b) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)
  · rcases hk c (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_left (c) l u (hk (c) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_hh : min c t = c := min_eq_left (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)
    · apply ((polynomialOn_const (max (0) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_hh : min c t = t := min_eq_right (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_hh]
        ring)

theorem density_corner_4_polynomial (a b c d l u : ℝ)
    (hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (min a t-(max 0 (t-d))) 0) l u := by
  rcases hk a (by simp [DenominatorKnots]) with hx | hx
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_left (a+d) l u (hk (a+d) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)
    · apply ((polynomialOn_const (max (a) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (d) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)
    · apply (polynomialOn_hinge_right (0) l u (Or.inl hl)).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll])

theorem density_corner_5_polynomial (a b c d l u : ℝ)
    (_hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (min a t+max 0 (t-d)-t) 0) l u := by
  rcases hk a (by simp [DenominatorKnots]) with hx | hx
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (a-d) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)
    · apply (polynomialOn_hinge_left (a) l u (hk (a) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_hi : min a t = a := min_eq_left (by linarith [ht.1])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_right (d) l u (hk (d) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)
    · apply ((polynomialOn_const (max (0) 0) l u).mono (by omega)).congr
      intro t ht
      have h_hi : min a t = t := min_eq_right (by linarith [ht.2])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_hi, h_ll]
        ring)

theorem density_corner_6_polynomial (a b c d l u : ℝ)
    (_hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (max 0 (t-b)-(max 0 (t-d))) 0) l u := by
  rcases hk b (by simp [DenominatorKnots]) with hx | hx
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (-b+d) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)
    · apply (polynomialOn_hinge_right (b) l u (hk (b) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_left (d) l u (hk (d) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)
    · apply ((polynomialOn_const (max (0) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)

theorem density_corner_7_polynomial (a b c d l u : ℝ)
    (hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 1 (fun t => max (max 0 (t-b)+max 0 (t-d)-t) 0) l u := by
  rcases hk b (by simp [DenominatorKnots]) with hx | hx
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply (polynomialOn_hinge_right (b+d) l u (hk (b+d) (by simp [DenominatorKnots]))).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)
    · apply ((polynomialOn_const (max (-b) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = t-b := max_eq_right (by linarith [ht.1])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)
  · rcases hk d (by simp [DenominatorKnots]) with hy | hy
    · apply ((polynomialOn_const (max (-d) 0) l u).mono (by omega)).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_ll : max 0 (t-d) = t-d := max_eq_right (by linarith [ht.1])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)
    · apply (polynomialOn_hinge_left (0) l u (Or.inl hl)).congr
      intro t ht
      have h_lo : max 0 (t-b) = 0 := max_eq_left (by linarith [ht.2])
      have h_ll : max 0 (t-d) = 0 := max_eq_left (by linarith [ht.2])
      exact congrArg (fun z : ℝ => max z 0) (by
        rw [h_lo, h_ll]
        ring)

theorem density_upper_polynomial (k l u : ℝ) (hk : k ≤ l ∨ u ≤ k) :
    PolynomialOn 1 (fun t => min k t) l u := by
  rcases hk with hk | hk
  · apply ((polynomialOn_const k l u).mono (by omega)).congr
    intro t ht
    exact (min_eq_left (hk.trans ht.1)).symm
  · apply (polynomialOn_id l u).congr
    intro t ht
    exact (min_eq_right (ht.2.trans hk)).symm

noncomputable def realW6Formula (t a b c d : ℝ) : ℝ :=
  let lo := max 0 (t-b)
  let hi := min a t
  let ll := max 0 (t-d)
  let hh := min c t
  3*(hi^2-lo^2)*(hh-ll) +
    (max (hi-hh) 0)^3 - (max (hi+hh-t) 0)^3 -
    (max (lo-hh) 0)^3 + (max (lo+hh-t) 0)^3 -
    (max (hi-ll) 0)^3 + (max (hi+ll-t) 0)^3 +
    (max (lo-ll) 0)^3 - (max (lo+ll-t) 0)^3

theorem realW6Formula_polynomial (a b c d l u : ℝ)
    (hl : 0 ≤ l) (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 3 (fun t => realW6Formula t a b c d) l u := by
  have hi := density_upper_polynomial a l u (hk a (by simp [DenominatorKnots]))
  have hh := density_upper_polynomial c l u (hk c (by simp [DenominatorKnots]))
  have lo := (polynomialOn_hinge_right b l u (hk b (by simp [DenominatorKnots]))).congr
    (fun t _ => max_comm (t-b) 0)
  have ll := (polynomialOn_hinge_right d l u (hk d (by simp [DenominatorKnots]))).congr
    (fun t _ => max_comm (t-d) 0)
  have first := (((hi.pow 2).sub (lo.pow 2)).mul (hh.sub ll)).const_mul 3
  have h0 := (density_corner_0_polynomial a b c d l u hl hk).pow 3
  have h1 := (density_corner_1_polynomial a b c d l u hl hk).pow 3
  have h2 := (density_corner_2_polynomial a b c d l u hl hk).pow 3
  have h3 := (density_corner_3_polynomial a b c d l u hl hk).pow 3
  have h4 := (density_corner_4_polynomial a b c d l u hl hk).pow 3
  have h5 := (density_corner_5_polynomial a b c d l u hl hk).pow 3
  have h6 := (density_corner_6_polynomial a b c d l u hl hk).pow 3
  have h7 := (density_corner_7_polynomial a b c d l u hl hk).pow 3
  apply (((((((first.add h0).sub h1).sub h2).add h3).sub h4).add h5).add h6).sub h7 |>.congr
  intro t _
  dsimp only [realW6Formula]
  ring

theorem realW6_eq_formula {a b c d t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : 0 ≤ t) (hmax : t ≤ min (a+b) (c+d)) :
    realW6 t a b c d = realW6Formula t a b c d := by
  have hlu : max 0 (t-b) ≤ min a t := by
    simp only [max_le_iff, le_min_iff]
    have hab := hmax.trans (min_le_left _ _)
    (repeat' constructor) <;> linarith
  have hmv : max 0 (t-d) ≤ min c t := by
    simp only [max_le_iff, le_min_iff]
    have hcd := hmax.trans (min_le_right _ _)
    (repeat' constructor) <;> linarith
  rw [realW6_integral ha hb hc hd ht hmax]
  have hi := denominator_density_cubic hlu hmv t
  have he (r s : ℝ) : r-(t-s) = r+s-t := by ring
  simp_rw [he] at hi
  dsimp only [realW6Formula]
  simp_rw [he]
  linear_combination hi

theorem realW6_polynomialOn {a b c d l u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hl : 0 ≤ l) (hu : u ≤ min (a+b) (c+d))
    (hk : AvoidsDenominatorKnots a b c d l u) :
    PolynomialOn 3 (fun t => realW6 t a b c d) l u := by
  apply (realW6Formula_polynomial a b c d l u hl hk).congr
  intro t ht
  exact (realW6_eq_formula ha hb hc hd (hl.trans ht.1) (ht.2.trans hu)).symm

end SixthMoment
