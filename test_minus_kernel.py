"""Independent exact regressions for the unbalanced denominator.

The first evaluator mirrors Finite.dminus's integer arithmetic. The second
integrates the original x-coordinate slice in (4.7): its inclusion-exclusion
masks use d minus selected caps, then integrate a two-variable polynomial.
It never performs the residual-coordinate change used by the Lean proof.

All arithmetic uses integers and Fraction. These six regressions supplement
the Lean kernel proof; they are not a formal proof or a zeta asymptotic.
Run with: python3 -m unittest -v test_minus_kernel
"""

from fractions import Fraction
from math import comb, factorial
import unittest


BASE = 100_000_000
SCALE = 24 * BASE
EVEN_DEGREES = (0, 2, 4, 6, 8)


def integer_shift(coefficients, delta):
    """The five integer coefficients of scale^4 p((z+delta)/scale)."""
    return [
        sum(
            (coefficients[r] if r < len(coefficients) else 0)
            * SCALE ** (4 - r)
            * comb(r, k)
            * delta ** (r - k)
            for r in range(k, 5)
        )
        for k in range(5)
    ]


def product_coefficients(p, q):
    return [
        sum(p[i] * q[k - i] for i in range(5) if 0 <= k - i < 5)
        for k in range(9)
    ]


def integer_minus_kernel(A, B, C, D, p, q):
    """Existing integer evaluator divided by 256 * 13! * scale^13."""
    if A + B + C <= D:
        return Fraction(0)
    values = [24 * A, 24 * B, 24 * C]
    H = sum(values) - 24 * D
    t0 = (SCALE - H) // 2
    assert 2 * t0 == SCALE - H
    pq = product_coefficients(integer_shift(p, -t0), integer_shift(q, t0))
    total = 0
    for mask in range(8):
        HH = H - sum(values[i] for i in range(3) if mask >> i & 1)
        if HH <= 0:
            continue
        sign = (-1) ** mask.bit_count()
        for k in EVEN_DEGREES:
            if pq[k] == 0:
                continue
            outer_quotient, remainder = divmod(factorial(13), factorial(k + 5))
            assert remainder == 0
            factor = factorial(k) * 2 ** (8 - k) * outer_quotient
            for l1 in range(k // 2 + 1):
                for l2 in range(k // 2 - l1 + 1):
                    exponents = [2 * l1 + 1, 2 * l2 + 1, 2 * (k // 2 - l1 - l2) + 1]
                    for d1 in range(exponents[0] + 1 if mask & 1 else 1):
                        for d2 in range(exponents[1] + 1 if mask & 2 else 1):
                            for d3 in range(exponents[2] + 1 if mask & 4 else 1):
                                h = k + 5 - d1 - d2 - d3
                                denominator = (
                                    factorial(d1) * factorial(d2)
                                    * factorial(d3) * factorial(h)
                                )
                                quotient, remainder = divmod(factorial(k + 5), denominator)
                                assert remainder == 0
                                total += (
                                    sign * pq[k] * factor * quotient
                                    * values[0] ** d1 * values[1] ** d2
                                    * values[2] ** d3 * HH ** h
                                )
    return Fraction(total, 256 * factorial(13) * SCALE ** 13)


def polynomial_multiply(p, q):
    """Sparse two-variable polynomials with Fraction coefficients."""
    result = {}
    for (i, j), coefficient in p.items():
        for (u, v), other in q.items():
            index = i + u, j + v
            result[index] = result.get(index, Fraction(0)) + coefficient * other
    return result


def polynomial_power(p, n):
    result = {(0, 0): Fraction(1)}
    for _ in range(n):
        result = polynomial_multiply(result, p)
    return result


def original_slice_kernel(A, B, C, D, p, q):
    """Direct dx1 dx2 integration of the original capped x-simplex.

    The box integrand is p(X-t0)q(X+t0). Its even moments are computed
    from three symmetric interval integrals. Upper-cap violations are
    removed in the x variables, not the residual variables; each remaining
    monomial is integrated on x,y >= 0, x+y <= D-sum(selected caps).
    """
    a, b, c, d = (Fraction(i, BASE) for i in (A, B, C, D))
    t0 = (1 - a - b - c + d) / 2

    def real_shift(coefficients, delta):
        return [
            sum(
                (coefficients[r] if r < len(coefficients) else 0)
                * comb(r, k) * delta ** (r - k)
                for r in range(k, 5)
            )
            for k in range(5)
        ]

    pq = product_coefficients(real_shift(p, -t0), real_shift(q, t0))
    total = Fraction(0)
    for mask in range(8):
        caps = [a, b, c]
        offsets = [caps[i] if mask >> i & 1 else Fraction(0) for i in range(3)]
        H = d - sum(offsets)
        if H <= 0:
            continue
        residuals = [
            {(0, 0): a - offsets[0], (1, 0): Fraction(-1)},
            {(0, 0): b - offsets[1], (0, 1): Fraction(-1)},
            {(0, 0): c - offsets[2] - H, (1, 0): Fraction(1), (0, 1): Fraction(1)},
        ]
        polynomial = {}
        for k in EVEN_DEGREES:
            for l1 in range(k // 2 + 1):
                for l2 in range(k // 2 - l1 + 1):
                    ls = [l1, l2, k // 2 - l1 - l2]
                    coefficient = pq[k] * Fraction(
                        factorial(k),
                        2 ** k * factorial(2 * ls[0] + 1)
                        * factorial(2 * ls[1] + 1) * factorial(2 * ls[2] + 1),
                    )
                    if coefficient == 0:
                        continue
                    term = {(0, 0): Fraction(1)}
                    for i in range(3):
                        term = polynomial_multiply(term, polynomial_power(residuals[i], 2 * ls[i] + 1))
                    for index, value in term.items():
                        polynomial[index] = polynomial.get(index, Fraction(0)) + coefficient * value
        value = sum(
            coefficient * Fraction(factorial(i) * factorial(j), factorial(i + j + 2))
            * H ** (i + j + 2)
            for (i, j), coefficient in polynomial.items()
        )
        total += (-1) ** mask.bit_count() * value
    return total


class MinusKernelRegressionTests(unittest.TestCase):
    def assert_kernel_equal(self, arguments, *, zero):
        integer = integer_minus_kernel(*arguments)
        original = original_slice_kernel(*arguments)
        self.assertEqual(integer, original)
        self.assertEqual(integer == 0, zero)

    def test_odd_polynomials_on_full_original_simplex(self):
        self.assert_kernel_equal((2, 3, 4, 1, [2, -3, 1], [-1, 2, 0, 1]), zero=False)

    def test_quartic_polynomial_with_active_upper_caps(self):
        self.assert_kernel_equal(
            (50_000_000, 30_000_000, 20_000_000, 40_000_000,
             [1, 2, -1, 3, 2], [-2, 1, 0, 1]),
            zero=False,
        )

    def test_odd_linear_polynomial_with_several_upper_caps(self):
        self.assert_kernel_equal(
            (50_000_000, 30_000_000, 20_000_000, 70_000_000, [0, 1], [1]),
            zero=False,
        )

    def test_zero_residual_total(self):
        self.assert_kernel_equal((2, 3, 4, 9, [1], [1]), zero=True)

    def test_zero_interval_width(self):
        self.assert_kernel_equal((0, 3, 4, 2, [1], [1]), zero=True)

    def test_zero_original_slice_total(self):
        self.assert_kernel_equal((2, 3, 4, 0, [1], [1]), zero=True)


if __name__ == "__main__":
    unittest.main()
