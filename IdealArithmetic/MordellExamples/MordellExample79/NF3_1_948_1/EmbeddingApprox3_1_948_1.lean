import IdealArithmetic.MordellExamples.MordellExample79.NF3_1_948_1.Invariants3_1_948_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# Bounds for `zeta1` under the real embedding

`K = ℚ(θ)` with `θ³ + 21θ² + 12θ + 2 = 0` has one real place.  Approximating the real root
by `r = -20.417` with error `ε = 0.001` and applying `realEmbeddingOfRealRootCubic_bound_ge`
to `zeta1 = (173θ² + 101θ + 17)/3` gives `23354.4 ≤ φ(ζ) ≤ 23358.6`, so the rounded bounds
`23300` and `23400` below are safe (the true value is `23356.994…`).

The Artin index bound uses `a/b = 5/2` and `c/d = 44/3`, so
`(c*b)/(a*d) = 88/15 = 5`: the primes `2`, `3`, `5` have to be certified.

Opus 5
-/

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module NumberField

namespace NF3_1_948_1

noncomputable section

/-- The defining polynomial of `K`, in the `Polynomial.C b₃ * X ^ 3 + …` shape. -/
lemma T_map_eq : map (algebraMap ℤ ℚ) T
    = Polynomial.C 1 * X ^ 3 + Polynomial.C 21 * X ^ 2 + Polynomial.C 12 * X
      + Polynomial.C 2 := by
  rw [T_def]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat, Polynomial.C_1, one_mul]

lemma hε_pos : (0 : ℚ) < 1 / 1000 := by norm_num

/-- `r = -20.417` is within `ε = 0.001` of the real root: the cubic changes sign across
`[r - ε, r + ε]`. -/
lemma hroot_sign :
    (((1 : ℚ) : ℝ) * ((-20417 / 1000 : ℝ) + ((1 / 1000 : ℚ) : ℝ)) ^ 3
        + ((21 : ℚ) : ℝ) * ((-20417 / 1000 : ℝ) + ((1 / 1000 : ℚ) : ℝ)) ^ 2
        + ((12 : ℚ) : ℝ) * ((-20417 / 1000 : ℝ) + ((1 / 1000 : ℚ) : ℝ)) + ((2 : ℚ) : ℝ)) *
    (((1 : ℚ) : ℝ) * ((-20417 / 1000 : ℝ) - ((1 / 1000 : ℚ) : ℝ)) ^ 3
        + ((21 : ℚ) : ℝ) * ((-20417 / 1000 : ℝ) - ((1 / 1000 : ℚ) : ℝ)) ^ 2
        + ((12 : ℚ) : ℝ) * ((-20417 / 1000 : ℝ) - ((1 / 1000 : ℚ) : ℝ)) + ((2 : ℚ) : ℝ)) < 0 := by
  push_cast
  norm_num

/-- `3 * C q = n` when `3 q = n`: folds the denominator of a basis coefficient away. -/
lemma cfold (q : ℚ) (n : ℕ) (h : 3 * q = (n : ℚ)) :
    (3 : ℚ[X]) * Polynomial.C q = (n : ℚ[X]) := by
  rw [show (3 : ℚ[X]) = Polynomial.C (3 : ℚ) from (map_ofNat Polynomial.C 3).symm,
    ← Polynomial.C_mul, h, Polynomial.C_eq_natCast]

/-- `zeta1 = (173θ² + 101θ + 17)/3`, the shape
`realEmbeddingOfRealRootCubic_bound_ge` requires.

Unlike the other examples the coefficients are *not* integers -- `ℤ[θ]` has index `3` in `O`
and `zeta1` genuinely needs the third basis vector -- so the identity is between polynomials
with rational coefficients and `ring` alone cannot close it: the products
`3 * Polynomial.C (101/3)` have to be folded to `Polynomial.C 101` first, which is what
`cfold` supplies to `linear_combination`. -/
lemma zeta1_eq_quadratic : (zeta1 : K) =
    ((173 / 3 : ℚ) : K) * Adj.root ^ 2 + ((101 / 3 : ℚ) : K) * Adj.root + ((17 / 3 : ℚ) : K) :=
  BQ.coe_equivFun_symm_quadratic ![-52, -24, 173] (17 / 3) (101 / 3) (173 / 3) (by
    simp [BQ, Fin.sum_univ_three, List.ofFn_succ, ofList_cons, ofList_nil, map_ofNat]
    linear_combination (-(X : ℚ[X]) ^ 2) * cfold (173/3) 173 (by norm_num)
      + (-(X : ℚ[X])) * cfold (101/3) 101 (by norm_num) - cfold (17/3) 17 (by norm_num))

/-- Lower bound for `zeta1` at the real place. -/
lemma zeta1_embedding_gt :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≥ 23300 := by
  have h := realEmbeddingOfRealRootCubic_bound_ge (K := K) (a₀ := 17 / 3) (a₁ := 101 / 3)
    (a₂ := 173 / 3) (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans ?_ h
  push_cast
  norm_num

/-- Upper bound for `zeta1` at the real place, from the same approximation. -/
lemma zeta1_embedding_le :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≤ 23400 := by
  have h := realEmbeddingOfRealRootCubic_bound_le (K := K) (a₀ := 17 / 3) (a₁ := 101 / 3)
    (a₂ := 173 / 3) (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans h ?_
  push_cast
  norm_num

/-- `8 ^ 5 ≤ ((|disc K| - 24)/4) ^ 2`. -/
lemma disc_pow_bound : (8:ℚ) ^ 5 ≤ ((((|NumberField.discr K| : ℤ) : ℚ) - 24) / 4) ^ 2 := by
  rw [K_discr]
  norm_num

/-- `φ(zeta1) ^ 3 ≤ 2 ^ 44`. -/
lemma zeta1_pow_le_two_pow :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K) ^ 3
      ≤ 2 ^ 44 := by
  refine le_trans (pow_le_pow_left₀ (le_trans (by norm_num) zeta1_embedding_gt)
    zeta1_embedding_le 3) ?_
  norm_num

/-- In particular `zeta1 > 1` at the real place. -/
lemma zeta1_embedding_one_lt :
    1 < (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding
      (zeta1 : K) := by
  refine lt_of_lt_of_le ?_ zeta1_embedding_gt
  norm_num

end

end NF3_1_948_1
