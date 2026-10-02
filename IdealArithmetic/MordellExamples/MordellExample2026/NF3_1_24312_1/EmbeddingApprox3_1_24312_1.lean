import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.Invariants3_1_24312_1
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# A lower bound for `zeta1` under the real embedding

`K = ℚ(θ)` with `θ³ + 3θ - 90 = 0` has one real place.  Approximating the real root by
`r = 4.258` with error `ε = 0.02` and applying `realEmbeddingOfRealRootCubic_bound_ge`
to `zeta1 = a₂θ² + a₁θ + a₀` gives

  `φ(zeta1) ≥ 4.8223…e29`,

in particular `φ(zeta1) > 1`, which is the hypothesis needed by the Artin
inequality.  (The true value is `4.84447…e29`; the approximation costs about `2.2e27`.)

Opus 5
-/

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module NumberField

noncomputable section

/-- The defining polynomial of `K`, in the `C b₃ * X ^ 3 + …` shape. -/
lemma T_map_eq : map (algebraMap ℤ ℚ) T = C 1 * X ^ 3 + C 0 * X ^ 2 + C 3 * X + C (-90) := by
  rw [T_def]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat, map_ofNat, Polynomial.C_1, Polynomial.C_0,
    one_mul, zero_mul, add_zero]
  simp only [Polynomial.C_neg, map_ofNat]
  ring

lemma hε_pos : (0 : ℚ) < 2 / 100 := by norm_num

/-- `r = 4.258` is within `ε = 0.02` of the real root: the defining cubic changes sign
across `[r - ε, r + ε]` (the two values are `+1.1269…` and `-1.1688…`). -/
lemma hroot_sign :
    (((1 : ℚ) : ℝ) * ((4258 / 1000 : ℝ) + ((2 / 100 : ℚ) : ℝ)) ^ 3
        + ((0 : ℚ) : ℝ) * ((4258 / 1000 : ℝ) + ((2 / 100 : ℚ) : ℝ)) ^ 2
        + ((3 : ℚ) : ℝ) * ((4258 / 1000 : ℝ) + ((2 / 100 : ℚ) : ℝ)) + ((-90 : ℚ) : ℝ)) *
    (((1 : ℚ) : ℝ) * ((4258 / 1000 : ℝ) - ((2 / 100 : ℚ) : ℝ)) ^ 3
        + ((0 : ℚ) : ℝ) * ((4258 / 1000 : ℝ) - ((2 / 100 : ℚ) : ℝ)) ^ 2
        + ((3 : ℚ) : ℝ) * ((4258 / 1000 : ℝ) - ((2 / 100 : ℚ) : ℝ)) + ((-90 : ℚ) : ℝ)) < 0 := by
  push_cast
  norm_num

/-- `zeta1` as a quadratic in `θ`, the shape required by
`realEmbeddingOfRealRootCubic_bound_ge`. -/
lemma zeta1_eq_quadratic : (zeta1 : K) =
    ((25318107466978248199411982702 / 3 : ℚ) : K) * Adj.root ^ 2
      + ((35938665342336427911821503300 : ℚ) : K) * Adj.root
      + ((178361260665498855294599509801 : ℚ) : K) := by
  rw [zeta1_coe]
  simp [← Adj.algebraMap_apply, eq_ratCast]

set_option quotPrecheck false
local notation "ψ" => (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding

/-- Lower bound for `zeta1` at the real place. -/
lemma zeta1_embedding_gt : ψ zeta1 ≥ 482230000000000000000000000000 := by
  have h := realEmbeddingOfRealRootCubic_bound_ge (K := K)
    (a₀ := 178361260665498855294599509801)
    (a₁ := 35938665342336427911821503300)
    (a₂ := 25318107466978248199411982702 / 3)
    (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans ?_ h
  push_cast
  norm_num

/-- Upper bound for `zeta1` at the real place, from the same approximation. -/
lemma zeta1_embedding_le :
    ψ zeta1
      ≤ 486570000000000000000000000000 := by
  have h := realEmbeddingOfRealRootCubic_bound_le (K := K)
    (a₀ := 178361260665498855294599509801)
    (a₁ := 35938665342336427911821503300)
    (a₂ := 25318107466978248199411982702 / 3)
    (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans h ?_
  push_cast
  norm_num

/-!
### Rational bounds in the shape `artin_inequality_bound_index` consumes

`log₈((|disc K| - 24)/4) = log₈ 6072 = 4.18932…`, approximated from **below** by `a/b = 4/1`.
`log₂|φ(zeta1)| ≤ log₂(4.8657e29) = 98.61856…`, approximated from **above** by `c/d = 99/1`.
These give the index bound `(c*b)/(a*d) = 99/4 = 24`, so the primes to certify are
`2,3,5,7,11,13,17,19,23` — exactly the `NPCU p` already available.
-/

/-- `8 ^ a ≤ ((|disc K| - 24)/4) ^ b` with `a/b = 4/1`  (`8^4 = 4096 ≤ 6072`). -/
lemma disc_pow_bound : (8:ℚ) ^ 4 ≤ ((((|NumberField.discr K| : ℤ) : ℚ) - 24) / 4) ^ 1 := by
  rw [K_discr]
  norm_num

/-- `|φ(zeta1)| ^ d ≤ 2 ^ c` with `c/d = 99/1`  (`4.8657e29 ≤ 2^99 = 6.3383e29`). -/
lemma zeta1_pow_le_two_pow :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K) ^ 1
      ≤ 2 ^ 99 := by
  refine le_trans (pow_le_pow_left₀ (le_trans (by norm_num) zeta1_embedding_gt)
    zeta1_embedding_le 1) ?_
  norm_num

/-- In particular `zeta1 > 1` at the real place, as `artin_inequality` requires. -/
lemma zeta1_embedding_one_lt :
    1 < (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding
      (zeta1 : K) := by
  refine lt_of_lt_of_le ?_ zeta1_embedding_gt
  norm_num

end
