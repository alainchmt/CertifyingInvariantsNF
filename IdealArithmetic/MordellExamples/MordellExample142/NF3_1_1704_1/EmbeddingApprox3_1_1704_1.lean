import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.Invariants3_1_1704_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# Bounds for `zeta1` under the real embedding

`K = ℚ(θ)` with `θ³ + 15θ² + 66θ + 106 = 0` has one real place.  Approximating the real root
by `r = -8.948` with error `ε = 0.002` and applying `realEmbeddingOfRealRootCubic_bound_ge` to
`zeta1 = 21357θ² + 129255θ + 253003` gives `805390.76 ≤ φ(zeta1) ≤ 807436.95`, so the
rounded bounds `805000` and `808000` below are safe (the true value is `806385.0019…`).

The Artin index bound uses `a/b = 20/7` and `c/d = 59/3`, so
`(c*b)/(a*d) = 413/60 = 6`: the primes `2`, `3`, `5` have to be certified.

Opus 5
-/

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module NumberField

namespace NF3_1_1704_1

noncomputable section

/-- The defining polynomial of `K`, in the `Polynomial.C b₃ * X ^ 3 + …` shape. -/
lemma T_map_eq : map (algebraMap ℤ ℚ) T
    = Polynomial.C 1 * X ^ 3 + Polynomial.C 15 * X ^ 2 + Polynomial.C 66 * X
      + Polynomial.C 106 := by
  rw [T_def]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_ofNat, map_ofNat, Polynomial.C_1, one_mul]

lemma hε_pos : (0 : ℚ) < 2 / 1000 := by norm_num

/-- `r = -8.948` is within `ε = 0.002` of the real root: the cubic changes sign across
`[r - ε, r + ε]`. -/
lemma hroot_sign :
    (((1 : ℚ) : ℝ) * ((-8948 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) ^ 3
        + ((15 : ℚ) : ℝ) * ((-8948 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) ^ 2
        + ((66 : ℚ) : ℝ) * ((-8948 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) + ((106 : ℚ) : ℝ)) *
    (((1 : ℚ) : ℝ) * ((-8948 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) ^ 3
        + ((15 : ℚ) : ℝ) * ((-8948 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) ^ 2
        + ((66 : ℚ) : ℝ) * ((-8948 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) + ((106 : ℚ) : ℝ)) < 0 := by
  push_cast
  norm_num

/-- `zeta1 = 21357θ² + 129255θ + 253003`, the shape
`realEmbeddingOfRealRootCubic_bound_ge` requires. -/
lemma zeta1_eq_quadratic : (zeta1 : K) =
    ((21357 : ℚ) : K) * Adj.root ^ 2 + ((129255 : ℚ) : K) * Adj.root + ((253003 : ℚ) : K) :=
  BQ.coe_equivFun_symm_quadratic ![231646, 86541, 64071] (253003) (129255) (21357) (by
    simp [BQ, Fin.sum_univ_three, List.ofFn_succ, ofList_cons, ofList_nil, map_ofNat]
    ring)

/-- Lower bound for `zeta1` at the real place. -/
lemma zeta1_embedding_gt :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≥ 805000 := by
  have h := realEmbeddingOfRealRootCubic_bound_ge (K := K) (a₀ := 253003) (a₁ := 129255)
    (a₂ := 21357) (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans ?_ h
  push_cast
  norm_num

/-- Upper bound for `zeta1` at the real place, from the same approximation. -/
lemma zeta1_embedding_le :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≤ 808000 := by
  have h := realEmbeddingOfRealRootCubic_bound_le (K := K) (a₀ := 253003) (a₁ := 129255)
    (a₂ := 21357) (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans h ?_
  push_cast
  norm_num

/-- `8 ^ 20 ≤ ((|disc K| - 24)/4) ^ 7`. -/
lemma disc_pow_bound : (8:ℚ) ^ 20 ≤ ((((|NumberField.discr K| : ℤ) : ℚ) - 24) / 4) ^ 7 := by
  rw [K_discr]
  norm_num

/-- `φ(zeta1) ^ 3 ≤ 2 ^ 59`. -/
lemma zeta1_pow_le_two_pow :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K) ^ 3
      ≤ 2 ^ 59 := by
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

end NF3_1_1704_1
