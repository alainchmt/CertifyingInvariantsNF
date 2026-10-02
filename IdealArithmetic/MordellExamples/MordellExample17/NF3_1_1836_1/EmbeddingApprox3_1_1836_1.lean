import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_1836_1.Invariants3_1_1836_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# Bounds for `zeta1` under the real embedding

`K = ℚ(θ)` with `θ³ - 6θ - 10 = 0` has one real place.  Approximating the real root by
`r = 3.047` with error `ε = 0.002` and applying `realEmbeddingOfRealRootCubic_bound_ge` to
`zeta1 = θ² + 3θ + 3` gives `21.4070 ≤ φ(zeta1) ≤ 21.4440` (the true value is `21.42230…`).

The Artin index bound uses `a/b = 5/2` and `c/d = 9/2`, so
`(c*b)/(a*d) = 18/10 = 1`: no prime has to be certified at all.

Opus 5
-/

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module NumberField

namespace NF3_1_1836_1

noncomputable section

/-- The defining polynomial of `K`, in the `Polynomial.C b₃ * X ^ 3 + …` shape. -/
lemma T_map_eq : map (algebraMap ℤ ℚ) T
    = Polynomial.C 1 * X ^ 3 + Polynomial.C 0 * X ^ 2 + Polynomial.C (-6) * X
      + Polynomial.C (-10) := by
  rw [T_def]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat, map_ofNat, Polynomial.C_1, Polynomial.C_0,
    one_mul, zero_mul, add_zero]
  simp only [Polynomial.C_neg, map_ofNat]
  ring

lemma hε_pos : (0 : ℚ) < 2 / 1000 := by norm_num

/-- `r = 3.047` is within `ε = 0.002` of the real root: the cubic changes sign across
`[r - ε, r + ε]`. -/
lemma hroot_sign :
    (((1 : ℚ) : ℝ) * ((3047 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) ^ 3
        + ((0 : ℚ) : ℝ) * ((3047 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) ^ 2
        + ((-6 : ℚ) : ℝ) * ((3047 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) + ((-10 : ℚ) : ℝ)) *
    (((1 : ℚ) : ℝ) * ((3047 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) ^ 3
        + ((0 : ℚ) : ℝ) * ((3047 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) ^ 2
        + ((-6 : ℚ) : ℝ) * ((3047 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) + ((-10 : ℚ) : ℝ)) < 0 := by
  push_cast
  norm_num

/-- `zeta1 = θ² + 3θ + 3`, the shape `realEmbeddingOfRealRootCubic_bound_ge` requires. -/
lemma zeta1_eq_quadratic : (zeta1 : K) =
    ((1 : ℚ) : K) * Adj.root ^ 2 + ((3 : ℚ) : K) * Adj.root + ((3 : ℚ) : K) :=
  BQ.coe_equivFun_symm_quadratic ![3, 3, 1] (3) (3) (1) (by
    simp [BQ, Fin.sum_univ_three, List.ofFn_succ, ofList_cons, ofList_nil, map_ofNat]
    ring)

/-- Lower bound for `zeta1` at the real place. -/
lemma zeta1_embedding_gt :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≥ 21407 / 1000 := by
  have h := realEmbeddingOfRealRootCubic_bound_ge (K := K) (a₀ := 3) (a₁ := 3) (a₂ := 1)
    (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans ?_ h
  push_cast
  norm_num

/-- Upper bound for `zeta1` at the real place, from the same approximation. -/
lemma zeta1_embedding_le :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≤ 21444 / 1000 := by
  have h := realEmbeddingOfRealRootCubic_bound_le (K := K) (a₀ := 3) (a₁ := 3) (a₂ := 1)
    (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans h ?_
  push_cast
  norm_num

/-- `8 ^ 5 ≤ ((|disc K| - 24)/4) ^ 2`. -/
lemma disc_pow_bound : (8:ℚ) ^ 5 ≤ ((((|NumberField.discr K| : ℤ) : ℚ) - 24) / 4) ^ 2 := by
  rw [K_discr]
  norm_num

/-- `φ(zeta1) ^ 2 ≤ 2 ^ 9`. -/
lemma zeta1_pow_le_two_pow :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K) ^ 2
      ≤ 2 ^ 9 := by
  refine le_trans (pow_le_pow_left₀ (le_trans (by norm_num) zeta1_embedding_gt)
    zeta1_embedding_le 2) ?_
  norm_num

/-- In particular `zeta1 > 1` at the real place. -/
lemma zeta1_embedding_one_lt :
    1 < (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding
      (zeta1 : K) := by
  refine lt_of_lt_of_le ?_ zeta1_embedding_gt
  norm_num

end

end NF3_1_1836_1
