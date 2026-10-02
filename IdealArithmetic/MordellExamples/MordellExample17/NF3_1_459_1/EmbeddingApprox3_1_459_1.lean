import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_459_1.Invariants3_1_459_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# Bounds for `zeta1` under the real embedding

`K = ℚ(θ)` with `θ³ + 3θ - 8 = 0` has one real place.  Approximating the real root by
`r = 1.513` with error `ε = 0.002` and applying `realEmbeddingOfRealRootCubic_bound_ge` to
`zeta1 = 4θ² + 6θ + 21` gives `39.1984 ≤ φ(zeta1) ≤ 39.2710` (the true value is
`39.23006…`).

The Artin index bound uses `a/b = 9/4` (`8⁹ ≤ ((459-24)/4)⁴`) and `c/d = 11/2`
(`φ(zeta1)² ≤ 2¹¹`), so `(c*b)/(a*d) = 44/18 = 2`: only `p = 2` has to be certified.

Opus 5
-/

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module NumberField

namespace NF3_1_459_1

noncomputable section

/-- The defining polynomial of `K`, in the `Polynomial.C b₃ * X ^ 3 + …` shape. -/
lemma T_map_eq : map (algebraMap ℤ ℚ) T = Polynomial.C 1 * X ^ 3 + Polynomial.C 0 * X ^ 2 + Polynomial.C 3 * X + Polynomial.C (-8) := by
  rw [T_def]
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_ofNat, map_ofNat, Polynomial.C_1, Polynomial.C_0,
    one_mul, zero_mul, add_zero]
  simp only [Polynomial.C_neg, map_ofNat]
  ring

lemma hε_pos : (0 : ℚ) < 2 / 1000 := by norm_num

/-- `r = 1.513` is within `ε = 0.002` of the real root: the cubic changes sign across
`[r - ε, r + ε]`. -/
lemma hroot_sign :
    (((1 : ℚ) : ℝ) * ((1513 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) ^ 3
        + ((0 : ℚ) : ℝ) * ((1513 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) ^ 2
        + ((3 : ℚ) : ℝ) * ((1513 / 1000 : ℝ) + ((2 / 1000 : ℚ) : ℝ)) + ((-8 : ℚ) : ℝ)) *
    (((1 : ℚ) : ℝ) * ((1513 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) ^ 3
        + ((0 : ℚ) : ℝ) * ((1513 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) ^ 2
        + ((3 : ℚ) : ℝ) * ((1513 / 1000 : ℝ) - ((2 / 1000 : ℚ) : ℝ)) + ((-8 : ℚ) : ℝ)) < 0 := by
  push_cast
  norm_num

/-- `zeta1 = 4θ² + 6θ + 21`, the shape `realEmbeddingOfRealRootCubic_bound_ge` requires. -/
lemma zeta1_eq_quadratic : (zeta1 : K) =
    ((4 : ℚ) : K) * Adj.root ^ 2 + ((6 : ℚ) : K) * Adj.root + ((21 : ℚ) : K) :=
  BQ.coe_equivFun_symm_quadratic ![21, 2, 8] 21 6 4 (by
    simp [BQ, Fin.sum_univ_three, List.ofFn_succ, ofList_cons, ofList_nil, map_ofNat]
    ring)

/-- Lower bound for `zeta1` at the real place. -/
lemma zeta1_embedding_gt :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≥ 39198 / 1000 := by
  have h := realEmbeddingOfRealRootCubic_bound_ge (K := K) (a₀ := 21) (a₁ := 6) (a₂ := 4)
    (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans ?_ h
  push_cast
  norm_num

/-- Upper bound for `zeta1` at the real place, from the same approximation. -/
lemma zeta1_embedding_le :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K)
      ≤ 39271 / 1000 := by
  have h := realEmbeddingOfRealRootCubic_bound_le (K := K) (a₀ := 21) (a₁ := 6) (a₂ := 4)
    (by norm_num) hε_pos T_map_eq Adj hroot_sign
  rw [zeta1_eq_quadratic]
  refine le_trans h ?_
  push_cast
  norm_num

/-- `8 ^ 9 ≤ ((|disc K| - 24)/4) ^ 4`  (`134217728 ≤ 139867583.3…`). -/
lemma disc_pow_bound : (8:ℚ) ^ 9 ≤ ((((|NumberField.discr K| : ℤ) : ℚ) - 24) / 4) ^ 4 := by
  rw [K_discr]
  norm_num

/-- `φ(zeta1) ^ 2 ≤ 2 ^ 11`  (`1542.2 ≤ 2048`). -/
lemma zeta1_pow_le_two_pow :
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign).embedding (zeta1 : K) ^ 2
      ≤ 2 ^ 11 := by
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

end NF3_1_459_1
