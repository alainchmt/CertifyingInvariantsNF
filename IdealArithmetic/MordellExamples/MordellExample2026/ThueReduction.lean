import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.Invariants2_2_8104_1
import IdealArithmetic.MordellThueProject.ClassGroupDescent

/-!
# `y ^ 2 = x ^ 3 + 2026` reduces to the Thue equation `A ^ 3 + 3AB ^ 2 - 90B ^ 3 = 1`

The case `3 ∤ h` with `x` odd, at `d = 2026`: here `2026 ≡ 2 [ZMOD 4]`, so `O = ℤ[√2026]` is
the full ring of integers, and `3 ∤ 14 = h_K`.

The certified inputs are those of `NF2_2_8104_1`: `O_integral_closure`, `ClassGroupO_equiv`
(whence the class number `14`) and `units_eq_zeta1_pow_mul_cube` (the units modulo cubes).

Opus 5
-/

set_option linter.all false

open Mordell Polynomial NumberField NF2_2_8104_1

-- `K` carries two `CommSemiring` paths (`instCommRingK` and `Field.toSemifield.toCommSemiring`)
-- and the diamond propagates to `O`.  Without this the `ring` family silently fails on both:
-- even `example (u v : K) : u + v = v + u := by ring` does not close.
attribute [local instance 10000] CommRing.toCommSemiring CommRing.toRing

noncomputable section

/-! ### `√2026` inside `O`, and `zeta1` in terms of it -/

/-- The element `√2026` of `O`: the second vector of the integral basis, i.e. `Adj.root`. -/
def sd : O := B.equivFun.symm ![0, 1]

lemma sd_eq_root : sd = ⟨Adj.root, hroot_mem⟩ := hroot_coord

lemma sd_sq : sd ^ 2 = 2026 := by
  have h : aeval (timesTableO.basis.equivFun.symm ![0, 1]) (ofList [(-2026 : ℤ), 0, 1]) = 0 := by
    rw [← minpoly_hroot]; exact minpoly.aeval ℤ _
  rw [T_ofList, T_def] at h
  simp only [map_sub, map_pow, aeval_X, map_ofNat] at h
  exact eq_of_sub_eq_zero h

/-- `(n : ℤ) • 1 = n` in `O`.  Needed because `B_one_repr`'s `1` and a freshly elaborated
`(1 : O)` go through different instance paths: they are defeq, but not syntactically equal,
so `simp` cannot bridge them and `exact` must. -/
lemma zsmul_one_eq (n : ℤ) : n • (1 : O) = (n : O) := by simp

/-- The fundamental unit, in terms of `√2026`: `zeta1 = 45 - √2026`. -/
lemma zeta1_eq : zeta1 = 45 - sd := by
  have h : (![45, -1] : Fin 2 → ℤ) = (45 : ℤ) • ![1, 0] - ![0, 1] := by decide
  show B.equivFun.symm ![45, -1] = 45 - B.equivFun.symm ![0, 1]
  rw [h, map_sub, map_smul, B_one_repr]
  congr 1
  exact zsmul_one_eq 45

/-! ### The class group of `O` -/

instance instNeZero14 : ∀ i : Fin 1, NeZero ((![14] : Fin 1 → ℕ) i) := fun i => by
  fin_cases i; exact ⟨by decide⟩

instance : Finite (ClassGroup O) :=
  Finite.of_equiv _ (ClassGroupO_equiv.toEquiv.trans Additive.toMul)

lemma card_classGroup : Nat.card (ClassGroup O) = 14 := by
  rw [Nat.card_congr (ClassGroupO_equiv.toEquiv.trans Additive.toMul).symm, Nat.card_pi]
  simp [Nat.card_eq_fintype_card, ZMod.card]

end

noncomputable section

/-! ### Coordinates with respect to `1, √2026` -/

lemma zsmul_eq (n : ℤ) (z : O) : n • z = (n : O) * z :=
  (Algebra.smul_def n z).trans (congrArg (· * z) (eq_intCast (algebraMap ℤ O) n))

lemma sd_eq_B1 : sd = B 1 := by
  show B.equivFun.symm ![0, 1] = B 1
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zero_smul]
  exact (zero_add _).trans (one_smul ℤ (B 1))

lemma coord_eq (p q : ℤ) : B.equivFun.symm ![p, q] = (p : O) + (q : O) * sd := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, sd_eq_B1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  congr 1
  · rw [B_one]; exact zsmul_one_eq p
  · exact zsmul_eq q (B 1)

lemma exists_coords (δ : O) : ∃ a b : ℤ, δ = (a : O) + (b : O) * sd := by
  refine ⟨B.equivFun δ 0, B.equivFun δ 1, ?_⟩
  rw [← coord_eq]
  conv_lhs => rw [← B.equivFun.symm_apply_apply δ]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma coords_inj {p q r s : ℤ} (hc : (p : O) + (q : O) * sd = (r : O) + (s : O) * sd) :
    p = r ∧ q = s := by
  rw [← coord_eq, ← coord_eq] at hc
  have h2 := B.equivFun.symm.injective hc
  exact ⟨congrFun h2 0, congrFun h2 1⟩

/-- Expansion of a cube in the basis `1, √2026`. -/
lemma cube_expand (a b : ℤ) :
    ((a : O) + (b : O) * sd) ^ 3
      = ((a ^ 3 + 6078 * a * b ^ 2 : ℤ) : O) + ((3 * a ^ 2 * b + 2026 * b ^ 3 : ℤ) : O) * sd := by
  push_cast
  linear_combination ((b : O) ^ 3 * sd + 3 * (a : O) * (b : O) ^ 2) * sd_sq

/-- Multiplication by `zeta1 = 45 - √2026` in the basis `1, √2026`. -/
lemma mul_zeta1_expand (P Q : ℤ) :
    zeta1 * (((P : ℤ) : O) + ((Q : ℤ) : O) * sd)
      = ((45 * P - 2026 * Q : ℤ) : O) + ((45 * Q - P : ℤ) : O) * sd := by
  rw [zeta1_eq]
  push_cast
  linear_combination (-(Q : O)) * sd_sq

/-! ### The descent -/

lemma sd_sq' : sd ^ 2 = ((2026 : ℤ) : O) := by push_cast; exact sd_sq

lemma hsqfree : Squarefree (2026 : ℤ) := Int.squarefree_natCast.mpr (by decide +kernel)

/-- **Mordell implies Thue.**  Every solution of `y ^ 2 = x ^ 3 + 2026` yields a solution of
`A ^ 3 + 3 * A * B ^ 2 - 90 * B ^ 3 = 1`, together with the formula recovering `x`.

The class-group descent is `exists_unit_mul_cube_of_mordell`, its coprimality input
`isCoprime_two_mul` (`x` is odd because `2026 ≡ 2 [ZMOD 4]`).  What is left is the
coefficient match in the basis `1, √2026`.  `x` is recovered from the *norm* `a ^ 2 - 2026 b ^ 2`
of `γ`: matching coefficients gives `y ^ 2 - 2026 = ± N ^ 3`, so `x = ± N` by `cube_inj`, and the
formula for `x` is then a single `linear_combination`.

Only `x` is concluded about: once `x` is known, `y` is determined up to sign by the equation
itself, so carrying a formula for `y` through the descent buys nothing.  This matches the
other examples. -/
theorem mordell_imp_thue {x y : ℤ} (h : y ^ 2 = x ^ 3 + 2026) :
    ∃ A B : ℤ, A ^ 3 + 3 * A * B ^ 2 - 90 * B ^ 3 = 1 ∧
      x = -A ^ 2 + 90 * A * B + B ^ 2 := by
  have hne : ((y : O) + sd) ≠ 0 := by
    intro h0
    refine one_ne_zero (coords_inj (p := y) (q := 1) (r := 0) (s := 0) ?_).2
    push_cast
    rw [one_mul, zero_mul, add_zero]
    exact h0
  have hcard3 : Nat.Coprime 3 (Nat.card (ClassGroup O)) := by rw [card_classGroup]; decide
  obtain ⟨u, γ, hγ⟩ := exists_unit_mul_cube_of_mordell sd_sq' hcard3 h
    (isCoprime_two_mul hsqfree h (not_two_dvd_of_mordell (by decide) h)) hne
  obtain ⟨e, t, ht⟩ := units_eq_zeta1_pow_mul_cube u
  obtain ⟨a, b, hab⟩ := exists_coords ((t : O) * γ)
  have hmain : (y : O) + sd = zeta1 ^ (e : ℕ) * ((a : O) + (b : O) * sd) ^ 3 := by
    rw [← hab, hγ, ht]; ring
  fin_cases e <;> norm_num at hmain
  · -- `e = 0` : `b * (3a² + 2026b²) = 1` is impossible
    exfalso
    rw [cube_expand] at hmain
    obtain ⟨-, hq⟩ := coords_inj (p := y) (q := 1)
      (r := a ^ 3 + 6078 * a * b ^ 2) (s := 3 * a ^ 2 * b + 2026 * b ^ 3)
      (by rw [Int.cast_one, one_mul]; exact hmain)
    have hbd : (b : ℤ) ∣ 1 := ⟨3 * a ^ 2 + 2026 * b ^ 2, by linear_combination hq⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hbd) with hb | hb <;>
      subst hb <;> nlinarith [sq_nonneg a, hq]
  · -- `e = 1` : `(A, B) = (-a + 45b, b)`, and `N(zeta1 γ³) = -N(γ)³`
    rw [cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨hy, hq⟩ := coords_inj (p := y) (q := 1)
      (r := 45 * (a ^ 3 + 6078 * a * b ^ 2) - 2026 * (3 * a ^ 2 * b + 2026 * b ^ 3))
      (s := 45 * (3 * a ^ 2 * b + 2026 * b ^ 3) - (a ^ 3 + 6078 * a * b ^ 2))
      (by rw [Int.cast_one, one_mul]; exact hmain)
    have hN : y ^ 2 - 2026 * 1 ^ 2 = -((a ^ 2 - 2026 * b ^ 2) ^ 3) := by rw [hy, hq]; ring
    have hxN : x = -(a ^ 2 - 2026 * b ^ 2) := cube_inj (by linear_combination hN - h)
    exact ⟨-a + 45 * b, b, by linear_combination -hq, by linear_combination hxN⟩
  · -- `e = 2` : `(A, B) = (b, a - 45b)`, and `N(zeta1² γ³) = N(γ)³`
    rw [cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨hy, hq⟩ := coords_inj (p := y) (q := 1)
      (r := 45 * (45 * (a ^ 3 + 6078 * a * b ^ 2) - 2026 * (3 * a ^ 2 * b + 2026 * b ^ 3))
        - 2026 * (45 * (3 * a ^ 2 * b + 2026 * b ^ 3) - (a ^ 3 + 6078 * a * b ^ 2)))
      (s := 45 * (45 * (3 * a ^ 2 * b + 2026 * b ^ 3) - (a ^ 3 + 6078 * a * b ^ 2))
        - (45 * (a ^ 3 + 6078 * a * b ^ 2) - 2026 * (3 * a ^ 2 * b + 2026 * b ^ 3)))
      (by rw [Int.cast_one, one_mul]; exact hmain)
    have hN : y ^ 2 - 2026 * 1 ^ 2 = (a ^ 2 - 2026 * b ^ 2) ^ 3 := by rw [hy, hq]; ring
    have hxN : x = a ^ 2 - 2026 * b ^ 2 := cube_inj (by linear_combination hN - h)
    exact ⟨b, a - 45 * b, by linear_combination -hq, by linear_combination hxN⟩

end
