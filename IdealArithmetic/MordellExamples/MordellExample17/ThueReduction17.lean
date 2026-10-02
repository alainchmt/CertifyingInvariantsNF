import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.Invariants2_2_17_1
import IdealArithmetic.MordellThueProject.ClassGroupDescent

/-!
# `y ^ 2 = x ^ 3 + 17` reduces to four Thue equations

The case `d ≡ 1 [ZMOD 8]`, where `x` may be even: here `O = ℤ[ω]` with
`ω = (1+√17)/2`, and `x` may be **even**.  The descent therefore splits:

* `x` odd  — `y + √17 = ζ^e γ³` with `γ ∈ ℤ[√17]` (the lattice lemma);
* `x` even — `y + √17 = ζ^e (2π) γ³` with `γ ∈ O` and `ππ̄ = 2`.

Certified inputs from `NF2_2_17_1`: `O_integral_closure`, `class_number_K_eq_1` and
`units_eq_zeta1_pow_mul_cube`.

Opus 5
-/

set_option linter.all false

open Mordell Polynomial NumberField NF2_2_17_1

-- `K` carries two `CommSemiring` paths and the diamond propagates to `O`; without this the
-- `ring` family silently fails on both.
attribute [local instance 10000] CommRing.toCommSemiring CommRing.toRing

noncomputable section

/-! ### `ω` and `√17` inside `O` -/

/-- `ω = (1+√17)/2`, the second vector of the integral basis. -/
def w : O := B.equivFun.symm ![0, 1]

/-- `√17 = 2ω - 1`. -/
def sd : O := B.equivFun.symm ![-1, 2]

lemma sd_sq : sd ^ 2 = 17 := by
  have h : aeval (timesTableO.basis.equivFun.symm ![(-1 : ℤ), 2]) (ofList [(-17 : ℤ), 0, 1]) = 0 := by
    rw [← minpoly_hroot]; exact minpoly.aeval ℤ _
  rw [T_ofList, T_def] at h
  simp only [map_sub, map_pow, aeval_X, map_ofNat] at h
  exact eq_of_sub_eq_zero h

lemma zsmul_one_eq' (n : ℤ) : n • (1 : O) = (n : O) := by simp

lemma zsmul_eq (n : ℤ) (z : O) : n • z = (n : O) * z :=
  (Algebra.smul_def n z).trans (congrArg (· * z) (eq_intCast (algebraMap ℤ O) n))

/-- Coordinates with respect to the basis `1, ω`. -/
lemma coord_eq (p q : ℤ) : B.equivFun.symm ![p, q] = (p : O) + (q : O) * w := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, show w = B 1 from ?_]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    congr 1
    · rw [B_one]; exact zsmul_one_eq' p
    · exact zsmul_eq q (B 1)
  · show B.equivFun.symm ![0, 1] = B 1
    rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zero_smul]
    exact (zero_add _).trans (one_smul ℤ (B 1))

lemma sd_eq : sd = 2 * w - 1 := by
  have h : (![(-1 : ℤ), 2]) = (2 : ℤ) • ![0, 1] - ![1, 0] := by decide
  show B.equivFun.symm ![-1, 2] = 2 * w - 1
  rw [h, map_sub, map_smul, B_one_repr, show w = B.equivFun.symm ![0, 1] from rfl]
  rw [zsmul_eq 2 (B.equivFun.symm ![0, 1])]
  norm_num

lemma four_ne_zero_O : (4 : O) ≠ 0 := by
  have h : ((4 : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  simpa using h

/-- `ω² = ω + 4`. -/
lemma w_sq : w ^ 2 = w + 4 := by
  have h := sd_sq
  rw [sd_eq] at h
  have h4 : (4 : O) * w ^ 2 = 4 * (w + 4) := by linear_combination h
  exact mul_left_cancel₀ four_ne_zero_O h4

lemma exists_coords (δ : O) : ∃ a b : ℤ, δ = (a : O) + (b : O) * w := by
  refine ⟨B.equivFun δ 0, B.equivFun δ 1, ?_⟩
  rw [← coord_eq]
  conv_lhs => rw [← B.equivFun.symm_apply_apply δ]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma coords_inj {p q r s : ℤ} (hc : (p : O) + (q : O) * w = (r : O) + (s : O) * w) :
    p = r ∧ q = s := by
  rw [← coord_eq, ← coord_eq] at hc
  have h2 := B.equivFun.symm.injective hc
  exact ⟨congrFun h2 0, congrFun h2 1⟩

/-- The fundamental unit, in coordinates: `zeta1 = 5 - 2ω = 4 - √17`. -/
lemma zeta1_eq : zeta1 = 5 - 2 * w := by
  have h : (![(5 : ℤ), -2]) = (5 : ℤ) • ![1, 0] - (2 : ℤ) • ![0, 1] := by decide
  show B.equivFun.symm ![5, -2] = 5 - 2 * w
  rw [h, map_sub, map_smul, map_smul, B_one_repr,
    show w = B.equivFun.symm ![0, 1] from rfl, zsmul_eq 2 (B.equivFun.symm ![0, 1])]
  congr 1
  exact zsmul_one_eq' 5

/-! ### The class group of `O` -/

instance instNeZero1 : ∀ i : Fin 1, NeZero ((![1] : Fin 1 → ℕ) i) := fun i => by
  fin_cases i; exact ⟨by decide⟩

instance : Finite (ClassGroup O) :=
  Finite.of_equiv _ (ClassGroupO_equiv.toEquiv.trans Additive.toMul)

lemma card_classGroup : Nat.card (ClassGroup O) = 1 := by
  rw [Nat.card_congr (ClassGroupO_equiv.toEquiv.trans Additive.toMul).symm, Nat.card_pi]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-! ### Expansion lemmas in the basis `1, ω` -/

lemma cube_expand (a b : ℤ) :
    ((a : O) + (b : O) * w) ^ 3
      = ((a ^ 3 + 12 * a * b ^ 2 + 4 * b ^ 3 : ℤ) : O)
        + ((3 * a ^ 2 * b + 3 * a * b ^ 2 + 5 * b ^ 3 : ℤ) : O) * w := by
  push_cast
  linear_combination (3 * (a : O) * (b : O) ^ 2 + (b : O) ^ 3 * (w + 1)) * w_sq

lemma mul_zeta1_expand (P Q : ℤ) :
    zeta1 * (((P : ℤ) : O) + ((Q : ℤ) : O) * w)
      = ((5 * P - 8 * Q : ℤ) : O) + ((3 * Q - 2 * P : ℤ) : O) * w := by
  rw [zeta1_eq]
  push_cast
  linear_combination (-2 * ((Q : ℤ) : O)) * w_sq

lemma mul_tw_expand (P Q : ℤ) :
    (2 * w - 6) * (((P : ℤ) : O) + ((Q : ℤ) : O) * w)
      = ((-6 * P + 8 * Q : ℤ) : O) + ((2 * P - 4 * Q : ℤ) : O) * w := by
  push_cast
  linear_combination (2 * ((Q : ℤ) : O)) * w_sq

/-! ### Arithmetic input -/

lemma hsqfree : Squarefree (17 : ℤ) := Int.squarefree_natCast.mpr (by decide +kernel)

lemma prime_17 : Prime (17 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; norm_num

lemma not_dvd_17 {x y : ℤ} (h : y ^ 2 = x ^ 3 + 17) : ¬ (17 : ℤ) ∣ x :=
  fun hd => not_dvd_of_dvd_x hsqfree h prime_17 hd dvd_rfl

lemma sd_sq' : sd ^ 2 = ((17 : ℤ) : O) := by push_cast; exact sd_sq

lemma two_ne_zero_O : (2 : O) ≠ 0 := by
  have h : ((2 : ℕ) : O) ≠ 0 := Nat.cast_ne_zero.mpr (by norm_num)
  simpa using h

lemma card_classGroup3 : Nat.Coprime 3 (Nat.card (ClassGroup O)) := by
  rw [card_classGroup]
  exact Nat.coprime_one_right 3

lemma ne_zero_of_add_sd (y : ℤ) : ((y : O) + sd) ≠ 0 := by
  intro h0
  rw [sd_eq] at h0
  have := coords_inj (p := y - 1) (q := 2) (r := 0) (s := 0) (by push_cast; linear_combination h0)
  simpa using this.2

/-- **The lattice lemma.**  The norm of `γ = a + bω` is `a² + ab - 4b²`, and the descent makes
it `± x`, which is odd; so `γ` already lies in `ℤ[√17]`, i.e. `b` is even.  This is
`Mordell.even_of_odd_norm` at `m = 4 = (17-1)/4`. -/
lemma even_of_norm_odd {x a b : ℤ} (hx2 : ¬ (2 : ℤ) ∣ x)
    (hx : x = a ^ 2 + a * b - 4 * b ^ 2 ∨ x = -(a ^ 2 + a * b - 4 * b ^ 2)) : Even b := by
  have hxo : Odd x := Int.not_even_iff_odd.mp fun he => hx2 he.two_dvd
  refine even_of_odd_norm (m := 4) (A := a) (B := b) (by decide) ?_
  rcases hx with hx | hx <;> rw [hx] at hxo <;> obtain ⟨k, hk⟩ := hxo
  · exact ⟨k, by linarith⟩
  · exact ⟨-k - 1, by linarith⟩

/-! ### The `x` odd branch -/

/-- With `x` odd the descent gives `y + √17 = zeta1 ^ e γ³`.  Taking norms on both sides of the
coefficient match does two jobs at once: it shows `N(γ) = ± x` is odd, whence `b` is even
(`even_of_norm_odd`), and it gives `x` as the quadratic form `± N(γ)`, so the formula for `x`
is a single `linear_combination`. -/
theorem odd_branch {x y : ℤ} (h : y ^ 2 = x ^ 3 + 17) (hx2 : ¬ (2 : ℤ) ∣ x) :
    ∃ A B : ℤ, A ^ 3 + 3 * A * B ^ 2 - 8 * B ^ 3 = 1 ∧ x = -A ^ 2 + 8 * A * B + B ^ 2 := by
  obtain ⟨u, γ, hγ⟩ := exists_unit_mul_cube_of_mordell sd_sq' card_classGroup3 h
    (isCoprime_two_mul hsqfree h hx2) (ne_zero_of_add_sd y)
  obtain ⟨e, t, ht⟩ := units_eq_zeta1_pow_mul_cube u
  obtain ⟨a, b, hab⟩ := exists_coords ((t : O) * γ)
  have hmain : (y : O) + sd = zeta1 ^ (e : ℕ) * ((a : O) + (b : O) * w) ^ 3 := by
    rw [← hab, hγ, ht]; ring
  rw [sd_eq] at hmain
  fin_cases e <;> norm_num at hmain
  · -- `e = 0` : degenerate
    exfalso
    rw [cube_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj (p := y - 1) (q := 2)
      (r := a ^ 3 + 12 * a * b ^ 2 + 4 * b ^ 3)
      (s := 3 * a ^ 2 * b + 3 * a * b ^ 2 + 5 * b ^ 3)
      (by push_cast at hmain ⊢; linear_combination hmain)
    have hN : (y - 1) ^ 2 + (y - 1) * 2 - 4 * 2 ^ 2 = (a ^ 2 + a * b - 4 * b ^ 2) ^ 3 := by
      rw [hG, hF]; ring
    obtain ⟨c, rfl⟩ : Even b :=
      even_of_norm_odd (a := a) hx2 (Or.inl (cube_inj (by linear_combination hN - h)))
    have hf : (1 : ℤ) = c * (3 * a ^ 2 + 6 * a * c + 20 * c ^ 2) :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hF)
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one ⟨_, hf⟩) with hc | hc <;>
      subst hc <;> nlinarith [sq_nonneg a, sq_nonneg (a + 1), sq_nonneg (a - 1), hf]
  · -- `e = 1` : `(A, B) = (-a + 3c, c)` with `b = 2c`
    rw [cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj (p := y - 1) (q := 2)
      (r := 5 * a ^ 3 - 24 * a ^ 2 * b + 36 * a * b ^ 2 - 20 * b ^ 3)
      (s := -2 * a ^ 3 + 9 * a ^ 2 * b - 15 * a * b ^ 2 + 7 * b ^ 3)
      (by push_cast at hmain ⊢; linear_combination hmain)
    have hN : (y - 1) ^ 2 + (y - 1) * 2 - 4 * 2 ^ 2 = -((a ^ 2 + a * b - 4 * b ^ 2) ^ 3) := by
      rw [hG, hF]; ring
    have hxN : x = -(a ^ 2 + a * b - 4 * b ^ 2) := cube_inj (by linear_combination hN - h)
    obtain ⟨c, rfl⟩ : Even b := even_of_norm_odd hx2 (Or.inr hxN)
    have hf : (1 : ℤ) = -a ^ 3 + 9 * a ^ 2 * c - 30 * a * c ^ 2 + 28 * c ^ 3 :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hF)
    exact ⟨-a + 3 * c, c, by linear_combination -hf, by linear_combination hxN⟩
  · -- `e = 2` : `(A, B) = (c, a - 3c)` with `b = 2c`
    rw [cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj (p := y - 1) (q := 2)
      (r := 41 * a ^ 3 - 192 * a ^ 2 * b + 300 * a * b ^ 2 - 156 * b ^ 3)
      (s := -16 * a ^ 3 + 75 * a ^ 2 * b - 117 * a * b ^ 2 + 61 * b ^ 3)
      (by push_cast at hmain ⊢; linear_combination hmain)
    have hN : (y - 1) ^ 2 + (y - 1) * 2 - 4 * 2 ^ 2 = (a ^ 2 + a * b - 4 * b ^ 2) ^ 3 := by
      rw [hG, hF]; ring
    have hxN : x = a ^ 2 + a * b - 4 * b ^ 2 := cube_inj (by linear_combination hN - h)
    obtain ⟨c, rfl⟩ : Even b := even_of_norm_odd hx2 (Or.inl hxN)
    have hf : (1 : ℤ) = -8 * a ^ 3 + 75 * a ^ 2 * c - 234 * a * c ^ 2 + 244 * c ^ 3 :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hF)
    exact ⟨c, a - 3 * c, by linear_combination -hf, by linear_combination hxN⟩

/-! ### The `x` even branch

`2` splits as `π π'` with `π = ω - 3`, `π' = -2 - ω`, and `π ∣ η = (y+√17)/2` exactly when
`(y-1)/2` is odd -- so after replacing `y` by `-y` (which leaves `x` alone) we may assume
`y ≡ 3 mod 4`, and then `κ = η/π` is written out in coordinates.  The rest is
`Mordell.exists_unit_mul_cube_of_even`: no primality of `π`, no valuation count. -/

lemma pi_mul_conj : ((w : O) - 3) * (-2 - w) = 2 := by linear_combination -w_sq

/-- The `x` even branch, normalised so that `y ≡ 3 mod 4`. -/
theorem even_branch_aux {x y m : ℤ} (h : y ^ 2 = x ^ 3 + 17) (hx2 : (2 : ℤ) ∣ x)
    (hm : y = 4 * m + 3) :
    ∃ A B : ℤ,
      (A ^ 3 - 6 * A * B ^ 2 - 10 * B ^ 3 = 1 ∧ x = 2 * A ^ 2 + 10 * A * B + 4 * B ^ 2) ∨
      (A ^ 3 + 6 * A * B ^ 2 - 6 * B ^ 3 = 1 ∧ x = -2 * A ^ 2 + 6 * A * B + 4 * B ^ 2) ∨
      (A ^ 3 - 12 * A * B ^ 2 - 18 * B ^ 3 = 1 ∧ x = 4 * A ^ 2 + 18 * A * B + 16 * B ^ 2) := by
  obtain ⟨X, hX⟩ := hx2
  -- `κ = η / π` and `κ' = η̄ / π̄`, written out in the basis `1, ω`
  set κ : O := ((-2 * m - 3 : ℤ) : O) + ((-m - 2 : ℤ) : O) * w with hκdef
  set κ' : O := ((-3 * m - 5 : ℤ) : O) + ((m + 2 : ℤ) : O) * w with hκ'def
  have hη : ((y : ℤ) : O) + sd = 2 * (((w : O) - 3) * κ) := by
    rw [hm, sd_eq, hκdef]; push_cast; linear_combination (2 * (m : O) + 4) * w_sq
  have hη' : ((y : ℤ) : O) - sd = 2 * ((-2 - (w : O)) * κ') := by
    rw [hm, sd_eq, hκ'def]; push_cast; linear_combination (2 * (m : O) + 4) * w_sq
  have h17X : ¬ (17 : ℤ) ∣ X := fun ⟨k, hk⟩ => not_dvd_17 h ⟨2 * k, by rw [hX, hk]; ring⟩
  have hbez : IsCoprime (2 * X) (17 : ℤ) := by
    refine isCoprime_of_prime_dvd (by simp) fun q hq hqX hq17 => ?_
    have h17 : (17 : ℤ) ∣ 2 * X := ((hq.associated_of_dvd prime_17 hq17).symm.dvd).trans hqX
    exact h17X ((prime_17.dvd_mul.mp h17).resolve_left (by norm_num))
  have hκ0 : κ ≠ 0 := fun h0 => ne_zero_of_add_sd y (by rw [hη, h0]; simp)
  obtain ⟨u, γ, hγ⟩ := exists_unit_mul_cube_of_even sd_sq' two_ne_zero_O card_classGroup3 h hX
    pi_mul_conj hη hη' hbez hκ0
  obtain ⟨e, t, ht⟩ := units_eq_zeta1_pow_mul_cube u
  obtain ⟨a, b, hab⟩ := exists_coords ((t : O) * γ)
  have hmain : (y : O) + sd = (2 * w - 6) * (zeta1 ^ (e : ℕ) * ((a : O) + (b : O) * w) ^ 3) := by
    rw [← hab, hη, hγ, ht]; ring
  rw [sd_eq] at hmain
  fin_cases e <;> norm_num at hmain
  · -- `e = 0` : the Thue equation `A³ - 6AB² - 10B³ = 1`
    rw [cube_expand, mul_tw_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj (p := y - 1) (q := 2)
      (r := -6 * a ^ 3 + 24 * a ^ 2 * b - 48 * a * b ^ 2 + 16 * b ^ 3)
      (s := 2 * a ^ 3 - 12 * a ^ 2 * b + 12 * a * b ^ 2 - 12 * b ^ 3)
      (by push_cast at hmain ⊢; linear_combination hmain)
    have hN : (y - 1) ^ 2 + (y - 1) * 2 - 4 * 2 ^ 2 = 8 * (a ^ 2 + a * b - 4 * b ^ 2) ^ 3 := by
      rw [hG, hF]; ring
    have hxN : x = 2 * (a ^ 2 + a * b - 4 * b ^ 2) := cube_inj (by linear_combination hN - h)
    have hf : (1 : ℤ) = a ^ 3 - 6 * a ^ 2 * b + 6 * a * b ^ 2 - 6 * b ^ 3 :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hF)
    exact ⟨a - 2 * b, b, Or.inl ⟨by linear_combination -hf, by linear_combination hxN⟩⟩
  · -- `e = 1` : the Thue equation `A³ - 12AB² - 18B³ = 1`
    rw [cube_expand, mul_zeta1_expand, mul_tw_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj (p := y - 1) (q := 2)
      (r := -46 * a ^ 3 + 216 * a ^ 2 * b - 336 * a * b ^ 2 + 176 * b ^ 3)
      (s := 18 * a ^ 3 - 84 * a ^ 2 * b + 132 * a * b ^ 2 - 68 * b ^ 3)
      (by push_cast at hmain ⊢; linear_combination hmain)
    have hN : (y - 1) ^ 2 + (y - 1) * 2 - 4 * 2 ^ 2 = -(8 * (a ^ 2 + a * b - 4 * b ^ 2) ^ 3) := by
      rw [hG, hF]; ring
    have hxN : x = -(2 * (a ^ 2 + a * b - 4 * b ^ 2)) := cube_inj (by linear_combination hN - h)
    have hf : (1 : ℤ) = 9 * a ^ 3 - 42 * a ^ 2 * b + 66 * a * b ^ 2 - 34 * b ^ 3 :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hF)
    exact ⟨3 * a - 4 * b, -a + b,
      Or.inr (Or.inr ⟨by linear_combination -hf, by linear_combination hxN⟩)⟩
  · -- `e = 2` : the Thue equation `A³ + 6AB² - 6B³ = 1`
    rw [cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand, mul_tw_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj (p := y - 1) (q := 2)
      (r := -374 * a ^ 3 + 1752 * a ^ 2 * b - 2736 * a * b ^ 2 + 1424 * b ^ 3)
      (s := 146 * a ^ 3 - 684 * a ^ 2 * b + 1068 * a * b ^ 2 - 556 * b ^ 3)
      (by push_cast at hmain ⊢; linear_combination hmain)
    have hN : (y - 1) ^ 2 + (y - 1) * 2 - 4 * 2 ^ 2 = 8 * (a ^ 2 + a * b - 4 * b ^ 2) ^ 3 := by
      rw [hG, hF]; ring
    have hxN : x = 2 * (a ^ 2 + a * b - 4 * b ^ 2) := cube_inj (by linear_combination hN - h)
    have hf : (1 : ℤ) = 73 * a ^ 3 - 342 * a ^ 2 * b + 534 * a * b ^ 2 - 278 * b ^ 3 :=
      mul_left_cancel₀ two_ne_zero (by linear_combination hF)
    exact ⟨a - 2 * b, -2 * a + 3 * b,
      Or.inr (Or.inl ⟨by linear_combination -hf, by linear_combination hxN⟩)⟩

/-- The `x` even branch.  The residue of `y` mod `4` decides which of `η, η̄` is divisible by
`π`; replacing `y` by `-y` swaps the two and leaves `x` untouched. -/
theorem even_branch {x y : ℤ} (h : y ^ 2 = x ^ 3 + 17) (hx2 : (2 : ℤ) ∣ x) :
    ∃ A B : ℤ,
      (A ^ 3 - 6 * A * B ^ 2 - 10 * B ^ 3 = 1 ∧ x = 2 * A ^ 2 + 10 * A * B + 4 * B ^ 2) ∨
      (A ^ 3 + 6 * A * B ^ 2 - 6 * B ^ 3 = 1 ∧ x = -2 * A ^ 2 + 6 * A * B + 4 * B ^ 2) ∨
      (A ^ 3 - 12 * A * B ^ 2 - 18 * B ^ 3 = 1 ∧ x = 4 * A ^ 2 + 18 * A * B + 16 * B ^ 2) := by
  obtain ⟨X, hX⟩ := hx2
  rcases Int.even_or_odd y with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact absurd (show (17 : ℤ) = 2 * (2 * k ^ 2 - 4 * X ^ 3) from by
      rw [hk, hX] at h; linarith) (by omega)
  rcases Int.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- `y ≡ 1 mod 4` : apply the normalised branch to `-y`
    exact even_branch_aux (x := x) (y := -y) (m := -m - 1) (by linear_combination h) ⟨X, hX⟩
      (by rw [hk, hm]; ring)
  · exact even_branch_aux h ⟨X, hX⟩ (by rw [hk, hm]; ring)

/-! ### The descent -/

/-- **Descent from the Mordell equation `y² = x³ + 17` to four Thue equations.**

`ℚ(√17)` has class number `1` and fundamental unit `zeta1 = 4 - √17`, so modulo cubes the
units are `1, zeta1, zeta1²`.  Splitting on the parity of `x` and running over these three
classes produces six binary cubic forms, which collapse to the four Thue equations below. -/
theorem mordell17_imp_thue {x y : ℤ} (h : y ^ 2 = x ^ 3 + 17) :
    ∃ A B : ℤ,
      (A ^ 3 + 3 * A * B ^ 2 - 8 * B ^ 3 = 1 ∧ x = -A ^ 2 + 8 * A * B + B ^ 2) ∨
      (A ^ 3 - 6 * A * B ^ 2 - 10 * B ^ 3 = 1 ∧ x = 2 * A ^ 2 + 10 * A * B + 4 * B ^ 2) ∨
      (A ^ 3 + 6 * A * B ^ 2 - 6 * B ^ 3 = 1 ∧ x = -2 * A ^ 2 + 6 * A * B + 4 * B ^ 2) ∨
      (A ^ 3 - 12 * A * B ^ 2 - 18 * B ^ 3 = 1 ∧ x = 4 * A ^ 2 + 18 * A * B + 16 * B ^ 2) := by
  by_cases hx2 : (2 : ℤ) ∣ x
  · obtain ⟨A, B, hAB⟩ := even_branch h hx2
    exact ⟨A, B, Or.inr hAB⟩
  · obtain ⟨A, B, h1, h2⟩ := odd_branch h hx2
    exact ⟨A, B, Or.inl ⟨h1, h2⟩⟩

end
