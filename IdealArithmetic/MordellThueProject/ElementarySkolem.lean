import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import IdealArithmetic.MordellThueProject.ArtinInequality

/-!
# The elementary Skolem method for a cubic Thue equation

## AI use
This file was largely generated using Claude Code with Opus 5, after multiples rounds of
prompting. The main statements of the main results and the
high-level proof strategies were specified by me.
We also carried out some polishing afterwards.

## Main definitions
- `muRecenter`: the translate `z ↦ mu (η * z)` of a functional, which moves the distinguished
  solution from `0` to any known exponent.  This is what makes the general criterion below
  possible.

## Main results
- `norm_intCast_sub_mul`: the cubic Thue form is the norm form, `N (a - bθ) = F a b`.
- `exists_zpow_eq_of_thue`: a solution of `F a b = 1` is `ε ^ n` for some `n`, and that `n`
  satisfies `mu (ε ^ n) = 0`.
- `skolem_zpow_eq_zero_iff`: the Skolem criterion -- under `(S1)(S2)(S3)`, `mu (ε ^ n) = 0`
  holds exactly for `n = 0`.
- `skolem_zpow_eq_zero_iff_mem`: the same with several surviving classes, for equations with
  more than one solution.
- `exists_zpow_eq_coeffs_of_thue`: the coefficients of the solution, read off from `ε ^ n`.  -/

open Finset Polynomial

/-! ## Section 1: from the Thue equation to a power of the fundamental unit -/

open NumberField NumberField.ComplexEmbedding

section Thue

/-- **An element of norm one is a unit** (in the only case we need).  If `θ` satisfies
`θ³ + c₁θ² + c₂θ + c₃ = 0` and `F(a,b) = 1`, then `a - bθ` is a unit: an explicit inverse is
`(a² + abc₁ + b²c₂) + (ab + b²c₁)θ + b²θ²`, the product of the two other conjugates. -/
lemma isUnit_intCast_sub_mul {R : Type*} [CommRing R] {θ : R} {c₁ c₂ c₃ a b : ℤ}
    (hθ : θ ^ 3 + c₁ * θ ^ 2 + c₂ * θ + c₃ = 0)
    (hF : a ^ 3 + c₁ * a ^ 2 * b + c₂ * a * b ^ 2 + c₃ * b ^ 3 = 1) :
    IsUnit ((a : R) - b * θ) := by
  have hFR : a ^ 3 + c₁ * a ^ 2 * b + c₂ * a * b ^ 2
      + c₃ * (b : R) ^ 3 = 1 := by exact_mod_cast congrArg (fun z : ℤ => (z : R)) hF
  exact IsUnit.of_mul_eq_one (b := (a : R) ^ 2 + a * b * c₁ + (b : R) ^ 2 * c₂
    + ((a : R) * b + (b : R) ^ 2 * c₁) * θ + (b : R) ^ 2 * θ ^ 2)
    (by linear_combination hFR - (b : R) ^ 3 * hθ)

variable {K : Type*} [Field K] [NumberField K]

/-- **The norm is the minimal polynomial, evaluated.**  `N(c - x) = f(c)` for `f = minpoly ℚ x`. -/
lemma norm_algebraMap_sub {x : K}
    (hx : (minpoly ℚ x).natDegree = Module.finrank ℚ K) (c : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ K c - x) = (minpoly ℚ x).eval c := by
  have htop : Algebra.adjoin ℚ {x} = ⊤ := by
    have h1 := congrArg IntermediateField.toSubalgebra <|
      (Field.primitive_element_iff_minpoly_natDegree_eq ℚ x).mpr hx
    rwa [IntermediateField.top_toSubalgebra,
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (IsAlgebraic.of_finite ℚ x)] at h1
  set pb := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite ℚ x) htop with hpb
  rw [Algebra.norm_eq_matrix_det pb.basis, map_sub, AlgHom.commutes,
    show x = pb.gen from (PowerBasis.ofAdjoinEqTop_gen ..).symm,
    ← charpoly_leftMulMatrix pb, Matrix.eval_charpoly]
  rfl

/-- **The cubic Thue form is the norm form**:
`N(a - bθ) = a³ + c₁a²b + c₂ab² + c₃b³`.  For `b ≠ 0` this is `b³ f(a/b)`. -/
theorem norm_intCast_sub_mul (hdeg : Module.finrank ℚ K = 3) {θ : K} {c₁ c₂ c₃ : ℤ}
    (hmin : minpoly ℚ θ = X ^ 3 + C (c₁ : ℚ) * X ^ 2 + C (c₂ : ℚ) * X + C (c₃ : ℚ)) (a b : ℤ) :
    Algebra.norm ℚ ((a : K) - b * θ)
      = ((a ^ 3 + c₁ * a ^ 2 * b + c₂ * a * b ^ 2 + c₃ * b ^ 3 : ℤ) : ℚ) := by
  have hd3 : (minpoly ℚ θ).natDegree = 3 := by rw [hmin]; compute_degree!
  rcases eq_or_ne b 0 with rfl | hb
  · rw [show (a - (0 : ℤ) * θ) = algebraMap ℚ K a by simp,
      Algebra.norm_algebraMap, hdeg]
    push_cast; ring
  · have hbQ : b ≠ 0 := Int.cast_ne_zero.mpr hb
    have hbK : (b : K) ≠ 0 := Int.cast_ne_zero.mpr hb
    have hfac : (a : K) - b * θ = algebraMap ℚ K b * (algebraMap ℚ K ((a : ℚ) / b) - θ) := by
      rw [map_div₀]
      simp only [eq_ratCast, Rat.cast_intCast]
      field_simp
    rw [hfac, map_mul, Algebra.norm_algebraMap, hdeg,
      norm_algebraMap_sub (hd3.trans hdeg.symm), hmin]
    simp only [eval_add, eval_mul, eval_pow, eval_C, eval_X]
    field_simp
    push_cast
    ring

/-- **Norm one is detected by the real place.**  In a cubic field with one real and one
complex place `N(x) = φ(x)·|σ(x)|²`, so a nonzero element of norm one is positive there. -/
lemma embedding_pos_of_norm_eq_one (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ) {x : K} (hx0 : x ≠ 0)
    (hN : Algebra.norm ℚ x = 1) : 0 < hφ.embedding x := by
  have h := norm_eq_mul_normSq hdeg σ φ hφ hσ x
  rw [← hφ.coe_embedding_apply x] at h
  have hreal : (Algebra.norm ℚ x : ℚ) = hφ.embedding x * Complex.normSq (σ x) := by
    exact_mod_cast h
  rw [hN] at hreal
  norm_num at hreal
  have hpos : 0 < Complex.normSq (σ x) :=
    Complex.normSq_pos.mpr fun hz => hx0 ((map_eq_zero_iff σ σ.injective).mp hz)
  by_contra hle
  rw [not_lt] at hle
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hle hpos.le]

variable {O : Subalgebra ℤ K}

omit [NumberField K] in
/-- Integer powers of a unit of `O`, seen in `K`. -/
lemma Subalgebra.coe_units_zpow (w : Oˣ) (n : ℤ) :
    (((w ^ n : Oˣ) : O) : K) = ((w : O) : K) ^ n := by
  let F : Oˣ →* Kˣ := Units.map (Subalgebra.val O).toRingHom.toMonoidHom
  have hF : ∀ u : Oˣ, ((F u : Kˣ) : K) = ((u : O) : K) := fun _ => rfl
  rw [← hF, map_zpow, Units.val_zpow_eq_zpow_val, hF]

/-- **Units of norm one are the powers of `ε`.**  If every unit is `±ε ^ n` and `φ(ε) > 1`,
then a unit that is *positive* at the real place is exactly `ε ^ n`. -/
lemma exists_zpow_eq_of_embedding_pos {φ : K →+* ℂ} (hφ : IsReal φ) (ε u : Oˣ)
    (hεone : 1 < hφ.embedding ((ε : O) : K))
    (hgen : ∀ w : Oˣ, ∃ n : ℤ, w = ε ^ n ∨ w = -ε ^ n)
    (hu : 0 < hφ.embedding ((u : O) : K)) : ∃ n : ℤ, u = ε ^ n := by
  obtain ⟨n, hn | hn⟩ := hgen u
  · exact ⟨n, hn⟩
  · exfalso
    rw [hn, Units.val_neg, Subalgebra.coe_neg, map_neg, Subalgebra.coe_units_zpow,
      map_zpow₀] at hu
    have : 0 < hφ.embedding (ε : O) ^ n := zpow_pos (by linarith) n
    linarith

omit [NumberField K] in
/-- The exponent in `u = ε ^ n` is unique. -/
lemma zpow_left_injective_of_embedding_one_lt {φ : K →+* ℂ} (hφ : IsReal φ) (ε : Oˣ)
    (hεone : 1 < hφ.embedding ((ε : O) : K)) {m n : ℤ} (h : (ε : Oˣ) ^ m = ε ^ n) : m = n := by
  have hV : hφ.embedding (ε : O) ^ m = hφ.embedding (ε : O) ^ n := by
    rw [← map_zpow₀, ← map_zpow₀, ← Subalgebra.coe_units_zpow, ← Subalgebra.coe_units_zpow, h]
  exact (zpow_right_inj₀ (by linarith) (by linarith)).mp hV

/-- **From a Thue solution to a vanishing coordinate.**  If `F(x,y) = 1` then `x - yθ` is a
unit of norm one, hence `ε ^ n` for a unique `n`, and `mu (ε ^ n) = 0`. -/
theorem exists_zpow_eq_of_thue (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ)
    {O : Subalgebra ℤ K} {θ : K} (hθO : θ ∈ O) {a b c : ℤ}
    (hmin : minpoly ℚ θ = X ^ 3 + C (a : ℚ) * X ^ 2 + C (b : ℚ) * X + C (c : ℚ))
    (ε : Oˣ) (hεone : 1 < hφ.embedding ε)
    (hgen : ∀ w : Oˣ, ∃ n : ℤ, w = ε ^ n ∨ w = -ε ^ n)
    (mu : O →ₗ[ℤ] ℤ) (hmu1 : mu 1 = 0) (hmuθ : mu ⟨θ, hθO⟩ = 0)
    {x y : ℤ} (hF : x ^ 3 + a * x ^ 2 * y + b * x * y ^ 2 + c * y ^ 3 = 1) :
    ∃ n : ℤ, ((ε ^ n : Oˣ) : K) = x - y * θ ∧ mu (ε ^ n : Oˣ) = 0 := by
  have hθK : θ ^ 3 + a * θ ^ 2 + b * θ + c = 0 := by
    have h := minpoly.aeval ℚ θ
    rw [hmin] at h
    simp only [map_add, map_mul, map_pow, aeval_C, aeval_X, eq_ratCast] at h
    push_cast at h
    linear_combination h
  set θO : O := ⟨θ, hθO⟩ with hθOdef
  have hθOrel : θO ^ 3 + a * θO ^ 2 + b * θO + c = 0 := by
    apply Subtype.ext
    push_cast
    exact hθK
  set xu : Oˣ := (isUnit_intCast_sub_mul hθOrel hF).unit with hxudef
  have hxK : (xu : O) = x - y * θ := by
    rw [hxudef, IsUnit.unit_spec]
    push_cast
    ring
  have hN : Algebra.norm ℚ ((xu : O) : K) = 1 := by
    rw [hxK, norm_intCast_sub_mul hdeg hmin, hF]; norm_num
  have hx0 : ((xu : O) : K) ≠ 0 := fun h0 => by rw [h0] at hN; simp at hN
  obtain ⟨n, hn⟩ := exists_zpow_eq_of_embedding_pos hφ ε xu hεone hgen
    (embedding_pos_of_norm_eq_one hdeg σ φ hφ hσ hx0 hN)
  refine ⟨n, by rw [← hn, hxK], ?_⟩
  rw [← hn, hxudef, IsUnit.unit_spec,
    show (x - y * θO) = x • 1 - y • θO by simp [zsmul_eq_mul],
    map_sub, map_zsmul, map_zsmul, hmu1, hmuθ]
  simp

/-- **The coefficients of a Thue solution.**  For a basis `1, θ, …` of `O` with first two
coordinates `nu`, `la`: `a = nu (ε ^ n)` and `b = - la (ε ^ n)`. -/
theorem exists_zpow_eq_coeffs_of_thue (hdeg : Module.finrank ℚ K = 3) (σ φ : K →+* ℂ)
    (hφ : IsReal φ) (hσ : ¬ IsReal σ)
    {O : Subalgebra ℤ K} {θ : K} (hθO : θ ∈ O) {c₁ c₂ c₃ : ℤ}
    (hmin : minpoly ℚ θ = X ^ 3 + C (c₁ : ℚ) * X ^ 2 + C (c₂ : ℚ) * X + C (c₃ : ℚ))
    (ε : Oˣ) (hεone : 1 < hφ.embedding ((ε : O) : K))
    (hgen : ∀ w : Oˣ, ∃ n : ℤ, w = ε ^ n ∨ w = -ε ^ n)
    (mu : O →ₗ[ℤ] ℤ) (hmu1 : mu 1 = 0) (hmuθ : mu ⟨θ, hθO⟩ = 0)
    (nu : O →ₗ[ℤ] ℤ) (hnu1 : nu 1 = 1) (hnuθ : nu ⟨θ, hθO⟩ = 0)
    (la : O →ₗ[ℤ] ℤ) (hla1 : la 1 = 0) (hlaθ : la ⟨θ, hθO⟩ = 1)
    {a b : ℤ} (hF : a ^ 3 + c₁ * a ^ 2 * b + c₂ * a * b ^ 2 + c₃ * b ^ 3 = 1) :
    ∃ n : ℤ, mu ((ε ^ n : Oˣ) : O) = 0 ∧ a = nu ((ε ^ n : Oˣ) : O)
      ∧ b = - la ((ε ^ n : Oˣ) : O) := by
  obtain ⟨n, hxK, hmun⟩ :=
    exists_zpow_eq_of_thue hdeg σ φ hφ hσ hθO hmin ε hεone hgen mu hmu1 hmuθ hF
  have hO : ((ε ^ n : Oˣ) : O) = a • 1 - b • (⟨θ, hθO⟩ : O) := by
    apply Subtype.ext
    rw [hxK]
    push_cast [zsmul_eq_mul]
    ring
  refine ⟨n, hmun, ?_, ?_⟩ <;>
    rw [hO, map_sub, map_zsmul, map_zsmul] <;> simp [hnu1, hnuθ, hla1, hlaθ]

end Thue

/-! ## Section 2: the Skolem criterion

Pure algebra: `R` is any commutative ring, `mu` any `ℤ`-linear functional with `mu 1 = 0`,
and `ε` any unit.  `(S1)` is written `↑(ε ^ f) = p * δ + 1`. -/

section Skolem

variable {R : Type*} [CommRing R] (mu : R →ₗ[ℤ] ℤ)

/-! ### Two arithmetic lemmas on binomial coefficients -/

lemma add_two_le_three_pow {w : ℕ} (hw : 1 ≤ w) : w + 2 ≤ 3 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => norm_num
  | succ w hw ih =>
    have h1 := Nat.one_le_pow w 3 (by norm_num)
    calc w + 1 + 2 ≤ 3 ^ w + 2 * 3 ^ w := by omega
      _ = 3 ^ (w + 1) := by ring

/-- If `p ≥ 3` and `i = p ^ w * i' ≥ 2`, then `i - v_p(i) ≥ 2`,
written without truncated subtraction as `w + 2 ≤ i`. -/
lemma add_two_le_of_eq_pow_mul {p w i i' : ℕ} (hp3 : 3 ≤ p)
    (hi : i = p ^ w * i') (hi2 : 2 ≤ i) : w + 2 ≤ i := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · omega
  · calc w + 2 ≤ 3 ^ w := add_two_le_three_pow hw
      _ ≤ p ^ w := Nat.pow_le_pow_left hp3 w
      _ ≤ p ^ w * i' := Nat.le_mul_of_pos_right _ (by grind)
      _ = i := hi.symm

/-- `v_p(k) ≤ v_p(C(k,i)) + v_p(i)`, in divisibility form.
The input is the identity `C(k,i) * i = k * C(k-1,i-1)`. -/
lemma pow_dvd_choose_mul_pow {p : ℕ} (hp : p.Prime) {v k k' w i i' : ℕ}
    (hk : k = p ^ v * k') (hi : i = p ^ w * i') (hi'p : ¬ p ∣ i')
    (hi0 : 0 < i) (hik : i ≤ k) : p ^ v ∣ k.choose i * p ^ w := by
  have hdvd : k ∣ k.choose i * i := by
    refine ⟨(k - 1).choose (i - 1), ?_⟩
    have h := Nat.add_one_mul_choose_eq (k - 1) (i - 1)
    rw [show k - 1 + 1 = k by omega, show i - 1 + 1 = i by omega] at h
    omega
  have h1 : p ^ v ∣ k.choose i * p ^ w * i' :=
    dvd_trans ⟨k', hk⟩ (hdvd.trans (by rw [hi]; ring_nf; exact dvd_refl _))
  exact ((hp.coprime_iff_not_dvd.mpr hi'p).pow_left v).dvd_of_dvd_mul_right h1

/-- The tail terms of the binomial expansion: for `2 ≤ i ≤ k` and `k = p ^ v * k'`,
`p ^ (v + 2)` divides `C(k,i) * p ^ i`. -/
lemma pow_dvd_choose_mul_pow_int {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {v k k' : ℕ}
    (hk : k = p ^ v * k') {i : ℕ} (hi2 : 2 ≤ i) (hik : i ≤ k) :
    (p : ℤ) ^ (v + 2) ∣ (k.choose i : ℤ) * (p : ℤ) ^ i := by
  obtain ⟨w, i', hi'p, hi⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := i) (by omega) p hp.ne_one
  have hwi : w + 2 ≤ i := add_two_le_of_eq_pow_mul hp3 hi hi2
  obtain ⟨c, hc⟩ := pow_dvd_choose_mul_pow hp hk hi hi'p (by omega) hik
  have hcast : ((k.choose i * p ^ w : ℕ) : ℤ) = ((p ^ v * c : ℕ) : ℤ) := by rw [hc]
  push_cast at hcast
  have hsplit : (p : ℤ) ^ i = (p : ℤ) ^ w * (p : ℤ) ^ 2 * (p : ℤ) ^ (i - w - 2) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  refine ⟨c * (p : ℤ) ^ (i - w - 2), ?_⟩
  calc (k.choose i : ℤ) * (p : ℤ) ^ i
      = (k.choose i : ℤ) * (p : ℤ) ^ w * ((p : ℤ) ^ 2 * (p : ℤ) ^ (i - w - 2)) := by
        rw [hsplit]; ring
    _ = (p : ℤ) ^ v * c * ((p : ℤ) ^ 2 * (p : ℤ) ^ (i - w - 2)) := by rw [hcast]
    _ = p ^ (v + 2) * (c * p ^ (i - w - 2)) := by rw [pow_add]; ring

/-! ### The binomial expansion, and the dominant linear term -/

/-- The finite binomial expansion of `mu ((p * δ + 1) ^ k)`. -/
lemma mu_pow_expand (p : ℕ) (δ : R) (k : ℕ) :
    mu ((p * δ + 1) ^ k) = ∑ i ∈ range (k + 1), (k.choose i : ℤ) * (p : ℤ) ^ i * mu (δ ^ i) := by
  rw [add_pow, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hterm : ((p : R) * δ) ^ i * 1 ^ (k - i) * (k.choose i : R)
      = ((k.choose i : ℤ) * (p : ℤ) ^ i) • δ ^ i := by
    simp only [one_pow, mul_one, mul_pow, zsmul_eq_mul]
    push_cast
    ring
  rw [hterm, map_zsmul, smul_eq_mul]

/-- **The dominant linear term.**  For `k = p ^ v * k'` with `p ∤ k'`, the `p`-adic valuation
of `mu ((p δ + 1) ^ k) - mu 1` is exactly `v + 1`. -/
lemma exists_eq_pow_mul_not_dvd {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {δ : R} (hS2 : ¬ (p : ℤ) ∣ mu δ) {v k' : ℕ} (hk'p : ¬ p ∣ k') (hk'0 : 0 < k') :
    ∃ m : ℤ, mu ((p * δ + 1) ^ (p ^ v * k')) - mu 1 = (p : ℤ) ^ (v + 1) * m ∧
      ¬ (p : ℤ) ∣ m := by
  set k := p ^ v * k' with hk
  have hk0 : 0 < k := Nat.mul_pos (pow_pos hp.pos v) hk'0
  have hsplit : ∑ i ∈ range (k + 1), k.choose i * p ^ i * mu (δ ^ i)
      = mu 1 + k * p * mu δ
        + ∑ i ∈ Ico 2 (k + 1), k.choose i * p ^ i * mu (δ ^ i) := by
    rw [range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < k + 1)]
    simp only [Nat.choose_zero_right, Nat.choose_one_right, pow_zero, pow_one]
    ring
  obtain ⟨s, hs⟩ : (p : ℤ) ^ (v + 2) ∣
      ∑ i ∈ Ico 2 (k + 1), (k.choose i : ℤ) * (p : ℤ) ^ i * mu (δ ^ i) :=
    Finset.dvd_sum fun i hi => by
      rw [Finset.mem_Ico] at hi
      exact (pow_dvd_choose_mul_pow_int hp hp3 hk hi.1 (by omega)).mul_right _
  refine ⟨k' * mu δ + p * s, by rw [mu_pow_expand, hsplit, hs, hk]; push_cast; ring, fun hdvd => ?_⟩
  have h1 : (p : ℤ) ∣ (k' : ℤ) * mu δ := by
    simpa using dvd_sub hdvd (dvd_mul_right (p : ℤ) s)
  rcases (Nat.prime_iff_prime_int.mp hp).dvd_mul.mp h1 with h | h
  exacts [hk'p (by exact_mod_cast h), hS2 h]

/-- `mu ((p δ + 1) ^ k) ≠ mu 1` for every `k ≥ 1`. -/
lemma mu_pow_ne_mu_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {δ : R} (hS2 : ¬ (p : ℤ) ∣ mu δ) {k : ℕ} (hk : 0 < k) :
    mu ((p * δ + 1) ^ k) ≠ mu 1 := by
  obtain ⟨v, k', hk'p, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := k) (by omega) p hp.ne_one
  have hk'0 : 0 < k' := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  obtain ⟨m, hm, hmp⟩ := exists_eq_pow_mul_not_dvd mu hp hp3 hS2 (v := v) hk'p hk'0
  intro hcon
  rw [hcon, sub_self] at hm
  rcases mul_eq_zero.mp hm.symm with h | h
  · exact absurd h (by positivity)
  · exact hmp (h ▸ dvd_zero _)

/-- If `U = 1 + p δ` is a unit then every integer power of `U` is again `1` mod `p`. -/
lemma exists_zpow_eq_pow_mul_add_one {p : ℕ} {U : Rˣ} {δ : R} (hU : (↑U : R) = p * δ + 1)
    (m : ℤ) : ∃ z : R, (↑(U ^ m) : R) = p * z + 1 := by
  have huv : (↑U : R) * ↑U⁻¹ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hU] at huv
  obtain ⟨δ', hδ'⟩ : ∃ δ' : R, ↑U⁻¹ = p * δ' + 1 :=
    ⟨-(δ * ↑U⁻¹), by linear_combination huv⟩
  refine Int.induction_on m ⟨0, by simp⟩ (fun n ⟨z, hz⟩ => ⟨z + δ + p * z * δ, ?_⟩)
    (fun n ⟨z, hz⟩ => ⟨z + δ' + p * z * δ', ?_⟩)
  · rw [zpow_add_one, Units.val_mul, hz, hU]; ring
  · rw [show -(n : ℤ) - 1 = -(n : ℤ) + -1 by ring, zpow_add, zpow_neg_one, Units.val_mul, hz,
      hδ']
    ring

/-- The dominant-term lemma at every nonzero integer exponent. -/
lemma mu_zpow_ne_mu_one {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p)
    {δ : R} (hS2 : ¬ (p : ℤ) ∣ mu δ) (U : Rˣ) (hU : (↑U : R) = p * δ + 1)
    {k : ℤ} (hk : k ≠ 0) : mu ↑(U ^ k) ≠ mu 1 := by
  have huv : (↑U : R) * ↑U⁻¹ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [hU] at huv
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · set δ' : R := -(δ * ↑U⁻¹) with hδ'
    have hUinv : ↑U⁻¹ = p * δ' + 1 := by rw [hδ']; linear_combination huv
    have hS2' : ¬ (p : ℤ) ∣ mu δ' := fun hd => hS2 <| by
      have hsum : mu δ' + mu δ = p * mu (δ ^ 2 * ↑U⁻¹) := by
        rw [← map_add, show δ' + δ = p * (δ ^ 2 * ↑U⁻¹) by
          rw [hδ']; linear_combination (-δ) * huv,
          show ((p : R) * (δ ^ 2 * ↑U⁻¹)) = (p : ℤ) • (δ ^ 2 * (↑U⁻¹ : R)) by
            rw [zsmul_eq_mul]; push_cast; ring, map_zsmul, smul_eq_mul]
      exact (dvd_add_right hd).mp ⟨_, hsum⟩
    obtain ⟨j, hj0, rfl⟩ : ∃ j : ℕ, 0 < j ∧ k = -j := ⟨(-k).toNat, by omega, by omega⟩
    rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val, hUinv]
    exact mu_pow_ne_mu_one mu hp hp3 hS2' hj0
  · obtain ⟨j, hj0, rfl⟩ : ∃ j : ℕ, 0 < j ∧ k = j := ⟨k.toNat, by omega, by omega⟩
    rw [zpow_natCast, Units.val_pow_eq_pow_val, hU]
    exact mu_pow_ne_mu_one mu hp hp3 hS2 hj0

/-! ### The congruence sieve -/

/-- **The congruence sieve.**  If `m % f = n % f` then
`p ∣ mu (ε ^ m * z) - mu (ε ^ n * z)` for every `z`. -/
lemma dvd_mu_zpow_mul_sub_of_emod_eq {p : ℕ} (ε : Rˣ) {f : ℕ} {δ : R}
    (hS1 : (↑(ε ^ f) : R) = p * δ + 1) {m n : ℤ} (hmn : m % (f : ℤ) = n % (f : ℤ)) (z : R) :
    (p : ℤ) ∣ mu (↑(ε ^ m) * z) - mu (↑(ε ^ n) * z) := by
  obtain ⟨c, hc⟩ : (f : ℤ) ∣ m - n := Int.ModEq.dvd hmn.symm
  obtain ⟨w, hw⟩ := exists_zpow_eq_pow_mul_add_one hS1 c
  have hval : ↑(ε ^ m) * z - ↑(ε ^ n) * z = p * (↑(ε ^ n) * z * w) := by
    have hsplit : ε ^ m = ε ^ n * (ε ^ f) ^ c := by
      rw [← zpow_natCast ε f, ← zpow_mul, ← zpow_add, show n + f * c = m by omega]
    rw [hsplit, Units.val_mul, hw]
    ring
  refine ⟨mu (↑(ε ^ n) * z * w), ?_⟩
  have hzsmul : (p : R) * (↑(ε ^ n) * z * w) = (p : ℤ) • (↑(ε ^ n) * z * w) := by
    rw [zsmul_eq_mul]
    push_cast
    ring
  rw [← map_sub, hval, hzsmul, map_zsmul, smul_eq_mul]

/-- **The congruence sieve.**  `p ∣ mu (ε ^ n) - mu (ε ^ (n % f))`. -/
lemma dvd_mu_zpow_sub_mu_zpow_emod {p : ℕ} (ε : Rˣ) {f : ℕ} {δ : R}
    (hS1 : (↑(ε ^ f) : R) = p * δ + 1) (n : ℤ) :
    (p : ℤ) ∣ mu ↑(ε ^ n) - mu ↑(ε ^ (n % f)) := by
  simpa using dvd_mu_zpow_mul_sub_of_emod_eq mu ε hS1
    (Int.emod_emod_of_dvd n (dvd_refl (f : ℤ))).symm 1

/-- **Re-centering.**  `muRecenter mu η : z ↦ mu (η * z)`.  Taking `η = ε ^ m` puts `m` in the
role `0` plays in `skolem_zpow_eq_zero_iff`. -/
def muRecenter (η : R) : R →ₗ[ℤ] ℤ := mu ∘ₗ LinearMap.mulLeft ℤ η

@[simp] lemma muRecenter_apply (η z : R) : muRecenter mu η z = mu (η * z) :=
  rfl

@[simp] lemma muRecenter_one (η : R) : muRecenter mu η 1 = mu η := by
  rw [muRecenter_apply, mul_one]

/-! ### What a single residue class can contain -/

/-- **The residue class of `r` is empty.**  If `p ∤ mu (ε ^ r)` then no `n` with
`n % f = r % f` satisfies `mu (ε ^ n) = 0`. -/
theorem mu_zpow_ne_zero_of_not_dvd (ε : Rˣ) {p f : ℕ} {δ : R}
    (hS1 : (↑(ε ^ f) : R) = p * δ + 1)
    {r : ℤ} (hr : ¬ (p : ℤ) ∣ mu ↑(ε ^ r)) {n : ℤ} (hn : n % (f : ℤ) = r % (f : ℤ)) :
    mu ↑(ε ^ n) ≠ 0 := fun h => by
  have hd := dvd_mu_zpow_mul_sub_of_emod_eq mu ε hS1 hn 1
  rw [mul_one, mul_one, h, zero_sub, dvd_neg] at hd
  exact hr hd

/-- **At most one solution per residue class.**  If `p ∤ mu (ε ^ r * δ)` then the class of `r`
modulo `f` contains at most one `n` with `mu (ε ^ n) = 0`. -/
theorem eq_of_mu_zpow_eq_zero_of_emod_eq (ε : Rˣ) {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (δ : R) (hS1 : (↑(ε ^ f) : R) = p * δ + 1)
    {r : ℤ} (hW : ¬ (p : ℤ) ∣ mu (↑(ε ^ r) * δ))
    {n₁ n₂ : ℤ} (h₁ : n₁ % (f : ℤ) = r % (f : ℤ)) (h₂ : n₂ % (f : ℤ) = r % (f : ℤ))
    (hz₁ : mu ↑(ε ^ n₁) = 0) (hz₂ : mu ↑(ε ^ n₂) = 0) : n₁ = n₂ := by
  by_contra hne
  obtain ⟨k, hk⟩ : (f : ℤ) ∣ n₂ - n₁ := Int.ModEq.dvd (h₁.trans h₂.symm)
  refine mu_zpow_ne_mu_one (muRecenter mu ↑(ε ^ n₁)) hp hp3 ?_ (ε ^ f) hS1 (k := k)
    (by rintro rfl; rw [mul_zero] at hk; omega) ?_
  · intro hd
    refine hW ?_
    exact (dvd_sub_right hd).mp (dvd_mu_zpow_mul_sub_of_emod_eq mu ε hS1 h₁ δ)
  · rw [muRecenter_one, hz₁, muRecenter_apply, ← Units.val_mul, ← zpow_natCast ε f, ← zpow_mul,
      ← zpow_add, show n₁ + f * k = n₂ by omega]
    exact hz₂

/-- **The residue class of `r` contains exactly `r`.**  If moreover `r` is a solution, then
`mu (ε ^ n) = 0` holds on that class precisely at `n = r`. -/
theorem mu_zpow_eq_zero_iff_of_not_dvd_mul (ε : Rˣ) {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (δ : R) (hS1 : (↑(ε ^ f) : R) = p * δ + 1)
    {s : ℤ} (hr : mu ↑(ε ^ s) = 0) (hW : ¬ (p : ℤ) ∣ mu (↑(ε ^ s) * δ))
    {n : ℤ} (hn : n % (f : ℤ) = s % (f : ℤ)) : mu ↑(ε ^ n) = 0 ↔ n = s :=
  ⟨fun h => eq_of_mu_zpow_eq_zero_of_emod_eq mu ε hp hp3 δ hS1 hW hn rfl h hr,
   fun h => h ▸ hr⟩

/-- **Skolem with several surviving classes.**  If the sieve kills every class not represented
in `S` and every represented class separates, then `S` is the complete solution set. -/
theorem skolem_zpow_eq_zero_iff_mem (ε : Rˣ) {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hf : 0 < f) (δ : R)
    (hS1 : ↑(ε ^ f) = p * δ + 1) (S : List ℤ)
    (hS3 : ∀ r : ℕ, r < f → (∀ s ∈ S, s % f ≠ r) →
      ¬ (p : ℤ) ∣ mu (ε ^ r))
    (hsol : ∀ s ∈ S, mu ↑(ε ^ s) = 0)
    (hW : ∀ s ∈ S, ¬ ↑p ∣ mu (ε ^ (s % f).toNat * δ))
    (n : ℤ) : mu ↑(ε ^ n) = 0 ↔ n ∈ S := by
  have hf' : (0 : ℤ) < f := by exact_mod_cast hf
  have hcast : ∀ k : ℤ, 0 ≤ k → (↑(ε ^ k) : R) = (ε : R) ^ k.toNat := fun k hk => by
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast ε, Int.toNat_of_nonneg hk]
  refine ⟨fun hn => ?_, fun hn => hsol n hn⟩
  have hnn := Int.emod_nonneg n hf'.ne'
  have hlt := Int.emod_lt_of_pos n hf'
  have hdvd : (p : ℤ) ∣ mu ((ε : R) ^ (n % (f : ℤ)).toNat) := by
    have h := dvd_mu_zpow_sub_mu_zpow_emod mu ε hS1 n
    rw [hn, zero_sub, dvd_neg, hcast _ hnn] at h
    exact h
  obtain ⟨s, hsS, hsr⟩ : ∃ s ∈ S, s % f = (n % f).toNat :=
    not_forall_not.mp fun hno => hS3 _ (by omega)
      (fun s hs hc => hno s ⟨hs, hc⟩) hdvd
  have hmod : ∀ k : ℤ, k % f = s % f → k % f = (s % f) % f :=
    fun k hk => by rw [hk, Int.emod_emod_of_dvd _ dvd_rfl]
  refine (eq_of_mu_zpow_eq_zero_of_emod_eq mu ε hp hp3 δ hS1 (r := s % f) ?_
    (hmod n (by omega)) (hmod s rfl) hn (hsol s hsS)) ▸ hsS
  rw [hcast _ (Int.emod_nonneg s hf'.ne')]
  exact hW s hsS

/-- **The Skolem criterion.**  The case `S = [0]` of `skolem_zpow_eq_zero_iff_mem`: the
certificate is `(S1)` `ε ^ f = 1 + p δ`, `(S2)` `p ∤ mu δ`, and `(S3)` `p ∤ mu (ε ^ r)` for
`0 < r < f`. -/
theorem skolem_zpow_eq_zero_iff (hmu1 : mu 1 = 0) (ε : Rˣ) {p f : ℕ}
    (hp : p.Prime) (hp3 : 3 ≤ p) (hf : 0 < f) (δ : R)
    (hS1 : (↑(ε ^ f) : R) = p * δ + 1)
    (hS2 : ¬ (p : ℤ) ∣ mu δ)
    (hS3 : ∀ r : ℕ, 0 < r → r < f → ¬ (p : ℤ) ∣ mu ↑(ε ^ r))
    (n : ℤ) : mu ↑(ε ^ n) = 0 ↔ n = 0 := by
  have h := skolem_zpow_eq_zero_iff_mem mu ε hp hp3 hf δ hS1 [0]
    (fun r hr hne => hS3 r (by
        have := hne 0 (by simp)
        rw [Int.zero_emod] at this
        omega) hr)
    (fun s hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs; simpa using hmu1)
    (fun s hs => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      subst hs
      simpa using hS2)
    n
  simpa using h


end Skolem
