import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.ClassGroup
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Data.Nat.Squarefree

/-!
# Mordell equations by class-group descent to Thue equations

## AI use
This file was largely generated using Claude Code with Opus 5, after multiples rounds of
prompting. The main statements of the main results and the
high-level proof strategies were specified by me.
We also carried out some polishing afterwards.

## Main results

### The `ℤ`-level input

* `not_dvd_of_dvd_x`, `not_dvd_of_dvd_y` : for a Mordell solution with `n` squarefree, no
  prime divides both `n` and one of `x`, `y`.
* `not_two_dvd_of_mordell` : `x` is odd when `n ≡ 2, 3 [ZMOD 4]`.
* `isCoprime_two_mul` : `x` is prime to `2 n` -- the Bézout relation the descent
  consumes.
* `even_of_odd_norm` : if the norm form `A ^ 2 + A * B - m * B ^ 2` is odd and `m` is even,
  then `B` is even.  With `m = (n - 1) / 4` this says that an element of odd norm lies in
  `ℤ[√n]`, which is what forces in our case the Thue equations to have right-hand side `1`.

### The descent, in general

* `exists_unit_mul_pow_rep` : a coprime factor of a `k`-th power is a `k`-th power, up to a
  unit and a multiplier `α i` drawn from the family, whose classes are asked to exhaust the
  `k`-torsion of `Cl R`.
* `exists_unit_mul_cube_of_mordell_rep` : the descent for `y ^ 2 = x ^ 3 + n`, giving
  `α i * (y + θ) = u δ ^ 3` with `δ` integral.  Stated with `n`, `x`, `y` in `R`.
* `exists_unit_mul_cube_of_even_rep` : the branch `x` even, only possible when
  `n ≡ 1 [ZMOD 8]`.  The element factorisation `π π' = 2` stays a hypothesis.
* `exists_unit_mul_cube_of_mordell_rep_int`, `exists_unit_mul_cube_of_even_rep_int` : the two
  above specialised to an integral Mordell equation.

### The class-group input

* `exists_eq_mk0_pow_of_cyclic_three` : when every class is a power of `[A]` and `A ^ 3` is
  principal, every class is `[A ^ j]` for some `j < 3` ;
  `exists_mul_eq_span_of_covers` converts such a covering into the
  statement about ideals that the proof consumes.

### The case `3 ∤ h`

* `exists_unit_mul_pow`, `exists_unit_mul_cube_of_mordell`, `exists_unit_mul_cube_of_even` :
  the trivial-family corollaries, in which the multiplier disappears.  The bridge is
  `eq_mk0_one_of_pow_eq_one`: a class killed by `k` is trivial as soon as `k` is prime to the
  class number.
-/

namespace Mordell

variable {x y n : ℤ}

/-! ### The `ℤ`-level input -/

/-- No prime divides both `x` and a squarefree `n`. -/
theorem not_dvd_of_dvd_x (hn : Squarefree n) (h : y ^ 2 = x ^ 3 + n)
    {q : ℤ} (hq : Prime q) (hqx : q ∣ x) : ¬ q ∣ n := by
  intro hqn
  have hqy : q ∣ y := by
    refine hq.dvd_of_dvd_pow (n := 2) ?_
    rw [h]
    exact dvd_add (dvd_pow hqx three_ne_zero) hqn
  have hx3 : q ^ 2 ∣ x ^ 3 := (pow_dvd_pow q (by norm_num)).trans (pow_dvd_pow_of_dvd hqx 3)
  have hn' : n = y ^ 2 - x ^ 3 := by linarith
  refine hq.not_unit (hn q ?_)
  rw [← sq, hn']
  exact dvd_sub (pow_dvd_pow_of_dvd hqy 2) hx3

/-- No prime divides both `y` and a squarefree `n`. -/
theorem not_dvd_of_dvd_y (hn : Squarefree n) (h : y ^ 2 = x ^ 3 + n)
    {q : ℤ} (hq : Prime q) (hqy : q ∣ y) : ¬ q ∣ n := by
  intro hqn
  refine not_dvd_of_dvd_x hn h hq (hq.dvd_of_dvd_pow (n := 3) ?_) hqn
  have : x ^ 3 = y ^ 2 - n := by linarith
  rw [this]
  exact dvd_sub (dvd_pow hqy two_ne_zero) hqn

/-- `x` is odd when `n ≡ 2, 3 [ZMOD 4]`. -/
theorem not_two_dvd_of_mordell (hn : (n : ZMod 4) = 2 ∨ (n : ZMod 4) = 3)
    (h : y ^ 2 = x ^ 3 + n) : ¬ 2 ∣ x := by
  have key : ∀ Y K : ZMod 4, Y ^ 2 ≠ (2 * K) ^ 3 + 2 ∧ Y ^ 2 ≠ (2 * K) ^ 3 + 3 := by decide
  rintro ⟨k, rfl⟩
  have hz := congrArg (fun z : ℤ => (z : ZMod 4)) h
  push_cast at hz
  rcases hn with hn | hn <;> rw [hn] at hz
  · exact (key _ _).1 hz
  · exact (key _ _).2 hz

/-- `x` is prime to `2 n`: to `2` because it is odd, to `n` by `not_dvd_of_dvd_x`. -/
theorem isCoprime_two_mul (hn : Squarefree n) (h : y ^ 2 = x ^ 3 + n)
    (h2 : ¬ 2 ∣ x) : IsCoprime x (2 * n) := by
  refine isCoprime_of_prime_dvd (fun h0 => h2 (h0.1 ▸ dvd_zero 2)) fun q hq hqx hqN => ?_
  rcases hq.dvd_mul.mp hqN with hq2 | hqn
  · exact h2 (((hq.associated_of_dvd Int.prime_two hq2).symm.dvd).trans hqx)
  · exact not_dvd_of_dvd_x hn h hq hqx hqn

/-- If `A ^ 2 + A * B - m * B ^ 2` is odd and `m` is even then `B` is even.  With
`m = (n - 1) / 4`: an element of `ℤ[(1+√n)/2]` of odd norm lies in `ℤ[√n]`. -/
theorem even_of_odd_norm {m A B : ℤ} (hm : Even m) (h : Odd (A ^ 2 + A * B - m * B ^ 2)) :
    Even B := by
  by_contra hB
  rw [Int.not_even_iff_odd] at hB
  exact (Int.not_even_iff_odd.mpr h) (by simp [parity_simps, hm, hB])

/-- Cubing is injective on `ℤ`. -/
theorem cube_inj {u v : ℤ} (h : u ^ 3 = v ^ 3) : u = v :=
  (Odd.strictMono_pow (by decide : Odd 3)).injective h

section Descent

open nonZeroDivisors

/-! ### Coprimality and cube extraction -/

/-- Coprimality of `α` and `β` from a Bézout relation between `α * β` and `(α - β) ^ 2`. -/
theorem isCoprime_of_bezout {R : Type*} [CommRing R] {α β m n : R}
    (h : m * (α * β) + n * (α - β) ^ 2 = 1) : IsCoprime α β :=
  ⟨m * β + n * α - 2 * n * β, n * β, by linear_combination h⟩

variable {R : Type*} [CommRing R] [IsDomain R] [IsDedekindDomain R]

omit [IsDomain R] in
/-- Coprime factors of a `k`-th power are `k`-th powers, as ideals of a Dedekind domain. -/
theorem Ideal.eq_pow_of_isCoprime_of_mul_eq_pow {I J C : Ideal R} {k : ℕ}
    (hIJ : IsCoprime I J) (h : I * J = C ^ k) : ∃ D : Ideal R, I = D ^ k :=
  exists_eq_pow_of_mul_eq_pow (Ideal.isUnit_iff.mpr (Ideal.isCoprime_iff_sup_eq.mp hIJ)) h

/-! ### The class-group input -/

/-- An ideal of trivial class is `Ideal.span {δ}` with `δ` in the ring. -/
lemma exists_gen_of_mk0_eq_one {A : nonZeroDivisors (Ideal R)} (h : ClassGroup.mk0 A = 1) :
    ∃ δ, (A : Ideal R) = Ideal.span {δ} :=
  ((ClassGroup.mk0_eq_one_iff A.2).mp h).principal

/-- If every class killed by `k` is some `[A i]`, then every `I` with `I ^ k` principal has
`I * A i = (δ)`, `δ` integral.  Applied to `[I]⁻¹`: the `k`-torsion is a subgroup. -/
lemma exists_mul_eq_span_of_covers {k : ℕ} {ι : Type*} {A : ι → Ideal R}
    (hA0 : ∀ i, A i ∈ nonZeroDivisors (Ideal R))
    (hcov : ∀ C : ClassGroup R, C ^ k = 1 → ∃ i, C = ClassGroup.mk0 ⟨A i, hA0 i⟩)
    (I : nonZeroDivisors (Ideal R)) (hI : ((I : Ideal R) ^ k).IsPrincipal) :
    ∃ (i : ι) (δ : R), (I : Ideal R) * A i = Ideal.span {δ} := by
  have hIk : ClassGroup.mk0 I ^ k = 1 := by
    rw [← map_pow]
    exact (ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ I.2 k)).mpr hI
  obtain ⟨i, hi⟩ := hcov (ClassGroup.mk0 I)⁻¹ (by rw [inv_pow, hIk, inv_one])
  obtain ⟨δ, hδ⟩ := exists_gen_of_mk0_eq_one (A := I * ⟨A i, hA0 i⟩)
    (by rw [map_mul, ← hi, mul_inv_cancel])
  exact ⟨i, δ, hδ⟩

/-- If every class is a power of `[A]` and `A ^ 3` is principal, every class is `[1]`, `[A]` or
`[A ^ 2]`.  `A` comes as ideal plus membership: `ClassGroup.mk0` of an opaque element of
`(Ideal R)⁰` forces an eta-expansion the unifier chokes on. -/
theorem exists_eq_mk0_pow_of_cyclic_three [Finite (ClassGroup R)]
    {A : Ideal R} (hA : A ∈ nonZeroDivisors (Ideal R)) (hA3 : (A ^ 3).IsPrincipal)
    (hgen : ∀ C : ClassGroup R, ∃ k : ℕ, C = ClassGroup.mk0 ⟨A, hA⟩ ^ k)
    (C : ClassGroup R) (_hC : C ^ 3 = 1) :
    ∃ j : Fin 3, C = ClassGroup.mk0 ⟨A ^ (j : ℕ), Submonoid.pow_mem _ hA _⟩ := by
  have hpow : ClassGroup.mk0 ⟨A, hA⟩ ^ 3 = 1 := by
    rw [← map_pow]
    exact (ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ hA 3)).mpr hA3
  obtain ⟨k, hk⟩ := hgen C
  refine ⟨⟨k % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
  have hmod : ClassGroup.mk0 ⟨A ^ (k % 3), Submonoid.pow_mem _ hA _⟩
      = ClassGroup.mk0 ⟨A, hA⟩ ^ (k % 3) := by
    rw [← map_pow]
    rfl
  rw [hmod, hk]
  conv_lhs => rw [← Nat.div_add_mod k 3]
  rw [pow_add, pow_mul, hpow, one_pow, one_mul]

/-- The trivial family `A = 1` covers the `k`-torsion when `k` is prime to the class number. -/
lemma eq_mk0_one_of_pow_eq_one [Finite (ClassGroup R)] {k : ℕ}
    (hk : Nat.Coprime k (Nat.card (ClassGroup R))) (C : ClassGroup R) (hC : C ^ k = 1) :
    ∃ _ : Unit, C = ClassGroup.mk0 ⟨1, one_mem _⟩ := by
  have hone : ClassGroup.mk0 (⟨1, one_mem _⟩ : nonZeroDivisors (Ideal R)) = 1 :=
    (ClassGroup.mk0_eq_one_iff (one_mem _)).mpr ⟨1, by simp⟩
  rw [hone]
  exact ⟨(), (powCoprime hk.symm).injective (by simpa using hC)⟩

/-! ### The descent step, with representatives -/

/-- **The descent step.**  If `a * b = z ^ k` with `a`, `b` coprime then `(a) = D ^ k`, and a
family `(A i, α i)` with `A i ^ k = (α i)` covering the `k`-torsion principalises `D`, giving
`α i * a = u δ ^ k` with `δ` integral.  Any `k ≠ 0`; finiteness of `Cl R`, where needed, sits
inside `hcov`. -/
theorem exists_unit_mul_pow_rep {k : ℕ} (hk : k ≠ 0) {a b z : R} (ha : a ≠ 0)
    (hcop : IsCoprime a b) (h : a * b = z ^ k)
    {ι : Type*} {A : ι → Ideal R} {α : ι → R}
    (hA0 : ∀ i, A i ∈ nonZeroDivisors (Ideal R)) (hA : ∀ i, A i ^ k = Ideal.span {α i})
    (hcov : ∀ C : ClassGroup R, C ^ k = 1 → ∃ i, C = ClassGroup.mk0 ⟨A i, hA0 i⟩) :
    ∃ (i : ι) (u : Rˣ) (δ : R), α i * a = u * δ ^ k := by
  have hspan : Ideal.span {a} * Ideal.span {b} = Ideal.span {z} ^ k := by
    rw [Ideal.span_singleton_mul_span_singleton, Ideal.span_singleton_pow, h]
  obtain ⟨D, hD⟩ := Ideal.eq_pow_of_isCoprime_of_mul_eq_pow
    ((Ideal.isCoprime_span_singleton_iff a b).mpr hcop) hspan
  have hD0 : D ≠ ⊥ := by
    rintro rfl
    rw [← Submodule.zero_eq_bot, zero_pow hk, Submodule.zero_eq_bot] at hD
    exact ha (Ideal.span_singleton_eq_bot.mp hD)
  obtain ⟨i, δ, hδ⟩ :=
    exists_mul_eq_span_of_covers hA0 hcov ⟨D, mem_nonZeroDivisors_of_ne_zero hD0⟩ ⟨_, hD.symm⟩
  refine ⟨i, ?_⟩
  have hpow : Ideal.span {α i * a} = Ideal.span {δ ^ k} := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← hA i, hD, mul_comm, ← mul_pow,
      ← Ideal.span_singleton_pow]
    exact congrArg (· ^ k) hδ
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hpow
  exact ⟨u⁻¹, δ, by rw [← hu, mul_comm _ (u : R), ← mul_assoc, Units.inv_mul, one_mul]⟩

/-! ### The descent for Mordell equations -/

/-- **The descent.**  `(y + θ)` is a cube `D ^ 3` as an ideal, and a family covering the
`3`-torsion gives `α i * (y + θ) = u δ ^ 3` with `δ` integral.  One *multiplies* by `A i`:
dividing by a representative would put `δ` in the fraction field only.  `n`, `x`, `y` range
over `R`. -/
theorem exists_unit_mul_cube_of_mordell_rep {n θ x y : R} (hθ : θ ^ 2 = n)
    (h : y ^ 2 = x ^ 3 + n) (hbez : IsCoprime x (2 * n)) (hne : y + θ ≠ 0)
    {ι : Type*} {A : ι → Ideal R} {α : ι → R}
    (hA0 : ∀ i, A i ∈ nonZeroDivisors (Ideal R)) (hA : ∀ i, A i ^ 3 = Ideal.span {α i})
    (hcov : ∀ C : ClassGroup R, C ^ 3 = 1 → ∃ i, C = ClassGroup.mk0 ⟨A i, hA0 i⟩) :
    ∃ (i : ι) (u : Rˣ) (δ : R), α i * (y + θ) = u * δ ^ 3 := by
  have hprod : (y + θ) * (y - θ) = x ^ 3 := by linear_combination h - hθ
  have hbez3 : IsCoprime (x ^ 3) (4 * n) := by
    have h2 : IsCoprime x 2 := hbez.of_mul_right_left
    have h22 : 4 * n = 2 * 2 * n := by ring
    rw [h22]
    exact ((h2.mul_right h2).mul_right hbez.of_mul_right_right).pow_left
  obtain ⟨m, k, hmk⟩ := hbez3
  have hcop : IsCoprime (y + θ) (y - θ) := by
    refine isCoprime_of_bezout (m := m) (n := k) ?_
    rw [hprod]
    linear_combination hmk + 4 * k * hθ
  exact exists_unit_mul_pow_rep three_ne_zero hne hcop hprod hA0 hA hcov

/-- `exists_unit_mul_cube_of_mordell_rep` with `n`, `x`, `y` in `ℤ`. -/
theorem exists_unit_mul_cube_of_mordell_rep_int
    {n : ℤ} {θ : R} (hθ : θ ^ 2 = (n : R))
    {x y : ℤ} (h : y ^ 2 = x ^ 3 + n)
    (hbez : IsCoprime x (2 * n))
    (hne : ((y : R) + θ) ≠ 0)
    {ι : Type*} {A : ι → Ideal R} {α : ι → R}
    (hA0 : ∀ i, A i ∈ nonZeroDivisors (Ideal R)) (hA : ∀ i, A i ^ 3 = Ideal.span {α i})
    (hcov : ∀ C : ClassGroup R, C ^ 3 = 1 → ∃ i, C = ClassGroup.mk0 ⟨A i, hA0 i⟩) :
    ∃ (i : ι) (u : Rˣ) (δ : R), α i * ((y : R) + θ) = u * δ ^ 3 :=
  exists_unit_mul_cube_of_mordell_rep (x := (x : R)) hθ
    (by exact_mod_cast congrArg (Int.cast : ℤ → R) h)
    (by simpa using hbez.map (Int.castRingHom R)) hne hA0 hA hcov

/-- **The descent, `x` even** (only for `n ≡ 1 [ZMOD 8]`).  With `2 = π π'`,
`(y + θ)/2 = π κ` and `(y - θ)/2 = π' κ'`, one gets `κ κ' = X ^ 3` for `X = x / 2`; cancelling
`π π' = 2` reduces to `exists_unit_mul_pow_rep`.  The hypothesis `π π' = 2` says the primes
above `2` are principal. -/
theorem exists_unit_mul_cube_of_even_rep {n θ y X : R} (hθ : θ ^ 2 = n) (h2 : (2 : R) ≠ 0)
    (h : y ^ 2 = 8 * X ^ 3 + n)
    {π π' κ κ' : R} (hππ : π * π' = 2)
    (hη : y + θ = 2 * (π * κ)) (hη' : y - θ = 2 * (π' * κ'))
    (hbez : IsCoprime (2 * X) n) (hκ : κ ≠ 0)
    {ι : Type*} {A : ι → Ideal R} {α : ι → R}
    (hA0 : ∀ i, A i ∈ nonZeroDivisors (Ideal R)) (hA : ∀ i, A i ^ 3 = Ideal.span {α i})
    (hcov : ∀ C : ClassGroup R, C ^ 3 = 1 → ∃ i, C = ClassGroup.mk0 ⟨A i, hA0 i⟩) :
    ∃ (i : ι) (u : Rˣ) (δ : R), α i * κ = u * δ ^ 3 := by
  have h22 : (4 : R) = 2 * 2 := by norm_num
  have h4 : (4 : R) ≠ 0 := by
    rw [h22]
    exact mul_ne_zero h2 h2
  have hprod : (π * κ) * (π' * κ') = 2 * X ^ 3 :=
    mul_left_cancel₀ h4 (by linear_combination (θ - y) * hη - 2 * (π * κ) * hη' + h - hθ)
  have hsub : (π * κ) - (π' * κ') = θ :=
    mul_left_cancel₀ h2 (by linear_combination hη' - hη)
  have hbez3 : IsCoprime (2 * X ^ 3) n :=
    hbez.of_mul_left_left.mul_left hbez.of_mul_left_right.pow_left
  obtain ⟨m, k, hmk⟩ := hbez3
  have hcop : IsCoprime κ κ' := by
    have hbz : IsCoprime (π * κ) (π' * κ') := by
      refine isCoprime_of_bezout (m := m) (n := k) ?_
      rw [hprod, hsub]
      linear_combination hmk + k * hθ
    exact hbz.of_mul_left_right.of_mul_right_right
  refine exists_unit_mul_pow_rep three_ne_zero (z := X) hκ hcop
    (mul_left_cancel₀ h2 ?_) hA0 hA hcov
  linear_combination hprod - (κ * κ') * hππ

/-- `exists_unit_mul_cube_of_even_rep` with `n`, `x`, `y`, `X` in `ℤ` and `hx : x = 2 * X`. -/
theorem exists_unit_mul_cube_of_even_rep_int
    {n : ℤ} {θ : R} (hθ : θ ^ 2 = (n : R)) (h2 : (2 : R) ≠ 0)
    {x y X : ℤ} (h : y ^ 2 = x ^ 3 + n) (hx : x = 2 * X)
    {π π' κ κ' : R} (hππ : π * π' = 2)
    (hη : (y : R) + θ = 2 * (π * κ)) (hη' : (y : R) - θ = 2 * (π' * κ'))
    (hbez : IsCoprime (2 * X) n) (hκ : κ ≠ 0)
    {ι : Type*} {A : ι → Ideal R} {α : ι → R}
    (hA0 : ∀ i, A i ∈ nonZeroDivisors (Ideal R)) (hA : ∀ i, A i ^ 3 = Ideal.span {α i})
    (hcov : ∀ C : ClassGroup R, C ^ 3 = 1 → ∃ i, C = ClassGroup.mk0 ⟨A i, hA0 i⟩) :
    ∃ (i : ι) (u : Rˣ) (δ : R), α i * κ = u * δ ^ 3 :=
  exists_unit_mul_cube_of_even_rep (X := (X : R)) hθ h2
    (by
      have hZ : y ^ 2 = 8 * X ^ 3 + n := by rw [h, hx]; ring
      exact_mod_cast congrArg (Int.cast : ℤ → R) hZ)
    hππ hη hη' (by simpa using hbez.map (Int.castRingHom R)) hκ hA0 hA hcov

/-! ### The case `3 ∤ h` -/

/-- The trivial-family case of `exists_unit_mul_pow_rep`: no multiplier is needed. -/
theorem exists_unit_mul_pow [Finite (ClassGroup R)] {k : ℕ} (hk0 : k ≠ 0) {a b z : R}
    (ha : a ≠ 0) (hcop : IsCoprime a b) (h : a * b = z ^ k)
    (hk : Nat.Coprime k (Nat.card (ClassGroup R))) :
    ∃ (u : Rˣ) (γ : R), a = u * γ ^ k := by
  obtain ⟨-, u, γ, hγ⟩ := exists_unit_mul_pow_rep hk0 ha hcop h (A := fun _ : Unit => 1)
    (α := fun _ : Unit => 1) (fun _ => one_mem _) (fun _ => by simp)
    (eq_mk0_one_of_pow_eq_one hk)
  exact ⟨u, γ, by simpa using hγ⟩

/-- The trivial-family case of `exists_unit_mul_cube_of_mordell_rep`. -/
theorem exists_unit_mul_cube_of_mordell [Finite (ClassGroup R)]
    {n : ℤ} {θ : R} (hθ : θ ^ 2 = (n : R))
    (hk : Nat.Coprime 3 (Nat.card (ClassGroup R)))
    {x y : ℤ} (h : y ^ 2 = x ^ 3 + n)
    (hbez : IsCoprime x (2 * n))
    (hne : ((y : R) + θ) ≠ 0) :
    ∃ (u : Rˣ) (γ : R), (y : R) + θ = u * γ ^ 3 := by
  obtain ⟨-, u, γ, hγ⟩ := exists_unit_mul_cube_of_mordell_rep_int hθ h hbez hne
    (A := fun _ : Unit => 1) (α := fun _ : Unit => 1) (fun _ => one_mem _)
    (fun _ => by simp) (eq_mk0_one_of_pow_eq_one hk)
  exact ⟨u, γ, by simpa using hγ⟩

/-- The trivial-family case of `exists_unit_mul_cube_of_even_rep`. -/
theorem exists_unit_mul_cube_of_even [Finite (ClassGroup R)]
    {n : ℤ} {θ : R} (hθ : θ ^ 2 = (n : R)) (h2 : (2 : R) ≠ 0)
    (hk : Nat.Coprime 3 (Nat.card (ClassGroup R)))
    {x y X : ℤ} (h : y ^ 2 = x ^ 3 + n) (hx : x = 2 * X)
    {π π' κ κ' : R} (hππ : π * π' = 2)
    (hη : (y : R) + θ = 2 * (π * κ)) (hη' : (y : R) - θ = 2 * (π' * κ'))
    (hbez : IsCoprime (2 * X) n) (hκ : κ ≠ 0) :
    ∃ (u : Rˣ) (γ : R), κ = u * γ ^ 3 := by
  obtain ⟨-, u, γ, hγ⟩ :=
    exists_unit_mul_cube_of_even_rep_int hθ h2 h hx hππ hη hη' hbez hκ
    (A := fun _ : Unit => 1) (α := fun _ : Unit => 1) (fun _ => one_mem _)
    (fun _ => by simp) (eq_mk0_one_of_pow_eq_one hk)
  exact ⟨u, γ, by simpa using hγ⟩

end Descent

end Mordell
