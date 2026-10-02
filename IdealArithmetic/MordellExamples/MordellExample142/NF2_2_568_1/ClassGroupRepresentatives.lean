import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.Invariants2_2_568_1
import IdealArithmetic.MordellThueProject.ClassGroupDescent

/-!
# Explicit representatives for the class group of `ℚ(√142)`

`class_group_equiv : (∀ i : Fin 1, ZMod 3) ≃+ Additive (ClassGroup (𝓞 K))` is
`ClassGroupO_equiv` followed by transport along `eO : O ≃+* 𝓞 K`, and `ClassGroupO_equiv`
comes from `equivClassGroupOfSaturated`, whose value is `∏ i, ClassGroup.mk0 (J' i) ^ (x i).val`.
With a single generator this is `ClassGroup.mk0 (J' 0) ^ (x 0).val`, so the three classes are
named by the powers of `J0 = (3, 2 + √142)`, the prime above `3` (with `J0 ^ 3 = (-13 + √142)`
principal).

Since `class_group_equiv` lands in the class group of `𝓞 K` rather than of `O`, the ideals are
pushed forward along `eO`; `JK k` is `J0 ^ k · 𝓞 K`.

* `class_group_equiv_zero` : `![0] ↦ 1`;
* `class_group_equiv_one`  : `![1] ↦ [J0 · 𝓞 K]`;
* `class_group_equiv_two`  : `![2] ↦ [J0 ^ 2 · 𝓞 K]` (see `JK_pow_coe`).

Opus 5
-/

set_option linter.all false

namespace NF2_2_568_1

open NumberField Mordell
open scoped Classical

noncomputable section

instance instNeZero3 : ∀ i : Fin 1, NeZero ((![3] : Fin 1 → ℕ) i) := fun i => by
  fin_cases i; exact ⟨by decide⟩

/-- The isomorphism `O ≃+* 𝓞 K` through which `class_group_equiv` factors. -/
abbrev eO : O ≃+* RingOfIntegers K := (Subalgebra.equivOfEq _ _ O_integral_closure).toRingEquiv

/-- `J0 = (3, 2 + √142)`, pushed forward to the ring of integers.  Non-degeneracy is inherited
from `J' 0`, the non-zero-divisor form of `J0` already built in `Invariants`. -/
def JK : nonZeroDivisors (Ideal (RingOfIntegers K)) :=
  Ideal.toNonZeroDivisorOfNeZero (Ideal.map eO (J' 0))
    fun hc => nonZeroDivisors.ne_zero (J' 0).2
      (((Ideal.map_eq_bot_iff_of_injective eO.injective).mp hc).trans Submodule.zero_eq_bot.symm)

lemma JK_pow_coe (k : ℕ) :
    ((JK ^ k : nonZeroDivisors (Ideal (RingOfIntegers K))) : Ideal (RingOfIntegers K))
      = Ideal.map (eO : O →+* RingOfIntegers K) (J0 ^ k) := by
  rw [SubmonoidClass.coe_pow]
  exact (Ideal.map_pow (f := (eO : O →+* RingOfIntegers K)) (I := J0) k).symm

/-- **The value of `class_group_equiv`**: `x` is sent to the class of `J0 ^ (x 0) · 𝓞 K`. -/
lemma class_group_equiv_apply (x : ∀ i : Fin 1, ZMod (![3] i)) :
    Additive.toMul (class_group_equiv x) = ClassGroup.mk0 (JK ^ (x 0).val) := by
  have hO : Additive.toMul (ClassGroupO_equiv x) = ∏ i, ClassGroup.mk0 (J' i) ^ (x i).val := rfl
  have h1 : ClassGroup.congr eO (ClassGroup.mk0 (J' 0)) = ClassGroup.mk0 JK :=
    ClassGroup.map_apply' _ eO.injective (J' 0) JK rfl
  show ClassGroup.congr eO (Additive.toMul (ClassGroupO_equiv x)) = _
  rw [hO, Fin.prod_univ_one, map_pow, h1, ← map_pow]

/-- `![0]` is sent to the trivial class. -/
theorem class_group_equiv_zero :
    Additive.toMul (class_group_equiv (fun _ => 0)) = 1 := by
  rw [class_group_equiv_apply, show ((0 : ZMod (![3] 0)).val) = 0 from rfl, pow_zero, map_one]

/-- `![1]` is sent to the class of `J0 · 𝓞 K`. -/
theorem class_group_equiv_one :
    Additive.toMul (class_group_equiv (fun _ => 1)) = ClassGroup.mk0 JK := by
  rw [class_group_equiv_apply, show ((1 : ZMod (![3] 0)).val) = 1 from rfl, pow_one]

/-- `![2]` is sent to the class of `J0 ^ 2 · 𝓞 K`. -/
theorem class_group_equiv_two :
    Additive.toMul (class_group_equiv (fun _ => 2)) = ClassGroup.mk0 (JK ^ 2) := by
  rw [class_group_equiv_apply, show ((2 : ZMod (![3] 0)).val) = 2 from rfl]


/-! ### The same inside `O`

The Thue reduction works in `O = ℤ[√142]`, where the integral basis and the coordinate
machinery live, so the representatives are needed there too.  In `O` no transport is involved:
`ClassGroupO_equiv` is already a statement about `ClassGroup O`. -/

lemma classGroupO_equiv_apply (x : ∀ i : Fin 1, ZMod (![3] i)) :
    Additive.toMul (ClassGroupO_equiv x) = ClassGroup.mk0 (J' 0) ^ (x 0).val := by
  have hO : Additive.toMul (ClassGroupO_equiv x) = ∏ i, ClassGroup.mk0 (J' i) ^ (x i).val := rfl
  rw [hO, Fin.prod_univ_one]

lemma J0_cube : J0 ^ 3 = Ideal.span {alpha0} := NPSU3.h 0

lemma J0_pow_cube (j : ℕ) : (J0 ^ j) ^ 3 = Ideal.span {alpha0 ^ j} := by
  have hc : (J0 ^ j) ^ 3 = (J0 ^ 3) ^ j := pow_right_comm J0 j 3
  rw [hc, J0_cube, Ideal.span_singleton_pow]

instance : Finite (ClassGroup O) :=
  Finite.of_equiv _ (ClassGroupO_equiv.toEquiv.trans Additive.toMul)

lemma J0_mem : J0 ∈ nonZeroDivisors (Ideal O) := by
  have h := (J' 0).2
  rw [J'_apply 0] at h
  exact h

lemma classGroup_gen (C : ClassGroup O) : ∃ k : ℕ, C = ClassGroup.mk0 ⟨J0, J0_mem⟩ ^ k := by
  obtain ⟨x, hx⟩ := ClassGroupO_equiv.surjective (Additive.ofMul C)
  refine ⟨(x 0).val, ?_⟩
  have hC : C = ClassGroup.mk0 (J' 0) ^ (x 0).val := by
    rw [← classGroupO_equiv_apply, hx]; rfl
  rw [hC]
  exact congrArg (· ^ (x 0).val) (congrArg ClassGroup.mk0 (Subtype.ext (J'_apply 0)))

/-- **The class-group representatives, inside `O`.**  The classes of `1, J0, J0 ^ 2` exhaust
`Cl(O)`, hence in particular its `3`-torsion -- which is the class-group input the descent
asks for. -/
theorem class_group_covers_O (C : ClassGroup O) (hC : C ^ 3 = 1) :
    ∃ j : Fin 3, C = ClassGroup.mk0 ⟨J0 ^ (j : ℕ), Submonoid.pow_mem _ J0_mem _⟩ :=
  exists_eq_mk0_pow_of_cyclic_three J0_mem ⟨alpha0, J0_cube⟩ classGroup_gen C hC

/-! ### The representatives

`Cl(K) = ⟨[J0]⟩ ≅ ℤ/3` with `J0 ^ 3 = (alpha0)`, so for any nonzero ideal `I` one of
`I`, `I·JK`, `I·JK²` is principal -- and being a product of *integral* ideals, its generator
lies in `𝓞 K`.  Cubing then puts the multiplier on the same side as `I ^ 3`:

* `[I] = 1`      : `I ^ 3 = (δ) ^ 3`;
* `[I] = [JK] ²` : `I ^ 3 · (alpha0)   = (δ) ^ 3`;
* `[I] = [JK]`   : `I ^ 3 · (alpha0 ²) = (δ) ^ 3`.

Note that dividing instead -- writing `I ^ 3 = (δ) ^ 3 · (alpha0)` -- would force `JK ∣ I`,
which fails already for the prime above `7`; there `δ` only exists in `K`, with `N(δ) = 7/3`.
-/

lemma JK_cube : (JK : Ideal (RingOfIntegers K)) ^ 3 = Ideal.span {eO alpha0} := by
  rw [← SubmonoidClass.coe_pow, JK_pow_coe 3]
  exact (congrArg (Ideal.map (eO : O →+* RingOfIntegers K)) (NPSU3.h 0)).trans
    (by rw [Ideal.map_span, Set.image_singleton]; rfl)

lemma JK_six : (JK : Ideal (RingOfIntegers K)) ^ 6 = Ideal.span {eO (alpha0 ^ 2)} := by
  rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, JK_cube, map_pow, Ideal.span_singleton_pow]

lemma mk0_JK_cube : ClassGroup.mk0 (JK ^ 3) = 1 := by
  rw [show (JK ^ 3 : nonZeroDivisors (Ideal (RingOfIntegers K)))
      = ⟨(JK : Ideal (RingOfIntegers K)) ^ 3,
          by rw [← SubmonoidClass.coe_pow]; exact (JK ^ 3).2⟩ from
    Subtype.ext (SubmonoidClass.coe_pow JK 3)]
  refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
  rw [JK_cube]
  exact ⟨eO alpha0, rfl⟩

/-- **The class-group representatives.**  Every nonzero ideal `I` of `𝓞 K` satisfies one of the
three relations, with `δ` integral: the multiplier `1`, `alpha0` or `alpha0 ^ 2` sits on the
same side as `I ^ 3`. -/
theorem class_group_representative (I : nonZeroDivisors (Ideal (RingOfIntegers K))) :
    ∃ δ : RingOfIntegers K,
      (I : Ideal (RingOfIntegers K)) ^ 3 = Ideal.span {δ} ^ 3 ∨
      (I : Ideal (RingOfIntegers K)) ^ 3 * Ideal.span {eO alpha0} = Ideal.span {δ} ^ 3 ∨
      (I : Ideal (RingOfIntegers K)) ^ 3 * Ideal.span {eO (alpha0 ^ 2)}
        = Ideal.span {δ} ^ 3 := by
  obtain ⟨x, hx⟩ := class_group_equiv.surjective (Additive.ofMul (ClassGroup.mk0 I))
  have hmk : ClassGroup.mk0 (JK ^ (x 0).val) = ClassGroup.mk0 I := by
    rw [← class_group_equiv_apply, hx]; rfl
  -- `I * JK ^ j` is principal for `j = 3 - (x 0).val`, and its generator is integral
  have key : ∀ j : ℕ, (x 0).val + j = 3 →
      ∃ δ, (I : Ideal (RingOfIntegers K)) * (JK : Ideal (RingOfIntegers K)) ^ j
        = Ideal.span {δ} := by
    intro j hj
    obtain ⟨δ, hδ⟩ := exists_gen_of_mk0_eq_one (A := I * JK ^ j)
      (by rw [map_mul, ← hmk, ← map_mul, ← pow_add, hj]; exact mk0_JK_cube)
    exact ⟨δ, by rwa [Submonoid.coe_mul, SubmonoidClass.coe_pow] at hδ⟩
  have hlt : (x 0).val < 3 := ZMod.val_lt (x 0)
  interval_cases h : (x 0).val
  · -- `[I] = 1` : `I` itself is principal
    obtain ⟨δ, hδ⟩ := exists_gen_of_mk0_eq_one (A := I) (by rw [← hmk, pow_zero, map_one])
    exact ⟨δ, Or.inl (by rw [hδ])⟩
  · -- `[I] = [JK]` : multiply by `JK ^ 2`, multiplier `alpha0 ^ 2`
    obtain ⟨δ, hδ⟩ := key 2 (by omega)
    refine ⟨δ, Or.inr (Or.inr ?_)⟩
    have h3 : ((I : Ideal (RingOfIntegers K)) * (JK : Ideal (RingOfIntegers K)) ^ 2) ^ 3
        = (Ideal.span {δ}) ^ 3 := by rw [hδ]
    rwa [mul_pow, ← pow_mul, show 2 * 3 = 6 from rfl, JK_six] at h3
  · -- `[I] = [JK] ^ 2` : multiply by `JK`, multiplier `alpha0`
    obtain ⟨δ, hδ⟩ := key 1 (by omega)
    refine ⟨δ, Or.inr (Or.inl ?_)⟩
    have h3 : ((I : Ideal (RingOfIntegers K)) * (JK : Ideal (RingOfIntegers K)) ^ 1) ^ 3
        = (Ideal.span {δ}) ^ 3 := by rw [hδ]
    rwa [mul_pow, ← pow_mul, show 1 * 3 = 3 from rfl, JK_cube] at h3

end

end NF2_2_568_1
