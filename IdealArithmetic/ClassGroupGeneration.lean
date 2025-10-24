import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Group.Subgroup.Finsupp

noncomputable def MinkowskiBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
  (↑(Module.finrank ℚ K).factorial / ↑(Module.finrank ℚ K) ^ Module.finrank ℚ K * √|↑(NumberField.discr K)|)

theorem K_minkowski_decimal {F : Type*} [Field F] [NumberField F] (r : ℝ)
    (h : (4 / 3.14159265358979323846 : ℝ) ^ NumberField.InfinitePlace.nrComplexPlaces F
    * (↑(Module.finrank ℚ F).factorial / ↑(Module.finrank ℚ F) ^ Module.finrank ℚ F * √|↑(NumberField.discr F)|) ≤ r) :
    MinkowskiBound F ≤ r  := by
  unfold MinkowskiBound
  have := Real.pi_gt_d20
  have : (4 / Real.pi) ^ (NumberField.InfinitePlace.nrComplexPlaces F) ≤
    (4 / 3.14159265358979323846) ^ (NumberField.InfinitePlace.nrComplexPlaces F) := by
    refine pow_le_pow_left₀ ?_ ?_ _
    · refine div_nonneg (by norm_num) (by exact Real.pi_nonneg)
    · refine le_of_lt ?_
      refine div_lt_div_of_pos_left (by norm_num) (by norm_num) this
  refine le_trans ?_ h
  refine mul_le_mul_of_nonneg_right this ?_
  refine mul_nonneg ?_ ?_
  · refine div_nonneg ?_ ?_
    · simp only [Nat.cast_nonneg]
    · simp only [Nat.cast_nonneg, pow_nonneg]
  · simp only [Real.sqrt_nonneg]

variable {K : Type*} [Field K] [NumberField K]

local notation "Oκ" => NumberField.RingOfIntegers K

lemma ClassGroup.closure_primes_norm_le_eq_top :
  Subgroup.closure
  (ClassGroup.mk0 '' {I : ↥(nonZeroDivisors (Ideal (Oκ))) | (I : Ideal Oκ).IsPrime ∧
  Ideal.absNorm (I : Ideal Oκ) ≤ MinkowskiBound K }) = ⊤ := by
refine le_antisymm (le_top) ?_
intro C hC
obtain ⟨J , hJC, hJnorm⟩ := NumberField.exists_ideal_in_class_of_norm_le C
have hJp := prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero J)
have hJn := Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 J.2
have hPf : ∀ p, p ∈ UniqueFactorizationMonoid.normalizedFactors (↑J : Ideal Oκ) → p.IsPrime ∧ J ≤ p :=
  fun p hp => (Ideal.mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero J)).1 hp
have aux1 : ∀ p, p ∈ UniqueFactorizationMonoid.normalizedFactors (↑J : Ideal Oκ) →
  p.absNorm ∣ (J : Ideal Oκ).absNorm := by
  intro p hp
  exact (Ideal.absNorm_dvd_absNorm_of_le (hPf p hp).2)
have aux2 : ∀ p, p ∈ UniqueFactorizationMonoid.normalizedFactors (↑J : Ideal Oκ) →
  p ∈ nonZeroDivisors (Ideal (Oκ)) := by
  intro p hp
  rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors]
  by_contra hc
  simp_rw [zero_dvd_iff.1 (hc ▸ aux1 p hp )] at hJn
  contradiction
let M := List.pmap (fun p hp => (⟨p, aux2 _ hp⟩ : nonZeroDivisors (Ideal (Oκ))))
  (UniqueFactorizationMonoid.normalizedFactors (↑J : Ideal Oκ)).toList (by simp)
have hMs : List.map Subtype.val M = (UniqueFactorizationMonoid.normalizedFactors (↑J : Ideal Oκ)).toList := by
  simp only [List.pmap_eq_attachWith, mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot, ne_eq,
    List.map_subtype, List.unattach_attachWith, List.map_id_fun', id_eq, M]
have hMprod : (Multiset.ofList M).prod = J := by
  rw [← Subtype.val_inj, ← hJp, Multiset.prod_coe, SubmonoidClass.coe_list_prod, hMs,
    Multiset.prod_toList]
apply_fun (ClassGroup.mk0) at hMprod
rw [map_multiset_prod, hJC ] at hMprod
rw [← hMprod]
refine Submonoid.multiset_prod_mem _  _ ?_
intro P hP
refine Subgroup.subset_closure ?_
obtain ⟨p, hp1, hp2⟩ := Multiset.mem_map.1 hP
simp only [List.pmap_eq_attachWith, Multiset.mem_coe, List.mem_attachWith, Multiset.mem_toList,
  M] at hp1
simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists, mem_nonZeroDivisors_iff_ne_zero,
  exists_and_left, M]
use (p : Ideal Oκ)
constructor
· constructor
  · exact (hPf _ hp1).1
  · have aux3 := Nat.le_of_dvd (hJn) (aux1 _ hp1)
    rify at aux3
    refine le_trans (aux3) hJnorm
· have : (p : Ideal Oκ) ≠ 0 := by
    rw [← mem_nonZeroDivisors_iff_ne_zero]
    simp only [SetLike.coe_mem, M]
  use this


/-- This is now in Mathlib by Riccardo -/
lemma Ideal.absNorm_eq_pow_inertiaDeg {R : Type*} [CommRing R][IsDedekindDomain R]
    [Module.Free ℤ R] [Module.Finite ℤ R] {p : ℤ}
    (P : Ideal R) [P.LiesOver (span {p})] (hp: Prime p) :
    absNorm P = p.natAbs ^ ((span {p}).inertiaDeg P) := by
  have : (span {p}).IsMaximal :=
    (isPrime_of_prime (prime_span_singleton_iff.mpr hp)).isMaximal (by simp [hp.ne_zero])
  have h : Module.Finite (ℤ ⧸ span {p}) (R ⧸ P) := module_finite_of_liesOver P (span {p})
  let _ : Field (ℤ ⧸ span {p}) := Quotient.field (span {p})
  rw [inertiaDeg_algebraMap, absNorm_apply, Submodule.cardQuot_apply,
    Module.natCard_eq_pow_finrank (K := ℤ ⧸ span {p})]
  simp [Nat.card_congr (Int.quotientSpanEquivZMod p).toEquiv]


lemma primes_below_bound_of_factorization (B : ℕ)
  (F : Nat.primesBelow B → Multiset (Ideal Oκ))
  (hP : ∀ p, ∀ q ∈ (F p), q.IsPrime)
  (hPpord : ∀ p, (F p).prod = Ideal.span {↑p} ) :
 {I : Ideal Oκ | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < B} =
  ⋃ (p : Nat.primesBelow B), {q ∈ F p | q.absNorm < B} := by
refine le_antisymm ?_ ?_
· intro I hIn
  rcases hIn with ⟨hIn1, hIn2, hIn3 ⟩
  let P := Ideal.under ℤ I
  have hPP: P.IsPrime :=  Ideal.IsPrime.under ℤ P
  let p := Submodule.IsPrincipal.generator P
  have hPeq : P = Ideal.span {p} := (Ideal.span_singleton_generator _ ).symm
  have : I.LiesOver (Ideal.span {p}) := by
    rw [← hPeq]
    simp only [Ideal.over_under, P]
  have hpn : p ≠ 0 := by
    intro hc
    erw [hc, Ideal.span_zero] at this
    have hIaux : I ∈ (⊥ : Ideal ℤ).primesOver Oκ := by
      exact ⟨hIn2, this ⟩
    rw [Ideal.primesOver_bot] at hIaux
    simp only [Set.mem_singleton_iff, P] at hIaux
    rw [hIaux] at hIn1
    simp only [Ideal.absNorm_bot, lt_self_iff_false] at hIn1
  have hpp : Prime p := by
    rw [← Ideal.span_singleton_prime, ← (Ideal.span_singleton_generator _ ).symm]
    exact hPP
    · exact hpn
  haveI hpM : Ideal.IsMaximal (Ideal.span {p} ):= by
    rw [← hPeq]
    refine IsPrime.to_maximal_ideal ?_
    rw [hPeq]
    simp only [ne_eq, Ideal.span_singleton_eq_bot, hpn, not_false_eq_true, P]
  simp only [Set.mem_iUnion,  Subtype.exists, P]
  use p.natAbs
  have hlB : p.natAbs < B := by
    rw [Ideal.absNorm_eq_pow_inertiaDeg I hpp] at hIn3
    refine lt_of_le_of_lt ?_ hIn3
    nth_rw 1 [← pow_one (p.natAbs)]
    refine Nat.pow_le_pow_of_le ?_ ?_
    · exact Nat.Prime.one_lt (Int.prime_iff_natAbs_prime.1 hpp)
    · exact (Ideal.inertiaDeg_pos (Ideal.span {p}) I)
  have hBm : p.natAbs ∈ B.primesBelow := by
    rw [Nat.mem_primesBelow]
    exact ⟨hlB, Int.prime_iff_natAbs_prime.1 hpp⟩
  use hBm
  constructor
  · dsimp
    have hprod : (F ⟨p.natAbs, hBm⟩).prod ≤ I := by
      rw [hPpord ⟨p.natAbs, hBm⟩ , Ideal.span_singleton_le_iff_mem]
      convert (Ideal.mem_of_liesOver I (Ideal.span {p}) ↑p.natAbs).1 ?_
      exact Eq.symm (algebraMap.coe_natCast p.natAbs)
      simp only [Int.natCast_natAbs, abs_mem_iff, P]
      exact Ideal.mem_span_singleton_self p
    obtain ⟨J, hJ1, hJ2⟩ := (Ideal.IsPrime.multiset_prod_le hIn2).1 hprod
    have hJp : J.IsPrime := hP _ J hJ1
    rw [Ring.DimensionLeOne.prime_le_prime_iff_eq ?_] at hJ2
    rw [← hJ2]
    exact hJ1
    · intro hc
      rw [hc] at hJ1
      have : (Ideal.span {↑p.natAbs} : Ideal Oκ) = 0 := by
        rw [← hPpord ⟨p.natAbs, hBm⟩]
        refine Multiset.prod_eq_zero ?_
        exact hJ1
      simp only [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero,
        Int.natAbs_eq_zero, P] at this
      exact hpn this
  · exact hIn3
· intro I hI
  simp only [Set.mem_iUnion] at hI
  obtain ⟨p, hp1, hp2⟩ := hI
  constructor
  · by_contra! hc
    simp only [nonpos_iff_eq_zero, Ideal.absNorm_eq_zero_iff] at hc
    rw [hc] at hp1
    have : (Ideal.span {↑p} : Ideal Oκ) = 0 := by
      rw [← hPpord p]
      refine Multiset.prod_eq_zero ?_
      exact hp1
    simp only [Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero,
      Int.natAbs_eq_zero] at this
    exact Nat.Prime.ne_zero (Nat.mem_primesBelow.1 p.2).2 this
  · exact ⟨hP _ _ hp1,  hp2⟩



-- Even though we could use the to_additive attribute in the multiplicative version,
-- proving the additive version first is easier.

-- Why use functions instead of lists? Because its better to use the linear algebra library,
-- where vectors and encoded in such a way.
lemma addSubgroup_closure_le_of_invertible_relation {G : Type*} {m n r : Type}
  [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
  [AddCommGroup G] {g : m → G} {x : n → G} {A : Matrix r m ℤ} {B : Matrix r n ℤ}
  (hA : ∃ M : Matrix m r ℤ, M * A = 1)
  (hg : ∀ i, ∑ j , (A i j) • (g j) = ∑ j , (B i j) • (x j)) :
    AddSubgroup.closure (Set.range g) ≤ AddSubgroup.closure (Set.range x) := by
  rw [AddSubgroup.closure_le]
  intro t ht
  obtain ⟨i, hi⟩  := Set.mem_range.1 ht
  rw [← hi]
  obtain ⟨M, hM⟩ := hA
  have : ∀ t , ∀ h : Fintype t, ∀ S : Matrix r t ℤ , ∀ g : t → G ,
    (∀ i , ∑ k, (M i k) • (∑ j, (S k j) • (g j)) = ∑ k, ((M * S) i k) • (g k)) := by
    intro t ht S g i
    simp_rw [Matrix.mul_apply]
    simp_rw [Finset.smul_sum, Finset.sum_smul, ← smul_assoc]
    rw [Finset.sum_comm]
    rfl
  have auxM := this m hm A g i
  have auxB := this n hn B x
  simp_rw [hg] at auxM
  rw [hM, auxB i] at auxM
  simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte] at auxM
  rw [← auxM]
  apply AddSubgroup.sum_mem
  intro c hc
  refine AddSubgroup.zsmul_mem _  ((AddSubgroup.subset_closure) (Set.mem_range_self c)) _

lemma addSubgroup_closure_eq_of_invertible_relation {G : Type*} {m n r : Type}
  [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
  [AddCommGroup G] {g : m → G} {x : n → G} {A : Matrix r m ℤ} {B : Matrix r n ℤ}
  (hA : ∃ M : Matrix m r ℤ, M * A = 1)
  (hg : ∀ i, ∑ j , (A i j) • (g j) = ∑ j , (B i j) • (x j))
  (hs : ∀ i, x i ∈ AddSubgroup.closure (Set.range g)) :
    AddSubgroup.closure (Set.range x) = AddSubgroup.closure (Set.range g) := by
  refine le_antisymm ?_ ?_
  · rw [AddSubgroup.closure_le]
    intro t ht
    obtain ⟨i, hi⟩ := Set.mem_range.1 ht
    rw [← hi]
    exact hs i
  · exact addSubgroup_closure_le_of_invertible_relation hA hg

lemma subgroup_closure_le_of_invertible_relation {G : Type*} {m n r : Type}
  [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
  [CommGroup G] {g : m → G} {x : n → G} {A : Matrix r m ℤ} {B : Matrix r n ℤ}
  (hA : ∃ M : Matrix m r ℤ, M * A = 1)
  (hg : ∀ i, ∏ j , (g j) ^ (A i j) = ∏ j, (x j) ^ (B i j)) :
    Subgroup.closure (Set.range g) ≤ Subgroup.closure (Set.range x) := by
  apply_fun Subgroup.toAddSubgroup
  rw [Subgroup.toAddSubgroup_closure, Subgroup.toAddSubgroup_closure]
  rw [Set.preimage_equiv_eq_image_symm, Set.preimage_equiv_eq_image_symm,
    ← Set.range_comp, ← Set.range_comp]
  refine addSubgroup_closure_le_of_invertible_relation hA hg

lemma subgroup_closure_eq_of_invertible_relation {G : Type*} {m n r : Type}
  [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
  [CommGroup G] {g : m → G} {x : n → G} {A : Matrix r m ℤ} {B : Matrix r n ℤ}
  (hA : ∃ M : Matrix m r ℤ, M * A = 1)
  (hg : ∀ i, ∏ j , (g j) ^ (A i j) = ∏ j, (x j) ^ (B i j))
  (hs : ∀ i, x i ∈ Subgroup.closure (Set.range g)) :
    Subgroup.closure (Set.range x) = Subgroup.closure (Set.range g) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    intro t ht
    obtain ⟨i, hi⟩ := Set.mem_range.1 ht
    rw [← hi]
    exact hs i
  · exact subgroup_closure_le_of_invertible_relation hA hg

-- I prefer to use less than in the bound, because I can use the primes less than type.
lemma subgroup_closure_eq_classGroup {m n r : Type} {b : ℕ}
    [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
    {g : m → Ideal Oκ} {g' : m → nonZeroDivisors (Ideal (Oκ))}
    {x : n → Ideal Oκ} {x' : n → nonZeroDivisors (Ideal (Oκ))}
    (hg' : ∀ i, ↑(g' i) = g i) (hx' : ∀ i, ↑(x' i) = x i)
    (hB : MinkowskiBound K < b)
    (hg : {I : Ideal Oκ | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < b} ⊆ Set.range g)
    {A : Matrix r m ℕ} {B : Matrix r n ℕ}
    (hA : ∃ M : Matrix m r ℤ, M * A.map (algebraMap ℕ ℤ) = 1)
    (hgmul : ∀ i, ∃ (α β : Oκ), ∃ (_ : α ≠ 0), ∃ (_ : β ≠ 0),
      Ideal.span {α} * ∏ j , (g j) ^ (A i j) = Ideal.span {β} * ∏ j, (x j) ^ (B i j)) :
      Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (x' i))) = ⊤ := by
  have hgnz : ∀ i , g i ∈ nonZeroDivisors (Ideal Oκ) := by
        intro i
        rw [← (hg' i )]
        exact SetLike.coe_mem _
  have aux1 : ClassGroup.mk0 '' {I : ↥(nonZeroDivisors (Ideal (Oκ))) | (I : Ideal Oκ).IsPrime ∧
    Ideal.absNorm (I : Ideal Oκ) < b } ⊆ Set.range (fun i => ClassGroup.mk0 (g' i)) := by
      intro x
      simp only [Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
        Submodule.zero_eq_bot, ne_eq, exists_and_left, Set.mem_range, forall_exists_index, and_imp]
      intro I hIp hIn hIz hIc
      have hmem : I ∈ Set.range g := by
        suffices h : I ∈ {I | 0 < Ideal.absNorm I ∧ I.IsPrime ∧ Ideal.absNorm I < b} from (hg h)
        constructor
        · exact Ideal.absNorm_pos_iff_mem_nonZeroDivisors.2 hIz
        · exact ⟨hIp, hIn⟩
      obtain ⟨y, hy⟩ :=  Set.mem_range.1 hmem
      use y
      simp_rw [← hIc, ← hy, ← hg']
  have htop: ⊤ = Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (g' i))) := by
    refine le_antisymm ?_ ?_
    · rw [← ClassGroup.closure_primes_norm_le_eq_top]
      refine Subgroup.closure_mono (le_trans (Set.image_mono ?_) aux1)
      intro I hIp
      refine ⟨hIp.1, ?_ ⟩
      rify
      refine lt_of_le_of_lt hIp.2 hB
    · exact le_top
  rw [htop]
  refine subgroup_closure_eq_of_invertible_relation (A := A.map (algebraMap ℕ ℤ))
    (B := B.map (algebraMap ℕ ℤ)) hA ?_ ?_
  · intro i
    simp only [Matrix.map_apply, eq_natCast, zpow_natCast]
    simp_rw [← map_pow, ← map_prod, ClassGroup.mk0_eq_mk0_iff]
    convert hgmul i
    · simp only [SubmonoidClass.coe_finset_prod, SubmonoidClass.coe_pow, hg']
    · simp only [SubmonoidClass.coe_finset_prod, SubmonoidClass.coe_pow, hx']
  · rw [← htop]
    simp only [Subgroup.mem_top, implies_true]

lemma subgroup_closure_eq_classGroup' {m n r : Type} {b : ℕ}
    [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
    {g : m → Ideal Oκ} {g' : m → nonZeroDivisors (Ideal (Oκ))}
    {x : n → Ideal Oκ} {x' : n → nonZeroDivisors (Ideal (Oκ))}
    (hg' : ∀ i, ↑(g' i) = g i) (hx' : ∀ i, ↑(x' i) = x i)
    (hB : MinkowskiBound K < b)
    (hg : {I : Ideal Oκ | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < b} ⊆ Set.range g)
    (B : Matrix m n ℕ) (hgmul : ∀ i, ∃ (α β : Oκ), ∃ (_ : α ≠ 0), ∃ (_ : β ≠ 0),
      Ideal.span {α} * (g i) = Ideal.span {β} * ∏ j, (x j) ^ (B i j)) :
      Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (x' i))) = ⊤ := by
  refine subgroup_closure_eq_classGroup hg' hx' hB hg (A := 1) (B := B) ?_ ?_
  · use 1
    simp only [eq_natCast, CharP.cast_eq_zero, Nat.cast_one, Matrix.map_one, mul_one]
  · intro i
    obtain ⟨α, β, hα, hβ, hp ⟩ :=  hgmul i
    use α , β , hα, hβ
    rw [← hp]
    congr
    rw [Finset.prod_eq_single (M := Ideal Oκ) i ?_ ?_, Matrix.one_apply]
    simp only [↓reduceIte, pow_one]
    · intro b hb hbn
      simp only [Matrix.one_apply, pow_ite, pow_one, pow_zero, Ideal.one_eq_top, ite_eq_right_iff]
      intro hc
      exfalso
      exact hbn hc.symm
    · simp only [Finset.mem_univ, not_true_eq_false, Matrix.one_apply_eq, pow_one,
      Ideal.one_eq_top, IsEmpty.forall_iff]


open FractionalIdeal
open Pointwise

lemma FractionalIdeal.den_mul_self_eq_num'' {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
  [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
  (S₁ : Submonoid R) (S₂ : Submonoid S) [IsLocalization S₂ P] (I : FractionalIdeal S₁ P)
  (hu : IsUnit ((algebraMap R P) ↑I.den)) :
    Submodule.span S (I : Set P) =
    FractionalIdeal.coeToSubmodule ((FractionalIdeal.spanSingleton  (S := S₂) ((hu.unit.inv) : P))
      *  FractionalIdeal.coeIdeal (Ideal.map (algebraMap R S) I.num)) := by
    have aux1 := FractionalIdeal.den_mul_self_eq_num I
    apply_fun (fun x => x.carrier) at aux1
    apply_fun Submodule.span S at aux1
    simp only [Submodule.pointwise_smul_toAddSubmonoid, Submodule.carrier_eq_coe, Submodule.map_coe,
      Algebra.linearMap_apply] at aux1
    have aux := Submodule.span_smul (R := S) ((I.den)) (I : Set P)
    apply_fun (fun x => (((algebraMap R S) ↑(I.den)) • x : Submodule S P))
    simp
    convert aux1
    convert aux.symm using 1
    · rw [← aux, Submodule.smul_span]
      congr
      ext x
      simp_rw [Set.mem_smul_set, Algebra.smul_def,
        Eq.symm (IsScalarTower.algebraMap_apply R S P _), ← Algebra.smul_def]
      rfl
    · unfold Ideal.map Ideal.span
      rw [Ideal.submodule_span_eq, IsLocalization.coeSubmodule_span,
        ← Set.image_comp, Submodule.span_mul_span, ← Submodule.span_smul (algebraMap R S (I.den )) _]
      congr
      have auxf := IsScalarTower.algebraMap_eq R S P
      apply_fun (fun x => x.toFun) at auxf
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp] at auxf
      rw [← auxf, Set.singleton_mul]
      ext x
      rw [Set.mem_smul_set]
      simp only [Set.mem_image, SetLike.mem_coe, exists_exists_and_eq_and, algebraMap_smul]
      simp_rw [Algebra.smul_def, ← mul_assoc, IsUnit.mul_val_inv, one_mul]
    · refine injective_of_le_imp_le (fun x ↦ (algebraMap R S) ↑I.den • x) ?_
      intro x y hxy i hi
      dsimp at hxy
      have := hxy (Submodule.smul_mem_pointwise_smul i ((algebraMap R S) ↑I.den) x hi)
      rw [Submodule.mem_smul_pointwise_iff_exists] at this
      obtain ⟨b, hb1, hb2⟩ := this
      apply_fun (fun x => (hu.unit.inv) • x) at hb2
      simp_rw [Algebra.smul_def _ b, ← (IsScalarTower.algebraMap_apply R S P ↑I.den),
        Algebra.smul_def _ i, ← (IsScalarTower.algebraMap_apply R S P ↑I.den) , Algebra.smul_def] at hb2
      simp only [ ← mul_assoc, Algebra.id.map_eq_id, Units.inv_eq_val_inv, RingHom.id_apply, IsUnit.val_inv_mul,
        one_mul] at hb2
      rw [← hb2]
      exact hb1


noncomputable def FractionalIdeal.map_map {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    {S₁ : Submonoid R} {S₂ : Submonoid S} [IsLocalization S₂ P]
    (h : (algebraMap R S)'' S₁ ≤ S₂) : FractionalIdeal S₁ P →* FractionalIdeal S₂ P where
  toFun := by
    intro I
    have hu : IsUnit ((algebraMap R P) I.den) := by
      rw [← Eq.symm (IsScalarTower.algebraMap_apply R S P _)]
      refine IsLocalization.map_units _ (⟨(algebraMap R S) ↑I.den , ?_ ⟩ : S₂)
      apply h
      use I.den.1 , I.den.2
    let J := FractionalIdeal.spanSingleton  (S := S₂) hu.unit.inv
    let II := (Ideal.map (algebraMap R S) I.num : FractionalIdeal S₂ P)
    exact J * II
  map_one' := by
    dsimp
    apply_fun FractionalIdeal.coeToSubmodule
    have : (↑(1 : FractionalIdeal S₁ P) : Set P) = ↑(1 : Submodule R P) := by
      rw [← FractionalIdeal.coe_one]
      rfl
    erw [← FractionalIdeal.den_mul_self_eq_num'' S₁ S₂ 1 ]
    simp_rw [FractionalIdeal.coe_one, this,
      Submodule.one_eq_span, Submodule.span_span_of_tower]
    · exact coeToSubmodule_injective
  map_mul' := by
    dsimp
    intro x y
    apply_fun FractionalIdeal.coeToSubmodule
    nth_rw 2 [coe_mul]
    erw [← FractionalIdeal.den_mul_self_eq_num'', ← FractionalIdeal.den_mul_self_eq_num''
    , ← FractionalIdeal.den_mul_self_eq_num'']
    have : Submodule.span S (↑(x * y) : Set P) =
      Submodule.span S ((coeToSubmodule x) * (coeToSubmodule y)) := by
     congr
     rw [FractionalIdeal.mul_def] ; rfl
    rw [this, Submodule.mul_def, Submodule.span_span_of_tower,
      ← Submodule.span_mul_span] ; rfl
    · exact coeToSubmodule_injective

lemma FractionalIdeal.map_map_apply {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (S₁ : Submonoid R) (S₂ : Submonoid S) [IsLocalization S₂ P]
    (h : (algebraMap R S)'' S₁ ≤ S₂)
    (I : FractionalIdeal S₁ P) : FractionalIdeal.map_map h I = Submodule.span S (I : Set P) := by
      erw [← FractionalIdeal.den_mul_self_eq_num'']

lemma FractionalIdeal.map_map_apply_int {R S P : Type*} [CommRing R] [CommRing S] [CommRing P]
    [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (S₁ : Submonoid R) (S₂ : Submonoid S) [IsLocalization S₂ P]
    (h : (algebraMap R S)'' S₁ ≤ S₂) (I : Ideal R) : FractionalIdeal.map_map h (I : FractionalIdeal S₁ P) = I.map (algebraMap R S) := by
      apply_fun FractionalIdeal.coeToSubmodule
      rw [FractionalIdeal.map_map_apply, Ideal.map, coe_coeIdeal, IsLocalization.coeSubmodule_span]
      have : (↑(↑I : FractionalIdeal S₁ P) : Set P) = ↑(↑(↑I : FractionalIdeal S₁ P) : Submodule R P) := by rfl
      rw [this, FractionalIdeal.coe_coeIdeal, IsLocalization.coeSubmodule]
      simp only [Submodule.map_coe, Algebra.linearMap_apply, ←
        Eq.symm (IsScalarTower.algebraMap_apply R S P _), ← Set.image_comp, Function.comp_apply]
      exact coeToSubmodule_injective

noncomputable def FractionalIdeal.mapOfInjective {R S P : Type*} [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [CommRing P] [Algebra R S] [Algebra R P] [Algebra S P] [IsScalarTower R S P]
    (hinj : Function.Injective (algebraMap R S)) [IsFractionRing S P] :
    FractionalIdeal (nonZeroDivisors R) P →* FractionalIdeal (nonZeroDivisors S) P := by
  refine FractionalIdeal.map_map ?_
  intro x hx
  simp only [SetLike.mem_coe, mem_nonZeroDivisors_iff_ne_zero, ne_eq]
  obtain ⟨a,ha1, ha2⟩ := hx
  rw [← ha2]
  refine (map_ne_zero_iff (algebraMap R S) hinj).mpr ?_
  intro hca
  rw [hca] at ha1
  exact zero_not_mem_nonZeroDivisors ha1

-- I need these algebra instances for the fraction ring statements


noncomputable def FractionalIdeal.mapOfInjective' {R S : Type*} (F K : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [CommRing F] [CommRing K] [Algebra R F] [Algebra S K] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [IsFractionRing R F] [IsFractionRing S K] :
      FractionalIdeal (nonZeroDivisors R) F →* FractionalIdeal (nonZeroDivisors S) K := by
  letI:  Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  let ψ : F →+* K := IsFractionRing.map hinj
  let ψa : F →ₐ[R] K := by
    refine AlgHom.mk' ψ ?_
    intro c x
    rw [Algebra.smul_def c (ψ x)]
    simp [ψ, IsFractionRing.map]
    rw [IsLocalization.map_smul, Algebra.smul_def _ _]
    rfl
  haveI : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  let f : (FractionalIdeal (nonZeroDivisors R) K) →*
    (FractionalIdeal (nonZeroDivisors S) K) :=
    FractionalIdeal.mapOfInjective (hinj)
  exact
  {toFun := fun x => (f ((FractionalIdeal.map ψa) x))
   map_one' := by simp only [Function.comp_apply, FractionalIdeal.map_one, map_one, ψ]
   map_mul' := by simp only [Function.comp_apply, FractionalIdeal.map_mul, map_mul, implies_true, ψ]}


lemma FractionalIdeal.mapOfInjective_apply' {R S : Type*} (F K : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [CommRing F] [CommRing K] [Algebra R F] [Algebra S K] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [IsFractionRing R F] [IsFractionRing S K]
    (I : FractionalIdeal (nonZeroDivisors R) F) :
    FractionalIdeal.mapOfInjective' F K hinj I =
    (Submodule.span S ((IsFractionRing.map hinj)'' (↑I : Set F)) : Submodule S K) := by
  unfold mapOfInjective' mapOfInjective
  dsimp
  simp_rw [FractionalIdeal.map_map_apply]
  rfl

lemma FractionalIdeal.mapOfInjective_apply_int' {R S : Type*} (F K : Type*) [CommRing R] [Nontrivial R]
    [CommRing S] [IsDomain S] [CommRing F] [CommRing K] [Algebra R F] [Algebra S K] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) [IsFractionRing R F] [IsFractionRing S K]
    (I : Ideal R) :
    FractionalIdeal.mapOfInjective' F K hinj I = Ideal.map (algebraMap R S) I := by
  apply_fun FractionalIdeal.coeToSubmodule
  rw [FractionalIdeal.mapOfInjective_apply', Ideal.map, coe_coeIdeal, IsLocalization.coeSubmodule_span]
  congr
  ext i
  unfold IsFractionRing.map
  simp only [Set.mem_image, SetLike.mem_coe, mem_coeIdeal, exists_exists_and_eq_and,
    IsLocalization.map_eq]
  · exact coeToSubmodule_injective

-- I need to ask for the ringHom to be injective, in order to induce a morphism
-- between fraction rings:
noncomputable def ClassGroup.map {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain R] [IsDomain S] {φ : R →+* S} (hinj : Function.Injective φ) :
    ClassGroup R →* ClassGroup S := by
  let F := FractionRing R
  let K := FractionRing S
  letI : Algebra R S := φ.toAlgebra
  letI :  Algebra R K := ((algebraMap S K).comp (algebraMap R S)).toAlgebra
  letI : Module R K := Algebra.toModule
  haveI :=  IsScalarTower.of_algebraMap_eq (R := R) (S := S) (A := K) (congrFun rfl)
  let ψ : F →+* K := IsFractionRing.map hinj
  unfold ClassGroup
  let g : (FractionalIdeal (nonZeroDivisors R) F) →*
    (FractionalIdeal (nonZeroDivisors S) K) := FractionalIdeal.mapOfInjective' _ _ hinj
  refine QuotientGroup.map _ _ (Units.map g) ?_
  · intro x hx
    simp only [MonoidHom.mem_range, toPrincipalIdeal_eq_iff, Subgroup.mem_comap, Units.coe_map, K,
      this, F, ψ] at hx ⊢
    obtain ⟨a, ha⟩ := hx
    use (Units.map ψ) a
    rw [← ha]
    unfold g
    have : ∀ x, (mapOfInjective' _ _ hinj).toFun x =
      (mapOfInjective' (F := (FractionRing R)) (K:= FractionRing S) hinj) x  := fun x => rfl
    rw [← this]
    unfold mapOfInjective'
    dsimp
    simp only [Units.coe_map, MonoidHom.coe_coe, FractionalIdeal.map, coe_spanSingleton,
      Submodule.map_span, AlgHom.toLinearMap_apply, Set.image_singleton, *]
    unfold FractionalIdeal.mapOfInjective
    apply_fun FractionalIdeal.coeToSubmodule
    simp_rw [FractionalIdeal.map_map_apply,  ← ha, coe_spanSingleton, Submodule.map_span]
    simp only [AlgHom.toLinearMap_apply, Set.image_singleton, *]
    rw [← @Submodule.span_span_of_tower (R := R) _ (S:= S) _ _ _ _ _ ]
    rfl
    · exact coeToSubmodule_injective

-- I need algebra instance to exist for FractionalIdeal.mapOfInjective'
def ClassGroup.map_apply {R S : Type*} [CommRing R]
    [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S] (hinj : Function.Injective (algebraMap R S))
    (I : (FractionalIdeal (nonZeroDivisors R) (FractionRing R))ˣ) :
    ClassGroup.map hinj (ClassGroup.mk I) =
      ClassGroup.mk ((Units.map (FractionalIdeal.mapOfInjective' _ (FractionRing S) hinj)) I) := by
  unfold ClassGroup.map
  simp only  [QuotientGroup.map_mk]
  unfold ClassGroup.mk
  simp only [canonicalEquiv_self, QuotientGroup.coe_mk']
  rfl


lemma ClassGroup.map_apply' {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  (φ : R →+* S) (hinj : Function.Injective φ)
  (I : nonZeroDivisors (Ideal R)) (J : nonZeroDivisors (Ideal S))
  (hI : ↑J = Ideal.map φ I) : ClassGroup.map hinj (mk0 I) = mk0 J := by
    letI : Algebra R S := φ.toAlgebra
    rw [← ClassGroup.mk_mk0 (K := FractionRing R), ClassGroup.map_apply hinj,
      ← ClassGroup.mk_mk0 (K := FractionRing S)]
    congr
    have : ((FractionalIdeal.mk0 (FractionRing R)) I :
      FractionalIdeal (nonZeroDivisors R) (FractionRing R)) = I := by rfl
    erw [← Units.eq_iff, Units.coe_map, this,
      FractionalIdeal.mapOfInjective_apply_int', ← hI]
    rfl


-- Note that to construct any inverse map of class groups induced by an inverse map (right or left)
--  of 'φ', we need to assume it is injective and thus φ is an iso.

def ClassGroup.map_inverse_apply {R S : Type*} [CommRing R]
  [CommRing S] [IsDomain R] [IsDomain S] (φ : R ≃+* S) (I : ClassGroup R) :
    ClassGroup.map (φ := φ.symm.toRingHom) (RingEquiv.injective φ.symm)
      (ClassGroup.map (φ := φ.toRingHom) (RingEquiv.injective φ) I) = I := by
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra S R := φ.symm.toRingHom.toAlgebra
  let J := Quot.out I
  have : ClassGroup.mk J = I := by rw [← ClassGroup.Quot_mk_eq_mk, Quot.out_eq]
  simp_rw [← this, ClassGroup.map_apply (RingEquiv.injective φ) J,
    ClassGroup.map_apply (RingEquiv.injective φ.symm) _]
  congr
  show ((Units.map (mapOfInjective' (FractionRing S) (FractionRing R) (RingEquiv.injective φ.symm))).comp
    (Units.map (mapOfInjective' (FractionRing R) (FractionRing S) (RingEquiv.injective φ)))) J = J
  rw [← Units.map_comp, ← Units.eq_iff, Units.coe_map]
  simp only [MonoidHom.coe_comp, Function.comp_apply]
  apply_fun FractionalIdeal.coeToSubmodule
  simp_rw [FractionalIdeal.mapOfInjective_apply' _ _ (RingEquiv.injective φ.symm), ← FractionalIdeal.coeToSet_coeToSubmodule]
  simp_rw [FractionalIdeal.mapOfInjective_apply' _ _ (RingEquiv.injective φ)]
  let φsymml : (FractionRing S) →ₛₗ[φ.symm.toRingHom] (FractionRing R) :=
    { toFun := IsFractionRing.map (j := φ.symm.toRingHom) (RingEquiv.injective φ.symm)
      map_add' := by simp only [map_add, implies_true]
      map_smul' := by
        intro x m
        simp only [IsFractionRing.map, IsLocalization.map_smul] }
  haveI : RingHomSurjective φ.symm.toRingHom := by
    refine { is_surjective := RingEquiv.surjective φ.symm }
  have := Submodule.map_coe φsymml ↑(Submodule.span S ((IsFractionRing.map (j := φ.toRingHom) (RingEquiv.injective φ)) '' (↑J : Set (FractionRing R))))
  erw [← this, Submodule.span_image, Submodule.span_span, ← Submodule.span_image, ← Set.image_comp]
  suffices heqid : ⇑φsymml ∘ ⇑(IsFractionRing.map (j := φ.toRingHom) ((RingEquiv.injective φ))) = id by
    rw [heqid]
    simp only [id_eq, Set.image_id']
    rw [← FractionalIdeal.coeToSet_coeToSubmodule J.val]
    simp only [Submodule.span_coe_eq_restrictScalars, Submodule.restrictScalars_self]
  · unfold φsymml
    simp only [RingEquiv.toRingHom_eq_coe, IsFractionRing.map, LinearMap.coe_mk, AddHom.coe_mk]
    ext x
    simp only [Function.comp_apply, IsLocalization.map_map, RingEquiv.symm_comp,
      IsLocalization.map_id, id_eq]
  · exact coeToSubmodule_injective

noncomputable def ClassGroup.congr {R S : Type*} [CommRing R]
  [CommRing S] [IsDomain R] [IsDomain S] (φ : R ≃+* S) : ClassGroup R ≃* ClassGroup S where
  toFun := ClassGroup.map (RingEquiv.injective φ)
  invFun := ClassGroup.map (RingEquiv.injective φ.symm)
  map_mul' := fun x y ↦ MonoidHom.map_mul (map (RingEquiv.injective φ)) x y
  left_inv := by
    intro I
    exact ClassGroup.map_inverse_apply φ I
  right_inv := by
    intro J
    exact ClassGroup.map_inverse_apply φ.symm J



/-


    --simp?
    --erw [Submodule.map_coe φsymml]
    --simp_rw [← Submodule.span_image (f := IsFractionRing.map (RingEquiv.injective φ))]


    --rw [← Units.map_comp (N := FractionalIdeal (nonZeroDivisors S) (FractionRing S)) (M := FractionalIdeal (nonZeroDivisors R) (FractionRing R)) _ _]
    --simp_rw [FractionalIdeal.mapOfInjective_apply']









#exit



    --simp only [Units.coe_map, MonoidHom.coe_coe, g, K, this, F, ψ]





  --let ff : (FractionalIdeal (nonZeroDivisors R) (FractionRing S))ˣ →* (FractionalIdeal (nonZeroDivisors S) (FractionRing S))ˣ := by
  --  exact Units.map f
  --  rintro ⟨I, hI⟩



  --refine QuotientGroup.map _ _ ?_ ?_



      --show c • ψ x = (OreLocalization.numeratorRingHom.comp (algebraMap R K) r) * ψ x
    --(algebraMap R K c) * ψ x := Algebra.smul_def c (ψ x)
    --unfold K at this

   -- simp [ψ, hinj, IsFractionRing.map, IsLocalization.map]
    --expose_names
    --have := (IsLocalization.lift (IsLocalization.map._proof_15 K φ (IsFractionRing.map._proof_23 hinj))) c x)
    --rw[ map_smul ]


    --(IsLocalization.lift (IsLocalization.map._proof_15 K φ (IsFractionRing.map._proof_23 hinj))) c x)
    --erw [OreLocalization.numeratorRingHom_apply]

  --letI : Algebra R K := {


  --}










#exit
-- We assume Dedekind domain to make the proof easier, since we can use mk0.
noncomputable def ClassGroup.map0 {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [IsDomain R] [IsDomain S]
  (φ : R →+* S) (hinj : Function.Injective φ) : ClassGroup R →* ClassGroup S where
    toFun := by
      intro I
      choose J hJ using ClassGroup.mk0_surjective I
      have : Ideal.map φ J.val ∈ nonZeroDivisors (Ideal S) := by
        simp only [mem_nonZeroDivisors_iff_ne_zero,
        Submodule.zero_eq_bot, ne_eq]
        rw [Ideal.map_eq_bot_iff_le_ker]
        simp only [(RingHom.injective_iff_ker_eq_bot _).1 hinj, le_bot_iff]
        intro hc
        exact (mem_nonZeroDivisors_iff_ne_zero.1 J.2) hc
      exact (mk0 ⟨_, this⟩ )
    map_one' := by
      dsimp
      have := Classical.choose_spec (mk0_surjective (1  : ClassGroup R))
      erw [ClassGroup.mk0_eq_one_iff]
      apply Submodule.IsPrincipal.map_ringHom
      rw [← ClassGroup.mk0_eq_one_iff]
      exact this
    map_mul' := by
      dsimp
      intro x y
      have hxy := Classical.choose_spec (mk0_surjective (x * y  : ClassGroup R))
      have hx:= Classical.choose_spec (mk0_surjective (x  : ClassGroup R))
      have hy := Classical.choose_spec (mk0_surjective (y  : ClassGroup R))
      rw [← map_mul, ClassGroup.mk0_eq_mk0_iff]
      rw [← hx, ← hy, ← map_mul, ClassGroup.mk0_eq_mk0_iff] at hxy
      obtain ⟨a, b, ha, hb, hab⟩ := hxy
      use φ a, φ b, ((map_ne_zero_iff φ hinj).mpr ha) ,  ((map_ne_zero_iff φ hinj).mpr hb)
      apply_fun (fun I => Ideal.map φ I) at hab
      simp only [map_mul, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
        Submonoid.coe_mul, hx, hy] at hab
      convert hab

lemma ClassGroup.map0_apply {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [IsDomain R] [IsDomain S]
  (φ : R →+* S) (hinj : Function.Injective φ)
  (I : nonZeroDivisors (Ideal R)) (J : nonZeroDivisors (Ideal S))
  (hI : ↑J = Ideal.map φ I) : ClassGroup.map0 φ hinj (mk0 I) = mk0 J := by
  have haux := Classical.choose_spec (mk0_surjective (mk0 I  : ClassGroup R))
  unfold map0
  dsimp
  rw [ClassGroup.mk0_eq_mk0_iff] at haux ⊢
  obtain ⟨a, b, ha, hb, hab⟩ := haux
  use φ a, φ b, ((map_ne_zero_iff φ hinj).mpr ha) ,  ((map_ne_zero_iff φ hinj).mpr hb)
  apply_fun (fun I => Ideal.map φ I) at hab
  simp only [map_mul, Ideal.map_mul, Ideal.map_span, Set.image_singleton,
        Submonoid.coe_mul, ← hI] at hab
  exact hab


noncomputable def ClassGroup.equiv0 {R S : Type*} [CommRing R]
  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
  [IsDomain R] [IsDomain S] (φ : R ≃+* S) : ClassGroup R ≃* ClassGroup S := by
  refine MulEquiv.ofBijective (ClassGroup.map0 (R := R) (S := S) φ (RingEquiv.injective φ)) ?_
  constructor
  · rw [← MonoidHom.ker_eq_bot_iff]
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro h
      let I := Classical.choose (mk0_surjective (x  : ClassGroup R))
      have haux : Ideal.map φ I ∈ nonZeroDivisors (Ideal S) := by
        simp only [mem_nonZeroDivisors_iff_ne_zero,
        Submodule.zero_eq_bot, ne_eq]
        rw [Ideal.map_eq_bot_iff_le_ker]
        simp only [RingHom.ker_equiv, le_bot_iff]
        intro hc
        exact (mem_nonZeroDivisors_iff_ne_zero.1 I.2) hc
      have hx := Classical.choose_spec (mk0_surjective (x  : ClassGroup R))
      rw [← hx] at h
      rw [ClassGroup.map0_apply (R := R) (S := S) φ (RingEquiv.injective φ) _
        ⟨_, haux⟩  rfl , ClassGroup.mk0_eq_one_iff] at h
      obtain ⟨s, hs⟩ := h
      rw [← hx, ClassGroup.mk0_eq_one_iff]
      use φ.symm s
      apply_fun (fun I => Ideal.map φ.symm I) at hs
      erw [Ideal.map_of_equiv, Ideal.map_span, Set.image_singleton] at hs
      rw [hs]
      rfl
    ·  intro h
       simp only [h, map_one]
  · intro y
    have hy := Classical.choose_spec (mk0_surjective (y  : ClassGroup S))
    use ClassGroup.map0 φ.symm (RingEquiv.injective φ.symm) y
    rw [← hy]
    apply ClassGroup.map0_apply
    erw [Ideal.map_of_equiv, hy]

-/

lemma primes_below_bound_of_equiv {m} {R S : Type*} [CommRing R] [CommRing S]
    (φ : R ≃+* S) {g : m → Ideal R} (b : ℕ)
    (h : {I : Ideal S | 0 < Nat.card (S ⧸ I) ∧ I.IsPrime ∧ Nat.card (S ⧸ I) < b} ⊆ Set.range (Ideal.map φ ∘ g)) :
    {I : Ideal R | 0 < Nat.card (R ⧸ I) ∧ I.IsPrime ∧ Nat.card (R ⧸ I) < b} ⊆ Set.range g := by
  rintro I hImem
  have hcard : ∀ (J : Ideal R), Nat.card (R ⧸ I) = Nat.card (S ⧸ (I.map φ)) := by
    intro J
    refine Nat.card_congr ?_
    exact (Ideal.quotientEquiv I (I.map φ) φ rfl).toEquiv
  have hprime : ∀ (J : Ideal R) , J.IsPrime ↔ (J.map φ).IsPrime := by
    intro J
    constructor
    · intro hx ; exact Ideal.map_isPrime_of_equiv φ
    · intro hx
      convert Ideal.map_isPrime_of_equiv φ.symm (I := (Ideal.map φ J))
      erw [Ideal.map_of_equiv]
  have : I.map φ ∈ Set.range (Ideal.map φ ∘ g) := by
    apply h
    dsimp
    rw [← hcard I , ← hprime I]
    exact hImem
  suffices haux : Ideal.map φ.symm (Ideal.map φ I) ∈ (Ideal.map φ.symm)'' (Set.range (Ideal.map φ ∘ g)) by
    erw [← Set.range_comp, Ideal.map_of_equiv] at haux
    convert haux
    ext i
    simp only [Function.comp_apply, Ideal.map_symm, Ideal.mem_comap, Ideal.apply_mem_of_equiv_iff]
  exact Set.mem_image_of_mem (Ideal.map φ.symm) this


      --exact mk0


  --refine MulEquiv.ofBijective


   -- exact mk0 ⟨Ideal.map equiv J, by simp only [mem_nonZeroDivisors_iff_ne_zero,
   --   Submodule.zero_eq_bot, ne_eq]; rw [Ideal.map_eq_bot_iff_le_ker]⟩


-- This is useful when the subalgebra O is not definitionally equal to Oκ
lemma subgroup_closure_eq_classGroup'' {m n r : Type} {b : ℕ}
    [hn : Fintype n] [hm : Fintype m] [Fintype r] [DecidableEq m]
    {O : Subalgebra ℤ K} [IsDedekindDomain ↥O] [Module.Free ℤ ↥O]
    ( φ : O ≃+* Oκ)
    {g : m → Ideal O} {g' : m → nonZeroDivisors (Ideal (O))}
    {x : n → Ideal O} {x' : n → nonZeroDivisors (Ideal (O))}
    (hg' : ∀ i, ↑(g' i) = g i) (hx' : ∀ i, ↑(x' i) = x i)
    (hB : MinkowskiBound K < b)
    (hg : {I : Ideal O | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < b} ⊆ Set.range g)
    (B : Matrix m n ℕ) (hgmul : ∀ i, ∃ (α β : O), ∃ (_ : α ≠ 0), ∃ (_ : β ≠ 0),
      Ideal.span {α} * (g i) = Ideal.span {β} * ∏ j, (x j) ^ (B i j)) :
      Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (x' i))) = ⊤ := by
  --let φ : O ≃+* Oκ := (O.equivOfEq _ heq).toRingEquiv. No need to assume equality of subalgebras.
  let gg : m → Ideal Oκ := fun i => Ideal.map φ (g i)
  let xx : n → Ideal Oκ := fun i => Ideal.map φ (x i)
  have hgaux : ∀ i, (g' i).val ≠ ⊥ := fun i => nonZeroDivisors.ne_zero (g' i).2
  have hxaux : ∀ i, (x' i).val ≠ ⊥ := fun i => nonZeroDivisors.ne_zero (x' i).2
  have hgg: ∀ i, Ideal.map φ (g' i).val ∈ nonZeroDivisors (Ideal Oκ) := by
    intro i
    rw [mem_nonZeroDivisors_iff_ne_zero (M₀ := Ideal Oκ), Submodule.zero_eq_bot, ne_eq, Ideal.map_eq_bot_iff_le_ker, RingHom.ker_equiv, le_bot_iff]
    exact hgaux i
  have hxx: ∀ i, Ideal.map φ (x' i).val ∈ nonZeroDivisors (Ideal Oκ) := by
    intro i
    rw [mem_nonZeroDivisors_iff_ne_zero (M₀ := Ideal Oκ), Submodule.zero_eq_bot, ne_eq, Ideal.map_eq_bot_iff_le_ker, RingHom.ker_equiv, le_bot_iff]
    exact hxaux i
  let gg' : m → nonZeroDivisors (Ideal Oκ) := fun i => ⟨Ideal.map φ (g' i).val, hgg i⟩
  let xx' : n → nonZeroDivisors (Ideal Oκ) := fun i => ⟨Ideal.map φ (x' i).val, hxx i⟩
  have : IsDedekindDomain ↥(integralClosure ℤ K) := by
    show IsDedekindDomain Oκ
    exact NumberField.RingOfIntegers.instIsDedekindDomain K
  let E : ClassGroup ↥O ≃* ClassGroup Oκ := ClassGroup.congr φ
  apply_fun (Subgroup.map (G := ClassGroup O) (N := ClassGroup Oκ) E)
  · rw [Subgroup.map_top_of_surjective _ (by exact EquivLike.surjective E)]
    rw [MonoidHom.map_closure]
    convert subgroup_closure_eq_classGroup' (K := K) (m := m) (n := n)
      (r := r) (b := b) (g := gg) (x := xx) (g' := gg') (x' := xx') ?_ ?_ hB ?_ B ?_
    · rw [← Set.range_comp]
      refine (congr_arg _ ?_)
      ext i
      simp only [ClassGroup.congr, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.toRingEquiv_toRingHom,
        MonoidHom.coe_coe, Function.comp_apply, MulEquiv.ofBijective_apply, E]
      apply ClassGroup.map_apply'
      rfl
    · intro i
      simp only [hg', gg, E, gg']
    · intro i
      simp only [hx', xx, E, gg, gg', xx']
    · convert primes_below_bound_of_equiv φ.symm (g := gg) b ?_
      convert hg
      ext i
      simp only [Function.comp_apply, Ideal.map_symm, Ideal.mem_comap, Ideal.apply_mem_of_equiv_iff,
        gg, gg', xx', xx, E]
    · intro i
      obtain ⟨α, β, hα, hβ, hαβ⟩ := hgmul i
      use (φ α), φ β, (EmbeddingLike.map_ne_zero_iff.mpr hα) ,(EmbeddingLike.map_ne_zero_iff.mpr hβ)
      simp [gg, xx]
      apply_fun (Ideal.map φ) at hαβ
      simp only [Ideal.map_mul, Ideal.map_span, Set.image_singleton,
        Submonoid.coe_mul] at hαβ
      convert hαβ
      let φaux := Ideal.mapHom φ
      have hIaux : ∀ I , Ideal.map φ I = φaux I := by
        intro I
        rfl
      simp_rw [hIaux, ← map_pow]
      rw [map_prod]
  · refine Subgroup.map_injective (EquivLike.injective E)


----------------------------------------------------------------------------------
/- How should I store the prime ideal info?
Maybe as a list of pairs ℕ × Ideal O, carrying ⟨p, I⟩ with I a prime ideal above p?
It's better do it local and then reconstruct it. Create a structure for each p.
Then a bigger one that proves that it is for all p's below certain bound, and
cetrtificates for each multiplication.

It seems to be better to use Lists instead of functions because, although the first allows for
easier indexing, the second has the flatten function which is rather useful.

Actually, I also need to store the norms of the ideals. So maybe it is better to use
Fn's.
-/

structure PrimesBelowPCertificate {S : Type*} [CommRing S] (p : ℕ) {g : ℕ} (F : Fin g → Ideal S) where
  Ip : ∀ i, (F i).IsPrime
  hPprod : ∏ i, F i = Ideal.span {↑p}

#eval Nat.primesBelow 100


-- Turns out it's better to use lists to encode the factorizations. Because pattern matching with large n
-- is annoying? Still not sure about this.

structure PrimesBelowBoundCertificate (S : Type*) [CommRing S] [Nontrivial S] (B : ℕ) where
  m : ℕ
  g : Fin m → ℕ
  P : Fin m → ℕ
  hP : Set.range P = Nat.primesBelow B
  I : Π i,  Fin (g i) → (Ideal S) -- Factorization for the i-th prime.
  hC : ∀ i : Fin m, PrimesBelowPCertificate (P i) (I i)
  N :  Π i,  Fin (g i) → ℕ -- Norms corresponding to the factorization of the i-th prime.
  hN : ∀ i, ∀ j, Nat.card (S ⧸ I i j) = N i j
  Il : Fin m → List (Ideal S) -- List of ideals over the i-th prime, with norm less than B
  hIl : ∀ i, List.map (Prod.fst) (List.filter (λ p => p.2 < B) (List.zip (List.ofFn (I i)) (List.ofFn (N i)))) = Il i

/-- Collects the prime ideals above the primes in the interval (A, B] but that have norm less than C -/
structure PrimesBelowBoundCertificateInterval (S : Type*) [CommRing S] [Nontrivial S] (A B : ℕ) (C : ℕ) where
  m : ℕ
  g : Fin m → ℕ
  P : Fin m → ℕ
  hP : ∀ p, p ∈ Set.range P ↔ Nat.Prime p ∧ A < p ∧ p ≤ B
  I : Π i,  Fin (g i) → (Ideal S) -- Factorization for the i-th prime.
  hC : ∀ i : Fin m, PrimesBelowPCertificate (P i) (I i)
  N :  Π i,  Fin (g i) → ℕ -- Norms corresponding to the factorization of the i-th prime.
  hN : ∀ i, ∀ j, Nat.card (S ⧸ I i j) = N i j
  Il : Fin m → List (Ideal S) -- List of ideals over the i-th prime, with norm less than B
  hIl : ∀ i, List.map (Prod.fst) (List.filter (λ p => p.2 < C) (List.zip (List.ofFn (I i)) (List.ofFn (N i)))) = Il i



def Fin.addCasesIter {α : Type*} {r : ℕ} (e : Fin r → ℕ) (g : ∀ i, Fin (e i) → α) :
  Fin (∑ i, e i) → α := by
  revert e
  induction' r with r hr
  · exact fun e he =>  Fin.elim0
  · intro e g
    exact (Fin.addCases ((hr (fun i => e i.castSucc) (fun i => g i.castSucc)) ) (g (last r))) ∘ (Fin.cast (Fin.sum_univ_castSucc e))

lemma List.ofFn_addCases {n m} {α} (left : Fin m → α) (right : Fin n → α) :
  List.ofFn (Fin.addCases left right) = List.ofFn left ++ List.ofFn right := by
  simp_rw [List.ofFn_add, Fin.addCases_left, Fin.addCases_right]

lemma List.addCases_comp {n m} {α} (f : Fin m → α)  (eq : n = m) :
  List.ofFn (f ∘ (Fin.cast eq))  = List.ofFn f := by
  refine ofFn_inj'.mpr ?_
  ext
  · exact eq
  · exact (Fin.heq_fun_iff eq).mpr (congrFun rfl)

lemma List.ofFn_addCasesIter {α : Type*} {r : ℕ} (e : Fin (r + 1) → ℕ) (g : ∀ i, Fin (e i) → α) :
  List.ofFn (Fin.addCasesIter e g) =
    List.ofFn (Fin.addCasesIter (fun i => e i.castSucc) (fun (i : Fin r) => g i.castSucc)) ++ List.ofFn (g (Fin.last r)) := by
  match r with
  | 0 =>
    simp [Fin.addCasesIter, Fin.addCases]
    rfl
  | r =>
    unfold Fin.addCasesIter
    simp_rw [List.addCases_comp, List.ofFn_addCases]
    rfl


def indexPair {r : ℕ} (e : Fin r → ℕ) (j : Fin (∑ i, e i)) : Σ (i : Fin r), Fin (e i) := by
  revert e
  induction' r with r hr
  · intro e j
    exact ⟨j, IsEmpty.elim (α := Fin 0) (p := fun (i : Fin 0) => Fin (e i)) (Fin.isEmpty') j⟩
  · intro e j
    let e' : Fin r → ℕ := fun i => e i.castSucc
    by_cases h : j < ∑ (i : Fin r), e i.castSucc
    · obtain ⟨i, hi⟩ := hr e' ⟨↑j, h⟩
      exact ⟨i.castSucc, hi⟩
    · let j' := Fin.subNat (∑ (i : Fin r), e i.castSucc) (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc ) by rw [Fin.sum_univ_castSucc, add_comm]) j)
      refine ⟨Fin.last r, ?_⟩
      refine j' ?_
      simp only [Fin.coe_cast]
      omega


lemma indexPair_left_aux {r : ℕ} {e : Fin (r + 1) → ℕ} {j : Fin (∑ i, e i)} (h : j < ∑ (i : Fin r), e i.castSucc) :
  indexPair e j = ⟨Fin.castSucc (indexPair (fun (i : Fin r) => e i.castSucc) ⟨↑j, h⟩).1,  (indexPair (fun (i : Fin r) => e i.castSucc) ⟨↑j, h⟩).2 ⟩ := by
  unfold indexPair
  unfold Nat.recAux
  simp only [h, ↓reduceDIte, Fin.coe_cast]

lemma indexPair_right_aux {r : ℕ} {e : Fin (r + 1) → ℕ} {j : Fin (∑ i, e i)} (h : ¬ j < ∑ (i : Fin r), e i.castSucc) :
  indexPair e j = ⟨Fin.last r, Fin.subNat (∑ (i : Fin r), e i.castSucc)
    (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc ) by rw [Fin.sum_univ_castSucc, add_comm]) j) (by simp only [Fin.coe_cast] ;  omega)⟩ := by
  unfold indexPair
  unfold Nat.recAux
  simp only [h, ↓reduceDIte, Fin.coe_cast]

noncomputable def indexPairEquiv {r : ℕ} (e : Fin r → ℕ) : Fin (∑ i, e i) ≃  Σ (i : Fin r), Fin (e i) := by
  apply Equiv.ofBijective (indexPair e)
  rw [Nat.bijective_iff_injective_and_card]
  constructor
  · revert e
    induction' r with r hr
    · simp only [Fin.forall_fin_zero_pi]
      unfold indexPair ; dsimp
      intro x y
      simp only [Sigma.mk.injEq, heq_eq_eq, and_imp]
      exact fun hx hxy => hx
    · intro e
      intro x y hxy
      by_cases h1 : x < ∑ (i : Fin r), e i.castSucc
      · by_cases h2 : y < ∑ (i : Fin r), e i.castSucc
        · rw [indexPair_left_aux h1, indexPair_left_aux h2] at hxy
          simp at hxy
          have := (Function.Injective.eq_iff (hr (fun i ↦ e i.castSucc)) (a := ⟨x, h1⟩) (b := ⟨y, h2⟩)).1 (Sigma.ext_iff.mpr hxy)
          simp only [Fin.mk.injEq] at this
          exact Fin.eq_of_val_eq this
        · rw [indexPair_left_aux h1, indexPair_right_aux h2] at hxy
          simp only [Sigma.mk.injEq, Fin.castSucc_ne_last, false_and] at hxy
      · by_cases h2 : y < ∑ (i : Fin r), e i.castSucc
        · rw [indexPair_right_aux h1, indexPair_left_aux h2, Eq.comm] at hxy
          simp only [Sigma.mk.injEq, Fin.castSucc_ne_last, false_and] at hxy
        · rw [indexPair_right_aux h1, indexPair_right_aux h2] at hxy
          simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hxy
          rw [Fin.subNat_mk, Fin.subNat_mk] at hxy
          simp only [Fin.coe_cast, Fin.mk.injEq] at hxy
          omega
  · simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_sigma]


lemma addCasesIter_apply {α : Type*} {r : ℕ} (e : Fin r → ℕ) (g : ∀ i, Fin (e i) → α) (j : Fin (∑ i, e i)) :
    Fin.addCasesIter e g j = g (indexPair e j).1 (indexPair e j).2 := by
  revert e
  induction' r with r hr
  · intro e g j
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at j
    exfalso
    exact Fin.isEmpty'.false j
  · intro e g j
    let e' := (fun (i : Fin r) => e i.castSucc)
    let g' := (fun (i : Fin r) => g i.castSucc)
    let f :=  Fin.addCasesIter e' g'
    have : Fin.addCasesIter e g = (Fin.addCases f (g (Fin.last r))) ∘ (Fin.cast (Fin.sum_univ_castSucc e))  := rfl
    rw [this, Function.comp_apply]
    let t := g (Fin.last r)
    by_cases h : j < ∑ (i : Fin r), e i.castSucc
    · have : (Fin.cast (Fin.sum_univ_castSucc e) j) = (Fin.castAdd (e (Fin.last r)) (⟨j, h⟩ )) := by rfl
      rw [this, Fin.addCases_left]
      simp only [hr e' g' ⟨j, h⟩, f, e', g']
      rw [indexPair_left_aux]
    · have : (Fin.cast (Fin.sum_univ_castSucc e) j) =
        (Fin.natAdd (∑ (i : Fin r), e i.castSucc) (Fin.subNat (∑ (i : Fin r), e i.castSucc)
        (Fin.cast (show ( ∑ i, e i = e (Fin.last r) + ∑ (i : Fin r), e i.castSucc )
        by rw [Fin.sum_univ_castSucc, add_comm]) j) (by simp only [Fin.coe_cast] ;  omega))) := by
        erw [Fin.natAdd_subNat_cast (i := Fin.cast (Fin.sum_univ_castSucc e) j )]
      rw [this, Fin.addCases_right, indexPair_right_aux h]



-- Tried defining e with lists, but again, for indexing is easier to do it as Fin r → ℕ.
-- Specially true for indexing to range over the certificates.
--(hn : e ≠ [])
 --(he : List.Sorted (fun x y => x < y) e)
 --(h0 : e[0]'(List.length_pos_iff.2 hn) = 1)
 --(hl : e.getLast hn = B)
def primesBelowBoundCertificate_of_Interval (S : Type*) [CommRing S] [Nontrivial S]
  {r : ℕ} (e : Fin (r + 1) → ℕ) (B : ℕ) (h0 : e 0 = 1) (hr : e (Fin.last r) = B)
  (hl : ∀ (i : Fin r), e i.castSucc  < e (i.castSucc + 1))
  (hC : ∀ (i : Fin r), PrimesBelowBoundCertificateInterval S (e i.castSucc) (e (i.castSucc + 1)) (B + 1)) :
    PrimesBelowBoundCertificate S (B + 1) where
 m := ∑ (i : Fin r), (hC i).m
 g := Fin.addCasesIter (fun (i : Fin r) => (hC i).m) (fun i => (hC i).g)
 P := Fin.addCasesIter (fun (i : Fin r) => (hC i).m) (fun i => (hC i).P)
 hP := by
  ext p
  simp only [Set.mem_range, Finset.mem_coe, Nat.mem_primesBelow]
  have auxe : ∀ k, e k < B + 1 := by
    intro k
    refine Fin.reverseInduction ?_ ?_ k
    · simp only [hr, lt_add_iff_pos_right, Nat.lt_one_iff, pos_of_gt]
    · intro i hr
      refine lt_trans (hl i ) ?_
      simp only [Fin.coeSucc_eq_succ, hr]
  constructor
  · rintro ⟨y, hy⟩
    rw [addCasesIter_apply] at hy
    have := (hC ((indexPair (fun i ↦ (hC i).m) y).fst)).hP p
    simp at this
    obtain ⟨hp, hl1,hl2⟩  := this.1 ⟨(indexPair (fun i ↦ (hC i).m) y).2, hy⟩
    refine ⟨lt_of_le_of_lt hl2 (auxe _) , hp⟩
  · rintro ⟨hpB, hp⟩
    have : ∃ (k : Fin r), e k.castSucc < p ∧ p ≤ e (k.castSucc + 1) := by
      by_contra! hc
      have : ∀ k, e k < p := by
        refine Fin.induction ?_ ?_
        · rw [h0]
          exact Nat.Prime.one_lt hp
        · convert hc
          simp only [Fin.coeSucc_eq_succ]
      specialize this (Fin.last r)
      rw [hr] at this
      linarith
    obtain ⟨k, hk⟩ := this
    have := ((hC k).hP p ).2 ⟨hp, hk⟩
    simp at this
    obtain ⟨j, hj⟩ := this
    use (indexPairEquiv ((fun (i : Fin r) => (hC i).m))).symm ⟨k, j⟩
    rw [addCasesIter_apply]
    have : (indexPair (fun i ↦ (hC i).m) ((indexPairEquiv fun i ↦ (hC i).m).symm ⟨k, j⟩)).fst = k := by
      unfold indexPairEquiv ; simp_rw [Equiv.ofBijective_apply_symm_apply]
    convert hj
    refine (Fin.heq_ext_iff ?_).mpr ?_
    congr
    unfold indexPairEquiv
    rw [Equiv.ofBijective_apply_symm_apply (indexPair (fun i ↦ (hC i).m) ) _ ⟨k, j⟩]
 I := by
  intro k
  exact (hC ((indexPair (fun i ↦ (hC i).m) k).1)).I ((indexPair (fun i ↦ (hC i).m) k).2) ∘ (Fin.cast (addCasesIter_apply _ _ _))
 hC := by
  intro k
  simp_rw [addCasesIter_apply]
  convert (hC (indexPair (fun i ↦ (hC i).m) k).1).hC (indexPair (fun i ↦ (hC i).m) k).2
  rw [addCasesIter_apply]
  (expose_names; exact (Fin.heq_fun_iff e_4).mpr (congrFun rfl))
 N := by
  intro k
  exact (hC ((indexPair (fun i ↦ (hC i).m) k).1)).N ((indexPair (fun i ↦ (hC i).m) k).2) ∘ (Fin.cast (addCasesIter_apply _ _ _))
 hN := by
  intro k l
  exact (hC (indexPair (fun i ↦ (hC i).m) k).1).hN (indexPair (fun i ↦ (hC i).m) k).2 ((Fin.cast (addCasesIter_apply _ _ k)) l)
 Il := Fin.addCasesIter (fun (i : Fin r) => (hC i).m) (fun i => (hC i).Il)
 hIl := by
  intro k
  conv => right ; rw [addCasesIter_apply]
  convert (hC (indexPair (fun i ↦ (hC i).m) k).1).hIl (indexPair (fun i ↦ (hC i).m) k).2
  · rw [addCasesIter_apply]
  · (expose_names; exact (Fin.heq_fun_iff e_2).mpr (congrFun rfl))
  · exact addCasesIter_apply (fun i ↦ (hC i).m) (fun i ↦ (hC i).g) k
  · (expose_names; exact (Fin.heq_fun_iff e_2).mpr (congrFun rfl))





/- structure PrimesBelowPCertificate {S : Type*} [CommRing S] (p : ℕ) (F : List (Ideal S)) where
  Ip : ∀ I ∈ F , I.IsPrime
  hPprod : F.prod = Ideal.span {↑p}

#eval Nat.primesBelow 100


-- Turns out it's better to use lists to encode the factorizations,
structure PrimesBelowBoundCertificate (S : Type*) [CommRing S] [Nontrivial S] (B : ℕ) where
  m : ℕ
  g : Fin m → ℕ
  P : Fin m → ℕ
  hP : Set.range P = Nat.primesBelow B
  I : Fin m → List (Ideal S) -- Factorization for the i-th prime.
  hC : ∀ i : Fin m, PrimesBelowPCertificate (P i) (I i)
  N :  Fin m → List ℕ -- Norms corresponding to the factorization of the i-th prime.
  hNle : ∀ i, (N i).length = g i
  hIle : ∀ i, (I i).length = g i
  hN : ∀ i, ∀ j, ∀ h: j < g i, Nat.card (S ⧸ ((I i)[j]'(by rw [hIle i] ; exact h))) = (N i)[j]'(by rw [hNle i] ; exact h)
  Il : Fin m → List (Ideal S) -- List of ideals over the i-th prime, with norm less than B
  hIl : ∀ i, List.map (Prod.fst) (List.filter (λ p => p.2 < B) (List.zip (I i) (N i))) = Il i -/

-- Function that sends an ideal with a proof that its has non-zero norm to a nonzerodivisor ideal.
-- To do: move
lemma zero_ne_mem_of_PrimesBelowCertificate {S : Type*} [CommRing S] [Nontrivial S]
  [CharZero S] (B : ℕ)
  (A : PrimesBelowBoundCertificate S B) : ¬ ⊥ ∈ List.flatten (List.ofFn A.Il) := by
  intro hc
  simp only [List.mem_flatten, List.mem_ofFn, exists_exists_eq_and] at hc
  obtain ⟨a, ha⟩ := hc
  have : A.Il a ⊆ (List.ofFn (A.I a)) := by
    rw [← A.hIl a]
    intro x hx
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists, exists_and_right,
      exists_eq_right] at hx
    obtain ⟨y, hy1, hy2⟩ :=  hx
    exact (List.of_mem_zip hy1).1
  have hmem : ⊥ ∈  List.ofFn (A.I a) := this ha
  rw [List.mem_iff_get] at hmem
  simp at hmem
  obtain ⟨i, hi⟩ := hmem
  set ii : Fin (A.g a):= ⟨↑i, id (Eq.mp (congrArg (LT.lt ↑i) List.length_ofFn) i.isLt)⟩
  have := (A.hC a).hPprod
  erw [Finset.prod_eq_zero (Finset.mem_univ ii) hi, Eq.comm, Ideal.span_singleton_eq_bot] at this
  have haP : (A.P a).Prime := by
    have hmemP : A.P a ∈ Nat.primesBelow B := by
      show A.P a ∈ (Nat.primesBelow B : Set ℕ)
      rw [← A.hP]
      simp only [Set.mem_range, exists_apply_eq_apply]
    exact Nat.prime_of_mem_primesBelow hmemP
  simp at this
  rw [this] at haP
  exact Nat.prime_zero_false haP


def Ideal.toNonZeroDivisorOfNeZero {R : Type} [CommRing R] [IsDomain R]
  (I : Ideal R) (hp : I ≠ ⊥) : nonZeroDivisors (Ideal R) := by
  refine ⟨I, ?_⟩
  simp only [mem_nonZeroDivisors_iff_ne_zero, Submodule.zero_eq_bot,
    ne_eq, hp, not_false_eq_true]

def Ideal.toNonZeroDivisorOfNormPos {R : Type} [CommRing R] [IsDomain R] [CharZero R]
  (I : Ideal R) (hp : 0 < Nat.card (R ⧸ I) ) : nonZeroDivisors (Ideal R) := by
  refine Ideal.toNonZeroDivisorOfNeZero I ?_
  intro hc
  rw [hc, Nat.card_congr (RingEquiv.quotientBot R).toEquiv] at hp
  simp only [Nat.card_eq_zero_of_infinite, gt_iff_lt, lt_self_iff_false] at hp


-- List.map (List.filter (List.zip (List.ofFn (A.I i)) (List.ofFn (A.N i))) (λ p => p.2 < B)) Prod.fst

variable (A : Type*) (a : A) (b : A) (c : A)

example : List.map (Prod.fst) (List.filter (λ p => p.2 ≤ 2) (List.zip (List.ofFn ![a,b,c]) (List.ofFn ![1,2,3]))) = [a ,b ] := by rfl
--#check List.zip [a,b,c] [1,2,3]

open Classical

-- Assuming equality in h, this equality actually holds, but we need to impose
-- the extra restriction that the function P is injective in order to prove it.
lemma le_primes_below_bound_of_PrimesBelowBoundCertificate {B r : ℕ}
    (g : Fin r → Ideal Oκ) (A : PrimesBelowBoundCertificate Oκ B)
    (h : List.flatten (List.ofFn A.Il) ⊆ List.ofFn g) :
    {I : Ideal Oκ | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < B} ⊆ Set.range g := by
  let F : Nat.primesBelow B → Multiset (Ideal Oκ) := by
    rintro ⟨p, hp1⟩
    rw [← Finset.mem_coe, ← A.hP] at hp1
    choose i hi using hp1
    exact ↑(List.ofFn (A.I i))
  have : ∀ i , ∀ I, I ∈ List.ofFn (A.I i) ∧ I.absNorm < B → I ∈ A.Il i := by
    intro i I
    rw [← A.hIl i]
    simp only [List.mem_map, List.mem_filter, decide_eq_true_eq, Prod.exists, exists_and_right,
      exists_eq_right, List.mem_ofFn]
    have heql : ((List.ofFn (A.I i)).zip (List.ofFn (A.N i))).length = (A.g i) := by
        rw [List.length_zip]
        simp only [List.length_ofFn, min_self]
    · rintro ⟨⟨j, hj⟩, hx⟩
      use A.N i j
      rw [List.mem_iff_get]
      constructor
      · use finCongr (heql).symm j
        simp only [finCongr_apply, List.get_eq_getElem, Fin.coe_cast, List.getElem_zip,
          List.getElem_ofFn, Fin.eta, hj]
      · rw [← A.hN i j, hj]
        exact hx
  intro x
  rw [Set.mem_range, ← List.mem_ofFn]
  intro hc ; apply h ; revert hc
  rw [List.mem_flatten, primes_below_bound_of_factorization B F]
  simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_and_right, Subtype.exists, List.mem_ofFn,
    exists_exists_eq_and, and_imp, forall_exists_index]
  intro p hpmem hF hn
  simp only [F, eq_mp_eq_cast, cast_eq, Multiset.mem_coe, List.mem_ofFn] at hF
  obtain ⟨j, hj⟩ := hF
  use @choose (Fin A.m) (fun y ↦ A.P y = p) (cast (congrArg (fun _a ↦ p ∈ _a) (Eq.symm A.hP)) hpmem)
  apply this
  rw [← hj]
  simp only [List.mem_ofFn, exists_apply_eq_apply, true_and]
  rw [hj]
  exact hn
  · intro p I hI
    simp only [F, eq_mp_eq_cast, cast_eq, Multiset.mem_coe, List.mem_ofFn] at hI
    obtain ⟨j, hj⟩ := hI
    rw [← hj]
    exact (A.hC _ ).Ip j
  · intro p
    simp only [F, eq_mp_eq_cast, cast_eq, Multiset.prod_coe]
    rw [List.prod_ofFn, (A.hC _ ).hPprod]
    congr
    exact @choose_spec (Fin A.m) (fun y ↦ A.P y = ↑p) _


-- We don't require definitional equality with the ring of integers.
lemma le_primes_below_bound_of_PrimesBelowBoundCertificate' {O : Subalgebra ℤ K}
    [IsDedekindDomain ↥O] [Module.Free ℤ ↥O]  {B r : ℕ} (φ : O ≃+* Oκ) (g : Fin r → Ideal O)
    (A : PrimesBelowBoundCertificate O B)
    (h : List.flatten (List.ofFn A.Il) ⊆ List.ofFn g) :
    {I : Ideal O | 0 < I.absNorm ∧ I.IsPrime ∧ I.absNorm < B} ⊆ Set.range g := by
  refine primes_below_bound_of_equiv φ B ?_
  let A' : PrimesBelowBoundCertificate Oκ B :=
  { m := A.m
    g := A.g
    P := A.P
    hP := A.hP
    I := fun i => (Ideal.map φ) ∘ (A.I i)
    hC := fun i =>
      { Ip :=  by
          intro j
          have := (A.hC i).Ip j
          exact Ideal.map_isPrime_of_equiv φ (I := (A.I i) j)
        hPprod := by
          have := (A.hC i ).hPprod
          apply_fun (Ideal.mapHom φ) at this
          rw [map_prod, Ideal.mapHom_apply, Ideal.map_span] at this
          simp only [Ideal.mapHom_apply, Set.image_singleton, map_natCast] at this
          exact this }
    N := A.N
    hN := by
      intro i j
      rw [← A.hN i j]
      refine Nat.card_congr ?_
      exact (Ideal.quotientEquiv _ ((A.I i j).map φ) φ rfl).toEquiv.symm
    Il := fun i => List.map (Ideal.map φ) (A.Il i)
    hIl := by
      intro i
      rw [← A.hIl i, ← List.map_ofFn, List.zip_map_left,
        List.filter_map, ← List.comp_map, ← List.comp_map]
      rfl }
  refine le_primes_below_bound_of_PrimesBelowBoundCertificate _ A' ?_
  unfold A'
  dsimp
  erw [← List.map_ofFn, ← List.map_ofFn (f := g), ← List.map_flatten]
  refine List.map_subset _ ?_
  exact h



------------------------------------------------------------------------------
/- # Group p-saturation -/

lemma addOrderOf_ne_eq_addSubgroup {ι : Type*} (n : ι → ℕ) [∀ i, NeZero (n i)]
    {p : ℕ} (hpos : 1 < p) (H : AddSubgroup (∀ i : ι , (ZMod (n i))))
    (hdvd : ∀ a : ι → ℕ, (fun i => ↑(a i)) ∈ H →  (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    ∀ b ∈ H , addOrderOf b ≠ p := by
  by_contra! hc
  obtain ⟨b, hb1, hb2⟩ := hc
  rw [addOrderOf_eq_iff (by omega)] at hb2
  specialize hdvd (fun i => (b i).val)
  suffices h : b = 0 from by
    · rw [h] at hb2
      simp only [smul_zero, ne_eq, not_true_eq_false, imp_false, not_lt, nonpos_iff_eq_zero,
        true_and] at hb2
      specialize hb2 1 hpos
      contradiction
  ext i
  dsimp
  rw [← ZMod.natCast_zmod_val (b i), ZMod.natCast_zmod_eq_zero_iff_dvd]
  refine hdvd ?_ ?_ i
  · convert hb1
    exact ZMod.natCast_zmod_val (b _)
  · intro i
    rcases hb2 with ⟨hb21, hb22⟩
    apply_fun (fun f => f i) at hb21
    simp only [Pi.smul_apply, nsmul_eq_mul, Pi.zero_apply] at hb21
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
    simp only [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id_eq, hb21]

lemma addHom_card_ker_dvd_of_dvd {G : Type*} [AddGroup G] {ι : Type*} [Finite ι]
  {n : ι → ℕ} [∀ i, NeZero (n i)] {p : ℕ} [hp: Fact $ Nat.Prime p]
  (φ : (∀ i : ι , (ZMod (n i))) →+ G)
  (hdvd : ∀ a : ι → ℕ, φ (fun i => a i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    ¬ p ∣ Nat.card (φ.ker) := by
  intro hc
  haveI : Fintype (φ.ker) := Fintype.ofFinite ↥φ.ker
  obtain ⟨b, hb⟩ := exists_prime_addOrderOf_dvd_card (G := φ.ker) p
    (by rw [Fintype.card_eq_nat_card] ; exact hc)
  refine addOrderOf_ne_eq_addSubgroup n (Nat.Prime.one_lt hp.out) φ.ker ?_ b.1 b.2 ?_
  · intro a ha i hi
    exact hdvd a (AddMonoidHom.mem_ker.1 ha) i hi
  · rw [AddSubgroup.addOrderOf_coe]
    exact hb

lemma addHom_injective_of_dvd {G : Type*} [AddGroup G] {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]
    (φ : (∀ i : ι , (ZMod (n i))) →+ G)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, φ (fun i => a i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    Function.Injective φ := by
  refine (AddMonoidHom.ker_eq_bot_iff φ).mp ?_
  rw [← AddSubgroup.card_eq_one, Nat.eq_one_iff_not_exists_prime_dvd]
  intro p hp
  haveI : Fact $ Nat.Prime p := {out := hp}
  by_cases hc : p ∣ ∏ i, n i
  · specialize hdvd p hp hc
    exact addHom_card_ker_dvd_of_dvd φ hdvd
  · intro hdvd
    have := dvd_trans hdvd (AddSubgroup.card_addSubgroup_dvd_card φ.ker)
    rw [Nat.card_pi] at this
    simp only [Nat.card_eq_fintype_card, ZMod.card] at this
    exact hc this

noncomputable def EquivOfSurjectiveOfDvd {G : Type*} [AddGroup G] {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]
    (φ : (∀ i : ι , (ZMod (n i))) →+ G) (hs : Function.Surjective φ)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, φ (fun i => a i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ G := by
  apply AddEquiv.ofBijective φ
  constructor
  · exact addHom_injective_of_dvd φ hdvd
  · exact hs

def AddHomOfGenerators {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (h : ∀ i, (n i) • (g i) = 0) : (∀ i : ι , (ZMod (n i))) →+ G where
  toFun := by
    intro x
    exact ∑ i, (x i).val • (g i)
  map_zero' := by
    simp only [Pi.zero_apply, ZMod.val_zero, zero_smul, Finset.sum_const_zero]
  map_add' := by
    intro x y
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← add_nsmul, nsmul_eq_nsmul_iff_modEq, Nat.modEq_iff_dvd]
    refine dvd_trans (Nat.cast_dvd_cast (addOrderOf_dvd_iff_nsmul_eq_zero.2 (h i))) ?_
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    simp only [Pi.add_apply, ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_add', ZMod.cast_id',
      id_eq, Nat.cast_add, Int.cast_add]

lemma AddHomOfGenerators_apply {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (h : ∀ i, (n i) • (g i) = 0) (x : ∀ i : ι , (ZMod (n i))) :
    AddHomOfGenerators h x = ∑ i, (x i).val • (g i) := by rfl

lemma AddHomOfGenerators_surjective {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)]
    (h : ∀ i, (n i) • (g i) = 0) (hgen : AddSubgroup.closure (Set.range g) = ⊤) :
    Function.Surjective (AddHomOfGenerators h) := by
  intro y
  have ymem : y ∈ AddSubgroup.closure (Set.range g) := by
    rw [hgen]
    exact trivial
  obtain ⟨a, ha⟩ := AddSubgroup.exists_of_mem_closure_range g y ymem
  use (fun i => (a i))
  rw [AddHomOfGenerators_apply, ha]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← natCast_zsmul, zsmul_eq_zsmul_iff_modEq, Int.modEq_iff_dvd]
  refine dvd_trans (Nat.cast_dvd_cast (addOrderOf_dvd_iff_nsmul_eq_zero.2 (h i))) ?_
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_intCast']

noncomputable def AddEquivOfGenerators {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (n i) • (g i) = 0)
    (hgen : AddSubgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∑ i, (a i) • (g i) = 0 →(∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ G := by
  refine EquivOfSurjectiveOfDvd (AddHomOfGenerators h) (AddHomOfGenerators_surjective h hgen) ?_
  intro p hp hpdvd a ha
  rw [AddHomOfGenerators_apply] at ha
  apply hdvd p hp hpdvd
  rw [← ha]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← natCast_zsmul, ← natCast_zsmul, zsmul_eq_zsmul_iff_modEq, Int.modEq_iff_dvd]
  refine dvd_trans (Nat.cast_dvd_cast (addOrderOf_dvd_iff_nsmul_eq_zero.2 (h i))) ?_
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp only [Int.cast_natCast, ZMod.val_natCast, Int.natCast_emod, ZMod.intCast_mod]

lemma AddEquivOfGenerators_apply {G : Type*} [AddCommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (n i) • (g i) = 0)
    (hgen : AddSubgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∑ i, (a i) • (g i) = 0 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i)
    (x : ∀ i : ι , (ZMod (n i))) :
    AddEquivOfGenerators h hgen hdvd x = ∑ i, (x i).val • (g i) := by rfl

noncomputable def AddEquivOfGeneratorsMult {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (g i) ^ (n i) = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∏ i, (g i) ^ (a i) = 1 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    (∀ i : ι , (ZMod (n i))) ≃+ Additive G := by
    refine AddEquivOfGenerators (g := g) (n := n) (G := Additive G) h ?_ hdvd
    · apply_fun Subgroup.toAddSubgroup at hgen
      rw [Subgroup.toAddSubgroup_closure, Set.preimage_equiv_eq_image_symm,
        ← Set.range_comp] at hgen
      simp only [Additive.toMul_symm_eq, map_top] at hgen
      exact hgen

lemma card_of_generators_saturated {G : Type*} [CommGroup G] {ι : Type*} [Fintype ι]
    {g : ι → G} {n : ι → ℕ} [∀ i, NeZero (n i)] (h : ∀ i, (g i) ^ (n i) = 1)
    (hgen : Subgroup.closure (Set.range g) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∏ i, (g i) ^ (a i) = 1 → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
    Nat.card G = ∏ i, n i := by
  rw [← Nat.card_congr (Additive.toMul (α := G)),
    Nat.card_congr (AddEquivOfGeneratorsMult h hgen hdvd).symm.toEquiv , Nat.card_pi]
  simp only [Nat.card_eq_fintype_card, ZMod.card]

noncomputable def equivClassGroupOfSaturated {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
  {ι : Type*} [Fintype ι]
  {n : ι → ℕ} [∀ i, NeZero (n i)]  {I : ι → Ideal S} {I' : ι → nonZeroDivisors (Ideal (S))}
  (hI' : ∀ i, ↑(I' i) = I i) {a : ι → S} (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i})
  (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (I' i))) = ⊤)
  (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∀ b : S, ∏ i, (I i) ^ (a i) = Ideal.span {b} → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
  (∀ i : ι , (ZMod (n i))) ≃+ Additive (ClassGroup S) := by
refine AddEquivOfGeneratorsMult (G := ClassGroup S) (g := (fun i => ClassGroup.mk0 (I' i)))
  (n := n) ?_ hgen ?_
· intro i
  dsimp
  rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI']
  use (a i)
  exact h i
· intro p hp hpdvd a heq
  simp_rw [← map_pow, ← map_prod] at heq
  have aux : (∏ x, I' x ^ a x) = ⟨ (∏ x, I' x ^ a x).1 , (∏ x, I' x ^ a x).2 ⟩ := rfl
  simp [hI'] at aux
  rw [aux, ClassGroup.mk0_eq_one_iff] at heq
  obtain ⟨b ,hb⟩ := heq
  specialize hdvd p hp hpdvd a b
  apply hdvd
  exact hb

@[simp]
lemma equivClassGroupOfSaturated_apply {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
    {ι : Type*} [Fintype ι]
    {n : ι → ℕ} [∀ i, NeZero (n i)]  {I : ι → Ideal S} {I' : ι → nonZeroDivisors (Ideal (S))}
    (hI' : ∀ i, ↑(I' i) = I i) {a : ι → S} (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i})
    (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (I' i))) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
        ∀ a : ι → ℕ, ∀ b : S, ∏ i, (I i) ^ (a i) = Ideal.span {b} → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i)
    (x : ∀ i : ι , (ZMod (n i))) :
    Additive.toMul (equivClassGroupOfSaturated hI' h hgen hdvd x) =
      ∏ i, ClassGroup.mk0 (I' i) ^ (x i).val := rfl

-- Here, type herarchy is important. Ring of integers is not of type type, but higher.
lemma class_number_of_saturated {S : Subalgebra ℤ K} [IsDedekindDomain S]
  {ι : Type*} [Fintype ι] (heq : S = integralClosure ℤ K)
  {n : ι → ℕ} [∀ i, NeZero (n i)]  {I : ι → Ideal S} {I' : ι → nonZeroDivisors (Ideal S)}
  (hI' : ∀ i, ↑(I' i) = I i) {a : ι → S} (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i})
  (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (I' i))) = ⊤)
  (hdvd : ∀ p, Nat.Prime p → p ∣ ∏ i, n i →
      ∀ a : ι → ℕ, ∀ b : S, ∏ i, (I i) ^ (a i) = Ideal.span {b} → (∀ i, n i ∣ p * (a i)) → ∀ i, n i ∣ a i) :
  NumberField.classNumber K =  ∏ i, n i := by
    unfold NumberField.classNumber
    have : ClassGroup S ≃* ClassGroup Oκ := ClassGroup.congr (Subalgebra.equivOfEq _ _ heq).toRingEquiv
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr this.toEquiv,
    ← Nat.card_congr (Additive.toMul (α := ClassGroup S)),
      Nat.card_congr (equivClassGroupOfSaturated hI' h hgen hdvd).symm.toEquiv , Nat.card_pi]
    simp only [Nat.card_eq_fintype_card, ZMod.card]

lemma class_order_of_not_principal {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
    {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal (S))}
    (hI' : ↑I' = I) {α : S} (h : I ^ n = Ideal.span {α})
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) :
    orderOf (ClassGroup.mk0 I') = n := by
    apply orderOf_eq_of_pow_and_pow_div_prime
    · exact Nat.pos_of_neZero n
    · rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI']
      use α
      exact h
    · intro p hp hpdvd hc
      rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI'] at hc
      apply hdvd p hp hpdvd
      obtain ⟨b, hb⟩ := hc
      use b
      exact hb

noncomputable def equivClassGroupCyclicOfSaturated {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
    {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal (S))}
    (hI' : ↑I' = I) {α : S} (h : I ^ n = Ideal.span {α})
    (hgen : Subgroup.closure (Set.range (fun (_ : Fin 1) => ClassGroup.mk0 I')) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) :
  ZMod n ≃+ Additive (ClassGroup S) := by
  refine AddEquiv.trans ((AddEquiv.piUnique fun (j : Fin 1) ↦ ZMod n).symm) ?_
  refine equivClassGroupOfSaturated (n := fun (i : Fin 1) => n) (a := fun _ => α)
    (I := fun (i : Fin 1) => I) (I' := fun (i : Fin 1) => I') ?_ ?_ hgen ?_
  · simp only [hI', implies_true]
  · simp only [h, implies_true]
  · intro p hp hpdvd a b heq i hdvd
    obtain ⟨z, hz⟩ := hdvd
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_const,
      Finset.card_singleton, pow_one] at hpdvd
    simp only [Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.prod_singleton] at heq
    have : (ClassGroup.mk0 I') ^ (a 0) = 1 := by
       rw [← map_pow, ClassGroup.mk0_eq_one_iff, SubmonoidClass.coe_pow, hI']
       exact ⟨b, heq⟩
    dsimp
    convert orderOf_dvd_of_pow_eq_one this
    exact (class_order_of_not_principal hI' h hdvd).symm

lemma equivClassGroupCyclicOfSaturated_apply {S : Type*} [CommRing S] [IsDomain S] [IsDedekindDomain S]
    {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal (S))}
    (hI' : ↑I' = I) {α : S} (h : I ^ n = Ideal.span {α})
    (hgen : Subgroup.closure (Set.range (fun (_ : Fin 1) => ClassGroup.mk0 I')) = ⊤)
    (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) (x : ZMod n) :
    Additive.toMul (equivClassGroupCyclicOfSaturated hI' h hgen hdvd x) =
      ClassGroup.mk0 I' ^ x.val := by
    unfold equivClassGroupCyclicOfSaturated
    simp only [AddEquiv.trans_apply, equivClassGroupOfSaturated_apply, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, AddEquiv.piUnique_symm_apply, uniqueElim_const,
      Finset.prod_const, Finset.card_singleton, pow_one]

lemma class_number_of_saturated_of_cyclic {S : Subalgebra ℤ K} [IsDedekindDomain S]
  {ι : Type*} [Fintype ι] (heq : S = integralClosure ℤ K)
  {n : ℕ} [NeZero n]  {I : Ideal S} {I' : nonZeroDivisors (Ideal S)}
  (hI' : ↑I' = I) {a : S} (h : I ^ n = Ideal.span {a})
  (hgen : Subgroup.closure (Set.range (fun (_ : Fin 1) => ClassGroup.mk0 I')) = ⊤)
  (hdvd : ∀ p, Nat.Prime p → p ∣ n → ¬ ∃ b, I ^ (n / p) = Ideal.span {b}) :
  NumberField.classNumber K =  n := by
    unfold NumberField.classNumber
    have : ClassGroup S ≃* ClassGroup Oκ := ClassGroup.congr (Subalgebra.equivOfEq _ _ heq).toRingEquiv
    rw [Fintype.card_eq_nat_card, ← Nat.card_congr this.toEquiv]
    rw [← Nat.card_congr (Additive.toMul (α := ClassGroup S)),
      Nat.card_congr (equivClassGroupCyclicOfSaturated  hI' h hgen hdvd).symm.toEquiv]
    simp only [Nat.card_eq_fintype_card, ZMod.card]







/-
lemma foo (G : Type*) [AddGroup G] {ι : Type*} (n : ι → ℕ) [∀ i, NeZero (n i)]
  {p : ℕ} (hpos : 1 < p) (φ : (∀ i : ι , (ZMod (n i))) →+ G)
  (hdiv : ∀ a : ι → ℕ, φ (fun i => a i) = 0 →  ∀ i, n i ∣ p * (a i) → ∀ i, n i ∣ a i) :
    ∀ b ∈ φ.ker , addOrderOf b ≠ p := by

-/
