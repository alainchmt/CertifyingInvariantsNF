import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable def MinkowskiBound (K : Type*) [Field K] [NumberField K] : ℝ :=
  (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
  (↑(Module.finrank ℚ K).factorial / ↑(Module.finrank ℚ K) ^ Module.finrank ℚ K * √|↑(NumberField.discr K)|)


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
























example : integralClosure ℤ K = {x : K | IsIntegral ℤ x} := by  rfl




variable (x : K)

example : IsIntegral ℤ x = ∃ (p : Polynomial ℤ), p.Monic ∧ Polynomial.eval₂ (algebraMap ℤ K) x p = 0 := by rfl
