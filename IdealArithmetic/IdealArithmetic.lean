import IdealArithmetic.TimesTableAsLists
import IdealArithmetic.TimesTable.Defs
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FreeModule.PID
import IdealArithmetic.AlgebraAuxiliaryLemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Data.ZMod.Algebra
import IdealArithmetic.QuotientModules
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Rank

section I
variable (O R : Type*) [CommRing O] [CommRing R] [CommRing S]
open BigOperators Classical


lemma submodule_span_le_span_iff [Module R O] [Module S O] {ι τ : Type _} [Fintype ι] [Fintype τ]
  (v : ι → O) (w : τ → O) (I : Set O) (hI : I = Submodule.span R (Set.range w))
  (hsmul : ∀ (s : S) {x : O}, x ∈ I → s • x ∈ I) :
  (Submodule.span S (Set.range v)).carrier ⊆ (Submodule.span R (Set.range w)) ↔
  ∀ (i : ι), (∃ (a : τ → R), v i = ∑ (j : τ), (a j) • (w j) ) := by
  constructor
  · intro h i
    have hvin : v i ∈ (Submodule.span S (Set.range v)).carrier := by
      exact Submodule.subset_span (R := S) (by simp only [Set.mem_range, exists_apply_eq_apply] )
    have hvw := h hvin
    erw [mem_span_range_iff_exists_fun] at hvw
    obtain ⟨a, ha⟩ :=  hvw
    use a
    exact ha.symm
  · intro h
    have : ∀ i , v i ∈ (Submodule.span R (Set.range w)) := by
      intro i
      rw [mem_span_range_iff_exists_fun]
      obtain ⟨a, ha⟩ := h i
      use a
      exact ha.symm
    let P : Submodule S O :=
      { carrier := I
        add_mem' := by
          rw [hI]
          intro a b ha hb
          exact (Submodule.add_mem_iff_right (Submodule.span R (Set.range w)) ha).mpr hb
        zero_mem' := by
          dsimp
          rw [hI]
          exact zero_mem (Submodule.span R (Set.range w))
        smul_mem' := by
          dsimp
          exact hsmul }
    have hleaux : Set.range v ⊆ P := by
      rintro a ⟨i, hi⟩
      simp only [Submodule.coe_set_mk, AddSubmonoid.coe_set_mk, AddSubsemigroup.coe_set_mk, P]
      rw [← hi, hI, SetLike.mem_coe]
      exact this i
    rw [← Submodule.span_le] at hleaux
    rw [← hI]
    exact hleaux

lemma ideal_eq_R_span [Algebra R O] {ι τ : Type _} [Fintype ι] [Fintype τ]
    (v : ι → O) (B : τ → O) (hspan : ⊤ = Submodule.span R (Set.range B)) :
    (Ideal.span (Set.range v)).carrier =
    Submodule.span R (Set.range (fun ⟨i, j⟩ => (v i) * (B j) : ι × τ → O )) := by
  ext x
  constructor
  · intro hx
    erw [mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have hmem : ∀ i , c i ∈ Submodule.span R (Set.range B) := by
      intro i
      rw [← hspan]
      simp only [Submodule.mem_top]
    simp_rw [mem_span_range_iff_exists_fun] at hmem
    let f : ι → (τ → R) := fun i => ((hmem i).choose)
    have hceq : ∀ i , ∑ j : τ , (f i j) • (B j) = c i := by
      intro i
      exact (hmem i).choose_spec
    simp_rw [← hceq] at hc
    erw [mem_span_range_iff_exists_fun, ← hc]
    use (fun ⟨i, j⟩ => f i j)
    dsimp
    let F : ι → (τ → O) := fun i => (fun j => (f i j) • ((v i) * (B j)))
    simp_rw [Fintype.sum_prod_type' F, Finset.sum_mul]
    congr ; ext i ; congr ; ext j
    rw [Algebra.smul_mul_assoc, mul_comm]
  · intro hx
    erw [mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    rw [← hc]
    refine Submodule.sum_mem _ ?_
    intro i _
    dsimp
    rw [mul_comm, ← Algebra.smul_mul_assoc]
    refine Ideal.mul_mem_left _ _ (Ideal.subset_span ?_)
    exact Set.mem_range_self i.1


lemma ideal_eq_R_span' [Algebra R O] {ι τ κ: Type _} [Fintype ι] [Fintype τ]
  [Fintype κ] (v : ι → O) (B : τ → O) (w : κ → O)
  (hspan : ⊤ = Submodule.span R (Set.range B))
  (h1 : ∀ k, (∃ (f : ι → τ → R) , w k = ∑ i , ∑ j , f i j • ((v i) * (B j))))
  (h2 : ∀ i j , (∃ (g : κ → R), (v i) * (B j) = ∑ k, (g k) • (w k) )) :
   (Ideal.span (Set.range v)).carrier = Submodule.span R (Set.range w) := by
  rw [ideal_eq_R_span O R v B hspan]
  refine subset_antisymm ?_ ?_
  erw [submodule_span_le_span_iff _ _ _ _ ((Submodule.span R (Set.range w)).carrier)]
  · rintro ⟨i , j⟩
    use (h2 i j).choose
    exact (h2 i j).choose_spec
  · rfl
  · intro s x hx
    exact (Submodule.span R (Set.range w)).smul_mem' s hx
  erw [submodule_span_le_span_iff]
  · intro k
    use (fun ⟨i , j⟩ =>  (h1 k).choose i j)
    simp_rw [(h1 k).choose_spec]
    exact Eq.symm (Fintype.sum_prod_type fun x ↦ (h1 k).choose x.1 x.2 • (v x.1 * B x.2))
  · exact (Submodule.span R (Set.range (fun ⟨i, j⟩ => (v i) * (B j) : ι × τ → O ))).carrier
  · rfl
  · intro s x hx
    exact Submodule.smul_mem' _ s hx

-- v are O-generators and w are Z-generators. we include them as parameters so n and m can be inferred
structure IdealEqSpanCertificate [Algebra R O] {r n m : ℕ} [NeZero r]
   (TT  : TimesTable (Fin r) R O) (I : Ideal O) (v : Fin m → Fin r → R) (w : Fin n → Fin r → R)  where
  T : Fin r → Fin r → List R
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  hieq : I = Ideal.span (Set.range (fun i => (TT.basis).equivFun.symm (v i)))
  f : Fin n → Fin m → Fin r → R
  g : Fin m → Fin r → Fin n → R
  M : Fin m → Fin r → Fin r → R -- products (v i) * (B j)
  hmulB : ∀ i j, table_mul_list T (List.ofFn (v i)) (List.ofFn (fun k => if k = j then 1 else 0 ))
    = List.ofFn (M i j)
  hle1 : ∀ k , List.ofFn (w k) = List.sum (List.ofFn (fun i => List.sum
    (List.ofFn (fun j => List.mulPointwise (f k i j) (List.ofFn (M i j) ) ))))
  hle2 : ∀ i j, List.ofFn (M i j) = List.sum (List.ofFn (fun k => List.mulPointwise (g i j k) (List.ofFn (w k))))

lemma ideal_eq_of_IdealEqSpanCertificate [Algebra R O] {r n : ℕ} [NeZero r]
    {TT  : TimesTable (Fin r) R O} {I : Ideal O}
    {v : Fin m → Fin r → R} {w : Fin n → Fin r → R} (A : IdealEqSpanCertificate O R TT I v w) :
    I.carrier = Submodule.span R (Set.range (fun i => (TT.basis).equivFun.symm (w i))) := by
  rw [A.hieq]
  have aux := A.hmulB
  simp_rw [table_mul_eq_table_mul' TT.table A.T A.heq] at aux
  have hmulaux := fun i j => table_mul_list_eq_mul TT.table TT.basis _ _ _ TT.basis_mul_basis (aux i j).symm
  have : ∀ j , TT.basis.equivFun.symm (fun k ↦ if k = j then 1 else 0) = TT.basis j := by
    simp only [Basis.equivFun_symm_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte, implies_true]
  simp_rw [this] at hmulaux
  refine ideal_eq_R_span' O R _ (TT.basis) _ ?_ ?_ ?_
  · exact Eq.symm (Basis.span_eq TT.basis)
  · intro k
    use (A.f k)
    have hle1 := A.hle1
    simp_rw [List.mulPointwise_ofFn, ← List.sum_ofFn' (Ne.symm (NeZero.ne' r))] at hle1
    convert table_sum_smul' TT.basis _ _ (hle1 k)
    simp_rw [hmulaux]
    simp only [Basis.equivFun_symm_apply, map_sum, map_smul]
  · intro i j
    use (A.g i j)
    simp_rw [hmulaux]
    refine table_sum_smul TT.basis _ _ _ ?_
    exact A.hle2 i j

/-- Certificate for I ≤ J -/
structure IdealLeCertificate [Algebra R O] {r n m : ℕ}
   (B  : Basis (Fin r) R O) (I : Ideal O) (J : Ideal O) (v : Fin m → Fin r → R)
  (w : Fin n → Fin r → R)  where
  hieq1 : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (v i)))
  hieq2 : J.carrier = Submodule.span R (Set.range (fun j => B.equivFun.symm (w j)))
  g : Fin m → Fin n → R
  hle2 : ∀ i, List.ofFn (v i) = List.sum (List.ofFn (fun k => List.mulPointwise (g i k) (List.ofFn (w k))))


lemma ideal_le_of_certificate [Algebra R O] {r n m : ℕ}
   (B  : Basis (Fin r) R O) (I : Ideal O) (J : Ideal O) (v : Fin m → Fin r → R)
   (w : Fin n → Fin r → R) (A : IdealLeCertificate O R B I J v w) : I ≤ J := by
  show (I.carrier ⊆ J.carrier)
  rw [A.hieq1, A.hieq2]
  convert (submodule_span_le_span_iff O R (fun i => B.equivFun.symm (v i))
    (fun i => B.equivFun.symm (w i))
    _ rfl (by intro s hs ; exact fun a ↦ SMulMemClass.smul_mem s a)).2 ?_
  · intro i
    use (A.g i)
    refine table_sum_smul B w (v i) (A.g i) ?_
    exact (A.hle2 i)

/-- Certificate for I ≤ J using O-generators for J and S-generators for I. -/
structure IdealLeCertificateO [Algebra R O] (S : Type*) [CommRing S] [Algebra S O]
  {r n m : ℕ} (TT  : TimesTable (Fin r) R O)  (I : Ideal O) (J : Ideal O) (v : Fin m → Fin r → R)
  (w : Fin n → Fin r → R) where
  T : Fin r → Fin r → List R
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  hieq1 : I.carrier = Submodule.span S (Set.range (fun i => TT.basis.equivFun.symm (v i)))
  hieq2 : J = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm (w j)))
  g : Fin m → Fin n → Fin r → R
  hle2 : ∀ i, List.ofFn (v i) = List.sum (List.ofFn (fun k => table_mul_list T  (List.ofFn (g i k)) (List.ofFn (w k))))

lemma ideal_le_of_IdealLeCertificateO [Algebra R O] (S : Type*) [CommRing S] [Algebra S O]
  {r n m : ℕ} (TT  : TimesTable (Fin r) R O) (I : Ideal O) (J : Ideal O) (v : Fin m → Fin r → R)
  (w : Fin n → Fin r → R) (A : IdealLeCertificateO O R S TT I J v w) : I ≤ J := by
  show I.carrier ⊆ J.carrier
  rw [A.hieq1, A.hieq2]
  unfold Ideal.span
  erw [submodule_span_le_span_iff (S := S) O O (fun j => TT.basis.equivFun.symm (v j))
    (fun j => TT.basis.equivFun.symm (w j)) J.carrier ?_ ?_]
  · intro i
    use (fun j => TT.basis.equivFun.symm (A.g i j) )
    simp_rw [smul_eq_mul]
    refine table_sum_mul TT.table TT.basis TT.basis_mul_basis _ _ _ ?_
    simp_rw [← table_mul_eq_table_mul' TT.table A.T A.heq]
    exact A.hle2 i
  · rw [A.hieq2]
    rfl
  · intro s x hx
    rw [algebra_compatible_smul O s x]
    exact J.smul_mem' ((algebraMap S O) s) hx

/-- Certificate for membership a ∈ I. -/
structure IdealMemCertificate [Algebra R O] {r m : ℕ} (B  : Basis (Fin r) R O)
  (I : Ideal O) (v : Fin m → Fin r → R)  (a : Fin r → R) where
  hieq : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (v i)))
  g : Fin m → R
  hmem : List.ofFn a = List.sum (List.ofFn (fun k => List.mulPointwise (g k) (List.ofFn (v k))))

lemma mem_of_certificate [Algebra R O] {r m : ℕ} (B  : Basis (Fin r) R O)
    (I : Ideal O) (v : Fin m → Fin r → R)  (a : Fin r → R) (A : IdealMemCertificate O R B I v a) :
    B.equivFun.symm a ∈ I := by
  show B.equivFun.symm a ∈ I.carrier
  erw [A.hieq, mem_span_range_iff_exists_fun]
  use A.g
  symm
  refine table_sum_smul B v a (A.g) (A.hmem)

-- Move
/-- If some collection of vectors of the same size as the rank spans the whole
space, then they are linearly independent. This is a version of
linearIndependent_of_top_le_span_of_card_eq_finrank which works over domains. -/
lemma linear_independent_of_top_le_span_of_card_eq_rank
  {τ : Type*} {M : Type*} [Fintype τ] [IsDomain R]
  [AddCommGroup M] [Module R M] (B : Basis τ R M) {b : τ → M}
  (hmem : ⊤ ≤ Submodule.span R (Set.range b)) : LinearIndependent R b := by
  let Q := FractionRing R
  let B' := Basis.baseChange Q B
  have hle : ⊤ ≤ Submodule.span Q (Set.range (fun i => ( 1 ⊗ₜ (b i) : TensorProduct R Q M))) := by
    let P : TensorProduct R Q M → Prop := fun x => x ∈ Submodule.span Q
      (Set.range (fun i => ( 1 ⊗ₜ (b i) : TensorProduct R Q M)))
    have : ∀ x, P x := by
      intro z
      refine TensorProduct.induction_on z ?_ ?_ ?_
      · simp only [Submodule.zero_mem, P]
      · intro x y
        have aux : y ∈ Submodule.span R (Set.range b) := hmem trivial
        rw [mem_span_range_iff_exists_fun] at aux
        obtain ⟨c, hc⟩ := aux
        simp only [mem_span_range_iff_exists_fun, ← hc, TensorProduct.tmul_sum,
          TensorProduct.tmul_smul, P]
        use (fun i => (c i) • x)
        congr ; ext i
        rw [smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · intro x y hx hy
        exact Submodule.add_mem _ hx hy
    intro x _
    exact this x
  have := linearIndependent_of_top_le_span_of_card_eq_finrank hle (Eq.symm
    (FiniteDimensional.finrank_eq_card_basis B'))
  rw [linearIndependent_iff'] at this ⊢
  intro s g hg i his
  rw [← NoZeroSMulDivisors.algebraMap_eq_zero_iff R Q]
  specialize this s (fun i => (algebraMap R Q) (g i))
  refine this ?_ i his
  simp_rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one,
  TensorProduct.smul_tmul, ← TensorProduct.tmul_sum _ _ (fun x => g x • b x), hg,
  TensorProduct.tmul_zero]


/-- If I is R-generated by the collection v with the same number of elements
  as the rank of O, then this is a basis for I. -/
noncomputable def BasisOfEqSpan {τ : Type*} [Fintype τ] [IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] (B : Basis τ R O) (I : Ideal O) (hI : I ≠ ⊥) (v : τ → O)
    (heq : I.carrier = Submodule.span R (Set.range v)) : Basis τ R I := by
    have hmem : ∀ i , v i ∈ I := by
      intro i
      show (v i) ∈ I.carrier
      rw [heq]
      refine Submodule.subset_span ⟨i, rfl⟩
    let v' := fun i => (⟨v i, hmem i⟩ : I)
    let f : I →ₗ[R] O :=
      { toFun := Subtype.val
        map_add' := fun x y ↦ rfl
        map_smul' := fun m x ↦ rfl }
    have hle : ⊤ ≤ Submodule.span R (Set.range v') := by
      have hf : Function.Injective f := by simp only [LinearMap.coe_mk, AddHom.coe_mk,
      Subtype.val_injective, f]
      have hvv : v = f ∘ v' := rfl
      intro x ?_
      rw [← Submodule.apply_mem_span_image_iff_mem_span hf, ← Set.range_comp, ← hvv]
      show (f x ∈ ((Submodule.span R (Set.range v) : Set O) ))
      rw [← heq]
      exact x.2
    refine Basis.mk (R := R) (v := v') ?_ ?_
    refine linear_independent_of_top_le_span_of_card_eq_rank R (Ideal.selfBasis B I hI) ?_
    exact hle ; exact hle


lemma BasisOfEqSpan_apply  {τ : Type*} [Fintype τ] [IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] (B : Basis τ R O) (I : Ideal O) (hI : I ≠ ⊥) (v : τ → O)
    (heq : I.carrier = Submodule.span R (Set.range v)) (i : τ) :
    (BasisOfEqSpan O R B I hI v heq) i = v i := by simp only [BasisOfEqSpan, Basis.coe_mk]


structure IdealNeMemCertificate [Algebra R O] {r : ℕ} (B : Basis (Fin r) R O)
(I : Ideal O) (v : Fin r → Fin r → R) (a : Fin r → R) where
    hieq : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (v i)))
    ha : a ≠ 0
    d : R
    g : Fin r → R
    hmem : List.mulPointwise d (List.ofFn a) = List.sum
      (List.ofFn (fun k => List.mulPointwise (g k) (List.ofFn (v k))))
    i : Fin r
    hnedvd : ¬ d ∣ (g i)

lemma ne_mem_of_certificate [IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] {r : ℕ}
    (B : Basis (Fin r) R O) (I : Ideal O) (v : Fin r → Fin r → R)
    (a : Fin r → R) (A : IdealNeMemCertificate O R B I v a) :
    B.equivFun.symm a ∉ I := by
    by_cases hI : I = ⊥
    · rw [hI, Ideal.mem_bot]
      exact (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr A.ha
    · have hc := A.hmem
      rw [List.mulPointwise_ofFn] at hc
      let B' := BasisOfEqSpan O R B I hI (fun i => B.equivFun.symm (v i)) A.hieq
      have heqaux := table_sum_smul B v (A.d • a) (A.g) hc
      by_contra hmema
      have := Basis.dvd_coord_smul B' A.i ⟨B.equivFun.symm a, hmema⟩ A.d
      simp_rw [SetLike.mk_smul_of_tower_mk,
        ← LinearEquiv.map_smul B.equivFun.symm A.d a, heqaux] at this
      apply A.hnedvd
      convert this
      rw [Basis.coord_apply]
      nth_rw 1 [← Basis.repr_sum_self B' A.g]
      congr
      simp only [BasisOfEqSpan, Basis.coe_mk, B']
      rw [← Subtype.val_inj, Submodule.coe_sum]
      rfl

lemma ideal_mul_eq_span {ι τ : Type _} [Fintype ι] [Fintype τ]
    (v : ι → O) (w : τ → O)  :
    (Ideal.span (Set.range v)) * (Ideal.span (Set.range w)) =
    Ideal.span (Set.range (fun (⟨i,j⟩ : ι × τ) => (v i) * (w j) )) := by
    rw [Ideal.span_mul_span]
    congr
    ext x
    simp only [Set.mem_range, Set.iUnion_exists, Set.iUnion_iUnion_eq',
      Set.iUnion_singleton_eq_range, Set.mem_iUnion, Prod.exists]



structure IdealMulEqCertificate [Algebra R O] {r n m s : ℕ} [NeZero r]
  (TT  : TimesTable (Fin r) R O) (I₁ I₂ : Ideal O)
  (u : Fin m → Fin r → R) (v : Fin n → Fin r → R) (w : Fin s → Fin r → R) where
  T : Fin r → Fin r → List R
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  hI1 : I₁ = Ideal.span (Set.range (fun i => (TT.basis).equivFun.symm (u i)))
  hI2 : I₂ = Ideal.span (Set.range (fun i => (TT.basis).equivFun.symm (v i)))
  M : Fin m → Fin n → Fin r → R -- products (u i) * (v j)
  hmul : ∀ i j, table_mul_list T (List.ofFn (u i)) (List.ofFn (v j)) = List.ofFn (M i j)
  f : Fin s → Fin m → Fin n → Fin r → R
  g : Fin m → Fin n → Fin s → Fin r → R
  hle1 : ∀ k , List.ofFn (w k) = List.sum (List.ofFn (fun i => List.sum
    (List.ofFn (fun j => table_mul_list T (List.ofFn (f k i j)) (List.ofFn (M i j) ) ))))
  hle2 : ∀ i j, List.ofFn (M i j) = List.sum (List.ofFn
    (fun k => table_mul_list T (List.ofFn (g i j k)) (List.ofFn (w k))))

lemma ideal_eq_mul_of_IdealMulEqCertificate [Algebra R O] {r n m s : ℕ} [NeZero r]
  (TT  : TimesTable (Fin r) R O) (I₁ I₂ : Ideal O)
  (u : Fin m → Fin r → R) (v : Fin n → Fin r → R) (w : Fin s → Fin r → R)
  (A : IdealMulEqCertificate O R TT I₁ I₂ u v w) :
  I₁ * I₂ = Ideal.span (Set.range (fun i => (TT.basis).equivFun.symm (w i))) := by
have aux := A.hmul
simp_rw [table_mul_eq_table_mul' TT.table A.T A.heq] at aux
have hmulaux := fun i j => table_mul_list_eq_mul TT.table TT.basis _ _ _ TT.basis_mul_basis (aux i j).symm
simp_rw [A.hI1, A.hI2, ideal_mul_eq_span, hmulaux]
unfold Ideal.span
rw [← Submodule.carrier_inj]
refine subset_antisymm ?_ ?_
· erw [submodule_span_le_span_iff O O _ _ ((Submodule.span O (Set.range fun i ↦ TT.basis.equivFun.symm (w i))).carrier) ]
  · rintro ⟨i,j⟩
    use (fun k => TT.basis.equivFun.symm (A.g i j k))
    dsimp
    refine table_sum_mul TT.table TT.basis TT.basis_mul_basis _ _ _ ?_
    simp_rw [← table_mul_eq_table_mul' TT.table A.T A.heq]
    exact (A.hle2 i j)
  · rfl
  · intro s x hx
    exact (Submodule.span O (Set.range fun i ↦ TT.basis.equivFun.symm (w i))).smul_mem' s hx
· erw [submodule_span_le_span_iff (S := O) O O _ _ ((Submodule.span O (Set.range fun (x : Fin m × Fin n)
    ↦ TT.basis.equivFun.symm (A.M x.1 x.2))).carrier) ]
  · intro k
    use (fun ⟨i,j⟩ => TT.basis.equivFun.symm (A.f k i j) )
    dsimp
    rw [Fintype.sum_prod_type]
    have aux := A.hle1 k
    let d : Fin m → Fin n → Fin r → R := fun i j => FnOfList r (table_mul_list' TT.table (List.ofFn (A.f k i j)) (List.ofFn (A.M i j))) (table_mul_list_length _ _ _)
    have hd : ∀ i j, List.ofFn (d i j) = table_mul_list' TT.table (List.ofFn (A.f k i j)) (List.ofFn (A.M i j)) :=
      fun i j ↦ listOfFn_of_FnOfList r _ (table_mul_list_length TT.table (List.ofFn (A.f k i j)) (List.ofFn (A.M i j)))
    have hmulaux2 := fun i j => table_mul_list_eq_mul TT.table TT.basis _ _ _ TT.basis_mul_basis (hd i j)
    simp_rw [table_mul_eq_table_mul' TT.table A.T A.heq, ← hd] at aux
    simp_rw [hmulaux2]
    exact table_sum_sum TT.basis _ _ aux
  · rfl
  · intro s x hx
    exact Submodule.smul_mem' _ s hx

end I

open Polynomial


noncomputable def IsAdjoinRoot_of_adjoin_root_irreducible {F K : Type*} [CommRing K] [Field F]
  [DecidableEq F] [Algebra F K] [FiniteDimensional F K] (f : F[X]) (hI : Irreducible f)
  (ha : ∃ (a : K) , Polynomial.aeval a f = 0 )
  (hr : FiniteDimensional.finrank F K = f.natDegree) : IsAdjoinRoot K f := by
  choose a h using ha
  have hint : IsIntegral F a := by
    use (normalize f)
    constructor
    · exact (Polynomial.monic_normalize (Irreducible.ne_zero hI))
    · rw [← Polynomial.aeval_def]
      simp only [normalize_apply, coe_normUnit, map_mul, h, aeval_C, zero_mul]
  have hmin : minpoly F a = normalize f := by
    simp only [normalize_apply, coe_normUnit]
    convert (minpoly.eq_of_irreducible hI h).symm
    refine CommGroupWithZero.coe_normUnit F (Polynomial.leadingCoeff_ne_zero.2 (
      Irreducible.ne_zero hI))
    · rw [← FiniteDimensional.finrank_pos_iff (R := F), hr]
      exact Irreducible.natDegree_pos hI
  have := Algebra.adjoin_isAdjoinRoot (Q := F) (K := K) (normalize f)
    (Polynomial.monic_normalize (Irreducible.ne_zero hI)) a ?_
  swap
  · rw [hmin]
    simp only [normalize_apply, coe_normUnit, Algebra.id.map_eq_id, Polynomial.map_mul, map_id,
      map_C, RingHom.id_apply]
  let e : Algebra.adjoin F {a} →ₐ[F] K := Subalgebra.val _
  have heB : Function.Bijective e := by
    show Function.Bijective e.toLinearMap
    constructor
    · exact (AlgHom.injective_codRestrict _ _ _).mp fun ⦃a₁ a₂⦄ a ↦ a
    · rw [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
      exact (AlgHom.injective_codRestrict _ _ _).mp fun ⦃a₁ a₂⦄ a ↦ a
      rw [PowerBasis.finrank (Algebra.adjoin.powerBasis hint), hr]
      simp only [Algebra.adjoin.powerBasis_dim, hmin, normalize_apply, coe_normUnit]
      refine Polynomial.natDegree_mul_C_eq_of_mul_ne_zero ?_
      simp only [ne_eq, mul_eq_zero, leadingCoeff_eq_zero, Units.ne_zero, or_false]
      exact Irreducible.ne_zero hI
  have IsA := IsAdjoinRoot.ofEquiv this (AlgEquiv.ofBijective e heB)
  exact
  { map := IsA.map
    map_surjective := IsA.map_surjective
    ker_map := by
      rw [IsA.ker_map, normalize_apply, coe_normUnit]
      refine Ideal.span_singleton_mul_right_unit ?_ _
      simp only [isUnit_map_iff, isUnit_iff_ne_zero, ne_eq, Units.ne_zero, not_false_eq_true]
    algebraMap_eq := IsA.algebraMap_eq }

noncomputable def field_of_adjoin_root_irreducible {F K : Type*} [CommRing K] [Field F]
  [DecidableEq F] [Algebra F K] [FiniteDimensional F K] (f : F[X]) (hI : Irreducible f)
  (ha : ∃ (a : K) , Polynomial.aeval a f = 0 )
  (hr : FiniteDimensional.finrank F K = f.natDegree) : IsField K := by
  letI E := IsAdjoinRoot.aequiv (IsAdjoinRoot_of_adjoin_root_irreducible f hI ha hr)
    (AdjoinRoot.isAdjoinRoot f)
  haveI : Fact $ Irreducible f := { out := hI }
  exact (MulEquiv.isField (AdjoinRoot f) (Semifield.toIsField (AdjoinRoot f)) E.toMulEquiv)


-- I substituted the q in dedekind criterion with algebra instance, so we can use the isScalarTower
noncomputable def quotient_finrank_of_index {O R F : Type*} {n : ℕ} [CommRing O] [CommRing R]
    [IsDomain R] [IsPrincipalIdealRing R] [IsDomain O] [Algebra R O] [Field F]
    (π : R) (hp : Prime π) [Algebra R F] (hqs : Function.Surjective (algebraMap R F))
    (hqker : RingHom.ker (algebraMap R F) = Ideal.span {π} )
    [Module.Free R O] [Module.Finite R O] (I : Ideal O) (hnb : I ≠ ⊥) [hI : Module F (O ⧸ I)]
    [hS : IsScalarTower R F (O ⧸ I)]
    (hr : Associated (Submodule.indexPID (I.restrictScalars R)) (π ^ n)) :
    FiniteDimensional.finrank F (O ⧸ I) = n := by
    haveI : Module F (O ⧸ (I.restrictScalars R)) := hI
    haveI : IsScalarTower R F (O ⧸ (I.restrictScalars R)) := sorry
    let B' := Module.Free.chooseBasis R O
    let b' := Ideal.selfBasis B' I hnb
    let B := Basis.reindex B' (Fintype.equivFin _)
    let b := Basis.reindex b' (Fintype.equivFin _)
    let e := moduleQuotientEquivPiSpan' (I.restrictScalars R) B b
    have hpi := Associated.trans (prod_moduleSmithCoeffs_associated_index (I.restrictScalars R) B b).symm hr
    let C := moduleSmithCoeffs (I.restrictScalars R) B b
    have hs : ∀ i, IsUnit (C i) ∨ Associated (C i) π := by
      intro i
      have hdvd : C i ∣ π ^ n := by
        refine dvd_trans (Finset.dvd_prod_of_mem C (Finset.mem_univ i)) (hpi.dvd)
      obtain ⟨m, hml, hma⟩ := (dvd_prime_pow hp n).1 hdvd
      by_cases hz : m = 0
      · rw [hz] at hma
        simp only [pow_zero, associated_one_iff_isUnit] at hma
        left
        exact hma
      · by_cases ho : m = 1
        · rw [ho, pow_one] at hma
          right
          exact hma
        · exfalso
          have hpi1 : π • e.symm (fun j => if j = i then 1 else 0) ≠ 0 := by
            by_contra hc
            rw [← map_smul, (injective_iff_map_eq_zero' _).1 (LinearEquiv.injective e.symm)] at hc
            have aux := congr_fun hc i
            simp only [Pi.smul_apply, ↓reduceIte, Pi.zero_apply] at aux
            erw [Submodule.Quotient.mk_eq_zero] at aux
            simp only [smul_eq_mul, mul_one] at aux
            rw  [Ideal.span_singleton_eq_span_singleton.2 hma, Ideal.mem_span_singleton] at aux
            sorry
          apply hpi1
          have heq : (1 : F) • e.symm (fun j => if j = i then 1 else 0) = e.symm (fun j => if j = i then 1 else 0) :=
            MulAction.one_smul _
          rw [← heq, ← IsScalarTower.smul_assoc π (1 : F) _]
          have hsz : π • (1 : F) = 0 := by
            rw [Algebra.smul_def, mul_one, ← RingHom.mem_ker, hqker]
            exact Ideal.mem_span_singleton_self π
          rw [hsz, zero_smul]
    --let pb : Fin n → Fin (Fintype.card (Module.Free.ChooseBasisIndex R O)) := by
    let G := { i | ¬ IsUnit (C i) }
    haveI : Fintype G := Fintype.ofFinite ↑G
    let B := { i | IsUnit (C i) }
    haveI : Fintype B := Fintype.ofFinite ↑B
    have hcard : Fintype.card G = n := by sorry
    let equivG := Equiv.trans (finCongr hcard.symm) (Fintype.equivFin G).symm
    let f := fun (i : Fin n) => (equivG i).val
    have fI : Function.Injective f := by sorry
    let tF : ∀ i , R ⧸ Ideal.span {C (f i)} ≃+* F := by sorry
    --let i : Fin n := by sorry
    let Ba : (O ⧸ I) ≃ₗ[F] Fin n →₀ F :=
     {toFun := fun x => (Finsupp.ofSupportFinite (fun i => (tF i) ((e x) (f i))) (Set.toFinite _) )
      map_smul' := sorry
      invFun := fun c => ∑ i, (c i) • e.symm (fun j => if j = f i then 1 else 0 )
      left_inv := by
        intro x
        simp [Finsupp.ofSupportFinite]
        sorry
      right_inv := by
        intro v
        simp
        ext x
        simp [Finsupp.ofSupportFinite]
        sorry
      map_add' := sorry }
    convert FiniteDimensional.finrank_eq_card_basis ({repr := Ba})
    simp only [Fintype.card_fin]


lemma ideal_index_associated_det (O R : Type*) [CommRing O]
    [CommRing R]{τ : Type*} [DecidableEq τ][Fintype τ] [IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] (B : Basis τ R O) (I : Ideal O)
    [Module.Free R O] [Module.Finite R O] [Module.Free R I] (hI : I ≠ ⊥)
    (V : Matrix τ τ R)
    (heq : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (V i)))) :
    Associated (Submodule.indexPID (I.restrictScalars R)) (V.det) := by
  let BI := BasisOfEqSpan O R B I hI (fun i => B.equivFun.symm (V i)) heq
  have eqV : LinearMap.toMatrix BI B (Submodule.subtype (I.restrictScalars R)) = V.transpose := by
    ext i j
    erw [Matrix.transpose_apply, LinearMap.toMatrix_apply, Submodule.subtype_apply (I.restrictScalars R)]
    have aux : B.repr ↑(BI j) = V j := by
      apply_fun B.equivFun.symm
      rw [Basis.equivFun_symm_eq_repr_symm, LinearEquiv.symm_apply_apply,
      BasisOfEqSpan_apply O R B I hI (fun i => B.equivFun.symm (V i)) heq j]
      exact LinearEquiv.injective B.equivFun.symm
    exact congrFun aux i
  rw [← Matrix.det_transpose]
  convert associated_index_of_basis (I.restrictScalars R) B BI
  convert eqV.symm


lemma ideal_index_associated_prod (O R : Type*) [CommRing O]
    [CommRing R][IsDomain R] [IsPrincipalIdealRing R]
    [IsDomain O] [Algebra R O] (B : Basis (Fin r) R O) (I : Ideal O)
    [Module.Free R O] [Module.Finite R O] [Module.Free R I] (hI : I ≠ ⊥)
    (V : Fin r → Fin r → R) (hd : ∀ i j, i < j → V i j = 0)
    (heq : I.carrier = Submodule.span R (Set.range (fun i => B.equivFun.symm (V i)))) :
    Associated (Submodule.indexPID (I.restrictScalars R)) (∏ i, V i i) := by
  convert ideal_index_associated_det O R B I hI V heq
  symm
  refine Matrix.det_of_lowerTriangular _ ?_
  intro i j
  simp only [OrderDual.toDual_lt_toDual]
  exact hd i j


-- We don't use Ideal.absNorm because we don't assume O is a Dedekind Domain.
lemma ideal_norm_eq_prod (O : Type*) [CommRing O]
    [IsDomain O] (B : Basis (Fin r) ℤ O) (I : Ideal O) (hI : I ≠ ⊥)
    (V : Fin r → Fin r → ℤ) (hd : ∀ i j, i < j → V i j = 0)
    (heq : I.carrier = Submodule.span ℤ (Set.range (fun i => B.equivFun.symm (V i)))) :
    Nat.card (O ⧸ I) = (∏ i, V i i).natAbs := by
  let BI := BasisOfEqSpan O ℤ B I hI (fun i => B.equivFun.symm (V i)) heq
  haveI : Module.Finite ℤ O := Module.Finite.of_basis B
  haveI : Module.Free ℤ O := Module.Free.of_basis B
  rw [Int.natAbs_eq_iff_associated.2 (ideal_index_associated_prod O ℤ B I hI V hd heq ).symm ]
  symm
  exact indexPID_eq_index_int _ B BI



noncomputable def isAdjoinRoot_of_adjoin_root_irreducible_finite {F K : Type*} {n : ℕ}
  [AddCommGroup K] [Field F] [Fintype F] [DecidableEq F] [Module F K]
  (hr : Nat.card K = Fintype.card F ^ n) : FiniteDimensional.finrank F K = n := by
  haveI : Fintype K := by
    haveI := ((Nat.card_pos_iff (α := K)).1 ?_).2
    exact Fintype.ofFinite K
    rw [hr]
    refine pow_pos (Fintype.card_pos) _
  haveI : FiniteDimensional F K := Module.IsNoetherian.finite F K
  rw [Nat.card_eq_fintype_card, Module.card_fintype (M := K) (R := F) (Basis.ofVectorSpace F K),
    ← FiniteDimensional.finrank_eq_card_basis (Basis.ofVectorSpace F K) ] at hr
  apply_fun (fun x => Fintype.card F ^ x)
  dsimp
  exact hr
  refine Nat.pow_right_injective (Nat.succ_le_of_lt (Fintype.one_lt_card) )

def ZModP_algebra_of_mem {O : Type*} [CommRing O] (I : Ideal O)
  (p : ℕ) (hI : ↑p ∈ I) : Algebra (ZMod p) (O ⧸ I) := by
  refine ZMod.algebra' (O ⧸ I) (ringChar (O ⧸ I)) ?_
  erw [← ringChar.spec, Ideal.Quotient.eq_zero_iff_mem]
  exact hI

attribute [-instance]  Lean.Omega.IntList.instAdd

-- We don't include computation tools as part of the parameters of the structure.
/-
This structure bundles an ideal `I` with a certifificate of its primality. Even more,
it proves that the residue field is given by adjoining a root of a polynomial f.
`r` : rank of `O`
`n` : inertia degree / dimension of the residue field as an `F_p`-algebra.
`f` : polynomial such that `O⧸I` is isomorphic to `F_p[X]/(f)`
`a` : represents the lift of the root of `f` in `O⧸I`.
`c` : represents the element `f(a)`, which lives in `I`.
-/

structure PrimeIdeal (O : Type*) (p : ℕ) [Fact $ Nat.Prime p] [CommRing O]  where
  r : ℕ
  n : ℕ
  hpos : 0 < n
  TT  : TimesTable (Fin r) ℤ O
  T : Fin r → Fin r → List ℤ
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  I : Ideal O
  hcard : Nat.card (O ⧸ I) = p ^ n
  P : List ℤ
  f : Polynomial (ZMod p)
  hfeq : f = ofList (List.map (algebraMap ℤ (ZMod p)) P)
  hirr : Irreducible f
  hneq : (List.map (algebraMap ℤ (ZMod p)) P).getLastD 0 ≠ 0
  hlen : P.length = n + 1
  c : Fin r → ℤ
  a : Fin r → ℤ
  hcmem : TT.basis.equivFun.symm c ∈ I
  hpmem : ↑p ∈ I
  z : Fin r → ℤ
  hBz : TT.basis.equivFun.symm z = 1
  hpol : List.ofFn c = List.sum
      (List.ofFn (fun (i : Fin (n + 1)) => if i = 0 then List.mulPointwise (P[i]' (by rw [hlen]; exact i.isLt)) (List.ofFn z)
      else List.mulPointwise (P[i]' (by rw [hlen] ; exact i.isLt )) (nPow_sq_table T (List.ofFn a) i) ))

lemma PrimeIdeal_polynomial_degree  {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : PrimeIdeal O p) : I.f.natDegree = I.n := by
    have hPlen : I.P.length = (ofList (List.map (algebraMap ℤ (ZMod p)) I.P)).natDegree + 1 := by
      rw [natDegree_ofList]
      exact Eq.symm (List.length_map I.P ⇑(algebraMap ℤ (ZMod p)))
      have := I.hneq
      by_contra hc
      erw [hc, List.getLastD_nil] at this
      exact this rfl
      refine eq_dropTrailingZeros_of_getLastD_ne_zero _ (I.hneq)
    rw [I.hfeq, ← Nat.succ_inj, Nat.succ_eq_add_one,  ← hPlen]
    exact I.hlen

def PrimeIdeal_residue_field_finite_dimensional {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
  (I : PrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] : FiniteDimensional (ZMod p) (O ⧸ I.I) := by
  have hcardaux :  Nat.card (O ⧸ I.I) = Fintype.card (ZMod p) ^ I.n := by
    rw [I.hcard]
    simp only [ZMod.card]
  refine FiniteDimensional.of_finrank_pos ?_
  rw [isAdjoinRoot_of_adjoin_root_irreducible_finite  hcardaux]
  exact I.hpos

lemma PrimeIdeal_residue_field_dimension {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
  (I : PrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] : FiniteDimensional.finrank (ZMod p) (O ⧸ I.I) = I.f.natDegree := by
  have hcardaux :  Nat.card (O ⧸ I.I) = Fintype.card (ZMod p) ^ I.n := by
    rw [I.hcard]
    simp only [ZMod.card]
  rw [PrimeIdeal_polynomial_degree ]
  exact isAdjoinRoot_of_adjoin_root_irreducible_finite  hcardaux

lemma PrimeIdeal_quotient_int_smul {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : PrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] (m : ℤ) (x : O) :
    Ideal.Quotient.mk I.I (m • x) = (m : ZMod p) • Ideal.Quotient.mk I.I x := by
  simp only [zsmul_eq_mul, map_mul, map_intCast]
  rw [Algebra.smul_def]
  simp only [map_intCast]

lemma PrimeIdeal_polynomial_aeval {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
  (I : PrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] :
  (aeval ((Ideal.Quotient.mk I.I) (I.TT.basis.equivFun.symm I.a))) I.f = 0 := by
  have hPlen : I.P.length = (ofList (List.map (algebraMap ℤ (ZMod p)) I.P)).natDegree + 1 := by
      rw [← I.hfeq, PrimeIdeal_polynomial_degree]
      exact I.hlen
  haveI : NeZero I.P.length := by
    rw [hPlen]
    exact NeZero.succ
  have aux : ∀ x , I.f.coeff x • ((Ideal.Quotient.mk I.I) (I.TT.basis.equivFun.symm I.a ^ x))
    = (Ideal.Quotient.mk I.I) ((I.P.getD x 0) • (I.TT.basis.equivFun.symm I.a ^ x)) := by
    intro x
    rw [PrimeIdeal_quotient_int_smul]
    have : ∀ x, ((I.P.getD x 0) : ZMod p) = I.f.coeff x := by
      rw [I.hfeq]
      intro j
      simp only [ algebraMap_int_eq, Int.coe_castRingHom, coeff_ofList]
      have auxz : Int.castRingHom (ZMod p) (0 : ℤ) = 0 := RingHom.map_zero (Int.castRingHom (ZMod p))
      erw [← auxz, List.getD_map I.P 0 (n := j) (Int.castRingHom (ZMod p))]
      rfl
    rw [this x]
  simp_rw [Polynomial.aeval_eq_sum_range, ← map_pow, aux, ← map_sum, Ideal.Quotient.eq_zero_iff_mem, I.hfeq]
  have hceq := table_polynomial_eval I.TT.table I.T I.TT.basis I.P I.z I.hBz I.a I.c I.TT.basis_mul_basis I.heq ?_
  convert I.hcmem
  rw [hceq, ← hPlen, Finset.sum_range]
  congr ; ext i
  congr
  simp only [List.getD_eq_getElem?_getD, Fin.is_lt, List.getElem?_eq_getElem, Option.getD_some,
    Fin.getElem_fin]
  rw [List.ofFn_congr I.hlen, I.hpol]
  congr
  refine funext ?_
  intro i
  simp only [Fin.getElem_fin, Fin.cast_eq_zero, Fin.coe_cast]


noncomputable def isAdjoinRoot_quot_ofPrimeIdeal {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : PrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] :
    IsAdjoinRoot (O ⧸ I.I) (I.f) := by
    haveI := PrimeIdeal_residue_field_finite_dimensional I
    refine IsAdjoinRoot_of_adjoin_root_irreducible I.f I.hirr ?_ ?_
    use Ideal.Quotient.mk I.I (I.TT.basis.equivFun.symm I.a)
    · exact PrimeIdeal_polynomial_aeval I
    · exact PrimeIdeal_residue_field_dimension I


noncomputable def PrimeIdeal_residue_field_is_field {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : PrimeIdeal O p) : IsField (O ⧸ I.I) := by
  haveI := ZModP_algebra_of_mem I.I p I.hpmem
  haveI := PrimeIdeal_residue_field_finite_dimensional I
  refine field_of_adjoin_root_irreducible (K := O ⧸ I.I) I.f I.hirr ?_ ?_
  · use ((Ideal.Quotient.mk I.I) (I.TT.basis.equivFun.symm I.a))
    exact PrimeIdeal_polynomial_aeval I
  · exact PrimeIdeal_residue_field_dimension I

lemma PrimeIdeal_isPrime {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : PrimeIdeal O p) : Ideal.IsPrime I.I := by
    refine Ideal.IsMaximal.isPrime ?_
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact PrimeIdeal_residue_field_is_field I

open Classical

lemma unit_eq_primitive_root_pow {R : Type*} [CommRing R] [Fintype R]
    {ζ : R} (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (x : Rˣ) :
    ∃ (n : ℕ), ζ ^ n = x := by
  have hu : IsUnit ζ := IsPrimitiveRoot.isUnit hr Fintype.card_pos
  obtain ⟨ζ',hz ⟩ := hu
  haveI : Fintype (Subgroup.zpowers ζ') := by exact
    (Subgroup.zpowers ζ').instFintypeSubtypeMemOfDecidablePred
  have heq : Subgroup.zpowers ζ' = ⊤ := by
    refine Subgroup.eq_top_of_le_card _ ?_
    rw [← Fintype.card_eq_nat_card (α := (Subgroup.zpowers ζ')), Fintype.card_zpowers,
    ← orderOf_units, hz, ← IsPrimitiveRoot.eq_orderOf hr, Fintype.card_eq_nat_card]
  have hmem : x ∈ Subgroup.zpowers ζ' := by
    rw [heq]
    exact trivial
  rw [Subgroup.mem_zpowers_iff] at hmem
  obtain ⟨k ,hk⟩ := hmem
  use (k % (orderOf ζ')).natAbs
  have hpow : ζ' ^ (k % (orderOf ζ')) = x := by
    rw [Int.emod_def, zpow_sub, hk, zpow_mul, zpow_natCast, pow_orderOf_eq_one]
    simp only [one_zpow, inv_one, mul_one]
  have hnpow : (↑(Int.natAbs (k % (orderOf ζ'))) : ℤ) = k % (orderOf ζ')  := by
    simp only [Int.natCast_natAbs, abs_eq_self]
    refine Int.emod_nonneg k (Int.ofNat_ne_zero.mpr ?_)
    have hu : orderOf ζ' = orderOf ζ := by
      rw [← hz]
      exact Eq.symm orderOf_units
    rw [hu]
    rw [← IsPrimitiveRoot.eq_orderOf hr]
    exact Fintype.card_ne_zero
  rw [← hnpow] at hpow
  rw [← hpow, zpow_natCast]
  simp only [Units.val_pow_eq_pow_val, hz]


noncomputable def LogFiniteRing {R : Type*} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (p : ℕ) : R → ZMod p := by
  intro x
  by_cases hc : IsUnit x
  · choose n _ using unit_eq_primitive_root_pow hr (hc.unit)
    exact (n : ZMod p)
  · exact 0

-- AVAILABLE IN UPDATED MATHLIB
@[to_additive]
theorem orderOf_dvd_sub_iff_zpow_eq_zpow [Group G] {x : G} {a b : ℤ} : (orderOf x : ℤ) ∣ a - b ↔ x ^ a = x ^ b := by
  rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]


lemma LogFiniteRing_of_pow  {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (n : ℕ) :
    LogFiniteRing hr p (ζ ^ n) = (n : ZMod p) := by
  have hc : IsUnit (ζ ^ n) := by
    refine IsUnit.pow n ?_
    exact IsPrimitiveRoot.isUnit hr Fintype.card_pos
  obtain ⟨ζ', hz ⟩ := IsPrimitiveRoot.isUnit hr Fintype.card_pos
  unfold LogFiniteRing
  simp only [hc, ↓reduceDIte]
  have aux := choose_spec (unit_eq_primitive_root_pow hr hc.unit)
  simp_rw [IsUnit.unit_spec, ← hz, ← Units.val_pow_eq_pow_val, ← zpow_natCast, Units.eq_iff,
    ← orderOf_dvd_sub_iff_zpow_eq_zpow, ← orderOf_units, hz, ← IsPrimitiveRoot.eq_orderOf hr] at aux
  symm
  refine (ZMod.eq_iff_modEq_nat p).mpr ?_
  refine Nat.modEq_of_dvd ?_
  refine dvd_trans (Int.natCast_dvd_natCast.2 hdvd) ?_
  convert aux
  simp only [IsUnit.unit_spec]
  simp_rw [ ← hz, ← Units.val_pow_eq_pow_val, ← zpow_natCast, Units.eq_iff,
    ← orderOf_dvd_sub_iff_zpow_eq_zpow, ← orderOf_units, hz, ← IsPrimitiveRoot.eq_orderOf hr]


lemma LogFiniteRing_of_ne_unit_eq_zero {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ))
    {x : R} (hx : ¬ IsUnit x) : LogFiniteRing hr p x = 0 := by
    unfold LogFiniteRing
    simp only [hx, ↓reduceDIte]

lemma LogFiniteRing_mul {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
   (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (x y : R)
   (hx : IsUnit x) (hy : IsUnit y) :
   LogFiniteRing hr p (x * y) = LogFiniteRing hr p x + LogFiniteRing hr p y := by
  obtain ⟨n, hn⟩ :=  unit_eq_primitive_root_pow hr hx.unit
  obtain ⟨m, hm⟩ :=  unit_eq_primitive_root_pow hr hy.unit
  rw [IsUnit.unit_spec] at hn hm
  have hmn : ζ ^ (n + m) = x * y := by
    rw [← hn, ← hm, pow_add]
  rw [← hmn, ← hm, ← hn, LogFiniteRing_of_pow hr hdvd, LogFiniteRing_of_pow hr hdvd, LogFiniteRing_of_pow hr hdvd]
  simp only [Nat.cast_add]

lemma LogFiniteRing_one {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) :
    LogFiniteRing hr p 1  = 0 := by
  rw [← pow_zero ζ, LogFiniteRing_of_pow hr hdvd]
  simp only [Nat.cast_zero]

-- AVAILABLE IN UPDATED MATHLIB
@[to_additive (attr := simp)]
lemma IsUnit.prod_iff {f : α → β} [CommMonoid β] : IsUnit (∏ a ∈ s, f a) ↔ ∀ a ∈ s, IsUnit (f a) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha hs => rw [Finset.prod_cons, IsUnit.mul_iff, hs, Finset.forall_mem_cons]

lemma LogFiniteRing_prod {R ι : Type*} {p : ℕ} [CommRing R] [Fintype R] (s : Finset ι) {ζ : R}
   (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ))
   (x : ι → R) (hx : ∀ i ∈ s, IsUnit (x i)) :
  LogFiniteRing hr p (∏ i ∈ s, x i) = ∑ i ∈ s, LogFiniteRing hr p (x i) := by
  induction' s using Finset.cons_induction_on with a s ha ih
  · simp only [Finset.prod_empty, Finset.sum_empty]
    exact LogFiniteRing_one hr hdvd
  · rw [Finset.forall_mem_cons] at hx
    simp only [Finset.cons_eq_insert, ha, not_false_eq_true, Finset.prod_insert, Finset.sum_insert, ← ih hx.2]
    refine LogFiniteRing_mul hr hdvd _ _ ?_ ?_
    · exact hx.1
    · rw [IsUnit.prod_iff]
      exact hx.2

lemma LogFiniteRing_p_power_eq_zero {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
  (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (x : R) :
  LogFiniteRing hr p (x ^ p) = 0 := by
  have hp : p ≠ 0
  · by_contra h
    rw [h, zero_dvd_iff] at hdvd
    exact Fintype.card_ne_zero hdvd
  by_cases hc : IsUnit x
  · obtain ⟨m, hm⟩ := unit_eq_primitive_root_pow hr hc.unit
    simp only [IsUnit.unit_spec] at hm
    rw [← hm, ← pow_mul, LogFiniteRing_of_pow hr hdvd _]
    simp only [Nat.cast_mul, CharP.cast_eq_zero, mul_zero]
  · rw [← isUnit_pow_iff hp] at hc
    exact LogFiniteRing_of_ne_unit_eq_zero hr hc

lemma LogFiniteRing_pow {R : Type*} {p : ℕ} [CommRing R] [Fintype R] {ζ : R}
    (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ)) (x : R) :
    LogFiniteRing hr p (x ^ n)  = n * LogFiniteRing hr p x := by
    by_cases hc : IsUnit x
    · obtain ⟨m, hm⟩ := unit_eq_primitive_root_pow hr hc.unit
      simp only [IsUnit.unit_spec] at hm
      rw [← hm, ← pow_mul, LogFiniteRing_of_pow hr hdvd _, LogFiniteRing_of_pow hr hdvd _]
      simp only [Nat.cast_mul, mul_comm]
    · by_cases hn : n = 0
      · rw [hn]
        simp only [pow_zero, Nat.cast_zero, zero_mul]
        rw [LogFiniteRing_one hr hdvd ]
      · have hcc := hc
        rw [← isUnit_pow_iff hn] at hc
        rw [LogFiniteRing_of_ne_unit_eq_zero hr hc, LogFiniteRing_of_ne_unit_eq_zero hr hcc]
        simp only [mul_zero]

open Matrix

lemma LogFiniteRing_hom_prod_eq_dot_product {S R ι : Type*} {p : ℕ} [CommRing R] [CommRing S] [Fintype R] [Fintype ι]
    {ζ : R} (hr : IsPrimitiveRoot ζ (Fintype.card Rˣ)) (hdvd : p ∣ (Fintype.card Rˣ))
    (φ : S →+* R) (x : ι → S) (hu : ∀ i, IsUnit (φ (x i))) (e : ι → ℕ) :
  LogFiniteRing hr p (φ (∏ i, (x i) ^ (e i))) =
  (fun i => LogFiniteRing hr p (φ (x i))) ⬝ᵥ (fun i => (e i : ZMod p)) := by
  simp_rw [map_prod, map_pow]
  rw [LogFiniteRing_prod _ hr hdvd]
  simp_rw [LogFiniteRing_pow hr hdvd]
  congr ; ext i ; dsimp
  rw [mul_comm]
  · intro i _
    exact IsUnit.pow (e i) (hu i)


noncomputable def MatrixLogProd {S ι τ : Type*} (p : ℕ) [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ)) : Matrix τ ι (ZMod p) :=
  fun i j => LogFiniteRing (hr i) p ((φ i) (x j))


lemma MatrixLogProd_def {S ι τ : Type*} (p : ℕ) [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ)) (i : τ) (j : ι) :
    (MatrixLogProd p F φ x ζ hr) i j = LogFiniteRing (hr i) p ((φ i) (x j)) := rfl


lemma exponent_vec_eq_zero_of_full_rank_matrix {S ι τ : Type*} {p : ℕ} [Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S) (e : ι → ℕ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hu : ∀ i j, IsUnit ((φ i) (x j)))
    (hrank : (MatrixLogProd p F φ x ζ hr).rank = Fintype.card ι)
    (hp : ∃ y, ∏ i, (x i) ^ (e i) = y ^ p) : ∀ i, p ∣ e i := by
  intro i
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd]
  let E : Matrix ι (Fin 1) (ZMod p) := fun i _ => (e i : ZMod p)
  obtain ⟨y, hy ⟩ := hp
  have hzM : (MatrixLogProd p F φ x ζ hr) * E = 0 := by
    ext i j
    fin_cases j
    simp [Matrix.mul_apply', MatrixLogProd, Pi.zero_apply]
    simp_rw [← LogFiniteRing_hom_prod_eq_dot_product (hr i) (hdvd i) (φ i) _ (hu i), hy,
    map_pow, LogFiniteRing_p_power_eq_zero (hr i) (hdvd i) ]
  have hle := Matrix.rank_add_rank_le_card_of_mul_eq_zero hzM
  rw [hrank] at hle
  simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero] at hle
  rw [← Matrix.rank_transpose] at hle
  have hEz : Eᵀ = 0 := by
    by_contra hc
    rw [LinearIndependent.rank_matrix ?_] at hle
    contradiction
    rw [linearIndependent_fin_succ]
    simp only [Nat.reduceAdd, Fin.tail_def, linearIndependent_empty_type, range_empty,
      Submodule.span_empty, Fin.isValue, Submodule.mem_bot, true_and]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hc
    fin_cases j
    simp only [Fin.zero_eta, Fin.isValue, ne_eq] at hj
    exact hj
  exact congr_fun (congr_fun hEz 0) i


lemma not_p_power_of_full_rank_matrix {S ι τ : Type*} {p : ℕ} [Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S) (e : ι → ℕ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hu : ∀ i j, IsUnit ((φ i) (x j)))
    (hrank : (MatrixLogProd p F φ x ζ hr).rank = Fintype.card ι) (he : ∃ i, ¬ p ∣ e i) :
    ¬ ∃ y , ∏ i, (x i) ^ (e i) = y ^ p := by
  obtain ⟨j ,hj⟩ := he
  by_contra hc
  exact hj (exponent_vec_eq_zero_of_full_rank_matrix F φ x e ζ hr hdvd hu hrank hc j)



lemma not_principal_of_full_rank_matrix {S ι τ : Type*} {p n : ℕ} [hp : Fact $ Nat.Prime p]
  [Fintype ι] [Fintype τ] (F : τ → Type*)
  [CommRing S] [IsDomain S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
  (u : ι → S) (hu : ∀ i, IsUnit (u i)) (hugen : ∀ (w : Sˣ), (∃ (e : ι → ℕ) , (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
  (I : Ideal S) (a : S) (hua : ∀ i, IsUnit ((φ i) a)) (hdvdp : p ∣ n) (h : I ^ n = Ideal.span {a})
  (hrank : (MatrixLogProd p F φ (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a)) ζ hr).rank = Fintype.card ι + 1) :
    ¬ ∃ b, I = Ideal.span {b} := by
  by_contra hb
  obtain ⟨c, hc⟩ := hb
  obtain ⟨m, hm⟩ := hdvdp
  set b := c ^ m with hb
  rw [hm, mul_comm, pow_mul, hc, Ideal.span_singleton_pow, ← hb,
    Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton] at h
  symm at h
  obtain ⟨w, hw⟩ := h
  obtain ⟨e, t, het⟩ := hugen w
  rw [mul_comm, het, mul_assoc, mul_comm _ a, ← mul_assoc, ← Units.mul_left_inj ((t⁻¹) ^ p), mul_assoc] at hw
  nth_rw 1 [inv_pow] at hw
  rw [(show ((t : S) ^ p  = ((t ^ p : Sˣ) : S)) by rfl), Units.mul_inv, mul_one] at hw
  erw [← mul_pow] at hw
  let e' := Sum.elim e (fun (i : Fin 1) => 1)
  let x := (Sum.elim (fun i => u i) (fun (i : Fin 1) => a))
  have auxp : ∏ i, x i ^ (e' i) = (∏ i : ι, u i ^ e i) * a := by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Finset.univ_unique, Fin.default_eq_zero,
      Fin.isValue, Sum.elim_inr, pow_one, Finset.prod_const, Finset.card_singleton, x, e']
  rw [← auxp] at hw
  refine not_p_power_of_full_rank_matrix F φ x e' ζ hr hdvd ?_ ?_ ?_ ?_
  · intro i j
    cases j
    · apply RingHom.isUnit_map
      simp only [Sum.elim_inl, x]
      exact hu _
    · exact hua i
  · rw [Fintype.card_sum, Fintype.card_ofSubsingleton]
    exact hrank
  · use Sum.inr 0
    simp only [Fin.isValue, Sum.elim_inr, Nat.dvd_one, e']
    refine Nat.Prime.ne_one hp.out
  · exact ⟨b * t⁻¹, hw⟩

























    --have aux : ∀ i, Eᵀ i = 0 := fun i => LinearIndependent.ne_zero i








-- (hu : ∀ i j, IsUnit (φ i j))






#exit

  --rw [← Int.natCast_inj, ZMod.intCast_eq_intCast_iff_dvd_sub]






-- (hdvd : p ∣ Fintype.card Rˣ)


/- def LogFiniteRing {F : Type*} {p : ℕ} [Field F] [Fintype F]
  (hdvd : p ∣ Fintype.card F ) (ζ : F)
  (hr : IsPrimitiveRoot ζ (Fintype.card F - 1)) : F → ZMod p := by
  intro x
  by_cases hc : x = 0
  · exact 0 -/





-- field_of_adjoin_root_irreducible





















      --refine not_subsingleton_iff_nontrivial.mp ?_
      --by_contra hc
      --have := Module.finrank_zero_of_subsingleton
      --exact Module.nontrivial_of_finrank_eq_succ




--end I


def O : Type := sorry

instance : CommRing O := sorry

instance : IsDomain O := sorry

instance : NoZeroSMulDivisors ℤ O := sorry

def TT : TimesTable (Fin 5) ℤ O :=
  { basis := sorry,
    table := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
  ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![2, -5, 0, 2, 0]],
  ![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![4, -10, 0, 5, 0],![0, 2, -3, 0, 4]],
  ![![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![4, -10, 0, 5, 0],![0, 4, -5, 0, 10],![8, -20, 2, 5, 0]],
  ![![0, 0, 0, 0, 1],![2, -5, 0, 2, 0],![0, 2, -3, 0, 4],![8, -20, 2, 5, 0],![0, 3, -6, 1, 3]]]
    basis_mul_basis := sorry }

def B := TT.basis

lemma B_one : TT.basis 0 = 1 := sorry

lemma B_one_repr : TT.basis.equivFun.symm ![1, 0, 0, 0, 0] = 1 := sorry

def T : Fin 5 → Fin 5 → List ℤ :=
  ![ ![[1, 0, 0, 0, 0],[0, 1, 0, 0, 0],[0, 0, 1, 0, 0],[0, 0, 0, 1, 0],[0, 0, 0, 0, 1]],
  ![[0, 1, 0, 0, 0],[0, 0, 1, 0, 0],[0, 0, 0, 1, 0],[0, 0, 1, 0, 2],[2, -5, 0, 2, 0]],
  ![[0, 0, 1, 0, 0],[0, 0, 0, 1, 0],[0, 0, 1, 0, 2],[4, -10, 0, 5, 0],[0, 2, -3, 0, 4]],
  ![[0, 0, 0, 1, 0],[0, 0, 1, 0, 2],[4, -10, 0, 5, 0],[0, 4, -5, 0, 10],[8, -20, 2, 5, 0]],
  ![[0, 0, 0, 0, 1],[2, -5, 0, 2, 0],[0, 2, -3, 0, 4],[8, -20, 2, 5, 0],[0, 3, -6, 1, 3]]]

lemma T_eq_TT : ∀ (i j : Fin 5), T i j = List.ofFn (TT.table i j) := by simp ; decide

def I : Ideal O := Ideal.span (Set.range (fun i ↦ TT.basis.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 3, 1, 0, 0]] i)))


def A' : IdealEqSpanCertificate O ℤ TT I
  ![![11, 0, 0, 0, 0], ![3, 3, 1, 0, 0]]
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 3, 1, 0, 0], ![2, 5, 0, 1, 0], ![2, 3, 0, 0, 1]] where
  T := T
  heq := T_eq_TT
  hieq := rfl
  M := ![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]],
  ![![3, 3, 1, 0, 0], ![0, 3, 3, 1, 0], ![0, 0, 4, 3, 2], ![4, -10, 3, 8, 6], ![6, -13, -3, 6, 7]]]
  hmulB := by simp[table_mul_list] ; decide
  f := ![![![-11, 0, 44, 31, 18], ![44, -44, -99, 0, 0]], ![![0, -11, 0, 5, 6], ![0, 44, -33, 0, 0]],
    ![![-3, -3, 11, 9, 6], ![12, 0, -33, 0, 0]], ![![-2, -5, 8, 8, 6], ![8, 12, -33, 0, 0]], ![![-2, -3, 8, 7, 5], ![8, 4, -27, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -3, 11, 0, 0], ![-2, -5, 0, 11, 0],
   ![-2, -3, 0, 0, 11]], ![![0, 0, 1, 0, 0], ![-1, -1, 3, 1, 0], ![-2, -3, 4, 3, 2], ![-3, -7, 3, 8, 6], ![-1, -5, -3, 6, 7]]]
  hle1 := by simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, List.ofFn_succ,
    Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_succ, List.ofFn_zero, zero_add, Fin.cast_eq_self, Matrix.vecCons_const] ; decide
  hle2 := by simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero,
    Matrix.vecCons_const, Matrix.cons_val_succ, List.ofFn_zero, zero_add, Fin.cast_eq_self] ; decide

lemma I_mem : ↑11 ∈ I := by
  unfold I
  refine Submodule.subset_span ?_
  use 0
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
    Basis.equivFun_symm_apply, zsmul_eq_mul]
  rw [Finset.sum_eq_single_of_mem 0 , B_one]
  · simp only [Fin.isValue, Matrix.cons_val_zero, Int.cast_ofNat, mul_one]
  · exact Finset.mem_univ 0
  · intro b hb hbz
    fin_cases b
    · contradiction
    all_goals {simp}


lemma I_card : Nat.card (O ⧸ I) = 11 ^ 2 := by
  refine ideal_norm_eq_prod O B I ?_ ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![3, 3, 1, 0, 0], ![2, 5, 0, 1, 0], ![2, 3, 0, 0, 1]] ?_ ?_
  · by_contra hc
    have := I_mem
    rw [hc] at this
    simp only [Ideal.mem_bot] at this
    have aux : 11 = (11 : ℤ) • (1 : O) := by simp only [zsmul_eq_mul, Int.cast_ofNat, mul_one]
    rw [aux, smul_eq_zero] at this
    simp only [OfNat.ofNat_ne_zero, one_ne_zero, or_self] at this
  · decide
  · exact ideal_eq_of_IdealEqSpanCertificate O ℤ A'

instance : Fact $ Nat.Prime 11 := by decide

def I_prime : PrimeIdeal O 11 where
  r := 5
  n := 2
  hpos := by decide
  TT := TT
  T := T
  heq := T_eq_TT
  I := I
  hcard := I_card
  P := [3, 3, 1]
  f := ofList [3, 3, 1]
  hfeq := by simp;
  hirr := by sorry
  hneq := by decide
  hlen := by decide
  c := ![3, 3, 1, 0, 0]
  a := ![0, 1, 0, 0, 0]
  hcmem := by
    refine Submodule.subset_span ?_
    use 1
    rfl
  hpmem := I_mem
  z := ![1, 0, 0, 0 ,0]
  hBz := B_one_repr
  hpol := by rfl



#exit


def A : IdealEqSpanCertificate O ℤ TT I
  ![![11, 0, 0, 0, 0], ![3, 3, 1, 0, 0]]
  ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![7, 8, -2, 0, 1], ![3, 3, 1, 0, 0], ![12, 5, -1, 1, 1]] where
  T := T
  heq := T_eq_TT
  hieq := rfl
  M := ![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]],
  ![![3, 3, 1, 0, 0], ![0, 3, 3, 1, 0], ![0, 0, 4, 3, 2], ![4, -10, 3, 8, 6], ![6, -13, -3, 6, 7]]]
  hmulB := by simp[table_mul_list] ; decide
  f := ![![![-11, 0, 44, 31, 18], ![44, -44, -99, 0, 0]], ![![0, -11, 0, 5, 6],
    ![0, 44, -33, 0, 0]], ![![-7, -8, 30, 25, 17], ![28, 4, -93, 0, 0]],
    ![![-3, -3, 11, 9, 6], ![12, 0, -33, 0, 0]], ![![-12, -5, 49, 37, 23], ![48, -28, -126, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-3, -3, 0, 11, 0],
    ![-2, 6, -11, -11, 11], ![-13, -14, 11, 22, 0]], ![![0, 0, 0, 1, 0], ![-1, 0, -1, 2, 1],
    ![-4, -2, -1, 5, 3], ![-9, -5, -2, 7, 8], ![-8, -6, 1, 5, 6]]]
  hle1 := by simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, List.ofFn_succ,
    Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.cons_val_succ, List.ofFn_zero, zero_add, Fin.cast_eq_self, Matrix.vecCons_const] ; decide
  hle2 := by simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Int.reduceNeg, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, List.ofFn_succ, Fin.isValue, Matrix.cons_val_zero,
    Matrix.vecCons_const, Matrix.cons_val_succ, List.ofFn_zero, zero_add, Fin.cast_eq_self] ; decide



example : I.carrier = Submodule.span ℤ
  (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![7, 8, -2, 0, 1], ![3, 3, 1, 0, 0], ![12, 5, -1, 1, 1]] i))) := by
exact ideal_eq_of_IdealEqSpanCertificate O ℤ A


def I₁ : Ideal O := Ideal.span (Set.range (fun i ↦ TT.basis.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 3, 1, 0, 0]] i)))
def I₂ : Ideal O := Ideal.span (Set.range (fun i ↦ TT.basis.equivFun.symm (![![11, 0, 0, 0, 0], ![7, 4, 1, 0, 0]] i)))
def I₃ : Ideal O := Ideal.span (Set.range (fun i ↦ TT.basis.equivFun.symm (![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))



def Mul1 : IdealMulEqCertificate O ℤ TT I₁ I₂
  ![![11, 0, 0, 0, 0], ![3, 3, 1, 0, 0]] ![![11, 0, 0, 0, 0], ![7, 4, 1, 0, 0]]
  ![![-39, 11, 17, -2, -10 ]] where
  T := T
  heq := T_eq_TT
  hI1 := rfl
  hI2 := rfl
  M := ![![![121,0,0,0,0], ![77,44,11,0,0]], ![![33,33,11,0,0], ![21,33,23,7,2]]]
  hmul := by simp[table_mul_list] ; decide
  f := ![![![![-484103393775 , 5659316100861 , 3324040951585  , 849109181313 , 953625794],
  ![  761656006206 , -9330518028830 , -806914134  ,  0  , -806914134]],  ![![ 200359 , 3970 , 0 , 0 , 0], ![39,0,0,0,0]]]]
  g := ![![![![-11 , 11 , 11  , 0  , 0]] , ![![-7,3,11,5,2]]] , ![![![-3 , 0 , 6  , 4  , 2]] , ![![1,-8,5,8,6]]]]
  hle1 := by simp[table_mul_list] ; decide
  hle2 := by simp[table_mul_list] ; decide



def Mul2 : IdealMulEqCertificate O ℤ TT (I₁ * I₂) I₃
  ![![-39, 11, 17, -2, -10 ]] ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![11, 0, 0, 0 ,0 ]] where
  T := T
  heq := T_eq_TT
  hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ TT I₁ I₂ _ _ _ Mul1
  hI2 := rfl
  M := ![![![-429 , 121 , 187 , -22 , -110] , ![-176 , 55 , 77, -11 , -44]]]
  hmul := by simp[table_mul_list] ; decide
  f := ![![![![-81699 , -20253   , 43   , 0   , 0] , ![224672 , -472 , 0 , 0 , 0]]]]
  g := ![![![![-39, 11, 17, -2, -10]] , ![![-16, 5, 7, -1, -4]]]]
  hle1 := by simp[table_mul_list] ; decide
  hle2 := by simp[table_mul_list] ; decide


lemma Mul11 :  Ideal.span {TT.basis.equivFun.symm ![11, 0, 0, 0, 0]} = I₁ * I₂ * I₃ := by
  rw [ideal_eq_mul_of_IdealMulEqCertificate O ℤ TT _ _ _ _ _ Mul2]
  simp






--FnOfList

/-
have zero_add': ∀ (l : List ℤ) , 0 + l = l := by simp only [zero_add, implies_true]
  have add_zero': ∀ (l : List ℤ) , l + 0 = l := by simp only [add_zero, implies_true]
  simp only [LinearEquiv.toFun_eq_coe, Basis.equivFun_symm_eq_repr_symm' B]
  apply_fun B.repr
  simp only [Basis.repr_symm_apply, map_add, map_sum, map_smul, Basis.repr_total, smul_smul]
  simp_rw [List.mulPointwise_ofFn] at h
  cases m
  · cases n
    · simp only [Nat.add_zero, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      dsimp at c
      exact Subsingleton.eq_zero (Finsupp.equivFunOnFinite.symm c)
    · rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a2 l * ↑p) • b2 l))] at h
      simp only [List.ofFn_zero, List.sum_nil, zero_add', List.ofFn_inj] at h
      ext k
      rw [h]
      simp only [zsmul_eq_mul, Int.cast_mul, Pi.intCast_def, Int.cast_id, Int.cast_natCast, Pi.natCast_def,
      Finset.sum_apply, Pi.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Finsupp.coe_zero,
      Pi.zero_apply, Finsupp.finset_sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      Finsupp.equivFunOnFinite_symm_apply_toFun, smul_eq_mul, zero_add]
  · cases n
    · rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a1 l) • b1 l))] at h
      simp only [List.ofFn_zero, List.sum_nil, add_zero', List.ofFn_inj] at h
      ext k
      rw [h]
      simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Int.cast_mul, Int.cast_natCast, Pi.natCast_def,
      Finsupp.equivFunOnFinite_symm_apply_toFun, Pi.add_apply, Finset.sum_apply, Pi.mul_apply,
      Finsupp.coe_add, Finsupp.coe_finset_sum, Finsupp.coe_smul, Nat.succ_eq_add_one,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    · rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a2 l * ↑p) • b2 l))] at h
      rw [← (List.sum_ofFn' (Nat.succ_ne_zero _) (fun l => (a1 l) • b1 l))] at h
      simp only [List.add_ofFn, List.ofFn_inj] at h
      ext k
      rw [h]
      simp only [zsmul_eq_mul, Pi.intCast_def, Int.cast_id, Int.cast_mul, Int.cast_natCast, Pi.natCast_def,
      Finsupp.equivFunOnFinite_symm_apply_toFun, Pi.add_apply, Finset.sum_apply, Pi.mul_apply,
      Finsupp.coe_add, Finsupp.coe_finset_sum, Finsupp.coe_smul]
  exact LinearEquiv.injective B.repr



-/




-- List.sum (List.ofFn (λ l => List.mulPointwise ((w2 l) * p) (List.ofFn (b2 l)))))









    --let f := (Submodule.span R (Set.range w)).subtype









 -- ∀ (j : τ), ∃ (b : ι → O), w j = ∑ (i : ι), (b i) * (v i) := by
