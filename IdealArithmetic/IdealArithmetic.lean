import IdealArithmetic.TimesTableAsLists
import IdealArithmetic.TimesTable.Defs
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FreeModule.PID

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




end I




#exit


def O : Type := sorry

instance : CommRing O := sorry

def TT : TimesTable (Fin 5) ℤ O :=
  { basis := sorry,
    table := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]],
  ![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![2, -5, 0, 2, 0]],
  ![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![4, -10, 0, 5, 0],![0, 2, -3, 0, 4]],
  ![![0, 0, 0, 1, 0],![0, 0, 1, 0, 2],![4, -10, 0, 5, 0],![0, 4, -5, 0, 10],![8, -20, 2, 5, 0]],
  ![![0, 0, 0, 0, 1],![2, -5, 0, 2, 0],![0, 2, -3, 0, 4],![8, -20, 2, 5, 0],![0, 3, -6, 1, 3]]]
    basis_mul_basis := sorry }

def B := TT.basis

def T : Fin 5 → Fin 5 → List ℤ :=
  ![ ![[1, 0, 0, 0, 0],[0, 1, 0, 0, 0],[0, 0, 1, 0, 0],[0, 0, 0, 1, 0],[0, 0, 0, 0, 1]],
  ![[0, 1, 0, 0, 0],[0, 0, 1, 0, 0],[0, 0, 0, 1, 0],[0, 0, 1, 0, 2],[2, -5, 0, 2, 0]],
  ![[0, 0, 1, 0, 0],[0, 0, 0, 1, 0],[0, 0, 1, 0, 2],[4, -10, 0, 5, 0],[0, 2, -3, 0, 4]],
  ![[0, 0, 0, 1, 0],[0, 0, 1, 0, 2],[4, -10, 0, 5, 0],[0, 4, -5, 0, 10],[8, -20, 2, 5, 0]],
  ![[0, 0, 0, 0, 1],[2, -5, 0, 2, 0],[0, 2, -3, 0, 4],[8, -20, 2, 5, 0],[0, 3, -6, 1, 3]]]

lemma T_eq_TT : ∀ (i j : Fin 5), T i j = List.ofFn (TT.table i j) := by simp ; decide

def I : Ideal O := Ideal.span (Set.range (fun i ↦ TT.basis.equivFun.symm (![![11, 0, 0, 0, 0], ![3, 3, 1, 0, 0]] i)))


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
