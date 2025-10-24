import IdealArithmetic.TimesTableAsLists
import IdealArithmetic.TimesTable.Defs
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FreeModule.PID
import IdealArithmetic.AlgebraAuxiliaryLemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
--import Mathlib.Data.ZMod.Algebra
import IdealArithmetic.QuotientModules
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Tactic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Matrix.Rank
import Mathlib.Algebra.Group.Subgroup.Finsupp
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Complement



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
    erw [Submodule.mem_span_range_iff_exists_fun] at hvw
    obtain ⟨a, ha⟩ :=  hvw
    use a
    exact ha.symm
  · intro h
    have : ∀ i , v i ∈ (Submodule.span R (Set.range w)) := by
      intro i
      rw [Submodule.mem_span_range_iff_exists_fun]
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
          rw [hI]
          exact zero_mem (Submodule.span R (Set.range w))
        smul_mem' := by
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
    erw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    have hmem : ∀ i , c i ∈ Submodule.span R (Set.range B) := by
      intro i
      rw [← hspan]
      simp only [Submodule.mem_top]
    simp_rw [Submodule.mem_span_range_iff_exists_fun] at hmem
    let f : ι → (τ → R) := fun i => ((hmem i).choose)
    have hceq : ∀ i , ∑ j : τ , (f i j) • (B j) = c i := by
      intro i
      exact (hmem i).choose_spec
    simp_rw [← hceq] at hc
    erw [Submodule.mem_span_range_iff_exists_fun, ← hc]
    use (fun ⟨i, j⟩ => f i j)
    dsimp
    let F : ι → (τ → O) := fun i => (fun j => (f i j) • ((v i) * (B j)))
    rw [Fintype.sum_prod_type' F]
    simp_rw [Finset.sum_mul]
    congr ; ext i ; congr ; ext j
    rw [Algebra.smul_mul_assoc, mul_comm]
  · intro hx
    erw [Submodule.mem_span_range_iff_exists_fun] at hx
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

/- Prove equality of ideals from O-generators. -/
structure IdealEqCertificateO [Algebra R O]
  {r n m : ℕ} (TT  : TimesTable (Fin r) R O) (I : Ideal O) (J : Ideal O) (v : Fin m → Fin r → R)
  (w : Fin n → Fin r → R) where
  T : Fin r → Fin r → List R
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  hieq1 : I = Ideal.span (Set.range (fun i => TT.basis.equivFun.symm (v i)))
  hieq2 : J = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm (w j)))
  g : Fin m → Fin n → Fin r → R
  h : Fin n → Fin m → Fin r → R
  hle1 : ∀ i, List.ofFn (v i) = List.sum (List.ofFn (fun k => table_mul_list T  (List.ofFn (g i k)) (List.ofFn (w k))))
  hle2 : ∀ i, List.ofFn (w i) = List.sum (List.ofFn (fun k => table_mul_list T  (List.ofFn (h i k)) (List.ofFn (v k))))

lemma ideal_eq_of_IdealEqCertificateO [Algebra R O]
  {r n m : ℕ} (TT  : TimesTable (Fin r) R O) (I : Ideal O) (J : Ideal O) (v : Fin m → Fin r → R)
  (w : Fin n → Fin r → R) (A : IdealEqCertificateO O R TT I J v w) : I = J := by
  let A1 : IdealLeCertificateO O R O TT I J v w :=
    { T := A.T
      heq := A.heq
      hieq1 := by
        rw [A.hieq1] ; rfl
      hieq2 := A.hieq2
      g := A.g
      hle2 := A.hle1 }
  let A2 : IdealLeCertificateO O R O TT J I w v :=
    { T := A.T
      heq := A.heq
      hieq1 := by
        rw [A.hieq2] ; rfl
      hieq2 := A.hieq1
      g := A.h
      hle2 := A.hle2 }
  refine le_antisymm ?_ ?_
  · exact ideal_le_of_IdealLeCertificateO _ _ _ TT I J v w A1
  · exact ideal_le_of_IdealLeCertificateO _ _ _ TT J I w v A2




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
  erw [A.hieq, Submodule.mem_span_range_iff_exists_fun]
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
        rw [Submodule.mem_span_range_iff_exists_fun] at aux
        obtain ⟨c, hc⟩ := aux
        simp only [Submodule.mem_span_range_iff_exists_fun, ← hc, TensorProduct.tmul_sum,
          TensorProduct.tmul_smul, P]
        use (fun i => (c i) • x)
        congr ; ext i
        rw [smul_assoc, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      · intro x y hx hy
        exact Submodule.add_mem _ hx hy
    intro x _
    exact this x
  have := linearIndependent_of_top_le_span_of_card_eq_finrank hle (Eq.symm
    (Module.finrank_eq_card_basis B'))
  rw [linearIndependent_iff'] at this ⊢
  intro s g hg i his
  rw [← FaithfulSMul.algebraMap_eq_zero_iff R Q]
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
rw [← SetLike.coe_set_eq]
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

structure IdealMulPrincipalCertificate [Algebra R O] {r m : ℕ} [NeZero r]
  (TT  : TimesTable (Fin r) R O) (I : Ideal O)
  (α : Fin r → R) (u : Fin m → Fin r → R) (w : Fin m → Fin r → R) where
  T : Fin r → Fin r → List R
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  hI : I = Ideal.span (Set.range (fun i => (TT.basis).equivFun.symm (u i)))
  hmul : ∀ i, table_mul_list T (List.ofFn α) (List.ofFn (u i)) = List.ofFn (w i)

lemma  ideal_eq_principal_mul_of_IdealMulPrincipalCertificate [Algebra R O] {r m : ℕ} [NeZero r]
  (TT  : TimesTable (Fin r) R O) (I : Ideal O)
  (α : Fin r → R) (u : Fin m → Fin r → R) (w : Fin m → Fin r → R)
  (A : IdealMulPrincipalCertificate O R TT I α u w) :
    Ideal.span {(TT.basis).equivFun.symm α} * I = Ideal.span (Set.range (fun i => (TT.basis).equivFun.symm (w i))) := by
  have aux := A.hmul
  simp_rw [table_mul_eq_table_mul' TT.table A.T A.heq] at aux
  rw [A.hI, Ideal.span_mul_span]
  congr
  simp only [Set.mem_singleton_iff, Set.mem_range, Set.iUnion_exists,
    Set.iUnion_iUnion_eq', Set.iUnion_singleton_eq_range, Set.iUnion_iUnion_eq_left]
  have : (fun i ↦ TT.basis.equivFun.symm (w i)) = fun x ↦ TT.basis.equivFun.symm α * TT.basis.equivFun.symm (u x) := by
    ext i
    exact (table_mul_list_eq_mul TT.table TT.basis _ _ _ TT.basis_mul_basis (aux i).symm).symm
  rw [this]

-- Prove element is nonzero from proof coordinates are not zero:
-- (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr hv

lemma ideal_mem_principal_class [Algebra R O] {r : ℕ} [NeZero r] (B : Basis (Fin r) R O)
  (I : Ideal O) (v : Fin r → R) (hv : v ≠ 0) (hI : I = Ideal.span (Set.range (fun _ : Fin 1 => B.equivFun.symm v))) :
   ∃ (α β : O), ∃ (_ : α ≠ 0), ∃ (_ : β ≠ 0),
      Ideal.span {α} * I = Ideal.span {β} := by
  use 1 , B.equivFun.symm v
  have haux : B.equivFun.symm v ≠ 0 := (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr hv
  have : Nontrivial O := nontrivial_of_ne (B.equivFun.symm v) 0 haux
  use (zero_ne_one' O).symm , haux
  simp only [Ideal.span_singleton_one, Ideal.top_mul]
  convert hI
  simp only [Basis.equivFun_symm_apply, Set.range_const]

lemma ideal_mem_principal_class'
  [Algebra R O] {r : ℕ} [NeZero r] (B : Basis (Fin r) R O)
  (I : Ideal O) {J : Ideal O} (v : Fin r → R) (hv : v ≠ 0)
  (hI : I = Ideal.span (Set.range (fun i : Fin 1 => B.equivFun.symm (![v] i) ))) :
   ∃ (α β : O), ∃ (_ : α ≠ 0), ∃ (_ : β ≠ 0),
      Ideal.span {α} * I = Ideal.span {β} * J ^ 0 := by
  convert ideal_mem_principal_class (r := r) O R B I v hv ?_
  · simp only [pow_zero, Ideal.one_eq_top, Ideal.mul_top]
  · rw [hI]
    refine congrArg _ ?_
    simp only [Matrix.cons_val_fin_one, Basis.equivFun_symm_apply, Set.range_const]

lemma ideal_mul_span_singleton_coe [Algebra R O] {r m : ℕ} [NeZero r] (B : Basis (Fin r) R O)
  (I : Ideal O) (v : Fin m → Fin r → R)
  (hI : I = Ideal.span (Set.range (fun i => B.equivFun.symm (v i)))) (r : R) :
  Ideal.span {(algebraMap R O r)} * I = Ideal.span (Set.range (fun i => B.equivFun.symm ((r • v) i))) := by
  rw [hI, Ideal.span_mul_span] ; congr
  simp only [Set.mem_singleton_iff, Basis.equivFun_symm_apply, Set.mem_range, Set.iUnion_exists,
    Set.iUnion_iUnion_eq', Set.iUnion_singleton_eq_range, Set.iUnion_iUnion_eq_left, Pi.smul_apply,
    map_smul]
  refine congrArg (f := Set.range) ?_
  simp only [Basis.equivFun_symm_apply, Algebra.smul_def, Pi.smul_apply, Pi.mul_apply,
    Pi.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply, map_mul]

end I

open Polynomial


noncomputable def IsAdjoinRoot_of_adjoin_root_irreducible {F K : Type*} [CommRing K] [Field F]
  [DecidableEq F] [Algebra F K] [FiniteDimensional F K] (f : F[X]) (hI : Irreducible f)
  (ha : ∃ (a : K) , Polynomial.aeval a f = 0 )
  (hr : Module.finrank F K = f.natDegree) : IsAdjoinRoot K f := by
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
    · rw [← Module.finrank_pos_iff (R := F), hr]
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
  (hr : Module.finrank F K = f.natDegree) : IsField K := by
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
    Module.finrank F (O ⧸ I) = n := by
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
    convert Module.finrank_eq_card_basis ({repr := Ba})
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
    erw [Matrix.transpose_apply, LinearMap.toMatrix_apply]
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

lemma ideal_norm_eq_prod' {O : Type*} [CommRing O] [IsDomain O]
    (B : Basis (Fin r) ℤ O) (I : Ideal O) (V : Fin r → Fin r → ℤ) (hd : ∀ i j, i < j → V i j = 0)
    (i : Fin r) (j : Fin r) (hij : V i j ≠ 0)
    (heq : I.carrier = Submodule.span ℤ (Set.range (fun i => B.equivFun.symm (V i)))) :
    Nat.card (O ⧸ I) = (∏ i, V i i).natAbs := by
  refine ideal_norm_eq_prod O B I ?_ V hd heq
  have : B.equivFun.symm (V i) ∈ I := by
    show B.equivFun.symm (V i) ∈ I.carrier
    rw [heq]
    apply Submodule.subset_span
    simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Set.mem_range, exists_apply_eq_apply]
  intro hc
  have := Ideal.mem_bot.1 (hc ▸ this)
  apply_fun B.equivFun at this
  simp only [LinearEquiv.apply_symm_apply, Basis.equivFun_apply, map_zero, Finsupp.coe_zero] at this
  apply_fun (fun f => f j) at this
  exact hij this



noncomputable def isAdjoinRoot_of_adjoin_root_irreducible_finite {F K : Type*} {n : ℕ}
  [AddCommGroup K] [Field F] [Fintype F] [DecidableEq F] [Module F K]
  (hr : Nat.card K = Fintype.card F ^ n) : Module.finrank F K = n := by
  haveI : Fintype K := by
    haveI := ((Nat.card_pos_iff (α := K)).1 ?_).2
    exact Fintype.ofFinite K
    rw [hr]
    refine pow_pos (Fintype.card_pos) _
  haveI : FiniteDimensional F K := Module.IsNoetherian.finite F K
  rw [Nat.card_eq_fintype_card, Module.card_fintype (M := K) (R := F) (Basis.ofVectorSpace F K),
    ← Module.finrank_eq_card_basis (Basis.ofVectorSpace F K) ] at hr
  apply_fun (fun x => Fintype.card F ^ x)
  dsimp
  exact hr
  refine Nat.pow_right_injective (Nat.succ_le_of_lt (Fintype.one_lt_card) )

noncomputable def ZModP_algebra_of_mem {O : Type*} [CommRing O] (I : Ideal O)
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
  z : Fin r → ℤ
  --hpmem : ↑p ∈ I
  hBz : TT.basis.equivFun.symm z = 1
  hpmem : TT.basis.equivFun.symm ((p : ℤ) • z) ∈ I
  hpol : List.ofFn c = List.sum
      (List.ofFn (fun (i : Fin (n + 1)) => if i = 0 then List.mulPointwise (P[i]' (by rw [hlen]; exact i.isLt)) (List.ofFn z)
      else List.mulPointwise (P[i]' (by rw [hlen] ; exact i.isLt )) (nPow_sq_table T (List.ofFn a) i) ))

lemma PrimeIdeal_polynomial_degree  {O : Type*} {p : ℕ} [Fact $ Nat.Prime p] [CommRing O]
    (I : PrimeIdeal O p) : I.f.natDegree = I.n := by
    have hPlen : I.P.length = (ofList (List.map (algebraMap ℤ (ZMod p)) I.P)).natDegree + 1 := by
      rw [natDegree_ofList]
      exact Eq.symm (List.length_map ⇑(algebraMap ℤ (ZMod p)))
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
  (I : PrimeIdeal O p) [Algebra (ZMod p) (O ⧸ I.I)] : Module.finrank (ZMod p) (O ⧸ I.I) = I.f.natDegree := by
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
    exact Nat.instNeZeroSucc
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
  have hpmem : ↑p ∈ I.I := by
    have := I.hpmem
    rw [LinearEquiv.map_smul, I.hBz] at this
    simp only [zsmul_eq_mul, Int.cast_natCast, mul_one] at this
    exact this
  haveI := ZModP_algebra_of_mem I.I p hpmem
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


/- noncomputable def ringEquivZModOfCard {R : Type*} [Ring R] [Fintype R] {p : ℕ}
  [Fact $ Nat.Prime p] (hcard : Fintype.card R = p) : R ≃+* (ZMod p) := by
  have := charP_of_card_eq_prime _ hcard
  symm
  refine RingEquiv.ofBijective (ZMod.castHom (Nat.dvd_refl p) R) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro i j hij
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val] at hij
    erw [CharP.natCast_eq_natCast R p, ← ZMod.eq_iff_modEq_nat] at hij
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq] at hij
    exact hij
  · rw [hcard]
    exact ZMod.card _ -/

noncomputable def modIdealEquivZMod {O : Type*} {p : ℕ} (hp : Nat.Prime p) [CommRing O] (I : Ideal O)
  (hcard : Nat.card (O ⧸ I) = p) : O ⧸ I ≃+* (ZMod p) := by
  haveI : Finite (O ⧸ I) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact Nat.Prime.ne_zero hp
  haveI : Fintype (O ⧸ I) := Fintype.ofFinite _
  exact (ZMod.ringEquivOfPrime _ hp (Eq.trans (Fintype.card_eq_nat_card ) hcard)).symm


noncomputable def modIdealToZMod {O : Type*} {p : ℕ} (hp : Nat.Prime p) [CommRing O] (I : Ideal O)
  (hcard : Nat.card (O ⧸ I) = p) : O ⧸ I →+* (ZMod p) := by
  haveI : Finite (O ⧸ I) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hcard]
    exact Nat.Prime.ne_zero hp
  haveI : Fintype (O ⧸ I) := Fintype.ofFinite _
  exact (id (ZMod.ringEquivOfPrime _ hp (Eq.trans (Fintype.card_eq_nat_card ) hcard)).symm).toRingHom

lemma prime_ideal_of_norm_prime {O : Type*} {p : ℕ} (hp : Nat.Prime p) [CommRing O] (I : Ideal O)
  (hcard : Nat.card (O ⧸ I) = p) : Ideal.IsPrime I := by
  haveI : Fact $ Nat.Prime p := {out := hp}
  refine Ideal.IsMaximal.isPrime ?_
  rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
  refine MulEquiv.isField (A := O ⧸ I) (ZMod p) ?_ (modIdealEquivZMod hp I hcard)
  exact Field.toIsField (ZMod p)


/- lemma modIdealToZMod_apply {O : Type u_1} {p : ℕ} (hp : Nat.Prime p) [CommRing O] (I : Ideal O)
  (hcard : Nat.card (O ⧸ I) = p) (m : ℤ) : (modIdealToZMod hp I hcard) m = m := by
    unfold modIdealToZMod
    simp only [id_eq, RingEquiv.toRingHom_eq_coe, map_intCast] -/


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
--@[to_additive]
--theorem orderOf_dvd_sub_iff_zpow_eq_zpow [Group G] {x : G} {a b : ℤ} : (orderOf x : ℤ) ∣ a - b ↔ x ^ a = x ^ b := by
 -- rw [orderOf_dvd_iff_zpow_eq_one, zpow_sub, mul_inv_eq_one]


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


/- Note : We could generalize this with expressions of the form
 ` ∏ i, (x i) ^ (e i) * z ^ p = y ^ p` however we have to impose extra assumptions. Either,
 * We ask for `z` or `y` to be units under every `φ`, so the logarithm splits into a sum on the LHS.
 * We ask that the ring `S` satisfies the property that `x * y ^ p = z ^ p` implies that
 `x` is a `p`-power. In particular, we can ask `S` to be integrally closed, for instance.

See : IsIntegrallyClosed.pow_dvd_pow_iff  -/
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
    simp only [mul_apply', MatrixLogProd, zero_apply, E]
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

lemma exponent_vec_eq_zero_of_full_rank_matrix' {S ι τ : Type*} {p : ℕ} [hp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [∀ i, CommRing (F i)]
    [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i)) (x : ι → S) (e : ι → ℕ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hu : ∀ i j, IsUnit ((φ i) (x j)))
    (hrank : (MatrixLogProd p F φ x ζ hr).rank = Fintype.card ι)
    (z : S) (hznz : z ≠ 0)
    (hp : ∃ y , (∏ i, (x i) ^ (e i)) * z ^ p = y ^ p) : ∀ i, p ∣ e i := by
  obtain ⟨y, hyz⟩ := hp
  obtain ⟨k, hk⟩:=
    (IsIntegrallyClosed.pow_dvd_pow_iff (Nat.Prime.ne_zero hp.out)).1 (Dvd.intro_left _ hyz)
  rw [hk, mul_pow, mul_comm (z ^ p) _] at hyz
  simp [hznz] at hyz
  exact exponent_vec_eq_zero_of_full_rank_matrix F φ x e ζ hr hdvd hu hrank ⟨k, hyz⟩



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
  let e' := Sum.elim e (fun (_ : Fin 1) => 1)
  let x := (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a))
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

lemma not_principal_of_full_rank_matrix' {S ι τ : Type*} {p n : ℕ} [hp : Fact $ Nat.Prime p]
  [Fintype ι] [Fintype τ] (F : τ → Type*)
  [CommRing S] [IsDomain S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
  (u : ι → S) (hu : ∀ i, IsUnit (u i)) (hugen : ∀ (w : Sˣ), (∃ (e : ι → ℕ) , (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
  (I : Ideal S) (a : S) (hua : ∀ i, IsUnit ((φ i) a)) (hdvdp : p ∣ n) (h : I ^ n = Ideal.span {a})
  (hrank : (MatrixLogProd p F φ (Sum.elim (fun i => u i) (fun (_ : Fin 1) => a)) ζ hr).rank = Fintype.card ι + 1) :
    ¬ ∃ b, I ^ (n / p) = Ideal.span {b} := by
  refine not_principal_of_full_rank_matrix (n := p) F u hu hugen φ ζ hr hdvd (I ^ (n / p)) a hua ?_ ?_ hrank
  · rfl
  · rw [← pow_mul, Nat.div_mul_cancel hdvdp]
    exact h

-- We assume integrally closed
lemma not_principal_of_full_rank_matrix'' {S ι τ κ γ : Type*} {p : ℕ} [hp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] [Fintype κ] [Fintype γ] (F : τ → Type*)
    [CommRing S] [IsDomain S] [IsIntegrallyClosed S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)]
    (u : ι → S) (hu : ∀ i, IsUnit (u i))
    (hugen : ∀ (w : Sˣ), (∃ (e : ι → ℕ) , (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
    (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (I : κ → Ideal S) (a : κ → S) (n : κ → ℕ) (r : κ → ℕ)
    (ψ : γ → κ) (hψ : ∀ i, (p ∣ n i) → ∃ j , ψ j = i )
    (hua : ∀ i j, IsUnit ((φ i) (a (ψ j))))
    (hnzero : ∀ j , j ∈ (Finset.image ψ Finset.univ)ᶜ → a j ≠ 0 )
    (h : ∀ i, (I i) ^ (n i) = Ideal.span {a i}) (b : S)
    (hrprod : ∏ i, (I i) ^ (r i) = Ideal.span {b}) (hdvdp : ∀ i , (n i) ∣ p * (r i))
    (hrank : (MatrixLogProd p F φ (Sum.elim (fun i => u i) (fun i => a (ψ i))) ζ hr).rank = Fintype.card ι + Fintype.card γ) :
    ∀ i , n i ∣ r i := by
  intro i
  by_cases hdvdc : p ∣ n i
  · have hdvdcc := hψ i hdvdc
    apply_fun (fun x => x ^ p) at hrprod
    let q := fun i => (hdvdp i).choose
    have hq : ∀ (i : κ), p * r i = n i * q i := fun i => (hdvdp i).choose_spec
    simp_rw [← Finset.prod_pow, ← pow_mul, Ideal.span_singleton_pow, mul_comm, hq, pow_mul, h,
      Ideal.span_singleton_pow, Ideal.prod_span_singleton, Ideal.span_singleton_eq_span_singleton] at hrprod
    obtain ⟨v, hv⟩ := hrprod
    rw [← Finset.prod_mul_prod_compl {j ∈ Finset.univ | ∃ k , ψ k = j}] at hv
    have haux : ∀ i , i ∈ ({j ∈ Finset.univ | ∃ k , ψ k = j} : Finset κ)ᶜ → p ∣ q i := by
      intro i hi
      simp at hi
      refine (Nat.Coprime.dvd_mul_left ?_ ).1 (Dvd.intro _ (hq i))
      refine (Nat.Prime.coprime_iff_not_dvd (hp.out)).2 ?_
      revert hi
      contrapose!
      exact hψ i
    let χ := fun i => if hi : i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ then (haux i hi).choose else 0
    have : ∀ i, i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ → q i = p * (χ i) := fun i hi => by
      unfold χ
      simp only [hi, ↓reduceDIte]
      exact (haux i hi).choose_spec
    have hauxprod : ∏ i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ, a i ^ q i = (∏ i ∈ (Finset.filter (fun j ↦ ∃ k , ψ k = j) Finset.univ)ᶜ, a i ^ (χ i)) ^ p := by
      simp_rw [← Finset.prod_pow, ← pow_mul, mul_comm]
      refine Finset.prod_congr rfl ?_
      intro x hx
      rw [this x hx]
    obtain ⟨e, t , het ⟩ := hugen v
    have hinj' : Function.Injective ψ := by
      unfold Function.Injective
      by_contra! hc
      obtain ⟨a,b, habeq, hneq⟩ := hc
      rw [Matrix.rank_eq_finrank_span_cols, Eq.comm] at hrank
      have := hrank ▸ (finrank_span_le_card _)
      simp at this
      have hunivcard : (Finset.univ (α := ι ⊕ γ)).card = Fintype.card ι + Fintype.card γ := by
        simp only [Finset.card_univ, Fintype.card_sum, Nat.add_left_cancel_iff]
      rw [← hunivcard] at this
      have heqcard := le_antisymm this (Finset.card_image_le)
      rw [Eq.comm, Finset.card_image_iff] at heqcard
      have := heqcard (x₁ := Sum.inr a) (by simp only [Finset.coe_univ, Set.mem_univ]) (x₂ := Sum.inr b) (by simp only [Finset.coe_univ,
        Set.mem_univ])
      rw [Sum.inr.injEq] at this
      refine hneq (this ?_ )
      ext i
      simp only [col_apply, MatrixLogProd, Sum.elim_inr, habeq]
    have hauxprod2 : (∏ i ∈ Finset.filter (fun j ↦ ∃ k, ψ k = j) Finset.univ, a i ^ q i) = ∏ i, a (ψ i) ^ q (ψ i) := by
      symm
      refine Finset.prod_nbij ψ ?_ ?_ ?_ ?_
      · intro x hx
        simp
      · exact fun x1 a x2 a ↦ fun a ↦ hinj' a
      · intro x hx
        simp at hx
        obtain ⟨j, hj⟩ := hx
        exact ⟨j, by simp only [Finset.coe_univ, Set.mem_univ, true_and] ; exact hj⟩
      · simp
    let e' := Sum.elim e (fun i => q (ψ i))
    let x := (Sum.elim (fun i => u i) (fun i => a (ψ i)))
    have auxp : ∏ i, x i ^ (e' i) = (∏ i : ι, u i ^ e i) * (∏ i : γ, a (ψ i) ^ q (ψ i)) := by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Finset.univ_unique, Fin.default_eq_zero,
        Fin.isValue, Sum.elim_inr, pow_one, Finset.prod_const, Finset.card_singleton, x, e']
    rw [hauxprod, hauxprod2, mul_assoc, mul_comm _ v.val, het, mul_assoc, ← mul_pow, ← mul_assoc,
      mul_comm _ (∏ i : ι, u i ^ e i), ← auxp] at hv
    have he : ∀ i , p ∣ e' i := by
      refine exponent_vec_eq_zero_of_full_rank_matrix' F φ x e' ζ hr hdvd ?_ ?_ _ ?_ ⟨b, hv⟩
      · intro i
        simp [x]
        constructor
        · intro j
          apply RingHom.isUnit_map
          exact hu j
        · intro j
          exact hua i j
      · simp only [Fintype.card_sum, x, q]
        exact hrank
      · simp only [Finset.univ_filter_exists, ne_eq, mul_eq_zero, Units.ne_zero, false_or, x, q]
        rw [← ne_eq, Finset.prod_ne_zero_iff]
        intro i hi
        exact pow_ne_zero _ (hnzero i hi)
    simp [e'] at he
    obtain ⟨m, hm⟩ := hdvdcc
    rcases he with ⟨h1, h2⟩
    obtain ⟨k, hk ⟩ := h2 m
    specialize hq (ψ m)
    rw [hk, ← mul_assoc, mul_comm _ p, mul_assoc] at hq
    simp only [mul_eq_mul_left_iff, Nat.Prime.ne_zero hp.out, or_false, q, e', x] at hq
    rw [← hm]
    exact ⟨k, hq⟩
  · rw [← Nat.Prime.coprime_iff_not_dvd (hp.out), Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm] at hdvdc
    specialize hdvdp i
    rw [← Nat.dvd_gcd_mul_iff_dvd_mul, hdvdc, one_mul] at hdvdp
    exact hdvdp


lemma nat_up_to_power_of_int_up_to_power {S ι : Type*} [CommRing S]
  [Fintype ι] {u : ι → S} (hu : ∀ i, IsUnit (u i)) {w : Sˣ} (hp : p ≠ 0)
  (e' : ι → ℤ) (t : Sˣ) (het : w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p) :
  ∃ (e : ι → ℕ), (∀ i, (e i : ZMod p) = e' i) ∧ (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p) := by
  use (fun i => ((e' i) % p).toNat)
  have : ∀ i, (u i) ^ ((e' i) % p).toNat = ↑((hu i).unit ^ ((e' i) % p)) := by
    intro i
    nth_rw 2 [← Int.toNat_of_nonneg (Int.emod_nonneg (e' i) (Int.ofNat_ne_zero.mpr hp))]
    rw [zpow_natCast]
    rfl
  constructor
  · intro i
    dsimp
    have := Int.toNat_of_nonneg (Int.emod_nonneg (e' i) (Int.ofNat_ne_zero.mpr hp))
    apply_fun (algebraMap ℤ (ZMod p)) at this
    simp only [algebraMap_int_eq, eq_intCast, ZMod.intCast_mod] at this
    rw [← this]
    exact Eq.symm (AddCommGroupWithOne.intCast_ofNat (e' i % ↑p).toNat)
  use (∏ (i : ι), ((hu i).unit) ^ ((e' i) / p)) * t
  simp_rw [this]
  simp only [Units.val_mul, Units.coe_prod, mul_pow, ← Finset.prod_pow]
  rw [← mul_assoc, ← Finset.prod_mul_distrib]
  have aux : ∀ i, (↑((hu i).unit ^ ((e' i) % p)) : S) * (↑((hu i).unit ^ ((e' i) / p)): S) ^ p =
    (↑((hu i).unit ^ (e' i)) : S) := by
    intro i
    nth_rw 3 [← Int.emod_add_ediv (e' i) p]
    rw [zpow_add]
    rw [Units.val_mul, Units.mul_right_inj, mul_comm, zpow_mul, zpow_natCast]
    rfl
  simp_rw [aux, het]
  simp only [Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]


lemma z_exponent_vec_eq_zero_of_full_rank_matrix {S ι τ : Type*} {p : ℕ} [hpp : Fact $ Nat.Prime p]
    [Fintype ι] [Fintype τ] (F : τ → Type*)
    [CommRing S] [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] (φ : Π i : τ, S →+* (F i))  (u : ι → S)
    (hu : ∀ i, IsUnit (u i)) (e : ι → ℤ)
    (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
    (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ))
    (hrank : (MatrixLogProd p F φ u ζ hr).rank = Fintype.card ι)
    (hp : ∃ y, ∏ i : ι, ↑(hu i).unit ^ (e i)= y ^ p) : ∀ i, ↑p ∣ e i := by
    obtain ⟨y, hy⟩ := hp
    have aux := nat_up_to_power_of_int_up_to_power hu (Nat.Prime.ne_zero hpp.out ) e (w := 1) (y⁻¹) ?_
    swap
    · rw [hy]
      simp only [inv_pow, mul_inv_cancel]
    obtain ⟨e', hmod, t, h2⟩ :=  aux
    symm at h2
    apply_fun (fun x => x * (↑t⁻¹) ^ p ) at h2
    rw [Units.val_one, one_mul, mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, mul_one] at h2
    have hdvde : ∀ (i : ι), p ∣ e' i := exponent_vec_eq_zero_of_full_rank_matrix F φ u e' ζ hr hdvd ?_ hrank ⟨↑t⁻¹, h2 ⟩
    intro k
    specialize hmod k
    specialize hdvde k
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at hdvde
    rw [hdvde, Eq.comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    exact hmod
    intro i j
    apply RingHom.isUnit_map
    exact hu j






lemma nat_up_to_p_power_iff_int_up_to_p_power {S ι : Type*} [CommRing S]
  [Fintype ι] (u : ι → S) (hu : ∀ i, IsUnit (u i)) (w : Sˣ) (hp : p ≠ 0) :
  (∃ (e : ι → ℕ), (∃ (t : Sˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)) ↔
  (∃ (e' : ι → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p)) := by
  constructor
  · rintro ⟨e, t, het ⟩
    use (fun i => e i) , t
    rw [← Units.eq_iff]
    simp only [het, zpow_natCast, Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val,
      IsUnit.unit_spec]
  · rintro ⟨e', t, het ⟩
    obtain ⟨e, hmod, tt, h2⟩ := nat_up_to_power_of_int_up_to_power hu hp e' t het
    use e, tt


lemma linearIndependent_int_iff_no_common_divisor {M ι R: Type*} [AddCommGroup M]
  [CommRing R] [IsDomain R] [WfDvdMonoid R] [Module R M] [NoZeroSMulDivisors R M]
  {p : R} (hp : Prime p) (v : ι → M) : ¬ LinearIndependent R v ↔
    ∃ (s : Finset ι) (g : ι → R), (∃ i ∈ s, ¬ p ∣ (g i)) ∧ ∑ i ∈ s, g i • v i = 0  := by
by_cases hnnempty : Nonempty ι
rw [linearIndependent_iff']
push_neg
constructor
swap
· rintro ⟨s , g , ⟨j , hpj1, hpj2⟩ ,hg⟩
  use s, g
  refine ⟨hg, ⟨j , ⟨hpj1, ?_ ⟩ ⟩ ⟩
  by_contra hz
  rw [hz] at hpj2
  simp only [dvd_zero, not_true_eq_false] at hpj2
· rintro ⟨s , g ,hg ,bhneq⟩
  by_cases hc : ∃ i ∈ s, ¬ p ∣ (g i)
  · use s , g
  · push_neg at hc
    let S := Finset.filter (fun x => g x ≠ 0) s
    haveI hS : S.Nonempty := by
      rw [Finset.filter_nonempty_iff]
      use bhneq.choose
      simp only [ne_eq, Finset.mem_univ, true_and]
      exact bhneq.choose_spec
    have hSaux : ∀ x, x ∈ S → x ∈ s := by
      intro x hx
      exact Finset.mem_of_mem_filter x hx
    · set m := S.inf' hS (fun i => multiplicity p (g i)) with hmm
      have hmp : m ≠ 0 := by
        suffices 1 ≤ m by exact Nat.ne_zero_of_lt this
        unfold m
        simp only [Finset.univ_nonempty, Finset.le_inf'_iff, Finset.mem_univ, forall_const]
        intro j
        by_cases  hm : FiniteMultiplicity p (g j)
        · intro hj
          refine FiniteMultiplicity.le_multiplicity_of_pow_dvd hm ?_
          rw [pow_one]
          exact hc j (hSaux _ hj)
        · intro hj
          rw [multiplicity_eq_one_of_not_finiteMultiplicity hm]
      have aux : ∀ i ∈ s , ∃ k, g i = p ^ m * k := by
        intro i hi
        by_cases hgi : g i ≠ 0
        have aux2 : m ≤ multiplicity p (g i) := by
          simp only [Finset.inf'_le_iff, m]
          use i
          exact ⟨Finset.mem_filter.mpr ⟨hi, hgi⟩  , by rfl⟩
        exact pow_dvd_of_le_multiplicity aux2
        push_neg at hgi
        use 0
        rw [hgi, mul_zero]
      let g' : ι → R := fun i => if hi : i ∈ s then (aux i hi).choose else 0
      have hgaux :  ∀ i ∈ s, g i = p ^ m  * g' i := by
        intro i hi
        simp only [hi, ↓reduceDIte, g', m]
        exact (aux i hi).choose_spec
      obtain ⟨a, ha1, ha2⟩ := Finset.exists_mem_eq_inf' hS (fun i => multiplicity p (g i))
      rw [← hmm] at ha2
      have hndvd : ¬ p ∣ g' a := by
        by_contra hdvd
        obtain ⟨t, ht ⟩ := hdvd
        specialize hgaux a  (hSaux _ ha1)
        rw [ht, ← mul_assoc] at hgaux
        nth_rw 2 [← pow_one (a := p)] at hgaux
        rw [← pow_add] at hgaux
        have haux2 := (FiniteMultiplicity.pow_dvd_iff_le_multiplicity ?_).1 (Dvd.intro t (id (Eq.symm hgaux)))
        rw [← ha2] at haux2
        simp only [add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, m] at haux2
        refine FiniteMultiplicity.of_prime_left (α := R) hp ?_
        rw [Finset.mem_filter] at ha1
        exact ha1.2
      have hg' := Finset.sum_congr (s₂ := s) (f := fun x => g x • v x) (g := fun x =>
        (p ^ m  * g' x) • v x) rfl (fun x hx => by simp only [hgaux x hx] )
      simp_rw [hg', MulAction.mul_smul, ← Finset.smul_sum] at hg
      simp only [smul_eq_zero, pow_eq_zero_iff', Prime.ne_zero hp, ne_eq, false_and, false_or,
        m] at hg
      use s , g'
      constructor
      · use a
        exact ⟨hSaux _ ha1, hndvd⟩
      · exact hg
simp only [not_nonempty_iff] at hnnempty
simp only [IsEmpty.exists_iff, false_and, exists_const, iff_false, Decidable.not_not]
exact linearIndependent_empty_type



 --(huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι)
-- ∃ (e' : ι → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p)
--(w : Sˣ)

lemma units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion {S ι τ : Type*} {p : ℕ}
  [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] (F : τ → Type*) [CommRing S] [IsDomain S]
  [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
  [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Sˣ))
  (hrank : (MatrixLogProd p F φ u ζ hr).rank = Fintype.card ι)  :
   LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit)) := by
  by_contra hi
  · rw [linearIndependent_int_iff_no_common_divisor (Nat.prime_iff_prime_int.1 hp.out)] at hi
    obtain ⟨ s , g , ⟨k, hk,  hdvdp⟩ , hg⟩ := hi
    simp_rw [← ofMul_zpow, ← ofMul_prod, ofMul_eq_zero] at hg
    have : ∏ i ∈ s, ((QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit) ^ (g i)) =
      QuotientGroup.mk (∏ i ∈ s, (hu i).unit ^ (g i)) := by
      exact Eq.symm (QuotientGroup.mk_prod (CommGroup.torsion Sˣ) s)
    rw [this, QuotientGroup.eq_one_iff] at hg
    have auxcard : (Nat.card (CommGroup.torsion Sˣ)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpndvdt
      exact hp.out
    let y := (powCoprime auxcard)⁻¹ ⟨_ , hg⟩
    have aux2 : (powCoprime auxcard) y = ∏ i ∈ s, (hu i).unit ^ (g i) := by
      simp only [Equiv.Perm.apply_inv_self, y]
    rw [powCoprime_apply] at aux2
    simp only [SubmonoidClass.coe_pow] at aux2
    have haux2 := nat_up_to_power_of_int_up_to_power hu (w := 1) (p := p) (Ne.symm (NeZero.ne' p)) (fun i => if i ∈ s then g i else 0) (y⁻¹) ?_
    obtain ⟨e, hmod, t, h2⟩ :=  haux2
    symm at h2
    apply_fun (fun x => x * (↑t⁻¹) ^ p ) at h2
    rw [Units.val_one, one_mul, mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, mul_one] at h2
    have hdvde : ∀ (i : ι), p ∣ e i := exponent_vec_eq_zero_of_full_rank_matrix F φ u e ζ hr hdvd ?_ hrank ⟨↑t⁻¹, h2 ⟩
    specialize hmod k
    specialize hdvde k
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at hdvde
    rw [hdvde, Eq.comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at hmod
    simp only [hk, ↓reduceIte, y] at hmod
    exact hdvdp hmod
    · intro i j
      apply RingHom.isUnit_map
      exact hu j
    · simp only [pow_ite, zpow_zero, Finset.prod_ite_mem, Finset.univ_inter]
      rw [← aux2]
      simp only [inv_pow, mul_inv_cancel, y]

-- some challenges are the switch between this as an additive subgroup vs multiplicative
lemma units_up_to_p_power_of_full_rank_matrix_of_p_not_dvd_torsion {S ι τ : Type*} {p : ℕ}
  [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] (F : τ → Type*) [CommRing S] [IsDomain S]
  [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
  [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Sˣ))
  (hrank : (MatrixLogProd p F φ u ζ hr).rank = Fintype.card ι)
  (huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι) (w : Sˣ) :
   ∃ (e' : ι → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p) := by
  have hlin := units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion F u hu φ ζ hr hdvd hpndvdt hrank
  let M : Submodule ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) :=
    Submodule.span ℤ (Set.range (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit)))
  let BM : Basis ι ℤ M := ⟨(LinearIndependent.linearCombinationEquiv hlin).symm⟩
  let N := ((Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))))
  have hdim : Module.finrank ℤ N = Fintype.card ι := by
    refine eq_of_le_of_le huc ?_
    refine le_of_eq_of_le ?_ (Submodule.finrank_le M)
    symm
    exact Module.finrank_eq_card_basis BM
  have B := Module.finBasisOfFinrankEq ℤ _ hdim
  have B' : Basis (Fin (Fintype.card ι)) ℤ M := Basis.reindex BM (Fintype.equivFin ι)
  have hinz : Nat.card (N ⧸ M) ≠ 0 := by
    rw [← indexPID_eq_index_int _ B B' , Int.natAbs_ne_zero,
    ← Associated.ne_zero_iff (Associated.comm.1 (prod_moduleSmithCoeffs_associated_index _ B B')), Finset.prod_ne_zero_iff]
    intro i hi
    exact moduleSmithCoeffs_ne_zero _ B B' i
  haveI : Finite (N ⧸ M) := (Nat.card_ne_zero.1 hinz).2
  have auxcard : (Nat.card (CommGroup.torsion Sˣ)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpndvdt
      exact hp.out
  have hpmaximal : ¬ p ∣ Nat.card (N ⧸ M) := by
    by_contra hpdvd
    obtain ⟨x  , hx ⟩ := exists_prime_addOrderOf_dvd_card' p hpdvd
    have xpow : p • x = 0  := by
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have xnezero : x ≠ 0 := by
      rw [addOrderOf_eq_iff] at hx
      rw [← one_nsmul x]
      exact (hx.2 1 (Nat.Prime.one_lt hp.out) (by decide))
      exact (Nat.Prime.pos hp.out)
    obtain ⟨y, hy ⟩ := Quotient.exists_rep x
    rw [← hy] at xpow xnezero
    simp only [ne_eq] at xnezero
    erw [Submodule.Quotient.mk_eq_zero] at xpow xnezero
    rw [Submodule.mem_span_range_iff_exists_fun] at xpow
    obtain ⟨g, hg⟩ := xpow
    dsimp at hg
    have hgc := hg
    conv at hg =>
      left  ; right ; intro i ; rw [← ofMul_zpow]
    rw [← ofMul_prod, ← ofMul_toMul y, ← ofMul_pow p _] at hg
    apply_fun Additive.ofMul.symm at hg
    erw [toMul_ofMul, toMul_ofMul] at hg
    obtain ⟨z, hz ⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion Sˣ) (Additive.toMul y)
    rw [← hz] at hg
    erw [← QuotientGroup.mk_prod, ← QuotientGroup.mk'_apply, Eq.comm, QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hg
    obtain ⟨t, htmem, ht ⟩ := hg
    have : t = ((((powCoprime auxcard)⁻¹ ⟨_ , htmem⟩)) ^ p : CommGroup.torsion Sˣ) := by
      rw [← powCoprime_apply auxcard]
      simp only [Equiv.Perm.apply_inv_self]
    rw [this] at ht
    dsimp at ht
    rw [← mul_pow, Eq.comm] at ht
    have hdvdgi : ∀ i, ↑p ∣ (g i):= z_exponent_vec_eq_zero_of_full_rank_matrix F φ u hu g ζ hr hdvd hrank ⟨_, ht⟩
    set J : ι → ℤ := fun i => (hdvdgi i).choose
    have htaux : ∀ i , g i = p * (J i) := fun i => (hdvdgi i).choose_spec
    simp_rw [htaux, MulAction.mul_smul, ← Finset.smul_sum, ← natCast_zsmul] at hgc
    rw [smul_right_inj (Ne.symm (NeZero.ne' (p : ℤ)))] at hgc
    apply xnezero
    rw [← hgc, Submodule.mem_span_range_iff_exists_fun]
    use J
  have auxcard' : (Nat.card (N ⧸ M)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpmaximal
      exact hp.out
  set α : N ⧸ M :=  (QuotientAddGroup.mk ((Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) w)) )) with hwdef
  have hauxg := nsmulCoprime_apply auxcard' ((nsmulCoprime auxcard')⁻¹ α)
  rw [Equiv.Perm.apply_inv_self] at hauxg
  --obtain ⟨α', hα ⟩ := QuotientAddGroup.mk'_surjective _ α
  obtain ⟨β', hβ ⟩ := QuotientAddGroup.mk'_surjective _ ((nsmulCoprime auxcard')⁻¹ α)
  nth_rw 1 [hwdef] at hauxg
  rw [ ← hβ, QuotientAddGroup.mk'_apply,  ← QuotientAddGroup.mk_nsmul] at hauxg
  rw [← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, Eq.comm, QuotientAddGroup.mk'_eq_mk'] at hauxg
  obtain ⟨m, hmmem, hmeq ⟩ := hauxg
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hmmem
  obtain ⟨e' ,he ⟩ := hmmem
  use e'
  apply_fun Additive.toMul at hmeq
  rw [← he] at hmeq
  simp only [toMul_add, toMul_nsmul, toMul_sum, toMul_zsmul, toMul_ofMul] at hmeq
  obtain ⟨β'', hβ'' ⟩ := QuotientGroup.mk'_surjective _ (Additive.toMul β')
  erw [← hβ'', ← QuotientGroup.mk_prod, ← QuotientGroup.mk_pow , QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hmeq
  obtain ⟨l, hlmem, hl⟩ := hmeq
  rw [mul_comm, ← mul_assoc] at hl
  have auxl : ((powCoprime auxcard)⁻¹ ⟨l ,hlmem⟩) ^ p  = l := by
    rw [← SubmonoidClass.coe_pow, ← powCoprime_apply auxcard, Equiv.Perm.apply_inv_self]
  rw [← auxl, ← mul_pow, mul_comm, Eq.comm] at hl
  exact ⟨_ , hl⟩



lemma units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion {S ι τ κ: Type*} {p : ℕ}
  [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] [Fintype κ] (F : τ → Type*) [CommRing S] [IsDomain S]
  [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
  [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
  (v : κ → S) (hv : ∀ i, IsUnit (v i))
  (hvt : ∀ w ∈ CommGroup.torsion Sˣ, (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Sˣ , w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (hrank : (MatrixLogProd p F φ (Sum.elim u v) ζ hr).rank = Fintype.card ι + Fintype.card κ) :
   LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit)) := by
  by_contra hi
  · rw [linearIndependent_int_iff_no_common_divisor (Nat.prime_iff_prime_int.1 hp.out)] at hi
    obtain ⟨ s , g , ⟨k, hk,  hdvdp⟩ , hg⟩ := hi
    simp_rw [← ofMul_zpow, ← ofMul_prod, ofMul_eq_zero] at hg
    have : ∏ i ∈ s, ((QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit) ^ (g i)) =
      QuotientGroup.mk (∏ i ∈ s, (hu i).unit ^ (g i)) := by
      exact Eq.symm (QuotientGroup.mk_prod (CommGroup.torsion Sˣ) s)
    rw [this, QuotientGroup.eq_one_iff] at hg
    obtain ⟨a, t, ht, ha⟩ := hvt _ hg
    have haux2 := nat_up_to_power_of_int_up_to_power (u := Sum.elim u v) (by simp only [Sum.forall, Sum.elim_inl, hu, implies_true, Sum.elim_inr, hv, and_self])
      (w := 1) (p := p) (Ne.symm (NeZero.ne' p)) (Sum.elim (fun i => if i ∈ s then g i else 0) (fun j => - a j) ) (t⁻¹ : Sˣ) ?_
    swap
    · simp only [Fintype.prod_sum_type, Sum.elim_inl, pow_ite, zpow_zero, Finset.prod_ite_mem,
      Finset.univ_inter, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, one_pow, mul_one]
      simp only [ha, mul_inv_cancel_comm, inv_pow, mul_inv_cancel]
    obtain ⟨e', hep, t, hpeq⟩ := haux2
    apply_fun (fun x => x * (↑t⁻¹) ^ p ) at hpeq
    rw [Units.val_one, one_mul, mul_assoc, ← mul_pow, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_pow, mul_one] at hpeq
    have hdvde : ∀ (i : _), p ∣ e' i := exponent_vec_eq_zero_of_full_rank_matrix F φ (Sum.elim u v) e' ζ hr hdvd ?_ (by simp only [hrank,
      Fintype.card_sum]) ⟨↑t⁻¹, hpeq.symm ⟩
    simp only [Sum.forall, Sum.elim_inl, Int.cast_ite, Int.cast_zero, Sum.elim_inr,
      Int.cast_neg] at hdvde hep
    rcases hdvde with ⟨hdvde1, hdvde2⟩
    rcases hep with ⟨hep1, hep2⟩
    specialize hdvde1 k
    specialize hep1 k
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at hdvde1
    simp only [hk, ↓reduceIte] at hep1
    rw [hdvde1, Eq.comm, ZMod.intCast_zmod_eq_zero_iff_dvd] at hep1
    exact hdvdp hep1
    · intro i j
      apply RingHom.isUnit_map
      cases j
      · simp only [Sum.elim_inl, hu]
      · simp only [Sum.elim_inr, hv]


lemma units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion {S ι τ κ: Type*} {p : ℕ}
  [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] [Fintype κ] (F : τ → Type*) [CommRing S] [IsDomain S]
  [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
  [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (v : κ → S) (hv : ∀ i, IsUnit (v i))
  (hvt : ∀ w ∈ CommGroup.torsion Sˣ, (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Sˣ , w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
  (hrank : (MatrixLogProd p F φ (Sum.elim u v) ζ hr).rank = Fintype.card ι + Fintype.card κ)
  (huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι) (w : Sˣ) :
    ∃ (e' : ι ⊕ κ → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι ⊕ κ), (Sum.elim (fun i => (hu i).unit) (fun i => (hv i).unit) i) ^ (e' i)) * t ^ p) := by
  have hlin := units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion F u hu v hv hvt φ ζ hr hdvd hrank
  let M : Submodule ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) :=
    Submodule.span ℤ (Set.range (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) (hu i).unit)))
  let BM : Basis ι ℤ M := ⟨(LinearIndependent.linearCombinationEquiv hlin).symm⟩
  let N := ((Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))))
  have hdim : Module.finrank ℤ N = Fintype.card ι := by
    refine eq_of_le_of_le huc ?_
    refine le_of_eq_of_le ?_ (Submodule.finrank_le M)
    symm
    exact Module.finrank_eq_card_basis BM
  have B := Module.finBasisOfFinrankEq ℤ _ hdim
  have B' : Basis (Fin (Fintype.card ι)) ℤ M := Basis.reindex BM (Fintype.equivFin ι)
  have hinz : Nat.card (N ⧸ M) ≠ 0 := by
    rw [← indexPID_eq_index_int _ B B' , Int.natAbs_ne_zero,
    ← Associated.ne_zero_iff (Associated.comm.1 (prod_moduleSmithCoeffs_associated_index _ B B')), Finset.prod_ne_zero_iff]
    intro i hi
    exact moduleSmithCoeffs_ne_zero _ B B' i
  haveI : Finite (N ⧸ M) := (Nat.card_ne_zero.1 hinz).2
  have hpmaximal : ¬ p ∣ Nat.card (N ⧸ M) := by
    by_contra hpdvd
    obtain ⟨x  , hx ⟩ := exists_prime_addOrderOf_dvd_card' p hpdvd
    have xpow : p • x = 0  := by
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have xnezero : x ≠ 0 := by
      rw [addOrderOf_eq_iff] at hx
      rw [← one_nsmul x]
      exact (hx.2 1 (Nat.Prime.one_lt hp.out) (by decide))
      exact (Nat.Prime.pos hp.out)
    obtain ⟨y, hy ⟩ := Quotient.exists_rep x
    rw [← hy] at xpow xnezero
    simp only [ne_eq] at xnezero
    erw [Submodule.Quotient.mk_eq_zero] at xpow xnezero
    rw [Submodule.mem_span_range_iff_exists_fun] at xpow
    obtain ⟨g, hg⟩ := xpow
    dsimp at hg
    have hgc := hg
    conv at hg =>
      left  ; right ; intro i ; rw [← ofMul_zpow]
    rw [← ofMul_prod, ← ofMul_toMul y, ← ofMul_pow p _] at hg
    apply_fun Additive.ofMul.symm at hg
    erw [toMul_ofMul, toMul_ofMul] at hg
    obtain ⟨z, hz ⟩ := QuotientGroup.mk'_surjective (CommGroup.torsion Sˣ) (Additive.toMul y)
    rw [← hz] at hg
    erw [← QuotientGroup.mk_prod, ← QuotientGroup.mk'_apply, Eq.comm, QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hg
    obtain ⟨t, htmem, ht ⟩ := hg
    obtain ⟨a, k, hk, ha⟩ := hvt _ htmem
    dsimp at ht
    have hdvdgi := z_exponent_vec_eq_zero_of_full_rank_matrix F φ (Sum.elim u v)
      (by simp only [Sum.forall, Sum.elim_inl, hu, implies_true, Sum.elim_inr, hv, and_self] ) (Sum.elim g (fun j => - a j) ) ζ hr hdvd
      (by simp only [hrank, Fintype.card_sum]) ?_
    swap
    use z * k
    · simp only [Fintype.prod_sum_type, Sum.elim_inl, ← ht, ha, Sum.elim_inr, zpow_neg,
      Finset.prod_inv_distrib, mul_inv_cancel_right]
      simp [mul_pow, mul_comm, mul_assoc]
    simp only [Sum.forall, Sum.elim_inl, Sum.elim_inr, dvd_neg] at hdvdgi
    set J : ι → ℤ := fun i => (hdvdgi.1 i).choose
    have htaux : ∀ i , g i = p * (J i) := fun i => (hdvdgi.1 i).choose_spec
    simp_rw [htaux, MulAction.mul_smul, ← Finset.smul_sum, ← natCast_zsmul] at hgc
    rw [smul_right_inj (Ne.symm (NeZero.ne' (p : ℤ)))] at hgc
    apply xnezero
    rw [← hgc, Submodule.mem_span_range_iff_exists_fun]
    use J
  have auxcard' : (Nat.card (N ⧸ M)).Coprime p := by
      rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd]
      exact hpmaximal
      exact hp.out
  set α : N ⧸ M :=  (QuotientAddGroup.mk ((Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Sˣ)) w)) )) with hwdef
  have hauxg := nsmulCoprime_apply auxcard' ((nsmulCoprime auxcard')⁻¹ α)
  rw [Equiv.Perm.apply_inv_self] at hauxg
  obtain ⟨β', hβ ⟩ := QuotientAddGroup.mk'_surjective _ ((nsmulCoprime auxcard')⁻¹ α)
  nth_rw 1 [hwdef] at hauxg
  rw [ ← hβ, QuotientAddGroup.mk'_apply,  ← QuotientAddGroup.mk_nsmul] at hauxg
  rw [← QuotientAddGroup.mk'_apply, ← QuotientAddGroup.mk'_apply, Eq.comm, QuotientAddGroup.mk'_eq_mk'] at hauxg
  obtain ⟨m, hmmem, hmeq ⟩ := hauxg
  rw [Submodule.mem_toAddSubgroup, Submodule.mem_span_range_iff_exists_fun] at hmmem
  obtain ⟨e' ,he ⟩ := hmmem
  apply_fun Additive.toMul at hmeq
  rw [← he] at hmeq
  simp only [toMul_add, toMul_nsmul, toMul_sum, toMul_zsmul, toMul_ofMul] at hmeq
  obtain ⟨β'', hβ'' ⟩ := QuotientGroup.mk'_surjective _ (Additive.toMul β')
  erw [← hβ'', ← QuotientGroup.mk_prod, ← QuotientGroup.mk_pow , QuotientGroup.mk'_eq_mk' (CommGroup.torsion Sˣ)] at hmeq
  obtain ⟨l, hlmem, hl⟩ := hmeq
  rw [mul_comm, ← mul_assoc] at hl
  obtain ⟨a', k, hk, ha'⟩ := hvt _ hlmem
  use Sum.elim e' a'
  use k * β''
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [mul_pow, mul_assoc _ _ (k ^ p * β'' ^ p), ← mul_assoc _ (k ^ p) ,
    ← ha', ← mul_assoc _ l, ← hl, mul_comm, mul_assoc]


lemma units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion' {S ι τ κ: Type*} {p : ℕ}
  [hp : Fact $ Nat.Prime p] [Fintype ι] [Fintype τ] [Fintype κ] (F : τ → Type*) [CommRing S] [IsDomain S]
  [∀ i, CommRing (F i)] [∀ i, Fintype (F i)] [Module.Finite ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))]
  [Module.Free ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ)))] (u : ι → S) (hu : ∀ i, IsUnit (u i))
  (φ : Π i : τ, S →+* (F i)) (ζ : Π i, F i) (hr : ∀ i , IsPrimitiveRoot (ζ i) (Fintype.card (F i)ˣ))
  (hdvd : ∀ i, p ∣ (Fintype.card (F i)ˣ)) (v : κ → S) (hv : ∀ i, IsUnit (v i))
  (hvt : CommGroup.torsion Sˣ = Subgroup.closure (Set.range (fun j => (hv j).unit )) )
  (hrank : (MatrixLogProd p F φ (Sum.elim u v) ζ hr).rank = Fintype.card ι + Fintype.card κ)
  (huc : Module.finrank ℤ (Additive (Sˣ ⧸ (CommGroup.torsion Sˣ))) ≤ Fintype.card ι) (w : Sˣ) :
    ∃ (e' : ι ⊕ κ → ℤ), (∃ (t : Sˣ) , w = (∏ (i : ι ⊕ κ), (Sum.elim (fun i => (hu i).unit) (fun i => (hv i).unit) i) ^ (e' i)) * t ^ p) := by
 refine units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion F u hu φ ζ hr hdvd v hv ?_ hrank huc w
 intro k hkmem
 rw [hvt, Subgroup.mem_closure_range_iff_of_fintype] at hkmem
 obtain ⟨a, ha⟩ := hkmem
 use a , 1
 simp [ha]
 exact Subgroup.one_mem (CommGroup.torsion Sˣ)



/- Even if we use this, we get stack overflow for big-ish exponents. We need to reduce at every step -/
@[reducible]
def expBySquaring {G : Type*} [Monoid G] (x : G) (n : ℕ) : G :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => if n % 2 = 0 then ((expBySquaring x (n / 2)) ^ 2 * x) else (expBySquaring x ((n + 1) / 2)) ^ 2

@[reducible]
def expBySquaringZMod (p : ℕ) (x : ZMod p) (n : ℕ) : ZMod p :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => if n % 2 = 0 then ((((expBySquaringZMod p x (n / 2)) ^ 2)) * x).val % p else ((expBySquaringZMod p x ((n + 1) / 2)) ^ 2).val % p


@[reducible]
def expBySquaringZModNat (p x n : ℕ) : ℕ :=
  match n with
  | Nat.zero => 1
  | Nat.succ n => if n % 2 = 0 then ((((expBySquaringZMod p x (n / 2)) ^ 2)) * x).val % p else ((expBySquaringZMod p x ((n + 1) / 2)) ^ 2).val % p

@[reducible]
def squareAndMultiply_aux (m b e res : ℕ) : ℕ :=
  match e with
    | 0 => res
    | Nat.succ e =>
      let res' := if (e + 1) % 2 = 1 then (res * b) % m else res
      let b' := (b * b) % m
      let e' := (e + 1) / 2
      squareAndMultiply_aux m b' e' res'

@[reducible]
def squareAndMultiply_aux' (m e : ℕ) (b res : ZMod m) : ZMod m :=
  match e with
    | 0 => res
    | Nat.succ e =>
      let res' := if (Nat.succ e) % 2 = 1 then ((res * b).val % m : ZMod m) else res
      let b' := ((b * b).val % m : ZMod m)
      let e' := (Nat.succ e) / 2
      squareAndMultiply_aux' m e' b' res'


@[reducible]
def squareAndMultiply'' (b e m : ℕ) : ℕ :=
  squareAndMultiply_aux m (b % m) e 1

@[reducible]
def squareAndMultiply (b e m : ℕ) : ZMod m :=
  squareAndMultiply_aux' m e (b % m) 1

#eval! squareAndMultiply'' 3 11002324556787 30
--set_option trace.profiler true

#eval expBySquaringZMod 30 (3 : ZMod 30)  110023
#eval (3 : ZMod 30) ^ 111234123


--Already this exponent causes MaxRecDepth
example : expBySquaringZMod 30 3 1100 = 21 := by
 native_decide

-- Using squareAndMultiply''
-- using tail recursion  doesn't allow us to use decide, even if def is reducible.
-- But, seems to be fast if we unfold and simp. Even big exponents!

#count_heartbeats in
example : squareAndMultiply'' 3 11002324556787 30 = 27 := by
  repeat (unfold squareAndMultiply_aux ; dsimp)


--This seems to be pretty slow.
--example : expBySquaringZMod 30 3 1100 = 21 := by
--  repeat (unfold expBySquaringZMod ; dsimp)
--  decide


#count_heartbeats in
example : squareAndMultiply'' 3 110023 30 = 27 := by
  repeat (unfold squareAndMultiply_aux ; dsimp)

-- Using Nat seems to perform better than using ZMod


structure IsOrderOf {G : Type*} [Monoid G] (x : G) (n : ℕ) where
  m : ℕ
  P : Fin m → ℕ
  e : Fin m → ℕ
  hP : ∀ i, Nat.Prime (P i)
  hm : ∏ i, (P i) ^ (e i) = n
  hid : x ^ n = 1
  hnid : ∀ i , x ^ (n / (P i)) ≠ 1

lemma orderOf_of_IsOrderOf {G : Type*} [Monoid G] {x : G} {n : ℕ} (h : IsOrderOf x n) :
  orderOf x = n := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ h.hid ?_
  · rw [← h.hm]
    simp only [CanonicallyOrderedAdd.prod_pos, Finset.mem_univ, forall_const]
    intro i
    apply Nat.pow_pos
    exact Nat.Prime.pos (h.hP i)
  · intro p hp hpdvd
    rw [← h.hm, Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp)] at hpdvd
    choose a hau hadvd using hpdvd
    rw [Nat.prime_eq_prime_of_dvd_pow hp (h.hP a) hadvd]
    exact h.hnid a

lemma is_primitive_root_finite_field {F : Type*} [Field F] [Fintype F] {n : ℕ}
  (hcard : n = Fintype.card F - 1) (ζ : F) (h : IsOrderOf ζ n) : IsPrimitiveRoot ζ (Fintype.card Fˣ) := by
  convert IsPrimitiveRoot.orderOf ζ
  rw [orderOf_of_IsOrderOf h, hcard]
  exact Fintype.card_units F

------------------

open Finset NumberField InfinitePlace


noncomputable def equivRealEmbeddingsRealRoots (K : Type*) [Field K] [NumberField K] {f : ℚ[X]} (hf : f ≠ 0)
   (hr : IsAdjoinRoot K f) :
   { φ : K →+* ℂ // ComplexEmbedding.IsReal φ } ≃ { x // x ∈ (map (algebraMap ℚ ℝ) f).roots} := by
  let i : { φ // ComplexEmbedding.IsReal φ } → ℝ :=
    fun ⟨φ, hφ⟩ => (ComplexEmbedding.IsReal.embedding hφ) hr.root
  have hmem : ∀ φ, ∀ hφ : ComplexEmbedding.IsReal φ,  i ⟨φ, hφ⟩  ∈ (map (algebraMap ℚ ℝ) f).roots := by
    intro a ha
    simp [i, hf]
    letI aux : Algebra K ℝ := ha.embedding.toAlgebra
    rw [← RingHom.algebraMap_toAlgebra ((ComplexEmbedding.IsReal.embedding ha)), Polynomial.aeval_algebraMap_apply,
    IsAdjoinRoot.aeval_root hr, map_zero]
  refine Equiv.ofBijective (fun ⟨φ, hφ⟩  => ⟨i ⟨φ, hφ⟩, hmem φ hφ⟩ ) ?_
  constructor
  · rintro φ τ heq
    rw [← Subtype.val_inj] at heq ⊢
    dsimp at heq
    have aux1 := IsAdjoinRoot.eq_lift (x := i φ) (i := algebraMap ℚ ℝ) ?_ hr (ComplexEmbedding.IsReal.embedding φ.2) (by simp) rfl
    have aux2 := IsAdjoinRoot.eq_lift (x := i τ) (i := algebraMap ℚ ℝ) ?_ hr (ComplexEmbedding.IsReal.embedding τ.2) (by simp) rfl
    simp_rw [heq, ← aux2] at aux1
    ext x
    rw [← NumberField.ComplexEmbedding.IsReal.coe_embedding_apply φ.2 x,
      ← NumberField.ComplexEmbedding.IsReal.coe_embedding_apply τ.2 x, aux1]
    · letI aux : Algebra K ℝ := (τ.2).embedding.toAlgebra
      have : algebraMap K ℝ = (τ.2).embedding := rfl
      simp[i]
      rw [IsScalarTower.algebraMap_eq ℚ K ℝ, ← Polynomial.eval₂_map, this,
        Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def, IsAdjoinRoot.aeval_root, map_zero]
    · letI aux : Algebra K ℝ := (φ.2).embedding.toAlgebra
      have : algebraMap K ℝ = (φ.2).embedding := rfl
      simp[i]
      rw [IsScalarTower.algebraMap_eq ℚ K ℝ, ← Polynomial.eval₂_map, this,
        Polynomial.eval₂_hom, Polynomial.eval_map, ← Polynomial.aeval_def, IsAdjoinRoot.aeval_root, map_zero]
  · rintro ⟨x, hx⟩
    simp at hx
    let φ := (algebraMap ℝ ℂ).comp (IsAdjoinRoot.lift (algebraMap ℚ ℝ) x hr (by  rw [← Polynomial.aeval_def] ; exact hx.2))
    have hφ: ComplexEmbedding.IsReal φ := by
      rw [NumberField.ComplexEmbedding.isReal_iff]
      ext x
      rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
      simp [φ]
    use ⟨φ, hφ⟩
    simp[i]
    rw [← algebraMap.coe_inj (A := ℂ)]
    convert (NumberField.ComplexEmbedding.IsReal.coe_embedding_apply hφ hr.root)
    simp [φ]


theorem nrRealPlaces_eq_nr_real_roots (K : Type*) [Field K] [NumberField K] {f : ℚ[X]} (hf : f ≠ 0)
   (hr : IsAdjoinRoot K f) : nrRealPlaces K = #(Multiset.toFinset (map (algebraMap ℚ ℝ) f).roots) := by
  rw [← NumberField.InfinitePlace.card_real_embeddings]
  symm ; apply Finset.card_eq_of_equiv_fintype
  simp_rw [Multiset.mem_toFinset]
  exact (equivRealEmbeddingsRealRoots K hf hr).symm


lemma card_infinite_place_eq (K : Type*) [Field K] [NumberField K] :
  Fintype.card (InfinitePlace K) = (nrRealPlaces K + Module.finrank ℚ K) / 2 := by
  rw [← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank, ← add_assoc, ← two_mul,
    ← mul_add]
  simp[NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]

lemma card_infinite_place_adjoin_root (K : Type*) [Field K] [NumberField K] (f : ℚ[X]) (hf : f ≠ 0)
    (hr : IsAdjoinRoot K f) :
  Fintype.card (InfinitePlace K) =
    (#(Multiset.toFinset (map (algebraMap ℚ ℝ) f).roots) + f.natDegree) / 2 := by
  rw [card_infinite_place_eq, nrRealPlaces_eq_nr_real_roots K hf hr]
  congr
  rw [LinearEquiv.finrank_eq ((IsAdjoinRoot.aequiv hr (AdjoinRoot.isAdjoinRoot f)).toLinearEquiv),
    Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux hf)]
  simp


/- If torsion has cardinality `t`, then its generator is a primitive root of order `t` and thus
a root of `Φₜ(X)`, therefore the order of this polynomial `φ(t)` divides the degree of `K`.
If `p^m` divides `t`, then `p^(m-1) * (p - 1)` divides `n`.
However, the converse is not true. And so this cannot be used in all situation to prove that a prime
does not divide torsion.  -/


/-- If an element `x` of prime order `p` is mapped through a ring homomorphism, and the characteristic of the
codomain does not divide `p`, then the image of `x` also has order `p`.

TO DO: Generalize this to power of `p`. This holds, becaus `X^p - 1` is separable in `R`, so
if `x` has order `p^m` it is a root of `Φₚₘ(X)`, thus a `φ(x)` a root of `φ(Φₚₘ(X))`. However, it cannot be
a root of `φ(Φₚₙ(X))` with `n < m` because of separability of `X^p - 1`. -/
lemma orderOf_prime_map  {S R : Type*} {q p : ℕ} [CommRing S] [IsDomain S] [CommRing R] [CharP R q]
  [hp : Fact $ Nat.Prime p] (hneq : ¬ q ∣ p)
  (φ : S →+* R) {x : S} (ho : orderOf x = p) : orderOf (φ x) = p := by
  rw [orderOf_eq_prime_iff] at ho ⊢
  rcases ho with ⟨ho1, ho2⟩
  rw [ne_eq, ← sub_eq_zero] at ho2
  have hec := Polynomial.cyclotomic_prime_mul_X_sub_one S p
  apply_fun (fun P => Polynomial.eval x P) at hec
  simp[ho1, ho2] at hec
  constructor
  · rw [← map_pow, ho1]
    simp
  · intro h
    apply_fun φ at hec
    rw [← Polynomial.cyclotomic.eval_apply, h,
      eval_one_cyclotomic_prime, map_zero, CharP.cast_eq_zero_iff R q p] at hec
    exact hneq hec

lemma orderOf_map_CharP  {S R : Type*} {q n : ℕ} [CommRing S] [IsDomain S]
  [CommRing R] [IsDomain R] [CharP R q] [NeZero n] (hneq : ¬ q ∣ n)
  (φ : S →+* R) {x : S} (ho : orderOf x = n) : orderOf (φ x) = n  := by
  have aux := IsPrimitiveRoot.isRoot_cyclotomic
    (Nat.pos_of_neZero _) (ho ▸ IsPrimitiveRoot.orderOf x)
  symm
  apply IsPrimitiveRoot.eq_orderOf
  haveI : NeZero (↑n : R) := by
    refine NeZero.of_not_dvd (p := q) R hneq
  rw [← Polynomial.isRoot_cyclotomic_iff]
  simp at aux ⊢
  rw [Polynomial.cyclotomic.eval_apply, aux, map_zero]

/--  If an element `x` of prime order `p ^ m` is mapped through a ring homomorphism,
  and the characteristic of the codomain does not divide `p`,
  then the image of `x` also has order `p ^ m`. Note that we assume both domain and
  codomain are integral domains. -/
lemma orderOf_prime_pow_map  {S R : Type*} {q p m : ℕ} [CommRing S] [IsDomain S]
  [CommRing R] [IsDomain R] [CharP R q] [hp : Fact $ Nat.Prime p] (hneq : ¬ q ∣ p)
  (φ : S →+* R) {x : S} (ho : orderOf x = p ^ m) : orderOf (φ x) = p ^ m  := by
  refine orderOf_map_CharP (q := q) ?_ φ ho
  rcases CharP.char_is_prime_or_zero R q with h1 | h2
  · intro h
    exact hneq (Nat.Prime.dvd_of_dvd_pow h1 h)
  · rw [h2]
    intro h
    simp only [zero_dvd_iff, pow_eq_zero_iff', Nat.Prime.ne_zero hp.out, ne_eq, false_and] at h



/-- The existance of such a q certificate can be proven with Chabotarev. `p` does not
  divide torsion iff the `p`-cyclotomic polynomial does not have a root in `K`,
  this is iff `Φₚ(X)` is irreducible in `K`. If so, then there is a `p-1` cycle in the Galois group
  and so there are primes `Q` of `K` of positive density s.t. `Φₚ(X) mod Q` is irreducible.
  Wlog we can assume `Q` of degree 1, and so `Φₚ(X) mod q` is irreducible for some prime number `q`,
  and this is iff `p` does not divide `q-1`.
  Remark : If the torsion group is cyclic, this can be generalized to powers of `p`  -/
lemma prime_not_dvd_torsion_of_not_dvd {S : Type*} [CommRing S] [IsDomain S] {p q : ℕ} [hp : Fact $ Nat.Prime p] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](I : Ideal S) (hcard : Nat.card (S ⧸ I) = q)
    (hpndvd : ¬ p ∣ (q - 1)) (hneq : p ≠ q) :
     ¬ p ∣ Nat.card (CommGroup.torsion Sˣ) := by
  haveI : Fact $ Nat.Prime q := {out := hq}
  rw [Nat.card_eq_fintype_card]
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hdvd
  rw [← orderOf_submonoid, ← orderOf_units] at hx
  let φ := (modIdealToZMod hq I hcard).comp (Ideal.Quotient.mk I)
  have aux : orderOf (φ ((x : Sˣ) : S)) = p := by
    refine orderOf_prime_map (q := q) ?_ φ hx
    rw [Nat.prime_dvd_prime_iff_eq hq hp.out]
    exact hneq.symm
  let y := IsOfFinOrder.unit (x := φ ((x : Sˣ) : S))
    (by by_contra hc ; rw [← orderOf_eq_zero_iff, aux] at hc ; exact Nat.Prime.ne_zero hp.out hc)
  have aux2 : orderOf y = p := by
    rw [← orderOf_units]
    simp[y, aux]
  apply hpndvd
  convert aux2 ▸ orderOf_dvd_card
  rw [(Nat.prime_iff_card_units q).1 hq]

/- If we want to, this can be further generalized to any prime ideal above `q`,
  and assuming `n` does not divide `q^m - 1`, where `q^m` is the norm of this ideal.
  However, we know that is suffices to consider primes of degree 1. -/
lemma not_dvd_torsion_of_not_dvd {S : Type*} [CommRing S] [IsDomain S]
    {n q : ℕ} [hn : NeZero n] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (I : Ideal S) (hcard : Nat.card (S ⧸ I) = q)
    (hpndvd : ¬ n ∣ q - 1) (hneq : ¬ q ∣ n) :
     ¬ n ∣ Nat.card (CommGroup.torsion Sˣ) := by
  haveI : Fact $ Nat.Prime q := {out := hq}
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hC
  intro hdvd
  rw [← hg] at hdvd
  set x := g ^ (orderOf g / n) with hxd
  have hx := hxd ▸ orderOf_pow_orderOf_div (Nat.ne_zero_of_lt (orderOf_pos g)) hdvd
  rw [← orderOf_submonoid, ← orderOf_units] at hx
  let φ := (modIdealToZMod hq I hcard).comp (Ideal.Quotient.mk I)
  have aux : orderOf (φ ((x : Sˣ) : S)) = n := by
    refine orderOf_map_CharP (q := q) hneq φ hx
  let y := IsOfFinOrder.unit (x := φ ((x : Sˣ) : S))
    (by by_contra hc ; rw [← orderOf_eq_zero_iff, aux] at hc ; exact (NeZero.ne n) hc )
  have aux2 : orderOf y = n := by
    rw [← orderOf_units]
    simp[y, aux]
  apply hpndvd
  convert aux2 ▸ orderOf_dvd_card
  rw [(Nat.prime_iff_card_units q).1 hq]

lemma prime_pow_not_dvd_torsion_of_not_dvd {S : Type*} [CommRing S] [IsDomain S]
    {p q : ℕ} [hp : Fact $ Nat.Prime p] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (I : Ideal S) (hcard : Nat.card (S ⧸ I) = q)
    (hpndvd : ¬ p ^ m ∣ q - 1) (hneq : p ≠ q) :
     ¬ p ^ m ∣ Nat.card (CommGroup.torsion Sˣ) := by
  refine not_dvd_torsion_of_not_dvd hq hC I hcard hpndvd ?_
  intro h
  exact hneq.symm ((Nat.prime_dvd_prime_iff_eq hq hp.out).1 (Nat.Prime.dvd_of_dvd_pow hq h))

lemma dvd_of_dvd_torsion {S : Type*} [CommRing S] [IsDomain S]
    {n q : ℕ} [hn : NeZero n] (hq : Nat.Prime q)
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (I : Ideal S) (hcard : Nat.card (S ⧸ I) = q) (hneq : ¬ q ∣ n)
    (hndd : n ∣ Nat.card (CommGroup.torsion Sˣ)) : n ∣ q - 1 := by
  revert hndd
  contrapose
  intro hpndvd
  exact not_dvd_torsion_of_not_dvd hq hC I hcard hpndvd hneq



/- You don't need to ask for `n` to be coprime with every `qᵢ`. You
  can refine this by keeping track of which prime
  powers you incorporate/discard according to `prime_pow_not_dvd_torsion_of_not_dvd`.

  In general, I want `less` primes to show up in the gcd. So is something gained if i consider
  primes of degree greater than 1? Every prime that appears as dividing `q-1` will also show up in any other
  prime ideal norm above `q`.

  In the case of number fields, if there is a torsion element of order `m`, then
  its minimal poly of order `φ(m)` divides the degree `d` of the number field. In particular,
  if `p` divides `m`, then `p-1` must divide `d`. Hence, prime divisors of the size of the
  torsion group is a subset of the primes `≤ d + 1` such that `p-1 ∣ d`. -/

#eval Multiset.filter (fun i => i ≠ 0) (Multiset.map
  (fun p => if Nat.Prime p ∧ p - 1 ∣ 12 then p else 0) (Multiset.range 13))

/--
We can certify that the size of the torsion group is `n` if:
* We provide a set of primes containing all the possible prime divisors of the
  torsion order.
* We provide a set of natural numbers `P` such that `lcm P = n` and for every `p ∈ P`
  there exists an `x` of order `p`.
* We provide a collection of prime ideals `I₁, ..., Iₘ` of degree 1 of norm
  `q₁, ..., qₘ` respectively, such that the `gcd` of the set
  `{q₁-1, ..., qₘ-1}` is `n`. -/

theorem eq_card_torsion_of_pow_of_gcd {S : Type*} [CommRing S] [IsDomain S]
    {n : ℕ} (M P : Finset ℕ) [Fintype ι] (q : ι → ℕ) (hq : ∀ i, Nat.Prime (q i))
    [Fintype (CommGroup.torsion Sˣ)](hC : IsCyclic (CommGroup.torsion Sˣ))
    (hmemd : ∀ p , Nat.Prime p → p ∣ Nat.card (CommGroup.torsion Sˣ) → p ∈ M)
    (I : ι → Ideal S) (hcard : ∀ i, Nat.card (S ⧸ (I i)) = q i)
    (hneq : ∀ i, ¬ (q i) ∈ M) (hPnz : ∀ p ∈ P, p ≠ 0)
    (hpow : ∀ p ∈ P, ∃ (x : S), orderOf x = p) (hgcd1 : Finset.lcm P id = n)
    (hgcd2 : (Finset.gcd (Finset.univ) (fun i : ι => (q i) - 1)) = n) :
    Nat.card (CommGroup.torsion Sˣ) = n := by
  apply Nat.dvd_antisymm
  · rw [← hgcd2, Finset.dvd_gcd_iff]
    simp only [mem_univ, Nat.card_eq_fintype_card, forall_const]
    intro i
    refine dvd_of_dvd_torsion (hq i) hC (I i) (hcard i) ?_ ?_
    · rw [← Nat.card_eq_fintype_card]
      intro h
      apply hneq i
      exact hmemd (q i) (hq i) h
    · rw [Nat.card_eq_fintype_card]
  · rw [← hgcd1, Finset.lcm_dvd_iff]
    intro b hbP
    obtain ⟨x, hx⟩ := hpow b hbP
    let x' := Units.ofPowEqOne x _ ((orderOf_eq_iff (Nat.pos_of_ne_zero (hPnz b hbP))).1 hx).1 ((hPnz b hbP))
    have hmem : x' ∈ CommGroup.torsion Sˣ := by
      rw [CommGroup.mem_torsion, ← orderOf_pos_iff, ← orderOf_units]
      simp [x', hx, Nat.pos_of_ne_zero (hPnz b hbP)]
    have hord2 : orderOf (⟨x', hmem⟩ : CommGroup.torsion Sˣ) = b  := by
      simp only [Subgroup.orderOf_mk, ← orderOf_units, Units.val_ofPowEqOne, hx, x']
    rw [← hord2]
    exact orderOf_dvd_natCard _

open NumberField Units

theorem prime_sub_dvd_finrank_of_prime_dvd_card_torsion {K : Type*} [Field K]
  [NumberField K] {p : ℕ} [hp : Fact $ Nat.Prime p]
  (hpdvd : p ∣ torsionOrder K) : p - 1 ∣ Module.finrank ℚ K := by
  simp [torsionOrder] at hpdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card p hpdvd
  have aux : IsPrimitiveRoot ((x : (RingOfIntegers K)ˣ) : K) p := by
    rw [← orderOf_submonoid, ← orderOf_units, ← orderOf_submonoid] at hx
    rw [← hx]
    exact IsPrimitiveRoot.orderOf _
  have := Polynomial.cyclotomic_eq_minpoly_rat aux (Nat.pos_of_neZero p)
  convert minpoly.degree_dvd (x := ((x : (RingOfIntegers K)ˣ) : K)) ?_
  · rw [← this, Polynomial.natDegree_cyclotomic, Nat.totient_prime hp.out]
  · rw [← minpoly.ne_zero_iff, ← this]
    exact cyclotomic_ne_zero p ℚ
