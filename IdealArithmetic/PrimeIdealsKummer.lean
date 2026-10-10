import Mathlib.NumberTheory.KummerDedekind
import IdealArithmetic.DedekindProject.Auxiliary.PolynomialBasics
import Mathlib.RingTheory.ZMod
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Separable
import IdealArithmetic.IdealArithmetic.CertifyPrimeIdeal
import IdealArithmetic.Generation.ClassGroupGeneration

/-
## AI use
This file is almost entirely human-writen. We have indicated whenever we use an AI-model to
complete the proof.  -/

open Ideal UniqueFactorizationMonoid Polynomial RingHom Algebra Classical


noncomputable section Adjoin

variable (R)  {S : Type*} [CommRing R]  [CommRing S] [Algebra R S]

namespace AdjoinRoot

/- A down-to-earth version of Kummer-Dedekind, for explicit computational uses. -/

lemma algHomDvd_polynomial_apply (f g h : S[X]) (hgf : g ∣ f) :
  algHomOfDvd S f g hgf (Ideal.Quotient.mk _ h) = Ideal.Quotient.mk _ h := by
  have aux1 : Ideal.Quotient.mk _ h = Polynomial.aeval (root f) h := by
    rw [aeval_eq] ; rfl
  have aux2 : Ideal.Quotient.mk _ h = Polynomial.aeval (root g) h := by
    rw [aeval_eq] ; rfl
  rw [aux1, aux2, ← Polynomial.aeval_algHom_apply,algHomOfDvd_root]

lemma algHomDvd_surjective (f g : S[X]) (hgf : g ∣ f) :
  Function.Surjective (algHomOfDvd S f g hgf) := by
  intro y
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective y
  use AdjoinRoot.mk _ p
  erw [algHomDvd_polynomial_apply, hp]

lemma algHomDvd_ker (f g : S[X]) (hgf : g ∣ f) :
  RingHom.ker (algHomOfDvd S f g hgf) = Ideal.span {Ideal.Quotient.mk _ g} := by
  ext x
  obtain ⟨h, hy⟩ := Ideal.Quotient.mk_surjective x
  erw [← hy, mem_ker, algHomDvd_polynomial_apply, AdjoinRoot.mk_eq_zero, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨k, hk⟩
    simp only [hk, map_mul]
    exact dvd_mul_right _ _
  · rintro ⟨k, hk⟩
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective k
    erw [← ht, ← map_mul ((Ideal.Quotient.mk (span {f}))), Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      Ideal.mem_span_singleton] at hk
    obtain ⟨l,ls⟩ := hk
    obtain ⟨m, hm⟩ := hgf
    use t + m * l
    rw [mul_add, ← mul_assoc, ← hm, ← ls]
    ring

end AdjoinRoot

end Adjoin

-------------------------------------------

noncomputable section

variable  {R S : Type*} [CommRing R]  [CommRing S]
  [Algebra R S] [NoZeroSMulDivisors R S]
  [IsIntegrallyClosed R] {x : S} {I : Ideal R}
  (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
  [IsDomain R] [IsDomain S]

/-- Same as `quotMapEquivQuotQuotMap'` in Mathlib but without the Dedekind domain assumption for `S`. -/
noncomputable def quotMapEquivQuotQuotMap' :
    S ⧸ I.map (algebraMap R S) ≃+* (R ⧸ I)[X] ⧸ span {(minpoly R x).map (Ideal.Quotient.mk I)} :=
  (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
    ((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans <|
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])


/-- Same as `quotMapEquivQuotQuotMap_symm_apply` in Mathlib but without the Dedekind domain assumption for `S`. -/
lemma quotMapEquivQuotQuotMap_symm_apply' (Q : R[X]) :
    (quotMapEquivQuotQuotMap' hx hx').symm (Q.map (Ideal.Quotient.mk I)) = Q.aeval x := by
  apply (quotMapEquivQuotQuotMap' hx hx').injective
  rw [quotMapEquivQuotQuotMap', AlgEquiv.toRingEquiv_eq_coe, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm, RingEquiv.coe_trans, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_trans_apply, quotEquivOfEq_symm, quotEquivOfEq_mk]
  congr
  convert (adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap_symm_apply_mk I Q
  · rfl
  apply (quotAdjoinEquivQuotMap hx
    (FaithfulSMul.algebraMap_injective ((adjoin R {x})) S)).injective
  simp only [RingEquiv.apply_symm_apply, adjoin.powerBasis'_gen, quotAdjoinEquivQuotMap_apply_mk,
    coe_aeval_mk_apply]

def quotMapHom (d : (R ⧸ I)[X])
  (hd : d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    S →+* (R ⧸ I)[X] ⧸ span {d} := by
  refine RingHom.comp ?_ (Ideal.Quotient.mk (I.map (algebraMap R S)) )
  exact RingHom.comp ((AdjoinRoot.algHomOfDvd (R ⧸ I) (S := (R ⧸ I))
    (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) d hd).toRingHom)
    (quotMapEquivQuotQuotMap' hx hx').toRingHom


lemma quotMapHom_ker (d : R[X])
  (hd : Polynomial.map (Ideal.Quotient.mk I) d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
  RingHom.ker (quotMapHom hx hx' (d.map (Ideal.Quotient.mk I)) hd) =
    Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x}) := by
  have key := Ideal.map_span (quotMapEquivQuotQuotMap' hx hx').symm
    {((Ideal.Quotient.mk (span {(minpoly R x).map (Ideal.Quotient.mk I)}))
      (d.map (Ideal.Quotient.mk I)))}
  rw [Set.image_singleton, quotMapEquivQuotQuotMap_symm_apply' hx hx' d] at key
  erw [← RingHom.comap_ker, ← RingHom.comap_ker, AdjoinRoot.algHomDvd_ker, ← Ideal.map_symm, key]
  refine le_antisymm ?_ ?_
  · intro y hy
    simp only [mem_comap, mem_span_singleton] at hy
    obtain ⟨t, ht⟩ := hy
    obtain ⟨l, hl⟩ := Ideal.Quotient.mk_surjective t
    rw [← hl, ← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at ht
    rw [Set.union_singleton, Ideal.mem_span_insert]
    use l , (y - (aeval x) d * l )
    refine ⟨by simp only [span_eq, ht], by ring⟩
  · intro y hy
    rw [Set.union_singleton, Ideal.mem_span_insert] at hy
    obtain ⟨a, z, hz, hy⟩ := hy
    rw [span_eq] at hz
    rw [mem_comap, hy, map_add, map_mul, Ideal.Quotient.eq_zero_iff_mem.2 hz, add_zero,
      mem_span_singleton]
    simp only [dvd_mul_left]

def quotMapEquiv (d : R[X])
    (hd : Polynomial.map (Ideal.Quotient.mk I) d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    S ⧸ Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x}) ≃+* (R ⧸ I)[X] ⧸ span {d.map (Ideal.Quotient.mk I)} := by
  refine RingEquiv.trans (quotEquivOfEq (quotMapHom_ker hx hx' d hd).symm) ?_
  refine RingHom.quotientKerEquivOfSurjective ?_
  unfold quotMapHom
  simp only [AlgHom.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, coe_comp]
  refine Function.Surjective.comp ?_ Ideal.Quotient.mk_surjective
  exact (AdjoinRoot.algHomDvd_surjective _ _ hd).comp
    (RingEquiv.surjective (quotMapEquivQuotQuotMap' hx hx'))

include hx hx'

attribute [local instance] Ideal.Quotient.field

lemma ideal_span_pair_maximal (hI : IsMaximal I) (d : R[X])
    (hd : Polynomial.map (Ideal.Quotient.mk I) d ∣ (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)))
    (hirr : Irreducible (Polynomial.map (Ideal.Quotient.mk I) d)) :
    IsMaximal (Ideal.span (I.map (algebraMap R S) ∪ {d.aeval x})) := by
  refine Ideal.Quotient.maximal_of_isField _ ?_
  haveI : Fact $ Irreducible (Polynomial.map (Ideal.Quotient.mk I) d) := {out := hirr}
  refine MulEquiv.isField (Field.toIsField (R :=
    (R ⧸ I)[X] ⧸ span {Polynomial.map (Ideal.Quotient.mk I) d})) (quotMapEquiv hx hx' _ hd).toMulEquiv

end



variable {p : ℕ}  {S : Type*} [CommRing S] {x : S}
  (hx : comap (algebraMap ℤ S) (conductor ℤ x) ⊔ (span {(p : ℤ)}) = ⊤) (hx' : IsIntegral ℤ x)


lemma quotMapInt.ideal_span_eq_span (d : ℤ[X]) :
  span {↑p, (aeval x) d} = span (↑(Ideal.map (algebraMap ℤ S) (span {↑p})) ∪ {(aeval x) d}) := by
  simp only [algebraMap_int_eq, map_span, eq_intCast, Set.image_singleton, Int.cast_natCast,
  Set.union_singleton]
  rw [Set.pair_comm, Ideal.span_insert, Ideal.span_insert, span_eq]


noncomputable def quotMapEquivInt [IsDomain S] [CharZero S]
  (d : ℤ[X]) (d' : (ZMod p) [X]) (hdeq : d' = d.map (algebraMap ℤ (ZMod p)))
  (hd : d' ∣ (minpoly ℤ x).map (algebraMap ℤ (ZMod p))) :
  S ⧸ Ideal.span {↑p, d.aeval x} ≃+* (ZMod p)[X] ⧸ span {d'} := by
  rw [hdeq] at hd
  choose g k hgk using exists_of_dvd_mod_pi (ZMod.ker_intCastRingHom p) (ZMod.ringHom_surjective (algebraMap ℤ (ZMod p))) _ _ hd
  have := quotMapEquiv hx hx' d ?_
  swap
  rw [hgk]
  have aux : Polynomial.map (Ideal.Quotient.mk (span {(↑p : ℤ)})) ↑p = 0 := by
    rw [← pi_dvd_iff_mod_zero (π := (p : ℤ))]
    simp only [map_natCast, dvd_refl]
    simp only [mk_ker]
  simp only [map_natCast, Polynomial.map_add, Polynomial.map_mul, aux, zero_mul, add_zero,
    dvd_mul_right]
  refine RingEquiv.trans (quotEquivOfEq ?_) (RingEquiv.trans this ?_)
  · refine quotMapInt.ideal_span_eq_span d
  · convert Ideal.quotientEquiv (span {Polynomial.map (Ideal.Quotient.mk (span {↑p})) d}) (span {d'})
      (Polynomial.mapEquiv (Int.quotientSpanNatEquivZMod p)) ?_
    simp only [Ideal.map_span, coe_coe, mapEquiv_apply, Set.image_singleton]
    rw [hdeq]
    congr 1
    rw [algebraMap_int_eq, Set.singleton_eq_singleton_iff, Polynomial.map_map]
    rfl

include hx hx'

lemma ideal_span_pair_maximal_int [IsDomain S] [CharZero S]
  [Fact $ Nat.Prime p] (d : ℤ[X]) (d' : (ZMod p) [X])
  (hdeq : d' = d.map (algebraMap ℤ (ZMod p))) (hd : d' ∣ (minpoly ℤ x).map (algebraMap ℤ (ZMod p)))
  (hdirr : Irreducible d') : IsMaximal (span {↑p, (aeval x) d}) := by
  rw [quotMapInt.ideal_span_eq_span]
  refine ideal_span_pair_maximal hx hx' ?_ d ?_ ?_
  · exact Ideal.Quotient.maximal_of_isField _ <|
    (Int.quotientSpanNatEquivZMod p).toMulEquiv.isField (Field.toIsField _)
  · rw [← map_dvd_iff (Polynomial.mapEquiv ((Int.quotientSpanNatEquivZMod p)))]
    simp only [mapEquiv_apply, Polynomial.map_map]
    exact hdeq ▸ hd
  · rw [← MulEquiv.irreducible_iff (Polynomial.mapEquiv ((Int.quotientSpanNatEquivZMod p)))]
    simp only [mapEquiv_apply, Polynomial.map_map]
    exact hdeq ▸ hdirr


lemma card_quot_span [IsDomain S] [CharZero S] [Fact $ Nat.Prime p]  (d : ℤ[X]) (d' : (ZMod p) [X])
  (hdeq : d' = d.map (algebraMap ℤ (ZMod p)))
  (hd : d' ∣ (minpoly ℤ x).map (algebraMap ℤ (ZMod p))) :
  Nat.card (S ⧸ Ideal.span {↑p, d.aeval x}) = p ^ d'.natDegree := by
  rw [Nat.card_eq_of_bijective (quotMapEquivInt hx hx' d d' hdeq hd)]
  show Nat.card (AdjoinRoot d') = p ^ d'.natDegree
  have hdz : d' ≠ 0 := by
    by_contra hc
    rw [hc, algebraMap_int_eq, zero_dvd_iff] at hd
    refine (Polynomial.map_monic_ne_zero (minpoly.monic hx') ) hd
  haveI : Module.Finite (ZMod p) (AdjoinRoot d') := PowerBasis.finite (AdjoinRoot.powerBasis hdz)
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Module.finrank_eq_card_basis
    (AdjoinRoot.powerBasis hdz).basis, (AdjoinRoot.powerBasis_dim hdz)]
  simp only [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
  exact RingEquiv.bijective (quotMapEquivInt hx hx' d d' hdeq hd)


omit hx hx'

/- Last part done with Claude Code Opus 5.  -/
lemma prod_ideal_le_span_pair {n}
  (d : Fin n → ℤ[X])  (I : Fin n → Ideal S) (hI : ∀ i, I i = Ideal.span {↑p, (d i).aeval x}) :
    ∏ i , I i ≤ Ideal.span {↑p, (∏ i, d i).aeval x} := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, one_eq_top, map_one, top_le_iff]
    refine Submodule.eq_top_iff'.mpr (Ideal.mem_of_one_mem ?_)
    refine Set.mem_of_subset_of_mem (Ideal.subset_span ) ?_
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  | succ n hn =>
    rw [Fin.prod_univ_castSucc]
    specialize hn (fun i => d i.castSucc) (fun i => I i.castSucc) (fun i => hI _ )
    refine le_trans (Ideal.mul_mono hn (le_of_eq rfl) ) ?_
    rw [hI, Ideal.span_pair_mul_span_pair, Ideal.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe]
    have hp : (p : S) ∈ span {(p : S), (aeval x) (∏ i, d i)} := Ideal.subset_span (by simp)
    have hgen : (aeval x) (∏ i, d i)
        = (aeval x) (∏ i : Fin n, d i.castSucc) * (aeval x) (d (Fin.last n)) := by
      rw [Fin.prod_univ_castSucc, map_mul]
    rcases hy with rfl | rfl | rfl | rfl
    · exact Ideal.mul_mem_left _ _ hp
    · exact Ideal.mul_mem_right _ _ hp
    · exact Ideal.mul_mem_left _ _ hp
    · rw [← hgen]
      exact Ideal.subset_span (by simp)


-- -- Proof with Claude Opus 5, with strategy specified by me.
lemma prod_ideal_le_span_pair' {n}
    (d : Fin n → ℤ[X])  (d' : Fin n → (ZMod p) [X])
    (hdeq : ∀ i , d' i = (d i).map (algebraMap ℤ (ZMod p)))
    (hd : ∏ i , d' i = (minpoly ℤ x).map (algebraMap ℤ (ZMod p)))
    (I : Fin n → Ideal S) (hI : ∀ i, I i = Ideal.span {↑p, (d i).aeval x}) :
    ∏ i , I i ≤ Ideal.span {↑p} := by
  obtain ⟨k, hk⟩ : (C (p : ℤ)) ∣ ((∏ i, d i) - minpoly ℤ x) := by
    refine (pi_dvd_iff_mod_zero (ZMod.ker_intCastRingHom p) _).mpr ?_
    rw [Polynomial.map_sub, Polynomial.map_prod, ← algebraMap_int_eq]
    simp_rw [← hdeq]
    rw [hd, sub_self]
  have hmem : ((∏ i, d i).aeval x) ∈ Ideal.span {(p : S)} := by
    have h2 : (∏ i, d i) = minpoly ℤ x + C (p : ℤ) * k := by rw [← hk]; ring
    have h3 : (algebraMap ℤ S) ((p : ℕ) : ℤ) = ((p : ℕ) : S) := by simp
    rw [h2]
    simp only [map_add, map_mul, minpoly.aeval, aeval_C, zero_add, h3]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  refine le_trans (prod_ideal_le_span_pair d I hI) ?_
  rw [Ideal.span_le]
  rintro y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
  rcases hy with rfl | rfl
  · exact Ideal.subset_span (by simp)
  · exact hmem

attribute [-instance]  Lean.Omega.IntList.instAdd

structure FactorsPolyZMod (l : List ℤ) (p m : ℕ) where
  D : Fin m → List ℤ
  D' : Fin m → List (ZMod p)
  heqm : ∀ i , (D i).map (algebraMap ℤ (ZMod p)) = D' i
  hProd : (List.prod (List.ofFn (fun i => D' i))).dropTrailingZeros' = l.map (algebraMap ℤ (ZMod p))
  {t : ℕ}
  s : Fin m → ℕ
  n : Fin m → ℕ
  hn : ∀ i, NeZero (n i) := by infer_instance
  hirr : ∀ i, CertificateIrreducibleZModOfList' p (n i) t (s i) (D' i)

structure PrimeIdealKummer {r : ℕ} (T : Fin r → Fin r → List ℤ) (a : Fin r → ℤ)
  (z : Fin r → ℤ) (l : List ℤ) (p : ℕ) where
  n : ℕ
  w : Fin 2 → Fin r → ℤ
  hpmem : (p : ℤ) • z = w 0
  hlen : l.length = n + 1
  hpol : List.ofFn (w 1) = List.sum
      (List.ofFn (fun (i : Fin (n + 1)) => if i = 0 then List.mulPointwise
      (l[i]' (by rw [hlen]; exact i.isLt)) (List.ofFn z)
      else List.mulPointwise (l[i]' (by rw [hlen] ; exact i.isLt ))
      (nPow_sq_table T (List.ofFn a) i) ))

lemma FactorsPolyZMod_eq_prod  {l : List ℤ} {p m : ℕ} (A : FactorsPolyZMod l p m) :
  ∏ i, ofList (A.D' i) = (ofList l).map (algebraMap ℤ (ZMod p)) := by
  rw [← list_sum_eq_ofList_prod, ofList_map, ← A.hProd,
    ← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList]

lemma FactorsPolyZMod_irreducible  {l : List ℤ} {p m : ℕ} [Fact $ Nat.Prime p]
  (A : FactorsPolyZMod l p m) :
  ∀ i , Irreducible (ofList (A.D' i)) := by
  intro i
  haveI := A.hn
  exact irreducible_ofList_ofCertificateIrreducibleZModOfList' (A.hirr i)

lemma PrimeIdealKummer_eq_p {O : Type*} [CommRing O]
  {p r : ℕ} {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ} {z : Fin r → ℤ} {l : List ℤ} {TT  : TimesTable (Fin r) ℤ O}
  (C : PrimeIdealKummer T a z l p)
  (hBz : TT.basis.equivFun.symm z = 1) : TT.basis.equivFun.symm (C.w 0) = ↑p := by
  rw [← C.hpmem, map_smul, hBz]
  simp

lemma PrimeIdealKummer_eq_poly_eval {O : Type*} [CommRing O]
  {p r : ℕ} {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ} {z : Fin r → ℤ} {l : List ℤ} {TT  : TimesTable (Fin r) ℤ O}
  (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  (C : PrimeIdealKummer T a z l p)
  (hBz : TT.basis.equivFun.symm z = 1) :
    TT.basis.equivFun.symm (C.w 1) = (ofList l).aeval (TT.basis.equivFun.symm a) := by
  haveI : NeZero l.length := ⟨by rw [C.hlen]; omega⟩
  have hceq := table_polynomial_eval TT.table T TT.basis l z hBz a (C.w 1)
    TT.basis_mul_basis heq ?_
  · rw [hceq]
    conv_rhs => rw [← List.ofFn_getElem (xs := l)]
    rw [ofList_eq_sum']
    simp [map_sum, Algebra.smul_def]
  · rw [List.ofFn_congr C.hlen, C.hpol]
    congr
    refine funext ?_
    intro i
    simp only [Fin.getElem_fin, Fin.cast_eq_zero, Fin.val_cast]

open Module

/-- Sonnet 5 : A `TimesTable (Fin r) ℤ O` already witnesses a `ℤ`-basis of `O`, so `O`
has characteristic zero: this need not be assumed separately. -/
lemma charZero_of_timesTable {O : Type*} [CommRing O] [IsDomain O] {ι : Type} [Finite ι]
    (B : Basis ι ℤ O) : CharZero O := by
  haveI : NoZeroSMulDivisors ℤ O := ⟨by
    intro n x h
    have h2 := congrArg B.equivFun h
    rw [map_smul, map_zero] at h2
    rcases eq_zero_or_eq_zero_of_smul_eq_zero h2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr (B.equivFun.injective (by rw [h1, map_zero]))⟩
  refine ⟨fun m n hmn => ?_⟩
  have h : ((m - n : ℤ) : O) = 0 := by push_cast; rw [hmn]; ring
  have h2 : (m - n : ℤ) • (1 : O) = 0 := by rwa [zsmul_eq_mul, mul_one]
  rcases eq_zero_or_eq_zero_of_smul_eq_zero h2 with h1 | h1
  · omega
  · exact absurd h1 one_ne_zero

-- -- Proof with Claude Opus 5, with strategy specified by me.
lemma PrimeIdealKummer_isPrime {O : Type*} [CommRing O] [IsDomain O]
  {p r m : ℕ} [Fact $ Nat.Prime p] {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ} {z : Fin r → ℤ} {l : List ℤ} {TT  : TimesTable (Fin r) ℤ O}
  (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  (hmin : minpoly ℤ (TT.basis.equivFun.symm a) = ofList l)
  (hcond : comap (algebraMap ℤ O) (conductor ℤ (TT.basis.equivFun.symm a))
      ⊔ span {(p : ℤ)} = ⊤)
  (A : FactorsPolyZMod l p m) {i : Fin m}
  (C : PrimeIdealKummer T a z (A.D i) p)
  (hBz : TT.basis.equivFun.symm z = 1) (I : Ideal O)
  (hieq : I = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm (C.w j)))) : I.IsPrime := by
  haveI := charZero_of_timesTable TT.basis
  haveI : Module.Finite ℤ O := Module.Finite.of_basis TT.basis
  have hint : IsIntegral ℤ (TT.basis.equivFun.symm a) := IsIntegral.of_finite ℤ _
  have hdeq : ofList (A.D' i) = (ofList (A.D i)).map (algebraMap ℤ (ZMod p)) := by
    rw [ofList_map, A.heqm i]
  have hdvd : ofList (A.D' i) ∣
      (minpoly ℤ (TT.basis.equivFun.symm a)).map (algebraMap ℤ (ZMod p)) := by
    rw [hmin, ← FactorsPolyZMod_eq_prod A]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have h0 : TT.basis.equivFun.symm (C.w 0) = (p : O) := PrimeIdealKummer_eq_p C hBz
  have h1 : TT.basis.equivFun.symm (C.w 1)
      = (ofList (A.D i)).aeval (TT.basis.equivFun.symm a) :=
    PrimeIdealKummer_eq_poly_eval heq C hBz
  have hI : I = Ideal.span {(p : O), (ofList (A.D i)).aeval (TT.basis.equivFun.symm a)} := by
    rw [hieq]
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact Or.inl h0
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
  rw [hI]
  exact (ideal_span_pair_maximal_int hcond hint (ofList (A.D i)) (ofList (A.D' i))
    hdeq hdvd (FactorsPolyZMod_irreducible A i)).isPrime

-- -- Proof with Claude Opus 5, with strategy specified by me.
lemma PrimeIdealKummer_card_quot {O : Type*} [CommRing O] [IsDomain O]
  {p r m : ℕ} [Fact $ Nat.Prime p] {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ} {z : Fin r → ℤ} {l : List ℤ} {TT  : TimesTable (Fin r) ℤ O}
  (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  (hmin : minpoly ℤ (TT.basis.equivFun.symm a) = ofList l)
  (hcond : comap (algebraMap ℤ O) (conductor ℤ (TT.basis.equivFun.symm a))
      ⊔ span {(p : ℤ)} = ⊤)
  (A : FactorsPolyZMod l p m) {i : Fin m}
  (C : PrimeIdealKummer T a z (A.D i) p)
  (hBz : TT.basis.equivFun.symm z = 1) (I : Ideal O)
  (hieq : I = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm (C.w j)))) :
    Nat.card (O ⧸ I) = p ^ (A.n i) := by
  haveI := charZero_of_timesTable TT.basis
  haveI : Module.Finite ℤ O := Module.Finite.of_basis TT.basis
  have hint : IsIntegral ℤ (TT.basis.equivFun.symm a) := IsIntegral.of_finite ℤ _
  have hdeq : ofList (A.D' i) = (ofList (A.D i)).map (algebraMap ℤ (ZMod p)) := by
    rw [ofList_map, A.heqm i]
  have hdvd : ofList (A.D' i) ∣
      (minpoly ℤ (TT.basis.equivFun.symm a)).map (algebraMap ℤ (ZMod p)) := by
    rw [hmin, ← FactorsPolyZMod_eq_prod A]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have h0 : TT.basis.equivFun.symm (C.w 0) = (p : O) := PrimeIdealKummer_eq_p C hBz
  have h1 : TT.basis.equivFun.symm (C.w 1)
      = (ofList (A.D i)).aeval (TT.basis.equivFun.symm a) :=
    PrimeIdealKummer_eq_poly_eval heq C hBz
  have hI : I = Ideal.span {(p : O), (ofList (A.D i)).aeval (TT.basis.equivFun.symm a)} := by
    rw [hieq]
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact Or.inl h0
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
  have hdeg : (ofList (A.D' i)).natDegree = A.n i := by
    haveI := A.hn i
    have hne : (A.D' i) ≠ 0 := List.ne_nil_of_length_eq_add_one (A.hirr i).hlen
    have htr : (A.D' i) = (A.D' i).dropTrailingZeros := by
      rw [dropTrailingZeros_eq_dropTrailingZeros']; exact (A.hirr i).htr
    have hl := natDegree_ofList (A.D' i) hne htr
    rw [(A.hirr i).hlen] at hl
    omega
  rw [hI, card_quot_span hcond hint (ofList (A.D i)) (ofList (A.D' i)) hdeq hdvd, hdeg]

-- -- Proof with Claude Opus 5, with strategy specified by me.
lemma PrimeIdealKummer_prod_le {O : Type*} [CommRing O] [IsDomain O]
  {p r m : ℕ} [Fact $ Nat.Prime p] {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ} {z : Fin r → ℤ} {l : List ℤ} {TT : TimesTable (Fin r) ℤ O}
  (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  (hmin : minpoly ℤ (TT.basis.equivFun.symm a) = ofList l)
  (A : FactorsPolyZMod l p m)
  (C : ∀ i : Fin m, PrimeIdealKummer T a z (A.D i) p)
  (hBz : TT.basis.equivFun.symm z = 1)
  (I : Fin m → Ideal O)
  (hieq : ∀ i , I i = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm ((C i).w j)))) :
  ∏ i , I i ≤ Ideal.span {↑p} := by
  refine prod_ideal_le_span_pair' (x := TT.basis.equivFun.symm a)
    (fun i => ofList (A.D i)) (fun i => ofList (A.D' i)) ?_ ?_ I ?_
  · intro i
    rw [ofList_map, A.heqm i]
  · rw [FactorsPolyZMod_eq_prod A, hmin]
  · intro i
    have h0 : TT.basis.equivFun.symm ((C i).w 0) = (p : O) :=
      PrimeIdealKummer_eq_p (C i) (hBz)
    have h1 : TT.basis.equivFun.symm ((C i).w 1)
        = (ofList (A.D i)).aeval (TT.basis.equivFun.symm a) :=
      PrimeIdealKummer_eq_poly_eval heq (C i) (hBz)
    rw [hieq i]
    congr 1
    ext y
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, rfl⟩
      fin_cases j
      · exact Or.inl h0
      · exact Or.inr h1
    · rintro (rfl | rfl)
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩

def PrimeIdealKummer_containsPrimesAbove {O : Type*} [CommRing O]
  [IsDomain O]
  {p r m : ℕ} [Fact $ Nat.Prime p] {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ} {z : Fin r → ℤ} {l : List ℤ} {TT : TimesTable (Fin r) ℤ O}
  (heq : ∀ i j , T i j = List.ofFn (TT.table i j))
  (hmin : minpoly ℤ (TT.basis.equivFun.symm a) = ofList l)
  (hcond : comap (algebraMap ℤ O) (conductor ℤ (TT.basis.equivFun.symm a)) ⊔ span {(p : ℤ)} = ⊤)
  (A : FactorsPolyZMod l p m)
  (C : ∀ i : Fin m, PrimeIdealKummer T a z (A.D i) p)
  (hBz : TT.basis.equivFun.symm z = 1)
  (I : Fin m → Ideal O)
  (hieq : ∀ i , I i = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm ((C i).w j)))) :
    ContainsPrimesAboveP p I where
  Ip := fun i => PrimeIdealKummer_isPrime heq hmin hcond A (C i) hBz (I i) (hieq i)
  hPprod := PrimeIdealKummer_prod_le heq hmin A C hBz I hieq


structure KummerData {O : Type*} [CommRing O] [IsDomain O]
  {m : ℕ} (p : ℕ) [Fact $ Nat.Prime p] (I : Fin m → Ideal O) (N : Fin m → ℕ) where
  {r : ℕ}
  {T : Fin r → Fin r → List ℤ}
  {a : Fin r → ℤ}
  {z : Fin r → ℤ}
  {l : List ℤ}
  {TT : TimesTable (Fin r) ℤ O}
  heq : ∀ i j , T i j = List.ofFn (TT.table i j)
  hmin : minpoly ℤ (TT.basis.equivFun.symm a) = ofList l
  hcond : comap (algebraMap ℤ O) (conductor ℤ (TT.basis.equivFun.symm a)) ⊔ span {(p : ℤ)} = ⊤
  A : FactorsPolyZMod l p m
  C : ∀ i : Fin m, PrimeIdealKummer T a z (A.D i) p
  hBz : TT.basis.equivFun.symm z = 1
  hieq : ∀ i , I i = Ideal.span (Set.range (fun j => TT.basis.equivFun.symm ((C i).w j)))
  hN : ∀ i, N i = p ^ (A.n i)


lemma containsPrimesAbove_of_KummerData {O : Type*} [CommRing O] [IsDomain O]
  {p m : ℕ} [Fact $ Nat.Prime p] {I : Fin m → Ideal O} {N : Fin m → ℕ}
  (D : KummerData p I N) : ContainsPrimesAboveP p I :=
  PrimeIdealKummer_containsPrimesAbove D.heq D.hmin D.hcond D.A D.C D.hBz I D.hieq

lemma card_quot_of_KummerData {O : Type*} [CommRing O] [IsDomain O]
  {p m : ℕ} [Fact $ Nat.Prime p] {I : Fin m → Ideal O} {N : Fin m → ℕ}
  (D : KummerData p I N) (i : Fin m) : Nat.card (O ⧸ I i) = N i := by
  rw [D.hN i]
  exact PrimeIdealKummer_card_quot D.heq D.hmin D.hcond D.A (D.C i) D.hBz (I i) (D.hieq i)
