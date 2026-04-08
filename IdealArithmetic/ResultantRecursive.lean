import IdealArithmetic.Discriminant
import Mathlib.Tactic.Polyrith
import IdealArithmetic.Sturm

open Polynomial

lemma resultant_pseudoremainder_of_split_monic {K : Type*} [Field K]
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] {s₁ : Finset ι} {t₁ : ι → K}
    {s₂ : Finset κ} {t₂ : κ → K} {s₃ : Finset τ} {t₃ : τ → K}
    {Q : K[X]} {e f : K} (he : e ≠ 0)
    (heq : C e * ( ∏ i ∈ s₁, (X - C (t₁ i))) =
      Q * (∏ i ∈ s₂, (X - C (t₂ i)))  - C f * (∏ i ∈ s₃, (X - C (t₃ i)) )) :
    resultant (∏ i ∈ s₁, (X - C (t₁ i))) (∏ i ∈ s₂, (X - C (t₂ i))) =
      (-1) ^ ((s₁.card + 1) * (s₂.card)) * (f / e) ^ (s₂.card) *
      (resultant (∏ i ∈ s₂, (X - C (t₂ i))) (∏ i ∈ s₃, (X - C (t₃ i)) )) := by
  rw [resultant_prod_X_sub_C]
  have :  ∀ i ∈ s₂, eval (t₂ i) (∏ i ∈ s₁, (X - C (t₁ i))) =
    - (f / e) * eval (t₂ i) (∏ i ∈ s₃, (X - C (t₃ i))) := by
    intro i hi
    apply_fun (fun x => eval (t₂ i) x) at heq
    simp only [eval_mul, eval_C, eval_sub] at heq
    nth_rw 2 [eval_prod] at heq
    rw [Finset.prod_eq_zero hi, mul_zero, zero_sub] at heq
    field_simp
    rw [← heq, mul_comm]
    simp only [eval_sub, eval_X, eval_C, sub_self]
  simp_rw [Finset.prod_congr rfl this]
  -- ← smul_eq_mul (-(f / e)) _
  rw [← Finset.pow_card_mul_prod, prod_X_sub_C_resultant,
    ← neg_one_mul (f / e), mul_pow, natDegree_finset_prod_X_sub_C_eq_card]
  ring


lemma resultant_pseudoremainder_of_split {K : Type*} [Field K]
    {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] {s₁ : Finset ι} {t₁ : ι → K}
    {s₂ : Finset κ} {t₂ : κ → K} {s₃ : Finset τ} {t₃ : τ → K}
    {Q : K[X]} {e f x₁ x₂ x₃ : K} (hx1 : x₁ ≠ 0) (hx2 : x₂ ≠ 0) (hx3 : x₃ ≠ 0) (he : e ≠ 0)
    (heq : C e * (C x₁ * ∏ i ∈ s₁, (X - C (t₁ i))) =
      Q * (C x₂ * ∏ i ∈ s₂, (X - C (t₂ i)))  - C f * (C x₃ * ∏ i ∈ s₃, (X - C (t₃ i)) )) :
      resultant (C x₁ * ∏ i ∈ s₁, (X - C (t₁ i))) (C x₂ * ∏ i ∈ s₂, (X - C (t₂ i))) =
      (-1) ^ ((s₁.card + 1) * (s₂.card)) * (f / e) ^ (s₂.card) * x₂ ^ (s₁.card - s₃.card : ℤ) *
      (resultant (C x₂ * ∏ i ∈ s₂, (X - C (t₂ i))) (C x₃ * ∏ i ∈ s₃, (X - C (t₃ i)) )) := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul] at heq
  rw [C_mul_resultant_of_not_eq_zero _ hx1, resultant_C_mul_of_not_eq_zero _ hx2,
    C_mul_resultant_of_not_eq_zero _ hx2, resultant_C_mul_of_not_eq_zero _ hx3,
    resultant_pseudoremainder_of_split_monic _ heq , natDegree_C_mul hx2,
    natDegree_C_mul hx3, zpow_sub₀ hx2]
  simp only [natDegree_finset_prod_X_sub_C_eq_card]
  field_simp
  ring_nf
  exact (mul_ne_zero_iff_right hx1).mpr he


open Classical

lemma resultant_pseudoremainder {K : Type*} [Field K] {P₁ P₂ P₃ Q : K[X]}
    (hP1 : P₁ ≠ 0) (hP2 : P₂ ≠ 0) (hP3 : P₃ ≠ 0) {e f : K} (he : e ≠ 0)
    (heq : C e * P₁ = Q * P₂ - C f * P₃) :
    resultant P₁ P₂ =
      (-1) ^ ((P₁.natDegree + 1) * P₂.natDegree) * (f / e) ^ (P₂.natDegree)
        * P₂.leadingCoeff ^ (P₁.natDegree - P₃.natDegree : ℤ) * resultant P₂ P₃ := by
  have aux1 : Splits (algebraMap K (AlgebraicClosure K)) P₁ := (IsAlgClosed.splits_codomain P₁)
  have aux2 : Splits (algebraMap K (AlgebraicClosure K)) P₂ := (IsAlgClosed.splits_codomain P₂)
  have aux3 : Splits (algebraMap K (AlgebraicClosure K)) P₃ := (IsAlgClosed.splits_codomain P₃)
  apply RingHom.injective (algebraMap K (AlgebraicClosure K))
  --simp [← resultant_map (RingHom.injective (algebraMap K (AlgebraicClosure K)))]
  simp only [map_mul, map_pow, map_neg, map_one,
    ← resultant_map (RingHom.injective (algebraMap K (AlgebraicClosure K))),
    Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_prod, hom_eval,
    ← Polynomial.eval_map]
  have prod1 := eq_prod_roots_of_splits aux1
  rw [← Multiset.prod_toList, List.Perm.prod_eq (Multiset.toList_map _ _),
    ← List.finset_prod_get] at prod1
  have prod2 := eq_prod_roots_of_splits aux2
  rw [← Multiset.prod_toList, List.Perm.prod_eq (Multiset.toList_map _ _),
    ← List.finset_prod_get] at prod2
  have prod3 := eq_prod_roots_of_splits aux3
  rw [← Multiset.prod_toList, List.Perm.prod_eq (Multiset.toList_map _ _),
    ← List.finset_prod_get] at prod3
  apply_fun map (algebraMap K (AlgebraicClosure K)) at heq
  simp at heq
  rw [prod1, prod2, prod3] at heq ⊢
  have auxr1 : P₁.natDegree =
    @Finset.univ.card (Fin (map (algebraMap K (AlgebraicClosure K)) P₁).roots.toList.length)  := by
    simp only [natDegree_eq_card_roots aux1, Finset.card_univ, Multiset.length_toList,
    Fintype.card_fin]
  have auxr2 : P₂.natDegree =
    @Finset.univ.card (Fin (map (algebraMap K (AlgebraicClosure K)) P₂).roots.toList.length) := by
    simp only [natDegree_eq_card_roots aux2, Finset.card_univ, Multiset.length_toList,
    Fintype.card_fin]
  have auxr3 : P₃.natDegree =
    @Finset.univ.card (Fin (map (algebraMap K (AlgebraicClosure K)) P₃).roots.toList.length) := by
    simp only [natDegree_eq_card_roots aux3, Finset.card_univ, Multiset.length_toList,
    Fintype.card_fin]
  convert resultant_pseudoremainder_of_split _ _ _ _ heq
  · simp only [map_div₀]
  · rw [← auxr1, ← auxr3, map_zpow₀]
  · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero, hP1, not_false_eq_true]
  · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero, hP2, not_false_eq_true]
  · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero, hP3, not_false_eq_true]
  · simp only [ne_eq, map_eq_zero, he, not_false_eq_true]


lemma resultant_psuedoremainder' {R : Type*} [CommRing R] [IsDomain R] {P₁ P₂ P₃ Q : R[X]}
  (hP1 : P₁ ≠ 0) (hP2 : P₂ ≠ 0) (hP3 : P₃ ≠ 0) {e f : R} (he : e ≠ 0)
  (heq : C e * P₁ = Q * P₂ - C f * P₃) (hmono : P₃.natDegree ≤ P₁.natDegree) :
   e ^ (P₂.natDegree) * resultant P₁ P₂ =
    ((-1) ^ ((P₁.natDegree + 1) * P₂.natDegree) * f ^ (P₂.natDegree) *
      P₂.leadingCoeff ^ (P₁.natDegree - P₃.natDegree) * resultant P₂ P₃) := by
  let K := FractionRing R
  have auxInj := FaithfulSMul.algebraMap_injective R K
  apply_fun (algebraMap R K)
  rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, map_pow ]
  rw [← Polynomial.leadingCoeff_map' auxInj, ← Polynomial.natDegree_map_eq_of_injective auxInj P₁,
  ← Polynomial.natDegree_map_eq_of_injective auxInj P₂,
    ← Polynomial.natDegree_map_eq_of_injective auxInj P₃]
  rw [← resultant_map auxInj, ← resultant_map auxInj]
  apply_fun map (algebraMap R K) at heq
  simp only [Polynomial.map_mul, map_C, Polynomial.map_sub] at heq
  rw [← Polynomial.map_ne_zero_iff auxInj] at hP1 hP2 hP3
  rw [resultant_pseudoremainder hP1 hP2 hP3 _ heq, div_pow]
  haveI : CommRing K := by exact OreLocalization.instCommRing
  field_simp
  rw [mul_div_cancel_left₀ (a := (algebraMap R K) e ^ (map (algebraMap R K) P₂).natDegree)]
  congr 2
  rw [← zpow_natCast]
  rw [← Polynomial.natDegree_map_eq_of_injective auxInj P₁,
     ← Polynomial.natDegree_map_eq_of_injective auxInj P₃] at hmono
  congr
  rw [Nat.cast_sub hmono]
  · simp only [ne_eq, pow_eq_zero_iff', FaithfulSMul.algebraMap_eq_zero_iff, he, false_and,
    not_false_eq_true]
  · simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff, he, not_false_eq_true]


lemma prod_mul_resultant_of_premainder_sequence_rec {R : Type*} [CommRing R] [IsDomain R]
    {P : List R[X]}  {p q : R[X]} (hlen : 2 ≤ P.length) (h0 : P[0] = p)
    (h1 : P[1] = q) (hPz : ∀ i, ∀ h : i < P.length, P[i] ≠ 0)
    (hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree)
    {e : List R} (hel : P.length ≤ e.length + 2) (hez : ∀ i, ∀ h : i + 2 < P.length, e[i] ≠ 0)
    {f : List R} (hfl : P.length ≤ f.length + 2)
    {Q : List R[X]} (hQl : P.length ≤ Q.length + 2)
    (hrem : ∀ i, ∀ h2 : i + 2 < P.length , C (e[i]) * P[i] =
      (Q[i]) * P[i + 1] - C (f[i]) * P[i + 2] )
    {n : ℕ} (hn : n ≤ P.length - 2) :
      (∏ (i : Fin n), e[i] ^ P[↑i + 1].natDegree) * resultant p q =
      (∏ i : Fin n, ((-1) ^ ((P[i].natDegree + 1)
      * P[↑i + 1].natDegree) * f[i] ^ (P[↑i + 1].natDegree)
      * P[↑i + 1].leadingCoeff ^ (P[i].natDegree - P[↑i + 2].natDegree)))
      * resultant P[n] P[n + 1] := by
  induction' n with n hni
  · simp only [Finset.univ_eq_empty, Fin.getElem_fin, Finset.prod_empty, one_mul, Nat.cast_one, h0,
    zero_add, h1]
  · specialize hni (by omega)
    rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
    simp
    rw [mul_assoc _ _ (P[n + 1].resultant P[n + 1 + 1]), ← resultant_psuedoremainder' (e := e[n])]
    · rw [← mul_assoc _ (e[n] ^ P[n + 1].natDegree) _, mul_comm _ (e[n] ^ P[n + 1].natDegree),
        mul_assoc (e[n] ^ P[n + 1].natDegree) _ _]
      rw [mul_comm _ (e[n] ^ P[n + 1].natDegree) , mul_assoc (e[n] ^ P[n + 1].natDegree) _ _]
      congr 1
      convert hni
      simp only [Nat.cast_one]
    · exact hPz _ (by omega)
    · exact hPz _ (by omega)
    · exact hPz _ (by omega)
    · exact hez _ (by omega)
    · exact hrem n (by omega)
    · refine le_of_lt (lt_trans (hmono (n + 1) (by omega)) (hmono (n) (by omega)))

lemma prod_mul_resultant_of_premainder_sequence {R : Type*} [CommRing R] [IsDomain R]
    {P : List R[X]}  {p q : R[X]} (hlen : 2 ≤ P.length) (h0 : P[0] = p)
    (h1 : P[1] = q) {c : R} (hcz : c ≠ 0) (hcl : P.getLastD 0 = C c)
    (hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree)
    {e : List R} (hel : P.length ≤ e.length + 2) (hez : ∀ i, ∀ h : i + 2 < P.length, e[i] ≠ 0)
    {f : List R} (hfl : P.length ≤ f.length + 2)
    {Q : List R[X]} (hQl : P.length ≤ Q.length + 2)
    (hrem : ∀ i, ∀ h2 : i + 2 < P.length , C (e[i]) * P[i] =
      (Q[i]) * P[i + 1] - C (f[i]) * P[i + 2] ) :
      (∏ (i : Fin (P.length - 2)), e[i] ^ P[↑i + 1].natDegree) * resultant p q =
      (∏ i : Fin (P.length - 2), ((-1) ^ ((P[i].natDegree + 1)
        * P[↑i + 1].natDegree) * f[i] ^ (P[↑i + 1].natDegree)
        * P[↑i + 1].leadingCoeff ^ (P[i].natDegree - P[↑i + 2].natDegree)))
        * c ^ (P[P.length - 2].natDegree) := by
  have hPz : ∀ i, ∀ h : i < P.length, P[i] ≠ 0 := by
    intro i hi hc
    exact (zero_not_member_of_mono hlen  ⟨c, hcz, hcl⟩ hmono ) (hc ▸ List.getElem_mem hi)
  rw [prod_mul_resultant_of_premainder_sequence_rec
    hlen h0 h1 hPz hmono hel hez hfl hQl hrem (by rfl)]
  congr
  convert resultant_C (P[P.length - 2]) c
  have hz : P ≠ [] := by
    intro h
    simp only [h, List.length_nil, nonpos_iff_eq_zero, OfNat.ofNat_ne_zero] at hlen
  rw [getLastD_eq_getLast_of_ne_nil hz] at hcl
  rw [← hcl, List.getLast_eq_getElem]
  congr
  omega

lemma resultant_eq_div_of_premainder_sequence {R : Type*} [CommRing R] [IsDomain R]
    [Div R] [MulDivCancelClass R] {P : List R[X]}  {p q : R[X]} (hlen : 2 ≤ P.length)
    (h0 : P[0] = p) (h1 : P[1] = q) {c : R} (hcz : c ≠ 0) (hcl : P.getLastD 0 = C c)
    (hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree)
    {e : List R} (hel : P.length ≤ e.length + 2) (hez : ∀ i, ∀ h : i + 2 < P.length, e[i] ≠ 0)
    {f : List R} (hfl : P.length ≤ f.length + 2)
    {Q : List R[X]} (hQl : P.length ≤ Q.length + 2)
    (hrem : ∀ i, ∀ h2 : i + 2 < P.length , C (e[i]) * P[i]
      = (Q[i]) * P[i + 1] - C (f[i]) * P[i + 2] ) :
      resultant p q =
      ((∏ i : Fin (P.length - 2), ((-1) ^ ((P[i].natDegree + 1) * P[↑i + 1].natDegree) *
        f[i] ^ (P[↑i + 1].natDegree)
          * P[↑i + 1].leadingCoeff ^ (P[i].natDegree - P[↑i + 2].natDegree)))
          * c ^ (P[P.length - 2].natDegree))
            / (∏ (i : Fin (P.length - 2)), e[i] ^ P[↑i + 1].natDegree) := by
  rw [← prod_mul_resultant_of_premainder_sequence
    hlen h0 h1 hcz hcl hmono hel hez hfl hQl hrem, mul_div_cancel_left₀]
  refine Finset.prod_ne_zero_iff.mpr ?_
  · intro i hi
    refine pow_ne_zero P[↑i + 1].natDegree (hez i (by omega))

def ResultantOfPRemainderCoeff {R : Type*} [CommRing R] (P : List (List R)) (f : List R)
      (i : ℕ) : R :=
  if H : i + 2 < P.length ∧ i < f.length then
    (-1) ^ ((P[i].length) * (P[i + 1].length - 1))  *
      ((f[i]) ^ ((P[i + 1]).length - 1)) *
      ((P[i + 1].getLastD 0) ^ (P[i].length  - P[i + 2].length))
  else 0

def ResultantOfPRemainder {R : Type*} [CommRing R] [Div R]  [Inhabited R]
      (P : List (List R)) (e : List R) (f : List R) :=
  if hlen : (2 ≤ P.length ∧ P.length ≤ e.length + 2) then
    (((∏ (i : Fin (P.length - 2)), ResultantOfPRemainderCoeff P f i)) *
    ((P.getLastD 0).getLastD 0) ^ (P[P.length - 2].length - 1)) /
    (∏ (i : Fin (P.length - 2)), e[i] ^ ((P[i.val + 1]).length - 1))
  else 0

def DiscriminantOfPRemainder {R : Type*} [CommRing R] [Div R]  [Inhabited R]
    (P : List (List R)) (e : List R) (f : List R) :=
  if hlen : 1 ≤ P.length then
  ((-1) ^ ((P[0].length - 1) * (P[0].length - 2) / 2) *
    ResultantOfPRemainder P e f) / (P[0].getLastD 0) else 0


theorem resultant_eq_ResultantOfPRemainder_of_SturmBuilderOfList {R : Type*} [CommRing R]
    [IsDomain R] [Div R] [MulDivCancelClass R] [LinearOrder R] [Inhabited R]
    {P : List (List R)}  {p q : List R} (h : SturmBuilderOfList P p q) :
      resultant (ofList p) (ofList q) = ResultantOfPRemainder P h.e h.f := by
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.1 h.hlast
  have hPl := h.hlen
  have hcz : c ≠ 0 := by
    rw [getLastD_eq_getLast_of_ne_nil (SturmBuilderOfList_ne_nil h)] at hc
    rw [List.getLast_eq_getElem] at hc
    intro hcc
    have := hcc ▸ hc ▸ (h.hdrop (P.length -1) (by omega))
    simp [List.dropTrailingZeros'] at this
  rw [resultant_eq_div_of_premainder_sequence (P := List.map (ofList) P)
    (hcz := hcz) (e := h.e) (f := h.f) (Q := List.map (ofList) h.Q)]
  simp only [ResultantOfPRemainder , h.hlen, h.hel, ↓reduceDIte, and_self]
  let E : Fin ((List.map ofList P).length - 2) ≃ Fin (P.length - 2) := by
    refine finCongr (by simp)
  congr 1
  · congr 1
    rw [Finset.prod_of_injOn E (s := Finset.univ) (t := Finset.univ)]
    · refine Set.injOn_of_injective (Equiv.injective E)
    · simp only [Finset.coe_univ, Set.mapsTo_univ_iff, Set.mem_univ, implies_true]
    · simp only [Finset.mem_univ, Finset.coe_univ, Set.image_univ, EquivLike.range_eq_univ,
     Set.mem_univ, not_true_eq_false, IsEmpty.forall_iff, imp_self, implies_true]
    · intro i hi
      unfold ResultantOfPRemainderCoeff
      simp only [Nat.cast_one, Fin.getElem_fin, List.getElem_map, finCongr_apply, Fin.coe_cast, E]
      have hiP : i + 2 < P.length := by
        have := i.2
        simp at this
        omega
      have hiF : i < h.f.length := by
        have := h.hfl
        omega
      simp only [hiP, hiF, and_self, ↓reduceDIte]
      congr 1
      · congr
        · rw [natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h _ _)]
          rw [dropTrailingZeros_eq_dropTrailingZeros']
          exact h.hdrop _ _
        · rw [natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _)]
          rw [dropTrailingZeros_eq_dropTrailingZeros']
          exact h.hdrop _ _
          simp only [List.length_map, hPl]
        · rw [natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _)]
          rw [dropTrailingZeros_eq_dropTrailingZeros']
          exact h.hdrop _ _
      rw [ofList_leadingCoeff _ (SturmBuilderOfList_not_mem_nil h _ _), ← getLastD_eq_getLast_of_ne_nil (a := 0)]
      congr 1
      rw [natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _)]
      rw [← natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h _ _), ← natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h _ _)]
      omega
      · rw [dropTrailingZeros_eq_dropTrailingZeros']
        exact h.hdrop _ _
      · rw [dropTrailingZeros_eq_dropTrailingZeros']
        exact h.hdrop _ _
      · rw [dropTrailingZeros_eq_dropTrailingZeros']
        exact h.hdrop _ _
      · rw [dropTrailingZeros_eq_dropTrailingZeros']
        exact h.hdrop _ _
    · simp [h.hfl]
    · conv =>
        right ; left ; left
        erw [hc]
      simp only [List.length_map, List.getElem_map, List.getLastD_eq_getLast?,
        List.getLast?_singleton, Option.getD_some]
      congr
      rw [natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _)]
      rw [dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop _ _
  · rw [Finset.prod_of_injOn E (s := Finset.univ) (t := Finset.univ)]
    · refine Set.injOn_of_injective (Equiv.injective E)
    · simp only [Finset.coe_univ, Set.mapsTo_univ_iff, Set.mem_univ, implies_true]
    · simp only [Finset.mem_univ, Finset.coe_univ, Set.image_univ, EquivLike.range_eq_univ,
     Set.mem_univ, not_true_eq_false, IsEmpty.forall_iff, imp_self, implies_true]
    · intro i hi
      congr
      rw [List.getElem_map, natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _)]
      rfl
      rw [dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop _ _
    · simp [h.hel]
  · simp [h.h0]
  · simp [h.h1]
  · convert List.getLastD_map (a := 0) (f := ofList)
    erw [hc]
    simp only [ofList_cons, ofList_nil, mul_zero, add_zero]
  · intro i hi
    simp at hi
    rw [List.getElem_map, List.getElem_map, ← Nat.succ_lt_succ_iff, Nat.succ_eq_add_one,
      Nat.succ_eq_add_one, natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h i (by omega)),
      natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h (i + 1) (by omega)) ]
    · exact h.hmono i hi
    · rw [dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop _ _
    · rw [dropTrailingZeros_eq_dropTrailingZeros']
      exact h.hdrop _ _
  · intro i hi
    simp only [List.length_map] at hi
    have := h.hel
    have := h.epos (i := i) (by omega)
    exact Ne.symm (ne_of_lt this)
  · simp [h.hQl]
  · intro i hi
    simp at hi
    have := h.hel ; have := h.hfl ; have := h.hQl
    simp only [List.getElem_map, ← ofList_mulPointwise_eq_C_mul, h.hrem i hi]
    simp only [ofList_sub, ofList_convolve_eq_mul, ofList_mulPointwise_eq_C_mul]


  /-- Should be able to get rid of the no smul divisors with ℕ. -/

theorem discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList
    {R : Type*} [CommRing R] [IsDomain R] [Div R] [MulDivCancelClass R]
    [NoZeroSMulDivisors ℕ R]
    [LinearOrder R] [Inhabited R] {P : List (List R)} {p : List R}
    (h : SturmBuilderOfList P p (List.derivative p).dropTrailingZeros) :
      discriminant (ofList p) = DiscriminantOfPRemainder P h.e h.f := by
  have := h.hlen
  have hleo : 1 ≤ P.length := by omega
  simp only [DiscriminantOfPRemainder, hleo, ↓reduceDIte, Nat.cast_one]
  rw [getLastD_eq_getLast_of_ne_nil (a := 0) (SturmBuilderOfList_not_mem_nil h _ _),
    ← ofList_leadingCoeff, ← resultant_eq_ResultantOfPRemainder_of_SturmBuilderOfList,
      ofList_dropTrailingZeros_eq_ofList, ofList_derivative_eq_derivative]
  rw [← natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _),
    ← natDegree_ofList _ (SturmBuilderOfList_not_mem_nil h _ _), h.h0]
  simp only [Nat.reduceSubDiff]
  rw [← discriminant_def, mul_div_cancel_left₀]
  · rw [ofList_leadingCoeff _ (h.h0 ▸ (SturmBuilderOfList_not_mem_nil h _ _)),
      ← eq_dropTrailingZeros_iff_last_entry_ne_zero, dropTrailingZeros_eq_dropTrailingZeros']
    exact (h.h0 ▸ h.hdrop 0 (by omega))
    rw [dropTrailingZeros_eq_dropTrailingZeros']
    exact (h.h0 ▸ h.hdrop 0 (by omega))
  · rw [← h.h0, natDegree_eq_length_sub_one _ (SturmBuilderOfList_not_mem_nil h _ _)]
    have := h.hmono 0 (by omega)
    simp only [zero_add] at this
    have : 1 ≤ P[1].length := by
      by_contra! hc
      simp at hc
      exact (SturmBuilderOfList_not_mem_nil h _ _) hc
    omega
    simp_rw [dropTrailingZeros_eq_dropTrailingZeros']
    exact h.hdrop 0 (by omega)
  repeat
  rw [dropTrailingZeros_eq_dropTrailingZeros']
  exact h.hdrop 0 (by omega)


-------------- EXAMPLE


def T12 : SturmBuilderOfList [[-1, -3, 4, -3, 4, -7, 8, -5, 2, -1, 2, -2, 1], [-3, 8, -9, 16, -35, 48, -35, 16, -9, 20, -22, 12], [75, 190, -231, 146, -157, 246, -253, 134, -39, -2, -2], [71, 154, -281, 214, -195, 282, -319, 210, -81, 10], [-10211, -24224, 35581, -23964, 23455, -36012, 38859, -22620, 7221], [-2267, -4492, 8045, 382, 1384, -5348, 5424, -1734], [246562, 814245, -405514, -231107, -606672, 731024, -399754], [14471167, 16037714, -36741730, -13829396, 17035399, -23152604], [-3486108299, -5816633006, 9229540306, -954771996, 311520877], [71085451054, 150856520123, -136214103852, -61173383617], [208293783922595, 367093071086944, -527066681760297], [-15465343873515557, -79274710004591368], [-1]] [-1, -3, 4, -3, 4, -7, 8, -5, 2, -1, 2, -2, 1] [-3, 8, -9, 16, -35, 48, -35, 16, -9, 20, -22, 12] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 12 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [144, 4, 100, 52142841, 3006756, 159803260516, 536043071980816, 97045256806849129, 3742182863152644002689, 277799287021810194306565528209, 6284479646312058733427640660111424]
  f := [2, 72, 2, 17400, 124002, 9688436, 79901630258, 804064607971224, 97045256806849129, 7484365726305288005378, 732895876018653850638624204849589761586603129983]
  epos := by decide
  fpos := by decide
  Q := [[-2, 12], [68, -24], [-182, -20], [-358701, 72210], [56376, -12521214], [-900670080, 693173436], [-10115140294650, 9255346059416], [-16798575497152661, -7212519502913708], [100840170669820907736, -19056786113425272109], [94250240986970406200560492, 32242452315061905220854249], [-37252464232808112746708894339821, 41783058349629791285370411316296]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 11 := by omega
    interval_cases i <;> (dsimp ; decide)


set_option maxRecDepth 1000

theorem discr12 : discriminant (C (-1) + C (-3) * X + C 4 * X ^ 2 + C (-3) * X ^ 3
  + C 4 * X ^ 4 + C (-7) * X ^ 5 + C 8 * X ^ 6 + C (-5) * X ^ 7 +
C 2 * X ^ 8 + C (-1) * X ^ 9 + C 2 * X ^ 10 + C (-2) * X ^ 11 + X ^ 12) = -2638220867575926287 := by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList T12
  simp ; ring


def T8 : SturmBuilderOfList [[-1, 2, 56, 2, 3, 4, 5, -7, 1], [2, 112, 6, 12, 20, 30, -49, 8], [50, -896, -2730, -164, -236, -306, 263], [-10317, 26744, 409348, -75968, 11487, 9730], [118039, -210658, -4396196, 3136696, -497669], [-891307726, 226789062, 30505154223, -38072891440], [-45100387975686, 152751896379902, 1843938372217163], [159617440905728815, 8192722259337557422], [1]] [-1, 2, 56, 2, 3, 4, 5, -7, 1] [2, 112, 6, 12, 20, 30, -49, 8] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 8 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [64, 69169, 94672900, 247674433561, 1449545062602025273600, 3400108720534880761404431768569, 67120698018645091490934057609147286084]
  f := [1, 64, 484183, 1932100, 1733721034927, 1449545062602025273600, 3179944025378457415939922163175606093704156735676809]
  epos := by decide
  fpos := by decide
  Q := [[-7, 8], [-10439, 2104], [-5998461, 2558990], [-36236775883, -4842319370], [-104241616691276053, 18947697810053360], [62065330790318273606368229, -70204065467474359003784720], [957129137466468373062228885080799, 15106874946910213575183718966433786]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 7 := by omega
    interval_cases i <;> (dsimp ; decide)


theorem discr8 : discriminant (C (-1) + C 2 * X + C 56 * X ^ 2 + C 2 * X ^ 3 +
  C 3 * X ^ 4 + C 4 * X ^ 5 + C 5 * X ^ 6 + C (-7) * X ^ 7 + X ^ 8) = 935247748453823378961 := by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList T8
  simp ; ring


#exit
  --· refine Finset.prod_bijective ?_ ?_ ?_ ?_



-- resultant_C













 /- rw [← Polynomial.leadingCoeff_of_injective, ← Polynomial.leadingCoeff_of_injective,
    ← Polynomial.leadingCoeff_of_injective, ← Polynomial.leadingCoeff_of_injective]


 ← List.finset_prod_get
  have := Finset.prod_eq_multiset_prod (s := (map (algebraMap K (AlgebraicClosure K)) P₁).roots) (f := fun a ↦ X - C a) (β := (AlgebraicClosure K)[X])
  rw [← Finset.prod_eq_multiset_prod (s := (map (algebraMap K (AlgebraicClosure K)) P₁).roots)] at this
  rw [eq_prod_roots_of_splits this,
      ← Finset.prod_eq_multiset_prod, ← one_mul (s.val.map _).prod, ← map_one C,
      resultant_multiset_eq_prod_roots] -/
open AdjoinRoot
variable {F : Type*} [Field F]

noncomputable
def xyz : AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F) ≃ₗ[F] Fin 2 → F := by
  letI p : Polynomial F := Polynomial.X ^ 2 + 1
  have hp₀ : p ≠ 0 := Polynomial.Monic.ne_zero <| by simp only [p]; monicity!
  letI pb := AdjoinRoot.powerBasis hp₀
  have hpb : pb.dim = 2 := by
    simp [pb, p]
    compute_degree!
  let congrAux : (Fin pb.dim →₀ F) ≃ₗ[F] Fin 2 →₀ F  := by
    refine Finsupp.domLCongr ?_
    exact finCongr hpb
  refine (((AdjoinRoot.powerBasis hp₀).basis.repr).trans congrAux).trans (Finsupp.linearEquivFunOnFinite F F (Fin 2))

lemma xyz_aux (a b : F) :
  xyz.symm ![a, b] = a • 1 + b • AdjoinRoot.root (Polynomial.X ^ 2 + 1 : Polynomial F) := by
  simp [xyz, Finsupp.linearEquivFunOnFinite, Finsupp.linearCombination]
  rw [Finsupp.sum_fintype]
  simp
  congr
  · exact PowerBasis.basis_eq_pow _ (Fin.cast _ 0)
  · convert PowerBasis.basis_eq_pow _ (Fin.cast _ 1)
    rw [AdjoinRoot.powerBasis_gen]
    simp only [powerBasis_dim, Fin.isValue, Fin.coe_cast, Fin.val_one, pow_one]
  simp only [zero_smul, implies_true]

lemma x_poly (a b : F) : AdjoinRoot.mk (X ^ 2 + 1) (C a + C b * X) = xyz.symm ![a, b] := by
  rw [xyz_aux]
  simp only [map_add, mk_C, map_mul, mk_X]
  rw [← AdjoinRoot.algebraMap_eq, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  simp

lemma xyz_mul (x y : AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F)) :
    xyz (x * y) = ![xyz x 0 * xyz y 0 - xyz x 1 * xyz y 1,
                    xyz x 0 * xyz y 1 + xyz x 1 * xyz y 0] := by
  have aux : ∀ x : AdjoinRoot (Polynomial.X ^ 2 + 1 : Polynomial F),
     x = xyz.symm ![xyz x 0, xyz x 1] := by
     intro x
     have aux1 : x = xyz.symm (xyz x) := by simp only [LinearEquiv.symm_apply_apply]
     have aux2 : (xyz x) = ![xyz x 0, xyz x 1] := List.ofFn_inj.mp rfl
     nth_rw 1 [aux1, aux2]
  apply_fun xyz.symm
  simp only [LinearEquiv.symm_apply_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue]
  nth_rw 1 [aux x, aux y, ← x_poly, ← x_poly, ← x_poly, ← map_mul]
  rw [AdjoinRoot.mk_eq_mk]
  use C (xyz x 1 • xyz y 1)
  simp ; ring
  exact LinearEquiv.injective xyz.symm
