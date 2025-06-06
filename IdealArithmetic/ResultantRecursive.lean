import IdealArithmetic.Discriminant

open Polynomial

lemma recursive_resultant_of_split_monic {K : Type*} [Field K]
  {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] {s₁ : Finset ι} {t₁ : ι → K}
  {s₂ : Finset κ} {t₂ : κ → K} {s₃ : Finset τ} {t₃ : τ → K}
  {Q : K[X]} {e f : K} (he : e ≠ 0)
  (heq : C e * ( ∏ i ∈ s₁, (X - C (t₁ i))) = Q * (∏ i ∈ s₂, (X - C (t₂ i)))  - C f * (∏ i ∈ s₃, (X - C (t₃ i)) )):
    resultant (∏ i ∈ s₁, (X - C (t₁ i))) (∏ i ∈ s₂, (X - C (t₂ i))) =
    (-1) ^ ((s₁.card + 1) * (s₂.card)) * (f / e) ^ (s₂.card) *
    (resultant (∏ i ∈ s₂, (X - C (t₂ i))) (∏ i ∈ s₃, (X - C (t₃ i)) )) := by
  rw [resultant_prod_X_sub_C]
  have :  ∀ i ∈ s₂, eval (t₂ i) (∏ i ∈ s₁, (X - C (t₁ i))) = - (f / e) * eval (t₂ i) (∏ i ∈ s₃, (X - C (t₃ i))) := by
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
  rw [← Finset.pow_card_mul_prod, prod_X_sub_C_resultant, ← neg_one_mul (f / e), mul_pow, natDegree_finset_prod_X_sub_C_eq_card]
  ring


#check C_mul_resultant_of_not_eq_zero

lemma recursive_resultant_of_split {K : Type*} [Field K]
  {ι κ τ : Type*} [DecidableEq ι] [DecidableEq κ] [DecidableEq τ] {s₁ : Finset ι} {t₁ : ι → K}
  {s₂ : Finset κ} {t₂ : κ → K} {s₃ : Finset τ} {t₃ : τ → K}
  {Q : K[X]} {e f x₁ x₂ x₃ : K} (hx1 : x₁ ≠ 0) (hx2 : x₂ ≠ 0) (hx3 : x₃ ≠ 0) (he : e ≠ 0)
  (heq : C e * (C x₁ * ∏ i ∈ s₁, (X - C (t₁ i))) = Q * (C x₂ * ∏ i ∈ s₂, (X - C (t₂ i)))  - C f * (C x₃ * ∏ i ∈ s₃, (X - C (t₃ i)) )):
    resultant (C x₁ * ∏ i ∈ s₁, (X - C (t₁ i))) (C x₂ * ∏ i ∈ s₂, (X - C (t₂ i))) =
    (-1) ^ ((s₁.card + 1) * (s₂.card)) * (f / e) ^ (s₂.card) * x₂ ^ (s₁.card - s₃.card : ℤ) *
    (resultant (C x₂ * ∏ i ∈ s₂, (X - C (t₂ i))) (C x₃ * ∏ i ∈ s₃, (X - C (t₃ i)) )) := by
  rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← C_mul, ← C_mul] at heq
  rw [C_mul_resultant_of_not_eq_zero _ hx1, resultant_C_mul_of_not_eq_zero _ hx2, C_mul_resultant_of_not_eq_zero _ hx2, resultant_C_mul_of_not_eq_zero _ hx3,
    recursive_resultant_of_split_monic _ heq , natDegree_C_mul hx2, natDegree_C_mul hx3, zpow_sub₀ hx2]
  simp only [natDegree_finset_prod_X_sub_C_eq_card]
  field_simp
  ring_nf
  exact (mul_ne_zero_iff_right hx1).mpr he


--example {S : Multiset α} (f : α → β): (Multiset.map f S).toList = List.map f (S.toList)  := by apply?
open Classical

lemma recursive_resultant {K : Type*} [Field K] (P₁ P₂ P₃ Q : K[X])
  (hP1 : P₁ ≠ 0) (hP2 : P₂ ≠ 0) (hP3 : P₃ ≠ 0) (e f : K) (he : e ≠ 0)
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
  rw [← Multiset.prod_toList, List.Perm.prod_eq (Multiset.toList_map _ _), ← List.finset_prod_get] at prod1
  have prod2 := eq_prod_roots_of_splits aux2
  rw [← Multiset.prod_toList, List.Perm.prod_eq (Multiset.toList_map _ _), ← List.finset_prod_get] at prod2
  have prod3 := eq_prod_roots_of_splits aux3
  rw [← Multiset.prod_toList, List.Perm.prod_eq (Multiset.toList_map _ _), ← List.finset_prod_get] at prod3
  apply_fun map (algebraMap K (AlgebraicClosure K)) at heq
  simp at heq
  rw [prod1, prod2, prod3] at heq ⊢
  have auxr1 : P₁.natDegree = @Finset.univ.card (Fin (map (algebraMap K (AlgebraicClosure K)) P₁).roots.toList.length)  := by
    simp only [natDegree_eq_card_roots aux1, Finset.card_univ, Multiset.length_toList,
    Fintype.card_fin]
  have auxr2 : P₂.natDegree = @Finset.univ.card (Fin (map (algebraMap K (AlgebraicClosure K)) P₂).roots.toList.length) := by
    simp only [natDegree_eq_card_roots aux2, Finset.card_univ, Multiset.length_toList,
    Fintype.card_fin]
  have auxr3 : P₃.natDegree = @Finset.univ.card (Fin (map (algebraMap K (AlgebraicClosure K)) P₃).roots.toList.length) := by
    simp only [natDegree_eq_card_roots aux3, Finset.card_univ, Multiset.length_toList,
    Fintype.card_fin]
  convert recursive_resultant_of_split _ _ _ _ heq
  · simp only [map_div₀]
  · rw [← auxr1, ← auxr3, map_zpow₀]
  · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero, hP1, not_false_eq_true]
  · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero, hP2, not_false_eq_true]
  · simp only [ne_eq, map_eq_zero, leadingCoeff_eq_zero, hP3, not_false_eq_true]
  · simp only [ne_eq, map_eq_zero, he, not_false_eq_true]


 /- rw [← Polynomial.leadingCoeff_of_injective, ← Polynomial.leadingCoeff_of_injective,
    ← Polynomial.leadingCoeff_of_injective, ← Polynomial.leadingCoeff_of_injective]


 ← List.finset_prod_get
  have := Finset.prod_eq_multiset_prod (s := (map (algebraMap K (AlgebraicClosure K)) P₁).roots) (f := fun a ↦ X - C a) (β := (AlgebraicClosure K)[X])
  rw [← Finset.prod_eq_multiset_prod (s := (map (algebraMap K (AlgebraicClosure K)) P₁).roots)] at this
  rw [eq_prod_roots_of_splits this,
      ← Finset.prod_eq_multiset_prod, ← one_mul (s.val.map _).prod, ← map_one C,
      resultant_multiset_eq_prod_roots] -/
