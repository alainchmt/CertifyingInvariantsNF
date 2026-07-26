/- Authors: Alain Chavarri Villarello -/

import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.Hom
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Sign.Basic
import Mathlib.Data.List.Destutter
import IdealArithmetic.DedekindProject.Polynomial.PolynomialsAsLists

open Polynomial

/- # Real closed fields

We develop some theory about real closed fields.

## Remark
An alternative definition `IsRealClosed` now exists in Mathlib by
Artie Khovanov, which was developed in parallel and independently to this formalization.
Most of our formalized results in this file are now part of the
repository mantained by Artie Khovanov on real closed fields.

## Main Definition:
- `IsRealClosedField`: A totally ordered field is a real closed field if it satisfies
  the intermediate value theorem for polynomial functions.

## Main Results:
- `rolle_theorem` : Rolle's theorem for polynomial functions over real closed field .
- `mean_value_theorem` : the mean value theorem for polynomial functions over real closed fields.

## Reference:
* `Formal proofs in real algebraic geometry` by `Assia Mahboubi` and `Cyril Cohen` .

-/


def IsRealClosedField (F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] : Prop :=
    ∀ {a b t : F} , ∀ {P : F[X]},
    a ≤ b → t ∈ Set.Ioo (P.eval a) (P.eval b) → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t

lemma Real.IsRealClosedField : IsRealClosedField ℝ := by
  rintro a b t P hab h
  let f : ℝ → ℝ := fun x => P.eval x
  exact (Set.mem_image _ _ _).1
    (intermediate_value_Ioo hab (f := f) (Polynomial.continuousOn P ) h)

namespace IsRealClosedField

variable {F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
open Set

lemma polynomial_has_root_of_le_zero_of_pos (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : P.eval a < 0) (hb : 0 < P.eval b ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  exact hc hab ⟨ha, hb⟩

lemma polynomial_has_root_of_pos_le_zero (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : 0 < P.eval a) (hb : P.eval b < 0 ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b 0 (- P) hab (by simp[ha, hb])
  simp only [eval_neg, neg_eq_zero] at hs2
  exact ⟨s, hs1, hs2 ⟩

lemma intermediate_value_theorem_swap (hc : IsRealClosedField F) {a b t : F} (hab : a ≤ b)
    {P : F[X]} (hmem : t ∈ Set.Ioo (P.eval b) (P.eval a)) : ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b (-t) (- P) hab (by simp [hmem.1, hmem.2])
  simp at hs2
  exact ⟨s, hs1, hs2⟩

lemma sign_ne_eq_iff_of_ne_zero {a b : SignType} (ha : a ≠ 0) (hb : b ≠ 0) :
  a ≠ b ↔ a * b = - 1 := by
  cases a ;
  cases b ; simp ; simp at ha ; simp at ha
  cases b ; simp at hb ; simp ; simp
  cases b ; simp at hb ; simp ; simp


lemma polynomial_has_root_of_mul_neg (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (habm : (P.eval a) * (P.eval b) < 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rcases lt_trichotomy (P.eval a) 0 with hl1 | hl2 | hl3
  · have : eval b P > 0 := by nlinarith
    exact polynomial_has_root_of_le_zero_of_pos hc hab hl1 this
  · simp[hl2] at habm
  · have : eval b P < 0 := by nlinarith
    exact polynomial_has_root_of_pos_le_zero hc hab hl3 this


lemma polynomial_has_root_of_ne_sign (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hne : SignType.sign (P.eval a) ≠ SignType.sign (P.eval b)) (hanz : P.eval a ≠ 0)
    (hbnz : P.eval b ≠ 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rw [sign_ne_eq_iff_of_ne_zero (by simp[hanz]) (by simp[hbnz] ), ← sign_mul,
    sign_eq_neg_one_iff] at hne
  exact polynomial_has_root_of_mul_neg hc hab hne


lemma neg_of_ne_zero_of_exists_neg (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Ioo a b , P.eval x < 0 := by
  intro x hx
  by_contra! hc'
  rcases le_iff_lt_or_eq.1 hc' with hz1 | hz2
  · rcases le_or_gt m x with hm1 | hm2
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc hm1 hneg hz1
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hm.1 hs1.1, lt_trans hs1.2 hx.2⟩
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm2) hz1 hneg
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hx.1 hs1.1, lt_trans hs1.2 hm.2⟩
  · exact hP x hx hz2.symm

lemma nonpos_of_ne_zero_of_exists_neg (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hneg : P.eval m < 0) :
    ∀ x ∈ Icc a b , P.eval x ≤ 0 := by
  intro x hmem
  rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hmem with ha | hb | hx
  · rw [ha]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm.1) hc' hneg
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨hs1.1, lt_trans hs1.2 hm.2⟩
  · rw [hb]
    by_contra! hc'
    obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hm.2) hneg hc'
    refine hP s ?_ hs2
    simp only [mem_Ioo] at hs1
    exact ⟨lt_trans hm.1 hs1.1, hs1.2⟩
  · exact le_of_lt (neg_of_ne_zero_of_exists_neg hc hP hm hneg x hx)


lemma pos_of_ne_zero_of_exists_pos (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Ioo a b , P.eval x > 0 := by
  have := neg_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma nonneg_of_ne_zero_of_exists_pos (hc : IsRealClosedField F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Icc a b , P.eval x ≥ 0 := by
  have := nonpos_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma constant_sign_of_ne_zero (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Ioo a b , P.eval x > 0) ∨ (∀ x ∈ Ioo a b , P.eval x < 0)  := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact neg_of_ne_zero_of_exists_neg hc hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact pos_of_ne_zero_of_exists_pos hc hP hm hl3
  · simp [h2]

lemma constant_sign_of_ne_zero' (hc : IsRealClosedField F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) :
    (∀ x ∈ Icc a b , P.eval x ≥ 0) ∨ (∀ x ∈ Icc a b , P.eval x ≤ 0) := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      exact nonpos_of_ne_zero_of_exists_neg hc hP hm hl1
    · exfalso ; exact hP m hm hl2
    · left
      exact nonneg_of_ne_zero_of_exists_pos hc hP hm hl3
  · simp [h2, LinearOrder.le_total 0 (eval b P)]

/- Weak version of Rolle's theorem for successive roots. -/
lemma rolle_theorem_weak (hc : IsRealClosedField F) {a b : F} (hab : a < b) {P : F[X]}
    (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , (derivative P).eval c = 0 := by
  have hPnz : P ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := exists_between hab
    specialize hP m hm
    simp [h, eval_zero] at hP
  obtain ⟨Q' , hQ'1, hQ'2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPnz a
  have hQnz : Q' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ'1
    exact hPnz hQ'1
  obtain ⟨Q , hQ1, hQ2⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q' hQnz b
  rw [hQ1] at hQ'1
  have ham : rootMultiplicity a P ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hPnz).2 ?_
    exact hPa
  have hbm : rootMultiplicity b Q' ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hQnz).2 ?_
    rw [hQ'1 ] at hPb
    simp[(sub_ne_zero_of_ne (Ne.symm (ne_of_lt hab))), hQnz] at hPb
    rcases hPb with hPb1 | hPb2
    · exact hPb1
    · rw [hQ1]
      simp[hPb2]
  rw [← Nat.succ_pred_eq_of_ne_zero ham, ← Nat.succ_pred_eq_of_ne_zero hbm] at hQ'1
  have hQr : Q.eval a ≠ 0 ∧ Q.eval b ≠ 0 := by
    constructor
    · intro hc
      apply hQ'2
      rw [Polynomial.dvd_iff_isRoot, hQ1]
      simp[hc]
    · rwa [Polynomial.dvd_iff_isRoot] at hQ2
  set Q1 : F[X] := C (rootMultiplicity b Q' : F) * (X - C a) * Q +
      C (rootMultiplicity a P : F) * (X - C b) * Q + (X - C a) * (X - C b) * derivative Q with hQd
  have hderiv : derivative P = ((X - C a) ^ (rootMultiplicity a P).pred) *
    ((X - C b) ^ (rootMultiplicity b Q').pred) * Q1 := by
    nth_rw 1 [hQ'1, hQd, ← mul_assoc, derivative_mul, derivative_mul,
      derivative_pow, derivative_pow, derivative_X_sub_C, derivative_X_sub_C, mul_one, mul_one]
    rw [mul_add, mul_add, add_mul _ _ Q]
    nth_rw 2 [add_comm]
    have : ∀ n : ℕ , (n : F[X]) + 1 = ↑(n + 1) := fun n => by simp only [Nat.cast_add, Nat.cast_one]
    congr 1
    congr 1
    · simp [Nat.succ_eq_add_one] ; simp_rw [this, Nat.sub_one_add_one hbm] ; ring
    · simp [Nat.succ_eq_add_one] ; simp_rw [this, Nat.sub_one_add_one ham] ; ring
    · simp [Nat.succ_eq_add_one] ; ring
  have hQ1a : Q1.eval a =  - (rootMultiplicity a P) * (b - a) * (Q.eval a) := by
    rw [hQd] ; simp ; ring
  have hQ1b : Q1.eval b =  (rootMultiplicity b Q') * (b - a) * (Q.eval b) := by
    rw [hQd] ; simp
  have hQIoo : ∀ x ∈ Ioo a b, Q.eval x ≠ 0 := by
    intro x hmem h
    apply hP x hmem
    rw [hQ'1] ; simp[h]
  have hzQ : ∃ c ∈ Ioo a b , Q1.eval c = 0 := by
    apply polynomial_has_root_of_mul_neg hc (le_of_lt hab)
    simp [hQ1a, hQ1b]
    have : ↑(rootMultiplicity a P) * (b - a) * eval a Q * (↑(rootMultiplicity b Q') * (b - a) * eval b Q) =
      ↑(rootMultiplicity a P) * (↑(rootMultiplicity b Q') * (b - a) * (b - a) * ((eval a Q) * (eval b Q))) := by ring
    rw [this]
    refine mul_pos ?_ (mul_pos ((mul_pos ((mul_pos ?_ ?_)) ?_)) ?_)
    · rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero ham
    · rw [Nat.cast_pos]
      exact Nat.pos_of_ne_zero hbm
    · linarith
    · linarith
    · refine lt_of_le_of_ne ?_ ?_
      · rcases constant_sign_of_ne_zero' hc (le_of_lt hab) hQIoo with hqal | hqag
        · refine mul_nonneg (hqal a (by simp [le_of_lt hab])) (hqal b (by simp [le_of_lt hab]))
        · refine mul_nonneg_of_nonpos_of_nonpos (hqag a (by simp [le_of_lt hab]))
            (hqag b (by simp [le_of_lt hab]))
      · simp[hQr]
  obtain ⟨c, hcI, hc⟩ := hzQ
  use c
  refine ⟨hcI, ?_ ⟩
  simp [hderiv, hc]

lemma rolle_theorem_weak' (hc : IsRealClosedField F) {a b : F} (hab : a < b) {P : F[X]}
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , ((derivative P).eval c = 0 ∨ P.eval c = 0) := by
  by_contra! hcc
  have hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0 := fun x hx => (hcc x hx).2
  obtain ⟨c, hc1, hc2⟩ := rolle_theorem_weak hc hab hP hPa hPb
  exact (hcc c hc1).1 hc2

open Finset

/-- Based on Assia and Cyril paper-/
lemma rolle_theorem_induction (hc : IsRealClosedField F) (n : ℕ)
    {a b : F} {P : F[X]} (hab : a < b) (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hcard : #((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b)) < n) :
    ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  revert P a b
  induction n with
  | zero => simp only [Set.mem_Ioo, not_lt_zero', IsEmpty.forall_iff, implies_true]
  | succ n hn =>
    intro a b P hab hPa hPb hcard
    obtain ⟨c , hcmem, hcd⟩ := rolle_theorem_weak' hc hab hPa hPb
    rcases hcd with hcd1 | hcd2
    · exact ⟨c, hcmem, hcd1⟩
    · have : P ≠ 0 → filter (fun x ↦ x ∈ Set.Ioo a c) P.roots.toFinset
        ⊂ filter (fun x ↦ x ∈ Set.Ioo a b) P.roots.toFinset := by
        intro hPz
        rw [Finset.ssubset_def, Finset.not_subset]
        constructor
        · intro r hr
          simp at hr ⊢
          refine ⟨hr.1, ⟨hr.2.1, lt_trans hr.2.2 hcmem.2 ⟩ ⟩
        · use c
          simp [hcd2, hPz]
          exact hcmem
      by_cases hPz : P = 0
      · simp [hPz, exists_between hab]
      · obtain ⟨r, hr1, hr2⟩ := hn hcmem.1 hPa hcd2 (by linarith [Finset.card_lt_card (this hPz)])
        refine ⟨r, ⟨hr1.1, lt_trans hr1.2 hcmem.2⟩, hr2  ⟩

/- Rolle's  theorem for polynomials  -/
theorem rolle_theorem (hc : IsRealClosedField F) {a b : F} {P : F[X]} (hab : a < b)
    (hPab : P.eval a = P.eval b) : ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  wlog h : P.eval a = 0
  · have := this hc (P := P - C (P.eval a) ) hab
    simp at this
    simp [this, hPab]
  · rw [h] at hPab
    exact rolle_theorem_induction hc
      ((#((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b))) + 1)
      hab h hPab.symm (lt_add_one _)

/- Mean value theorem for polynomials -/
theorem mean_value_theorem  (hc : IsRealClosedField F) {a b : F} {P : F[X]} (hab : a < b) :
    ∃ c ∈ Ioo a b , P.eval b - P.eval a = ((derivative P).eval c) * (b - a) := by
  let Q : F[X] :=  (C (P.eval b) - C (P.eval a)) * (X - C a) - (C b - C a) * (P - C (P.eval a))
  have Q_deriv : derivative Q = (C (P.eval b) - C (P.eval a)) - (C b - C a) * (derivative P) := by
    simp[Q]
  have hQa : Q.eval a = 0 := by simp[Q]
  have hQb : Q.eval b = 0 := by simp[Q] ; ring
  obtain ⟨c, hcmem, hc⟩ := rolle_theorem hc hab (Eq.trans hQa hQb.symm)
  use c , hcmem
  rw [Q_deriv] at hc
  simp at hc
  linarith

lemma change_sign_of_unique_root_of_squarefree (hc : IsRealClosedField F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) : (P.eval a) * (P.eval b) < 0 := by
  by_contra! hcc
  rcases le_iff_eq_or_lt.1 hcc with hz | hpos
  · simp at hz
    rcases hz with ha | hb
    · rw [hur a (Set.left_mem_Icc.2 (le_of_lt hab)) ha] at hmem
      exact Set.left_notMem_Ioo hmem
    · rw [hur b (Set.right_mem_Icc.2 (le_of_lt hab)) hb] at hmem
      exact Set.right_notMem_Ioo hmem
  · rcases mul_pos_iff.1 hpos with hpos1 | hpos2
    · by_cases hleq : eval a P < eval b P
      · rw [← hr] at hpos1
        obtain ⟨s, hsmem, hs⟩  := hc (le_of_lt hmem.2) ⟨hpos1.1, hleq⟩
        obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hmem.1 hsmem.1) hs.symm
        refine hd t ?_ htmem2
        exact ⟨le_of_lt htmem.1, le_of_lt (lt_trans htmem.2 hsmem.2) ⟩
      · push Not at hleq
        rcases le_iff_eq_or_lt.1 hleq with hz2 | hpos'
        · obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc hab hz2.symm
          refine hd t ?_ htmem2
          exact mem_Icc_of_Ioo htmem
        · rw [← hr] at hpos1
          obtain ⟨s, hsmem, hs⟩  := intermediate_value_theorem_swap hc (le_of_lt hmem.1) ⟨hpos1.2, hpos'⟩
          obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hsmem.2 hmem.2 ) hs
          refine hd t ?_ htmem2
          exact ⟨le_of_lt (lt_trans hsmem.1 htmem.1), le_of_lt (htmem.2)⟩
    · by_cases hleq : eval a P < eval b P
      · rw [← hr] at hpos2
        obtain ⟨s, hsmem, hs⟩ := hc (le_of_lt hmem.1) ⟨hleq, hpos2.2⟩
        obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hsmem.2 hmem.2) hs
        refine hd t ?_ htmem2
        exact ⟨le_of_lt (lt_trans hsmem.1 htmem.1), le_of_lt (htmem.2)⟩
      · push Not at hleq
        rcases le_iff_eq_or_lt.1 hleq with hz2 | hpos'
        · obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc hab hz2.symm
          refine hd t ?_ htmem2
          exact mem_Icc_of_Ioo htmem
        · rw [← hr] at hpos2
          obtain ⟨s, hsmem, hs⟩  := intermediate_value_theorem_swap hc (le_of_lt hmem.2) ⟨hpos', hpos2.1⟩
          obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hmem.1 hsmem.1 ) hs.symm
          refine hd t ?_ htmem2
          exact ⟨le_of_lt htmem.1, le_of_lt (lt_trans htmem.2 hsmem.2) ⟩

lemma sign_derivative_of_opposite_sign_neg (hc : IsRealClosedField F) {a b : F}
    {P : F[X]} (hab : a < b) (hsign : (P.eval a) * (P.eval b) < 0)
    (hapos : 0 < P.eval a ) (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
    ∀ x ∈ Icc a b, (derivative P).eval x < 0  := by
  intro x hxmem
  refine lt_of_le_of_ne ?_ ?_
  · have : P.eval b < P.eval a := by nlinarith
    obtain ⟨c, hcmem, hcp⟩ := mean_value_theorem hc hab (P := P)
    refine nonpos_of_ne_zero_of_exists_neg hc (fun y hy => hd y (mem_Icc_of_Ioo hy) ) (hcmem) ?_ x hxmem
    nlinarith
  · exact hd x hxmem

lemma sign_derivative_of_opposite_pos (hc : IsRealClosedField F) {a b : F}
    {P : F[X]} (hab : a < b) (hsign : (P.eval a) * (P.eval b) < 0)
    (hapos : P.eval a < 0) (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
    ∀ x ∈ Icc a b, 0 < (derivative P).eval x   := by
  intro x hxmem
  refine lt_of_le_of_ne ?_ ?_
  · have : P.eval a < P.eval b  := by nlinarith
    obtain ⟨c, hcmem, hcp⟩ := mean_value_theorem hc hab (P := P)
    refine nonneg_of_ne_zero_of_exists_pos hc (fun y hy => hd y (mem_Icc_of_Ioo hy) ) (hcmem) ?_ x hxmem
    nlinarith
  · symm
    exact hd x hxmem

lemma derivative_mul_neg_of_sign_neg_left (hc : IsRealClosedField F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
      (P.eval a) * (derivative P).eval a < 0 := by
  have hnz : P.eval a ≠ 0 := by
    intro heval
    rw [hur a (by simp[le_of_lt hab]) heval] at hmem
    simp at hmem
  have aux := change_sign_of_unique_root_of_squarefree hc hab hmem hr hur hd
  rcases lt_trichotomy (P.eval a) 0 with hn | hz | hpos
  · nlinarith [sign_derivative_of_opposite_pos hc hab aux hn hd a (by simp[le_of_lt hab])]
  · exfalso ; rw [hz] at aux
    contradiction
  · nlinarith [sign_derivative_of_opposite_sign_neg hc hab aux hpos hd a (by simp[le_of_lt hab])]

lemma derivative_mul_neg_of_sign_neg_right (hc : IsRealClosedField F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) :
      0 < (P.eval b) * (derivative P).eval b := by
  have hnz : P.eval a ≠ 0 := by
    intro heval
    rw [hur a (by simp[le_of_lt hab]) heval] at hmem
    simp at hmem
  have aux := change_sign_of_unique_root_of_squarefree hc hab hmem hr hur hd
  rcases lt_trichotomy (P.eval a) 0 with hn | hz | hpos
  · nlinarith [sign_derivative_of_opposite_pos hc hab aux hn hd b (by simp[le_of_lt hab])]
  · exfalso ; rw [hz] at aux
    contradiction
  · nlinarith [sign_derivative_of_opposite_sign_neg hc hab aux hpos hd b (by simp[le_of_lt hab])]

end IsRealClosedField
