import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Real.CompleteField
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Data.Sign
import Mathlib.Data.List.Destutter

open Polynomial

/- ## Previous work:
* Verifying accuracy of polynomial approximations in HOl -- John Harrison (1997)
* A Formalisation of Sturm’s Theorem -- Manuel Eberl (2014)

* It has also been formalized by NASA researchers in Langley:
  A Formally-Verified Decision Procedure for
  Univariate Polynomial Computation Based on
  Sturm’s Theorem  (2014)

* Assia and Cyril Cohen formalized sign changes of pseudo-remainder sequences
 in Coq over real closed fields. Sturm theorem is a corollary of these results.

-/

/- ## Real Closed Field : definition from nLab
A real closed field `F` is a linearly ordered field such that
*  Every nonnegative element has a square root
*  Every odd degree polynomial with coefficients in `F` has a root in `F`.

This is equivalent to `F` satisfying the intermediate value theorem for polynomial functions.  -/


/- def IsRealClosed (F : Type*) [LinearOrderedField F] : Prop :=
    ∀ {a b : F} ,
    a ≤ b → ∀ {P : F[X]} {t : F},
    (t ∈ Set.Ioo (P.eval a) (P.eval b) ∨ t ∈ Set.Ioo (P.eval b) (P.eval a))
    → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t -/

def IsRealClosed (F : Type*) [LinearOrderedField F] : Prop :=
    ∀ {a b t : F} , ∀ {P : F[X]},
    a ≤ b → t ∈ Set.Ioo (P.eval a) (P.eval b) → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t


/- lemma Real.IsRealClosedField : IsRealClosed ℝ := by
  rintro a b hab P t h
  let f : ℝ → ℝ := fun x => P.eval x
  rcases h with ⟨h1, h2⟩  | ⟨h1', h2'⟩
  exact (Set.mem_image _ _ _).1
    (intermediate_value_Ioo hab (f := f) (Polynomial.continuousOn P ) ⟨h1 , h2⟩)
  exact (Set.mem_image _ _ _).1
    (intermediate_value_Ioo' hab (f := f) (Polynomial.continuousOn P ) ⟨h1' , h2'⟩) -/

lemma Real.IsRealClosedField' : IsRealClosed ℝ := by
  rintro a b t P hab h
  let f : ℝ → ℝ := fun x => P.eval x
  exact (Set.mem_image _ _ _).1
    (intermediate_value_Ioo hab (f := f) (Polynomial.continuousOn P ) h)

namespace IsRealClosedField

variable {F : Type*} [LinearOrderedField F]
open Set

lemma polynomial_has_root_of_le_zero_of_pos (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : P.eval a < 0) (hb : 0 < P.eval b ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  exact hc hab ⟨ha, hb⟩

lemma polynomial_has_root_of_pos_le_zero (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : 0 < P.eval a) (hb : P.eval b < 0 ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b 0 (- P) hab (by simp[ha, hb])
  simp only [eval_neg, neg_eq_zero] at hs2
  exact ⟨s, hs1, hs2 ⟩

lemma intermediate_value_theorem_swap (hc : IsRealClosed F) {a b t : F} (hab : a ≤ b)
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


lemma polynomial_has_root_of_mul_neg (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (habm : (P.eval a) * (P.eval b) < 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rcases lt_trichotomy (P.eval a) 0 with hl1 | hl2 | hl3
  · have : eval b P > 0 := by nlinarith
    exact polynomial_has_root_of_le_zero_of_pos hc hab hl1 this
  · simp[hl2] at habm
  · have : eval b P < 0 := by nlinarith
    exact polynomial_has_root_of_pos_le_zero hc hab hl3 this


lemma polynomial_has_root_of_ne_sign (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (hne : SignType.sign (P.eval a) ≠ SignType.sign (P.eval b)) (hanz : P.eval a ≠ 0)
    (hbnz : P.eval b ≠ 0) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  rw [sign_ne_eq_iff_of_ne_zero (by simp[hanz]) (by simp[hbnz] ), ← sign_mul,
    sign_eq_neg_one_iff] at hne
  exact polynomial_has_root_of_mul_neg hc hab hne


lemma neg_of_ne_zero_of_exists_neg (hc : IsRealClosed F) {a b m : F} {P : F[X]}
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

lemma nonpos_of_ne_zero_of_exists_neg (hc : IsRealClosed F) {a b m : F} {P : F[X]}
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


lemma pos_of_ne_zero_of_exists_pos (hc : IsRealClosed F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Ioo a b , P.eval x > 0 := by
  have := neg_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero, and_imp] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this

lemma nonneg_of_ne_zero_of_exists_pos (hc : IsRealClosed F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Icc a b , P.eval x ≥ 0 := by
  have := nonpos_of_ne_zero_of_exists_neg hc (P := - P)
    (by simp only [eval_neg, ne_eq, neg_eq_zero, and_imp] ; exact hP ) hm (by simp[hpos])
  simp at this ⊢
  exact this


lemma constant_sign_of_ne_zero (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
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

lemma constant_sign_of_ne_zero' (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
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

lemma rolle_theorem_weak (hc : IsRealClosed F) {a b : F} (hab : a < b) {P : F[X]}
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

lemma rolle_theorem_weak' (hc : IsRealClosed F) {a b : F} (hab : a < b) {P : F[X]}
    (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , ((derivative P).eval c = 0 ∨ P.eval c = 0) := by
  by_contra! hcc
  have hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0 := fun x hx => (hcc x hx).2
  obtain ⟨c, hc1, hc2⟩ := rolle_theorem_weak hc hab hP hPa hPb
  exact (hcc c hc1).1 hc2

open Finset

/-- Based on Assia and Cyril paper-/
lemma rolle_theorem_induction (hc : IsRealClosed F) (n : ℕ)
    {a b : F} {P : F[X]} (hab : a < b) (hPa : P.eval a = 0) (hPb : P.eval b = 0)
    (hcard : #((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b)) < n) :
    ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  revert P a b
  induction' n with n hn
  · simp only [Set.mem_Ioo, not_lt_zero', IsEmpty.forall_iff, implies_true]
  · intro a b P hab hPa hPb hcard
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

lemma rolle_theorem (hc : IsRealClosed F) {a b : F} {P : F[X]} (hab : a < b)
    (hPab : P.eval a = P.eval b) : ∃ c ∈ Ioo a b, (derivative P).eval c = 0 := by
  wlog h : P.eval a = 0
  · have := this hc (P := P - C (P.eval a) ) hab
    simp at this
    simp [this, hPab]
  · rw [h] at hPab
    exact rolle_theorem_induction hc
      ((#((Multiset.toFinset P.roots).filter ( fun x => x ∈ Ioo a b))) + 1)
      hab h hPab.symm (lt_add_one _)

theorem mean_value_theorem  (hc : IsRealClosed F) {a b : F} {P : F[X]} (hab : a < b) :
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

lemma change_sign_of_unique_root_of_squarefree (hc : IsRealClosed F) {a b c : F}
    {P : F[X]} (hab : a < b) (hmem : c ∈ Ioo a b) (hr : P.eval c = 0)
    (hur : ∀ x ∈ Icc a b , (P.eval x = 0 → x = c))
    (hd : ∀ x ∈ Icc a b, (derivative P).eval x ≠ 0) : (P.eval a) * (P.eval b) < 0 := by
  by_contra! hcc
  rcases le_iff_eq_or_lt.1 hcc with hz | hpos
  · simp at hz
    rcases hz with ha | hb
    · rw [hur a (Set.left_mem_Icc.2 (le_of_lt hab)) ha, Set.left_mem_Ioo] at hmem
      exact hmem
    · rw [hur b (Set.right_mem_Icc.2 (le_of_lt hab)) hb, Set.right_mem_Ioo] at hmem
      exact hmem
  · rcases mul_pos_iff.1 hpos with hpos1 | hpos2
    · by_cases hleq : eval a P < eval b P
      · rw [← hr] at hpos1
        obtain ⟨s, hsmem, hs⟩  := hc (le_of_lt hmem.2) ⟨hpos1.1, hleq⟩
        obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hmem.1 hsmem.1) hs.symm
        refine hd t ?_ htmem2
        exact ⟨le_of_lt htmem.1, le_of_lt (lt_trans htmem.2 hsmem.2) ⟩
      · push_neg at hleq
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
      · push_neg at hleq
        rcases le_iff_eq_or_lt.1 hleq with hz2 | hpos'
        · obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc hab hz2.symm
          refine hd t ?_ htmem2
          exact mem_Icc_of_Ioo htmem
        · rw [← hr] at hpos2
          obtain ⟨s, hsmem, hs⟩  := intermediate_value_theorem_swap hc (le_of_lt hmem.2) ⟨hpos', hpos2.1⟩
          obtain ⟨t, htmem, htmem2⟩ := rolle_theorem hc (lt_trans hmem.1 hsmem.1 ) hs.symm
          refine hd t ?_ htmem2
          exact ⟨le_of_lt htmem.1, le_of_lt (lt_trans htmem.2 hsmem.2) ⟩

lemma sign_derivative_of_opposite_sign_neg (hc : IsRealClosed F) {a b : F}
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

lemma sign_derivative_of_opposite_pos (hc : IsRealClosed F) {a b : F}
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


lemma derivative_mul_neg_of_sign_neg_left (hc : IsRealClosed F) {a b : F}
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

lemma derivative_mul_neg_of_sign_neg_right (hc : IsRealClosed F) {a b : F}
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







      /- refine mul_neg_of_pos_of_neg (mul_pos ?_ ?_) ?_
      · rw [Nat.cast_pos]
        exact Nat.pos_of_ne_zero hbm
      · linarith
      · specialize hqal b (by linarith)
        simp[hQr.2]-/











    --norm_num
    --simp[Nat.succ_pred_eq_of_ne_zero ham, Nat.succ_pred_eq_of_ne_zero hbm]





  --Polynomial.rootMultiplicity_pos
  --rw [hQ1] at hQ'1

section signChanges

section

variable {R : Type*}  [LinearOrderedRing R]
/-- The number of sign changes in a nonempty sequence `[a₀, a₁, …, aₙ]`. This is
computed as `∑ i, σ(aᵢ * aᵢ₊₁)`, where `σ x` is `1` if `x < 0` and `0` otherwise.  -/
/- def signChanges {n : ℕ} (f : Fin (n + 1) → R) :=
  ∑ (i : Fin n),
  (fun x => if x = -1 then 1 else 0)
  (SignType.sign (f (Fin.castSucc i)) * SignType.sign (f (Fin.castSucc i + 1))) -/

-- Similar to definition in Isabelle by Manuel Eberl
def signChangesList (L : List R) : ℕ :=
  List.length
  (List.destutter (fun a b => a ≠ b)
  (List.filter (fun x => if x ≠ 0 then true else false) (List.map SignType.sign L))) - 1


-- Similar to Coq (residue sequences)
def signChanges' (L : List R) : ℕ :=
  match L  with
  | [] => 0
  | (a :: as) => if SignType.sign a * SignType.sign (as.headD 0) < 0 then 1 + signChanges' as else signChanges' as

def signChanges (L : List R) : ℕ  :=
  signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L)


lemma signChanges_def (L : List R) : signChanges L = signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L) := by
  rfl

lemma signChanges_eq_signChanges' (L : List R) (hz : ∀ x ∈ L, x ≠ 0) : signChanges L = signChanges' L := by
  rw [signChanges_def]
  congr ; simp ; exact hz

#eval signChangesList [1,0, 0, -2,3,-1,-3,4,5,6,-7, -1,-1,4,5,-1,0,0,0,-2,3]
#eval signChanges [1,0, 0, -2,3,-1,-3,4,5,6,-7, -1,-1,4,5,-1,0,0,0,-2,3]

open SignType

/- The sign changes of a polynomial sequence at `a` is simply the sign changes of the resulting
list when evaluating the polys at `a` -/
def signChangesPolySeq (P : List R[X]) (a : R) : ℕ :=
  signChanges (List.map (fun x => x.eval a) P)

lemma signChangesPolySeq_def (P : List R[X]) (a : R) :
  signChangesPolySeq P a = signChanges (List.map (fun x => x.eval a) P) := rfl

end

section


variable [LinearOrderedCommRing R]
/-- A list of polynomials is a sturm sequence starting with `p` and `q`
  if it has length at least two, it ends in a non-zero constant polynomial, it has strictly decreasing degree
  and `Pᵢ₊₁ ∣ (e₁ * Pᵢ + fᵢ * Pᵢ₊₂)` with `eᵢ` and `f₁` strictly positive numbers. -/
structure IsSturmSequence (P : List R[X]) (p q : R[X])  where
  hlen : 2 ≤ P.length
  h0 : P[0] = p
  h1 : P[1] = q
  hc : ∃ c : R, c ≠ 0 ∧ P.getLastD 0 = C c
  hmono : ∀ i, ∀ h : i + 1 < P.length , P[i + 1].natDegree < P[i].natDegree
  hrem : ∀ i, ∀ h2 : i + 2 < P.length ,
    (∃ e f : R, ∃ Q : R[X], 0 < e ∧ 0 < f ∧ C e * P[i] = Q * P[i + 1] - C f * P[i + 2] )


lemma sturm_sequence_ne_nil (P : List R[X]) (p q : R[X])
  (hs : IsSturmSequence P p q) : P ≠ [] := by
  have := hs.hlen
  intro h
  simp [h] at this

lemma getLastD_eq_getLast_of_ne_nil {α : Type*} {a : α} {l : List α} (h : l ≠ []) :
  l.getLastD a = l.getLast h := by
  match l with
  | [] => contradiction
  | (b :: bs) =>
    match bs with
    | [] => simp
    | (c :: cs) =>
    rw [List.getLast_eq_getLastD, List.getLastD_cons]

/-- The zero polynomial is not in a sturm sequence. -/
lemma zero_not_member {P : List R[X]} {p q : R[X]}
    (hs : IsSturmSequence P p q) : ¬ 0 ∈ P := by
  intro h
  rw [List.mem_iff_getElem] at h
  obtain ⟨i, hile, hi⟩ := h
  by_cases hieq : i = P.length - 1
  · simp_rw [hieq] at hi
    have hsl := hs.hlen
    obtain ⟨c, hcz, hzl⟩ := hs.hc
    rw [← List.getLast_eq_getElem _ (fun  h => by simp [h] at hsl)] at hi
    rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil P p q hs), hi, Eq.comm,
      Polynomial.C_eq_zero] at hzl
    exact hcz hzl
  · have := hs.hmono i (by omega)
    rw [hi] at this
    simp at this


lemma no_consecutive_zero1 (P : List R[X]) (p q : R[X])
    (hs : IsSturmSequence P p q) (a : R) (i : ℕ)
    (hlen : i + 1 < P.length) (hz : P[i + 1].eval a = 0) : P[i].eval a ≠ 0 := by
  revert i
  by_contra! hc
  obtain ⟨i, hle, heval1, heval2⟩ := hc
  have hin : ∀ j, ∀ hj : i + j < P.length , P[i + j].eval a = 0 := by
    intro j hj
    induction' j using Nat.strong_induction_on with j hjin
    match j with
    | 0 => exact heval2
    | 1 => exact heval1
    | j + 1 + 1 =>
    have := hjin j (by omega) (by omega)
    have :=  hjin (j + 1) (by omega) (by omega)
    obtain ⟨e, f, Q, hepos, hfpos, hef⟩ := hs.hrem (i + j) (by omega)
    apply_fun (fun (x : R[X]) => x.eval a) at hef
    simp at hef
    simp_rw [ hjin j (by omega) (by omega), add_assoc, hjin (j + 1) (by omega) (by omega)  ] at hef
    simp[Ne.symm (ne_of_lt hfpos)] at hef
    exact hef
  obtain ⟨c, hcz, hzl⟩ := hs.hc
  rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil P p q hs), List.getLast_eq_getElem] at hzl
  have aux := hin (P.length- 1 - i) (by omega)
  have : i + (P.length - 1 - i) = P.length - 1 := by omega
  simp_rw [this, hzl] at aux
  simp only [eval_C] at aux
  exact hcz aux


lemma sturm_sequence_cons (P : List R[X]) (p q : R[X]) (a : R[X]) (hPl : 2 ≤ P.length)
    (hs : IsSturmSequence (a :: P) p q) : IsSturmSequence P q P[1] where
  hlen := hPl
  h0 := by rw [← List.getElem_cons_succ a ] ; exact hs.h1
  h1 := rfl
  hc := by
    have : P ≠ [] := fun h => by rw [h] at hPl ; simp at hPl
    obtain ⟨c, neq, hcl⟩  := hs.hc
    rw [List.getLastD_cons, getLastD_eq_getLast_of_ne_nil this] at hcl
    simp_rw [getLastD_eq_getLast_of_ne_nil this]
    exact ⟨c, neq, hcl⟩
  hmono := by
    intro i h
    have := hs.hmono (i + 1) (by simp ; omega)
    simp at this
    exact this
  hrem := by
    intro i h
    obtain ⟨e, f, Q, hepos, hfpos, heq⟩  := hs.hrem (i + 1) (by simp ; omega)
    simp at heq
    exact ⟨e, f, Q, hepos, hfpos, heq⟩



--lemma signChangesPolySeq_getLastD (P : List R[X]) (p q : R[X])
--    (hs : IsSturmSequence P p q) (a : R) : (signChangesPolySeq P a).getLastD  ≠ 0

end

open SignType

variable {R : Type*}  [LinearOrderedRing R]


@[simp]
lemma signChanges_nil : signChanges (R := R) [] = 0 := rfl


@[simp]
lemma signChanges_single' (a : R) : signChanges' [a] = 0 := by
  simp[signChanges']

@[simp]
lemma signChanges_single (a : R) : signChanges [a] = 0 := by
  by_cases ha : a ≠ 0
  · simp[signChanges, signChanges', ha]
  · push_neg at ha
    simp [signChanges, signChanges', ha]


lemma signChanges_zero_head (as : List R) : signChanges (0 :: as) = signChanges as := by
  unfold signChanges
  simp

lemma signChanges_zero_head' (as : List R) : signChanges' (0 :: as) = signChanges' as := by
  simp_rw [signChanges', sign_zero, zero_mul]
  rfl

lemma signChanges_length_two (a b : R) (hab : a * b < 0) : signChanges [a, b] = 1 := by
  have : a ≠ 0 ∧ b ≠ 0 := by
    by_contra! hc
    by_cases haz : a = 0
    · simp [haz] at hab
    · simp [hc haz] at hab
  rw [signChanges_eq_signChanges']
  simp [signChanges']
  simp [← sign_mul, hab]
  simp[this]

lemma signChanges_cons_eq_add' (a b : R) (as : List R) :
  signChanges' (a :: b :: as) = signChanges' [a, b] + signChanges' (b :: as) := by
by_cases hc : sign a * sign b = -1
· simp [signChanges', hc]
· simp [signChanges', hc]

lemma signChanges_cons_eq_add (a b : R) (as : List R) (hb : b ≠ 0) :
  signChanges (a :: b :: as) = signChanges [a, b] + signChanges (b :: as) := by
have aux : ∀ x y : R, ∀ L : List R,  x :: y :: L = [x, y] ++ L := by simp
by_cases ha : a ≠ 0
· have aux2 : (List.filter (fun x ↦ if x ≠ 0 then true else false) [a, b]) = [a, b] := by
    simp[ha, hb]
  unfold signChanges
  rw [aux, List.filter_append, aux2, ← aux, signChanges_cons_eq_add']
  congr ; simp [hb]
· push_neg at ha
  rw [ha]
  simp[signChanges_zero_head, signChanges_single]


lemma signChanges_modify_zero (a : R) (bs : List R) :
  signChanges (a :: 0 :: bs) = signChanges (a :: bs) := by
  by_cases ha : a = 0
  · rw [ha, signChanges_zero_head]
  · have aux : (List.filter (fun x => if x ≠ 0 then true else false)) (a :: 0 :: bs) =
      a :: (List.filter (fun x => if x ≠ 0 then true else false) bs) := by
      simp only [ne_eq, ite_not, Bool.if_true_right, Bool.or_false, ha, decide_false,
        Bool.not_false, List.filter_cons_of_pos, decide_true, Bool.not_true, Bool.false_eq_true,
        not_false_eq_true, List.filter_cons_of_neg]
    simp_rw [signChanges, aux]
    simp[ha]

lemma signChanges_cons {a : R} {as : List R} (ha : a ≠ 0) (hh : as.headD 0 ≠ 0) :
  signChanges (a :: as) = if sign a * sign (as.headD 0) < 0 then 1 + signChanges as else signChanges as := by
  have aux : (List.filter (fun x => if x ≠ 0 then true else false)) (a :: as) =
      a :: (List.filter (fun x => if x ≠ 0 then true else false) as) := by
    simp[ha]
  have aux2 : (List.filter (fun x => if x ≠ 0 then true else false) as).headD 0 = as.headD 0 := by
    match as with
    | [] => simp
    | (b :: bs) =>
    simp at hh
    simp[hh]
  unfold signChanges
  rw [aux]
  nth_rw 1 [signChanges']
  simp_rw [aux2]

lemma signChanges_map' {S : Type*} [LinearOrderedRing S] (f : R → S)
    (hmono1 : ∀ a , 0 < a ↔ 0 < f a ) (hmono2 : ∀ a , a < 0 ↔ f a < 0 ) (L : List R) :
    signChanges' L = signChanges' (L.map f) := by
induction' L with a as hi
· rfl
· match as with
  | [] => simp [signChanges']
  | (b :: bs) =>
  simp
  by_cases ha : sign a * sign b = -1
  · have hac := ha
    have ha : sign (f a) * sign (f b) = -1 := by
       rw [← sign_mul, sign_eq_neg_one_iff, mul_neg_iff] at ha ⊢
       rw [hmono1, hmono1, hmono2, hmono2] at ha
       exact ha
    unfold signChanges'
    simp [ha, hac]
    simp[hi]
  · have hac := ha
    have ha : ¬ sign (f a) * sign (f b) = -1 := by
      rw [← sign_mul, sign_eq_neg_one_iff, mul_neg_iff] at ha ⊢
      rw [hmono1, hmono1, hmono2, hmono2] at ha
      exact ha
    unfold signChanges'
    simp [ha, hac]
    simp[hi]

lemma signChanges_map {S : Type*} [LinearOrderedRing S] (f : R → S)
  (hmono1 : ∀ a , 0 < a ↔ 0 < f a ) (hmono2 : ∀ a , a < 0 ↔ f a < 0 )
  (L : List R) :
  signChanges L = signChanges (L.map f) := by
  have : ∀ x , f x = 0 ↔ x = 0 := by
    intro x
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h1 | h2 | h3
      · have := (hmono2 x).1 h1 ; simp [hx] at this
      · exact h2
      · have := (hmono1 x).1 h3 ; simp [hx] at this
    · rintro rfl
      rcases lt_trichotomy (f 0) 0 with h1 | h2 | h3
      · have := (hmono2 0).2 h1
        simp at this
      · exact h2
      · have := (hmono1 0).2 h3
        simp at this
  unfold signChanges
  rw [List.filter_map]
  have : (List.filter ((fun x ↦ if x ≠ 0 then true else false) ∘ f) L) =
    List.filter (fun x ↦ if x ≠ 0 then true else false) L := by
    apply List.filter_congr
    intro x hL
    simp[this x]
  rw [this]
  apply signChanges_map' f hmono1 hmono2


lemma signChanges_eq_map_sign_int (L : List R) :
  signChanges L = signChanges (L.map (fun x ↦ (sign x : ℤ))) := by
  apply signChanges_map _ ?_ ?_ _
  · intro a
    rw [← sign_eq_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp
  · intro a
    rw [← sign_eq_neg_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp

lemma signChanges_eq_map_sign_int' (L : List R) :
  signChanges' L = signChanges' (L.map (fun x ↦ (sign x : ℤ))) := by
  apply signChanges_map' _ ?_ ?_ _
  · intro a
    rw [← sign_eq_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp
  · intro a
    rw [← sign_eq_neg_one_iff]
    constructor
    · intro h ; simp [h]
    · cases sign a  <;> simp

lemma signChanges_congr (L₁ L₂ : List R)
  (hlen : L₁.length = L₂.length)
  (hi : ∀ i, ∀ hi : i < L₁.length, sign (L₁[i]) = sign (L₂[i]) ) :
  signChanges L₁ = signChanges L₂ := by
  refine Eq.trans (b := signChanges (L₁.map (fun x ↦ (sign x : ℤ)))) ?_ ?_
  · exact signChanges_eq_map_sign_int L₁
  · rw [signChanges_eq_map_sign_int L₂]
    congr 1
    refine List.ext_get ?_ ?_
    · simp[hlen]
    · intro i hi1 hi2
      simp at hi1 hi2 ⊢
      rw [hi]

lemma signChanges_congr' (L₁ L₂ : List R)
  (hlen : L₁.length = L₂.length)
  (hi : ∀ i, ∀ hi : i < L₁.length, sign (L₁[i]) = sign (L₂[i]) ) :
  signChanges' L₁ = signChanges' L₂ := by
  refine Eq.trans (b := signChanges' (L₁.map (fun x ↦ (sign x : ℤ)))) ?_ ?_
  · exact signChanges_eq_map_sign_int' L₁
  · rw [signChanges_eq_map_sign_int' L₂]
    congr 1
    refine List.ext_get ?_ ?_
    · simp[hlen]
    · intro i hi1 hi2
      simp at hi1 hi2 ⊢
      rw [hi]

lemma sign_changes_add (as bs : List R) (b : R) :
  signChanges' (as ++ (b :: bs) ) = signChanges' (as ++ [b]) + signChanges' (b :: bs) := by
  induction' as with c cs hi
  · simp[signChanges']
  · match cs with
    | [] =>
    simp [signChanges_cons_eq_add' c b bs]
    | (d :: ds) =>
    by_cases hc : sign c * sign d = -1
    · conv => left ; unfold signChanges' ; simp[hc]
      conv =>  right ; left ; unfold signChanges' ; simp[hc]
      rw [add_assoc, add_right_inj]
      simp at hi
      exact hi
    · conv => left ; unfold signChanges' ; simp[hc]
      conv =>  right ; left ; unfold signChanges' ; simp[hc]
      simp at hi
      exact hi

lemma sign_changes_add_triple (a b c : R) (as : List R) :
  signChanges' (a :: b :: c :: as) = signChanges' [a, b, c] + signChanges' (c :: as) := by
  exact sign_changes_add [a, b] as c

-- to do the induction
-- the correct should be? If the signs are not the same, then either we are at the
-- head or inside and the sides have opposite sign.

-- Consider (a :: b :: c :: cs) and split according to if c has the same sign in the
-- two lists. If yes, then you can apply induction hypothesis to (c :: cs). If not,
-- then use (b :: c :: cs) since b is forced to have same sign.

lemma List.getElem_cons_pred {α : Type* } (a : α) (as : List α) (i : ℕ) (h : i  < (a :: as).length)
  (hi' : i - 1 < as.length) (hi : i ≠ 0) : (a :: as)[i] = as[i - 1] := by
  match i with
  | 0 => contradiction
  | i + 1 => simp


lemma signChanges_of_mul_neg {a b c : R}
    (ha : a * c < 0) : signChanges [a, b, c] = 1 := by
    rcases lt_trichotomy b 0 with hb1 | hb2 | hb3
    swap
    · rw [hb2, signChanges_modify_zero, signChanges_length_two _ _ ha]
    · rw [mul_neg_iff] at ha
      rcases ha with hapos | haneg
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', hapos.1, hb1, hapos.2]
        aesop
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', haneg.1, hb1, haneg.2]
        aesop
    · rw [mul_neg_iff] at ha
      rcases ha with hapos | haneg
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', hapos.1, hb3, hapos.2]
        simp ; aesop
      · rw [signChanges_eq_signChanges']
        unfold signChanges'
        simp [signChanges', haneg.1, hb3, haneg.2]
        aesop


lemma aux_induction_three_base (a1 a2 a3 b1 b2 b3 : R)
    (hin : sign a1 = sign b1) (hlast : sign a3 = sign b3)
    (hi : sign a2 ≠ sign b2 → a1 * a3 < 0 ∧ sign a1 = sign b1 ∧ sign a3 = sign b3) :
  signChanges [a1, a2, a3] = signChanges [b1, b2, b3] := by
  by_cases heq : sign a2 ≠ sign b2
  · have := (hi heq)
    have aux : b1 * b3 < 0 := by
      rw [← sign_eq_neg_one_iff, sign_mul, ← this.2.1, ← this.2.2, ← sign_mul ]
      simp[this.1]
    rw [signChanges_of_mul_neg this.1, signChanges_of_mul_neg aux]
  · push_neg at heq
    apply signChanges_congr
    · intro i hii
      simp at hii
      interval_cases i
      · exact hin
      · exact heq
      · exact hlast
    · rfl

lemma List.three_le_length_iff {α : Type*} {l : List α} :  3 ≤ l.length ↔ ∃ (a b c : α), ∃ (as : List α) ,
  l = (a :: b :: c :: as) := by
  constructor
  · intro hlen
    match l with
    | [] => simp at hlen
    | [a] => simp at hlen
    | [a, b] => simp at hlen
    | (a :: b :: c :: as) =>
    use a , b, c, as
  · rintro ⟨a, b, c, as, has⟩
    simp [has]


/-- If I just case match, the proof is too slow. -/
lemma aux_induction_list_opposite_sign {n : ℕ}(L₁ L₂ : List R)
  (hzL1 : ∀ x ∈ L₁, x ≠ 0) (hzL2 : ∀ x ∈ L₂, x ≠ 0)
  (hlenn : L₁.length = n)
  (hlen : L₁.length = L₂.length) (hlast : sign (L₁.getLastD 0) = sign (L₂.getLastD 0))
  (hi : ∀ i , ∀ hi : i + 1 < L₁.length , sign (L₁[i]) ≠ sign (L₂[i]) →
    (1 ≤ i ∧ L₁[i - 1] * L₁[i + 1] < 0 ∧ sign (L₁[i - 1]) = sign (L₂[i - 1]) ∧ sign (L₁[i + 1]) = sign (L₂[i + 1]))) :
    signChanges L₁ = signChanges L₂ := by
  rw [signChanges_eq_signChanges' _ hzL2 , signChanges_eq_signChanges' _ hzL1]
  revert L₁ L₂
  induction' n using Nat.strong_induction_on with n hn
  · by_cases hnz : n < 1
    · simp at hnz
      intro L₁ L₂ hzL1 hzL2 hlenn hlen hlast hi
      rw [hnz] at hlenn
      rw [hlenn] at hlen
      rw [List.length_eq_zero.1 hlenn, List.length_eq_zero.1 hlen.symm]
    · intro L₁ L₂ hzL1 hzL2 hlenn hlen hlast hi
      have hszero : sign (L₁[0]) = sign (L₂[0]) := by
        rcases lt_trichotomy L₁.length 1 with hl0 | hl1 | hl2
        · linarith
        · rw [hl1, Eq.comm] at hlen
          rw [List.length_eq_one] at hlen hl1
          obtain ⟨a, ha⟩ := hl1
          obtain ⟨b, hb⟩ := hlen
          simp [ha, hb] at hlast ⊢
          exact hlast
        · by_contra hcc
          linarith [(hi 0 (by linarith) hcc).1]
      by_cases ht : 3 ≤ n
      · obtain ⟨a1, a2,a3, as, has ⟩:= List.three_le_length_iff.1 (le_of_le_of_eq ht hlenn.symm)
        obtain ⟨b1, b2,b3, bs, hbs ⟩:= List.three_le_length_iff.1 (le_of_le_of_eq ht (Eq.trans hlenn.symm hlen))
        simp_rw [has] at hlenn hlen hlast hi hszero hzL1 ⊢
        simp_rw [hbs] at hlenn hlen hlast hi hszero hzL2 ⊢
        by_cases han : as = []
        · have hbn : bs = [] := by rw [han] at hlen ; simp at hlen ; exact hlen
          simp_rw [han, hbn] at hi hlast ⊢
          simp at hlast
          rw [← signChanges_eq_signChanges', ← signChanges_eq_signChanges']
          apply aux_induction_three_base
          · simp at hszero ; exact hszero
          · exact hlast
          · have := hi 1 (by simp)
            simp at this ; exact this
          · simp[hzL2]
          · simp[hzL1]
        · by_cases hseq : sign a3 = sign b3
          · rw [sign_changes_add_triple, sign_changes_add_triple b1]
            rw [hn (n - 2) (by omega) (a3 :: as) (b3 :: bs) ?_ ?_ ?_ ]
            · congr 1
              rw [← signChanges_eq_signChanges', ← signChanges_eq_signChanges']
              apply aux_induction_three_base
              · exact hszero
              · exact hseq
              · intro hneq
                have := hi 1 (by simp) hneq
                simp at this
                exact this
              simp [hzL2] ; simp [hzL1]
            · simp at hlen ; simp [hlen]
            · exact hlast
            · intro i hii hns
              have higt : 1 ≤ i := by
                by_contra! hcc
                simp [Nat.lt_one_iff.1 hcc, hseq] at hns
              constructor
              · exact higt
              · specialize hi (i + 2) (by simp at hii ⊢ ; exact hii) hns
                simp at hi ; simp[hii]
                rw [List.getElem_cons_pred, List.getElem_cons_pred b2] at hi
                exact hi ; exact Nat.not_eq_zero_of_lt higt ;  exact Nat.not_eq_zero_of_lt higt
            · simp at hzL1
              simp [hzL1] ; exact hzL1.2.2.2
            · simp at hzL2 ; simp [hzL2] ; exact hzL2.2.2.2
            · simp at hlenn ; simp ; omega
          · have has2 : sign (a2) = sign (b2) := by
              have := hi 2 (by simp ; exact List.length_pos.mpr han) hseq
              simp at this
              rw[this.2.1]
            rw [signChanges_cons_eq_add', signChanges_cons_eq_add' b1]
            rw [hn (n - 1) (by omega) (a2 :: a3 :: as) (b2 :: b3 :: bs) ?_ ?_ ?_ ]
            · congr 1
              rw [signChanges_congr']
              · rfl
              · intro i hii ; simp at hii
                interval_cases i
                exact hszero ; exact has2
            · simp at hlen ⊢ ; exact hlen
            · simp at hlast ⊢ ; exact hlast
            · intro i hii hns
              have higt : 1 ≤ i := by
                by_contra! hcc
                simp [Nat.lt_one_iff.1 hcc, hseq] at hns
                exact hns has2
              constructor
              · exact higt
              · specialize hi (i + 1) (by simp at hii ⊢ ; exact hii) hns
                simp at hi ; simp[hii]
                rw [List.getElem_cons_pred, List.getElem_cons_pred b1] at hi
                exact hi ; exact Nat.not_eq_zero_of_lt higt ; exact Nat.not_eq_zero_of_lt higt
            · simp at hzL1 ; simp [hzL1] ; exact hzL1.2.2.2
            · simp at hzL2 ; simp [hzL2] ; exact hzL2.2.2.2
            · simp at hlenn ; simp ; omega
      · push_neg at ht hnz
        interval_cases n
        · obtain ⟨a, ha⟩ := List.length_eq_one.1 hlenn
          obtain ⟨b, hb⟩ := List.length_eq_one.1 (Eq.trans hlen.symm hlenn)
          rw [ha, hb, signChanges_single', signChanges_single']
        · obtain ⟨a1, a2, ha⟩ := List.length_eq_two.1 hlenn
          obtain ⟨b1, b2, hb⟩ := List.length_eq_two.1 (Eq.trans hlen.symm hlenn)
          simp_rw [ha, hb] at hszero hlast hzL1 hzL2 ⊢
          rw [signChanges_congr']
          · rfl
          · intro i hii
            simp at hii
            interval_cases i
            exact hszero
            exact hlast


lemma signChanges_eq_of_lists_opposite_sign (L₁ L₂ : List R)
  (hzL1 : ∀ x ∈ L₁, x ≠ 0) (hzL2 : ∀ x ∈ L₂, x ≠ 0)
  (hlen : L₁.length = L₂.length) (hlast : sign (L₁.getLastD 0) = sign (L₂.getLastD 0))
  (hi : ∀ i , ∀ hi : i + 1 < L₁.length , sign (L₁[i]) ≠ sign (L₂[i]) →
    (1 ≤ i ∧ L₁[i - 1] * L₁[i + 1] < 0 ∧ sign (L₁[i - 1]) = sign (L₂[i - 1]) ∧ sign (L₁[i + 1]) = sign (L₂[i + 1]))) :
    signChanges L₁ = signChanges L₂ := by
  exact aux_induction_list_opposite_sign L₁ L₂ hzL1 hzL2 rfl hlen hlast hi


variable (F : Type*) [LinearOrderedField F]

open Set IsRealClosedField

lemma polynomial_change_sign_aux (hc : IsRealClosed F) {a b e f : F} (P0 P1 P2 Q : F[X])
  (hab : a < b) (hpose : 0 < e ) (hposf : 0 < f) (heq : C e * P0 = Q * P1 - C f * P2)
  (hz0 : ∀ x ∈ Icc a b , P0.eval x ≠ 0) (hz2 : ∀ x ∈ Icc a b , P2.eval x ≠ 0)
  (hP1a : P1.eval a ≠ 0) (hP1b : P1.eval b ≠ 0) (hneq : sign (P1.eval a) ≠ sign (P1.eval b)) :
    (P0.eval a) * (P2.eval a) < 0 ∧ sign (P0.eval a) = sign (P0.eval b) ∧
    sign (P2.eval a) = sign (P2.eval b) := by
  have : (P1.eval a) * (P1.eval b) < 0 := by
    rw [← sign_eq_neg_one_iff, sign_mul, ← sign_ne_eq_iff_of_ne_zero (sign_ne_zero.mpr hP1a) (sign_ne_zero.mpr hP1b )]
    exact hneq
  obtain ⟨r, hrmem, hrr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) this
  constructor
  · have aux2 : e * P0.eval r = - f * P2.eval r := by
      rw [← eval_C (x := r) (a := e), ← eval_mul, heq]
      simp[hrr]
    have aux3 : (P0.eval r) * (P2.eval r) < 0 := by
      rw [← mul_lt_mul_left hpose, ← mul_assoc, aux2]
      simp
      rw [mul_assoc, mul_pos_iff_of_pos_left hposf]
      simp[hz2 _ (mem_Icc_of_Ioo hrmem)]
    refine lt_of_le_of_ne ?_ ?_
    · rw [← eval_mul]
      apply nonpos_of_ne_zero_of_exists_neg hc (P := P0 * P2) ?_ hrmem
      · rw [eval_mul]
        exact aux3
      · simp [le_of_lt hab]
      · simp only [eval_mul, ne_eq, mul_eq_zero, not_or, and_imp]
        intro x hxmem
        exact ⟨hz0 x (mem_Icc_of_Ioo hxmem), hz2 x (mem_Icc_of_Ioo hxmem)⟩
    · simp
      exact ⟨hz0 a (by simp ; exact le_of_lt hab), hz2 a (by simp ; exact le_of_lt hab)⟩
  · constructor
    · by_contra! hcc
      rw [sign_ne_eq_iff_of_ne_zero, ← sign_mul, sign_eq_neg_one_iff] at hcc
      obtain ⟨c, hcmem, hcr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hcc
      exact hz0 c (mem_Icc_of_Ioo hcmem) hcr
      simp [hz0 a (by simp ; exact le_of_lt hab)]
      simp [hz0 b (by simp ; exact le_of_lt hab)]
    · by_contra! hcc
      rw [sign_ne_eq_iff_of_ne_zero, ← sign_mul, sign_eq_neg_one_iff] at hcc
      obtain ⟨c, hcmem, hcr⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hcc
      exact hz2 c (mem_Icc_of_Ioo hcmem) hcr
      simp [hz2 a (by simp ; exact le_of_lt hab)]
      simp [hz2 b (by simp ; exact le_of_lt hab)]


lemma sturm_sequence_unique_root_ne_p (hc : IsRealClosed F) (a b : F) (hab : a < b)
   (P : List F[X]) (p q : F[X]) (hs : IsSturmSequence P p q) (c : F) (hcmem : c ∈ Ioo a b)
   (hpnr : p.eval c ≠ 0) (hr : ∀ x ∈ Icc a b,  ∀ i , ∀ h : i < P.length , P[i].eval x = 0 → x = c) :
    signChangesPolySeq P a = signChangesPolySeq P b := by
  have hevala : ∀ i, ∀ h : i < P.length, P[i].eval a ≠ 0 := by
    intro i hi haeval
    rw [← hr a (by simp [le_of_lt hab]) i hi haeval ] at hcmem
    simp at hcmem
  have hevalb : ∀ i, ∀ h : i < P.length, P[i].eval b ≠ 0 := by
    intro i hi hbeval
    rw [← hr b (by simp [le_of_lt hab]) i hi hbeval] at hcmem
    simp at hcmem
  have hlgt := hs.hlen
  have hanenil : (List.map (fun x => x.eval a) P) ≠ [] := by
    simp [sturm_sequence_ne_nil P p q hs]
  have hbnenil : (List.map (fun x => x.eval b) P) ≠ [] := by
    simp [sturm_sequence_ne_nil P p q hs]
  apply signChanges_eq_of_lists_opposite_sign
  · simp_rw [List.mem_iff_getElem]
    simp only [List.getElem_map, List.length_map, ne_eq, forall_exists_index]
    exact fun x i h heq  => by rw[← heq] ; exact hevala i h
  · simp_rw [List.mem_iff_getElem]
    simp only [List.getElem_map, List.length_map, ne_eq, forall_exists_index]
    exact fun x i h heq  => by rw[← heq] ; exact hevalb i h
  · obtain ⟨c, hcnz, hcl⟩ := hs.hc
    rw [getLastD_eq_getLast_of_ne_nil hanenil, getLastD_eq_getLast_of_ne_nil hbnenil,
      List.getLast_map, List.getLast_map]
    rw [getLastD_eq_getLast_of_ne_nil (sturm_sequence_ne_nil P p q hs)] at hcl
    rw [hcl]
    simp
  · simp only [List.length_map, List.getElem_map, ne_eq]
    intro i hi hsneq
    have higt : 1 ≤ i := by
      by_contra! hiz
      simp at hiz
      simp_rw [hiz, hs.h0] at hsneq
      rw [← ne_eq, sign_ne_eq_iff_of_ne_zero ?_ ?_, ← sign_mul, sign_eq_neg_one_iff] at hsneq
      obtain ⟨s, hsmem, hs'⟩ := polynomial_has_root_of_mul_neg hc (le_of_lt hab) hsneq
      rw [← hr s (Set.mem_Icc_of_Ioo hsmem ) 0 (by omega) (by simp_rw [hs.h0] ; exact hs') ] at hpnr
      exact hpnr hs'
      · simp only [ne_eq, sign_eq_zero_iff]
        convert hevala 0 (by omega)
        exact (hs.h0).symm
      · simp only [ne_eq, sign_eq_zero_iff]
        convert hevalb 0 (by omega)
        exact (hs.h0).symm
    constructor
    · exact higt
    · obtain ⟨r, hrmem, hrr⟩ := polynomial_has_root_of_ne_sign hc (le_of_lt hab)
        hsneq (hevala i (by omega)) ((hevalb i (by omega)))
      have hreqc := hr r (mem_Icc_of_Ioo hrmem) i (by omega) hrr
      rw [hreqc] at hrr
      obtain ⟨e, f, Q, hepos, hfpos, hdvd⟩ := hs.hrem (i - 1) (by omega)
      have aux : i - 1 + 2 = i + 1 := by omega
      have := polynomial_change_sign_aux F hc _ _ _  Q hab hepos hfpos hdvd
      simp_rw [Nat.sub_add_cancel higt, aux] at this
      apply this
      · intro x hxmem heval
        have aux2 := hr x hxmem (i - 1) (by omega) heval
        rw [aux2] at heval
        exact no_consecutive_zero1 P p q hs c (i - 1) (by omega)
          (by simp[Nat.sub_add_cancel higt, hrr]) heval
      · intro x hxmem heval
        have aux2 := hr x hxmem (i + 1) (by omega) heval
        rw [aux2] at heval
        exact no_consecutive_zero1 P p q hs c i (by omega) heval hrr
      · exact hevala i (by omega)
      · exact hevalb i (by omega)
      · exact hsneq
  · simp

lemma signChanges_derivative  (hc : IsRealClosed F) {a b : F} (hab : a < b) (p : F[X])
  {c : F} (hcmem : c ∈ Ioo a b) (hpr : p.eval c = 0) (hdc : (derivative p).eval c ≠ 0)
  (hr : ∀ x ∈ Icc a b, ∀ i , ∀ h : i < [p, derivative p].length , [p, derivative p][i].eval x = 0 → x = c) :
  signChangesPolySeq [p, derivative p] a = signChangesPolySeq [p, derivative p] b + 1 := by
  have hpevala : p.eval a ≠ 0 := by
    intro haeval
    rw [hr a (by simp [le_of_lt hab]) 0 (by simp) haeval] at hcmem
    simp at hcmem
  have hpevalb : p.eval b ≠ 0 := by
    intro haeval
    rw [hr b (by simp [le_of_lt hab]) 0 (by simp) haeval] at hcmem
    simp at hcmem
  have hderivn : ∀ x ∈ Icc a b, (derivative p).eval x ≠ 0 := by
    intro x hxmem  heval
    have := hr x hxmem 1 (by simp) heval
    rw [this] at heval
    exact hdc heval
  have hxru : ∀ x ∈ Icc a b, p.eval x = 0 → x = c := by
    intro x hxmem hxeval
    exact hr x hxmem 0 (by simp) hxeval
  unfold signChangesPolySeq
  simp ; rw [signChanges_cons hpevala]
  simp ; rw [signChanges_cons hpevalb]
  simp only [← sign_mul, derivative_mul_neg_of_sign_neg_left hc hab hcmem hpr hxru hderivn,
    sign_neg, ↓reduceIte, List.headD_cons,
    derivative_mul_neg_of_sign_neg_right hc hab hcmem hpr hxru hderivn, sign_pos, neg_iff,
    self_eq_neg_iff, one_ne_zero, signChanges_single, zero_add]
  · simp ; exact hderivn b (by simp[le_of_lt hab] )
  · simp ; exact hderivn a (by simp[le_of_lt hab] )



lemma sturm_sequence_unique_root_p (hc : IsRealClosed F) (a b : F) (hab : a < b)
   (P : List F[X]) (p : F[X]) (hs : IsSturmSequence P p (derivative p)) {c : F} (hcmem : c ∈ Ioo a b)
   (hpr : p.eval c = 0) (hr : ∀ x ∈ Icc a b, ∀ i , ∀ h : i < P.length , P[i].eval x = 0 → x = c) :
  signChangesPolySeq P a = signChangesPolySeq P b + 1 := by
  have havePl := hs.hlen
  have hdpevala : (derivative p).eval a ≠ 0 := by
    intro haeval
    rw [hr a (by simp [le_of_lt hab]) 1 (by omega) (by rw[hs.h1] ; exact haeval )] at hcmem
    simp at hcmem
  have hdpevalb : (derivative p).eval b ≠ 0 := by
    intro haeval
    rw [hr b (by simp [le_of_lt hab]) 1 (by omega) (by rw[hs.h1] ; exact haeval )] at hcmem
    simp at hcmem
  have hPL : ∃ as , P = (p :: derivative p  :: as) := by
    match P with
    | [] =>
    simp at havePl
    | [a] =>
    simp at havePl
    | (a :: b :: as) =>
      use as
      have aux1 := hs.h0
      have aux2 := hs.h1
      simp at aux1 aux2 ⊢
      exact ⟨aux1, aux2⟩
  obtain ⟨as, has⟩ := hPL
  by_cases hasn : as = []
  · rw [hasn] at has
    simp_rw [has] at *
    apply signChanges_derivative F hc hab _ hcmem hpr _ hr
    intro hevald
    exact no_consecutive_zero1 [p, derivative p] _ _ hs c 0 (by simp) hevald hpr
  · simp_rw [has] at *
    simp [signChangesPolySeq]
    rw [signChanges_cons_eq_add _ _ _ hdpevala, signChanges_cons_eq_add _ _ _ hdpevalb,
      add_assoc, add_comm _ 1, ← add_assoc]
    congr 1
    · refine signChanges_derivative F hc hab _ hcmem hpr ?_ ?_
      · intro hevald
        exact no_consecutive_zero1 _ _ _ hs c 0 (by simp) hevald hpr
      · rintro x hxmem i hile hieval
        simp at hile
        interval_cases i
        · exact hr x hxmem 0 (by simp) hieval
        · exact hr x hxmem 1 (by simp) hieval
    · simp_rw [← List.map_cons, ← signChangesPolySeq_def ]
      apply sturm_sequence_unique_root_ne_p F hc _ _ hab _ _ _
        (sturm_sequence_cons (derivative p :: as) p (derivative p) _ ?_ hs) c hcmem
      · intro hevald
        exact no_consecutive_zero1 _ _ _ hs c 0 (by simp) hevald hpr
      · rintro x hxmem i hile hieval
        simp at hile
        exact hr x hxmem (i + 1) (by simp ; omega) hieval
      · simp ; by_contra! hc' ; simp[hasn] at hc'


open Finset

lemma roots_of_prod_mem_iff (a b : F) (P : List F[X]) (x : F) (hz : 0 ∉ P) :
  x ∈ (((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))) ↔
  ∃ i : ℕ , (∃ h : i < P.length, P[i].eval x = 0 ∧ x ∈ Icc a b)  := by
  simp
  have : ∀ x, (Polynomial.aeval x) (P.prod) = (List.map (fun y => y.eval x) P).prod := by
    intro c
    simp [← List.prod_hom]
  rintro hle1 hle2
  simp at this
  simp [this, hz,  List.mem_iff_getElem]


lemma finset_card_add_interval (a b c : F) (hcmem : c ∈ Icc a b) (S : Finset F) (hcn : c ∉ S)  :
  #(S.filter (fun x => x ∈ Icc a b)) =
    #(S.filter (fun x => x ∈ Icc a c)) + #(S.filter (fun x => x ∈ Icc c b)) := by
  convert Finset.card_union_of_disjoint (α := F) ?_ using 2
  rw [Set.mem_Icc] at hcmem
  · ext x
    simp
    rcases LinearOrder.le_total x c with h1 | h2
    · constructor
      · intro h
        exact Or.inl ⟨h.1, ⟨h.2.1, h1⟩ ⟩
      · intro h
        rcases h with h3 | h4
        · exact ⟨h3.1, ⟨h3.2.1, le_trans h1 hcmem.2⟩ ⟩
        · exact ⟨h4.1, ⟨le_trans hcmem.1 h4.2.1 , h4.2.2⟩⟩
    · constructor
      · intro h
        exact Or.inr ⟨h.1, ⟨h2, h.2.2⟩ ⟩
      · intro h
        rcases h with h3 | h4
        · exact ⟨h3.1, ⟨h3.2.1, le_trans h3.2.2 hcmem.2⟩ ⟩
        · exact ⟨h4.1, ⟨le_trans hcmem.1 h4.2.1 , h4.2.2⟩⟩
  · rw [Finset.disjoint_iff_ne]
    intro u hu w hw
    simp at hu hw
    rcases lt_or_eq_of_le (le_trans hu.2.2  hw.2.1) with hc1 | hc2
    · exact ne_of_lt hc1
    · exfalso
      have aux : c = w := by
        rw [hc2] at hu
        exact eq_of_le_of_le  hw.2.1 hu.2.2
      rw [← aux] at hw
      exact hcn hw.1


lemma finset_sorted_list_cons_cons  {F : Type u_2} [LinearOrderedField F]
    {u v : F} {as : List F} {S : Finset F} (heq : S.sort (fun x y => x ≤ y) = (u :: v :: as)) :
    ∀ x ∈ S , x = u ∨ v ≤ x := by
  have aux1 : List.Sorted (fun x y => x ≤ y) (u :: v :: as) := by
    rw [← heq]
    simp only [sort_sorted]
  have aux2 := List.Sorted.of_cons aux1
  intro x hxmem
  rw [← Finset.mem_sort (r := fun x y => x ≤ y), heq, List.mem_cons] at hxmem
  simp at hxmem
  rcases hxmem with h1 | h2 | h3
  · left
    exact h1
  · right
    exact le_of_eq (id (Eq.symm h2))
  · right
    exact List.rel_of_sorted_cons aux2 x h3


lemma not_mem_finset_card_eq_one_of_sorted_mem_interval {a b d u v : F} {as : List F}
  {S : Finset F}  (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) : d ∈ Icc a b := by
  have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
  simp at hauxu
  have hauxv := getElem_congr_coll (w := by simp) (i := 1) heqc
  simp at hauxv
  have humem : u ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxu]
    simp only [Set.mem_Icc, List.getElem_mem]
  have hwmem : v ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxv]
    simp only [Set.mem_Icc, List.getElem_mem]
  simp at humem hwmem
  constructor
  · refine le_of_lt (lt_of_le_of_lt humem.2.1 hle1)
  · refine le_of_lt (lt_of_lt_of_le hle2 hwmem.2.2)

lemma not_mem_finset_card_eq_one_of_sorted  {a b d u v : F} {as : List F}
  {S : Finset F} (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) (x : F) :
    x ∈ (S.filter (fun x => x ∈ Icc a d)) ↔ x = u := by
  have hauxu := getElem_congr_coll (w := by simp) (i := 0) heqc
  simp at hauxu
  have humem : u ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
    rw [hauxu]
    simp only [Set.mem_Icc, List.getElem_mem]
  simp at humem
  have hdmem : d ∈ Icc a b := not_mem_finset_card_eq_one_of_sorted_mem_interval F heqc hle1 hle2
  constructor
  · intro h
    simp at h
    obtain ⟨hxmemS, hxa, hxd⟩ := h
    rcases finset_sorted_list_cons_cons heqc.symm x
      (by simp ; exact ⟨hxmemS, ⟨hxa, le_trans hxd hdmem.2⟩⟩) with h1 | h2
    · exact h1
    · linarith
  · intro heq
    simp [heq]
    exact ⟨humem.1, ⟨humem.2.1, le_of_lt hle1⟩⟩

lemma not_mem_finset_card_eq_one_of_sorted_not_mem  {a b d u v : F} {as : List F}
  {S : Finset F} (heqc : (u :: v :: as) = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)))
  (hle1 : u < d) (hle2 : d < v) : d ∉ S := by
  intro hc
  have aux1 := not_mem_finset_card_eq_one_of_sorted_mem_interval F heqc hle1 hle2
  have aux2 := not_mem_finset_card_eq_one_of_sorted F heqc hle1 hle2 d
  simp at aux1 aux2
  rw [aux2.1 ⟨hc, aux1.1⟩] at hle1
  simp at hle1



lemma not_mem_finset_card_eq_one_of_sorted_single (a b u : F) (S : Finset F)
  (heq : [u] = ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) )
  (x : F) : x ∈ (S.filter (fun x => x ∈ Icc a b)) ↔ x = u := by
  rw [← Finset.mem_sort (r := fun x y => x ≤ y) , ← heq]
  simp




lemma finset_card_eq_one_of_sorted  (a b c : F) (S : Finset F)
  (hcard : 1 ≤ #(S.filter (fun x => x ∈ Icc a b)))
  (hmem : (S.filter (fun x => x ∈ Icc a b)).sort [0])


:

/-- have hxmem : x ∈ ((S.filter (fun x => x ∈ Icc a b)).sort (fun x y => x ≤ y)) := by
      simp
      refine ⟨hxmemS, ⟨hxa, le_trans hxd hdmem.2⟩⟩ -/







lemma sturm_theorem_induction_aux (hc : IsRealClosed F) {n : ℕ} (a b : F) (hab : a < b)
    (P : List F[X]) (p : F[X]) (hs : IsSturmSequence P p (derivative p))
    (ha : ∀ i , ∀ h : i < P.length , P[i].eval a ≠ 0) (hb : ∀ i , ∀ h : i < P.length , P[i].eval b ≠ 0)
    (hi : #(((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))) = n) :
    #((Multiset.toFinset p.roots).filter ( fun x => x ∈ Icc a b)) = signChangesPolySeq P b - signChangesPolySeq P a := by
  have hPl := hs.hlen
  have auxNz : ∀ i, ∀ h : i < P.length , P[i] ≠ 0 := by
    intro i hi h
    have : P[i] ∈ P := by simp
    rw [h] at this
    exact zero_not_member hs this
  revert a b
  induction' n with n hn
  · intro a b hab ha hb hnr
    rw [Finset.card_eq_zero] at hnr
    have aux : ∀ i , ∀ h : i < P.length , Finset.filter (fun x ↦ x ∈ Set.Icc a b) P[i].roots.toFinset = ∅ := by
      intro i hi
      by_contra! hc
      rw [← Finset.nonempty_iff_ne_empty] at hc
      obtain ⟨c, hc⟩ := Finset.Nonempty.exists_mem hc
      have hcmem : c ∈ filter (fun x ↦ x ∈ Set.Icc a b) P.prod.roots.toFinset := by
        rw [roots_of_prod_mem_iff]
        use i , (by omega)
        simp at hc
        simp [hs.h0, hc]
        exact zero_not_member hs
      rw [hnr] at hcmem
      simp at hcmem
    have := aux 0 (by omega)
    rw [hs.h0] at this
    rw [this, card_empty, Eq.comm]
    refine Nat.sub_eq_zero_of_le (le_of_eq ?_)
    apply signChanges_congr
    · intro i hi
      simp at hi ⊢
      symm ; by_contra hcc
      obtain ⟨s, hsmem, hsp⟩ := polynomial_has_root_of_ne_sign hc (le_of_lt hab) hcc
        (ha i (by omega)) (hb i (by omega))
      have hsroot : s ∈ Finset.filter (fun x ↦ x ∈ Set.Icc a b) P[i].roots.toFinset := by
        simp [hsp]
        refine ⟨auxNz i (by omega), Set.mem_Icc_of_Ioo hsmem⟩
      rw [aux i (by omega)] at hsroot
      simp at hsroot
    · simp
  · intro a b hab ha hb hnr
    sorry













 --have : #(((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))) =
 --       ((((Multiset.toFinset (P.prod).roots).filter (fun x => x ∈ Icc a b))).sort (fun x y => x ≤ y)).length := by simp


-- zero_not_member




      --simp at this



    --rList.getLast_map

  -- getLastD_eq_getLast_of_ne_nil












--lemma signChanges_sturm_unique_root_case1 :








#exit





             -- convert hi using 3
             -- rw [← Nat.sub_one_add_one (show (i ≠ 0) by sorry)]
              --simp at hi
              --simp[hii]
      --· have s2 : sign a2 = sign b2 := by
      --    by_contra hcc'



  induction' L₁ with a as hin
  /- revert L₂
  induction' L₁ with a as hin
  · intro L₂ hLz hlen hsign
    simp only [List.length_nil] at hlen
    simp [List.length_eq_zero.1 hlen.symm]
  · intro L₂ hzL2 hlen hlast hi
    match L₂ with
    | [] => sorry
    | [b] => sorry
    | (b1 :: b2 :: []) => sorry
    | (b1 :: b2 :: b3 :: bs) =>
    have hca : ∃ c1 c2 c3 cs , (a :: as) = (c1 :: c2 :: c3 :: cs) := by sorry
    obtain ⟨c1, c2,c3, cs, hc ⟩:= hca
    simp_rw [hc] at hzL1 hlen hlast hi ⊢ -/

    /- match as with
    | [] => sorry
    | (c :: cs) =>
    match bs with
    | [] => sorry
    | (d :: ds) =>
    simp at hi -/















lemma SignType.sq_of_ne_zero {a : SignType} (ha : a ≠ 0) : a ^ 2 = 1 := by
  cases a
  · simp at ha
  repeat {simp}

lemma signChanges_cons_cons (a b : R) (bs : List R) (h : sign a * sign (bs.headD 0) < 0)  :
  signChanges (a :: b :: bs) = signChanges (a :: 0 :: bs) := by
  by_cases hbz : b = 0
  · rw [hbz]
  · have has : a ≠ 0 := by
      rintro rfl
      simp only [sign_zero, List.headD_eq_head?_getD, zero_mul, lt_self_iff_false] at h
    have hbh : bs.headD 0 ≠ 0 := by
      intro h1
      rw [h1] at h
      simp only [sign_zero, mul_zero, lt_self_iff_false] at h
    by_cases ha : sign a = sign b
    · have aux1 : sign a * sign b = 1 := by
        rw [ha, ← sq]
        exact SignType.sq_of_ne_zero (sign_ne_zero.mpr hbz)
      rw [signChanges_modify_zero, signChanges_cons has hbh, signChanges_cons has (by simp[hbz])]
      simp only [List.headD_cons, sign_zero, mul_zero, lt_self_iff_false, ↓reduceIte, aux1]
      rw [ha]
      simp only [neg_iff, self_eq_neg_iff, one_ne_zero, ↓reduceIte]
      rw[signChanges_cons hbz hbh]
      simp only [List.headD_eq_head?_getD, neg_iff]
    · push_neg at ha hbz
      have aux1 : sign a * sign b = - 1 := by
        cases hb : sign b
        · exfalso  ; simp at hb ; exact hbz hb
        · simp
          erw [ hb, ← SignType.nonneg_iff_ne_neg_one, SignType.nonneg_iff] at ha
          simp [has] at ha
          exact ha
        · simp
          erw [ hb, ← SignType.nonpos_iff_ne_one, SignType.nonpos_iff] at ha
          simp [has] at ha
          exact ha
      have aux2 : sign b * sign (bs.headD 0) = 1 := by
        simp at h
        rw [← neg_neg 1, neg_eq_neg_one_mul]
        nth_rw 1 [← aux1, ← h]
        rw [mul_assoc, ← mul_assoc (sign b), mul_comm (sign b),
          mul_comm (sign b), mul_assoc, ← mul_assoc (sign a), ← sq ,
            SignType.sq_of_ne_zero (sign_ne_zero.mpr has), one_mul,
            mul_comm, List.headD_eq_head?_getD]
      rw [signChanges_modify_zero, signChanges_cons has hbh, signChanges_cons has (by simp[hbz])]
      simp only [List.headD_cons, aux1, neg_iff, ↓reduceIte, h]
      rw[signChanges_cons hbz hbh, aux2]
      rfl


lemma head_filter_eq_head_filter_modify (as : List R) (hi : i + 1 < as.length -1)
  (has : ∃ j : Fin (as.length -1), j ≤ i ∧ as[j] ≠ 0) :
  ((List.filter (fun x => if x ≠ 0 then true else false)) as).headD 0 =
  ((List.filter (fun x => if x ≠ 0 then true else false)) (List.modify (fun x ↦ 0) (i + 1) as)).headD 0 := by
  revert i
  induction' as with b bs hbi
  · simp
  · rintro i hle ⟨⟨j, hjs⟩, hje1, hje2⟩
    by_cases hiz : i = 0
    · rw [hiz] at hje1 ⊢
      simp at hje1
      simp_rw [hje1] at hje2
      simp at hje2
      simp [List.filter_cons, List.modify_succ_cons, hje2]
    · by_cases hb : b = 0
      · rw [hb] at hje2 ⊢
        have hj : j ≠ 0 := by
          by_contra hjc
          simp_rw [hjc] at hje2
          simp at hje2
        rw [List.filter_cons, List.modify_succ_cons, List.filter_cons]
        simp only [ne_eq, not_true_eq_false, ↓reduceIte, Bool.false_eq_true, ite_not]
        have hip : 1 ≤ i := by exact Nat.zero_lt_of_ne_zero hiz
        have hjp : 1 ≤ j := by exact Nat.zero_lt_of_ne_zero hj
        have hjlehi : j - 1 ≤ i - 1 := by
          zify [hip, hjp]
          linarith
        simp at hjs
        have hjo : 1 ≤ bs.length := by linarith
        have hjlebs : j - 1 < bs.length - 1 := by
          zify at hjs
          zify [hjs,  hjp, hjo]
          linarith
        have hjsucc : j = (j - 1) + 1 := by
          exact (Nat.sub_eq_iff_eq_add hjp).mp rfl
        simp at hje2
        convert hbi (i := i - 1) ?_ ⟨⟨j -1 , hjlebs ⟩, ⟨hjlehi, ?_ ⟩  ⟩  using 2
        · simp only [Bool.if_true_right, Bool.or_false, ne_eq, ite_not]
        · simp only [Bool.if_true_right, Bool.or_false, ne_eq, ite_not]
          congr
          exact (Nat.sub_eq_iff_eq_add hip).mp rfl
        · zify[hip, hjo]
          simp at hle
          linarith
        · erw [← List.getElem_cons_succ 0 bs (j - 1)]
          convert hje2
          exact id (Eq.symm hjsucc)
          simp
          linarith
      · simp [List.filter_cons, List.modify_succ_cons, hb]


lemma signChanges_eq_signChanges_replace_zero' (L : List R) (i : ℕ)
  (hi : 0 ≤ i ∧ i + 2 < L.length - 1) (hL : sign (L[i]) * sign (L[i + 2]) = -1 ) :
  signChanges L = signChanges (List.modify (fun x => 0) (i + 1) L) := by
revert i
induction' L with a as haz
· simp
· by_cases hass : as = []
  · simp_rw [hass]
    simp only [List.length_singleton, tsub_self, not_lt_zero', and_false, List.getElem_singleton,
      List.getElem_cons_succ, List.modify_succ_cons, List.modify_nil, implies_true]
  · intro i hi hL
    have hasl : 1 ≤ as.length := by refine Nat.one_le_iff_ne_zero.mpr (by simp[hass])
    match i with
    | 0 =>
      dsimp
      match as with
        | [] => simp
        | (b :: []) => simp at hi
        | (b :: b2 :: bs) =>
          simp at hL ⊢
          refine signChanges_cons_cons a _ _ ?_
          rwa [List.headD_cons, neg_iff]
    | i + 1 =>
    · have aux : ((List.filter (fun x => if x ≠ 0 then true else false)) as).headD 0 =
        ((List.filter (fun x => if x ≠ 0 then true else false)) (List.modify (fun x ↦ 0) (i + 1) as)).headD 0 := by
        simp only [le_add_iff_nonneg_left, zero_le, List.length_cons, add_tsub_cancel_right,
          true_and] at hi
        refine head_filter_eq_head_filter_modify as ?_ ?_
        · zify [hasl]
          linarith
        · use ⟨i , by zify [hasl, hi] ; zify at hi ; linarith⟩
          constructor
          · simp
          · erw [← List.getElem_cons_succ a _ i]
            intro h
            rw [h] at hL
            simp at hL
      dsimp
      have aux2 : signChanges as = signChanges (List.modify (fun x ↦ 0) (i + 1) as) := by
        specialize haz i
        convert haz ?_ ?_
        · simp at hi
          refine ⟨ by linarith, ?_ ⟩
          zify[hasl] ; linarith
        · simp only [List.getElem_cons_succ] at hL
          exact hL
      by_cases ha : a = 0
      · rw [ha, signChanges_zero_head, signChanges_zero_head]
        exact aux2
      · unfold signChanges
        rw [List.filter_cons_of_pos (by simp[ha]), List.filter_cons_of_pos]
        unfold signChanges'
        simp_rw [aux, ← signChanges_def, aux2]
        simp[ha]

-- I can assume that my list has no zeros. For each entry either the sign stays the same
-- or for two consecutive entries (skipping one), the signs are opposite.
lemma signChanges_eq_signChanges (L₁ L₂ : List R)
  (hlen : L₁.length = L₂.length)
  (hi : ∀ i,  0 ≤ i ∧ i + 2 < L₁.length - 1 → sign (L₁[i + 1]) = sign (L₂[i + 1]) ∨
    (sign (L₁[i]) * sign (L₁[i + 2]) = -1 ∧ sign (L₂[i]) * sign (L₂[i + 2]) = -1)) :



(i : ℕ)
  (hi : 0 ≤ i ∧ i + 2 < L.length - 1) (hL : sign (L[i]) * sign (L[i + 2]) = -1 )






#exit


      --simp only [signChanges', hc1]
      --dsimp
      --nth_rw 1 [signChanges']
      --simp only [hcc1]
      --dsimp
      --simp [signChanges']



    --unfold signChanges'
    --dsimp




/- have hnz : sign (L[i]) ≠ 0 := by
  intro h
  rw [h] at hL
  simp only [zero_mul, reduceCtorEq] at hL
have hnz2 : sign (L[i + 2]) ≠ 0 := by
  intro h
  rw [h] at hL
  simp only [mul_zero, reduceCtorEq] at hL
induction' L with a as haz
sorry -/




lemma signChanges_eq_signChanges_replace_zero (L : List R) (i : ℕ) (hi : 0 < i ∧ i + 2 < L.length - 1)
  (hL : sign (L[i]) * sign (L[i + 2]) = -1 ) :
  signChangesList L = signChangesList (List.modify (fun x => 0) (i + 1) L ) := by
have hnz : sign (L[i]) ≠ 0 := by
  intro h
  rw [h] at hL
  simp only [zero_mul, reduceCtorEq] at hL
have hnz : sign (L[i + 2]) ≠ 0 := by
  intro h
  rw [h] at hL
  simp only [mul_zero, reduceCtorEq] at hL
by_cases hc : sign (L[i]) = 1
· have hs2 : sign L[i + 2] = -1 := by sorry
  by_cases hc2 : sign (L[i + 1]) = 1
  ·






/-- If the interval [a,b] contains only one root `c` of any of the polynomials in the sequence
  (which can be a root for multiple elements in the list), and `c` is not a root of the first polynomial, and
  if we assume that only subsequences of the form `[+, 0, -1]` or `[-, 0, +]` can appear at `c`, then
  the the sign change at `a` is the same as at `b`. -/
lemma no_sign_change_of_zero_opposite_signs {n i : ℕ} [NeZero n] (a b c : R)
  (hc : a ≤ c ∧ c ≤ b) (P : Fin n → R[X])
  (hi : ∀ (i : Fin n), ∀ h : i.val + 2 < n  ,
    ((P ⟨i + 1, by linarith⟩).eval c = 0 → (P i).eval c ≠ 0 ∧ sign ((P i).eval c) = - sign ((P (⟨i + 2, by linarith ⟩)).eval c)))
  (hu : ∀ x, a ≤ x ∧ x ≤ b → ∃ (i : Fin n), (P i).eval x = 0 → x = c) (hn : (P 0).eval c ≠ 0) :
  signChangesPolySeq P a = signChangesPolySeq P b := by sorry





#eval signChangesList  [1,2,-3,4,-4,5,5,5,5,5]

lemma signChanges_pos_pos_neg {a b c : R}
    (ha : 0 < a) (hb : 0 < b) (hc : c < 0) : signChangesList [a, b, c] = 1 := by
  unfold signChangesList
  simp [ha, hb, hc]
  rfl

lemma signChanges_pos_zero_neg {a b c : R}
    (ha : 0 < a) (hb : b = 0) (hc : c < 0) : signChangesList [a, b, c] = 1 := by
  unfold signChangesList
  simp [ha, hb, hc]


lemma signChanges_pos_neg_neg {a b c : R}
    (ha : 0 < a) (hb : b < 0) (hc : c < 0) : signChangesList [a, b, c] = 1 := by
  unfold signChangesList
  simp [ha, hb, hc]
  rfl

lemma signChanges_neg_neg_pos {a b c : R}
    (ha : a < 0) (hb : b < 0) (hc : 0 < c) : signChangesList [a, b, c] = 1 := by
  unfold signChangesList
  simp [ha, hb, hc]
  rfl

lemma signChanges_neg_pos_pos {a b c : R}
    (ha : a < 0) (hb : 0 < b) (hc : 0 < c) : signChangesList [a, b, c] = 1 := by
  unfold signChangesList
  simp [ha, hb, hc]
  rfl

lemma signChanges_neg_zero_pos {a b c : R}
    (ha : a < 0) (hb : b = 0) (hc : 0 < c) : signChangesList [a, b, c] = 1 := by
  unfold signChangesList
  simp [ha, hb, hc]

--lemma signChanges_congr (k l : List R) (hl : k.length = l.length)


lemma signChanges_single (a : R) : signChangesList [a] = 0 := by
  by_cases ha : a = 0
  · simp[ha, signChangesList]
  · simp[ha, signChangesList]




lemma signChanges_eq_signChanges_ne_zero (l : List R) :
    signChangesList l  = signChangesList (List.filter (fun x => if x ≠ 0 then true else false) l) := by
  have : ∀ (L : List R), List.filter (fun x => if x ≠ 0 then true else false) (List.map SignType.sign L) =
  List.map SignType.sign (List.filter (fun x => if x ≠ 0 then true else false) L) := by
    intro L
    rw [List.filter_map]
    congr
    ext x
    simp only [ne_eq, ite_not, Bool.if_true_right, Bool.or_false, Function.comp_apply,
      sign_eq_zero_iff]
  dsimp[signChangesList]
  simp_rw [this]
  congr 4
  simp only [ne_eq, ite_not, Bool.if_true_right, Bool.or_false, List.filter_filter, Bool.and_self]


lemma signChanges_cons (a b : R) (l : List R)  (hbz : b ≠ 0) :
  signChangesList (a :: b :: l) = signChangesList [a,b] + signChangesList (b :: l) := by sorry

-- assume that no entry in l1 or l2 is zero.
lemma signChanges_concat_concat (l₁ l₂ : List R) (a : R) (ha : a ≠ 0) :
  signChangesList (l₁ ++ [a] ++ l₂) =
  signChangesList (l₁ ++ [a]) + signChangesList (a :: l₂) := by
induction' l₁ with b bs hab
· simp
  exact signChanges_single _
· match bs with
  | [] => simp ; exact signChanges_cons _ _ _ ha
  | (c :: cs) =>







  /- omega
  unfold signChangesList
  congr 2
  rw [List.map_cons]
  by_cases ha : SignType.sign a = 0
  · simp_rw [ha]
    simp only [ne_eq, ite_not, Bool.if_true_right, Bool.or_false, decide_true, Bool.not_true,
      Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg]
  · by_cases hb : SignType.sign b = 0
    · exfalso
      simp only [sign_eq_zero_iff] at hb
      exact hbz hb
    · simp[ha, hb] -/

    --rw [List.destutter_cons', (List.destutter'_eq_self_iff _ _ _).2]


#exit
lemma signChanges_append_eq_add (k l : List R)
    (h : SignType.sign (k.getLastD 0) * SignType.sign (l.headD 0)  ≠ -1 ) :
    signChangesList (k ++ l) = signChangesList k + signChangesList l := by
    revert l
    induction' k with a as has
    · simp
      rfl
    · match as with
      | [] => simp[has] ; sorry
      | (b :: bs) => by simp







#exit


lemma signChanges_pos_pos_neg {a b c : R}
    (ha : 0 < a) (hb : 0 < b) (hc : c < 0) : signChanges ![a, b, c] = 1 := by
  unfold signChanges
  rw [Finset.sum_congr (rfl) (g :=  ![0,1])]
  · rfl
  · intro i hi
    fin_cases i
    · simp [ha, hb]
    · simp [hb, hc]

lemma signChanges_pos_zero_neg {a b c : R}
    (ha : 0 < a) (hb : b = 0) (hc : c < 0) : signChanges ![a, b, c] = 1 := by
  unfold signChanges
  rw [Finset.sum_congr (rfl) (g :=  ![0,1])]
  · rfl
  · intro i hi
    fin_cases i
    · simp [ha, hb]
    · simp [hb, hc]




end signChanges
