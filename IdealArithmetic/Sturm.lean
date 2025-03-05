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
    a ≤ b → t ∈ Set.Ioo (P.eval a) (P.eval b)  → ∃ s, s ∈ Set.Ioo a b ∧ P.eval s = t


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

variable {F : Type} [LinearOrderedField F]
open Set

lemma polynomial_has_root_of_le_zero_of_pos (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : P.eval a < 0) (hb : 0 < P.eval b ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  exact hc hab ⟨ha, hb⟩

lemma polynomial_has_root_of_pos_le_zero (hc : IsRealClosed F) {a b : F} (hab : a ≤ b)
    {P : F[X]} (ha : 0 < P.eval a) (hb : P.eval b < 0 ) : ∃ s ∈ Ioo a b , P.eval s = 0 := by
  obtain ⟨s, hs1, hs2⟩ := @hc a b 0 (- P) hab (by simp[ha, hb])
  simp only [eval_neg, neg_eq_zero] at hs2
  exact ⟨s, hs1, hs2 ⟩


  --exact hc hab (Or.inr ⟨hb , ha⟩)


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

lemma pos_of_ne_zero_of_exists_pos (hc : IsRealClosed F) {a b m : F} {P : F[X]}
    (hP : ∀ x ∈ Ioo a b , P.eval x ≠ 0) (hm : m ∈ Ioo a b) (hpos : P.eval m > 0) :
    ∀ x ∈ Ioo a b , P.eval x > 0 := by
  intro x hx
  by_contra! hc'
  rcases le_iff_lt_or_eq.1 hc' with hz1 | hz2
  · rcases le_or_gt m x with hm1 | hm2
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc hm1 hpos hz1
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hm.1 hs1.1, lt_trans hs1.2 hx.2⟩
    · obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hm2) hz1 hpos
      refine hP s ?_ hs2
      simp only [mem_Ioo] at hs1 hx ⊢
      exact ⟨lt_trans hx.1 hs1.1, lt_trans hs1.2 hm.2⟩
  · exact hP x hx hz2


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
    (∀ x ∈ Icc a b , P.eval x ≥ 0) ∨ (∀ x ∈ Icc a b , P.eval x ≤ 0)  := by
  rcases le_iff_lt_or_eq.1 hab with h1 | h2
  · obtain ⟨m, hm⟩ := exists_between  h1
    rcases lt_trichotomy (P.eval m) 0 with hl1 | hl2 | hl3
    · right
      intro x hmem
      rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hmem with ha | hb | hx
      · rw [ha]
        by_contra! hc'
        obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm.1) hc' hl1
        refine hP s ?_ hs2
        simp only [mem_Ioo] at hs1
        exact ⟨hs1.1, lt_trans hs1.2 hm.2⟩
      · rw [hb]
        by_contra! hc'
        obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hm.2) hl1 hc'
        refine hP s ?_ hs2
        simp only [mem_Ioo] at hs1
        exact ⟨lt_trans hm.1 hs1.1, hs1.2⟩
      · exact le_of_lt (neg_of_ne_zero_of_exists_neg hc hP hm hl1 x hx)
    · exfalso ; exact hP m hm hl2
    · left
      intro x hmem
      rcases Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hmem with ha | hb | hx
      · rw [ha]
        by_contra! hc'
        obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hm.1) hc' hl3
        refine hP s ?_ hs2
        simp only [mem_Ioo] at hs1
        exact ⟨hs1.1, lt_trans hs1.2 hm.2⟩
      · rw [hb]
        by_contra! hc'
        obtain ⟨s, hs1, hs2⟩ := polynomial_has_root_of_pos_le_zero hc (le_of_lt hm.2) hl3 hc'
        refine hP s ?_ hs2
        simp only [mem_Ioo] at hs1
        exact ⟨lt_trans hm.1 hs1.1, hs1.2⟩
      · exact le_of_lt (pos_of_ne_zero_of_exists_pos hc hP hm hl3 x hx)
  · simp [h2, LinearOrder.le_total 0 (eval b P)]



lemma rolle_theorem_weak (hc : IsRealClosed F) {a b : F} (hab : a < b) {P : F[X]}
    (hP : ∀ x ∈ Ioo a b, P.eval x ≠ 0) (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Ioo a b , (derivative P).eval c = 0 := by
  have hPnz : P ≠ 0 := by
    intro h
    obtain ⟨m, hm⟩ := exists_between  hab
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
    rcases constant_sign_of_ne_zero' hc (le_of_lt hab) hQIoo with hqal | hqag
    · have ha1 : Q1.eval a < 0 := by
        rw [hQ1a]
        simp only [neg_mul, Left.neg_neg_iff]
        refine mul_pos (mul_pos ?_ ?_) ?_
        · rw [Nat.cast_pos]
          exact Nat.pos_of_ne_zero ham
        · linarith
        · specialize hqal a (by simp ; exact le_of_lt hab )
          exact lt_of_le_of_ne hqal (hQr.1).symm
      have hb1 : Q1.eval b > 0 := by
        rw [hQ1b]
        refine mul_pos (mul_pos ?_ ?_) ?_
        · rw [Nat.cast_pos]
          exact Nat.pos_of_ne_zero hbm
        · linarith
        · specialize hqal b (by simp ; exact le_of_lt hab )
          exact lt_of_le_of_ne hqal (hQr.2).symm
      exact polynomial_has_root_of_le_zero_of_pos hc (le_of_lt hab) ha1 hb1
    · have ha1 : Q1.eval a > 0 := by
        rw [hQ1a] ; simp
        refine mul_neg_of_pos_of_neg (mul_pos ?_ ?_) ?_
        · rw [Nat.cast_pos]
          exact Nat.pos_of_ne_zero ham
        · linarith
        · specialize hqag a (by simp ; exact le_of_lt hab )
          exact lt_of_le_of_ne hqag (hQr.1)
      have hb1 : Q1.eval b < 0 := by
        rw [hQ1b]
        refine mul_neg_of_pos_of_neg (mul_pos ?_ ?_) ?_
        · rw [Nat.cast_pos]
          exact Nat.pos_of_ne_zero hbm
        · linarith
        · specialize hqag b (by simp ; exact le_of_lt hab )
          exact lt_of_le_of_ne hqag (hQr.2)
      exact polynomial_has_root_of_pos_le_zero hc (le_of_lt hab) ha1 hb1
  obtain ⟨c, hcI, hc⟩ := hzQ
  use c
  refine ⟨hcI, ?_ ⟩
  simp [hderiv, hc]






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

def signChanges (L : List R) : ℕ  := signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L)


lemma signChanges_def (L : List R) : signChanges L = signChanges' (List.filter (fun x => if x ≠ 0 then true else false) L) := by
  rfl

#eval signChangesList [1,-2,3,-1,-3,4,5,6,-7]
#eval signChanges' [1,0, 0, -2,3,-1,-3,4,5,6,-7]

open SignType

def signChangesPolySeq {n : ℕ} (P : Fin n → R[X]) (a : R) : ℕ :=
  signChangesList (List.ofFn (fun i => (P i).eval a))

lemma signChanges_zero_head (as : List R) : signChanges (0 :: as) = signChanges as := by
  unfold signChanges
  simp

lemma signChanges_zero_head' (as : List R) : signChanges' (0 :: as) = signChanges' as := by
  simp_rw [signChanges', sign_zero, zero_mul]
  rfl


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
