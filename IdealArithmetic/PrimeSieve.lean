import Mathlib.NumberTheory.SmoothNumbers

/- For p > 1, computes the multiples n of p (excluding p) such that A < n ≤ B, returns a list. -/
def MultiplesBetween (p : ℕ) (A B : ℕ) : List ℕ := by
  let m := A / p
  let n := B / p
  let t := n - m
  exact (if p < 2 then [] else
   (( List.range t).map (fun k => m + 1 + k)).map (fun k => p * k))


lemma MultiplesBetween_mem (p : ℕ) (A B : ℕ) (m : ℕ) :
  m ∈ MultiplesBetween p A B ↔ 2 ≤ p ∧ p ∣ m ∧ A < m ∧ m ≤ B := by
  have hAp : A = (A / p) * p + A % p := Eq.symm (Nat.div_add_mod' A p)
  have hBp : B = (B / p) * p + B % p := Eq.symm (Nat.div_add_mod' B p)
  constructor
  · intro hm
    have : ¬ p < 2 := by
      intro hc
      simp only [MultiplesBetween, hc, ↓reduceIte, List.not_mem_nil] at hm
    simp [MultiplesBetween, this] at hm
    obtain ⟨t,ht,htt⟩ := hm
    have hpdvd : p ∣ m := by
      use (A / p + 1 + t)
      exact htt.symm
    refine ⟨by omega,⟨hpdvd, ⟨?_, ?_⟩ ⟩ ⟩
    have hrAp : A % p < p := by refine Nat.mod_lt A (by omega)
    · suffices hm : (A / p + 1 ≤ m / p) by nlinarith
      rw [← htt, Nat.mul_div_cancel_left _ (by omega)]
      omega
    · suffices hm : (m / p ≤ B / p) by
        have := Nat.mul_le_mul_left p hm
        rw [Nat.mul_div_cancel' hpdvd] at this
        refine le_trans this (Nat.mul_div_le B p)
      rw [← htt, Nat.mul_div_cancel_left _ (by omega)]
      omega
  · rintro ⟨hpt, ⟨z,hz⟩ , hpA, hpB⟩
    have : ¬ p < 2 := by omega
    have hrAp : A % p < p := by refine Nat.mod_lt A (by omega)
    have hrBp : B % p < p := by refine Nat.mod_lt B (by omega)
    simp [MultiplesBetween, this]
    use z - (A / p + 1)
    have : A / p < z := by
      rw [← Nat.mul_lt_mul_left (a := p) (by omega), ← hz, mul_comm]
      rw [hAp] at hpA
      omega
    have : A / p + 1 ≤ z := by omega
    have hAB : A < B := by omega
    have hABp : A / p ≤ B / p := by refine Nat.div_le_div_right (by omega)
    constructor
    · rw [← Nat.mul_lt_mul_left (a := p) (by omega)]
      zify [this, hABp]
      nlinarith
    · zify [this]
      simp only [add_sub_cancel, hz, Nat.cast_mul]



/- A naive sieve, where we cross out multiples of 2, ..., √n (repeating elements that
where already crossed out) this is to prove properties easier.
Possible optimizations:
* Classic Sieve or Ertahostenes
* Segmented sieve, where the classic sieve is used to determien primes up to √N, and then
  the multiples of these primes are crossed out from segments [1,...,a₁], [a₁ + 1, ..., a₂], .., [aκ + 1,..,N] . -/
def PrimeSieveNaive (B : ℕ) : List ℕ :=
  let k := Nat.sqrt B
  let rec aux (cont : ℕ) (accum : List ℕ) : List ℕ  :=
    match cont , accum with
    | 0, accum => accum
    | cont + 1 , accum => aux cont (List.diff accum ((MultiplesBetween (cont + 1) (cont + 1) B)))
  (aux k (List.range (B + 1))).drop 2



def PrimeSieve_loop (P : List ℕ) (A B : ℕ) (cont : ℕ) (accum : List ℕ) : List ℕ :=
    match cont , accum with
    | 0, accum => accum
    | cont + 1 , accum => if h : cont + 1 < P.length then
      PrimeSieve_loop P A B cont (List.diff accum ((MultiplesBetween (P[cont + 1]) (max A P[cont + 1]) B))) else []

/- lemma List.Subset.diff_right {α : Type*} [DecidableEq α] (l₁ l₂ l₃ : List α) (h : l₁.Sublist l₂) :
  (l₁.diff l₃ ⊆ l₂.diff l₃ := by
  revert l₁ l₂
  induction' l₃ with a as has
  · intro l₁ l₂ hl
    simp [hl]
  · intro l₁ l₂ hl
    simp
    refine has _ _ ?_
    intro x hx
    refine List.mem_diff_of_mem ?_ ?_ -/





lemma PrimeSieve_loop_sublist_aux {P : List ℕ} (A B : ℕ) {c : ℕ} (hcl : c < P.length) {L₁ L₂ : List ℕ}
  (hL : L₁.Sublist L₂)  : (PrimeSieve_loop P A B c L₁).Sublist (PrimeSieve_loop P A B c L₂) := by
  revert L₁ L₂
  induction' c with c hc
  · intro L₁ L₂ hL
    simp only [PrimeSieve_loop, hL]
  · intro L₁ L₂ hL
    simp [PrimeSieve_loop, hcl ]
    refine hc (show c < P.length by omega) (List.Sublist.diff_right hL)


lemma PrimeSieve_loop_sublist {P : List ℕ} (A B : ℕ) {c d : ℕ} (h : c ≤ d)
  (hdd : d < P.length) (L : List ℕ) :
  (PrimeSieve_loop P A B d L).Sublist (PrimeSieve_loop P A B c L) := by
  induction' d with d hd
  · simp only [nonpos_iff_eq_zero] at h
    rw [h]
  · have hdaux : d < P.length := by omega
    have haux: (PrimeSieve_loop P A B (d + 1) L).Sublist (PrimeSieve_loop P A B d L) := by
      simp only [PrimeSieve_loop, hdd, ↓reduceDIte]
      refine PrimeSieve_loop_sublist_aux A B hdaux ?_
      exact List.diff_sublist L (MultiplesBetween P[d + 1] (max A P[d + 1]) B)
    by_cases hi : c ≤ d
    · refine List.Sublist.trans ?_ (hd hi hdaux)
      exact haux
    · have : c = d + 1 := by omega
      rw [this]

lemma PrimeSieve_loop_multiples_aux (P : List ℕ) (A B : ℕ) (i : ℕ)
  (hdd : i < P.length) (hPz : i ≠ 0 → 2 ≤ P[i]) (L : List ℕ)
  (hL : L.Nodup) (n : ℕ) (hz : P[0] = 0)
  (hna : A < n) (hnb : n ≤ B) (hn : P[i] ∣ n) (hneq : n ≠ P[i]) :
    ¬ n ∈ PrimeSieve_loop P A B i L := by
  match i with
  | 0 =>
    simp only [hz, zero_dvd_iff] at hn
    simp only [hn, hz, ne_eq, not_true_eq_false] at hneq
  | i + 1 =>
    simp [PrimeSieve_loop, hdd]
    intro hnn
    have hnaux : n ∈ PrimeSieve_loop P A B 0 (L.diff (MultiplesBetween P[i + 1] (max A P[i + 1]) B)):= by
      refine List.Sublist.mem hnn ?_
      refine PrimeSieve_loop_sublist A B (show 0 ≤ i by omega) (by omega) _
    refine (?_ : _ → False) hnaux
    simp only [PrimeSieve_loop, List.Nodup.mem_diff_iff hL, imp_false, not_and, Decidable.not_not]
    simp only [ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      forall_const] at hPz
    intro hni
    rw [MultiplesBetween_mem]
    refine ⟨hPz, ⟨hn, ⟨?_, hnb⟩ ⟩ ⟩
    simp only [sup_lt_iff, hna, true_and]
    refine lt_of_le_of_ne (Nat.le_of_dvd (Nat.zero_lt_of_lt hna) hn) (fun a ↦ hneq (id (Eq.symm a)))


lemma PrimeSieve_loop_prime_mem {P : List ℕ} (A B : ℕ) {i : ℕ} (hdd : i < P.length)
  {L : List ℕ} (hL : L.Nodup) {n : ℕ} (hnl : n ∈ L)
  (hn : ∀ k, ∀ h : k ≤ i , P[k] ≠ n → ¬ P[k] ∣ n) :
  n ∈ PrimeSieve_loop P A B i L := by
  revert L
  induction' i with i hi
  · simp only [PrimeSieve_loop, imp_self, implies_true]
  · intro L hnndup hlmem
    simp [PrimeSieve_loop, hdd]
    refine hi (by omega) ?_ ?_ ?_
    · intro k hk
      exact hn k (by omega)
    · exact List.Nodup.diff hnndup
    · rw [List.Nodup.mem_diff_iff hnndup]
      refine ⟨hlmem, ?_ ⟩
      rw [MultiplesBetween_mem]
      intro hc
      refine  hn (i + 1) (by omega) (by omega) hc.2.1





/- Computes the primes p such that A < p ≤ B. For correctness, L must be a list
with all the primes up to the square root of B. -/
def PrimeSieve (A : ℕ) (B : ℕ) (L : List ℕ) : List ℕ :=
  let P := (0 :: L)
  let m := List.length L
  let r := B - A
  (PrimeSieve_loop P A B m ((List.range r).map (fun k => A + 1 + k) ))


lemma PrimeSieve_mem (A : ℕ) (B : ℕ) (hA : 1 ≤ A) (L : List ℕ)
  (h : ∀ q, Nat.Prime q → q < Nat.sqrt B + 1 → q ∈ L) (hpL : ¬ 1 ∈ L) (p : ℕ)  :
  p ∈ PrimeSieve A B L ↔ Nat.Prime p ∧ A < p ∧ p ≤ B := by
  constructor
  · intro hp
    unfold PrimeSieve at hp
    have hleaux : A < p ∧ p ≤ B := by
      have : p ∈ ((List.range (B - A)).map (fun k => A + 1 + k) ) := by
        refine List.Sublist.mem hp ?_
        refine PrimeSieve_loop_sublist (P := (0 :: L)) A B (c := 0) (d := List.length L) (by omega)
          (by simp) ((List.map (fun k ↦ A + 1 + k) (List.range (B - A))))
      simp at this
      omega
    refine ⟨?_, hleaux⟩
    rw [Nat.prime_def_le_sqrt]
    refine ⟨by omega, ?_ ⟩
    intro m hmm hmsq
    let q := Nat.minFac m
    have hqp : Nat.Prime q := Nat.minFac_prime (by omega)
    have hqm : q ≤ m := Nat.minFac_le (by omega)
    suffices ¬ q ∣ p by exact fun hc => this (dvd_trans (Nat.minFac_dvd m) hc)
    have hqmem : q ∈ L := by
      refine h q hqp ?_
      refine lt_of_le_of_lt (le_trans hqm hmsq ) ?_
      refine Order.lt_add_one_iff.mpr (Nat.sqrt_le_sqrt hleaux.2)
    intro hc
    obtain ⟨j, hjl, hj⟩ := List.getElem_of_mem hqmem
    have := (PrimeSieve_loop_multiples_aux (0 :: L) A B (j + 1) (by simp[hjl]) ?_
      ((List.range (B - A)).map (fun k => A + 1 + k) ) ?_ p rfl hleaux.1 hleaux.2 ?_ ?_)
    apply this
    refine List.Sublist.mem hp ?_
    refine PrimeSieve_loop_sublist (P := (0 :: L)) A B (c := j + 1)
      (d := List.length L) (by omega) (by simp) _
    · simp only [ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      List.getElem_cons_succ, hj, forall_const]
      exact Nat.Prime.two_le hqp
    · refine List.Nodup.map (add_right_injective (A + 1)) (List.nodup_range)
    · simp only [List.getElem_cons_succ, hj, hc]
    · simp only [List.getElem_cons_succ, hj, ne_eq]
      have := lt_of_le_of_lt hmsq (Nat.sqrt_lt_self (n := p) (by omega))
      linarith
  · rintro ⟨hp, hla, hlb⟩
    refine PrimeSieve_loop_prime_mem A B (i := L.length)
      (L := ((List.range (B - A)).map (fun k => A + 1 + k) )) (by simp) (n := p) ?_ ?_ ?_
    · exact List.Nodup.map (add_right_injective (A + 1)) (List.nodup_range)
    · simp only [List.mem_map, List.mem_range]
      use (p - (A + 1))
      omega
    · intro k hk hneq
      match k with
      | 0 =>
        simp only [List.getElem_cons_zero, zero_dvd_iff, ne_eq]
        exact id (Ne.symm hneq)
      | k + 1 =>
        simp at hneq ⊢
        intro hc
        rw [Nat.dvd_prime hp] at hc
        simp only [hneq, or_false] at hc
        simp only [← hc, List.getElem_mem, not_true_eq_false] at hpL


lemma PrimeSieve_mem_of_primesBelow (A : ℕ) (B C : ℕ) (hC : C ≤ B)
  (hA : 1 ≤ A) (L : List ℕ)
  (hL : L.toFinset = Nat.primesBelow (B.sqrt + 1))  (p : ℕ) :
  p ∈ PrimeSieve A C L ↔ Nat.Prime p ∧ A < p ∧ p ≤ C := by
  refine PrimeSieve_mem A C hA L ?_ ?_ p
  · intro q hqp hqlt
    suffices q ∈ L.toFinset by exact List.mem_dedup.mp this
    rw [hL]
    refine Nat.mem_primesBelow.mpr ⟨?_, hqp⟩
    refine lt_of_lt_of_le hqlt ?_
    simp only [add_le_add_iff_right]
    exact Nat.sqrt_le_sqrt hC
  · intro hc
    have : 1 ∈ L.toFinset := by exact List.mem_toFinset.mpr hc
    rw [hL, Nat.mem_primesBelow] at this
    exact Nat.prime_one_false this.2

lemma list_eq_primesBelow {B : ℕ} {L : List ℕ}
  (h : ∀ p, p ∈ L ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ B) :
    L.toFinset = Nat.primesBelow (B + 1) := by
  ext p
  rw [List.mem_toFinset]
  convert h p
  rw [Nat.mem_primesBelow]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ⟨ Nat.Prime.one_lt h2 , by omega⟩ ⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h1 ⟩



lemma sqrt10000 : Nat.sqrt 10000  = 100 := by
  unfold Nat.sqrt
  repeat dsimp ; unfold Nat.sqrt.iter
  decide


#eval List.foldl (fun x y => x ++ y) [] [[1,2,3], [4,5,6], [7,8,9]]


lemma primes_below_append  (e P : List ℕ) (hneq : e ≠ []) (L : List (List ℕ))
  (he : List.Sorted (fun x1 x2 => x1 < x2) e)
  (hlength : e.length = L.length + 1) (hM : P.toFinset = Nat.primesBelow (Nat.sqrt (e.getLast hneq) + 1) )
  (hez : e[0]'(List.length_pos_iff.mpr hneq) ≠ 0)
  (hl : ∀ i, ∀ h : i + 1 < e.length , PrimeSieve (e[i]) (e[i + 1]) P = L[i]) (p : ℕ) :
  p ∈ List.foldr (fun x y => x ++ y) [] L ↔
    Nat.Prime p ∧ e[0]'(List.length_pos_iff.mpr hneq) < p ∧ p ≤ e.getLast hneq := by
  revert L
  induction' e with e es hes
  · exact fun L hlength hl ↦ False.elim (hneq rfl)
  · intro L hlength
    simp only [List.length_cons, add_lt_add_iff_right, List.getElem_cons_succ,
      List.getElem_cons_zero]
    intro hl
    match L with
    | [] =>
      simp only [List.length_cons, List.length_nil, zero_add, Nat.add_eq_right,
        List.length_eq_zero_iff] at hlength
      simp_rw [hlength]
      simp only [List.foldr_nil, List.not_mem_nil, List.getLast_singleton, false_iff, not_and,
        not_le, imp_self, implies_true]
    | (b :: bs) =>
      by_cases hess : es = []
      · simp[hess] at hlength
      · simp
        rw [List.getLast_cons hess]
        haveI : NeZero (e :: es).length := Nat.instNeZeroSucc
        have hlees : e <  es[0]'(List.length_pos_iff.mpr hess) := by
          convert List.Sorted.rel_get_of_lt he (a := 0) (b := ⟨1, by simp[List.length_pos_iff.mpr hess]⟩ ) ?_
          · refine Fin.val_pos_iff.mp ?_
            simp only [Nat.lt_one_iff, pos_of_gt]
        have hleql : es[0]'(List.length_pos_iff.mpr hess) ≤ es.getLast hess := by
          simp at he
          have : es.length ≠ 0 := by
            intro hc
            apply hess
            exact List.eq_nil_iff_length_eq_zero.mpr hc
          haveI : NeZero (es.length) := by exact { out := this }
          by_cases hesl : 1 < es.length
          · refine le_of_lt ?_
            convert List.Sorted.rel_get_of_lt he.2 (a := 0) (b := ⟨es.length - 1, by omega⟩ ) ?_
            · simp
              exact List.getLast_eq_getElem hess
            · refine Fin.val_pos_iff.mp ?_
              rw [tsub_pos_iff_lt]
              omega
          · refine le_of_eq ?_
            obtain ⟨b, hb⟩ := (List.length_eq_one_iff  (l := es) ).1 (by omega)
            simp_rw [hb]
            rfl
        have : e < p ∧ p ≤ es.getLast hess ↔ (e < p ∧ p ≤ es[0]'(List.length_pos_iff.mpr hess)) ∨ (es[0]'(List.length_pos_iff.mpr hess) < p ∧  p ≤ es.getLast hess) := by
          constructor
          · rintro ⟨he1, he2⟩
            omega
          · rintro (⟨he1, he2⟩ | ⟨he3, he4⟩)
            · refine ⟨he1, le_trans he2 hleql ⟩
            · refine ⟨lt_trans hlees he3, he4⟩
        rw [this, and_or_left]
        simp at he
        rw [List.getLast_cons hess] at hM
        simp at hlength
        have haux : (p ∈ List.foldr (fun x y ↦ x ++ y) [] bs ↔ Nat.Prime p ∧ es[0] < p ∧ p ≤ es.getLast hess) := by
          apply hes hess he.2 hM ?_ bs hlength
          intro i hi
          refine hl (i + 1) hi
          exact Nat.ne_zero_of_lt hlees
        have := hl 0 (by omega)
        simp only [List.getElem_cons_zero] at this
        refine or_congr ?_ haux
        rw [← this]
        refine PrimeSieve_mem_of_primesBelow e _ _ hleql ?_ P hM p
        simp at hez
        omega



def primes_below_100 := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


lemma primes_below_100_proof : primes_below_100.toFinset = Nat.primesBelow (Nat.sqrt 10000 + 1) := by
  refine list_eq_primesBelow ?_
  have heq : PrimeSieve 1 100 [2, 3, 5,7] = primes_below_100 := by rfl
  intro p
  rw [← PrimeSieve_mem_of_primesBelow 1 (Nat.sqrt 10000) (Nat.sqrt 10000) (by omega) (by omega) [2, 3, 5,7] ?_ p, sqrt10000, heq]
  rw [sqrt10000] ; rfl


#exit
--example : PrimeSieve 1 200 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97] =
--  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
--  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] := by
--  decide

def primesBelow10000 :=
  [[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199],
  [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397],
  [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599],
  [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797],
  [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997],
  [1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193],
  [1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399],
  [1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597],
  [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789],
  [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999],
  [2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179],
  [2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399],
  [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593],
  [2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797],
  [2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999],
  [3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191],
  [3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391],
  [3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593],
  [3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797],
  [3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989],
  [4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177],
  [4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397],
  [4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597],
  [4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799],
  [4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999],
  [5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197],
  [5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399],
  [5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591],
  [5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791],
  [5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987],
  [6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199],
  [6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397],
  [6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599],
  [6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793],
  [6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997],
  [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193],
  [7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393],
  [7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591],
  [7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793],
  [7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993],
  [8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191],
  [8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389],
  [8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599],
  [8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783],
  [8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999],
  [9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199],
   [9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397],
   [9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587],
   [9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791],
   [9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973]]


def e_interval_aux := [1, 200, 400, 600, 800, 1000, 1200, 1400, 1600, 1800, 2000, 2200,
  2400, 2600, 2800, 3000, 3200, 3400, 3600, 3800, 4000, 4200, 4400, 4600, 4800, 5000, 5200, 5400,
  5600, 5800, 6000, 6200, 6400, 6600, 6800, 7000, 7200, 7400, 7600, 7800, 8000, 8200, 8400, 8600, 8800, 9000, 9200, 9400, 9600, 9800,10000]

lemma e_sorted : List.Sorted (fun x1 x2 => x1 < x2) e_interval_aux := by decide

-- Reach max recursiond depth
/- lemma primesBelow10000_eq_primesBelow_aux_fldr :
  List.foldr (fun x y => x ++ y) [] primesBelow_aux = primesBelow10000 := rfl -/



lemma PB0 : PrimeSieve 1 200 primes_below_100 = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] := by sorry
lemma PB200 : PrimeSieve 200 400 primes_below_100 = [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397] := by sorry
lemma PB400 : PrimeSieve 400 600 primes_below_100 = [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599] := by sorry
lemma PB600 : PrimeSieve 600 800 primes_below_100 = [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797] := by sorry
lemma PB800 : PrimeSieve 800 1000 primes_below_100 = [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997] := by sorry
lemma PB1000 : PrimeSieve 1000 1200 primes_below_100 = [1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193] := by sorry
lemma PB1200 : PrimeSieve 1200 1400 primes_below_100 = [1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399] := by sorry
lemma PB1400 : PrimeSieve 1400 1600 primes_below_100 = [1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481, 1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597] := by sorry
lemma PB1600 : PrimeSieve 1600 1800 primes_below_100 = [1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789] :=by sorry
lemma PB1800 : PrimeSieve 1800 2000 primes_below_100 = [1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999] := by sorry
lemma PB2000 : PrimeSieve 2000 2200 primes_below_100 = [2003, 2011, 2017, 2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143, 2153, 2161, 2179] := by sorry
lemma PB2200 : PrimeSieve 2200 2400 primes_below_100 = [2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297, 2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399] := by sorry
lemma PB2400 : PrimeSieve 2400 2600 primes_below_100 = [2411, 2417, 2423, 2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593] := by sorry
lemma PB2600 : PrimeSieve 2600 2800 primes_below_100 = [2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713, 2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797] := by sorry
lemma PB2800 : PrimeSieve 2800 3000 primes_below_100 = [2801, 2803, 2819, 2833, 2837, 2843, 2851, 2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999] := by sorry
lemma PB3000 : PrimeSieve 3000 3200 primes_below_100 = [3001, 3011, 3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181, 3187, 3191] := by sorry
lemma PB3200 : PrimeSieve 3200 3400 primes_below_100 = [3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323, 3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391] := by sorry
lemma PB3400 : PrimeSieve 3400 3600 primes_below_100 = [3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467, 3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593] := by sorry
lemma PB3600 : PrimeSieve 3600 3800 primes_below_100 = [3607, 3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739, 3761, 3767, 3769, 3779, 3793, 3797] := by sorry
lemma PB3800 : PrimeSieve 3800 4000 primes_below_100 = [3803, 3821, 3823, 3833, 3847, 3851, 3853, 3863, 3877, 3881, 3889, 3907, 3911, 3917, 3919, 3923, 3929, 3931, 3943, 3947, 3967, 3989] := by sorry
lemma PB4000 : PrimeSieve 4000 4200 primes_below_100 = [4001, 4003, 4007, 4013, 4019, 4021, 4027, 4049, 4051, 4057, 4073, 4079, 4091, 4093, 4099, 4111, 4127, 4129, 4133, 4139, 4153, 4157, 4159, 4177] := by sorry
lemma PB4200 : PrimeSieve 4200 4400 primes_below_100 = [4201, 4211, 4217, 4219, 4229, 4231, 4241, 4243, 4253, 4259, 4261, 4271, 4273, 4283, 4289, 4297, 4327, 4337, 4339, 4349, 4357, 4363, 4373, 4391, 4397] := by sorry
lemma PB4400 : PrimeSieve 4400 4600 primes_below_100 = [4409, 4421, 4423, 4441, 4447, 4451, 4457, 4463, 4481, 4483, 4493, 4507, 4513, 4517, 4519, 4523, 4547, 4549, 4561, 4567, 4583, 4591, 4597] := by sorry
lemma PB4600 : PrimeSieve 4600 4800 primes_below_100 = [4603, 4621, 4637, 4639, 4643, 4649, 4651, 4657, 4663, 4673, 4679, 4691, 4703, 4721, 4723, 4729, 4733, 4751, 4759, 4783, 4787, 4789, 4793, 4799] := by sorry
lemma PB4800 : PrimeSieve 4800 5000 primes_below_100 = [4801, 4813, 4817, 4831, 4861, 4871, 4877, 4889, 4903, 4909, 4919, 4931, 4933, 4937, 4943, 4951, 4957, 4967, 4969, 4973, 4987, 4993, 4999] := by sorry
lemma PB5000 : PrimeSieve 5000 5200 primes_below_100 = [5003, 5009, 5011, 5021, 5023, 5039, 5051, 5059, 5077, 5081, 5087, 5099, 5101, 5107, 5113, 5119, 5147, 5153, 5167, 5171, 5179, 5189, 5197] :=by sorry
lemma PB5200 : PrimeSieve 5200 5400 primes_below_100 = [5209, 5227, 5231, 5233, 5237, 5261, 5273, 5279, 5281, 5297, 5303, 5309, 5323, 5333, 5347, 5351, 5381, 5387, 5393, 5399] := by sorry
lemma PB5400 : PrimeSieve 5400 5600 primes_below_100 = [5407, 5413, 5417, 5419, 5431, 5437, 5441, 5443, 5449, 5471, 5477, 5479, 5483, 5501, 5503, 5507, 5519, 5521, 5527, 5531, 5557, 5563, 5569, 5573, 5581, 5591] := by sorry
lemma PB5600 : PrimeSieve 5600 5800 primes_below_100 = [5623, 5639, 5641, 5647, 5651, 5653, 5657, 5659, 5669, 5683, 5689, 5693, 5701, 5711, 5717, 5737, 5741, 5743, 5749, 5779, 5783, 5791] := by sorry
lemma PB5800 : PrimeSieve 5800 6000 primes_below_100 = [5801, 5807, 5813, 5821, 5827, 5839, 5843, 5849, 5851, 5857, 5861, 5867, 5869, 5879, 5881, 5897, 5903, 5923, 5927, 5939, 5953, 5981, 5987] := by sorry
lemma PB6000 : PrimeSieve 6000 6200 primes_below_100 = [6007, 6011, 6029, 6037, 6043, 6047, 6053, 6067, 6073, 6079, 6089, 6091, 6101, 6113, 6121, 6131, 6133, 6143, 6151, 6163, 6173, 6197, 6199] := by sorry
lemma PB6200 : PrimeSieve 6200 6400 primes_below_100 = [6203, 6211, 6217, 6221, 6229, 6247, 6257, 6263, 6269, 6271, 6277, 6287, 6299, 6301, 6311, 6317, 6323, 6329, 6337, 6343, 6353, 6359, 6361, 6367, 6373, 6379, 6389, 6397] := by sorry
lemma PB6400 : PrimeSieve 6400 6600 primes_below_100 = [6421, 6427, 6449, 6451, 6469, 6473, 6481, 6491, 6521, 6529, 6547, 6551, 6553, 6563, 6569, 6571, 6577, 6581, 6599] := by sorry
lemma PB6600 : PrimeSieve 6600 6800 primes_below_100 = [6607, 6619, 6637, 6653, 6659, 6661, 6673, 6679, 6689, 6691, 6701, 6703, 6709, 6719, 6733, 6737, 6761, 6763, 6779, 6781, 6791, 6793] := by sorry
lemma PB6800 : PrimeSieve 6800 7000 primes_below_100 = [6803, 6823, 6827, 6829, 6833, 6841, 6857, 6863, 6869, 6871, 6883, 6899, 6907, 6911, 6917, 6947, 6949, 6959, 6961, 6967, 6971, 6977, 6983, 6991, 6997] := by sorry
lemma PB7000 : PrimeSieve 7000 7200 primes_below_100 = [7001, 7013, 7019, 7027, 7039, 7043, 7057, 7069, 7079, 7103, 7109, 7121, 7127, 7129, 7151, 7159, 7177, 7187, 7193] := by sorry
lemma PB7200 : PrimeSieve 7200 7400 primes_below_100 = [7207, 7211, 7213, 7219, 7229, 7237, 7243, 7247, 7253, 7283, 7297, 7307, 7309, 7321, 7331, 7333, 7349, 7351, 7369, 7393] :=by sorry
lemma PB7400 : PrimeSieve 7400 7600 primes_below_100 = [7411, 7417, 7433, 7451, 7457, 7459, 7477, 7481, 7487, 7489, 7499, 7507, 7517, 7523, 7529, 7537, 7541, 7547, 7549, 7559, 7561, 7573, 7577, 7583, 7589, 7591] := by sorry
lemma PB7600 : PrimeSieve 7600 7800 primes_below_100 = [7603, 7607, 7621, 7639, 7643, 7649, 7669, 7673, 7681, 7687, 7691, 7699, 7703, 7717, 7723, 7727, 7741, 7753, 7757, 7759, 7789, 7793] :=by sorry
lemma PB7800 : PrimeSieve 7800 8000 primes_below_100 = [7817, 7823, 7829, 7841, 7853, 7867, 7873, 7877, 7879, 7883, 7901, 7907, 7919, 7927, 7933, 7937, 7949, 7951, 7963, 7993] := by sorry
lemma PB8000 : PrimeSieve 8000 8200 primes_below_100 = [8009, 8011, 8017, 8039, 8053, 8059, 8069, 8081, 8087, 8089, 8093, 8101, 8111, 8117, 8123, 8147, 8161, 8167, 8171, 8179, 8191] := by sorry
lemma PB8200 : PrimeSieve 8200 8400 primes_below_100 = [8209, 8219, 8221, 8231, 8233, 8237, 8243, 8263, 8269, 8273, 8287, 8291, 8293, 8297, 8311, 8317, 8329, 8353, 8363, 8369, 8377, 8387, 8389] := by sorry
lemma PB8400 : PrimeSieve 8400 8600 primes_below_100 = [8419, 8423, 8429, 8431, 8443, 8447, 8461, 8467, 8501, 8513, 8521, 8527, 8537, 8539, 8543, 8563, 8573, 8581, 8597, 8599] := by sorry
lemma PB8600 : PrimeSieve 8600 8800 primes_below_100 = [8609, 8623, 8627, 8629, 8641, 8647, 8663, 8669, 8677, 8681, 8689, 8693, 8699, 8707, 8713, 8719, 8731, 8737, 8741, 8747, 8753, 8761, 8779, 8783] := by sorry
lemma PB8800 : PrimeSieve 8800 9000 primes_below_100 = [8803, 8807, 8819, 8821, 8831, 8837, 8839, 8849, 8861, 8863, 8867, 8887, 8893, 8923, 8929, 8933, 8941, 8951, 8963, 8969, 8971, 8999] := by sorry
lemma PB9000 : PrimeSieve 9000 9200 primes_below_100 = [9001, 9007, 9011, 9013, 9029, 9041, 9043, 9049, 9059, 9067, 9091, 9103, 9109, 9127, 9133, 9137, 9151, 9157, 9161, 9173, 9181, 9187, 9199] := by sorry
lemma PB9200 : PrimeSieve 9200 9400 primes_below_100 = [9203, 9209, 9221, 9227, 9239, 9241, 9257, 9277, 9281, 9283, 9293, 9311, 9319, 9323, 9337, 9341, 9343, 9349, 9371, 9377, 9391, 9397] := by sorry
lemma PB9400 : PrimeSieve 9400 9600 primes_below_100 = [9403, 9413, 9419, 9421, 9431, 9433, 9437, 9439, 9461, 9463, 9467, 9473, 9479, 9491, 9497, 9511, 9521, 9533, 9539, 9547, 9551, 9587] := by sorry
lemma PB9600 : PrimeSieve 9600 9800 primes_below_100 = [9601, 9613, 9619, 9623, 9629, 9631, 9643, 9649, 9661, 9677, 9679, 9689, 9697, 9719, 9721, 9733, 9739, 9743, 9749, 9767, 9769, 9781, 9787, 9791] := by sorry
lemma PB9800 : PrimeSieve 9800 10000 primes_below_100 = [9803, 9811, 9817, 9829, 9833, 9839, 9851, 9857, 9859, 9871, 9883, 9887, 9901, 9907, 9923, 9929, 9931, 9941, 9949, 9967, 9973] := by sorry



lemma primes_below_10000 (p : ℕ):
  p ∈ primesBelow10000.foldr (fun x y => x ++ y) [] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 10000 := by
  convert primes_below_append e_interval_aux primes_below_100 (by decide) primesBelow10000 (by decide) ?_ ?_ (by decide) ?_ p
  · rfl
  · exact primes_below_100_proof
  · intro i hi
    have : e_interval_aux.length = 51 := by decide
    have hif : i < 50 := by omega
    interval_cases i
    exact PB0 ; exact PB200 ; exact PB400 ; exact PB600 ; exact PB800 ; exact PB1000 ; exact PB1200
    exact PB1400 ; exact PB1600 ; exact PB1800 ; exact PB2000 ; exact PB2200 ; exact PB2400 ; exact PB2600
    exact PB2800 ; exact PB3000 ; exact PB3200 ; exact PB3400 ; exact PB3600 ; exact PB3800 ; exact PB4000
    exact PB4200 ; exact PB4400 ; exact PB4600 ; exact PB4800 ; exact PB5000 ; exact PB5200 ; exact PB5400
    exact PB5600 ; exact PB5800 ; exact PB6000 ; exact PB6200 ; exact PB6400 ; exact PB6600 ; exact PB6800
    exact PB7000 ; exact PB7200 ; exact PB7400 ; exact PB7600 ; exact PB7800 ; exact PB8000 ; exact PB8200
    exact PB8400 ; exact PB8600 ; exact PB8800 ; exact PB9000 ; exact PB9200 ; exact PB9400 ; exact PB9600
    exact PB9800

#print axioms primes_below_10000






#exit



#exit





















lemma L1P : PrimeSieve 1 200 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] =
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] := by
  decide

lemma L2P : PrimeSieve 200 400 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] =
  [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397] := by decide

lemma L3P : PrimeSieve 400 600 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] = [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
  563, 569, 571, 577, 587, 593, 599] := by decide

lemma L4P : PrimeSieve 600 800 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] = [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
  757, 761, 769, 773, 787, 797] := by decide

lemma L5P : PrimeSieve 800 1000 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] = [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967,
  971, 977, 983, 991, 997] := by decide





def L1000 := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
    113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
    241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379,
    383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521,
    523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661,
    673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
    829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991,
    997]


lemma primes_less_than_1000 : Nat.primesBelow 1001 = L1000.toFinset := by

  let L1 := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199]
  let L2 := [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397]
  let L3 := [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
  563, 569, 571, 577, 587, 593, 599]
  let L4 := [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
  757, 761, 769, 773, 787, 797]
  let L5 := [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967,
  971, 977, 983, 991, 997]
  have hL: L1000 = L1 ++ L2 ++ L3 ++ L4 ++ L5 := by rfl
  ext p
  rw [Nat.mem_primesBelow]
  have : 1 < p ∧ p < 1001 ↔
    (1 < p ∧ p ≤ 200) ∨ (200 < p ∧ p ≤ 400) ∨ (400 < p ∧ p ≤ 600) ∨ (600 < p ∧ p ≤ 800) ∨ (800 < p ∧ p ≤ 1000) := by omega
  have haux : p < 1001 ∧ Nat.Prime p ↔ (1 < p ∧ p < 1001) ∧ Nat.Prime p := by
    constructor
    · rintro ⟨h1, h2⟩ ; refine ⟨ ⟨Nat.Prime.one_lt h2 , h1⟩, h2 ⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩ ; exact And.symm ⟨h3, h2⟩
  rw [haux, this, or_and_right, or_and_right, or_and_right, or_and_right, hL]
  simp only [List.append_assoc, List.toFinset_append, Finset.mem_union, List.mem_toFinset]
  have hL1: L1 = PrimeSieve 1 200 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by rw [L1P]
  have hL2: L2 = PrimeSieve 200 400 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by rw [L2P]
  have hL3: L3 = PrimeSieve 400 600 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by rw [L3P]
  have hL4: L4 = PrimeSieve 600 800 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by rw [L4P]
  have hL5: L5 = PrimeSieve 800 1000 [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by rw [L5P]
  rw [hL1, hL2, hL3, hL4, hL5, PrimeSieve_mem_of_primesBelow _ 1000 _ (by decide) (by decide) _ example1
  , PrimeSieve_mem_of_primesBelow _ 1000 _ (by decide) (by decide) _ example1,
  PrimeSieve_mem_of_primesBelow _ 1000 _ (by decide) (by decide) _ example1,
  PrimeSieve_mem_of_primesBelow _ 1000 _ (by decide) (by decide) _ example1,
  PrimeSieve_mem_of_primesBelow _ 1000 _ (by decide) (by decide) _ example1]
  simp only [and_comm]











  --




















    --constructor








set_option pp.deepTerms true
#eval PrimeSieveNaive 1000
#eval PrimeSieve 1 1000 (0 :: PrimeSieveNaive 31)
#eval MultiplesBetween 3 12 105
#eval (0 :: PrimeSieveNaive 31)




/- example : PrimeSieveNaive 300 =
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
  241, 251, 257, 263, 269, 271, 277, 281, 283, 293] := by decide


example : PrimeSieve 1 380 =
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239,
  241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379] := by decide -/

#exit
lemma example1 : 0 :: PrimeSieveNaive 31 = [0, 2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] := by decide


-- Do not ask to recompute the square root (this is done via newton)
#exit
example : PrimeSieve 1 200 (0 :: PrimeSieveNaive 31) =
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109,
  113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199] := by
  decide

example : PrimeSieve 200 400 (0 :: PrimeSieveNaive 31) =
  [211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397] := by decide
--  decide

example : PrimeSieve 400 600 (0 :: PrimeSieveNaive 31) = [401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557,
  563, 569, 571, 577, 587, 593, 599] := by decide
--  decide

example : PrimeSieve 600 800 (0 :: PrimeSieveNaive 31) = [601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
  757, 761, 769, 773, 787, 797] := by decide

example : PrimeSieve 800 1000 (0 :: PrimeSieveNaive 31) = [809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967,
  971, 977, 983, 991, 997] := by decide
