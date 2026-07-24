
import IdealArithmetic.Examples.NF3_1_108471_1.RI3_1_108471_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [81, 79, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 65, 30], [3, 17, 53], [0, 1]]
 g := ![![[74, 45, 41], [56, 55, 65], [7, 77], [58, 49], [63, 68, 1], []], ![[21, 2, 4, 1], [80, 69, 18, 28], [27, 9], [23, 7], [41, 41, 58, 38], [28, 70]], ![[1, 44, 14, 57], [71, 15, 1, 58], [13, 48], [48, 31], [37, 33, 12, 74], [5, 70]]]
 h' := ![![[65, 65, 30], [29, 18, 46], [79, 16, 27], [56, 0, 34], [43, 56, 76], [0, 0, 1], [0, 1]], ![[3, 17, 53], [4, 74, 77], [8, 25, 26], [28, 56, 80], [27, 79, 67], [48, 70, 17], [65, 65, 30]], ![[0, 1], [44, 74, 43], [59, 42, 30], [38, 27, 52], [78, 31, 23], [19, 13, 65], [3, 17, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 4], []]
 b := ![[], [67, 3, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [81, 79, 15, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-387444, 147657, -40006]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4668, 1779, -482]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13037774, 3993761, -1620550]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-13037774, 3993761, -1620550]] 
 ![![89, 0, 0], ![34, 1, 0], ![85, 0, 1]] where
  M :=![![![-13037774, 3993761, -1620550], ![121541250, -37230796, 15107155], ![-177990825, 54522560, -22123641]]]
  hmulB := by decide  
  f := ![![![68564, 4199, -2155]], ![![28009, 2038, -660]], ![![63760, 4700, -1461]]]
  g := ![![![-124482, 3993761, -1620550], ![1160451, -37230796, 15107155], ![-1699420, 54522560, -22123641]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-33, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-33, 1, 0]] 
 ![![89, 0, 0], ![56, 1, 0], ![36, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-33, 1, 0], ![0, -35, 5], ![-75, 10, -30]]]
  hmulB := by decide  
  f := ![![![1354, -41, 0], ![3649, 0, 0]], ![![892, -27, 0], ![2404, 0, 0]], ![![564, -10, -1], ![1520, 18, 0]]]
  g := ![![![1, 0, 0], ![-56, 89, 0], ![-36, 0, 89]], ![![-1, 1, 0], ![20, -35, 5], ![5, 10, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-2, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-2, 1, 0]] 
 ![![89, 0, 0], ![87, 1, 0], ![34, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-2, 1, 0], ![0, -4, 5], ![-75, 10, 1]]]
  hmulB := by decide  
  f := ![![![99, -49, 0], ![4361, 0, 0]], ![![97, -48, 0], ![4273, 0, 0]], ![![38, -18, -1], ![1674, 18, 0]]]
  g := ![![![1, 0, 0], ![-87, 89, 0], ![-34, 0, 89]], ![![-1, 1, 0], ![2, -4, 5], ![-11, 10, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-13037774, 3993761, -1620550]] ![![89, 0, 0], ![-33, 1, 0]]
  ![![89, 0, 0], ![7, -18, 1]] where
 M := ![![![-1160361886, 355444729, -144228950], ![551787792, -169024909, 68585305]]]
 hmul := by decide  
 g := ![![![![-12898726, 3636209, -1600686], ![-1767896, 0, 0]], ![![6133738, -1729121, 761175], ![840730, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![7, -18, 1]] ![![89, 0, 0], ![-2, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-178, 89, 0]], ![![623, -1602, 89], ![-89, 89, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-2, 1, 0]]], ![![![7, -18, 1]], ![![-1, 1, -1]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)


lemma PB94I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 93 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 93 (by omega)

def PB94I2 : PrimesBelowBoundCertificateInterval O 79 93 94 where
  m := 2
  g := ![1, 3]
  P := ![83, 89]
  hP := PB94I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![89, 89, 89]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
  β := ![I89N0, I89N1, I89N2]
  Il := ![[], [I89N0, I89N1, I89N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
