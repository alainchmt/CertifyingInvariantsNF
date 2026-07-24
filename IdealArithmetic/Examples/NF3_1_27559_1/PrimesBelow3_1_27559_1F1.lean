
import IdealArithmetic.Examples.NF3_1_27559_1.RI3_1_27559_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 5, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![6, 5, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![6, 5, 1]] where
  M :=![![![6, 5, 1], ![-21, 1, 15], ![-98, -57, -4]]]
  hmulB := by decide  
  f := ![![![-23, 1, -2]], ![![42, -2, 3]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![-3, -2, 15], ![-2, -1, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [22, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 36], [0, 1]]
 g := ![![[22, 9], [33], [12, 36], [9], [1]], ![[32, 28], [33], [15, 1], [9], [1]]]
 h' := ![![[34, 36], [2, 3], [32, 12], [27, 31], [15, 34], [0, 1]], ![[0, 1], [30, 34], [33, 25], [8, 6], [24, 3], [34, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [8, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [22, 3, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-223, -377, -253]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35, 24, -253]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 1, -2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-23, 1, -2]] 
 ![![37, 0, 0], ![22, 1, 0], ![4, 0, 1]] where
  M :=![![![-23, 1, -2], ![42, -2, 3], ![-35, 4, -3]]]
  hmulB := by decide  
  f := ![![![6, 5, 1]], ![![3, 3, 1]], ![![-2, -1, 0]]]
  g := ![![![-1, 1, -2], ![2, -2, 3], ![-3, 4, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![6, 5, 1]] ![![-23, 1, -2]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -14, 7]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-37, -14, 7]] 
 ![![41, 0, 0], ![0, 41, 0], ![24, 39, 1]] where
  M :=![![![-37, -14, 7], ![-147, -121, -42], ![343, 91, -107]]]
  hmulB := by decide  
  f := ![![![-409, 21, -35]], ![![735, -38, 63]], ![![443, -23, 38]]]
  g := ![![![-5, -7, 7], ![21, 37, -42], ![71, 104, -107]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [14, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 40], [0, 1]]
 g := ![![[3, 32], [1], [40], [27, 1], [1]], ![[12, 9], [1], [40], [26, 40], [1]]]
 h' := ![![[40, 40], [32, 14], [13, 40], [32, 32], [27, 40], [0, 1]], ![[0, 1], [18, 27], [14, 1], [0, 9], [28, 1], [40, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [3, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [14, 1, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-21, -275, -252]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147, 233, -252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-409, 21, -35]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-409, 21, -35]] 
 ![![41, 0, 0], ![6, 1, 0], ![27, 0, 1]] where
  M :=![![![-409, 21, -35], ![735, -38, 63], ![-686, 35, -59]]]
  hmulB := by decide  
  f := ![![![-37, -14, 7]], ![![-9, -5, 0]], ![![-16, -7, 2]]]
  g := ![![![10, 21, -35], ![-18, -38, 63], ![17, 35, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-37, -14, 7]] ![![-409, 21, -35]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [31, 17, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 11, 24], [29, 31, 19], [0, 1]]
 g := ![![[37, 37, 25], [37, 23, 17], [13, 15], [26, 0, 1], []], ![[41, 17, 9, 1], [26, 18, 24, 1], [20, 4], [18, 22, 3, 16], [12, 17]], ![[2, 24, 12, 12], [8, 4, 35, 5], [4, 14], [28, 30, 8, 20], [17, 17]]]
 h' := ![![[14, 11, 24], [14, 8, 5], [19, 39, 24], [11, 31, 12], [0, 0, 1], [0, 1]], ![[29, 31, 19], [20, 37, 3], [39, 38, 3], [10, 38, 41], [39, 7, 31], [14, 11, 24]], ![[0, 1], [10, 41, 35], [0, 9, 16], [34, 17, 33], [13, 36, 11], [29, 31, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 32], []]
 b := ![[], [39, 23, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [31, 17, 0, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-264622, 1204, -10492]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6154, 28, -244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀



lemma PB47I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 46 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 46 (by omega)

def PB47I1 : PrimesBelowBoundCertificateInterval O 31 46 47 where
  m := 3
  g := ![2, 2, 1]
  P := ![37, 41, 43]
  hP := PB47I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![79507]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
  β := ![I37N1, I41N1]
  Il := ![[I37N1], [I41N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
