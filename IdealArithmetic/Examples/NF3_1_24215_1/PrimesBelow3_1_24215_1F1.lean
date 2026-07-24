
import IdealArithmetic.Examples.NF3_1_24215_1.RI3_1_24215_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 6, 9]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![157, 6, 9]] 
 ![![37, 0, 0], ![0, 37, 0], ![1, 13, 1]] where
  M :=![![![157, 6, 9], ![117, 4, 6], ![78, 15, 4]]]
  hmulB := by decide  
  f := ![![![-2, 3, 0]], ![![0, -2, 3]], ![![1, -2, 1]]]
  g := ![![![4, -3, 9], ![3, -2, 6], ![2, -1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [26, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 36], [0, 1]]
 g := ![![[23, 10], [1], [12, 3], [36], [1]], ![[0, 27], [1], [31, 34], [36], [1]]]
 h' := ![![[31, 36], [8, 26], [21, 36], [36, 22], [11, 31], [0, 1]], ![[0, 1], [0, 11], [27, 1], [15, 15], [10, 6], [31, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [36, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [26, 6, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52, -27, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 7, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -3, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![2, -3, 0]] 
 ![![37, 0, 0], ![24, 1, 0], ![16, 0, 1]] where
  M :=![![![2, -3, 0], ![0, 2, -3], ![-39, 51, 2]]]
  hmulB := by decide  
  f := ![![![-157, -6, -9]], ![![-105, -4, -6]], ![![-70, -3, -4]]]
  g := ![![![2, -3, 0], ![0, 2, -3], ![-35, 51, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![157, 6, 9]] ![![2, -3, 0]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [24, 35, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 35, 30], [15, 5, 11], [0, 1]]
 g := ![![[5, 19, 33], [24, 18], [17, 9], [2, 18, 1], []], ![[27, 12, 31, 3], [4, 18], [25, 5], [24, 29, 2, 12], [14, 39]], ![[16, 10, 5, 11], [15, 31], [33, 18], [9, 15, 13, 27], [33, 39]]]
 h' := ![![[3, 35, 30], [16, 27, 22], [10, 26, 10], [34, 31, 38], [0, 0, 1], [0, 1]], ![[15, 5, 11], [37, 23, 18], [16, 25, 10], [1, 18, 13], [1, 14, 5], [3, 35, 30]], ![[0, 1], [1, 32, 1], [19, 31, 21], [27, 33, 31], [7, 27, 35], [15, 5, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 24], []]
 b := ![[], [18, 13, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [24, 35, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13284, -20500, 3485]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![324, -500, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11916, -503, -679]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-11916, -503, -679]] 
 ![![43, 0, 0], ![0, 43, 0], ![9, 11, 1]] where
  M :=![![![-11916, -503, -679], ![-8827, -373, -503], ![-6539, -276, -373]]]
  hmulB := by decide  
  f := ![![![-7, 5, 6]], ![![78, -109, 5]], ![![20, -27, 0]]]
  g := ![![![-135, 162, -679], ![-100, 120, -503], ![-74, 89, -373]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [14, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 42], [0, 1]]
 g := ![![[5, 40], [22, 4], [31], [36, 41], [1]], ![[0, 3], [0, 39], [31], [4, 2], [1]]]
 h' := ![![[16, 42], [36, 30], [11, 2], [12, 26], [29, 16], [0, 1]], ![[0, 1], [0, 13], [0, 41], [41, 17], [27, 27], [16, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [19, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [14, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2356, -54, 85]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![37, -23, 85]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -5, -6]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![7, -5, -6]] 
 ![![43, 0, 0], ![32, 1, 0], ![8, 0, 1]] where
  M :=![![![7, -5, -6], ![-78, 109, -5], ![-65, 7, 109]]]
  hmulB := by decide  
  f := ![![![11916, 503, 679]], ![![9073, 383, 517]], ![![2369, 100, 135]]]
  g := ![![![5, -5, -6], ![-82, 109, -5], ![-27, 7, 109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-11916, -503, -679]] ![![7, -5, -6]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)


lemma PB45I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 44 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 44 (by omega)

def PB45I1 : PrimesBelowBoundCertificateInterval O 31 44 45 where
  m := 3
  g := ![2, 1, 2]
  P := ![37, 41, 43]
  hP := PB45I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
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
    · exact ![68921]
    · exact ![1849, 43]
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
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
  β := ![I37N1, I43N1]
  Il := ![[I37N1], [], [I43N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
