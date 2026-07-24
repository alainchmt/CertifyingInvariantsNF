
import IdealArithmetic.Examples.NF3_1_29535_1.RI3_1_29535_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [8, 20, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 5, 14], [0, 31, 23], [0, 1]]
 g := ![![[28, 16, 25], [3, 11], [18, 18, 34], [35, 1], []], ![[0, 10, 11, 22], [20, 34], [10, 0, 36, 29], [18, 36], [7, 11]], ![[0, 20, 7, 31], [10, 4], [9, 1, 14, 6], [25, 25], [35, 11]]]
 h' := ![![[35, 5, 14], [29, 14, 5], [4, 11, 23], [16, 32, 21], [0, 0, 1], [0, 1]], ![[0, 31, 23], [0, 14, 18], [7, 12, 16], [7, 21, 26], [22, 11, 31], [35, 5, 14]], ![[0, 1], [35, 9, 14], [2, 14, 35], [19, 21, 27], [16, 26, 5], [0, 31, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 14], []]
 b := ![[], [17, 32, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [8, 20, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1147, -185, -185]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, -5, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -38, -15]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-137, -38, -15]] 
 ![![41, 0, 0], ![0, 41, 0], ![31, 8, 1]] where
  M :=![![![-137, -38, -15], ![-495, -137, -53], ![-1749, -495, -190]]]
  hmulB := by decide  
  f := ![![![5, -5, 1]], ![![33, 5, -4]], ![![7, -2, 0]]]
  g := ![![![8, 2, -15], ![28, 7, -53], ![101, 25, -190]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [31, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 40], [0, 1]]
 g := ![![[2, 4], [4], [37], [36, 31], [1]], ![[0, 37], [4], [37], [0, 10], [1]]]
 h' := ![![[20, 40], [40, 39], [0, 39], [32, 23], [10, 20], [0, 1]], ![[0, 1], [0, 2], [1, 2], [0, 18], [0, 21], [20, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [28, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [31, 21, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88, 259, 58]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46, -5, 58]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 5, -1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-5, 5, -1]] 
 ![![41, 0, 0], ![32, 1, 0], ![1, 0, 1]] where
  M :=![![![-5, 5, -1], ![-33, -5, 4], ![132, -33, -1]]]
  hmulB := by decide  
  f := ![![![137, 38, 15]], ![![119, 33, 13]], ![![46, 13, 5]]]
  g := ![![![-4, 5, -1], ![3, -5, 4], ![29, -33, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-137, -38, -15]] ![![-5, 5, -1]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [35, 23, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 15, 18], [4, 27, 25], [0, 1]]
 g := ![![[40, 18, 38], [3, 13, 24], [36, 13], [33, 23, 1], []], ![[24, 4, 9, 28], [12, 16, 40, 37], [41, 35], [10, 7, 17, 7], [37, 23]], ![[6, 10, 8, 14], [35, 30, 42, 38], [40, 15], [28, 29, 37, 35], [30, 23]]]
 h' := ![![[19, 15, 18], [24, 5, 9], [23, 30, 29], [6, 27, 23], [0, 0, 1], [0, 1]], ![[4, 27, 25], [12, 19, 32], [38, 2, 33], [21, 23, 32], [12, 32, 27], [19, 15, 18]], ![[0, 1], [26, 19, 2], [42, 11, 24], [25, 36, 31], [41, 11, 15], [4, 27, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 20], []]
 b := ![[], [40, 3, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [35, 23, 20, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-177074, 4042, -9718]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4118, 94, -226]
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

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 3, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![10, 3, 1]] 
 ![![47, 0, 0], ![27, 1, 0], ![23, 0, 1]] where
  M :=![![![10, 3, 1], ![33, 10, 4], ![132, 33, 14]]]
  hmulB := by decide  
  f := ![![![8, -9, 2]], ![![6, -5, 1]], ![![-1, -3, 1]]]
  g := ![![![-2, 3, 1], ![-7, 10, 4], ![-23, 33, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 5, 2]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![19, 5, 2]] 
 ![![47, 0, 0], ![31, 1, 0], ![26, 0, 1]] where
  M :=![![![19, 5, 2], ![66, 19, 7], ![231, 66, 26]]]
  hmulB := by decide  
  f := ![![![32, 2, -3]], ![![19, 2, -2]], ![![17, -1, -1]]]
  g := ![![![-4, 5, 2], ![-15, 19, 7], ![-53, 66, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 10, -1]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![-23, 10, -1]] 
 ![![47, 0, 0], ![35, 1, 0], ![44, 0, 1]] where
  M :=![![![-23, 10, -1], ![-33, -23, 9], ![297, -33, -14]]]
  hmulB := by decide  
  f := ![![![-619, -173, -67]], ![![-508, -142, -55]], ![![-748, -209, -81]]]
  g := ![![![-7, 10, -1], ![8, -23, 9], ![44, -33, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![10, 3, 1]] ![![19, 5, 2]]
  ![![619, 173, 67]] where
 M := ![![![619, 173, 67]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![619, 173, 67]] ![![-23, 10, -1]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)


lemma PB49I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 48 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 48 (by omega)

def PB49I1 : PrimesBelowBoundCertificateInterval O 31 48 49 where
  m := 4
  g := ![1, 2, 1, 3]
  P := ![37, 41, 43, 47]
  hP := PB49I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1, I47N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![47, 47, 47]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
  β := ![I41N1, I47N0, I47N1, I47N2]
  Il := ![[], [I41N1], [], [I47N0, I47N1, I47N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
