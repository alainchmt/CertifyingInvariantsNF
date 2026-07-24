
import IdealArithmetic.Examples.NF3_1_42423_4.RI3_1_42423_4
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [11, 12, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 28, 15], [18, 8, 22], [0, 1]]
 g := ![![[18, 9, 9], [11, 4], [19, 35, 21], [5, 1], []], ![[34, 16, 27, 35], [32, 26], [5, 1, 22, 15], [30, 27], [4, 3]], ![[19, 35, 0, 35], [23, 33], [35, 9, 25, 20], [14, 7], [34, 3]]]
 h' := ![![[24, 28, 15], [11, 6, 34], [13, 7, 2], [19, 3, 13], [0, 0, 1], [0, 1]], ![[18, 8, 22], [2, 5, 29], [24, 21, 10], [14, 1, 1], [14, 5, 8], [24, 28, 15]], ![[0, 1], [10, 26, 11], [2, 9, 25], [15, 33, 23], [24, 32, 28], [18, 8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 27], []]
 b := ![[], [7, 5, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [11, 12, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2849, 3996, -4107]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77, 108, -111]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![22, -4, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![22, -4, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![22, 37, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![22, -4, 1], ![42, 11, -13], ![-175, 43, 20]]]
  hmulB := by decide  
  f := ![![![-21, 4, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -37, 41]], ![![0, -1, 1], ![8, 12, -13], ![-15, -17, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [27, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 40], [0, 1]]
 g := ![![[10, 31], [36], [9], [18, 2], [1]], ![[4, 10], [36], [9], [11, 39], [1]]]
 h' := ![![[17, 40], [16, 21], [39, 35], [6, 38], [14, 17], [0, 1]], ![[0, 1], [4, 20], [19, 6], [37, 3], [16, 24], [17, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [1, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [27, 24, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1508, 960, -240]
  a := ![-3, 0, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![92, 240, -240]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![13, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![13, 1, 0]] 
 ![![41, 0, 0], ![13, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![13, 1, 0], ![-1, 14, 3], ![38, -7, 12]]]
  hmulB := by decide  
  f := ![![![-107, 1329, 285], ![41, -3895, 0]], ![![-30, 420, 90], ![1, -1230, 0]], ![![-51, 681, 146], ![9, -1995, 0]]]
  g := ![![![1, 0, 0], ![-13, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-6, 14, 3], ![-3, -7, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![22, -4, 1]] ![![41, 0, 0], ![13, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![533, 41, 0]], ![![902, -164, 41], ![328, -41, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![13, 1, 0]]], ![![![22, -4, 1]], ![![8, -1, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-4, -7, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-4, -7, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![39, 36, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-4, -7, 1], ![45, -18, -22], ![-289, 64, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -36, 43]], ![![-1, -1, 1], ![21, 18, -22], ![-4, 4, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 42], [0, 1]]
 g := ![![[22, 13], [33, 41], [23], [18, 25], [1]], ![[0, 30], [0, 2], [23], [22, 18], [1]]]
 h' := ![![[38, 42], [14, 20], [6, 27], [35, 18], [33, 38], [0, 1]], ![[0, 1], [0, 23], [0, 16], [31, 25], [15, 5], [38, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [29, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 5, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![218561, 10951, -23691]
  a := ![1, -64, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26570, 20089, -23691]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-21, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-21, 1, 0]] 
 ![![43, 0, 0], ![22, 1, 0], ![3, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-21, 1, 0], ![-1, -20, 3], ![38, -7, -22]]]
  hmulB := by decide  
  f := ![![![25, 480, -72], ![0, 1032, 0]], ![![13, 240, -36], ![1, 516, 0]], ![![12, 33, -5], ![21, 72, 0]]]
  g := ![![![1, 0, 0], ![-22, 43, 0], ![-3, 0, 43]], ![![-1, 1, 0], ![10, -20, 3], ![6, -7, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-4, -7, 1]] ![![43, 0, 0], ![-21, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-903, 43, 0]], ![![-172, -301, 43], ![129, 129, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-21, 1, 0]]], ![![![-4, -7, 1]], ![![3, 3, -1]]]]
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
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [35, 29, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 0, 11], [27, 46, 36], [0, 1]]
 g := ![![[15, 45, 21], [23, 42, 4], [38, 10, 3], [3, 19, 1], []], ![[35, 44, 24, 39], [7, 18, 18, 13], [23, 32, 22, 33], [1, 23, 23, 11], [43, 27]], ![[39, 4, 40, 21], [19, 7, 43, 9], [43, 4], [24, 17], [18, 27]]]
 h' := ![![[39, 0, 11], [41, 33, 16], [33, 32, 45], [36, 0, 35], [0, 0, 1], [0, 1]], ![[27, 46, 36], [33, 37, 18], [27, 13, 25], [32, 31, 12], [16, 17, 46], [39, 0, 11]], ![[0, 1], [25, 24, 13], [41, 2, 24], [23, 16], [5, 30], [27, 46, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 11], []]
 b := ![[], [1, 35, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [35, 29, 28, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-346813, 123610, -24769]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7379, 2630, -527]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-19, -24, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-19, -24, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![34, 29, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-19, -24, 1], ![62, -50, -73], ![-935, 183, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-34, -29, 53]], ![![-1, -1, 1], ![48, 39, -73], ![-17, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [52, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 52], [0, 1]]
 g := ![![[51, 52], [6], [26, 24], [25], [51, 1]], ![[0, 1], [6], [31, 29], [25], [49, 52]]]
 h' := ![![[51, 52], [46, 23], [26, 18], [29, 36], [51, 5], [0, 1]], ![[0, 1], [0, 30], [43, 35], [10, 17], [41, 48], [51, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [13, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [52, 2, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![300, 47, -66]
  a := ![1, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 37, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![20, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![20, 1, 0]] 
 ![![53, 0, 0], ![20, 1, 0], ![1, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![20, 1, 0], ![-1, 21, 3], ![38, -7, 19]]]
  hmulB := by decide  
  f := ![![![-107, 1847, 264], ![53, -4664, 0]], ![![-33, 693, 99], ![1, -1749, 0]], ![![-19, 34, 5], ![46, -88, 0]]]
  g := ![![![1, 0, 0], ![-20, 53, 0], ![-1, 0, 53]], ![![0, 1, 0], ![-8, 21, 3], ![3, -7, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-19, -24, 1]] ![![53, 0, 0], ![20, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1060, 53, 0]], ![![-1007, -1272, 53], ![-318, -530, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![20, 1, 0]]], ![![![-19, -24, 1]], ![![-6, -10, -1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)


lemma PB59I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 58 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 58 (by omega)

def PB59I1 : PrimesBelowBoundCertificateInterval O 31 58 59 where
  m := 5
  g := ![1, 2, 2, 1, 2]
  P := ![37, 41, 43, 47, 53]
  hP := PB59I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
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
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
  β := ![I41N1, I43N1, I53N1]
  Il := ![[], [I41N1], [I43N1], [], [I53N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
