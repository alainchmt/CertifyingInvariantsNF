
import IdealArithmetic.Examples.NF3_1_732108_1.RI3_1_732108_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [3, 0, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 28, 36], [28, 8, 1], [0, 1]]
 g := ![![[11, 4, 34], [22, 28], [3, 18, 33], [32, 1], []], ![[28, 3], [32, 26], [27, 30, 1, 9], [34, 27], [13, 1]], ![[30, 3, 11, 34], [12, 7], [15, 33, 22, 36], [21, 7], [11, 1]]]
 h' := ![![[4, 28, 36], [15, 20, 21], [28, 23, 18], [15, 34, 25], [0, 0, 1], [0, 1]], ![[28, 8, 1], [19, 21], [2, 34, 10], [20, 2, 18], [14, 36, 8], [4, 28, 36]], ![[0, 1], [29, 33, 16], [19, 17, 9], [21, 1, 31], [11, 1, 28], [28, 8, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 23], []]
 b := ![[], [14, 27, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [3, 0, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![172716, -131202, -134865]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4668, -3546, -3645]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![5, -3, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![5, -3, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![5, 38, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![5, -3, 1], ![43, -34, -16], ![-120, 113, -24]]]
  hmulB := by decide  
  f := ![![![-4, 3, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -38, 41]], ![![0, -1, 1], ![3, 14, -16], ![0, 25, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [34, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 40], [0, 1]]
 g := ![![[21, 16], [31], [5], [15, 2], [1]], ![[36, 25], [31], [5], [22, 39], [1]]]
 h' := ![![[24, 40], [30, 37], [31, 21], [23, 13], [7, 24], [0, 1]], ![[0, 1], [16, 4], [2, 20], [7, 28], [9, 17], [24, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [9, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [34, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![446, 454, -4552]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![566, 4230, -4552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![16, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![16, 1, 0]] 
 ![![41, 0, 0], ![16, 1, 0], ![24, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![16, 1, 0], ![-2, 18, 5], ![37, -33, 15]]]
  hmulB := by decide  
  f := ![![![745, -7131, -1980], ![123, 16236, 0]], ![![276, -2774, -770], ![83, 6314, 0]], ![![424, -4175, -1159], ![103, 9504, 0]]]
  g := ![![![1, 0, 0], ![-16, 41, 0], ![-24, 0, 41]], ![![0, 1, 0], ![-10, 18, 5], ![5, -33, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![5, -3, 1]] ![![41, 0, 0], ![16, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![656, 41, 0]], ![![205, -123, 41], ![123, -82, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![16, 1, 0]]], ![![![5, -3, 1]], ![![3, -2, 0]]]]
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


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [34, 18, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 1, 32], [21, 41, 11], [0, 1]]
 g := ![![[33, 6, 11], [9, 22, 14], [37, 14], [13, 17, 1], []], ![[40, 7, 23, 7], [22, 27, 38, 33], [34, 35], [0, 0, 42, 42], [14, 35]], ![[3, 14, 32, 31], [36, 0, 21, 13], [14, 11], [37, 17, 7, 11], [35, 35]]]
 h' := ![![[39, 1, 32], [38, 9, 21], [4, 28, 33], [31, 5, 10], [0, 0, 1], [0, 1]], ![[21, 41, 11], [17, 3, 31], [20, 37, 13], [12, 39, 11], [13, 12, 41], [39, 1, 32]], ![[0, 1], [21, 31, 34], [41, 21, 40], [42, 42, 22], [25, 31, 1], [21, 41, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 28], []]
 b := ![[], [39, 9, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [34, 18, 26, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11703150900, -9126330234, -7856970062]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![272166300, -212240238, -182720234]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![1, -8, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![1, -8, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![1, 39, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![1, -8, 1], ![53, -48, -41], ![-305, 278, -23]]]
  hmulB := by decide  
  f := ![![![0, 0, 1], ![-6, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -39, 47]], ![![0, -1, 1], ![2, 33, -41], ![-6, 25, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [43, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 46], [0, 1]]
 g := ![![[3, 8], [34, 32], [28, 8], [38, 3], [1]], ![[5, 39], [42, 15], [30, 39], [27, 44], [1]]]
 h' := ![![[12, 46], [42, 14], [18, 19], [11, 14], [4, 12], [0, 1]], ![[0, 1], [22, 33], [11, 28], [38, 33], [7, 35], [12, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [13, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [43, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1593, -477, -5175]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![144, 4284, -5175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-6, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-6, 1, 0]] 
 ![![47, 0, 0], ![41, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-6, 1, 0], ![-2, -4, 5], ![37, -33, -7]]]
  hmulB := by decide  
  f := ![![![3091, 6245, -7800], ![-235, 73320, 0]], ![![2697, 5444, -6800], ![-187, 63920, 0]], ![![1513, 3056, -3817], ![-112, 35880, 0]]]
  g := ![![![1, 0, 0], ![-41, 47, 0], ![-23, 0, 47]], ![![-1, 1, 0], ![1, -4, 5], ![33, -33, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![1, -8, 1]] ![![47, 0, 0], ![-6, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![-282, 47, 0]], ![![47, -376, 47], ![47, 0, -47]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![-6, 1, 0]]], ![![![1, -8, 1]], ![![1, 0, -1]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![26, -20, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![26, -20, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![26, 33, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![26, -20, 1], ![77, -47, -101], ![-749, 674, 14]]]
  hmulB := by decide  
  f := ![![![-25, 20, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -33, 53]], ![![0, -1, 1], ![51, 62, -101], ![-21, 4, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 52], [0, 1]]
 g := ![![[15, 46], [15], [5, 16], [25], [40, 1]], ![[0, 7], [15], [9, 37], [25], [27, 52]]]
 h' := ![![[40, 52], [47, 24], [31, 42], [20, 4], [36, 48], [0, 1]], ![[0, 1], [0, 29], [15, 11], [21, 49], [48, 5], [40, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [31, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 13, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![912, -673, -870]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![444, 529, -870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-5, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-5, 1, 0]] 
 ![![53, 0, 0], ![48, 1, 0], ![39, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-5, 1, 0], ![-2, -3, 5], ![37, -33, -6]]]
  hmulB := by decide  
  f := ![![![-1417, -2144, 3570], ![106, -37842, 0]], ![![-1281, -1940, 3230], ![107, -34238, 0]], ![![-1041, -1578, 2627], ![96, -27846, 0]]]
  g := ![![![1, 0, 0], ![-48, 53, 0], ![-39, 0, 53]], ![![-1, 1, 0], ![-1, -3, 5], ![35, -33, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![26, -20, 1]] ![![53, 0, 0], ![-5, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-265, 53, 0]], ![![1378, -1060, 53], ![-53, 53, -106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-5, 1, 0]]], ![![![26, -20, 1]], ![![-1, 1, -2]]]]
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
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![27, 22, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![27, 22, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![27, 22, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![27, 22, 1], ![-7, 38, 109], ![805, -712, -27]]]
  hmulB := by decide  
  f := ![![![-26, -22, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -22, 59]], ![![0, 0, 1], ![-50, -40, 109], ![26, -2, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [32, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 58], [0, 1]]
 g := ![![[32, 57], [23, 51], [12], [11, 16], [38, 1]], ![[15, 2], [14, 8], [12], [29, 43], [17, 58]]]
 h' := ![![[38, 58], [31, 36], [33, 13], [2, 22], [23, 55], [0, 1]], ![[0, 1], [42, 23], [55, 46], [12, 37], [48, 4], [38, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [48, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [32, 21, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11960, -9845, 349]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, -297, 349]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![9, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![9, 1, 0]] 
 ![![59, 0, 0], ![9, 1, 0], ![27, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![9, 1, 0], ![-2, 11, 5], ![37, -33, 8]]]
  hmulB := by decide  
  f := ![![![360, -2025, -920], ![59, 10856, 0]], ![![47, -309, -140], ![60, 1652, 0]], ![![162, -927, -421], ![45, 4968, 0]]]
  g := ![![![1, 0, 0], ![-9, 59, 0], ![-27, 0, 59]], ![![0, 1, 0], ![-4, 11, 5], ![2, -33, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![27, 22, 1]] ![![59, 0, 0], ![9, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![531, 59, 0]], ![![1593, 1298, 59], ![236, 236, 118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![9, 1, 0]]], ![![![27, 22, 1]], ![![4, 4, 2]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![0, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![0, 1, 0]] 
 ![![61, 0, 0], ![0, 1, 0], ![24, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![0, 1, 0], ![-2, 2, 5], ![37, -33, -1]]]
  hmulB := by decide  
  f := ![![![-61, 61, 155], ![61, -1891, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-24, 24, 61], ![24, -744, 0]]]
  g := ![![![1, 0, 0], ![0, 61, 0], ![-24, 0, 61]], ![![0, 1, 0], ![-2, 2, 5], ![1, -33, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![22, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![22, 1, 0]] 
 ![![61, 0, 0], ![22, 1, 0], ![16, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![22, 1, 0], ![-2, 24, 5], ![37, -33, 21]]]
  hmulB := by decide  
  f := ![![![657, -8402, -1750], ![122, 21350, 0]], ![![230, -3025, -630], ![62, 7686, 0]], ![![168, -2204, -459], ![44, 5600, 0]]]
  g := ![![![1, 0, 0], ![-22, 61, 0], ![-16, 0, 61]], ![![0, 1, 0], ![-10, 24, 5], ![7, -33, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-23, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-23, 1, 0]] 
 ![![61, 0, 0], ![38, 1, 0], ![25, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-23, 1, 0], ![-2, -21, 5], ![37, -33, -24]]]
  hmulB := by decide  
  f := ![![![3269, 36739, -8745], ![-610, 106689, 0]], ![![2041, 22875, -5445], ![-365, 66429, 0]], ![![1339, 15057, -3584], ![-252, 43725, 0]]]
  g := ![![![1, 0, 0], ![-38, 61, 0], ![-25, 0, 61]], ![![-1, 1, 0], ![11, -21, 5], ![31, -33, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![0, 1, 0]] ![![61, 0, 0], ![22, 1, 0]]
  ![![61, 0, 0], ![24, 17, 1]] where
 M := ![![![3721, 0, 0], ![1342, 61, 0]], ![![0, 61, 0], ![-2, 24, 5]]]
 hmul := by decide  
 g := ![![![![37, -17, -1], ![61, 0, 0]], ![![-2, -16, -1], ![61, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-2, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![24, 17, 1]] ![![61, 0, 0], ![-23, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1403, 61, 0]], ![![1464, 1037, 61], ![-549, -366, 61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-23, 1, 0]]], ![![![24, 17, 1]], ![![-9, -6, 1]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [38, 13, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 58, 7], [18, 8, 60], [0, 1]]
 g := ![![[43, 14, 25], [42, 64, 36], [14, 14], [61, 55], [59, 1], []], ![[58, 7, 56, 58], [8, 1, 47, 2], [8, 35], [4, 1], [39, 64], [18, 49]], ![[35, 59, 25, 15], [27, 47, 61, 40], [18, 16], [3, 21], [64, 14], [32, 49]]]
 h' := ![![[41, 58, 7], [12, 59, 62], [25, 60, 61], [50, 60, 58], [36, 66, 51], [0, 0, 1], [0, 1]], ![[18, 8, 60], [59, 38, 38], [54, 49, 37], [36, 42, 13], [56, 61, 66], [59, 47, 8], [41, 58, 7]], ![[0, 1], [40, 37, 34], [25, 25, 36], [46, 32, 63], [19, 7, 17], [46, 20, 58], [18, 8, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 17], []]
 b := ![[], [62, 9, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [38, 13, 8, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180431, 265789, -563872]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2693, 3967, -8416]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-6, -29, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-6, -29, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![65, 42, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-6, -29, 1], ![95, -97, -146], ![-1082, 971, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -42, 71]], ![![-1, -1, 1], ![135, 85, -146], ![-7, 19, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [59, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 70], [0, 1]]
 g := ![![[8, 15], [22, 38], [27, 4], [20], [57], [1]], ![[28, 56], [49, 33], [56, 67], [20], [57], [1]]]
 h' := ![![[25, 70], [51, 50], [40, 31], [35, 2], [47, 37], [12, 25], [0, 1]], ![[0, 1], [23, 21], [34, 40], [14, 69], [49, 34], [69, 46], [25, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [7, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [59, 46, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2641, -1660, -2795]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2596, 1630, -2795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![4, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![4, 1, 0]] 
 ![![71, 0, 0], ![4, 1, 0], ![9, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![4, 1, 0], ![-2, 6, 5], ![37, -33, 3]]]
  hmulB := by decide  
  f := ![![![-791, 2376, 1980], ![0, -28116, 0]], ![![-44, 132, 110], ![1, -1562, 0]], ![![-101, 301, 251], ![13, -3564, 0]]]
  g := ![![![1, 0, 0], ![-4, 71, 0], ![-9, 0, 71]], ![![0, 1, 0], ![-1, 6, 5], ![2, -33, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-6, -29, 1]] ![![71, 0, 0], ![4, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![284, 71, 0]], ![![-426, -2059, 71], ![71, -213, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![4, 1, 0]]], ![![![-6, -29, 1]], ![![1, -3, -2]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [56, 39, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 56, 38], [31, 16, 35], [0, 1]]
 g := ![![[0, 29, 71], [58, 16], [59, 72], [57, 24, 72], [31, 1], []], ![[19, 47, 36, 49], [66, 8], [3, 67], [7, 64, 24, 36], [68, 37], [37, 57]], ![[72, 8, 59, 46], [25, 25], [9, 23], [0, 22, 31, 54], [70, 70], [40, 57]]]
 h' := ![![[0, 56, 38], [1, 54, 61], [16, 0, 4], [20, 47, 46], [16, 49, 46], [0, 0, 1], [0, 1]], ![[31, 16, 35], [45, 25, 35], [50, 2, 64], [46, 27, 40], [42, 66, 43], [45, 37, 16], [0, 56, 38]], ![[0, 1], [14, 67, 50], [10, 71, 5], [21, 72, 60], [6, 31, 57], [35, 36, 56], [31, 16, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 21], []]
 b := ![[], [33, 27, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [56, 39, 42, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5656551, -4418690, -3740885]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77487, -60530, -51245]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-35, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-35, 1, 0]] 
 ![![79, 0, 0], ![44, 1, 0], ![53, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-35, 1, 0], ![-2, -33, 5], ![37, -33, -36]]]
  hmulB := by decide  
  f := ![![![975, 17228, -2610], ![-158, 41238, 0]], ![![546, 9571, -1450], ![-78, 22910, 0]], ![![655, 11558, -1751], ![-104, 27666, 0]]]
  g := ![![![1, 0, 0], ![-44, 79, 0], ![-53, 0, 79]], ![![-1, 1, 0], ![15, -33, 5], ![43, -33, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-27, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-27, 1, 0]] 
 ![![79, 0, 0], ![52, 1, 0], ![70, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-27, 1, 0], ![-2, -25, 5], ![37, -33, -28]]]
  hmulB := by decide  
  f := ![![![-2220, -29455, 5890], ![395, -93062, 0]], ![![-1441, -19379, 3875], ![317, -61225, 0]], ![![-1950, -26100, 5219], ![400, -82460, 0]]]
  g := ![![![1, 0, 0], ![-52, 79, 0], ![-70, 0, 79]], ![![-1, 1, 0], ![12, -25, 5], ![47, -33, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-18, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-18, 1, 0]] 
 ![![79, 0, 0], ![61, 1, 0], ![21, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-18, 1, 0], ![-2, -16, 5], ![37, -33, -19]]]
  hmulB := by decide  
  f := ![![![5995, 49257, -15390], ![-711, 243162, 0]], ![![4627, 38023, -11880], ![-552, 187704, 0]], ![![1605, 13093, -4091], ![-139, 64638, 0]]]
  g := ![![![1, 0, 0], ![-61, 79, 0], ![-21, 0, 79]], ![![-1, 1, 0], ![11, -16, 5], ![31, -33, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-35, 1, 0]] ![![79, 0, 0], ![-27, 1, 0]]
  ![![79, 0, 0], ![-1, -12, 1]] where
 M := ![![![6241, 0, 0], ![-2133, 79, 0]], ![![-2765, 79, 0], ![943, -60, 5]]]
 hmul := by decide  
 g := ![![![![79, 0, 0], ![0, 0, 0]], ![![-26, 13, -1], ![79, 0, 0]]], ![![![-34, 13, -1], ![79, 0, 0]], ![![12, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-1, -12, 1]] ![![79, 0, 0], ![-18, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1422, 79, 0]], ![![-79, -948, 79], ![79, 158, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-18, 1, 0]]], ![![![-1, -12, 1]], ![![1, 2, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB243I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB243I1 : PrimesBelowBoundCertificateInterval O 31 79 243 where
  m := 11
  g := ![1, 2, 1, 2, 2, 2, 3, 1, 2, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB243I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![79, 79, 79]
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N1, I47N1, I53N1, I59N1, I61N0, I61N1, I61N2, I71N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N1], [], [I47N1], [I53N1], [I59N1], [I61N0, I61N1, I61N2], [], [I71N1], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
