
import IdealArithmetic.Examples.NF3_1_688076_2.RI3_1_688076_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [39, 24, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 25, 6], [63, 57, 77], [0, 1]]
 g := ![![[74, 44, 64], [24, 61, 70], [34, 33], [13, 64], [60, 82, 1], []], ![[67, 46, 34, 55], [46, 82, 14, 67], [27, 4], [4, 75], [31, 21, 50, 72], [15, 36]], ![[24, 48, 50, 37], [45, 55, 54, 37], [18, 51], [78, 12], [37, 70, 19, 68], [27, 36]]]
 h' := ![![[19, 25, 6], [60, 69, 8], [6, 34, 30], [81, 26, 38], [67, 10, 8], [0, 0, 1], [0, 1]], ![[63, 57, 77], [77, 27, 40], [74, 2, 5], [31, 13, 81], [42, 46, 18], [25, 16, 57], [19, 25, 6]], ![[0, 1], [13, 70, 35], [71, 47, 48], [62, 44, 47], [38, 27, 57], [11, 67, 25], [63, 57, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 23], []]
 b := ![[], [33, 50, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [39, 24, 1, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-48887, 22078, -830]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-589, 266, -10]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![42, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![42, 1, 0]] 
 ![![89, 0, 0], ![42, 1, 0], ![53, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![42, 1, 0], ![1, 42, 2], ![-174, 20, 43]]]
  hmulB := by decide  
  f := ![![![-2738, -180269, -8586], ![-3293, 382077, 0]], ![![-1311, -85033, -4050], ![-1512, 180225, 0]], ![![-1664, -107352, -5113], ![-1890, 227529, 0]]]
  g := ![![![1, 0, 0], ![-42, 89, 0], ![-53, 0, 89]], ![![0, 1, 0], ![-21, 42, 2], ![-37, 20, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, -5, 1]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![22, -5, 1]] 
 ![![89, 0, 0], ![53, 1, 0], ![20, 0, 1]] where
  M :=![![![22, -5, 1], ![-179, 42, -9], ![793, -177, 37]]]
  hmulB := by decide  
  f := ![![![-39, 8, 3]], ![![-29, 5, 2]], ![![-27, 1, 1]]]
  g := ![![![3, -5, 1], ![-25, 42, -9], ![106, -177, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-7, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-7, 1, 0]] 
 ![![89, 0, 0], ![82, 1, 0], ![65, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-7, 1, 0], ![1, -7, 2], ![-174, 20, -6]]]
  hmulB := by decide  
  f := ![![![-68, 531, -152], ![89, 6764, 0]], ![![-62, 489, -140], ![90, 6230, 0]], ![![-51, 388, -111], ![48, 4940, 0]]]
  g := ![![![1, 0, 0], ![-82, 89, 0], ![-65, 0, 89]], ![![-1, 1, 0], ![5, -7, 2], ![-16, 20, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![42, 1, 0]] ![![22, -5, 1]]
  ![![89, 0, 0], ![1, 3, 1]] where
 M := ![![![1958, -445, 89]], ![![745, -168, 33]]]
 hmul := by decide  
 g := ![![![![21, -8, 0], ![89, 0, 0]]], ![![![8, -3, 0], ![33, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![1, 3, 1]] ![![89, 0, 0], ![-7, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-623, 89, 0]], ![![89, 267, 89], ![-178, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-7, 1, 0]]], ![![![1, 3, 1]], ![![-2, 0, 0]]]]
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
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-19, -1, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-19, -1, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![78, 96, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-19, -1, 1], ![-175, 1, -1], ![97, -97, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -96, 97]], ![![-1, -1, 1], ![-1, 1, -1], ![1, -1, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [37, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 96], [0, 1]]
 g := ![![[68, 66], [65], [65], [61], [1], [6, 1]], ![[76, 31], [65], [65], [61], [1], [12, 96]]]
 h' := ![![[6, 96], [44, 58], [86, 68], [39, 68], [68, 62], [69, 96], [0, 1]], ![[0, 1], [4, 39], [9, 29], [59, 29], [52, 35], [63, 1], [6, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [19, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [37, 91, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1782, -2515, 963]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-756, -979, 963]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![1, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![1, 1, 0]] 
 ![![97, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![1, 1, 0], ![1, 1, 2], ![-174, 20, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![97, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -1], ![48, 49, 0]]]
  g := ![![![1, 0, 0], ![-1, 97, 0], ![0, 0, 97]], ![![0, 1, 0], ![0, 1, 2], ![-2, 20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-19, -1, 1]] ![![97, 0, 0], ![1, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![97, 97, 0]], ![![-1843, -97, 97], ![-194, 0, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![1, 1, 0]]], ![![![-19, -1, 1]], ![![-2, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![5, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![5, 1, 0]] 
 ![![101, 0, 0], ![5, 1, 0], ![89, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![5, 1, 0], ![1, 5, 2], ![-174, 20, 6]]]
  hmulB := by decide  
  f := ![![![-323, -1620, -648], ![0, 32724, 0]], ![![-16, -80, -32], ![1, 1616, 0]], ![![-287, -1428, -571], ![48, 28836, 0]]]
  g := ![![![1, 0, 0], ![-5, 101, 0], ![-89, 0, 101]], ![![0, 1, 0], ![-2, 5, 2], ![-8, 20, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![8, 1, 0]] 
 ![![101, 0, 0], ![8, 1, 0], ![19, 0, 1]] where
  M :=![![![8, 1, 0], ![1, 8, 2], ![-174, 20, 9]]]
  hmulB := by decide  
  f := ![![![-32, 9, -2]], ![![1, 0, 0]], ![![-20, 5, -1]]]
  g := ![![![0, 1, 0], ![-1, 8, 2], ![-5, 20, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-14, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-14, 1, 0]] 
 ![![101, 0, 0], ![87, 1, 0], ![54, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-14, 1, 0], ![1, -14, 2], ![-174, 20, -13]]]
  hmulB := by decide  
  f := ![![![-3423, 49886, -7128], ![1010, 359964, 0]], ![![-2942, 42957, -6138], ![910, 309969, 0]], ![![-1820, 26671, -3811], ![613, 192456, 0]]]
  g := ![![![1, 0, 0], ![-87, 101, 0], ![-54, 0, 101]], ![![-1, 1, 0], ![11, -14, 2], ![-12, 20, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![5, 1, 0]] ![![8, 1, 0]]
  ![![101, 0, 0], ![-30, -44, 1]] where
 M := ![![![808, 101, 0]], ![![41, 13, 2]]]
 hmul := by decide  
 g := ![![![![8, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-30, -44, 1]] ![![101, 0, 0], ![-14, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-1414, 101, 0]], ![![-3030, -4444, 101], ![202, 606, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-14, 1, 0]]], ![![![-30, -44, 1]], ![![2, 6, -1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-18, 7, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-18, 7, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![85, 7, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-18, 7, 1], ![-167, 2, 15], ![-1295, 63, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -7, 103]], ![![-1, 0, 1], ![-14, -1, 15], ![-20, 0, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [32, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 102], [0, 1]]
 g := ![![[62, 29], [66, 83], [65, 58], [2], [61], [76, 1]], ![[0, 74], [91, 20], [44, 45], [2], [61], [49, 102]]]
 h' := ![![[76, 102], [51, 82], [83, 17], [34, 77], [60, 38], [40, 79], [0, 1]], ![[0, 1], [0, 21], [36, 86], [15, 26], [64, 65], [70, 24], [76, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [44, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [32, 27, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309941, -338155, 93788]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80407, -9657, 93788]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-15, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-15, 1, 0]] 
 ![![103, 0, 0], ![88, 1, 0], ![94, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-15, 1, 0], ![1, -15, 2], ![-174, 20, -14]]]
  hmulB := by decide  
  f := ![![![-818, 12957, -1728], ![309, 88992, 0]], ![![-692, 11067, -1476], ![310, 76014, 0]], ![![-749, 11825, -1577], ![265, 81216, 0]]]
  g := ![![![1, 0, 0], ![-88, 103, 0], ![-94, 0, 103]], ![![-1, 1, 0], ![11, -15, 2], ![-6, 20, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-18, 7, 1]] ![![103, 0, 0], ![-15, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1545, 103, 0]], ![![-1854, 721, 103], ![103, -103, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-15, 1, 0]]], ![![![-18, 7, 1]], ![![1, -1, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [65, 16, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 41, 94], [95, 65, 13], [0, 1]]
 g := ![![[54, 26, 79], [93, 79, 34], [6, 14], [37, 4, 69], [13, 81], [1]], ![[10, 23, 82, 60], [62, 50, 75, 24], [65, 4], [15, 47, 93, 78], [22, 10], [3, 66, 51, 50]], ![[36, 50, 78, 76], [103, 48, 31, 48], [48, 81], [89, 83, 68, 105], [2, 27], [56, 68, 84, 57]]]
 h' := ![![[21, 41, 94], [54, 23, 20], [71, 27, 81], [56, 14, 11], [63, 31, 47], [42, 91, 9], [0, 1]], ![[95, 65, 13], [44, 71, 38], [27, 15, 99], [20, 73, 105], [53, 35, 84], [78, 43, 44], [21, 41, 94]], ![[0, 1], [74, 13, 49], [47, 65, 34], [8, 20, 98], [87, 41, 83], [89, 80, 54], [95, 65, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 93], []]
 b := ![[], [81, 5, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [65, 16, 98, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1763574, 215712, 5671]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16482, 2016, 53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-14, -2, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-14, -2, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![95, 107, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-14, -2, 1], ![-176, 6, -3], ![271, -117, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -107, 109]], ![![-1, -1, 1], ![1, 3, -3], ![-1, -5, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [42, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 108], [0, 1]]
 g := ![![[33, 64], [29], [103, 7], [16, 45], [29], [31, 1]], ![[55, 45], [29], [102, 102], [103, 64], [29], [62, 108]]]
 h' := ![![[31, 108], [47, 101], [34, 62], [91, 94], [17, 46], [6, 47], [0, 1]], ![[0, 1], [17, 8], [103, 47], [62, 15], [26, 63], [46, 62], [31, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [41, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [42, 78, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1038, -304, -66]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![48, 62, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![3, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![3, 1, 0]] 
 ![![109, 0, 0], ![3, 1, 0], ![105, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![3, 1, 0], ![1, 3, 2], ![-174, 20, 4]]]
  hmulB := by decide  
  f := ![![![-6925, -20802, -13870], ![-327, 755915, 0]], ![![-190, -570, -380], ![1, 20710, 0]], ![![-6672, -20039, -13361], ![-274, 728175, 0]]]
  g := ![![![1, 0, 0], ![-3, 109, 0], ![-105, 0, 109]], ![![0, 1, 0], ![-2, 3, 2], ![-6, 20, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-14, -2, 1]] ![![109, 0, 0], ![3, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![327, 109, 0]], ![![-1526, -218, 109], ![-218, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![3, 1, 0]]], ![![![-14, -2, 1]], ![![-2, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-8, 43, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-8, 43, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![105, 43, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-8, 43, 1], ![-131, 12, 87], ![-7559, 783, 55]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -43, 113]], ![![-1, 0, 1], ![-82, -33, 87], ![-118, -14, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [30, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 112], [0, 1]]
 g := ![![[37, 49], [102], [16], [82], [100, 57], [20, 1]], ![[0, 64], [102], [16], [82], [110, 56], [40, 112]]]
 h' := ![![[20, 112], [86, 7], [78, 92], [28, 4], [51, 46], [78, 31], [0, 1]], ![[0, 1], [0, 106], [110, 21], [108, 109], [67, 67], [20, 82], [20, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [105, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [30, 93, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19948, 3430, 1307]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1391, -467, 1307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![26, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![26, 1, 0]] 
 ![![113, 0, 0], ![26, 1, 0], ![58, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![26, 1, 0], ![1, 26, 2], ![-174, 20, 27]]]
  hmulB := by decide  
  f := ![![![-7567, -218368, -16800], ![-3616, 949200, 0]], ![![-1750, -50225, -3864], ![-790, 218316, 0]], ![![-3892, -112083, -8623], ![-1821, 487200, 0]]]
  g := ![![![1, 0, 0], ![-26, 113, 0], ![-58, 0, 113]], ![![0, 1, 0], ![-7, 26, 2], ![-20, 20, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-8, 43, 1]] ![![113, 0, 0], ![26, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2938, 113, 0]], ![![-904, 4859, 113], ![-339, 1130, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![26, 1, 0]]], ![![![-8, 43, 1]], ![![-3, 10, 1]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![0, 47, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![0, 47, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 47, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![0, 47, 1], ![-127, 20, 95], ![-8255, 863, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, -46, -1], ![127, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -47, 127]], ![![0, 0, 1], ![-1, -35, 95], ![-65, -18, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [117, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 126], [0, 1]]
 g := ![![[43, 38], [83, 32], [42, 117], [124, 13], [14, 4], [49, 1]], ![[0, 89], [0, 95], [60, 10], [126, 114], [83, 123], [98, 126]]]
 h' := ![![[49, 126], [68, 66], [39, 64], [97, 25], [13, 34], [109, 125], [0, 1]], ![[0, 1], [0, 61], [0, 63], [52, 102], [28, 93], [11, 2], [49, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [97, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [117, 78, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2413, -831, -42]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 9, -42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![32, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![32, 1, 0]] 
 ![![127, 0, 0], ![32, 1, 0], ![60, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![32, 1, 0], ![1, 32, 2], ![-174, 20, 33]]]
  hmulB := by decide  
  f := ![![![205, 7551, 472], ![127, -29972, 0]], ![![27, 1887, 118], ![128, -7493, 0]], ![![84, 3567, 223], ![111, -14160, 0]]]
  g := ![![![1, 0, 0], ![-32, 127, 0], ![-60, 0, 127]], ![![0, 1, 0], ![-9, 32, 2], ![-22, 20, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![0, 47, 1]] ![![127, 0, 0], ![32, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![4064, 127, 0]], ![![0, 5969, 127], ![-127, 1524, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![32, 1, 0]]], ![![![0, 47, 1]], ![![-1, 12, 1]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![46, -60, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![46, -60, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![46, 71, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![46, -60, 1], ![-234, 66, -119], ![10363, -1277, 6]]]
  hmulB := by decide  
  f := ![![![-45, 60, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-46, -71, 131]], ![![0, -1, 1], ![40, 65, -119], ![77, -13, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [35, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 130], [0, 1]]
 g := ![![[30, 15], [20, 123], [44], [75], [1], [4], [1]], ![[0, 116], [36, 8], [44], [75], [1], [4], [1]]]
 h' := ![![[129, 130], [86, 43], [14, 75], [47, 31], [24, 72], [37, 1], [96, 129], [0, 1]], ![[0, 1], [0, 88], [126, 56], [116, 100], [11, 59], [35, 130], [100, 2], [129, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [79, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [35, 2, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2580, -1066, 354]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-144, -200, 354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-12, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-12, 1, 0]] 
 ![![131, 0, 0], ![119, 1, 0], ![125, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-12, 1, 0], ![1, -12, 2], ![-174, 20, -11]]]
  hmulB := by decide  
  f := ![![![15349, -187179, 31200], ![-2751, -2043600, 0]], ![![13943, -170021, 28340], ![-2488, -1856270, 0]], ![![14647, -178606, 29771], ![-2614, -1950000, 0]]]
  g := ![![![1, 0, 0], ![-119, 131, 0], ![-125, 0, 131]], ![![-1, 1, 0], ![9, -12, 2], ![-9, 20, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![46, -60, 1]] ![![131, 0, 0], ![-12, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-1572, 131, 0]], ![![6026, -7860, 131], ![-786, 786, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-12, 1, 0]]], ![![![46, -60, 1]], ![![-6, 6, -1]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![14, 59, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![14, 59, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![14, 59, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![14, 59, 1], ![-115, 34, 119], ![-10343, 1103, 93]]]
  hmulB := by decide  
  f := ![![![-13, -59, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -59, 137]], ![![0, 0, 1], ![-13, -51, 119], ![-85, -32, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [8, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 136], [0, 1]]
 g := ![![[88, 120], [130], [72], [10, 7], [30], [87], [1]], ![[0, 17], [130], [72], [14, 130], [30], [87], [1]]]
 h' := ![![[118, 136], [24, 95], [70, 33], [57, 88], [103, 12], [53, 21], [129, 118], [0, 1]], ![[0, 1], [0, 42], [128, 104], [29, 49], [12, 125], [65, 116], [79, 19], [118, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [42, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [8, 19, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1987, -1925, 455]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -210, 455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![18, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![18, 1, 0]] 
 ![![137, 0, 0], ![18, 1, 0], ![44, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![18, 1, 0], ![1, 18, 2], ![-174, 20, 19]]]
  hmulB := by decide  
  f := ![![![-2105, -39200, -4356], ![-548, 298386, 0]], ![![-286, -5148, -572], ![1, 39182, 0]], ![![-680, -12590, -1399], ![-146, 95832, 0]]]
  g := ![![![1, 0, 0], ![-18, 137, 0], ![-44, 0, 137]], ![![0, 1, 0], ![-3, 18, 2], ![-10, 20, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![14, 59, 1]] ![![137, 0, 0], ![18, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![2466, 137, 0]], ![![1918, 8083, 137], ![137, 1096, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![18, 1, 0]]], ![![![14, 59, 1]], ![![1, 8, 1]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB235I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB235I2 : PrimesBelowBoundCertificateInterval O 79 137 235 where
  m := 11
  g := ![1, 3, 2, 3, 2, 1, 2, 2, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB235I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I89N0, I89N1, I89N2, I97N1, I101N0, I101N1, I101N2, I103N1, I109N1, I113N1, I127N1, I131N1, I137N1]
  Il := ![[], [I89N0, I89N1, I89N2], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [], [I109N1], [I113N1], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
