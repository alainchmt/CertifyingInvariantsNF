
import IdealArithmetic.Examples.NF3_1_329427_1.RI3_1_329427_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![16, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![16, 1, 0]] 
 ![![83, 0, 0], ![16, 1, 0], ![30, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![16, 1, 0], ![0, 17, 2], ![112, 10, 15]]]
  hmulB := by decide  
  f := ![![![321, 20, 0], ![-1660, 0, 0]], ![![48, 3, 0], ![-248, 0, 0]], ![![106, -2, -1], ![-548, 42, 0]]]
  g := ![![![1, 0, 0], ![-16, 83, 0], ![-30, 0, 83]], ![![0, 1, 0], ![-4, 17, 2], ![-6, 10, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-32, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-32, 1, 0]] 
 ![![83, 0, 0], ![51, 1, 0], ![2, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-32, 1, 0], ![0, -31, 2], ![112, 10, -33]]]
  hmulB := by decide  
  f := ![![![1761, -55, 0], ![4565, 0, 0]], ![![1089, -34, 0], ![2823, 0, 0]], ![![54, 14, -1], ![140, 42, 0]]]
  g := ![![![1, 0, 0], ![-51, 83, 0], ![-2, 0, 83]], ![![-1, 1, 0], ![19, -31, 2], ![-4, 10, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![16, 1, 0]] ![![83, 0, 0], ![16, 1, 0]]
  ![![83, 0, 0], ![-38, -25, 1]] where
 M := ![![![6889, 0, 0], ![1328, 83, 0]], ![![1328, 83, 0], ![256, 33, 2]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![16, 1, 0], ![0, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-38, -25, 1]] ![![83, 0, 0], ![-32, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2656, 83, 0]], ![![-3154, -2075, 83], ![1328, 747, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-32, 1, 0]]], ![![![-38, -25, 1]], ![![16, 9, -1]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-21, -17, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-21, -17, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![68, 72, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-21, -17, 1], ![112, -28, -35], ![-2016, -119, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -72, 89]], ![![-1, -1, 1], ![28, 28, -35], ![-28, -7, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [8, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 88], [0, 1]]
 g := ![![[14, 78], [10], [18], [78, 71], [38, 84], [1]], ![[0, 11], [10], [18], [47, 18], [64, 5], [1]]]
 h' := ![![[66, 88], [77, 73], [35, 59], [88, 75], [52, 31], [81, 66], [0, 1]], ![[0, 1], [0, 16], [13, 30], [54, 14], [51, 58], [76, 23], [66, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [80, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [8, 23, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![344, 537, 26]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -15, 26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![35, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![35, 1, 0]] 
 ![![89, 0, 0], ![35, 1, 0], ![82, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![35, 1, 0], ![0, 36, 2], ![112, 10, 34]]]
  hmulB := by decide  
  f := ![![![561, 16, 0], ![-1424, 0, 0]], ![![175, 5, 0], ![-444, 0, 0]], ![![568, -2, -1], ![-1442, 45, 0]]]
  g := ![![![1, 0, 0], ![-35, 89, 0], ![-82, 0, 89]], ![![0, 1, 0], ![-16, 36, 2], ![-34, 10, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-21, -17, 1]] ![![89, 0, 0], ![35, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3115, 89, 0]], ![![-1869, -1513, 89], ![-623, -623, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![35, 1, 0]]], ![![![-21, -17, 1]], ![![-7, -7, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![32, -22, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![32, -22, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![32, 75, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![32, -22, 1], ![112, 20, -45], ![-2576, -169, 65]]]
  hmulB := by decide  
  f := ![![![-31, 22, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -75, 97]], ![![0, -1, 1], ![16, 35, -45], ![-48, -52, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [53, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [61, 96], [0, 1]]
 g := ![![[8, 11], [53], [31], [35], [33], [61, 1]], ![[0, 86], [53], [31], [35], [33], [25, 96]]]
 h' := ![![[61, 96], [26, 60], [33, 21], [67, 15], [51, 61], [65, 79], [0, 1]], ![[0, 1], [0, 37], [53, 76], [12, 82], [86, 36], [34, 18], [61, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [15, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [53, 36, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-878, 931, 306]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-110, -227, 306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![45, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![45, 1, 0]] 
 ![![97, 0, 0], ![45, 1, 0], ![32, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![45, 1, 0], ![0, 46, 2], ![112, 10, 44]]]
  hmulB := by decide  
  f := ![![![2566, 57, 0], ![-5529, 0, 0]], ![![1170, 26, 0], ![-2521, 0, 0]], ![![866, -4, -1], ![-1866, 49, 0]]]
  g := ![![![1, 0, 0], ![-45, 97, 0], ![-32, 0, 97]], ![![0, 1, 0], ![-22, 46, 2], ![-18, 10, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![32, -22, 1]] ![![97, 0, 0], ![45, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4365, 97, 0]], ![![3104, -2134, 97], ![1552, -970, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![45, 1, 0]]], ![![![32, -22, 1]], ![![16, -10, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-54, 35, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-54, 35, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![47, 35, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-54, 35, 1], ![112, -9, 69], ![3808, 401, -78]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -35, 101]], ![![-1, 0, 1], ![-31, -24, 69], ![74, 31, -78]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [45, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 100], [0, 1]]
 g := ![![[23, 9], [13], [1, 25], [88], [70], [76, 1]], ![[0, 92], [13], [83, 76], [88], [70], [51, 100]]]
 h' := ![![[76, 100], [26, 98], [56, 66], [99, 96], [76, 47], [14, 75], [0, 1]], ![[0, 1], [0, 3], [22, 35], [22, 5], [12, 54], [58, 26], [76, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [93, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [45, 25, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2429, 51, 114]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -39, 114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![32, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![32, 1, 0]] 
 ![![101, 0, 0], ![32, 1, 0], ![78, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![32, 1, 0], ![0, 33, 2], ![112, 10, 31]]]
  hmulB := by decide  
  f := ![![![1345, 42, 0], ![-4242, 0, 0]], ![![416, 13, 0], ![-1312, 0, 0]], ![![1014, 15, -1], ![-3198, 51, 0]]]
  g := ![![![1, 0, 0], ![-32, 101, 0], ![-78, 0, 101]], ![![0, 1, 0], ![-12, 33, 2], ![-26, 10, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-54, 35, 1]] ![![101, 0, 0], ![32, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![3232, 101, 0]], ![![-5454, 3535, 101], ![-1616, 1111, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![32, 1, 0]]], ![![![-54, 35, 1]], ![![-16, 11, 1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![19, 17, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![19, 17, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![19, 17, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![19, 17, 1], ![112, 46, 33], ![1792, 221, 13]]]
  hmulB := by decide  
  f := ![![![-18, -17, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -17, 103]], ![![0, 0, 1], ![-5, -5, 33], ![15, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [20, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 102], [0, 1]]
 g := ![![[81, 91], [47, 32], [77, 50], [49], [98], [28, 1]], ![[54, 12], [16, 71], [35, 53], [49], [98], [56, 102]]]
 h' := ![![[28, 102], [90, 83], [5, 49], [52, 16], [65, 7], [58, 43], [0, 1]], ![[0, 1], [45, 20], [38, 54], [88, 87], [55, 96], [26, 60], [28, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [65, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [20, 75, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-464, 1325, -122]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, 33, -122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-33, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-33, 1, 0]] 
 ![![103, 0, 0], ![70, 1, 0], ![90, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-33, 1, 0], ![0, -32, 2], ![112, 10, -34]]]
  hmulB := by decide  
  f := ![![![1288, -39, 0], ![4017, 0, 0]], ![![892, -27, 0], ![2782, 0, 0]], ![![1128, -18, -1], ![3518, 52, 0]]]
  g := ![![![1, 0, 0], ![-70, 103, 0], ![-90, 0, 103]], ![![-1, 1, 0], ![20, -32, 2], ![24, 10, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![19, 17, 1]] ![![103, 0, 0], ![-33, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3399, 103, 0]], ![![1957, 1751, 103], ![-515, -515, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-33, 1, 0]]], ![![![19, 17, 1]], ![![-5, -5, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![13, -24, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![13, -24, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![13, 83, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![13, -24, 1], ![112, -1, -49], ![-2800, -189, 48]]]
  hmulB := by decide  
  f := ![![![-12, 24, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -83, 107]], ![![0, -1, 1], ![7, 38, -49], ![-32, -39, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [22, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 106], [0, 1]]
 g := ![![[64, 48], [30, 9], [39], [21, 101], [27], [90, 1]], ![[104, 59], [91, 98], [39], [16, 6], [27], [73, 106]]]
 h' := ![![[90, 106], [89, 35], [84, 3], [73, 50], [75, 23], [53, 53], [0, 1]], ![[0, 1], [29, 72], [33, 104], [79, 57], [5, 84], [8, 54], [90, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [26, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [22, 17, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![358, 549, 44]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -29, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![49, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![49, 1, 0]] 
 ![![107, 0, 0], ![49, 1, 0], ![59, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![49, 1, 0], ![0, 50, 2], ![112, 10, 48]]]
  hmulB := by decide  
  f := ![![![3578, 73, 0], ![-7811, 0, 0]], ![![1568, 32, 0], ![-3423, 0, 0]], ![![1972, 15, -1], ![-4305, 54, 0]]]
  g := ![![![1, 0, 0], ![-49, 107, 0], ![-59, 0, 107]], ![![0, 1, 0], ![-24, 50, 2], ![-30, 10, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![13, -24, 1]] ![![107, 0, 0], ![49, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5243, 107, 0]], ![![1391, -2568, 107], ![749, -1177, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![49, 1, 0]]], ![![![13, -24, 1]], ![![7, -11, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [103, 89, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 87, 54], [2, 21, 55], [0, 1]]
 g := ![![[1, 51, 16], [32, 102], [29, 5, 63], [86, 75, 104], [69, 64], [1]], ![[46, 13, 89, 17], [77, 93], [28, 52, 46, 65], [50, 100, 28, 96], [3, 3], [7, 8, 37, 68]], ![[71, 78, 52, 101], [92, 75], [63, 64, 37, 79], [86, 31, 102, 13], [1, 88], [14, 91, 44, 41]]]
 h' := ![![[6, 87, 54], [57, 4, 4], [65, 34, 59], [80, 77, 64], [14, 42, 39], [6, 20, 8], [0, 1]], ![[2, 21, 55], [38, 19, 82], [98, 40, 23], [72, 18, 52], [92, 92, 35], [40, 101, 49], [6, 87, 54]], ![[0, 1], [88, 86, 23], [9, 35, 27], [57, 14, 102], [77, 84, 35], [92, 97, 52], [2, 21, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 46], []]
 b := ![[], [27, 27, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [103, 89, 101, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77705446, 17465615, 3054616]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![712894, 160235, 28024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [38, 85, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 52, 43], [83, 60, 70], [0, 1]]
 g := ![![[82, 89, 2], [104, 1], [81, 15], [52, 102], [76, 60, 98], [1]], ![[90, 35, 88, 48], [37, 31], [64, 81], [60, 77], [55, 49, 100, 21], [32, 87, 49, 68]], ![[46, 26, 4, 29], [67, 8], [45, 97], [26, 4], [22, 78, 76, 84], [2, 41, 54, 45]]]
 h' := ![![[48, 52, 43], [102, 26, 51], [72, 43, 1], [72, 107, 44], [50, 49, 21], [75, 28, 18], [0, 1]], ![[83, 60, 70], [0, 53, 110], [29, 17, 101], [75, 23, 9], [78, 19, 90], [105, 47, 24], [48, 52, 43]], ![[0, 1], [51, 34, 65], [26, 53, 11], [70, 96, 60], [70, 45, 2], [44, 38, 71], [83, 60, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 25], []]
 b := ![[], [32, 52, 73], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [38, 85, 95, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43279, 11413, 2034]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![383, 101, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [38, 6, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 25, 99], [11, 101, 28], [0, 1]]
 g := ![![[51, 72, 32], [54, 108, 88], [118, 98, 21], [115, 33, 35], [49, 30, 103], [1]], ![[114, 98, 22, 1], [114, 55, 85, 64], [21, 79, 93, 21], [0, 12, 67, 117], [115, 48, 101, 37], [24, 19, 89, 19]], ![[94, 67, 1, 96], [90, 12, 125, 119], [45, 33, 105, 89], [4, 36, 84, 55], [70, 85, 107, 106], [59, 74, 99, 108]]]
 h' := ![![[94, 25, 99], [107, 14, 64], [88, 50, 56], [75, 32, 104], [43, 10, 110], [89, 121, 105], [0, 1]], ![[11, 101, 28], [108, 60, 103], [2, 12, 65], [73, 43, 83], [100, 77, 35], [108, 37, 105], [94, 25, 99]], ![[0, 1], [34, 53, 87], [106, 65, 6], [74, 52, 67], [124, 40, 109], [105, 96, 44], [11, 101, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 29], []]
 b := ![[], [31, 26, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [38, 6, 22, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![840486, 195453, 23876]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6618, 1539, 188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [76, 77, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 105, 80], [80, 25, 51], [0, 1]]
 g := ![![[44, 71, 62], [70, 83, 12], [18, 25], [122, 112], [70, 102], [11, 1], []], ![[9, 78, 94, 34], [129, 24, 65, 100], [59, 108], [79, 16], [43, 46], [0, 101], [85, 112]], ![[83, 16, 13, 17], [111, 111, 91, 51], [121, 80], [71, 113], [15, 81], [24, 21], [114, 112]]]
 h' := ![![[62, 105, 80], [51, 74, 18], [47, 46, 55], [74, 65, 126], [62, 34, 80], [81, 125, 44], [0, 0, 1], [0, 1]], ![[80, 25, 51], [126, 55, 82], [106, 84, 77], [23, 111, 97], [1, 37, 4], [16, 1, 96], [4, 59, 25], [62, 105, 80]], ![[0, 1], [65, 2, 31], [120, 1, 130], [88, 86, 39], [84, 60, 47], [69, 5, 122], [94, 72, 105], [80, 25, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 19], []]
 b := ![[], [41, 31, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [76, 77, 120, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1170354, -57640, -43230]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8934, -440, -330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![40, 43, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![40, 43, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![40, 43, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![40, 43, 1], ![112, 93, 85], ![4704, 481, 8]]]
  hmulB := by decide  
  f := ![![![-39, -43, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -43, 137]], ![![0, 0, 1], ![-24, -26, 85], ![32, 1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [96, 98, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 136], [0, 1]]
 g := ![![[21, 107], [14], [1], [116, 30], [107], [14], [1]], ![[84, 30], [14], [1], [53, 107], [107], [14], [1]]]
 h' := ![![[39, 136], [37, 92], [55, 98], [98, 1], [136, 116], [63, 45], [41, 39], [0, 1]], ![[0, 1], [63, 45], [41, 39], [0, 136], [2, 21], [37, 92], [55, 98], [39, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [21, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [96, 98, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1427, 51, 135]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29, -42, 135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![52, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![52, 1, 0]] 
 ![![137, 0, 0], ![52, 1, 0], ![129, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![52, 1, 0], ![0, 53, 2], ![112, 10, 51]]]
  hmulB := by decide  
  f := ![![![677, 13, 0], ![-1781, 0, 0]], ![![260, 5, 0], ![-684, 0, 0]], ![![661, -14, -1], ![-1739, 69, 0]]]
  g := ![![![1, 0, 0], ![-52, 137, 0], ![-129, 0, 137]], ![![0, 1, 0], ![-22, 53, 2], ![-51, 10, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![40, 43, 1]] ![![137, 0, 0], ![52, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7124, 137, 0]], ![![5480, 5891, 137], ![2192, 2329, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![52, 1, 0]]], ![![![40, 43, 1]], ![![16, 17, 1]]]]
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


lemma PB163I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB163I2 : PrimesBelowBoundCertificateInterval O 79 137 163 where
  m := 11
  g := ![3, 2, 2, 2, 2, 2, 1, 1, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB163I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I89N1, I97N1, I101N1, I103N1, I107N1, I137N1]
  Il := ![[I83N0, I83N0, I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N1], [], [], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
