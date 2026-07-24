
import IdealArithmetic.Examples.NF3_1_136971_1.RI3_1_136971_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![39, 38, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![39, 38, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![39, 38, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![39, 38, 1], ![71, 33, 38], ![2698, -157, 33]]]
  hmulB := by decide  
  f := ![![![-38, -38, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -38, 83]], ![![0, 0, 1], ![-17, -17, 38], ![17, -17, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [78, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 82], [0, 1]]
 g := ![![[0, 33], [], [], [44], [], [1]], ![[0, 50], [], [], [44], [], [1]]]
 h' := ![![[0, 82], [0, 38], [11], [54], [0, 25], [5], [0, 1]], ![[0, 1], [0, 45], [11], [54], [0, 58], [5], [0, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [0, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [78, 0, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![220, 59, -5]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 3, -5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-38, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-38, 1, 0]] 
 ![![83, 0, 0], ![45, 1, 0], ![50, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-38, 1, 0], ![0, -38, 1], ![71, -6, -38]]]
  hmulB := by decide  
  f := ![![![2775, -73, 0], ![6059, 0, 0]], ![![1521, -40, 0], ![3321, 0, 0]], ![![1690, -44, 0], ![3690, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 83, 0], ![-50, 0, 83]], ![![-1, 1, 0], ![20, -38, 1], ![27, -6, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![39, 38, 1]] ![![83, 0, 0], ![-38, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3154, 83, 0]], ![![3237, 3154, 83], ![-1411, -1411, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-38, 1, 0]]], ![![![39, 38, 1]], ![![-17, -17, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20, -4, -1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-20, -4, -1]] 
 ![![89, 0, 0], ![49, 1, 0], ![2, 0, 1]] where
  M :=![![![-20, -4, -1], ![-71, -14, -4], ![-284, -47, -14]]]
  hmulB := by decide  
  f := ![![![-8, 9, -2]], ![![-6, 5, -1]], ![![7, -2, 0]]]
  g := ![![![2, -4, -1], ![7, -14, -4], ![23, -47, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![117, 22, 6]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![117, 22, 6]] 
 ![![89, 0, 0], ![80, 1, 0], ![8, 0, 1]] where
  M :=![![![117, 22, 6], ![426, 81, 22], ![1562, 294, 81]]]
  hmulB := by decide  
  f := ![![![93, -18, -2]], ![![82, -15, -2]], ![![-6, -2, 1]]]
  g := ![![![-19, 22, 6], ![-70, 81, 22], ![-254, 294, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-20, -4, -1]] ![![-20, -4, -1]]
  ![![968, 183, 50]] where
 M := ![![![968, 183, 50]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI89N1 : IdealMulLeCertificate' Table 
  ![![968, 183, 50]] ![![117, 22, 6]]
  ![![89, 0, 0]] where
 M := ![![![269314, 50819, 13884]]]
 hmul := by decide  
 g := ![![![![3026, 571, 156]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-43, -40, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-43, -40, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![54, 57, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-43, -40, 1], ![71, -49, -40], ![-2840, 311, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -57, 97]], ![![-1, -1, 1], ![23, 23, -40], ![-2, 32, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [84, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 96], [0, 1]]
 g := ![![[47, 24], [43], [64], [44], [70], [29, 1]], ![[64, 73], [43], [64], [44], [70], [58, 96]]]
 h' := ![![[29, 96], [78, 86], [2, 25], [25, 8], [61, 23], [86, 78], [0, 1]], ![[0, 1], [50, 11], [48, 72], [63, 89], [49, 74], [20, 19], [29, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [16, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [84, 68, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-835, 579, 148]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91, -81, 148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![40, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![40, 1, 0]] 
 ![![97, 0, 0], ![40, 1, 0], ![49, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![40, 1, 0], ![0, 40, 1], ![71, -6, 40]]]
  hmulB := by decide  
  f := ![![![521, 13, 0], ![-1261, 0, 0]], ![![200, 5, 0], ![-484, 0, 0]], ![![297, 7, 0], ![-719, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 97, 0], ![-49, 0, 97]], ![![0, 1, 0], ![-17, 40, 1], ![-17, -6, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-43, -40, 1]] ![![97, 0, 0], ![40, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3880, 97, 0]], ![![-4171, -3880, 97], ![-1649, -1649, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![40, 1, 0]]], ![![![-43, -40, 1]], ![![-17, -17, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-24, -24, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-24, -24, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![77, 77, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-24, -24, 1], ![71, -30, -24], ![-1704, 215, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -77, 101]], ![![-1, -1, 1], ![19, 18, -24], ![6, 25, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [93, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 100], [0, 1]]
 g := ![![[10, 25], [70], [64, 37], [70], [5], [80, 1]], ![[91, 76], [70], [95, 64], [70], [5], [59, 100]]]
 h' := ![![[80, 100], [3, 5], [7, 26], [8, 21], [85, 26], [34, 45], [0, 1]], ![[0, 1], [100, 96], [67, 75], [72, 80], [44, 75], [99, 56], [80, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [48, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [93, 21, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2703, -24, 102]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, -78, 102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![24, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![24, 1, 0]] 
 ![![101, 0, 0], ![24, 1, 0], ![30, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![24, 1, 0], ![0, 24, 1], ![71, -6, 24]]]
  hmulB := by decide  
  f := ![![![1201, 50, 0], ![-5050, 0, 0]], ![![264, 11, 0], ![-1110, 0, 0]], ![![342, 14, 0], ![-1438, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 101, 0], ![-30, 0, 101]], ![![0, 1, 0], ![-6, 24, 1], ![-5, -6, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-24, -24, 1]] ![![101, 0, 0], ![24, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![2424, 101, 0]], ![![-2424, -2424, 101], ![-505, -606, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![24, 1, 0]]], ![![![-24, -24, 1]], ![![-5, -6, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-46, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-46, 1, 0]] 
 ![![103, 0, 0], ![57, 1, 0], ![47, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-46, 1, 0], ![0, -46, 1], ![71, -6, -46]]]
  hmulB := by decide  
  f := ![![![3497, -76, 0], ![7828, 0, 0]], ![![1979, -43, 0], ![4430, 0, 0]], ![![1585, -34, 0], ![3548, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 103, 0], ![-47, 0, 103]], ![![-1, 1, 0], ![25, -46, 1], ![25, -6, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-40, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-40, 1, 0]] 
 ![![103, 0, 0], ![63, 1, 0], ![48, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-40, 1, 0], ![0, -40, 1], ![71, -6, -40]]]
  hmulB := by decide  
  f := ![![![3881, -97, 0], ![9991, 0, 0]], ![![2401, -60, 0], ![6181, 0, 0]], ![![1776, -44, 0], ![4572, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 103, 0], ![-48, 0, 103]], ![![-1, 1, 0], ![24, -40, 1], ![23, -6, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-17, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-17, 1, 0]] 
 ![![103, 0, 0], ![86, 1, 0], ![20, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-17, 1, 0], ![0, -17, 1], ![71, -6, -17]]]
  hmulB := by decide  
  f := ![![![1684, -99, 0], ![10197, 0, 0]], ![![1412, -83, 0], ![8550, 0, 0]], ![![360, -21, 0], ![2180, 1, 0]]]
  g := ![![![1, 0, 0], ![-86, 103, 0], ![-20, 0, 103]], ![![-1, 1, 0], ![14, -17, 1], ![9, -6, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-46, 1, 0]] ![![103, 0, 0], ![-40, 1, 0]]
  ![![103, 0, 0], ![-14, 17, 1]] where
 M := ![![![10609, 0, 0], ![-4120, 103, 0]], ![![-4738, 103, 0], ![1840, -86, 1]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![-26, -16, -1], ![103, 0, 0]]], ![![![-32, -16, -1], ![103, 0, 0]], ![![18, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-14, 17, 1]] ![![103, 0, 0], ![-17, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1751, 103, 0]], ![![-1442, 1751, 103], ![309, -309, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-17, 1, 0]]], ![![![-14, 17, 1]], ![![3, -3, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)


lemma PB105I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 104 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 104 (by omega)

def PB105I2 : PrimesBelowBoundCertificateInterval O 79 104 105 where
  m := 5
  g := ![2, 3, 2, 2, 3]
  P := ![83, 89, 97, 101, 103]
  hP := PB105I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
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
      exact NI103N2
  β := ![I83N1, I89N0, I89N1, I97N1, I101N1, I103N0, I103N1, I103N2]
  Il := ![[I83N1], [I89N0, I89N0, I89N1], [I97N1], [I101N1], [I103N0, I103N1, I103N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
