
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [28, 22, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 14, 9], [56, 68, 74], [0, 1]]
 g := ![![[16, 71, 38], [42, 64, 9], [3, 30], [40, 25], [9, 23, 1], []], ![[56, 13, 67, 37], [35, 72, 63, 17], [20, 1], [12, 40], [12, 80, 30, 33], [40, 81]], ![[71, 44, 56, 58], [77, 71, 56, 54], [57, 3], [15, 61], [79, 37, 48, 62], [58, 81]]]
 h' := ![![[50, 14, 9], [69, 5, 11], [27, 73, 3], [51, 69, 69], [80, 71, 5], [0, 0, 1], [0, 1]], ![[56, 68, 74], [61, 15, 46], [15, 11, 31], [34, 40, 1], [72, 56, 66], [52, 78, 68], [50, 14, 9]], ![[0, 1], [49, 63, 26], [19, 82, 49], [11, 57, 13], [79, 39, 12], [18, 5, 14], [56, 68, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 64], []]
 b := ![[], [33, 39, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [28, 22, 60, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5324450, -42994, -79846]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64150, -518, -962]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [9, 25, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 59, 78], [25, 29, 11], [0, 1]]
 g := ![![[28, 69, 50], [33, 67], [0, 20], [23, 45, 73], [62, 40, 1], []], ![[45, 84, 66, 25], [73, 78], [68, 72], [78, 34, 4, 11], [67, 64, 13, 5], [71, 32]], ![[10, 11, 87, 55], [74, 40], [84, 84], [59, 69, 46, 81], [27, 14, 79, 21], [49, 32]]]
 h' := ![![[15, 59, 78], [57, 56, 36], [40, 23, 45], [60, 41, 38], [65, 48, 47], [0, 0, 1], [0, 1]], ![[25, 29, 11], [55, 54, 72], [0, 9, 73], [73, 7, 28], [17, 8, 34], [31, 63, 29], [15, 59, 78]], ![[0, 1], [71, 68, 70], [84, 57, 60], [67, 41, 23], [34, 33, 8], [6, 26, 59], [25, 29, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 24], []]
 b := ![[], [38, 66, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [9, 25, 49, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50373288, 1535428, -999648]
  a := ![-13, 10, 28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![565992, 17252, -11232]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-36, -31, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-36, -31, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![61, 66, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-36, -31, 1], ![368, -222, -409], ![-5810, 14, 156]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-61, -66, 97]], ![![-1, -1, 1], ![261, 276, -409], ![-158, -106, 156]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [59, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 96], [0, 1]]
 g := ![![[16, 89], [32], [93], [22], [61], [26, 1]], ![[2, 8], [32], [93], [22], [61], [52, 96]]]
 h' := ![![[26, 96], [88, 63], [91, 56], [7, 53], [23, 33], [18, 35], [0, 1]], ![[0, 1], [77, 34], [92, 41], [27, 44], [8, 64], [55, 62], [26, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [49, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [59, 71, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14378935, 7823925, 1186360]
  a := ![326, -389, -717]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-597825, -726555, 1186360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![21, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![21, 1, 0]] 
 ![![97, 0, 0], ![21, 1, 0], ![38, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![21, 1, 0], ![-6, 27, 13], ![182, 0, 15]]]
  hmulB := by decide  
  f := ![![![14350, -66958, -32227], ![2425, 240463, 0]], ![![3090, -14478, -6968], ![583, 51992, 0]], ![![5621, -26231, -12625], ![953, 94202, 0]]]
  g := ![![![1, 0, 0], ![-21, 97, 0], ![-38, 0, 97]], ![![0, 1, 0], ![-11, 27, 13], ![-4, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-36, -31, 1]] ![![97, 0, 0], ![21, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![2037, 97, 0]], ![![-3492, -3007, 97], ![-388, -873, -388]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![21, 1, 0]]], ![![![-36, -31, 1]], ![![-4, -9, -4]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![10, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![10, 1, 0]] 
 ![![101, 0, 0], ![10, 1, 0], ![96, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![10, 1, 0], ![-6, 16, 13], ![182, 0, 4]]]
  hmulB := by decide  
  f := ![![![33603, -90297, -73346], ![2525, 569842, 0]], ![![3318, -8931, -7254], ![304, 56358, 0]], ![![31948, -85826, -69715], ![2314, 541632, 0]]]
  g := ![![![1, 0, 0], ![-10, 101, 0], ![-96, 0, 101]], ![![0, 1, 0], ![-14, 16, 13], ![-2, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![32, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![32, 1, 0]] 
 ![![101, 0, 0], ![32, 1, 0], ![7, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![32, 1, 0], ![-6, 38, 13], ![182, 0, 26]]]
  hmulB := by decide  
  f := ![![![5673, -38774, -13260], ![1414, 103020, 0]], ![![1778, -12279, -4199], ![506, 32623, 0]], ![![371, -2688, -919], ![168, 7140, 0]]]
  g := ![![![1, 0, 0], ![-32, 101, 0], ![-7, 0, 101]], ![![0, 1, 0], ![-13, 38, 13], ![0, 0, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-42, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-42, 1, 0]] 
 ![![101, 0, 0], ![59, 1, 0], ![93, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-42, 1, 0], ![-6, -36, 13], ![182, 0, -48]]]
  hmulB := by decide  
  f := ![![![-5465, -37603, 13572], ![1919, -105444, 0]], ![![-3191, -21935, 7917], ![1112, -61509, 0]], ![![-5013, -34625, 12497], ![1813, -97092, 0]]]
  g := ![![![1, 0, 0], ![-59, 101, 0], ![-93, 0, 101]], ![![-1, 1, 0], ![9, -36, 13], ![46, 0, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![10, 1, 0]] ![![101, 0, 0], ![32, 1, 0]]
  ![![101, 0, 0], ![-38, 27, 1]] where
 M := ![![![10201, 0, 0], ![3232, 101, 0]], ![![1010, 101, 0], ![314, 48, 13]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![32, 1, 0], ![0, 0, 0]]], ![![![10, 1, 0], ![0, 0, 0]], ![![8, -3, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-38, 27, 1]] ![![101, 0, 0], ![-42, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4242, 101, 0]], ![![-3838, 2727, 101], ![1616, -1010, 303]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-42, 1, 0]]], ![![![-38, 27, 1]], ![![16, -10, 3]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![38, 7, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![38, 7, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![38, 7, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![38, 7, 1], ![140, 80, 85], ![1106, 14, 2]]]
  hmulB := by decide  
  f := ![![![-37, -7, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -7, 103]], ![![0, 0, 1], ![-30, -5, 85], ![10, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [76, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 102], [0, 1]]
 g := ![![[20, 61], [68, 30], [11, 59], [72], [23], [25, 1]], ![[0, 42], [97, 73], [44, 44], [72], [23], [50, 102]]]
 h' := ![![[25, 102], [85, 79], [91, 37], [69, 70], [59, 22], [57, 34], [0, 1]], ![[0, 1], [0, 24], [89, 66], [68, 33], [94, 81], [83, 69], [25, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [45, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [76, 78, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19067, 10558, -331]
  a := ![13, -11, -28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, 125, -331]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![18, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![18, 1, 0]] 
 ![![103, 0, 0], ![18, 1, 0], ![101, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![18, 1, 0], ![-6, 24, 13], ![182, 0, 12]]]
  hmulB := by decide  
  f := ![![![11431, -46888, -25389], ![1648, 201159, 0]], ![![1992, -8187, -4433], ![310, 35123, 0]], ![![11219, -45977, -24896], ![1559, 197253, 0]]]
  g := ![![![1, 0, 0], ![-18, 103, 0], ![-101, 0, 103]], ![![0, 1, 0], ![-17, 24, 13], ![-10, 0, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![38, 7, 1]] ![![103, 0, 0], ![18, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![1854, 103, 0]], ![![3914, 721, 103], ![824, 206, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![18, 1, 0]]], ![![![38, 7, 1]], ![![8, 2, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-44, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-44, 1, 0]] 
 ![![107, 0, 0], ![63, 1, 0], ![52, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-44, 1, 0], ![-6, -38, 13], ![182, 0, -50]]]
  hmulB := by decide  
  f := ![![![-9083, -65922, 22542], ![3210, -185538, 0]], ![![-5327, -38778, 13260], ![1927, -109140, 0]], ![![-4408, -32037, 10955], ![1575, -90168, 0]]]
  g := ![![![1, 0, 0], ![-63, 107, 0], ![-52, 0, 107]], ![![-1, 1, 0], ![16, -38, 13], ![26, 0, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-19, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-19, 1, 0]] 
 ![![107, 0, 0], ![88, 1, 0], ![104, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-19, 1, 0], ![-6, -13, 13], ![182, 0, -25]]]
  hmulB := by decide  
  f := ![![![26800, 59709, -59670], ![-4173, 491130, 0]], ![![22037, 49094, -49062], ![-3423, 403818, 0]], ![![26047, 58035, -57997], ![-4065, 477360, 0]]]
  g := ![![![1, 0, 0], ![-88, 107, 0], ![-104, 0, 107]], ![![-1, 1, 0], ![-2, -13, 13], ![26, 0, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-44, 1, 0]] ![![107, 0, 0], ![-44, 1, 0]]
  ![![107, 0, 0], ![25, -31, 1]] where
 M := ![![![11449, 0, 0], ![-4708, 107, 0]], ![![-4708, 107, 0], ![1930, -82, 13]]]
 hmul := by decide  
 g := ![![![![82, 31, -1], ![107, 0, 0]], ![![-44, 1, 0], ![0, 0, 0]]], ![![![-44, 1, 0], ![0, 0, 0]], ![![15, 3, 0], ![13, 0, 0]]]]
 hle2 := by decide  
def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![25, -31, 1]] ![![107, 0, 0], ![-19, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2033, 107, 0]], ![![2675, -3317, 107], ![-107, 428, -428]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-19, 1, 0]]], ![![![25, -31, 1]], ![![-1, 4, -4]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 37, 24]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![293, 37, 24]] 
 ![![109, 0, 0], ![0, 109, 0], ![44, 106, 1]] where
  M :=![![![293, 37, 24], ![4146, 515, 337], ![2702, 336, 215]]]
  hmulB := by decide  
  f := ![![![-23, 1, 1]], ![![176, -17, 7]], ![![162, -16, 7]]]
  g := ![![![-7, -23, 24], ![-98, -323, 337], ![-62, -206, 215]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [100, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 108], [0, 1]]
 g := ![![[68, 12], [93], [36, 46], [39, 5], [78], [67, 1]], ![[0, 97], [93], [66, 63], [47, 104], [78], [25, 108]]]
 h' := ![![[67, 108], [83, 98], [106, 23], [24, 41], [33, 88], [58, 29], [0, 1]], ![[0, 1], [0, 11], [12, 86], [46, 68], [43, 21], [39, 80], [67, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [81, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [100, 42, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4826, 2282, -143]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102, 160, -143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 1, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-23, 1, 1]] 
 ![![109, 0, 0], ![45, 1, 0], ![41, 0, 1]] where
  M :=![![![-23, 1, 1], ![176, -17, 7], ![14, 14, -23]]]
  hmulB := by decide  
  f := ![![![293, 37, 24]], ![![159, 20, 13]], ![![135, 17, 11]]]
  g := ![![![-1, 1, 1], ![6, -17, 7], ![3, 14, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![293, 37, 24]] ![![-23, 1, 1]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-21, 51, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-21, 51, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![92, 51, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-21, 51, 1], ![-124, 285, 657], ![9114, 14, -321]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -51, 113]], ![![-1, 0, 1], ![-536, -294, 657], ![342, 145, -321]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [87, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 112], [0, 1]]
 g := ![![[87, 13], [30], [91], [100], [61, 109], [2, 1]], ![[0, 100], [30], [91], [100], [53, 4], [4, 112]]]
 h' := ![![[2, 112], [74, 76], [56, 97], [17, 54], [4, 10], [52, 30], [0, 1]], ![[0, 1], [0, 37], [24, 16], [12, 59], [24, 103], [112, 83], [2, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [90, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [87, 111, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167269, 16589, 9157]
  a := ![-11, 31, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5975, -3986, 9157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![21, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![21, 1, 0]] 
 ![![113, 0, 0], ![21, 1, 0], ![95, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![21, 1, 0], ![-6, 27, 13], ![182, 0, 15]]]
  hmulB := by decide  
  f := ![![![27805, -128556, -61880], ![4068, 537880, 0]], ![![5157, -23875, -11492], ![792, 99892, 0]], ![![23377, -108078, -52023], ![3414, 452200, 0]]]
  g := ![![![1, 0, 0], ![-21, 113, 0], ![-95, 0, 113]], ![![0, 1, 0], ![-16, 27, 13], ![-11, 0, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-21, 51, 1]] ![![113, 0, 0], ![21, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2373, 113, 0]], ![![-2373, 5763, 113], ![-565, 1356, 678]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![21, 1, 0]]], ![![![-21, 51, 1]], ![![-5, 12, 6]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-59, -45, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-59, -45, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![68, 82, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-59, -45, 1], ![452, -329, -591], ![-8358, 14, 217]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -82, 127]], ![![-1, -1, 1], ![320, 379, -591], ![-182, -140, 217]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [17, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 126], [0, 1]]
 g := ![![[66, 15], [58, 94], [4, 74], [30, 35], [126, 71], [21, 1]], ![[0, 112], [0, 33], [34, 53], [3, 92], [93, 56], [42, 126]]]
 h' := ![![[21, 126], [30, 53], [59, 100], [125, 70], [17, 110], [24, 43], [0, 1]], ![[0, 1], [0, 74], [0, 27], [71, 57], [41, 17], [38, 84], [21, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [45, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [17, 106, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17326, 7398, -1155]
  a := ![11, -9, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![482, 804, -1155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-44, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-44, 1, 0]] 
 ![![127, 0, 0], ![83, 1, 0], ![37, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-44, 1, 0], ![-6, -38, 13], ![182, 0, -50]]]
  hmulB := by decide  
  f := ![![![50131, 349372, -119483], ![-14478, 1167257, 0]], ![![32737, 228303, -78078], ![-9524, 762762, 0]], ![![14629, 101785, -34810], ![-4149, 340067, 0]]]
  g := ![![![1, 0, 0], ![-83, 127, 0], ![-37, 0, 127]], ![![-1, 1, 0], ![21, -38, 13], ![16, 0, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-59, -45, 1]] ![![127, 0, 0], ![-44, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-5588, 127, 0]], ![![-7493, -5715, 127], ![3048, 1651, -635]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-44, 1, 0]]], ![![![-59, -45, 1]], ![![24, 13, -5]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![19, -62, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![19, -62, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![19, 69, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![19, -62, 1], ![554, -353, -812], ![-11452, 14, 397]]]
  hmulB := by decide  
  f := ![![![-18, 62, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -69, 131]], ![![0, -1, 1], ![122, 425, -812], ![-145, -209, 397]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [109, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 130], [0, 1]]
 g := ![![[100, 125], [28, 35], [9], [91], [61], [74], [1]], ![[0, 6], [0, 96], [9], [91], [61], [74], [1]]]
 h' := ![![[104, 130], [92, 115], [25, 64], [58, 128], [26, 22], [16, 89], [22, 104], [0, 1]], ![[0, 1], [0, 16], [0, 67], [8, 3], [87, 109], [102, 42], [96, 27], [104, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [109, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [109, 27, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8379, 10517, 2275]
  a := ![-12, 13, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-266, -1118, 2275]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![26, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![26, 1, 0]] 
 ![![131, 0, 0], ![26, 1, 0], ![127, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![26, 1, 0], ![-6, 32, 13], ![182, 0, 20]]]
  hmulB := by decide  
  f := ![![![47659, -262137, -106470], ![7467, 1072890, 0]], ![![9438, -52012, -21125], ![1573, 212875, 0]], ![![46199, -254133, -103219], ![7263, 1040130, 0]]]
  g := ![![![1, 0, 0], ![-26, 131, 0], ![-127, 0, 131]], ![![0, 1, 0], ![-19, 32, 13], ![-18, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![19, -62, 1]] ![![131, 0, 0], ![26, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![3406, 131, 0]], ![![2489, -8122, 131], ![1048, -1965, -786]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![26, 1, 0]]], ![![![19, -62, 1]], ![![8, -15, -6]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [83, 9, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 81, 58], [33, 55, 79], [0, 1]]
 g := ![![[86, 26, 105], [33, 129], [28, 4], [112, 55, 99], [74, 56], [19, 1], []], ![[110, 101, 61, 75], [51, 11], [28, 74], [34, 7, 49, 54], [9, 78], [115, 11], [17, 76]], ![[44, 93, 135, 70], [110, 126], [121, 63], [115, 103, 120, 40], [48, 112], [110, 122], [133, 76]]]
 h' := ![![[123, 81, 58], [37, 120, 70], [131, 32, 35], [20, 125, 2], [128, 106, 109], [67, 20, 78], [0, 0, 1], [0, 1]], ![[33, 55, 79], [28, 120, 124], [39, 121, 82], [87, 65, 99], [58, 96, 87], [95, 4, 107], [18, 39, 55], [123, 81, 58]], ![[0, 1], [32, 34, 80], [95, 121, 20], [0, 84, 36], [6, 72, 78], [47, 113, 89], [51, 98, 81], [33, 55, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 49], []]
 b := ![[], [124, 83, 96], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [83, 9, 118, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-414512817, -9961270, -7645970]
  a := ![25, -30, -55]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3025641, -72710, -55810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB264I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB264I2 : PrimesBelowBoundCertificateInterval O 79 137 264 where
  m := 11
  g := ![1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB264I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![2571353]
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
      exact NI107N0
      exact NI107N1
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
  β := ![I97N1, I101N0, I101N1, I101N2, I103N1, I107N0, I107N1, I109N1, I113N1, I127N1, I131N1]
  Il := ![[], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N0, I107N0, I107N1], [I109N1], [I113N1], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
