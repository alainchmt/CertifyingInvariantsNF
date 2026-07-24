
import IdealArithmetic.Examples.NF5_1_8100000_3.RI5_1_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0, 0, 0]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]] where
  M :=![![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![0, 0, 0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 5 2 6 [30, 104, 19, 40, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 84, 37, 91, 45], [87, 100, 84, 12, 3], [92, 16, 100, 68, 26], [83, 13, 100, 43, 33], [0, 1]]
 g := ![![[73, 100, 105, 71, 49], [80, 31, 50, 84, 57], [37, 18, 41, 42], [71, 21, 26, 78, 12], [105, 1], []], ![[73, 66, 42, 70, 66, 49, 69, 8], [17, 50, 37, 52, 11, 45, 56, 17], [71, 92, 98, 90], [46, 45, 42, 44, 55, 23, 55, 15], [84, 38, 44, 9], [25, 92, 10, 10, 106, 68, 34, 68]], ![[28, 65, 88, 100, 73, 74, 26, 33], [61, 96, 60, 11, 4, 78, 89, 92], [59, 67, 90, 10], [83, 71, 99, 4, 45, 45, 4, 34], [25, 74, 15, 53], [80, 31, 20, 82, 95, 18, 56, 27]], ![[14, 102, 95, 104, 30, 48, 39, 73], [78, 102, 44, 13, 72, 11, 59, 24], [70, 103, 3, 33], [61, 49, 60, 5, 82, 9, 77, 18], [16, 90, 6, 79], [52, 82, 32, 36, 96, 3, 32, 28]], ![[39, 106, 94, 42, 95, 78, 33, 100], [79, 29, 34, 10, 102, 0, 20, 29], [39, 89, 76, 9], [30, 9, 30, 38, 0, 34, 42, 57], [59, 56, 27, 83], [45, 30, 97, 35, 70, 28, 20, 92]]]
 h' := ![![[57, 84, 37, 91, 45], [61, 21, 98, 72, 100], [60, 101, 65, 89, 48], [10, 80, 34, 73, 91], [60, 71, 41, 61, 71], [0, 0, 0, 1], [0, 1]], ![[87, 100, 84, 12, 3], [37, 42, 61, 1, 94], [26, 46, 61, 34, 31], [4, 70, 84, 104, 25], [31, 91, 91, 39, 101], [82, 81, 22, 61, 104], [57, 84, 37, 91, 45]], ![[92, 16, 100, 68, 26], [50, 88, 14, 59, 15], [21, 46, 12, 16, 67], [87, 52, 41, 28, 44], [12, 106, 104, 65, 58], [86, 5, 68, 104, 69], [87, 100, 84, 12, 3]], ![[83, 13, 100, 43, 33], [67, 5, 66, 105, 9], [102, 64, 46, 14, 90], [94, 2, 75, 29, 51], [10, 82, 25, 60, 46], [94, 43, 29, 28, 87], [92, 16, 100, 68, 26]], ![[0, 1], [37, 58, 82, 84, 103], [55, 64, 30, 61, 85], [72, 10, 87, 87, 3], [21, 78, 60, 96, 45], [20, 85, 95, 20, 61], [83, 13, 100, 43, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 82, 11, 70], [], [], []]
 b := ![[], [68, 96, 102, 13, 46], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 5
  hpos := by decide
  P := [30, 104, 19, 40, 2, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![190331172, 336328071, -181098035, 53195906, 157696386]
  a := ![-5, -7, -3, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1778796, 3143253, -1692505, 497158, 1473798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 14025517307 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![183, -67, 21, 22, 40]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![183, -67, 21, 22, 40]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![40, 61, 85, 6, 1]] where
  M :=![![![183, -67, 21, 22, 40], ![-58, 26, 13, 24, 4], ![16, -41, 34, 46, 44], ![8, -75, 17, 23, 22], ![-77, 27, -41, -17, -21]]]
  hmulB := by decide  
  f := ![![![1, 1, -1, 0, 0]], ![![0, 0, 1, -2, 0]], ![![-2, -1, 0, 0, -4]], ![![4, 9, -5, 3, 2]], ![![-1, 0, 0, -1, -3]]]
  g := ![![![-13, -23, -31, -2, 40], ![-2, -2, -3, 0, 4], ![-16, -25, -34, -2, 44], ![-8, -13, -17, -1, 22], ![7, 12, 16, 1, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [69, 71, 41, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 63, 61, 81], [29, 65, 83, 24], [45, 89, 74, 4], [0, 1]]
 g := ![![[9, 42, 60, 102], [61, 49, 80], [95, 108, 85, 60], [82, 88, 27, 31], [72, 107, 1], []], ![[26, 35, 71, 14, 56, 66], [36, 3, 78], [48, 34, 73, 83, 35, 48], [17, 68, 11, 61, 14, 80], [19, 107, 49], [60, 20, 62, 102, 5, 66]], ![[107, 62, 19, 80, 84, 77], [106, 90, 74], [78, 93, 32, 39, 58, 39], [46, 1, 51, 35, 92, 96], [36, 35, 49], [68, 68, 90, 88, 18, 90]], ![[10, 89, 5, 107, 9, 93], [81, 105, 7], [18, 16, 53, 69, 60, 36], [31, 102, 65, 104, 107, 4], [73, 103, 7], [103, 41, 73, 17, 45, 64]]]
 h' := ![![[33, 63, 61, 81], [49, 17, 102, 59], [94, 73, 107, 84], [10, 32, 55, 96], [46, 40, 64, 85], [0, 0, 0, 1], [0, 1]], ![[29, 65, 83, 24], [106, 19, 70, 81], [44, 44, 48, 80], [43, 41, 60, 46], [86, 51, 36, 27], [78, 57, 38, 7], [33, 63, 61, 81]], ![[45, 89, 74, 4], [14, 42, 30, 12], [5, 48, 27, 69], [89, 24, 98, 73], [66, 52, 55, 107], [77, 22, 64, 7], [29, 65, 83, 24]], ![[0, 1], [52, 31, 16, 66], [54, 53, 36, 94], [15, 12, 5, 3], [91, 75, 63, 108], [88, 30, 7, 94], [45, 89, 74, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [59, 9, 98], []]
 b := ![[], [], [10, 0, 65, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [69, 71, 41, 2, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2349492964, 7241671544, -7191081001, 4864361399, -202471573]
  a := ![9, -56, 5, -57, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![95856476, 179747133, 91917456, 55772393, -202471573]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-1, -1, 1, 0, 0]] 
 ![![109, 0, 0, 0, 0], ![98, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 0, 0], ![0, 0, -1, 2, 0], ![2, 1, 0, 0, 4], ![-4, -9, 5, -3, -2], ![3, 9, -9, 5, -1]]]
  hmulB := by decide  
  f := ![![![-183, 67, -21, -22, -40]], ![![-164, 60, -19, -20, -36]], ![![-163, 60, -19, -20, -36]], ![![-173, 64, -20, -21, -38]], ![![-142, 52, -16, -17, -31]]]
  g := ![![![0, -1, 1, 0, 0], ![-1, 0, -1, 2, 0], ![-4, 1, 0, 0, 4], ![8, -9, 5, -3, -2], ![-4, 9, -9, 5, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![183, -67, 21, 22, 40]] ![![-1, -1, 1, 0, 0]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7243, -2873, 381, 434, 1380]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![7243, -2873, 381, 434, 1380]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![107, 106, 78, 1, 0], ![76, 21, 32, 0, 1]] where
  M :=![![![7243, -2873, 381, 434, 1380], ![-2326, 1158, -113, -184, -512], ![840, -63, 134, 102, 144], ![1070, -401, 169, 205, 286], ![-3177, 1065, -133, -99, -515]]]
  hmulB := by decide  
  f := ![![![-19, -145, 183, -152, 60]], ![![-272, -288, -25, 154, -364]], ![![882, 1677, -1016, 468, 672]], ![![333, 738, -538, 313, 182]], ![![181, 325, -180, 71, 151]]]
  g := ![![![-1275, -689, -687, 434, 1380], ![498, 278, 271, -184, -512], ![-186, -123, -110, 102, 144], ![-377, -249, -221, 205, 286], ![412, 198, 213, -99, -515]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [65, 106, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 3, 47], [71, 109, 66], [0, 1]]
 g := ![![[32, 5, 9], [29, 25], [30, 57], [18, 64], [77, 42, 60], [1]], ![[89, 34, 61, 58], [44, 28], [59, 25], [81, 7], [69, 111, 110, 84], [47, 83, 71, 89]], ![[81, 60, 71, 45], [19, 91], [82, 53], [35, 11], [20, 49, 104, 103], [82, 60, 82, 24]]]
 h' := ![![[67, 3, 47], [68, 1, 3], [91, 37, 108], [32, 34, 31], [80, 0, 8], [48, 7, 25], [0, 1]], ![[71, 109, 66], [108, 19, 35], [16, 9, 64], [110, 79, 5], [8, 5, 81], [66, 79, 3], [67, 3, 47]], ![[0, 1], [49, 93, 75], [43, 67, 54], [47, 0, 77], [66, 108, 24], [21, 27, 85], [71, 109, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 13], []]
 b := ![[], [71, 16, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [65, 106, 88, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1319, -32, -3590, 7395, 4067]
  a := ![0, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9726, -7693, -6288, 7395, 4067]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 145, -183, 152, -60]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![19, 145, -183, 152, -60]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![56, 70, 1, 0, 0], ![74, 8, 0, 1, 0], ![22, 36, 0, 0, 1]] where
  M :=![![![19, 145, -183, 152, -60], ![272, 288, 25, -154, 364], ![-882, -1677, 1016, -468, -672], ![302, 1369, -1523, 1195, -314], ![615, -129, 1211, -1365, 1357]]]
  hmulB := by decide  
  f := ![![![-7243, 2873, -381, -434, -1380]], ![![2326, -1158, 113, 184, 512]], ![![-2156, 707, -120, -102, -368]], ![![-4588, 1803, -243, -273, -870]], ![![-641, 181, -37, -25, -101]]]
  g := ![![![3, 123, -183, 152, -60], ![20, -118, 25, -154, 364], ![-74, -397, 1016, -468, -672], ![36, 971, -1523, 1195, -314], ![35, -1087, 1211, -1365, 1357]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [35, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 112], [0, 1]]
 g := ![![[53, 97], [25], [28], [53], [101, 51], [66, 1]], ![[14, 16], [25], [28], [53], [77, 62], [19, 112]]]
 h' := ![![[66, 112], [3, 53], [55, 5], [73, 64], [81, 36], [63, 27], [0, 1]], ![[0, 1], [111, 60], [46, 108], [3, 49], [84, 77], [37, 86], [66, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [60, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [35, 47, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95, -2443, 2055, 1776, 3392]
  a := ![9, 27, 5, 26, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2841, -2501, 2055, 1776, 3392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![7243, -2873, 381, 434, 1380]] ![![19, 145, -183, 152, -60]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 125, -17, -28, 42]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-79, 125, -17, -28, 42]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![110, 6, 51, 84, 1]] where
  M :=![![![-79, 125, -17, -28, 42], ![-112, -334, 209, -104, -98], ![92, 483, -530, 412, -110], ![372, 429, 27, -217, 516], ![-715, -1309, 621, -165, -705]]]
  hmulB := by decide  
  f := ![![![-7, -29, 11, 22, 18]], ![![-14, -64, 7, 26, 26]], ![![-26, -111, -12, 14, 26]], ![![-12, -45, -33, -31, -12]], ![![-25, -102, -17, 5, 19]]]
  g := ![![![-37, -1, -17, -28, 42], ![84, 2, 41, 64, -98], ![96, 9, 40, 76, -110], ![-444, -21, -207, -343, 516], ![605, 23, 288, 465, -705]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [38, 30, 88, 103, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 33, 95, 74], [106, 116, 79, 56], [42, 104, 80, 124], [0, 1]]
 g := ![![[30, 32, 77, 8], [4, 101, 17, 34], [62, 54, 12, 69], [105, 87, 84, 87], [45, 107, 24, 1], []], ![[35, 98, 29, 0, 65, 47], [67, 104, 81, 17, 39, 1], [54, 67, 63, 12, 30, 70], [84, 19, 50, 97, 92, 87], [110, 104, 90, 42, 123, 74], [60, 46, 68, 95, 54, 94]], ![[38, 90, 69, 12, 11, 119], [35, 36, 52, 60, 57, 112], [45, 111, 84, 2, 0, 116], [93, 81, 120, 120, 106, 83], [84, 114, 107, 52, 101, 119], [57, 46, 110, 22, 63, 102]], ![[62, 45, 14, 97, 46, 98], [46, 69, 66, 108, 83, 103], [84, 110, 77, 86, 43, 113], [109, 115, 20, 39, 29, 50], [13, 2, 46, 7, 113, 120], [125, 78, 12, 1, 115, 100]]]
 h' := ![![[3, 33, 95, 74], [102, 53, 24, 32], [57, 40, 97, 62], [74, 73, 95, 113], [68, 45, 46, 50], [0, 0, 0, 1], [0, 1]], ![[106, 116, 79, 56], [34, 20, 86, 84], [112, 88, 40, 49], [60, 48, 34, 7], [103, 58, 15, 90], [33, 10, 74, 1], [3, 33, 95, 74]], ![[42, 104, 80, 124], [36, 95, 26, 79], [24, 106, 45, 111], [25, 53, 78, 45], [48, 57, 88, 90], [3, 23, 85, 48], [106, 116, 79, 56]], ![[0, 1], [67, 86, 118, 59], [123, 20, 72, 32], [71, 80, 47, 89], [51, 94, 105, 24], [123, 94, 95, 77], [42, 104, 80, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [101, 79, 89], []]
 b := ![[], [], [92, 23, 2, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [38, 30, 88, 103, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-95062043, -264711545, 232483415, -155772261, -13891088]
  a := ![-11, -9, -5, -7, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11283131, -1428071, 7408889, 7961253, -13891088]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 29, -11, -22, -18]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![7, 29, -11, -22, -18]] 
 ![![127, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![7, 29, -11, -22, -18], ![14, 64, -7, -26, -26], ![26, 111, 12, -14, -26], ![12, 45, 33, 31, 12], ![-13, -61, 27, 51, 41]]]
  hmulB := by decide  
  f := ![![![79, -125, 17, 28, -42]], ![![55, -83, 10, 20, -28]], ![![31, -54, 11, 8, -16]], ![![12, -27, 3, 7, -12]], ![![33, -33, 1, 11, -9]]]
  g := ![![![-5, 29, -11, -22, -18], ![-27, 64, -7, -26, -26], ![-69, 111, 12, -14, -26], ![-54, 45, 33, 31, 12], ![7, -61, 27, 51, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-79, 125, -17, -28, 42]] ![![7, 29, -11, -22, -18]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47458, 20922, -2796, -3739, -9960]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-47458, 20922, -2796, -3739, -9960]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![9, 75, 44, 116, 1]] where
  M :=![![![-47458, 20922, -2796, -3739, -9960], ![16181, -4193, 1002, 629, 2482], ![-4335, 5402, 771, 151, -1224], ![-6791, 3450, 976, 1144, -478], ![20084, -11230, 1656, 2770, 5361]]]
  hmulB := by decide  
  f := ![![![366, 738, -484, 249, 250]], ![![-251, -1119, 1238, -969, 248]], ![![-1465, -1222, -623, 1259, -2186]], ![![2941, 5610, -3416, 1584, 2228]], ![![1971, 3909, -2510, 1256, 1391]]]
  g := ![![![322, 5862, 3324, 8791, -9960], ![-47, -1453, -826, -2193, 2482], ![51, 742, 417, 1085, -1224], ![-19, 300, 168, 432, -478], ![-215, -3155, -1788, -4726, 5361]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [22, 130, 92, 60, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 72, 13, 95], [37, 50, 45, 117], [86, 8, 73, 50], [0, 1]]
 g := ![![[50, 67, 79, 1], [88, 69, 58, 74], [106, 41, 15], [59, 83, 16], [34, 55, 63], [1], []], ![[104, 105, 0, 82, 52, 57], [87, 129, 21, 59, 109, 70], [21, 68, 49], [29, 78, 81], [99, 115, 39], [38, 91, 25], [68, 35, 117]], ![[23, 46, 72, 28, 1, 13], [18, 16, 60, 9, 18, 48], [124, 6, 15], [35, 73, 28], [114, 8, 77], [114, 103, 38], [63, 80, 65]], ![[4, 77, 79, 61, 3, 93], [72, 63, 84, 72, 28, 95], [48, 54, 84], [74, 46, 60], [117, 81, 28], [71, 61, 64], [110, 90, 11]]]
 h' := ![![[79, 72, 13, 95], [29, 18, 4, 1], [20, 46, 38, 104], [16, 100, 113, 43], [129, 90, 114, 4], [109, 1, 39, 71], [0, 0, 1], [0, 1]], ![[37, 50, 45, 117], [30, 14, 84, 70], [12, 95, 26, 124], [122, 102, 122, 124], [74, 59, 75, 122], [5, 118, 98, 68], [29, 63, 15, 5], [79, 72, 13, 95]], ![[86, 8, 73, 50], [127, 52, 104, 44], [35, 90, 82, 77], [76, 92, 41, 43], [45, 116, 114, 91], [8, 93, 121, 83], [114, 38, 125, 118], [37, 50, 45, 117]], ![[0, 1], [14, 47, 70, 16], [35, 31, 116, 88], [82, 99, 117, 52], [111, 128, 90, 45], [14, 50, 4, 40], [129, 30, 121, 8], [86, 8, 73, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 92, 110], []]
 b := ![[], [], [94, 89, 10, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [22, 130, 92, 60, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-89636446, -89561992, -16054456, 57260292, -123749320]
  a := ![6, -4, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7817614, 70165168, 41442104, 110016652, -123749320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-366, -738, 484, -249, -250]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-366, -738, 484, -249, -250]] 
 ![![131, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-366, -738, 484, -249, -250], ![251, 1119, -1238, 969, -248], ![1465, 1222, 623, -1259, 2186], ![-2941, -5610, 3416, -1584, -2228], ![2964, 7630, -6364, 4170, 893]]]
  hmulB := by decide  
  f := ![![![47458, -20922, 2796, 3739, 9960]], ![![11107, -4919, 654, 880, 2338]], ![![31551, -13936, 1851, 2482, 6624]], ![![27947, -12324, 1636, 2189, 5858]], ![![22670, -9976, 1332, 1777, 4749]]]
  g := ![![![117, -738, 484, -249, -250], ![109, 1119, -1238, 969, -248], ![-1003, 1222, 623, -1259, 2186], ![1039, -5610, 3416, -1584, -2228], ![-437, 7630, -6364, 4170, 893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-47458, 20922, -2796, -3739, -9960]] ![![-366, -738, 484, -249, -250]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![827002, -340834, 45160, 54795, 163032]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![827002, -340834, 45160, 54795, 163032]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![35, 11, 112, 66, 1]] where
  M :=![![![827002, -340834, 45160, 54795, 163032], ![-271269, 111797, -14770, -17917, -53442], ![88967, -36746, 4913, 5985, 17608], ![121019, -49986, 6620, 8060, 23902], ![-358248, 147606, -19596, -23770, -70637]]]
  hmulB := by decide  
  f := ![![![6, 50, -64, 53, -22]], ![![97, 105, 6, -53, 128]], ![![-309, -590, 361, -169, -234]], ![![101, 474, -532, 420, -116]], ![![-193, -233, 26, 70, -239]]]
  g := ![![![-35614, -15578, -132952, -78141, 163032], ![11673, 5107, 43582, 25615, -53442], ![-3849, -1682, -14359, -8439, 17608], ![-5223, -2284, -19492, -11456, 23902], ![15431, 6749, 57604, 33856, -70637]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [21, 98, 84, 110, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 64, 87, 72], [1, 115, 3, 121], [118, 94, 47, 81], [0, 1]]
 g := ![![[37, 87, 34, 17], [12, 61, 107], [88, 62, 39], [42, 51, 9, 77], [10, 77, 44], [1], []], ![[2, 66, 135, 55, 21, 126], [105, 106, 17], [26, 113, 38], [118, 80, 69, 2, 128, 60], [10, 116, 133], [84, 136, 87], [132, 15, 115]], ![[75, 94, 51, 23, 36, 8], [132, 3, 28], [100, 110, 129], [84, 61, 119, 90, 58, 122], [87, 95, 37], [93, 121, 88], [74, 103, 119]], ![[20, 61, 12, 69, 75, 50], [17, 66, 103], [39, 58, 7], [91, 56, 126, 108, 73, 11], [102, 123, 38], [70, 41, 60], [31, 85, 122]]]
 h' := ![![[45, 64, 87, 72], [41, 23, 108, 90], [108, 47, 66, 45], [77, 87, 117, 83], [94, 12, 123, 25], [116, 39, 53, 27], [0, 0, 1], [0, 1]], ![[1, 115, 3, 121], [2, 59, 70, 6], [120, 21, 56, 47], [23, 30, 43, 77], [4, 15, 34, 72], [25, 33, 120, 74], [75, 44, 104, 19], [45, 64, 87, 72]], ![[118, 94, 47, 81], [7, 6, 64, 43], [54, 109, 127, 113], [28, 113, 11, 102], [82, 127, 92, 107], [26, 131, 1, 96], [91, 131, 39, 15], [1, 115, 3, 121]], ![[0, 1], [18, 49, 32, 135], [52, 97, 25, 69], [7, 44, 103, 12], [0, 120, 25, 70], [19, 71, 100, 77], [121, 99, 130, 103], [118, 94, 47, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [40, 95, 91], []]
 b := ![[], [], [120, 133, 37, 117], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [21, 98, 84, 110, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![57104360, 93522430, -44660429, -29413510, 39912739]
  a := ![19, 19, 10, 20, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9779865, -2522027, -32955381, -19442732, 39912739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -50, 64, -53, 22]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-6, -50, 64, -53, 22]] 
 ![![137, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![101, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![41, 0, 0, 0, 1]] where
  M :=![![![-6, -50, 64, -53, 22], ![-97, -105, -6, 53, -128], ![309, 590, -361, 169, 234], ![-101, -474, 532, -420, 116], ![-224, 30, -416, 474, -483]]]
  hmulB := by decide  
  f := ![![![-827002, 340834, -45160, -54795, -163032]], ![![-34239, 14111, -1870, -2269, -6750]], ![![-610337, 251540, -33329, -40440, -120320]], ![![-634717, 261588, -34660, -42055, -125126]], ![![-244882, 100924, -13372, -16225, -48275]]]
  g := ![![![-11, -50, 64, -53, 22], ![6, -105, -6, 53, -128], ![43, 590, -361, 169, 234], ![-85, -474, 532, -420, 116], ![85, 30, -416, 474, -483]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![827002, -340834, 45160, 54795, 163032]] ![![-6, -50, 64, -53, 22]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![847, -319, 35, 56, 178]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![847, -319, 35, 56, 178]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![93, 113, 90, 5, 1]] where
  M :=![![![847, -319, 35, 56, 178], ![-300, 48, 37, -52, -66], ![80, 15, -84, 88, -38], ![232, 113, -49, 5, 140], ![-527, -177, 185, -121, -191]]]
  hmulB := by decide  
  f := ![![![3, 11, 7, 6, 2]], ![![2, 6, 15, 18, 10]], ![![-2, -15, 26, 38, 26]], ![![-8, -37, 11, 23, 20]], ![![2, 1, 34, 44, 27]]]
  g := ![![![-113, -147, -115, -6, 178], ![42, 54, 43, 2, -66], ![26, 31, 24, 2, -38], ![-92, -113, -91, -5, 140], ![124, 154, 125, 6, -191]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [88, 53, 4, 131, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 133, 53, 131], [83, 68, 64, 73], [0, 76, 22, 74], [0, 1]]
 g := ![![[113, 136, 103, 117], [25, 88, 50, 45], [60, 102, 117], [74, 76, 133, 131], [133, 31, 64], [1], []], ![[56, 120, 48, 67, 116, 25], [67, 100, 85, 88, 11, 49], [135, 133, 77], [34, 2, 1, 123, 36, 86], [26, 107, 113], [20, 30, 121], [100, 81, 64]], ![[130, 59, 46, 81, 74, 105], [60, 10, 40, 91, 38, 95], [86, 38, 64], [66, 66, 11, 11, 96, 72], [24, 126, 37], [54, 8, 11], [134, 129, 47]], ![[0, 65, 126, 78, 94, 93], [52, 20, 11, 10, 10, 82], [32, 75, 106], [49, 14, 62, 0, 98, 10], [39, 69, 13], [57, 109, 36], [75, 82, 55]]]
 h' := ![![[64, 133, 53, 131], [24, 86, 13, 123], [26, 115, 124, 103], [21, 130, 0, 16], [71, 107, 15, 39], [51, 86, 135, 8], [0, 0, 1], [0, 1]], ![[83, 68, 64, 73], [118, 101, 50, 7], [78, 22, 129, 18], [137, 110, 27, 76], [5, 116, 125, 118], [114, 32, 65, 104], [22, 9, 109, 11], [64, 133, 53, 131]], ![[0, 76, 22, 74], [27, 77, 112, 126], [29, 119, 87, 66], [77, 127, 47, 131], [62, 8, 138, 129], [28, 62, 103, 68], [101, 62, 125, 122], [83, 68, 64, 73]], ![[0, 1], [11, 14, 103, 22], [112, 22, 77, 91], [136, 50, 65, 55], [50, 47, 0, 131], [29, 98, 114, 98], [72, 68, 43, 6], [0, 76, 22, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [104, 76, 13], []]
 b := ![[], [], [12, 123, 5, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [88, 53, 4, 131, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![397566, 88739, 564271, -746457, 738307]
  a := ![1, -3, 1, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-491115, -599568, -473981, -31928, 738307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -11, -7, -6, -2]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-3, -11, -7, -6, -2]] 
 ![![139, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-3, -11, -7, -6, -2], ![-2, -6, -15, -18, -10], ![2, 15, -26, -38, -26], ![8, 37, -11, -23, -20], ![7, 27, 15, 11, 3]]]
  hmulB := by decide  
  f := ![![![-847, 319, -35, -56, -178]], ![![-790, 298, -33, -52, -166]], ![![-354, 133, -14, -24, -74]], ![![-349, 130, -14, -23, -74]], ![![-569, 217, -25, -37, -119]]]
  g := ![![![17, -11, -7, -6, -2], ![26, -6, -15, -18, -10], ![30, 15, -26, -38, -26], ![-7, 37, -11, -23, -20], ![-38, 27, 15, 11, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![847, -319, 35, 56, 178]] ![![-3, -11, -7, -6, -2]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -1, 1, 2, 2]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![9, -1, 1, 2, 2]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![69, 76, 1, 0, 0], ![60, 127, 0, 1, 0], ![59, 58, 0, 0, 1]] where
  M :=![![![9, -1, 1, 2, 2], ![-2, 2, 3, 2, 2], ![-2, -7, 6, 6, 2], ![2, -1, -3, 7, 4], ![-5, -7, 3, -7, 1]]]
  hmulB := by decide  
  f := ![![![15, -5, -1, -4, -2]], ![![0, 20, -9, -4, -6]], ![![7, 8, -5, -4, -4]], ![![6, 15, -8, -5, -6]], ![![6, 6, -4, -3, -3]]]
  g := ![![![-2, -3, 1, 2, 2], ![-3, -4, 3, 2, 2], ![-6, -9, 6, 6, 2], ![-3, -6, -3, 7, 4], ![1, 4, 3, -7, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [90, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 148], [0, 1]]
 g := ![![[86, 103], [63], [125, 68], [144], [22, 113], [64], [1]], ![[16, 46], [63], [73, 81], [144], [32, 36], [64], [1]]]
 h' := ![![[8, 148], [104, 38], [74, 19], [64, 98], [106, 137], [105, 115], [59, 8], [0, 1]], ![[0, 1], [110, 111], [77, 130], [103, 51], [10, 12], [131, 34], [123, 141], [8, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [4, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [90, 141, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1623, -4485, 3033, 933, -114]
  a := ![13, 9, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1746, -2328, 3033, 933, -114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1796, 740, -98, -119, -354]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-1796, 740, -98, -119, -354]] 
 ![![149, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-1796, 740, -98, -119, -354], ![589, -243, 32, 39, 116], ![-193, 80, -11, -13, -38], ![-263, 108, -14, -18, -52], ![778, -320, 42, 52, 153]]]
  hmulB := by decide  
  f := ![![![-12, -100, 26, 75, 80]], ![![-5, -39, 10, 28, 30]], ![![-9, -72, 17, 53, 56]], ![![-1, -12, 2, 8, 10]], ![![-6, -44, 12, 31, 33]]]
  g := ![![![-48, 740, -98, -119, -354], ![16, -243, 32, 39, 116], ![-5, 80, -11, -13, -38], ![-7, 108, -14, -18, -52], ![21, -320, 42, 52, 153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63, 41, -165, 176, -158]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-63, 41, -165, 176, -158]] 
 ![![149, 0, 0, 0, 0], ![79, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![-63, 41, -165, 176, -158], ![492, 738, -275, 4, 510], ![-1016, -2329, 1758, -1056, -502], ![-272, 729, -1529, 1479, -1060], ![1721, 1735, 289, -1089, 2363]]]
  hmulB := by decide  
  f := ![![![-755677, 311525, -41339, -50186, -149058]], ![![-398997, 164487, -21828, -26500, -78704]], ![![-86763, 35772, -4747, -5764, -17116]], ![![-173178, 71395, -9473, -11501, -34160]], ![![-459324, 189354, -25126, -30503, -90601]]]
  g := ![![![53, 41, -165, 176, -158], ![-669, 738, -275, 4, 510], ![1575, -2329, 1758, -1056, -502], ![96, 729, -1529, 1479, -1060], ![-2136, 1735, 289, -1089, 2363]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2

def I149N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-58, -38, -14, -3, 0]] i)))

def SI149N3: IdealEqSpanCertificate' Table ![![-58, -38, -14, -3, 0]] 
 ![![149, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-58, -38, -14, -3, 0], ![-3, -75, -38, -31, -6], ![-19, -42, -87, -101, -56], ![7, 74, -58, -94, -70], ![50, 122, 22, -6, -21]]]
  hmulB := by decide  
  f := ![![![898, 1638, -926, 379, 738]], ![![523, 945, -526, 209, 436]], ![![9, 42, -47, 37, -10]], ![![517, 938, -526, 212, 428]], ![![762, 1366, -750, 290, 643]]]
  g := ![![![24, -38, -14, -3, 0], ![67, -75, -38, -31, -6], ![131, -42, -87, -101, -56], ![71, 74, -58, -94, -70], ![-50, 122, 22, -6, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N3 : Nat.card (O ⧸ I149N3) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N3)

lemma isPrimeI149N3 : Ideal.IsPrime I149N3 := prime_ideal_of_norm_prime hp149.out _ NI149N3
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![9, -1, 1, 2, 2]] ![![-1796, 740, -98, -119, -354]]
  ![![-15916, 6559, -869, -1055, -3138]] where
 M := ![![![-15916, 6559, -869, -1055, -3138]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![-15916, 6559, -869, -1055, -3138]] ![![-63, 41, -165, 176, -158]]
  ![![-898, -1638, 926, -379, -738]] where
 M := ![![![-898, -1638, 926, -379, -738]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI149N2 : IdealMulLeCertificate' Table 
  ![![-898, -1638, 926, -379, -738]] ![![-58, -38, -14, -3, 0]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2, I149N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
    exact isPrimeI149N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1 ⊙ MulI149N2)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-274, 137, -5, -11, -54]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-274, 137, -5, -11, -54]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![63, 4, 107, 1, 0], ![23, 33, 51, 0, 1]] where
  M :=![![![-274, 137, -5, -11, -54], ![97, -20, 29, 33, 32], ![-31, -1, 44, 59, 34], ![-53, -39, 19, 40, 26], ![109, -101, -15, -5, 25]]]
  hmulB := by decide  
  f := ![![![0, 7, -9, 7, -4]], ![![15, 18, -1, -7, 18]], ![![-43, -83, 54, -27, -32]], ![![-30, -55, 34, -16, -24]], ![![-11, -23, 17, -10, -7]]]
  g := ![![![11, 13, 26, -11, -54], ![-18, -8, -34, 33, 32], ![-30, -9, -53, 59, 34], ![-21, -7, -37, 40, 26], ![-1, -6, -5, -5, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [66, 47, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 76, 46], [122, 74, 105], [0, 1]]
 g := ![![[78, 117, 55], [34, 11, 138], [30, 126, 25], [49, 78], [52, 88, 100], [108, 1], []], ![[50, 74, 76, 53], [147, 106, 132, 41], [78, 150, 28, 150], [49, 21], [93, 79, 31, 54], [24, 40], [111, 2]], ![[94, 18, 71, 43], [140, 30, 23, 10], [105, 127, 111, 50], [100, 118], [2, 77, 49, 68], [105, 38], [52, 2]]]
 h' := ![![[137, 76, 46], [21, 79, 31], [134, 126, 17], [108, 46, 146], [41, 108, 57], [120, 143, 141], [0, 0, 1], [0, 1]], ![[122, 74, 105], [6, 113, 39], [74, 96, 108], [82, 111, 85], [121, 138, 126], [109, 21, 100], [118, 73, 74], [137, 76, 46]], ![[0, 1], [6, 110, 81], [149, 80, 26], [102, 145, 71], [71, 56, 119], [139, 138, 61], [127, 78, 76], [122, 74, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 2], []]
 b := ![[], [149, 90, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [66, 47, 43, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34514, 112619, -122899, 79287, -9529]
  a := ![7, 7, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31400, 728, -53779, 79287, -9529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -21, 23, -18, 4]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-5, -21, 23, -18, 4]] 
 ![![151, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![146, 0, 0, 0, 1]] where
  M :=![![![-5, -21, 23, -18, 4], ![-26, -20, -13, 24, -40], ![104, 185, -100, 38, 88], ![-56, -189, 187, -137, 14], ![-39, 77, -179, 177, -133]]]
  hmulB := by decide  
  f := ![![![-33857, 14037, -1837, -2248, -6692]], ![![-1720, 714, -93, -114, -340]], ![![-19531, 8098, -1059, -1296, -3860]], ![![-22679, 9402, -1230, -1505, -4482]], ![![-32639, 13531, -1771, -2167, -6451]]]
  g := ![![![-4, -21, 23, -18, 4], ![31, -20, -13, 24, -40], ![-62, 185, -100, 38, 88], ![-20, -189, 187, -137, 14], ![109, 77, -179, 177, -133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![114, -46, 6, 7, 22]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![114, -46, 6, 7, 22]] 
 ![![151, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![108, 0, 0, 0, 1]] where
  M :=![![![114, -46, 6, 7, 22], ![-37, 17, -2, -3, -8], ![13, -2, 1, 1, 2], ![17, -6, 2, 2, 4], ![-50, 18, -2, -2, -9]]]
  hmulB := by decide  
  f := ![![![10, 10, 26, -21, 12]], ![![5, 5, 14, -11, 6]], ![![7, 8, 15, -12, 8]], ![![1, 0, 4, -3, 2]], ![![6, 6, 18, -14, 7]]]
  g := ![![![5, -46, 6, 7, 22], ![-2, 17, -2, -3, -8], ![-1, -2, 1, 1, 2], ![-1, -6, 2, 2, 4], ![-2, 18, -2, -2, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-274, 137, -5, -11, -54]] ![![-5, -21, 23, -18, 4]]
  ![![10, 10, 26, -21, 12]] where
 M := ![![![10, 10, 26, -21, 12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![10, 10, 26, -21, 12]] ![![114, -46, 6, 7, 22]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB178I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB178I3 : PrimesBelowBoundCertificateInterval O 103 151 178 where
  m := 9
  g := ![1, 2, 2, 2, 2, 2, 2, 4, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB178I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2, I149N3]
    · exact ![I151N0, I151N1, I151N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![14025517307]
    · exact ![141158161, 109]
    · exact ![1442897, 12769]
    · exact ![260144641, 127]
    · exact ![294499921, 131]
    · exact ![352275361, 137]
    · exact ![373301041, 139]
    · exact ![22201, 149, 149, 149]
    · exact ![3442951, 151, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
      exact NI149N3
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I109N1, I127N1, I131N1, I137N1, I139N1, I149N1, I149N2, I149N3, I151N1, I151N2]
  Il := ![[], [I109N1], [], [I127N1], [I131N1], [I137N1], [I139N1], [I149N1, I149N2, I149N3], [I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
