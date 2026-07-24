
import IdealArithmetic.Examples.NF5_3_303750000_1.RI5_3_303750000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -7, 25, -13, 14]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![23, -7, 25, -13, 14]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![84, 47, 88, 1, 0], ![72, 89, 30, 0, 1]] where
  M :=![![![23, -7, 25, -13, 14], ![-12, 36, -91, 65, -76], ![4, -42, 115, -84, 104], ![-52, 213, -491, 368, -436], ![20, -45, 145, -95, 123]]]
  hmulB := by decide  
  f := ![![![9, 11, 5, -1, -2]], ![![16, 0, 33, 5, -12]], ![![-12, -24, -17, 2, 8]], ![![4, -11, 4, 3, 0]], ![![16, 1, 26, 4, -9]]]
  g := ![![![1, -6, 7, -13, 14], ![0, 35, -33, 65, -76], ![-4, -50, 41, -84, 104], ![4, 203, -185, 368, -436], ![-8, -61, 45, -95, 123]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [22, 79, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 63, 20], [39, 43, 87], [0, 1]]
 g := ![![[85, 77, 34], [52, 47, 23], [64, 49], [79, 100, 14], [61, 37], [1]], ![[3, 97, 54, 95], [97, 57, 31, 21], [69, 13], [32, 53, 48, 38], [60, 10], [97, 102, 37, 82]], ![[103, 46, 11, 14], [85, 32, 16, 33], [25, 89], [94, 48, 79, 12], [82, 61], [52, 89, 47, 25]]]
 h' := ![![[56, 63, 20], [33, 69, 26], [17, 96, 68], [81, 16, 7], [105, 90, 11], [85, 28, 95], [0, 1]], ![[39, 43, 87], [91, 35, 37], [81, 104, 29], [84, 94, 86], [12, 76, 26], [35, 75, 44], [56, 63, 20]], ![[0, 1], [67, 3, 44], [96, 14, 10], [2, 104, 14], [34, 48, 70], [74, 4, 75], [39, 43, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 47], []]
 b := ![[], [105, 69, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [22, 79, 12, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180369816, -207734362, -294910788, 6064100, -209073466]
  a := ![-20, -41, -39, 24, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![134238648, 169297116, 50875256, 6064100, -209073466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, -38, -70, -14, 12]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-205, -38, -70, -14, 12]] 
 ![![107, 0, 0, 0, 0], ![29, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![-205, -38, -70, -14, 12], ![-80, -143, -126, -30, -88], ![-8, -124, -97, -24, -88], ![-560, -902, -806, -191, -544], ![-464, -662, -602, -142, -389]]]
  hmulB := by decide  
  f := ![![![-103, -382, -150, 18, 92]], ![![-33, -101, -52, 4, 28]], ![![-96, -364, -137, 16, 88]], ![![2, -22, 2, 9, -8]], ![![-87, -336, -124, 16, 79]]]
  g := ![![![67, -38, -70, -14, 12], ![237, -143, -126, -30, -88], ![204, -124, -97, -24, -88], ![1496, -902, -806, -191, -544], ![1099, -662, -602, -142, -389]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -55, 111, 25, -46]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![53, -55, 111, 25, -46]] 
 ![![107, 0, 0, 0, 0], ![97, 1, 0, 0, 0], ![85, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![53, -55, 111, 25, -46], ![-152, -314, -277, 15, 108], ![-84, 232, -189, -66, 80], ![256, 537, 467, -28, -180], ![232, 45, 461, 57, -187]]]
  hmulB := by decide  
  f := ![![![3571, 515, 1103, 217, -318]], ![![3245, 483, 1014, 200, -278]], ![![2833, 423, 886, 175, -242]], ![![2361, 434, 802, 161, -142]], ![![2221, 388, 738, 148, -149]]]
  g := ![![![-26, -55, 111, 25, -46], ![428, -314, -277, 15, 108], ![-67, 232, -189, -66, 80], ![-728, 537, 467, -28, -180], ![-328, 45, 461, 57, -187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![23, -7, 25, -13, 14]] ![![-205, -38, -70, -14, 12]]
  ![![-3571, -515, -1103, -217, 318]] where
 M := ![![![-3571, -515, -1103, -217, 318]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-3571, -515, -1103, -217, 318]] ![![53, -55, 111, 25, -46]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 25, 15, -2, -5]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![9, 25, 15, -2, -5]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![76, 35, 1, 0, 0], ![79, 41, 0, 1, 0], ![42, 40, 0, 0, 1]] where
  M :=![![![9, 25, 15, -2, -5], ![36, -17, 72, 14, -26], ![-28, -50, -53, 2, 24], ![-40, 58, -96, -17, 62], ![14, 94, 12, -10, 13]]]
  hmulB := by decide  
  f := ![![![495, 19, 129, 12, -67]], ![![-72, 19, -72, 38, -38]], ![![320, 19, 67, 20, -58]], ![![329, 22, 63, 25, -65]], ![![164, 14, 24, 18, -39]]]
  g := ![![![-7, -2, 15, -2, -5], ![-50, -19, 72, 14, -26], ![26, 7, -53, 2, 24], ![55, 15, -96, -17, 62], ![-6, -4, 12, -10, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [95, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 108], [0, 1]]
 g := ![![[63, 84], [84], [94, 61], [51, 7], [25], [10, 1]], ![[31, 25], [84], [50, 48], [12, 102], [25], [20, 108]]]
 h' := ![![[10, 108], [41, 53], [8, 53], [60, 72], [3, 15], [31, 5], [0, 1]], ![[0, 1], [26, 56], [102, 56], [17, 37], [44, 94], [81, 104], [10, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [35, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [95, 99, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![169745, 185966, 300530, -27721, 219035]
  a := ![-37, -75, -76, 33, -127]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-272294, -164747, 300530, -27721, 219035]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, -2, 146, 29, -89]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![491, -2, 146, 29, -89]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![78, 69, 1, 0, 0], ![52, 28, 0, 1, 0], ![61, 66, 0, 0, 1]] where
  M :=![![![491, -2, 146, 29, -89], ![-124, -104, -127, -1, 54], ![-240, 82, -101, -32, 56], ![-152, 161, 129, -14, -34], ![34, -7, 147, 21, -57]]]
  hmulB := by decide  
  f := ![![![1, 144, -230, 201, -211]], ![![268, -288, 1399, -843, 1186]], ![![170, -72, 708, -379, 588]], ![![84, -19, 323, -164, 266]], ![![167, -79, 709, -384, 590]]]
  g := ![![![-64, -46, 146, 29, -89], ![60, 47, -127, -1, 54], ![54, 39, -101, -32, 56], ![-68, -56, 129, -14, -34], ![-83, -64, 147, 21, -57]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [25, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 108], [0, 1]]
 g := ![![[20, 48], [71], [60, 25], [11, 21], [27], [45, 1]], ![[0, 61], [71], [95, 84], [84, 88], [27], [90, 108]]]
 h' := ![![[45, 108], [100, 22], [26, 92], [52, 104], [5, 81], [74, 38], [0, 1]], ![[0, 1], [0, 87], [24, 17], [45, 5], [53, 28], [40, 71], [45, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [96, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [25, 64, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5508, 5897, 9514, -599, 6458]
  a := ![-5, -11, -10, 6, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10086, -9725, 9514, -599, 6458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 40, 76, 3, -33]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![39, 40, 76, 3, -33]] 
 ![![109, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![39, 40, 76, 3, -33], ![20, -186, 63, 37, -42], ![-120, -66, -229, -24, 80], ![-120, 199, -217, -88, 6], ![42, 151, 101, -29, -101]]]
  hmulB := by decide  
  f := ![![![90701, 4298, 21628, 3639, -14075]], ![![18194, 866, 4329, 737, -2832]], ![![76172, 3604, 18177, 3046, -11808]], ![![42820, 2051, 10157, 1758, -6694]], ![![28216, 1331, 6743, 1121, -4365]]]
  g := ![![![-63, 40, 76, 3, -33], ![-20, -186, 63, 37, -42], ![192, -66, -229, -24, 80], ![182, 199, -217, -88, 6], ![-70, 151, 101, -29, -101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![9, 25, 15, -2, -5]] ![![491, -2, 146, 29, -89]]
  ![![-2147, -1675, -4369, -321, 1742]] where
 M := ![![![-2147, -1675, -4369, -321, 1742]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-2147, -1675, -4369, -321, 1742]] ![![39, 40, 76, 3, -33]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![518731, 713187, 977403, 14170, -386187]]]
 hmul := by decide  
 g := ![![![![4759, 6543, 8967, 130, -3543]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, -3352, 526, 649, -265]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![115, -3352, 526, 649, -265]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![73, 37, 106, 1, 0], ![21, 99, 12, 0, 1]] where
  M :=![![![115, -3352, 526, 649, -265], ![-5936, -3406, -11603, -1037, 4662], ![1536, 9308, 2261, -1282, -776], ![10100, 5983, 19725, 1730, -7922], ![3902, -6791, 8421, 2343, -3525]]]
  hmulB := by decide  
  f := ![![![-395, -30, -38, -51, 113]], ![![64, 138, -173, 177, -182]], ![![248, -66, 375, -196, 252]], ![![1, -29, 262, -150, 241]], ![![11, 109, -114, 123, -108]]]
  g := ![![![-369, -10, -576, 649, -265], ![-249, -3775, 375, -1037, 4662], ![986, 1182, 1305, -1282, -776], ![444, 6427, -607, 1730, -7922], ![-824, 2261, -1749, 2343, -3525]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [33, 15, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 61, 73], [74, 51, 40], [0, 1]]
 g := ![![[101, 111, 97], [6, 2], [50, 52], [102, 69], [50, 94, 98], [1]], ![[5, 29, 75, 19], [58, 62], [70, 11], [40, 8], [8, 33, 37, 10], [106, 67, 52, 71]], ![[56, 56, 40, 103], [9, 112], [32, 14], [33, 57], [11, 27, 96, 3], [86, 3, 7, 42]]]
 h' := ![![[57, 61, 73], [43, 56, 53], [44, 100, 62], [15, 78, 74], [45, 62, 71], [80, 98, 18], [0, 1]], ![[74, 51, 40], [79, 58, 11], [33, 93, 66], [14, 78, 89], [59, 98, 11], [104, 2, 49], [57, 61, 73]], ![[0, 1], [99, 112, 49], [82, 33, 98], [11, 70, 63], [99, 66, 31], [106, 13, 46], [74, 51, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 72], []]
 b := ![[], [108, 108, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [33, 15, 95, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1850360129, 2094501943, 3090763228, -120283032, 2206248289]
  a := ![46, 95, 92, -54, 215]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-315930908, -1874987668, -94108096, -120283032, 2206248289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12031, -578, -2834, -505, 1899]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-12031, -578, -2834, -505, 1899]] 
 ![![113, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![90, 0, 0, 0, 1]] where
  M :=![![![-12031, -578, -2834, -505, 1899], ![1632, 104, 401, 75, -242], ![5576, 290, 1335, 236, -860], ![6540, 473, 1645, 314, -934], ![1206, 167, 373, 69, -107]]]
  hmulB := by decide  
  f := ![![![-6137, 8332, -13038, -3253, 5425]], ![![-1552, 2696, -3349, -931, 1402]], ![![-955, 1116, -2013, -473, 835]], ![![-748, 13, -1501, -212, 610]], ![![-5144, 6627, -10897, -2661, 4529]]]
  g := ![![![-943, -578, -2834, -505, 1899], ![105, 104, 401, 75, -242], ![411, 290, 1335, 236, -860], ![369, 473, 1645, 314, -934], ![-19, 167, 373, 69, -107]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, -4, 2, -2]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-1, 0, -4, 2, -2]] 
 ![![113, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-1, 0, -4, 2, -2], ![0, -3, 10, -10, 12], ![0, 8, -13, 12, -16], ![8, -34, 74, -51, 60], ![-4, 2, -22, 14, -17]]]
  hmulB := by decide  
  f := ![![![-3817, -184, -908, -162, 602]], ![![-2968, -143, -706, -126, 468]], ![![-660, -32, -157, -28, 104]], ![![-1435, -70, -342, -61, 226]], ![![-2024, -98, -482, -86, 319]]]
  g := ![![![1, 0, -4, 2, -2], ![-2, -3, 10, -10, 12], ![0, 8, -13, 12, -16], ![1, -34, 74, -51, 60], ![6, 2, -22, 14, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![115, -3352, 526, 649, -265]] ![![-12031, -578, -2834, -505, 1899]]
  ![![3817, 184, 908, 162, -602]] where
 M := ![![![3817, 184, 908, 162, -602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![3817, 184, 908, 162, -602]] ![![-1, 0, -4, 2, -2]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2453, -44, -762, 34, 218]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-2453, -44, -762, 34, 218]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![110, 41, 39, 1, 0], ![105, 47, 58, 0, 1]] where
  M :=![![![-2453, -44, -762, 34, 218], ![416, -325, 940, -612, 708], ![1008, 494, -849, 854, -1156], ![1808, -1854, 5176, -3471, 4072], ![92, 522, -1244, 950, -1177]]]
  hmulB := by decide  
  f := ![![![-11, 8, -10, -10, -22]], ![![-48, -155, -20, -12, -124]], ![![-128, -206, -183, -22, -44]], ![![-70, -113, -79, -21, -76]], ![![-89, -149, -104, -24, -87]]]
  g := ![![![-229, -92, -116, 34, 218], ![-52, -67, -128, -612, 708], ![224, 156, 259, 854, -1156], ![-346, -401, -753, -3471, 4072], ![151, 133, 236, 950, -1177]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [101, 54, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [116, 97, 2], [98, 29, 125], [0, 1]]
 g := ![![[24, 117, 31], [69, 6, 42], [58, 124, 81], [118, 25, 44], [15, 10, 76], [1]], ![[55, 75, 98, 13], [63, 87, 104, 44], [36, 70, 74, 44], [71, 2, 8, 25], [71, 68, 115, 8], [35, 32, 82, 8]], ![[3, 7, 118, 45], [104, 86, 107, 67], [9, 74, 54, 56], [81, 124, 112, 89], [24, 67, 94, 33], [53, 68, 33, 119]]]
 h' := ![![[116, 97, 2], [16, 115, 44], [111, 111, 114], [20, 74, 9], [9, 126, 60], [26, 73, 87], [0, 1]], ![[98, 29, 125], [112, 121, 109], [9, 109, 99], [53, 20, 28], [121, 62, 87], [87, 117, 2], [116, 97, 2]], ![[0, 1], [8, 18, 101], [126, 34, 41], [41, 33, 90], [49, 66, 107], [103, 64, 38], [98, 29, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 115], []]
 b := ![[], [34, 74, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [101, 54, 40, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-515462486, -571202714, -880481397, 50294662, -631924075]
  a := ![-27, -60, -55, 38, -147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![474835847, 213127147, 266217505, 50294662, -631924075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -8, 10, 10, 22]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![11, -8, 10, 10, 22]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![28, 54, 1, 0, 0], ![57, 28, 0, 1, 0], ![60, 124, 0, 0, 1]] where
  M :=![![![11, -8, 10, 10, 22], ![48, 155, 20, 12, 124], ![128, 206, 183, 22, 44], ![720, 842, 976, 217, 432], ![468, 530, 604, 158, 359]]]
  hmulB := by decide  
  f := ![![![2453, 44, 762, -34, -218]], ![![-416, 325, -940, 612, -708]], ![![356, 144, -225, 246, -340]], ![![995, 106, 94, 147, -286]], ![![752, 334, -548, 574, -785]]]
  g := ![![![-17, -28, 10, 10, 22], ![-68, -131, 20, 12, 124], ![-70, -124, 183, 22, 44], ![-511, -878, 976, 217, 432], ![-370, -638, 604, 158, 359]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [103, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [100, 126], [0, 1]]
 g := ![![[110, 37], [5, 19], [41, 72], [101, 19], [79, 81], [100, 1]], ![[0, 90], [0, 108], [2, 55], [96, 108], [51, 46], [73, 126]]]
 h' := ![![[100, 126], [120, 75], [95, 107], [11, 96], [118, 107], [114, 118], [0, 1]], ![[0, 1], [0, 52], [0, 20], [86, 31], [23, 20], [103, 9], [100, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [54, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [103, 27, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4409, -276, 18786, -10862, 15712]
  a := ![2, 16, 14, -18, 32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6655, -20936, 18786, -10862, 15712]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-2453, -44, -762, 34, 218]] ![![11, -8, 10, 10, 22]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 18, -32, 25, -25]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-11, 18, -32, 25, -25]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![45, 23, 85, 1, 0], ![14, 38, 102, 0, 1]] where
  M :=![![![-11, 18, -32, 25, -25], ![36, -36, 179, -107, 150], ![0, 100, -179, 150, -164], ![208, -191, 1015, -600, 858], ![58, 205, -131, 193, -139]]]
  hmulB := by decide  
  f := ![![![-23, -32, -16, 3, 7]], ![![-44, 12, -93, -15, 38]], ![![40, 74, 61, -4, -24]], ![![11, 39, 19, -4, -7]], ![![16, 57, 19, -7, -7]]]
  g := ![![![-6, 3, 3, 25, -25], ![21, -25, -46, -107, 150], ![-34, 22, 29, 150, -164], ![116, -145, -271, -600, 858], ![-51, 8, -18, 193, -139]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [98, 74, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 13, 27], [55, 117, 104], [0, 1]]
 g := ![![[5, 105, 7], [72, 69, 39], [40, 7], [10, 43], [54, 38], [89, 1], []], ![[36, 23, 96, 48], [54, 74, 106, 64], [31, 77], [70, 84], [38, 114], [7, 65], [83, 74]], ![[14, 46, 122, 26], [79, 92, 72, 37], [104, 129], [108, 9], [4, 15], [94, 38], [6, 74]]]
 h' := ![![[34, 13, 27], [18, 85, 111], [56, 27, 68], [96, 28, 20], [91, 72, 49], [55, 128, 118], [0, 0, 1], [0, 1]], ![[55, 117, 104], [71, 47, 86], [35, 123, 39], [86, 112, 83], [38, 109, 79], [15, 20, 101], [96, 66, 117], [34, 13, 27]], ![[0, 1], [100, 130, 65], [101, 112, 24], [72, 122, 28], [62, 81, 3], [42, 114, 43], [79, 65, 13], [55, 117, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 101], []]
 b := ![[], [128, 21, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [98, 74, 42, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3420862676, 4134416605, 5262584243, 175250838, 3660941458]
  a := ![60, 102, 106, -52, 251]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-425332866, -1061161283, -2924044013, 175250838, 3660941458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -32, -16, 3, 7]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-23, -32, -16, 3, 7]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![98, 110, 1, 0, 0], ![35, 125, 0, 1, 0], ![56, 81, 0, 0, 1]] where
  M :=![![![-23, -32, -16, 3, 7], ![-44, 12, -93, -15, 38], ![40, 74, 61, -4, -24], ![88, -17, 163, 26, -66], ![10, -89, 25, 19, -11]]]
  hmulB := by decide  
  f := ![![![-11, 18, -32, 25, -25]], ![![36, -36, 179, -107, 150]], ![![22, -16, 125, -70, 106]], ![![33, -31, 170, -100, 143]], ![![18, -13, 96, -54, 81]]]
  g := ![![![8, 6, -16, 3, 7], ![57, 69, -93, -15, 38], ![-34, -32, 61, -4, -24], ![-100, -121, 163, 26, -66], ![-19, -33, 25, 19, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [76, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 130], [0, 1]]
 g := ![![[124, 74], [84, 114], [7], [77], [43], [64], [1]], ![[61, 57], [79, 17], [7], [77], [43], [64], [1]]]
 h' := ![![[8, 130], [35, 27], [91, 30], [19, 20], [32, 48], [126, 82], [55, 8], [0, 1]], ![[0, 1], [120, 104], [69, 101], [48, 111], [23, 83], [127, 49], [119, 123], [8, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [48, 119]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [76, 123, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![390, 500, 1320, -1035, 2075]
  a := ![0, 3, 2, -4, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1595, -1400, 1320, -1035, 2075]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-11, 18, -32, 25, -25]] ![![-23, -32, -16, 3, 7]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -18, -12, -3, -9]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-13, -18, -12, -3, -9]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![45, 135, 25, 1, 0], ![93, 94, 130, 0, 1]] where
  M :=![![![-13, -18, -12, -3, -9], ![-60, -82, -81, -15, -42], ![-48, -60, -61, -18, -36], ![-336, -459, -429, -94, -294], ![-246, -351, -303, -75, -205]]]
  hmulB := by decide  
  f := ![![![-59, 0, -12, -3, 9]], ![![12, -2, 9, 3, -6]], ![![24, -6, 1, 0, 0]], ![![-3, -3, 5, 2, -3]], ![![-9, -7, -1, 0, 2]]]
  g := ![![![7, 9, 9, -3, -9], ![33, 43, 42, -15, -42], ![30, 42, 37, -18, -36], ![228, 291, 293, -94, -294], ![162, 212, 206, -75, -205]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [124, 79, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 67, 90], [77, 69, 47], [0, 1]]
 g := ![![[17, 88, 100], [112, 39], [79, 8], [13, 19, 1], [81, 135], [24, 1], []], ![[66, 125, 79, 3], [84, 109], [112, 18], [109, 53, 82, 21], [74, 120], [33, 103], [1, 17]], ![[131, 107, 29, 66], [126, 7], [112, 2], [61, 92, 132, 21], [56, 81], [135, 105], [44, 17]]]
 h' := ![![[84, 67, 90], [102, 6, 127], [133, 104, 54], [32, 44, 75], [31, 71, 136], [38, 35, 86], [0, 0, 1], [0, 1]], ![[77, 69, 47], [60, 132, 124], [8, 69, 71], [14, 41, 93], [22, 72, 19], [29, 9, 42], [82, 27, 69], [84, 67, 90]], ![[0, 1], [81, 136, 23], [118, 101, 12], [124, 52, 106], [93, 131, 119], [119, 93, 9], [62, 110, 67], [77, 69, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99], []]
 b := ![[], [61, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [124, 79, 113, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1811305809, 2002277690, 3104717714, -187396580, 2235371278]
  a := ![45, 91, 91, -56, 217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1442666985, -1334482366, -2064296598, -187396580, 2235371278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93, -201, -169, 11, 66]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-93, -201, -169, 11, 66]] 
 ![![137, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-93, -201, -169, 11, 66], ![-248, 304, -525, -125, 220], ![308, 406, 581, 12, -228], ![440, -489, 919, 216, -368], ![-88, -705, -119, 107, 47]]]
  hmulB := by decide  
  f := ![![![403015, 19479, 95169, 16865, -63394]], ![![93740, 4532, 22133, 3925, -14748]], ![![231037, 11165, 54562, 9665, -36338]], ![![142571, 6898, 33650, 5979, -22442]], ![![114453, 5530, 27032, 4786, -17999]]]
  g := ![![![121, -201, -169, 11, 66], ![212, 304, -525, -125, 220], ![-367, 406, 581, 12, -228], ![-385, -489, 919, 216, -368], ![181, -705, -119, 107, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1871, 783, 975, 211, 206]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![1871, 783, 975, 211, 206]] 
 ![![137, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![85, 0, 0, 0, 1]] where
  M :=![![![1871, 783, 975, 211, 206], ![2400, 3548, 3207, 759, 2100], ![1668, 3126, 2741, 652, 1940], ![15504, 22323, 20259, 4788, 13136], ![11736, 16335, 14913, 3511, 9547]]]
  hmulB := by decide  
  f := ![![![6475, 54471, 8193, -8207, -2494]], ![![4420, 31904, 6057, -4631, -1972]], ![![4083, 35967, 5024, -5473, -1490]], ![![5101, 51900, 5664, -8119, -1506]], ![![3755, 34788, 4470, -5348, -1283]]]
  g := ![![![-1435, 783, 975, 211, 206], ![-6260, 3548, 3207, 759, 2100], ![-5501, 3126, 2741, 652, 1940], ![-39403, 22323, 20259, 4788, 13136], ![-28857, 16335, 14913, 3511, 9547]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-13, -18, -12, -3, -9]] ![![-93, -201, -169, 11, 66]]
  ![![1449, 81, 2989, 352, -1401]] where
 M := ![![![1449, 81, 2989, 352, -1401]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![1449, 81, 2989, 352, -1401]] ![![1871, 783, 975, 211, 206]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-3093597, -4262070, -3896554, -917489, -2484221]]]
 hmul := by decide  
 g := ![![![![-22581, -31110, -28442, -6697, -18133]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [45, 105, 14, 52, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 88, 14, 55, 114], [57, 23, 131, 9, 107], [98, 97, 58, 4, 8], [117, 69, 75, 71, 49], [0, 1]]
 g := ![![[74, 38, 4, 85, 42], [10, 106, 60, 118, 120], [6, 25, 120, 7], [33, 112, 34, 43, 96], [125, 87, 0, 1], [], []], ![[42, 0, 104, 80, 5, 138], [90, 84, 136, 112, 123, 92, 111, 50], [132, 6, 63, 1], [28, 16, 42, 16, 102, 43, 78, 126], [81, 38, 88, 131], [33, 50, 130, 116], [35, 127, 30, 69]], ![[13, 115, 97, 17, 118, 10, 35, 38], [56, 41, 29, 106, 39, 126, 58, 118], [4, 54, 20, 34], [117, 95, 33, 101, 22, 38, 51, 137], [88, 14, 20, 136], [90, 19, 52, 36], [100, 26, 119, 51]], ![[47, 92, 93, 117, 88, 94, 19, 135], [47, 23, 21, 105, 131, 42, 75, 138], [104, 122, 19, 79], [48, 18, 37, 79, 70, 117, 1, 97], [14, 61, 87, 129], [102, 87, 79, 46], [16, 118, 64, 64]], ![[9, 78, 83, 71, 37, 25, 121, 113], [16, 60, 22, 66, 29, 130, 59, 96], [47, 75, 42, 31], [33, 6, 47, 57, 17, 36, 77, 35], [12, 14, 96, 9], [97, 39, 29, 79], [62, 129, 8, 38]]]
 h' := ![![[6, 88, 14, 55, 114], [106, 22, 78, 22, 43], [137, 102, 26, 110, 113], [44, 29, 105, 50, 29], [74, 57, 96, 21, 97], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[57, 23, 131, 9, 107], [33, 136, 72, 28], [74, 127, 97, 98, 89], [68, 20, 137, 38, 138], [133, 101, 120, 15, 36], [5, 3, 16, 6, 100], [129, 6, 104, 82, 33], [6, 88, 14, 55, 114]], ![[98, 97, 58, 4, 8], [107, 11, 103, 37, 76], [95, 8, 30, 103, 127], [54, 132, 29, 82, 112], [15, 26, 7, 96, 104], [120, 120, 134, 41, 85], [0, 126, 1, 42, 133], [57, 23, 131, 9, 107]], ![[117, 69, 75, 71, 49], [40, 13, 120, 56, 25], [129, 57, 110, 32, 82], [19, 20, 94, 45, 45], [69, 118, 98, 76, 51], [2, 6, 73, 108, 95], [127, 68, 1, 91, 18], [98, 97, 58, 4, 8]], ![[0, 1], [111, 96, 44, 135, 134], [14, 123, 15, 74, 6], [34, 77, 52, 63, 93], [32, 115, 96, 70, 129], [135, 10, 55, 123, 136], [57, 78, 32, 63, 94], [117, 69, 75, 71, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138, 32, 31, 83], [], [], []]
 b := ![[], [54, 37, 30, 23, 20], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [45, 105, 14, 52, 0, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![456539562405527, 560705028793112, 685444744610330, 39396138117537, 467700527297633]
  a := ![18, 39, 36, -24, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3284457283493, 4033849128008, 4931257155470, 283425454083, 3364751994947]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 51888844699 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-629, -34, -118, -29, 61]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-629, -34, -118, -29, 61]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![19, 146, 86, 107, 1]] where
  M :=![![![-629, -34, -118, -29, 61], ![-4, -266, -73, 1, -110], ![128, -130, -197, -32, -56], ![-312, -633, -777, -220, -534], ![-330, -489, -435, -141, -433]]]
  hmulB := by decide  
  f := ![![![-15, 56, -142, 103, -125]], ![![68, -258, 653, -473, 574]], ![![-88, 332, -843, 610, -740]], ![![384, -1449, 3681, -2666, 3234]], ![![289, -1092, 2772, -2008, 2436]]]
  g := ![![![-12, -60, -36, -44, 61], ![14, 106, 63, 79, -110], ![8, 54, 31, 40, -56], ![66, 519, 303, 382, -534], ![53, 421, 247, 310, -433]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [17, 94, 31, 88, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 13, 12, 99], [85, 46, 46, 32], [43, 89, 91, 18], [0, 1]]
 g := ![![[39, 60, 35, 6], [102, 145, 33], [62, 107, 92, 102], [60, 101, 19], [99, 13, 146, 145], [1], []], ![[99, 128, 37, 3, 128, 87], [126, 147, 73], [38, 63, 56, 66, 13, 93], [121, 88, 68], [130, 89, 43, 43, 3, 57], [93, 12, 129], [107, 65, 116]], ![[139, 69, 116, 116, 28, 128], [94, 100, 49], [59, 88, 64, 140, 137, 8], [136, 29, 121], [15, 133, 66, 120, 51, 48], [128, 22, 125], [102, 146, 130]], ![[3, 3, 27, 3, 76, 2], [29, 74, 104], [0, 61, 14, 44, 63, 59], [12, 17, 133], [124, 127, 41, 79, 108, 137], [86, 8, 35], [23, 94, 26]]]
 h' := ![![[82, 13, 12, 99], [26, 109, 141, 30], [138, 138, 84, 35], [22, 93, 33, 20], [105, 0, 148, 82], [132, 55, 118, 61], [0, 0, 1], [0, 1]], ![[85, 46, 46, 32], [135, 14, 82, 22], [108, 132, 22, 85], [110, 113, 74, 67], [9, 117, 42, 51], [53, 92, 120, 96], [137, 58, 125, 24], [82, 13, 12, 99]], ![[43, 89, 91, 18], [12, 137, 11, 147], [57, 108, 68, 142], [103, 73, 9, 74], [110, 81, 131, 138], [96, 115, 4, 134], [127, 71, 78, 42], [85, 46, 46, 32]], ![[0, 1], [87, 38, 64, 99], [122, 69, 124, 36], [58, 19, 33, 137], [34, 100, 126, 27], [9, 36, 56, 7], [117, 20, 94, 83], [43, 89, 91, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [32, 49, 72], []]
 b := ![[], [], [76, 18, 118, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [17, 94, 31, 88, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![319960667547, 404756266768, 461526838318, 43891323974, 311002462160]
  a := ![21, 37, 37, -19, 92]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37510645057, -302024182608, -176407281258, -223042765954, 311002462160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -56, 142, -103, 125]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![15, -56, 142, -103, 125]] 
 ![![149, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![126, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![15, -56, 142, -103, 125], ![-68, 258, -653, 473, -574], ![88, -332, 843, -610, 740], ![-384, 1449, -3681, 2666, -3234], ![102, -387, 981, -711, 863]]]
  hmulB := by decide  
  f := ![![![629, 34, 118, 29, -61]], ![![152, 10, 29, 7, -14]], ![![168, 10, 33, 8, -16]], ![![534, 33, 105, 26, -48]], ![![589, 35, 113, 28, -54]]]
  g := ![![![-54, -56, 142, -103, 125], ![248, 258, -653, 473, -574], ![-320, -332, 843, -610, 740], ![1398, 1449, -3681, 2666, -3234], ![-373, -387, 981, -711, 863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-629, -34, -118, -29, 61]] ![![15, -56, 142, -103, 125]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0, 0, 0]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]] where
  M :=![![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![0, 0, 0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 5 2 7 [124, 35, 48, 66, 65, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 65, 108, 20, 16], [148, 9, 39, 55, 68], [20, 112, 97, 25, 23], [64, 115, 58, 51, 44], [0, 1]]
 g := ![![[140, 76, 2, 19, 45], [81, 52, 34, 44, 55], [141, 45, 88, 37, 45], [23, 10, 30, 25], [141, 120, 82, 86, 1], [], []], ![[99, 76, 91, 65, 17, 85, 114, 85], [134, 101, 103, 141, 136, 95, 133, 5], [138, 125, 82, 104, 125, 53, 84, 84], [13, 52, 11, 99], [129, 14, 30, 104, 93, 123, 1, 16], [71, 36, 138, 145], [77, 9, 6, 105]], ![[72, 45, 82, 109, 127, 115, 94, 49], [2, 115, 143, 102, 50, 40, 10, 17], [132, 114, 54, 147, 19, 38, 21, 80], [6, 62, 130, 148], [70, 114, 79, 106, 87, 117, 93, 62], [133, 108, 55, 58], [132, 51, 11, 94]], ![[70, 140, 124, 26, 143, 93, 113, 6], [54, 52, 109, 42, 25, 104, 3, 115], [29, 14, 80, 40, 22, 38, 140, 14], [109, 136, 36, 59], [33, 144, 103, 129, 81, 130, 20, 67], [112, 17, 106, 137], [56, 140, 136, 76]], ![[91, 9, 7, 147, 112, 15, 77, 50], [105, 82, 26, 124, 142, 87, 136, 11], [57, 43, 122, 67, 34, 89, 34, 138], [8, 67, 79, 29], [123, 91, 40, 1, 33, 145, 35, 17], [132, 112, 133, 121], [32, 67, 52, 124]]]
 h' := ![![[5, 65, 108, 20, 16], [73, 46, 14, 89, 137], [32, 9, 0, 129, 31], [135, 7, 13, 95, 14], [32, 117, 4, 90, 5], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[148, 9, 39, 55, 68], [117, 120, 135, 105, 85], [113, 48, 107, 148, 24], [127, 95, 112, 20, 63], [94, 132, 137, 117, 34], [54, 99, 87, 131, 1], [141, 10, 97, 26, 30], [5, 65, 108, 20, 16]], ![[20, 112, 97, 25, 23], [134, 18, 140, 127, 15], [136, 48, 116, 130, 76], [49, 8, 55, 121, 111], [75, 97, 138, 75, 65], [1, 90, 15, 103, 118], [100, 25, 26, 123, 80], [148, 9, 39, 55, 68]], ![[64, 115, 58, 51, 44], [16, 80, 67, 86, 124], [68, 2, 114, 11, 96], [46, 31, 113, 62, 77], [24, 98, 94, 82, 19], [38, 68, 148, 1, 45], [100, 109, 126, 91, 52], [20, 112, 97, 25, 23]], ![[0, 1], [65, 38, 97, 46, 92], [109, 44, 116, 35, 75], [103, 10, 9, 4, 37], [75, 9, 80, 89, 28], [16, 45, 52, 67, 137], [128, 7, 52, 62, 140], [64, 115, 58, 51, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 68, 72, 147], [], [], []]
 b := ![[], [21, 39, 27, 2, 38], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 5
  hpos := by decide
  P := [124, 35, 48, 66, 65, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-402464218105225475, -480742085276631691, -626136551816014458, -15714628152150580, -432306707428736526]
  a := ![-75, -156, -157, 98, -371]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2665325947716725, -3183722419050541, -4146599680900758, -104070385113580, -2862958327342626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 78502725751 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀



lemma PB853I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB853I3 : PrimesBelowBoundCertificateInterval O 103 151 853 where
  m := 9
  g := ![3, 3, 3, 2, 2, 3, 1, 2, 1]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB853I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
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
    · exact ![1225043, 107, 107]
    · exact ![11881, 11881, 109]
    · exact ![1442897, 113, 113]
    · exact ![2048383, 16129]
    · exact ![2248091, 17161]
    · exact ![2571353, 137, 137]
    · exact ![51888844699]
    · exact ![492884401, 149]
    · exact ![78502725751]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
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
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
  β := ![I107N1, I107N2, I109N2, I113N1, I113N2, I137N1, I137N2, I149N1]
  Il := ![[I107N1, I107N2], [I109N2], [I113N1, I113N2], [], [], [I137N1, I137N2], [], [I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
