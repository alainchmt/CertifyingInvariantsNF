
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![364, 92, -43, -87, -105]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![364, 92, -43, -87, -105]] 
 ![![67, 0, 0, 0, 0], ![0, 67, 0, 0, 0], ![0, 0, 67, 0, 0], ![0, 0, 0, 67, 0], ![1, 54, 17, 64, 1]] where
  M :=![![![364, 92, -43, -87, -105], ![1260, 303, -154, -296, -348], ![4176, 1054, -497, -1004, -1184], ![6474, 1598, -760, -1533, -1834], ![7905, 1956, -955, -1873, -2212]]]
  hmulB := by decide  
  f := ![![![-14, -4, -1, 1, 1]], ![![-12, -15, -2, 0, 4]], ![![-48, -10, 1, 4, 0]], ![![6, -18, -8, 1, 6]], ![![-17, -32, -9, 2, 9]]]
  g := ![![![7, 86, 26, 99, -105], ![24, 285, 86, 328, -348], ![80, 970, 293, 1116, -1184], ![124, 1502, 454, 1729, -1834], ![151, 1812, 547, 2085, -2212]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 4 2 6 [9, 18, 39, 49, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 58, 43, 39], [0, 42, 17, 28], [62, 33, 7], [0, 1]]
 g := ![![[57, 56, 40, 1], [18, 6, 36, 16], [57, 8, 6], [3, 6, 56], [1], []], ![[40, 41, 42, 62, 54, 40], [55, 46, 65, 11, 9, 16], [62, 8, 17], [8, 62, 47], [61, 31, 4], [8, 46, 47]], ![[8, 8, 33, 26, 19, 52], [29, 21, 6, 5, 50, 48], [26, 45, 37], [35, 59, 4], [59, 33, 4], [7, 56, 47]], ![[23, 34, 63, 49, 27], [57, 40, 2, 20, 18], [10, 48, 39], [49, 32, 10], [53, 53, 16], [49]]]
 h' := ![![[23, 58, 43, 39], [39, 38, 56, 66], [58, 53, 65, 63], [54, 15, 29, 26], [58, 49, 28, 18], [0, 0, 1], [0, 1]], ![[0, 42, 17, 28], [65, 23, 25, 49], [61, 24, 59, 3], [4, 51, 30, 33], [64, 42, 14, 39], [55, 33, 27, 65], [23, 58, 43, 39]], ![[62, 33, 7], [7, 54, 24, 50], [31, 16, 62, 24], [59, 24, 2, 29], [21, 33, 20, 65], [4, 40, 60, 65], [0, 42, 17, 28]], ![[0, 1], [46, 19, 29, 36], [60, 41, 15, 44], [63, 44, 6, 46], [54, 10, 5, 12], [53, 61, 46, 4], [62, 33, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 35, 33], []]
 b := ![[], [], [56, 2, 57, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 4
  hpos := by decide
  P := [9, 18, 39, 49, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5035490889, -1252349084, 432788151, 1164277244, 1628434167]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-99461568, -1331161106, -406725264, -1538141932, 1628434167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 20151121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -4, -1, 1, 1]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![-14, -4, -1, 1, 1]] 
 ![![67, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-14, -4, -1, 1, 1], ![-12, -15, -2, 0, 4], ![-48, -10, 1, 4, 0], ![6, -18, -8, 1, 6], ![-45, -8, 1, 1, 2]]]
  hmulB := by decide  
  f := ![![![364, 92, -43, -87, -105]], ![![84, 21, -10, -20, -24]], ![![372, 94, -44, -89, -107]], ![![390, 98, -46, -93, -112]], ![![319, 80, -38, -76, -91]]]
  g := ![![![0, -4, -1, 1, 1], ![2, -15, -2, 0, 4], ![-3, -10, 1, 4, 0], ![6, -18, -8, 1, 6], ![-2, -8, 1, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![364, 92, -43, -87, -105]] ![![-14, -4, -1, 1, 1]]
  ![![67, 0, 0, 0, 0]] where
 M := ![![![67, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36478, -21775, -3292, 2169, 5129]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-36478, -21775, -3292, 2169, 5129]] 
 ![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![26, 18, 11, 19, 1]] where
  M :=![![![-36478, -21775, -3292, 2169, 5129], ![-61548, -36810, -5597, 3674, 8676], ![-104112, -62143, -9454, 6158, 14696], ![-57402, -34109, -5039, 3405, 7978], ![-91377, -54741, -8378, 5467, 12922]]]
  hmulB := by decide  
  f := ![![![-476, 279, 42, 37, -69]], ![![828, -540, -71, -54, 148]], ![![-1776, 959, 160, 154, -216]], ![![882, -723, -71, -29, 234]], ![![-23, -71, 5, 18, 40]]]
  g := ![![![-2392, -1607, -841, -1342, 5129], ![-4044, -2718, -1423, -2270, 8676], ![-6848, -4601, -2410, -3846, 14696], ![-3730, -2503, -1307, -2087, 7978], ![-6019, -4047, -2120, -3381, 12922]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 4 2 6 [63, 11, 29, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 60, 41, 57], [15, 27, 18, 26], [18, 54, 12, 59], [0, 1]]
 g := ![![[46, 38, 58, 4], [63, 22, 35, 45], [63, 26, 17, 37], [36, 25, 57], [1], []], ![[70, 64, 65, 46, 44, 30], [55, 23, 10, 0, 37, 9], [51, 26, 45, 0, 69, 27], [33, 5, 54], [1, 46, 6], [38, 58, 54]], ![[2, 56, 39, 44, 51, 11], [40, 19, 12, 42, 46, 51], [67, 0, 64, 63, 18, 33], [30, 51, 12], [24, 42, 57], [25, 11, 37]], ![[41, 36, 60, 16, 44, 33], [41, 26, 68, 48, 54, 11], [17, 22, 49, 3, 45, 28], [69, 24, 8], [63, 63, 19], [69, 17, 2]]]
 h' := ![![[13, 60, 41, 57], [7, 29, 67, 69], [7, 21, 42, 51], [68, 54, 1, 45], [8, 60, 42, 46], [0, 0, 1], [0, 1]], ![[15, 27, 18, 26], [53, 25, 55, 47], [43, 1, 47, 51], [23, 33, 16, 8], [16, 20, 15, 57], [47, 44, 21, 52], [13, 60, 41, 57]], ![[18, 54, 12, 59], [40, 7, 17, 5], [54, 15, 42, 23], [1, 36, 67, 69], [51, 33, 33, 15], [70, 55, 9, 46], [15, 27, 18, 26]], ![[0, 1], [45, 10, 3, 21], [69, 34, 11, 17], [67, 19, 58, 20], [15, 29, 52, 24], [24, 43, 40, 44], [18, 54, 12, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [44, 66, 10], []]
 b := ![[], [], [33, 12, 15, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 4
  hpos := by decide
  P := [63, 11, 29, 25, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33211369461135, -8699891739136, 3651232148682, 8244275214470, 9787537359996]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4051934377761, -2603881186184, -1464953222694, -2503083586274, 9787537359996]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 25411681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-476, 279, 42, 37, -69]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-476, 279, 42, 37, -69]] 
 ![![71, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-476, 279, 42, 37, -69], ![828, -540, -71, -54, 148], ![-1776, 959, 160, 154, -216], ![882, -723, -71, -29, 234], ![-1383, 613, 130, 145, -100]]]
  hmulB := by decide  
  f := ![![![-36478, -21775, -3292, 2169, 5129]], ![![-34776, -20760, -3139, 2068, 4890]], ![![-25100, -14983, -2266, 1492, 3530]], ![![-6460, -3854, -581, 384, 907]], ![![-1287, -771, -118, 77, 182]]]
  g := ![![![-299, 279, 42, 37, -69], ![568, -540, -71, -54, 148], ![-1044, 959, 160, 154, -216], ![735, -723, -71, -29, 234], ![-696, 613, 130, 145, -100]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-36478, -21775, -3292, 2169, 5129]] ![![-476, 279, 42, 37, -69]]
  ![![71, 0, 0, 0, 0]] where
 M := ![![![71, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17129, -10264, -1560, 1032, 2412]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-17129, -10264, -1560, 1032, 2412]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![0, 0, 73, 0, 0], ![37, 58, 45, 1, 0], ![7, 11, 60, 0, 1]] where
  M :=![![![-17129, -10264, -1560, 1032, 2412], ![-28944, -17309, -2680, 1704, 4128], ![-49536, -29200, -4205, 2896, 6816], ![-26424, -16256, -2524, 1759, 3728], ![-43188, -25672, -3988, 2476, 6199]]]
  hmulB := by decide  
  f := ![![![3622735, -2204200, -317048, -266072, 566836]], ![![-6802032, 4138595, 595288, 499576, -1064288]], ![![12771456, -7770608, -1117709, -938000, 1998304]], ![![4186987, -2547514, -366429, -307513, 655124]], ![![9938917, -6047191, -869816, -729964, 1555107]]]
  g := ![![![-989, -1324, -2640, 1032, 2412], ![-1656, -2213, -4480, 1704, 4128], ![-2800, -3728, -7445, 2896, 6816], ![-1611, -2182, -4183, 1759, 3728], ![-2441, -3253, -6676, 2476, 6199]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [62, 30, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 72, 37], [5, 0, 36], [0, 1]]
 g := ![![[48, 58, 67], [31, 65], [68, 3], [16, 48, 37], [22, 1], []], ![[18, 71, 60, 69], [10, 8], [36, 67], [54, 19, 0, 8], [], [41, 55]], ![[72, 10, 68, 69], [58, 67], [15, 71], [48, 35, 36, 19], [18, 1], [42, 55]]]
 h' := ![![[17, 72, 37], [61, 25, 33], [42, 55, 49], [30, 66, 52], [23, 8, 16], [0, 0, 1], [0, 1]], ![[5, 0, 36], [13, 55, 49], [7, 66, 64], [66, 49, 33], [27, 33, 4], [10, 71], [17, 72, 37]], ![[0, 1], [51, 66, 64], [17, 25, 33], [61, 31, 61], [44, 32, 53], [49, 2, 72], [5, 0, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 31], []]
 b := ![[], [2, 15, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [62, 30, 51, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4588548, 1346472, -609234, -1286458, -1229996]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![832842, 1225904, 1795632, -1286458, -1229996]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3622735, 2204200, 317048, 266072, -566836]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-3622735, 2204200, 317048, 266072, -566836]] 
 ![![73, 0, 0, 0, 0], ![0, 73, 0, 0, 0], ![23, 56, 1, 0, 0], ![13, 50, 0, 1, 0], ![16, 61, 0, 0, 1]] where
  M :=![![![-3622735, 2204200, 317048, 266072, -566836], ![6802032, -4138595, -595288, -499576, 1064288], ![-12771456, 7770608, 1117709, 938000, -1998304], ![8588808, -5225728, -751660, -630807, 1343856], ![-8716788, 5303608, 762860, 640204, -1363887]]]
  hmulB := by decide  
  f := ![![![17129, 10264, 1560, -1032, -2412]], ![![28944, 17309, 2680, -1704, -4128]], ![![28279, 16912, 2605, -1672, -4020]], ![![23237, 13906, 2148, -1375, -3308]], ![![28532, 17065, 2636, -1684, -4063]]]
  g := ![![![-72663, 78396, 317048, 266072, -566836], ![136432, -147195, -595288, -499576, 1064288], ![-256163, 276376, 1117709, 938000, -1998304], ![172271, -185858, -751660, -630807, 1343856], ![-174836, 188635, 762860, 640204, -1363887]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P1 : CertificateIrreducibleZModOfList' 73 2 2 6 [63, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 72], [0, 1]]
 g := ![![[24, 46], [23], [8], [59, 54], [3], [1]], ![[41, 27], [23], [8], [25, 19], [3], [1]]]
 h' := ![![[21, 72], [35, 22], [43, 60], [6, 64], [57, 45], [10, 21], [0, 1]], ![[0, 1], [59, 51], [62, 13], [36, 9], [53, 28], [13, 52], [21, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [65, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N1 : CertifiedPrimeIdeal' SI73N1 73 where
  n := 2
  hpos := by decide
  P := [63, 52, 1]
  hirr := P73P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448903, -55740, 91093, 68853, 81594]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-64995, -185984, 91093, 68853, 81594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N1 B_one_repr
lemma NI73N1 : Nat.card (O ⧸ I73N1) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-17129, -10264, -1560, 1032, 2412]] ![![-3622735, 2204200, 317048, 266072, -566836]]
  ![![73, 0, 0, 0, 0]] where
 M := ![![![-73, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0, 0, 0]] 
 ![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]] where
  M :=![![![79, 0, 0, 0, 0], ![0, 79, 0, 0, 0], ![0, 0, 79, 0, 0], ![0, 0, 0, 79, 0], ![0, 0, 0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 5 2 6 [65, 21, 17, 26, 69, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 62, 55, 53, 27], [54, 60, 52, 43, 33], [59, 23, 55, 28, 61], [4, 12, 75, 34, 37], [0, 1]]
 g := ![![[77, 35, 71, 62, 52], [34, 77, 57, 49, 50], [16, 51, 19, 43, 50], [66, 68, 74, 10, 1], [], []], ![[37, 36, 64, 14, 24, 38, 57, 61], [20, 39, 14, 39, 33, 64, 22, 17], [21, 58, 44, 11, 33, 5, 30, 15], [64, 16, 23, 50, 63, 66, 31, 41], [14, 66, 27, 2], [4, 23, 40, 18]], ![[24, 18, 48, 42, 35, 50, 1, 77], [43, 77, 75, 5, 21, 78, 8, 43], [49, 8, 0, 6, 3, 76, 72, 47], [41, 54, 26, 63, 16, 44, 30, 30], [57, 60, 13, 13], [76, 13, 61, 62]], ![[50, 62, 5, 18, 66, 76, 60, 37], [74, 48, 22, 61, 73, 32, 25, 60], [41, 41, 18, 33, 65, 7, 22, 35], [78, 44, 29, 44, 58, 12], [19, 75, 66, 20], [63, 60, 20, 8]], ![[2, 37, 41, 10, 31, 71, 39, 35], [12, 13, 18, 11, 17, 6, 23, 3], [39, 43, 31, 48, 68, 17, 13, 15], [53, 34, 39, 46, 12, 38, 52, 12], [77, 46, 45, 52], [63, 57, 11, 26]]]
 h' := ![![[51, 62, 55, 53, 27], [2, 59, 27, 46, 62], [66, 6, 5, 38, 45], [55, 40, 66, 59, 45], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[54, 60, 52, 43, 33], [28, 39, 73, 24, 62], [3, 25, 66, 32, 67], [71, 14, 4, 77, 33], [10, 24, 2, 22, 38], [50, 5, 62, 4, 70], [51, 62, 55, 53, 27]], ![[59, 23, 55, 28, 61], [7, 11, 39, 48, 23], [61, 20, 69, 59, 68], [74, 60, 67, 72, 13], [39, 6, 67, 31, 53], [30, 10, 52, 58, 31], [54, 60, 52, 43, 33]], ![[4, 12, 75, 34, 37], [63, 19, 64, 57, 23], [69, 52, 5, 9, 24], [19, 40, 10, 56, 39], [37, 71, 11, 17], [18, 19, 70, 24, 40], [59, 23, 55, 28, 61]], ![[0, 1], [54, 30, 34, 62, 67], [66, 55, 13, 20, 33], [14, 4, 11, 52, 28], [23, 57, 78, 9, 66], [29, 45, 52, 72, 17], [4, 12, 75, 34, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 25, 8, 31], [], [], []]
 b := ![[], [57, 36, 72, 22, 72], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 5
  hpos := by decide
  P := [65, 21, 17, 26, 69, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1371376559287, 753295601361, -423524052287, -751700148092, -102268040956]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17359196953, 9535387359, -5361063953, -9515191748, -1294532164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 3077056399 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀

instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46742, -27915, -4228, 2785, 6587]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-46742, -27915, -4228, 2785, 6587]] 
 ![![83, 0, 0, 0, 0], ![0, 83, 0, 0, 0], ![0, 0, 83, 0, 0], ![79, 19, 7, 1, 0], ![14, 17, 42, 0, 1]] where
  M :=![![![-46742, -27915, -4228, 2785, 6587], ![-79044, -47168, -7137, 4718, 11140], ![-133680, -79759, -12044, 8006, 18872], ![-73710, -43845, -6573, 4469, 10442], ![-117927, -70249, -10560, 7117, 16690]]]
  hmulB := by decide  
  f := ![![![392, -73, -154, 37, 45]], ![![-540, 246, 33, -218, 148]], ![![-1776, -141, 1274, 362, -872]], ![![166, -37, -58, 22, 11]], ![![-979, -23, 635, 137, -402]]]
  g := ![![![-4325, -2323, -3619, 2785, 6587], ![-7322, -3930, -6121, 4718, 11140], ![-12414, -6659, -10370, 8006, 18872], ![-6903, -3690, -5740, 4469, 10442], ![-11010, -5894, -9173, 7117, 16690]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [4, 75, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 19, 10], [42, 63, 73], [0, 1]]
 g := ![![[1, 28, 64], [58, 32, 63], [71, 77], [44, 28], [41, 38, 1], []], ![[30, 2, 53, 21], [63, 75, 40, 28], [53, 36], [51, 21], [27, 63, 42, 16], [30, 17]], ![[52, 63, 58, 71], [39, 35, 21, 39], [30, 23], [31, 17], [30, 71, 67, 42], [50, 17]]]
 h' := ![![[79, 19, 10], [17, 5, 75], [1, 54, 35], [77, 31, 49], [2, 10, 32], [0, 0, 1], [0, 1]], ![[42, 63, 73], [82, 18, 44], [46, 66, 6], [3, 75, 77], [37, 0, 41], [62, 20, 63], [79, 19, 10]], ![[0, 1], [82, 60, 47], [71, 46, 42], [78, 60, 40], [6, 73, 10], [70, 63, 19], [42, 63, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 50], []]
 b := ![[], [12, 38, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [4, 75, 45, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11654356, -175152, -7338594, -1639602, 4844028]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![883934, -618930, -2401332, -1639602, 4844028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 63, 9, 6, -16]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-79, 63, 9, 6, -16]] 
 ![![83, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-79, 63, 9, 6, -16], ![192, -92, -13, -14, 24], ![-288, 217, 32, 22, -56], ![240, -121, -19, -17, 32], ![-192, 153, 23, 14, -39]]]
  hmulB := by decide  
  f := ![![![835, 209, -95, -198, -240]], ![![85, 21, -10, -20, -24]], ![![698, 175, -80, -166, -200]], ![![780, 195, -89, -185, -224]], ![![811, 202, -94, -192, -231]]]
  g := ![![![-4, 63, 9, 6, -16], ![10, -92, -13, -14, 24], ![-15, 217, 32, 22, -56], ![13, -121, -19, -17, 32], ![-10, 153, 23, 14, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 5, 0, -1, -1]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![22, 5, 0, -1, -1]] 
 ![![83, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![54, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![66, 0, 0, 0, 1]] where
  M :=![![![22, 5, 0, -1, -1], ![12, 22, 3, -2, -4], ![48, 13, 10, -2, -8], ![42, 15, -9, 3, -2], ![33, 19, 6, -7, -2]]]
  hmulB := by decide  
  f := ![![![-3868, -961, 462, 919, 1089]], ![![-3140, -780, 375, 746, 884]], ![![-3048, -757, 364, 724, 858]], ![![-3894, -967, 465, 925, 1096]], ![![-4071, -1011, 486, 967, 1146]]]
  g := ![![![-2, 5, 0, -1, -1], ![-14, 22, 3, -2, -4], ![-8, 13, 10, -2, -8], ![-6, 15, -9, 3, -2], ![-11, 19, 6, -7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-46742, -27915, -4228, 2785, 6587]] ![![-79, 63, 9, 6, -16]]
  ![![-1045702, -623216, -94493, 62215, 146907]] where
 M := ![![![-1045702, -623216, -94493, 62215, 146907]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![-1045702, -623216, -94493, 62215, 146907]] ![![22, 5, 0, -1, -1]]
  ![![83, 0, 0, 0, 0]] where
 M := ![![![-27558739, -16443213, -2493071, 1639416, 3876266]]]
 hmul := by decide  
 g := ![![![![-332033, -198111, -30037, 19752, 46702]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62411, 37920, 5464, 4594, -9738]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-62411, 37920, 5464, 4594, -9738]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![0, 0, 89, 0, 0], ![76, 65, 6, 1, 0], ![39, 70, 20, 0, 1]] where
  M :=![![![-62411, 37920, 5464, 4594, -9738], ![116856, -71279, -10220, -8548, 18376], ![-220512, 133560, 19321, 16312, -34192], ![146724, -90208, -12806, -10597, 23436], ![-151350, 90948, 13288, 11334, -23099]]]
  hmulB := by decide  
  f := ![![![-55, 88, 60, -26, -22]], ![![264, 9, 52, 76, -104]], ![![1248, 136, -559, -104, 304]], ![![208, 97, 60, 23, -76]], ![![477, 74, -60, 28, -25]]]
  g := ![![![-357, 4730, 1940, 4594, -9738], ![560, -9011, -3668, -8548, 18376], ![-1424, 16480, 6801, 16312, -34192], ![428, -11707, -4696, -10597, 23436], ![-1257, 10912, 4576, 11334, -23099]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [11, 81, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 4, 25], [57, 84, 64], [0, 1]]
 g := ![![[17, 62, 81], [53, 40], [28, 4], [85, 61, 11], [87, 48, 1], []], ![[28, 85, 78, 67], [74, 87], [34, 21], [14, 29, 35, 80], [44, 51, 50, 2], [29, 2]], ![[17, 11], [40, 44], [46, 68], [33, 19, 8, 36], [61, 67, 43, 45], [79, 2]]]
 h' := ![![[80, 4, 25], [4, 84, 80], [26, 43, 29], [44, 48, 2], [22, 79, 10], [0, 0, 1], [0, 1]], ![[57, 84, 64], [55, 73, 9], [35, 80, 40], [26, 23, 33], [46, 5, 56], [29, 49, 84], [80, 4, 25]], ![[0, 1], [15, 21], [30, 55, 20], [64, 18, 54], [23, 5, 23], [66, 40, 4], [57, 84, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 14], []]
 b := ![[], [49, 22, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [11, 81, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-606880, 3016884, 2168821, -2287364, -2824379]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3184085, 3925866, 813265, -2287364, -2824379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -88, -60, 26, 22]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![55, -88, -60, 26, 22]] 
 ![![89, 0, 0, 0, 0], ![0, 89, 0, 0, 0], ![10, 77, 1, 0, 0], ![60, 67, 0, 1, 0], ![60, 54, 0, 0, 1]] where
  M :=![![![55, -88, -60, 26, 22], ![-264, -9, -52, -76, 104], ![-1248, -136, 559, 104, -304], ![1956, -544, -754, 293, 156], ![-1158, 196, 140, -266, 167]]]
  hmulB := by decide  
  f := ![![![62411, -37920, -5464, -4594, 9738]], ![![-116856, 71279, 10220, 8548, -18376]], ![![-91610, 55907, 8011, 6696, -14420]], ![![-47544, 29109, 4154, 3457, -7532]], ![![-27126, 16662, 2368, 1962, -4325]]]
  g := ![![![-25, 18, -60, 26, 22], ![-16, 39, -52, -76, 104], ![58, -379, 559, 104, -304], ![-196, 331, -754, 293, 156], ![38, -20, 140, -266, 167]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P1 : CertificateIrreducibleZModOfList' 89 2 2 6 [76, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 88], [0, 1]]
 g := ![![[55, 79], [39], [84], [43, 39], [16, 9], [1]], ![[25, 10], [39], [84], [71, 50], [43, 80], [1]]]
 h' := ![![[3, 88], [26, 41], [26, 67], [25, 23], [30, 67], [13, 3], [0, 1]], ![[0, 1], [60, 48], [49, 22], [5, 66], [53, 22], [22, 86], [3, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [73, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N1 : CertifiedPrimeIdeal' SI89N1 89 where
  n := 2
  hpos := by decide
  P := [76, 86, 1]
  hirr := P89P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108, -676, 165, -75, 76]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18, -140, 165, -75, 76]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N1 B_one_repr
lemma NI89N1 : Nat.card (O ⧸ I89N1) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-62411, 37920, 5464, 4594, -9738]] ![![55, -88, -60, 26, 22]]
  ![![89, 0, 0, 0, 0]] where
 M := ![![![-89, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1999, 1456, 220, -116, -346]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![1999, 1456, 220, -116, -346]] 
 ![![97, 0, 0, 0, 0], ![0, 97, 0, 0, 0], ![0, 0, 97, 0, 0], ![0, 0, 0, 97, 0], ![73, 67, 93, 85, 1]] where
  M :=![![![1999, 1456, 220, -116, -346], ![4152, 1989, 304, -252, -464], ![5568, 4244, 637, -320, -1008], ![3972, 1764, 274, -245, -408], ![5046, 3640, 550, -290, -865]]]
  hmulB := by decide  
  f := ![![![-5, 0, 0, 0, 2]], ![![-24, -3, 8, 4, 0]], ![![0, -20, -11, 16, 16]], ![![-84, -4, 2, 3, 32]], ![![-95, -25, -3, 21, 45]]]
  g := ![![![281, 254, 334, 302, -346], ![392, 341, 448, 404, -464], ![816, 740, 973, 880, -1008], ![348, 300, 394, 355, -408], ![703, 635, 835, 755, -865]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 4 2 6 [39, 4, 23, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 84, 11, 71], [51, 79, 5, 2], [3, 30, 81, 24], [0, 1]]
 g := ![![[7, 2, 64, 61], [2, 89, 4], [4, 75, 6], [40, 65, 94], [20, 72, 1], []], ![[6, 63, 42, 4, 21, 5], [35, 63, 47], [36, 88, 27], [21, 56, 33], [29, 68, 49], [20, 74, 3, 49, 85, 78]], ![[17, 34, 8, 68, 76, 88], [11, 42, 4], [4, 71, 88], [18, 50, 3], [53, 37, 31], [5, 8, 68, 49, 54, 8]], ![[19, 60, 30, 48, 96, 11], [94, 3, 64], [79, 19, 93], [4, 88, 6], [30, 83, 44], [53, 57, 27, 52, 8, 50]]]
 h' := ![![[18, 84, 11, 71], [44, 26, 84, 62], [5, 11, 23, 2], [8, 39, 91, 54], [93, 22, 86, 71], [0, 0, 0, 1], [0, 1]], ![[51, 79, 5, 2], [41, 17, 44, 37], [57, 91, 5, 85], [54, 60, 79, 30], [0, 91, 86, 79], [8, 15, 30, 7], [18, 84, 11, 71]], ![[3, 30, 81, 24], [21, 79, 62, 74], [16, 52, 84, 2], [50, 8, 15, 66], [49, 90, 18, 87], [51, 58, 40, 15], [51, 79, 5, 2]], ![[0, 1], [21, 72, 4, 21], [1, 40, 82, 8], [47, 87, 9, 44], [3, 88, 4, 54], [94, 24, 27, 74], [3, 30, 81, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 58, 64], []]
 b := ![[], [], [27, 7, 27, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 4
  hpos := by decide
  P := [39, 4, 23, 25, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26114848530, -4546703865, 2797466734, 4381772533, 7544293310]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5946889280, -5257879955, -7204348568, -6565805761, 7544293310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 88529281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 0, 0, 0, 2]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-5, 0, 0, 0, 2]] 
 ![![97, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-5, 0, 0, 0, 2], ![-24, -3, 8, 4, 0], ![0, -20, -11, 16, 16], ![-84, -4, 2, 3, 32], ![-102, -24, 26, 26, 11]]]
  hmulB := by decide  
  f := ![![![1999, 1456, 220, -116, -346]], ![![1032, 741, 112, -60, -176]], ![![552, 404, 61, -32, -96]], ![![1669, 1204, 182, -97, -286]], ![![1000, 728, 110, -58, -173]]]
  g := ![![![-1, 0, 0, 0, 2], ![-4, -3, 8, 4, 0], ![-8, -20, -11, 16, 16], ![-17, -4, 2, 3, 32], ![-22, -24, 26, 26, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![1999, 1456, 220, -116, -346]] ![![-5, 0, 0, 0, 2]]
  ![![97, 0, 0, 0, 0]] where
 M := ![![![97, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2768, 315, -2108, -685, 1509]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![2768, 315, -2108, -685, 1509]] 
 ![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![10, 99, 82, 30, 1]] where
  M :=![![![2768, 315, -2108, -685, 1509], ![-18108, 2854, 7721, -1198, -2740], ![32880, -11929, -5710, 9962, -4792], ![37806, 4781, -29371, -9903, 21294], ![-51969, 4657, 26516, 643, -12984]]]
  hmulB := by decide  
  f := ![![![-938, 511, 74, 69, -131]], ![![1572, -1064, -151, -114, 276]], ![![-3312, 1811, 268, 250, -456]], ![![1950, -1343, -181, -131, 362]], ![![-685, 91, 25, 61, -8]]]
  g := ![![![-122, -1476, -1246, -455, 1509], ![92, 2714, 2301, 802, -2740], ![800, 4579, 3834, 1522, -4792], ![-1734, -20825, -17579, -6423, 21294], ![771, 12773, 10804, 3863, -12984]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 4 2 6 [85, 56, 6, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 47, 40, 44], [35, 24, 33, 8], [23, 29, 28, 49], [0, 1]]
 g := ![![[97, 40, 34, 88], [58, 88, 52], [17, 70, 98, 25], [90, 58, 4], [30, 95, 1], []], ![[72, 75, 31, 65, 64, 66], [49, 72, 45], [64, 37, 1, 67, 87, 32], [28, 90, 87], [67, 27, 21], [33, 76, 23, 82, 77, 41]], ![[7, 37, 77, 13, 69, 40], [93, 11, 70], [30, 78, 95, 35, 10, 67], [51, 57, 87], [38, 47, 19], [18, 8, 49, 8, 32, 7]], ![[5, 82, 34, 55, 90, 1], [33, 0, 6], [73, 8, 33, 6, 73, 17], [45, 66, 4], [83, 14, 17], [36, 43, 56, 28, 83, 85]]]
 h' := ![![[37, 47, 40, 44], [71, 59, 37, 54], [70, 72, 26, 31], [45, 50, 45, 5], [76, 42, 71, 2], [0, 0, 0, 1], [0, 1]], ![[35, 24, 33, 8], [68, 42, 97, 31], [30, 71, 8, 34], [96, 8, 36, 41], [31, 25, 83, 84], [75, 93, 80, 18], [37, 47, 40, 44]], ![[23, 29, 28, 49], [98, 61, 81, 45], [78, 32, 83, 75], [31, 85, 12, 18], [86, 30, 20, 17], [36, 56, 82, 25], [35, 24, 33, 8]], ![[0, 1], [19, 40, 88, 72], [20, 27, 85, 62], [14, 59, 8, 37], [1, 4, 28, 99], [17, 53, 40, 57], [23, 29, 28, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 9, 64], []]
 b := ![[], [], [58, 56, 47, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 4
  hpos := by decide
  P := [85, 56, 6, 6, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1188873515, -99518736, 147689049, 106388683, 306032930]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42071315, -300958206, -247000111, -89847517, 306032930]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 104060401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![938, -511, -74, -69, 131]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![938, -511, -74, -69, 131]] 
 ![![101, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![58, 0, 0, 0, 1]] where
  M :=![![![938, -511, -74, -69, 131], ![-1572, 1064, 151, 114, -276], ![3312, -1811, -268, -250, 456], ![-1950, 1343, 181, 131, -362], ![2349, -1205, -188, -187, 290]]]
  hmulB := by decide  
  f := ![![![-2768, -315, 2108, 685, -1509]], ![![-2068, -284, 1635, 568, -1198]], ![![-1504, -16, 954, 193, -595]], ![![-758, -91, 583, 193, -420]], ![![-1075, -227, 948, 387, -738]]]
  g := ![![![390, -511, -74, -69, 131], ![-801, 1064, 151, 114, -276], ![1390, -1811, -268, -250, 456], ![-997, 1343, 181, 131, -362], ![941, -1205, -188, -187, 290]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![2768, 315, -2108, -685, 1509]] ![![938, -511, -74, -69, 131]]
  ![![101, 0, 0, 0, 0]] where
 M := ![![![-101, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![519256, -315932, -45445, -38137, 81247]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![519256, -315932, -45445, -38137, 81247]] 
 ![![103, 0, 0, 0, 0], ![0, 103, 0, 0, 0], ![0, 0, 103, 0, 0], ![0, 0, 0, 103, 0], ![55, 17, 32, 58, 1]] where
  M :=![![![519256, -315932, -45445, -38137, 81247], ![-974964, 593195, 85330, 71604, -152548], ![1830576, -1113786, -160205, -134436, 286416], ![-1231014, 749014, 107710, 90409, -192598], ![1249341, -760172, -109319, -91761, 195480]]]
  hmulB := by decide  
  f := ![![![1102, 660, 101, -65, -155]], ![![1860, 1113, 170, -108, -260]], ![![3120, 1878, 289, -180, -432]], ![![1662, 1022, 170, -89, -230]], ![![2827, 1711, 270, -160, -393]]]
  g := ![![![-38343, -16477, -25683, -46121, 81247], ![71992, 30937, 48222, 86596, -152548], ![-135168, -58086, -90539, -162588, 286416], ![90892, 39060, 60882, 109331, -192598], ![-92253, -39644, -61793, -110967, 195480]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 4 2 6 [45, 26, 46, 101, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 23, 59, 3], [34, 22, 43, 64], [18, 57, 1, 36], [0, 1]]
 g := ![![[24, 50, 88, 92], [49, 14, 65, 29], [44, 90, 49, 55], [88, 86, 16], [61, 2, 1], []], ![[62, 86, 89, 61, 49, 45], [9, 31, 86, 14, 60, 96], [67, 88, 1, 0, 31, 43], [65, 28, 61], [54, 12, 79], [84, 48, 90, 12, 102, 27]], ![[65, 88, 91, 84, 17, 13], [10, 95, 62, 4, 29, 66], [47, 71, 47, 89, 82, 34], [86, 63, 49], [5, 45, 72], [25, 72, 39, 53, 12, 9]], ![[10, 94, 29, 34, 86, 17], [74, 71, 29, 8, 87, 61], [75, 18, 0, 32, 22, 29], [8, 81, 29], [64, 25, 33], [26, 73, 83, 39, 71, 100]]]
 h' := ![![[53, 23, 59, 3], [61, 67, 31, 35], [80, 49, 17, 82], [14, 66, 34, 40], [36, 75, 84, 4], [0, 0, 0, 1], [0, 1]], ![[34, 22, 43, 64], [28, 101, 62, 18], [80, 102, 37, 54], [81, 62, 8, 17], [15, 18, 71, 24], [73, 60, 80, 39], [53, 23, 59, 3]], ![[18, 57, 1, 36], [82, 31, 94, 72], [84, 75, 76, 66], [60, 24, 85, 94], [4, 6, 54, 96], [69, 100, 75, 22], [34, 22, 43, 64]], ![[0, 1], [98, 7, 19, 81], [73, 83, 76, 4], [93, 54, 79, 55], [12, 4, 100, 82], [27, 46, 51, 41], [18, 57, 1, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [95, 10, 74], []]
 b := ![[], [], [50, 65, 23, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 4
  hpos := by decide
  P := [45, 26, 46, 101, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11397891, 2422492, 4987132, -1273724, -1965656]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![938963, 347948, 659108, 1094508, -1965656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 112550881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1102, 660, 101, -65, -155]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1102, 660, 101, -65, -155]] 
 ![![103, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![45, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![1102, 660, 101, -65, -155], ![1860, 1113, 170, -108, -260], ![3120, 1878, 289, -180, -432], ![1662, 1022, 170, -89, -230], ![2715, 1640, 257, -147, -370]]]
  hmulB := by decide  
  f := ![![![519256, -315932, -45445, -38137, 81247]], ![![378716, -230423, -33145, -27815, 59257]], ![![244632, -148842, -21410, -17967, 38277]], ![![406478, -247314, -35575, -29854, 63601]], ![![475931, -289572, -41653, -34955, 74468]]]
  g := ![![![-336, 660, 101, -65, -155], ![-569, 1113, 170, -108, -260], ![-969, 1878, 289, -180, -432], ![-545, 1022, 170, -89, -230], ![-863, 1640, 257, -147, -370]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![519256, -315932, -45445, -38137, 81247]] ![![1102, 660, 101, -65, -155]]
  ![![103, 0, 0, 0, 0]] where
 M := ![![![103, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB1705I2_primes (p : ℕ) :
  p ∈ Set.range ![67, 71, 73, 79, 83, 89, 97, 101, 103] ↔ Nat.Prime p ∧ 61 < p ∧ p ≤ 103 := by
  rw [← List.mem_ofFn']
  convert primes_range 61 103 (by omega)

def PB1705I2 : PrimesBelowBoundCertificateInterval O 61 103 1705 where
  m := 9
  g := ![2, 2, 2, 1, 3, 2, 2, 2, 2]
  P := ![67, 71, 73, 79, 83, 89, 97, 101, 103]
  hP := PB1705I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![20151121, 67]
    · exact ![25411681, 71]
    · exact ![389017, 5329]
    · exact ![3077056399]
    · exact ![571787, 83, 83]
    · exact ![704969, 7921]
    · exact ![88529281, 97]
    · exact ![104060401, 101]
    · exact ![112550881, 103]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
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
  β := ![I67N1, I71N1, I83N1, I83N2, I97N1, I101N1, I103N1]
  Il := ![[I67N1], [I71N1], [], [], [I83N1, I83N2], [], [I97N1], [I101N1], [I103N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
