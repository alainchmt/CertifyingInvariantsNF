
import IdealArithmetic.Examples.NF5_3_1518750000_3.RI5_3_1518750000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-481, 357, -105, -315, -19]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-481, 357, -105, -315, -19]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![76, 15, 90, 56, 1]] where
  M :=![![![-481, 357, -105, -315, -19], ![456, -766, 433, 657, -315], ![7560, -4269, 1136, 6297, 657], ![-6408, 5037, -2199, -7132, 721], ![-28968, 15249, -2773, -19875, -4312]]]
  hmulB := by decide  
  f := ![![![14485, 693, -3671, -1323, -895]], ![![21480, 1060, -5417, -1947, -1323]], ![![31752, 1635, -7952, -2847, -1947]], ![![-8088, -393, 2045, 736, 499]], ![![35732, 1809, -8974, -3218, -2195]]]
  g := ![![![9, 6, 15, 7, -19], ![228, 37, 269, 171, -315], ![-396, -132, -542, -285, 657], ![-572, -54, -627, -444, 721], ![2792, 747, 3601, 2071, -4312]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [33, 0, 48, 36, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 68, 30, 24], [39, 88, 20, 28], [26, 57, 57, 55], [0, 1]]
 g := ![![[29, 98, 24, 9], [56, 13, 68, 36], [12, 55, 48], [25, 105, 35, 35], [71, 71, 1], []], ![[82, 9, 37, 51, 5, 84], [14, 3, 81, 101, 66, 22], [11, 22, 42], [1, 45, 67, 71, 53, 70], [75, 34, 64], [47, 61, 78, 23, 45, 21]], ![[30, 106, 2, 59, 54, 82], [62, 51, 27, 36, 14, 59], [103, 81, 34], [106, 48, 70, 76, 46, 24], [19, 70, 83], [77, 80, 91, 12, 97, 17]], ![[93, 62, 53, 6, 76, 72], [65, 69, 74, 106, 24, 104], [32, 46, 99], [14, 67, 56, 98, 18, 58], [45, 19, 23], [13, 4, 68, 43, 76, 97]]]
 h' := ![![[6, 68, 30, 24], [78, 43, 49, 104], [30, 42, 29, 101], [31, 80, 27, 35], [11, 11, 90, 28], [0, 0, 0, 1], [0, 1]], ![[39, 88, 20, 28], [46, 62, 10, 48], [7, 96, 20, 62], [100, 33, 39, 91], [19, 67, 4, 84], [56, 88, 1, 99], [6, 68, 30, 24]], ![[26, 57, 57, 55], [72, 18, 14, 27], [20, 62, 10, 82], [67, 26, 93, 26], [38, 62, 31, 13], [68, 8, 3, 46], [39, 88, 20, 28]], ![[0, 1], [98, 91, 34, 35], [24, 14, 48, 76], [63, 75, 55, 62], [100, 74, 89, 89], [27, 11, 103, 68], [26, 57, 57, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [79, 86, 11], []]
 b := ![[], [], [10, 86, 12, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [33, 0, 48, 36, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2051025735, 1354534877, -438489130, -1767033712, -54528495]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![19562055, 20303386, 41767060, 12023944, -54528495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14485, 693, -3671, -1323, -895]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![14485, 693, -3671, -1323, -895]] 
 ![![107, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![14485, 693, -3671, -1323, -895], ![21480, 1060, -5417, -1947, -1323], ![31752, 1635, -7952, -2847, -1947], ![-8088, -393, 2045, 736, 499], ![-4488, -147, 1193, 441, 286]]]
  hmulB := by decide  
  f := ![![![-481, 357, -105, -315, -19]], ![![-225, 163, -46, -144, -12]], ![![-262, 207, -62, -159, -7]], ![![-433, 324, -102, -311, -8]], ![![-491, 306, -74, -330, -49]]]
  g := ![![![3780, 693, -3671, -1323, -895], ![5558, 1060, -5417, -1947, -1323], ![8117, 1635, -7952, -2847, -1947], ![-2102, -393, 2045, 736, 499], ![-1270, -147, 1193, 441, 286]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-481, 357, -105, -315, -19]] ![![14485, 693, -3671, -1323, -895]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15943, -2203, -6175, -2728, -1304]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![15943, -2203, -6175, -2728, -1304]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![62, 25, 1, 0, 0], ![74, 39, 0, 1, 0], ![46, 4, 0, 0, 1]] where
  M :=![![![15943, -2203, -6175, -2728, -1304], ![31296, -3617, -12784, -5394, -2728], ![65472, -9624, -25663, -11418, -5394], ![-11160, 2239, 3895, 1937, 794], ![12936, -2157, -5167, -2340, -1075]]]
  hmulB := by decide  
  f := ![![![-2405, 2681, -1465, -3448, 918]], ![![-22032, 11365, -1938, -14970, -3448]], ![![-5662, 3455, -963, -4520, -406]], ![![-9346, 6008, -1855, -7845, -396]], ![![-5702, 4623, -1965, -5992, 619]]]
  g := ![![![6061, 2420, -6175, -2728, -1304], ![12372, 4929, -12784, -5394, -2728], ![25226, 10081, -25663, -11418, -5394], ![-3968, -1595, 3895, 1937, 794], ![5100, 2042, -5167, -2340, -1075]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [60, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 108], [0, 1]]
 g := ![![[22, 20], [106], [76, 71], [44, 81], [80], [97, 1]], ![[0, 89], [106], [96, 38], [53, 28], [80], [85, 108]]]
 h' := ![![[97, 108], [68, 42], [18, 91], [85, 17], [101, 100], [66, 84], [0, 1]], ![[0, 1], [0, 67], [16, 18], [99, 92], [100, 9], [39, 25], [97, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [41, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [60, 12, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5553, -4369, 4336, 2612, 323]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4325, -1981, 4336, 2612, 323]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-283, -196, 278, 46, 68]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-283, -196, 278, 46, 68]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![100, 28, 1, 0, 0], ![101, 90, 0, 1, 0], ![14, 59, 0, 0, 1]] where
  M :=![![![-283, -196, 278, 46, 68], ![-1632, 737, 320, 306, 46], ![-1104, -942, 1207, 174, 306], ![-672, 1052, -390, 115, -124], ![-144, -318, 300, 66, 49]]]
  hmulB := by decide  
  f := ![![![7698377, 338712, -1975318, -716702, -479472]], ![![11507328, 506297, -2952652, -1071306, -716702]], ![![10176548, 447746, -2611189, -947414, -633818]], ![![16595233, 730154, -4258152, -1544979, -1033588]], ![![7197382, 316669, -1846768, -670060, -448269]]]
  g := ![![![-309, -148, 278, 46, 68], ![-598, -353, 320, 306, 46], ![-1318, -628, 1207, 174, 306], ![261, 82, -390, 115, -124], ![-344, -161, 300, 66, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [19, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 108], [0, 1]]
 g := ![![[51, 100], [36], [66, 104], [12, 75], [38], [12, 1]], ![[52, 9], [36], [6, 5], [40, 34], [38], [24, 108]]]
 h' := ![![[12, 108], [52, 99], [54, 6], [99, 70], [32, 27], [99, 16], [0, 1]], ![[0, 1], [41, 10], [17, 103], [67, 39], [29, 82], [73, 93], [12, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [13, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [19, 97, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1035, 959, -813, -1615, 209]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2206, 1438, -813, -1615, 209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2813, 232, 1014, 425, 221]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-2813, 232, 1014, 425, 221]] 
 ![![109, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-2813, 232, 1014, 425, 221], ![-5304, 502, 1965, 831, 425], ![-10200, 1071, 3866, 1647, 831], ![1776, -158, -650, -274, -141], ![-1488, 258, 646, 285, 134]]]
  hmulB := by decide  
  f := ![![![21151, -23010, 5140, -4105, 1901]], ![![10448, -11366, 2539, -2027, 939]], ![![5755, -6261, 1398, -1120, 518]], ![![11445, -12452, 2782, -2221, 1028]], ![![12875, -14004, 3130, -2486, 1155]]]
  g := ![![![-755, 232, 1014, 425, 221], ![-1491, 502, 1965, 831, 425], ![-2978, 1071, 3866, 1647, 831], ![489, -158, -650, -274, -141], ![-539, 258, 646, 285, 134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![15943, -2203, -6175, -2728, -1304]] ![![-283, -196, 278, 46, 68]]
  ![![7921619, -1386773, -3053311, -1414974, -632388]] where
 M := ![![![7921619, -1386773, -3053311, -1414974, -632388]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![7921619, -1386773, -3053311, -1414974, -632388]] ![![-2813, 232, 1014, 425, 221]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![14643701465, -2068030731, -5985377153, -2607051209, -1261230825]]]
 hmul := by decide  
 g := ![![![![134345885, -18972759, -54911717, -23917901, -11570925]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14741, 689, -3801, -1373, -923]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![14741, 689, -3801, -1373, -923]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![33, 47, 93, 102, 1]] where
  M :=![![![14741, 689, -3801, -1373, -923], ![22152, 896, -5649, -2073, -1373], ![32952, 1557, -8486, -2961, -2073], ![-8184, -469, 2135, 694, 543], ![-4632, 111, 989, 75, 250]]]
  hmulB := by decide  
  f := ![![![7117, -1005, -2909, -1267, -613]], ![![14712, -2078, -6013, -2619, -1267]], ![![30408, -4293, -12430, -5415, -2619]], ![![-4728, 667, 1933, 842, 407]], ![![29013, -4097, -11859, -5166, -2499]]]
  g := ![![![400, 390, 726, 821, -923], ![597, 579, 1080, 1221, -1373], ![897, 876, 1631, 1845, -2073], ![-231, -230, -428, -484, 543], ![-114, -103, -197, -225, 250]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [21, 64, 32, 69, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 75, 4, 35], [27, 51, 107, 88], [9, 99, 2, 103], [0, 1]]
 g := ![![[5, 52, 99, 60], [100, 94, 60], [97, 56, 22], [96, 74, 7], [40, 96, 44, 1], []], ![[58, 2, 39, 7, 75, 5], [83], [95, 72, 97], [55, 57, 28], [60, 53, 58, 95, 99, 23], [55, 52, 104, 79, 88, 48]], ![[97, 106, 93, 105, 31, 51], [77, 56, 82], [101, 31, 83], [90, 31, 105], [104, 88, 28, 78, 52, 4], [85, 41, 111, 54, 42, 82]], ![[43, 49, 89, 100, 93, 84], [78, 49, 102], [109, 38, 87], [62, 17, 61], [3, 99, 52, 33, 109, 101], [29, 72, 52, 95, 105, 17]]]
 h' := ![![[8, 75, 4, 35], [73, 25, 78, 25], [79, 41, 44, 25], [46, 50, 24, 94], [64, 57, 14, 32], [0, 0, 0, 1], [0, 1]], ![[27, 51, 107, 88], [57, 46, 34, 53], [61, 68, 99], [19, 41, 14, 60], [65, 14, 3, 49], [35, 70, 15, 47], [8, 75, 4, 35]], ![[9, 99, 2, 103], [37, 89, 74, 81], [33, 75, 73, 67], [81, 96, 20, 14], [29, 44, 83, 52], [44, 33, 44, 107], [27, 51, 107, 88]], ![[0, 1], [5, 66, 40, 67], [20, 42, 10, 21], [106, 39, 55, 58], [39, 111, 13, 93], [7, 10, 54, 71], [9, 99, 2, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [102, 8, 101], []]
 b := ![[], [], [63, 12, 104, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [21, 64, 32, 69, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2834170349, 1337080982, -134906986, -1758618754, -546021960]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![134376587, 238939054, 448187038, 477306382, -546021960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7117, -1005, -2909, -1267, -613]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![7117, -1005, -2909, -1267, -613]] 
 ![![113, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![105, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![31, 0, 0, 0, 1]] where
  M :=![![![7117, -1005, -2909, -1267, -613], ![14712, -2078, -6013, -2619, -1267], ![30408, -4293, -12430, -5415, -2619], ![-4728, 667, 1933, 842, 407], ![6456, -915, -2635, -1143, -556]]]
  hmulB := by decide  
  f := ![![![14741, 689, -3801, -1373, -923]], ![![1631, 75, -420, -152, -102]], ![![13989, 654, -3607, -1302, -876]], ![![12190, 569, -3143, -1136, -763]], ![![4003, 190, -1034, -376, -251]]]
  g := ![![![4086, -1005, -2909, -1267, -613], ![8446, -2078, -6013, -2619, -1267], ![17460, -4293, -12430, -5415, -2619], ![-2715, 667, 1933, 842, 407], ![3698, -915, -2635, -1143, -556]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![14741, 689, -3801, -1373, -923]] ![![7117, -1005, -2909, -1267, -613]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0, 0, 0]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]] where
  M :=![![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![0, 0, 0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [86, 6, 25, 75, 46, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 39, 104, 78, 33], [2, 71, 78, 66, 71], [0, 21, 20, 26, 51], [113, 122, 52, 84, 99], [0, 1]]
 g := ![![[89, 63, 18, 10, 81], [21, 68, 21, 13, 103], [21, 64, 6, 121, 98], [11, 69, 8, 110, 99], [9, 81, 1], []], ![[4, 60, 64, 4, 119, 7, 19, 83], [88, 22, 105, 104, 51, 44, 30, 59], [114, 116, 72, 121, 34, 83, 120, 102], [42, 13, 87, 40, 71, 71, 69, 123], [10, 65, 70, 29, 33, 11, 85, 77], [30, 10, 6, 81, 46, 66, 121, 123]], ![[114, 23, 37, 47, 2, 94, 69, 44], [107, 45, 56, 32, 104, 38, 16, 44], [84, 88, 48, 100, 74, 52, 32, 36], [31, 123, 102, 40, 88, 65, 25, 124], [118, 39, 22, 114, 63, 111, 9, 115], [82, 43, 54, 59, 91, 75, 18, 25]], ![[74, 25, 49, 116, 24, 85, 5, 5], [26, 83, 81, 35, 5, 6, 62, 65], [77, 81, 71, 63, 97, 80, 5, 93], [11, 21, 84, 85, 60, 118, 69, 54], [96, 31, 96, 78, 113, 53, 34, 23], [5, 124, 64, 53, 78, 39, 82, 63]], ![[77, 105, 33, 73, 103, 94, 95, 26], [64, 76, 56, 121, 14, 65, 80, 16], [21, 51, 123, 103, 45, 10, 41, 115], [71, 80, 96, 42, 113, 116, 113, 79], [50, 106, 3, 87, 76, 9, 74, 41], [89, 90, 117, 12, 85, 44, 98, 19]]]
 h' := ![![[93, 39, 104, 78, 33], [99, 17, 41, 10, 9], [99, 32, 44, 45, 105], [70, 113, 98, 40, 15], [115, 92, 92, 88, 90], [0, 0, 0, 1], [0, 1]], ![[2, 71, 78, 66, 71], [31, 43, 82, 82, 101], [100, 34, 71, 46, 112], [53, 9, 67, 49, 108], [32, 124, 111, 25, 94], [26, 100, 115, 8, 77], [93, 39, 104, 78, 33]], ![[0, 21, 20, 26, 51], [87, 113, 93, 19, 37], [3, 57, 63, 74, 90], [116, 74, 80, 108, 118], [116, 125, 53, 51, 5], [68, 91, 100, 40, 117], [2, 71, 78, 66, 71]], ![[113, 122, 52, 84, 99], [50, 18, 79, 110, 5], [109, 95, 85, 14, 43], [70, 54, 78, 63, 46], [126, 62, 8, 18, 4], [78, 101, 104, 82, 49], [0, 21, 20, 26, 51]], ![[0, 1], [110, 63, 86, 33, 102], [19, 36, 118, 75, 31], [114, 4, 58, 121, 94], [117, 105, 117, 72, 61], [16, 89, 62, 123, 11], [113, 122, 52, 84, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 117, 4, 19], [], [], []]
 b := ![[], [36, 37, 121, 114, 61], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [86, 6, 25, 75, 46, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1557934474803, -569976128397, -66299660771, 764314892500, 453802145607]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12267200589, -4488001011, -522044573, 6018227500, 3573245241]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 33038369407 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18839, 20508, -4582, 3666, -1698]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-18839, 20508, -4582, 3666, -1698]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![67, 118, 1, 0, 0], ![68, 55, 0, 1, 0], ![123, 18, 0, 0, 1]] where
  M :=![![![-18839, 20508, -4582, 3666, -1698], ![40752, -44309, 9888, -7926, 3666], ![-87984, 95742, -21383, 17118, -7926], ![75696, -82350, 18388, -14723, 6816], ![-24480, 26628, -5946, 4758, -2201]]]
  hmulB := by decide  
  f := ![![![40907, -5772, -16714, -7278, -3522]], ![![84528, -11923, -34548, -15054, -7278]], ![![98395, -13880, -40213, -17520, -8472]], ![![56516, -7973, -23096, -10061, -4866]], ![![50307, -7098, -20556, -8952, -4331]]]
  g := ![![![1891, 2978, -4582, 3666, -1698], ![-4074, -6421, 9888, -7926, 3666], ![8821, 13894, -21383, 17118, -7926], ![-7584, -11947, 18388, -14723, 6816], ![2451, 3864, -5946, 4758, -2201]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [76, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 130], [0, 1]]
 g := ![![[31, 43], [127, 58], [44], [55], [108], [4], [1]], ![[117, 88], [112, 73], [44], [55], [108], [4], [1]]]
 h' := ![![[2, 130], [42, 82], [31, 53], [10, 31], [28, 29], [101, 97], [55, 2], [0, 1]], ![[0, 1], [75, 49], [6, 78], [72, 100], [86, 102], [33, 34], [59, 129], [2, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [62, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [76, 129, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3436, -1348, -718, 686, 600]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-526, 266, -718, 686, 600]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![613129, 26976, -157322, -57081, -38187]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![613129, 26976, -157322, -57081, -38187]] 
 ![![131, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![613129, 26976, -157322, -57081, -38187], ![916488, 40324, -235161, -85323, -57081], ![1369944, 60273, -351512, -127539, -85323], ![-343680, -15120, 88184, 31996, 21405], ![-174816, -7692, 44856, 16275, 10888]]]
  hmulB := by decide  
  f := ![![![539, -78, -212, -93, 3]], ![![127, -14, -55, -30, 0]], ![![375, -63, -140, -54, -6]], ![![151, -30, -48, -5, 6]], ![![-19, 54, -44, -78, 25]]]
  g := ![![![117743, 26976, -157322, -57081, -38187], ![175999, 40324, -235161, -85323, -57081], ![263079, 60273, -351512, -127539, -85323], ![-65999, -15120, 88184, 31996, 21405], ![-33571, -7692, 44856, 16275, 10888]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, -179, 45, -30, 16]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![145, -179, 45, -30, 16]] 
 ![![131, 0, 0, 0, 0], ![33, 1, 0, 0, 0], ![90, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![145, -179, 45, -30, 16], ![-384, 385, -78, 72, -30], ![720, -834, 199, -144, 72], ![-648, 717, -163, 127, -60], ![216, -231, 51, -42, 19]]]
  hmulB := by decide  
  f := ![![![-61, -29, 57, 66, -2]], ![![-15, -8, 15, 18, 0]], ![![-54, -12, 37, 36, 0]], ![![-53, -28, 52, 61, -4]], ![![22, -43, 33, 66, -3]]]
  g := ![![![36, -179, 45, -30, 16], ![-99, 385, -78, 72, -30], ![180, -834, 199, -144, 72], ![-164, 717, -163, 127, -60], ![55, -231, 51, -42, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2

def I131N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![245, 11, -63, -23, -15]] i)))

def SI131N3: IdealEqSpanCertificate' Table ![![245, 11, -63, -23, -15]] 
 ![![131, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![245, 11, -63, -23, -15], ![360, 20, -95, -39, -23], ![552, 15, -134, -39, -39], ![-120, -13, 35, 22, 13], ![-120, 51, -11, -63, 22]]]
  hmulB := by decide  
  f := ![![![-4265, 4119, -677, 821, -287]], ![![-2552, 2450, -395, 491, -169]], ![![-769, 744, -123, 148, -52]], ![![-567, 536, -82, 109, -36]], ![![-3459, 3342, -550, 666, -233]]]
  g := ![![![20, 11, -63, -23, -15], ![29, 20, -95, -39, -23], ![52, 15, -134, -39, -39], ![-12, -13, 35, 22, 13], ![-38, 51, -11, -63, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N3 : Nat.card (O ⧸ I131N3) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N3)

lemma isPrimeI131N3 : Ideal.IsPrime I131N3 := prime_ideal_of_norm_prime hp131.out _ NI131N3
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-18839, 20508, -4582, 3666, -1698]] ![![613129, 26976, -157322, -57081, -38187]]
  ![![4421953, 223938, -1147590, -409041, -279363]] where
 M := ![![![4421953, 223938, -1147590, -409041, -279363]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![4421953, 223938, -1147590, -409041, -279363]] ![![145, -179, 45, -30, 16]]
  ![![-66357647, 23027059, 5576481, 8502945, 641191]] where
 M := ![![![-66357647, 23027059, 5576481, 8502945, 641191]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N2 : IdealMulLeCertificate' Table 
  ![![-66357647, 23027059, 5576481, 8502945, 641191]] ![![245, 11, -63, -23, -15]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![-5986961083, -263583266, 1536262676, 557357578, 372904076]]]
 hmul := by decide  
 g := ![![![![-45701993, -2012086, 11727196, 4254638, 2846596]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2, I131N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
    exact isPrimeI131N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1 ⊙ MulI131N2)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, 57, 9, 74, -20]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-89, 57, 9, 74, -20]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![25, 4, 116, 10, 1]] where
  M :=![![![-89, 57, 9, 74, -20], ![480, -389, 90, 192, 74], ![-1776, 1590, -607, -1368, 192], ![120, -611, 365, 185, -324], ![6360, -4983, 2083, 6654, -595]]]
  hmulB := by decide  
  f := ![![![10655, -1507, -4357, -1898, -918]], ![![22032, -3115, -9008, -3924, -1898]], ![![45552, -6438, -18623, -8112, -3924]], ![![-7080, 1001, 2895, 1261, 610]], ![![40711, -5754, -16644, -7250, -3507]]]
  g := ![![![3, 1, 17, 2, -20], ![-10, -5, -62, -4, 74], ![-48, 6, -167, -24, 192], ![60, 5, 277, 25, -324], ![155, -19, 519, 92, -595]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [83, 20, 110, 98, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 104, 13, 87], [65, 47, 69, 130], [59, 122, 55, 57], [0, 1]]
 g := ![![[72, 45, 45, 76], [45, 50, 9], [38, 131, 63], [65, 63, 17, 115], [88, 49, 14], [1], []], ![[82, 112, 32, 102, 94, 129], [84, 87, 130], [17, 28, 130], [108, 56, 131, 43, 77, 34], [81, 33, 18], [115, 24, 8], [58, 26, 34]], ![[55, 34, 86, 57, 22, 88], [14, 55, 136], [102, 71, 123], [101, 86, 38, 45, 92, 118], [80, 103, 112], [101, 42, 4], [85, 123, 49]], ![[114, 112, 81, 29, 51, 40], [91, 9, 1], [75, 91, 22], [27, 1, 123, 18, 77, 45], [7, 37, 36], [66, 19, 38], [112, 91, 98]]]
 h' := ![![[52, 104, 13, 87], [115, 88, 2, 58], [98, 36, 73, 134], [85, 63, 97, 101], [133, 96, 125, 72], [54, 117, 27, 39], [0, 0, 1], [0, 1]], ![[65, 47, 69, 130], [91, 73, 11, 110], [58, 75, 7, 104], [109, 115, 44, 33], [112, 95, 117, 118], [56, 52, 50, 44], [82, 100, 117, 62], [52, 104, 13, 87]], ![[59, 122, 55, 57], [15, 117, 130, 12], [128, 44, 42, 37], [127, 19, 38, 64], [17, 14, 16, 9], [128, 128, 94, 48], [47, 92, 97, 135], [65, 47, 69, 130]], ![[0, 1], [127, 133, 131, 94], [62, 119, 15, 136], [56, 77, 95, 76], [132, 69, 16, 75], [24, 114, 103, 6], [76, 82, 59, 77], [59, 122, 55, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [70, 129, 56], []]
 b := ![[], [], [94, 17, 118, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [83, 20, 110, 98, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1966039848, 1124268677, -268743648, -1474515482, -208790339]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23749771, 14302409, 174824348, 4477284, -208790339]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10655, -1507, -4357, -1898, -918]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![10655, -1507, -4357, -1898, -918]] 
 ![![137, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![10655, -1507, -4357, -1898, -918], ![22032, -3115, -9008, -3924, -1898], ![45552, -6438, -18623, -8112, -3924], ![-7080, 1001, 2895, 1261, 610], ![9672, -1365, -3953, -1722, -833]]]
  hmulB := by decide  
  f := ![![![-89, 57, 9, 74, -20]], ![![-79, 50, 9, 70, -18]], ![![-37, 27, -2, 10, -4]], ![![-42, 23, 7, 37, -12]], ![![-1, -6, 20, 88, -15]]]
  g := ![![![4055, -1507, -4357, -1898, -918], ![8383, -3115, -9008, -3924, -1898], ![17329, -6438, -18623, -8112, -3924], ![-2694, 1001, 2895, 1261, 610], ![3677, -1365, -3953, -1722, -833]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-89, 57, 9, 74, -20]] ![![10655, -1507, -4357, -1898, -918]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 245, -217, -308, 228]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![11, 245, -217, -308, 228]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![87, 38, 88, 1, 0], ![56, 14, 110, 0, 1]] where
  M :=![![![11, 245, -217, -308, 228], ![-5472, 3431, -1010, -4482, -308], ![7392, -10092, 6115, 12930, -4482], ![14232, -4927, -849, 6631, 4396], ![-55416, 55299, -28121, -71292, 15337]]]
  hmulB := by decide  
  f := ![![![100817, 4431, -25845, -9380, -6274]], ![![150576, 6707, -38628, -13998, -9380]], ![![225120, 9876, -57659, -20934, -13998]], ![![246381, 10842, -63136, -22913, -15328]], ![![233728, 10267, -59879, -21736, -14537]]]
  g := ![![![101, 63, 13, -308, 228], ![2890, 1281, 3074, -4482, -308], ![-6234, -3156, -4595, 12930, -4482], ![-5819, -2291, -7683, 6631, 4396], ![38044, 18343, 32795, -71292, 15337]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [16, 49, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 51, 110], [138, 87, 29], [0, 1]]
 g := ![![[121, 120, 80], [115, 78, 127], [135, 80], [131, 23, 34], [123, 51], [9, 1], []], ![[89, 37, 10, 101], [33, 2, 21, 70], [4, 67], [113, 138, 118, 98], [24, 63], [83, 63], [24, 7]], ![[58, 0, 114, 49], [13, 129], [9, 35], [98, 54, 75, 127], [93, 106], [10, 99], [105, 7]]]
 h' := ![![[10, 51, 110], [106, 98, 48], [46, 136, 108], [128, 33, 48], [3, 90, 27], [134, 99, 32], [0, 0, 1], [0, 1]], ![[138, 87, 29], [103, 57, 83], [63, 93, 31], [31, 78, 22], [46, 134, 17], [98, 87, 52], [133, 10, 87], [10, 51, 110]], ![[0, 1], [36, 123, 8], [112, 49], [123, 28, 69], [33, 54, 95], [100, 92, 55], [128, 129, 51], [138, 87, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 96], []]
 b := ![[], [103, 120, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [16, 49, 130, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-182496, 155368, -71708, -213703, 28437]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![120987, 56676, 112274, -213703, 28437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![421, -292, -12, -79, 7]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![421, -292, -12, -79, 7]] 
 ![![139, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![421, -292, -12, -79, 7], ![-168, 526, -277, 39, -79], ![1896, -1353, -28, -357, 39], ![-1104, 1090, -192, 212, -79], ![480, -372, 14, -87, 14]]]
  hmulB := by decide  
  f := ![![![741823, 32642, -190346, -69067, -46203]], ![![360210, 15850, -92427, -33537, -22435]], ![![502916, 22129, -129044, -46823, -31323]], ![![285198, 12550, -73180, -26554, -17763]], ![![137234, 6040, -35214, -12779, -8548]]]
  g := ![![![179, -292, -12, -79, 7], ![-68, 526, -277, 39, -79], ![806, -1353, -28, -357, 39], ![-466, 1090, -192, 212, -79], ![202, -372, 14, -87, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-186731, 26373, 76325, 33245, 16083]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-186731, 26373, 76325, 33245, 16083]] 
 ![![139, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![106, 0, 0, 0, 1]] where
  M :=![![![-186731, 26373, 76325, 33245, 16083], ![-385992, 54514, 157771, 68721, 33245], ![-797880, 112683, 326126, 142053, 68721], ![124056, -17519, -50709, -22090, -10685], ![-169272, 23907, 69183, 30129, 14576]]]
  hmulB := by decide  
  f := ![![![-2041601, 2220925, -495873, 397145, -183809]], ![![-1495792, 1627176, -363305, 290971, -134669]], ![![-450454, 490019, -109408, 87625, -40555]], ![![-616658, 670823, -149777, 119956, -55519]], ![![-1575974, 1714399, -382779, 306569, -141888]]]
  g := ![![![-58619, 26373, 76325, 33245, 16083], ![-121170, 54514, 157771, 68721, 33245], ![-250468, 112683, 326126, 142053, 68721], ![38944, -17519, -50709, -22090, -10685], ![-53132, 23907, 69183, 30129, 14576]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![11, 245, -217, -308, 228]] ![![421, -292, -12, -79, 7]]
  ![![1511, -1277, 407, 1023, -217]] where
 M := ![![![1511, -1277, 407, 1023, -217]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![1511, -1277, 407, 1023, -217]] ![![-186731, 26373, 76325, 33245, 16083]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![49665395, -7012550, -20301228, -8844014, -4276752]]]
 hmul := by decide  
 g := ![![![![357305, -50450, -146052, -63626, -30768]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1385, -981, 355, 1276, -12]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![1385, -981, 355, 1276, -12]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![46, 119, 107, 142, 1]] where
  M :=![![![1385, -981, 355, 1276, -12], ![288, 1205, -1144, -1482, 1276], ![-30624, 19428, -5849, -25386, -1482], ![21240, -18523, 8457, 23983, -3490], ![116856, -67251, 16347, 88176, 12031]]]
  hmulB := by decide  
  f := ![![![144157, 6343, -36987, -13420, -8978]], ![![215472, 9487, -55286, -20058, -13420]], ![![322080, 14172, -82633, -29982, -20058]], ![![-80808, -3551, 20731, 7523, 5032]], ![![370598, 16316, -95086, -34498, -23081]]]
  g := ![![![13, 3, 11, 20, -12], ![-392, -1011, -924, -1226, 1276], ![252, 1314, 1025, 1242, -1482], ![1220, 2663, 2563, 3487, -3490], ![-2930, -10060, -8530, -10874, 12031]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [54, 17, 86, 107, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 13, 59, 120], [63, 107, 35, 122], [50, 28, 55, 56], [0, 1]]
 g := ![![[131, 86, 77, 132], [92, 78, 33], [76, 32, 125, 35], [97, 135, 116], [43, 71, 112, 125], [1], []], ![[64, 18, 134, 29, 103, 132], [104, 102, 67], [32, 19, 48, 4, 72, 30], [133, 7, 25], [48, 47, 37, 126, 8, 9], [21, 77, 102], [125, 14, 96]], ![[142, 91, 20, 57, 58, 138], [89, 31, 47], [147, 8, 85, 130, 112, 135], [57, 118, 63], [133, 19, 43, 70, 100, 90], [48, 3, 143], [75, 120, 133]], ![[14, 119, 6, 102, 61, 78], [89, 104, 22], [13, 27, 53, 36, 52, 57], [23, 84, 104], [44, 134, 45, 122, 80, 3], [53, 85, 42], [83, 47, 7]]]
 h' := ![![[78, 13, 59, 120], [103, 96, 121, 79], [68, 87, 92, 35], [96, 102, 140, 83], [62, 139, 121, 50], [95, 132, 63, 42], [0, 0, 1], [0, 1]], ![[63, 107, 35, 122], [81, 20, 99, 145], [83, 26, 62, 31], [115, 94, 89, 75], [88, 35, 0, 5], [41, 26, 109, 47], [79, 41, 55, 20], [78, 13, 59, 120]], ![[50, 28, 55, 56], [66, 36, 137, 37], [113, 127, 96, 135], [82, 61, 77, 137], [110, 35, 43, 130], [95, 114, 25, 120], [68, 65, 38, 21], [63, 107, 35, 122]], ![[0, 1], [35, 146, 90, 37], [64, 58, 48, 97], [19, 41, 141, 3], [48, 89, 134, 113], [57, 26, 101, 89], [104, 43, 55, 108], [50, 28, 55, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [112, 65, 2], []]
 b := ![[], [], [27, 20, 37, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [54, 17, 86, 107, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5338935, -18313916, 17652557, 21179966, -18644975]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5720335, 14768041, 13507818, 17911184, -18644975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-144157, -6343, 36987, 13420, 8978]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-144157, -6343, 36987, 13420, 8978]] 
 ![![149, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![121, 0, 0, 0, 1]] where
  M :=![![![-144157, -6343, 36987, 13420, 8978], ![-215472, -9487, 55286, 20058, 13420], ![-322080, -14172, 82633, 29982, 20058], ![80808, 3551, -20731, -7523, -5032], ![41112, 1809, -10551, -3828, -2561]]]
  hmulB := by decide  
  f := ![![![-1385, 981, -355, -1276, 12]], ![![-67, 38, -9, -50, -8]], ![![-724, 528, -199, -686, 18]], ![![-440, 335, -133, -435, 26]], ![![-1909, 1248, -398, -1628, -71]]]
  g := ![![![-35666, -6343, 36987, 13420, 8978], ![-53311, -9487, 55286, 20058, 13420], ![-79682, -14172, 82633, 29982, 20058], ![19991, 3551, -20731, -7523, -5032], ![10174, 1809, -10551, -3828, -2561]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![1385, -981, 355, 1276, -12]] ![![-144157, -6343, 36987, 13420, 8978]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22655, -997, 5813, 2109, 1411]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-22655, -997, 5813, 2109, 1411]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![61, 135, 1, 0, 0], ![107, 51, 0, 1, 0], ![140, 3, 0, 0, 1]] where
  M :=![![![-22655, -997, 5813, 2109, 1411], ![-33864, -1490, 8689, 3153, 2109], ![-50616, -2229, 12988, 4713, 3153], ![12696, 561, -3259, -1184, -791], ![6456, 285, -1657, -603, -404]]]
  hmulB := by decide  
  f := ![![![343, -77, -121, -63, -25]], ![![600, -32, -277, -87, -63]], ![![685, -62, -300, -105, -67]], ![![443, -64, -179, -74, -39]], ![![332, -73, -118, -60, -25]]]
  g := ![![![-5301, -5944, 5813, 2109, 1411], ![-7924, -8885, 8689, 3153, 2109], ![-11845, -13281, 12988, 4713, 3153], ![2973, 3333, -3259, -1184, -791], ![1514, 1695, -1657, -603, -404]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [102, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 150], [0, 1]]
 g := ![![[22, 137], [95, 78], [118, 17], [123], [140, 36], [139], [1]], ![[30, 14], [72, 73], [22, 134], [123], [141, 115], [139], [1]]]
 h' := ![![[21, 150], [125, 52], [44, 94], [135, 116], [65, 24], [1, 145], [49, 21], [0, 1]], ![[0, 1], [9, 99], [55, 57], [4, 35], [116, 127], [26, 6], [37, 130], [21, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [83, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [102, 130, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2383, 2819, -1249, -3592, 1385]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1750, 2321, -1249, -3592, 1385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4319, 4318, -878, 807, -337]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-4319, 4318, -878, 807, -337]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![26, 30, 1, 0, 0], ![8, 91, 0, 1, 0], ![100, 148, 0, 0, 1]] where
  M :=![![![-4319, 4318, -878, 807, -337], ![8088, -9374, 2225, -1623, 807], ![-19368, 20193, -4304, 3693, -1623], ![16176, -17382, 3832, -3128, 1427], ![-5088, 5628, -1274, 999, -470]]]
  hmulB := by decide  
  f := ![![![7, 68, -60, -81, 73]], ![![-1752, 1102, -323, -1431, -81]], ![![-334, 211, -62, -273, -13]], ![![-1024, 656, -199, -851, -36]], ![![-1820, 1236, -414, -1599, 2]]]
  g := ![![![303, 47, -878, 807, -337], ![-778, -317, 2225, -1623, 807], ![1492, 354, -4304, 3693, -1623], ![-1332, -390, 3832, -3128, 1427], ![444, 149, -1274, 999, -470]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [99, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 150], [0, 1]]
 g := ![![[93, 90], [96, 127], [144, 19], [2], [127, 125], [16], [1]], ![[0, 61], [0, 24], [69, 132], [2], [23, 26], [16], [1]]]
 h' := ![![[4, 150], [9, 111], [89, 91], [43, 64], [111, 105], [63, 27], [52, 4], [0, 1]], ![[0, 1], [0, 40], [0, 60], [148, 87], [78, 46], [20, 124], [68, 147], [4, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [89, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [99, 147, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![727, -19, 7, 175, -1]
  a := ![4, 0, 0, 1, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5, -106, 7, 175, -1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8611, -1376, -3482, -1557, -727]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![8611, -1376, -3482, -1557, -727]] 
 ![![151, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![144, 0, 0, 1, 0], ![138, 0, 0, 0, 1]] where
  M :=![![![8611, -1376, -3482, -1557, -727], ![17448, -2294, -7357, -3135, -1557], ![37368, -5907, -15002, -6711, -3135], ![-6144, 1344, 2224, 1114, 449], ![8160, -1284, -3224, -1449, -674]]]
  hmulB := by decide  
  f := ![![![16525, -12370, 4800, 16071, -869]], ![![15131, -11200, 4285, 14556, -682]], ![![9046, -6949, 2782, 9021, -635]], ![![17136, -13152, 5260, 17074, -1193]], ![![25422, -17724, 6248, 23079, -164]]]
  g := ![![![5899, -1376, -3482, -1557, -727], ![11774, -2294, -7357, -3135, -1557], ![25403, -5907, -15002, -6711, -3135], ![-4294, 1344, 2224, 1114, 449], ![5480, -1284, -3224, -1449, -674]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-22655, -997, 5813, 2109, 1411]] ![![-4319, 4318, -878, 807, -337]]
  ![![4133041, 185967, -1062313, -384408, -257970]] where
 M := ![![![4133041, 185967, -1062313, -384408, -257970]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![4133041, 185967, -1062313, -384408, -257970]] ![![8611, -1376, -3482, -1557, -727]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-605376365, -24000695, 154183533, 56599179, 37352417]]]
 hmul := by decide  
 g := ![![![![-4009115, -158945, 1021083, 374829, 247367]]]]
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


lemma PB1906I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1906I3 : PrimesBelowBoundCertificateInterval O 103 151 1906 where
  m := 9
  g := ![2, 3, 2, 1, 4, 2, 3, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1906I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2, I131N3]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
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
    · exact ![131079601, 107]
    · exact ![11881, 11881, 109]
    · exact ![163047361, 113]
    · exact ![33038369407]
    · exact ![17161, 131, 131, 131]
    · exact ![352275361, 137]
    · exact ![2685619, 139, 139]
    · exact ![492884401, 149]
    · exact ![22801, 22801, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
      exact NI131N3
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
  β := ![I107N1, I109N2, I113N1, I131N1, I131N2, I131N3, I137N1, I139N1, I139N2, I149N1, I151N2]
  Il := ![[I107N1], [I109N2], [I113N1], [], [I131N1, I131N2, I131N3], [I137N1], [I139N1, I139N2], [I149N1], [I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
