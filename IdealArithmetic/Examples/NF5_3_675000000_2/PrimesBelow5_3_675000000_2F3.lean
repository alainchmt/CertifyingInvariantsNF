
import IdealArithmetic.Examples.NF5_3_675000000_2.RI5_3_675000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14845, 423, 2647, -2266, -6258]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-14845, 423, 2647, -2266, -6258]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![90, 68, 17, 23, 1]] where
  M :=![![![-14845, 423, 2647, -2266, -6258], ![41000, -10134, -1303, 4890, -2160], ![36840, 37215, -22074, 2210, 67320], ![-73472, 4667, 10663, -10171, -23196], ![44236, 890, -7856, 5736, 18779]]]
  hmulB := by decide  
  f := ![![![1409, -31, 259, -1758, -2634]], ![![14040, -1688, 851, -9710, -10560]], ![![45640, -1975, 7172, -51450, -74280]], ![![31824, -3579, 2239, -23409, -26748]], ![![24250, -2178, 2395, -20947, -26629]]]
  g := ![![![5125, 3981, 1019, 1324, -6258], ![2200, 1278, 331, 510, -2160], ![-56280, -42435, -10902, -14450, 67320], ![18824, 14785, 3785, 4891, -23196], ![-15382, -11926, -3057, -3983, 18779]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [15, 65, 60, 75, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 15, 90, 43], [18, 0, 30, 92], [91, 91, 94, 79], [0, 1]]
 g := ![![[105, 3, 50, 92], [65, 79, 81, 29], [72, 70, 75], [83, 22, 63, 87], [1, 32, 1], []], ![[36, 60, 4, 70, 106, 58], [81, 5, 59, 28, 83, 51], [35, 59, 36], [77, 33, 21, 11, 75, 91], [5, 60, 34], [98, 60, 90, 56, 53, 6]], ![[31, 85, 21, 29, 28, 61], [74, 32, 60, 68, 36, 105], [71, 27, 16], [20, 54, 48, 93, 81, 35], [43, 63, 42], [62, 38, 67, 3, 97, 49]], ![[4, 56, 77, 68, 53, 79], [68, 52, 93, 60, 82, 23], [65, 36, 49], [9, 66, 30, 58, 6, 64], [5, 30, 76], [11, 36, 81, 26, 17, 90]]]
 h' := ![![[30, 15, 90, 43], [95, 2, 94, 29], [13, 11, 104, 52], [39, 64, 7, 17], [92, 97, 92, 80], [0, 0, 0, 1], [0, 1]], ![[18, 0, 30, 92], [19, 53, 6, 41], [26, 8, 62, 83], [103, 32, 100, 101], [62, 35, 13, 53], [64, 60, 28, 81], [30, 15, 90, 43]], ![[91, 91, 94, 79], [74, 72, 93, 38], [16, 29, 26, 97], [92, 35, 74, 103], [76, 72, 56, 60], [87, 1, 30, 91], [18, 0, 30, 92]], ![[0, 1], [68, 87, 21, 106], [57, 59, 22, 89], [60, 83, 33, 100], [72, 10, 53, 21], [19, 46, 49, 41], [91, 91, 94, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [26, 85, 76], []]
 b := ![[], [], [20, 92, 32, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [15, 65, 60, 75, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6829752090, 496137615, -822613776, 6560335800, 8844957420]
  a := ![-25, -8, 9, -28, -75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7503513270, -5616457635, -1412961588, -1839940980, 8844957420]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1409, 31, -259, 1758, 2634]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-1409, 31, -259, 1758, 2634]] 
 ![![107, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![71, 0, 0, 0, 1]] where
  M :=![![![-1409, 31, -259, 1758, 2634], ![-14040, 1688, -851, 9710, 10560], ![-45640, 1975, -7172, 51450, 74280], ![-31824, 3579, -2239, 23409, 26748], ![-5388, -420, -1666, 9772, 16199]]]
  hmulB := by decide  
  f := ![![![14845, -423, -2647, 2266, 6258]], ![![6415, -99, -1200, 992, 2886]], ![![7980, -585, -1278, 1250, 2880]], ![![8456, -265, -1485, 1281, 3492]], ![![9437, -289, -1683, 1450, 3977]]]
  g := ![![![-2550, 31, -259, 1758, 2634], ![-12516, 1688, -851, 9710, 10560], ![-73525, 1975, -7172, 51450, 74280], ![-30681, 3579, -2239, 23409, 26748], ![-14787, -420, -1666, 9772, 16199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-14845, 423, 2647, -2266, -6258]] ![![-1409, 31, -259, 1758, 2634]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-158457, -48713, -21013, 45236, 79181]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-158457, -48713, -21013, 45236, 79181]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![40, 3, 1, 0, 0], ![97, 69, 0, 1, 0], ![108, 32, 0, 0, 1]] where
  M :=![![![-158457, -48713, -21013, 45236, 79181], ![-452504, -139105, -60004, 129176, 226108], ![-1292160, -397240, -171349, 368880, 645680], ![-142740, -43882, -18930, 40751, 71330], ![-111222, -34192, -14748, 31750, 55575]]]
  hmulB := by decide  
  f := ![![![2549, -233, 255, -2206, -2815]], ![![13696, -1197, 1364, -11904, -15212]], ![![1992, -179, 199, -1728, -2204]], ![![11241, -992, 1121, -9763, -12473]], ![![6678, -594, 666, -5794, -7399]]]
  g := ![![![-112453, -51750, -21013, 45236, 79181], ![-321120, -147777, -60004, 129176, 226108], ![-917000, -421997, -171349, 368880, 645680], ![-101303, -46619, -18930, 40751, 71330], ![-78928, -36322, -14748, 31750, 55575]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [52, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 108], [0, 1]]
 g := ![![[31, 28], [36], [94, 22], [30, 16], [46], [23, 1]], ![[21, 81], [36], [55, 87], [71, 93], [46], [46, 108]]]
 h' := ![![[23, 108], [52, 79], [17, 103], [75, 83], [15, 105], [3, 41], [0, 1]], ![[0, 1], [16, 30], [97, 6], [22, 26], [32, 4], [74, 68], [23, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [87, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [52, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-322881, -101424, -138028, 880220, 1514640]
  a := ![-169, -58, 56, -170, -510]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2236369, -999000, -138028, 880220, 1514640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-987, 716, -178, -144, 746]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-987, 716, -178, -144, 746]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![50, 62, 1, 0, 0], ![17, 68, 0, 1, 0], ![83, 92, 0, 0, 1]] where
  M :=![![![-987, 716, -178, -144, 746], ![-6544, -1275, 1750, -864, -4712], ![34240, -3370, -4259, 4620, 8480], ![-1664, 3242, -1288, -283, 4508], ![4036, -2098, 326, 568, -1731]]]
  hmulB := by decide  
  f := ![![![-50159, -15716, -6770, 14456, 25646]], ![![-147344, -43907, -18982, 41416, 70888]], ![![-110502, -33376, -14415, 31268, 54044]], ![![-100203, -29962, -12950, 28213, 48410]], ![![-162837, -49138, -21224, 46056, 79551]]]
  g := ![![![-473, -432, -178, -144, 746], ![2860, 3509, 1750, -864, -4712], ![-4910, -7648, -4259, 4620, 8480], ![-2813, -2866, -1288, -283, 4508], ![1117, 902, 326, 568, -1731]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [70, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 108], [0, 1]]
 g := ![![[44, 63], [43], [45, 31], [38, 9], [3], [81, 1]], ![[24, 46], [43], [49, 78], [4, 100], [3], [53, 108]]]
 h' := ![![[81, 108], [54, 45], [11, 32], [65, 85], [12, 3], [107, 60], [0, 1]], ![[0, 1], [102, 64], [96, 77], [83, 24], [37, 106], [62, 49], [81, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [6, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [70, 28, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4532, -400, -864, 6518, 10044]
  a := ![-14, -5, 5, -16, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8310, -12056, -864, 6518, 10044]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -77, -55, 166, 459]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![197, -77, -55, 166, 459]] 
 ![![109, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![197, -77, -55, 166, 459], ![-3008, 547, 50, 1032, 156], ![2880, -1570, -1361, 4940, 11760], ![-5928, 1004, 6, 2451, 1146], ![2694, -808, -444, 878, 3481]]]
  hmulB := by decide  
  f := ![![![-8377, 1047, 1001, -1200, -1929]], ![![-3284, 363, 418, -472, -840]], ![![-1458, 368, 93, -220, -66]], ![![-3258, 422, 380, -465, -720]], ![![-4913, 623, 585, -706, -1124]]]
  g := ![![![-294, -77, -55, 166, 459], ![-716, 547, 50, 1032, 156], ![-7966, -1570, -1361, 4940, 11760], ![-2020, 1004, 6, 2451, 1146], ![-1989, -808, -444, 878, 3481]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-158457, -48713, -21013, 45236, 79181]] ![![-987, 716, -178, -144, 746]]
  ![![-8377, 1047, 1001, -1200, -1929]] where
 M := ![![![-8377, 1047, 1001, -1200, -1929]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-8377, 1047, 1001, -1200, -1929]] ![![197, -77, -55, 166, 459]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-831, -105, -51, 174, 131]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-831, -105, -51, 174, 131]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![7, 36, 45, 1, 0], ![18, 4, 33, 0, 1]] where
  M :=![![![-831, -105, -51, 174, 131], ![-352, -781, -322, 448, 1564], ![-10720, 50, -113, 1700, -880], ![1560, -656, -262, 167, 1610], ![-3018, 496, 164, 238, -1227]]]
  hmulB := by decide  
  f := ![![![719, 39, -143, 96, 355]], ![![-2456, 455, 202, -336, -268]], ![![800, -2050, 859, 140, -2960]], ![![-387, -669, 392, -41, -1229]], ![![244, -578, 239, 42, -827]]]
  g := ![![![-39, -61, -108, 174, 131], ![-280, -205, -638, 448, 1564], ![-60, -510, -421, 1700, -880], ![-253, -116, -539, 167, 1610], ![154, -28, 265, 238, -1227]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [9, 7, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 65, 22], [65, 47, 91], [0, 1]]
 g := ![![[36, 100, 98], [112, 105], [82, 49], [18, 102], [21, 7, 72], [1]], ![[44, 38, 16, 49], [100, 32], [15, 53], [31, 63], [13, 89, 28, 53], [64, 11, 71, 26]], ![[42, 106, 85, 97], [110, 109], [45, 50], [74, 16], [3, 5, 78, 2], [77, 44, 59, 87]]]
 h' := ![![[15, 65, 22], [58, 102, 95], [106, 71, 61], [77, 32, 106], [37, 97, 92], [104, 106, 80], [0, 1]], ![[65, 47, 91], [54, 53, 42], [29, 16, 22], [86, 81, 36], [79, 82, 17], [87, 49, 103], [15, 65, 22]], ![[0, 1], [59, 71, 89], [22, 26, 30], [75, 0, 84], [96, 47, 4], [20, 71, 43], [65, 47, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 102], []]
 b := ![[], [62, 38, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [9, 7, 33, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-309850687, -8051327, -80511013, 493670321, 786347785]
  a := ![90, 27, -31, 89, 269]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-158582328, -185182071, -426948251, 493670321, 786347785]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![719, 39, -143, 96, 355]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![719, 39, -143, 96, 355]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![76, 2, 1, 0, 0], ![30, 19, 0, 1, 0], ![71, 97, 0, 0, 1]] where
  M :=![![![719, 39, -143, 96, 355], ![-2456, 455, 202, -336, -268], ![800, -2050, 859, 140, -2960], ![3652, 0, -630, 491, 1486], ![-1946, -186, 426, -258, -1089]]]
  hmulB := by decide  
  f := ![![![-831, -105, -51, 174, 131]], ![![-352, -781, -322, 448, 1564]], ![![-660, -84, -41, 140, 108]], ![![-266, -165, -70, 123, 312]], ![![-851, -732, -307, 496, 1414]]]
  g := ![![![-146, -318, -143, 96, 355], ![100, 287, 202, -336, -268], ![1252, 2484, 859, 140, -2960], ![-608, -1347, -630, 491, 1486], ![449, 969, 426, -258, -1089]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P1 : CertificateIrreducibleZModOfList' 113 2 2 6 [3, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 112], [0, 1]]
 g := ![![[85, 50], [91], [85], [1], [52, 62], [84, 1]], ![[104, 63], [91], [85], [1], [62, 51], [55, 112]]]
 h' := ![![[84, 112], [44, 29], [59, 59], [38, 57], [70, 112], [87, 47], [0, 1]], ![[0, 1], [107, 84], [43, 54], [80, 56], [99, 1], [80, 66], [84, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [26, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N1 : CertifiedPrimeIdeal' SI113N1 113 where
  n := 2
  hpos := by decide
  P := [3, 29, 1]
  hirr := P113P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1075, -7573, -5005, 27096, 54038]
  a := ![-37, -7, 14, -32, -110]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37771, -50921, -5005, 27096, 54038]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N1 B_one_repr
lemma NI113N1 : Nat.card (O ⧸ I113N1) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-831, -105, -51, 174, 131]] ![![719, 39, -143, 96, 355]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 5 2 6 [16, 71, 30, 19, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [81, 120, 61, 96, 51], [38, 81, 0, 32, 30], [71, 42, 6, 36, 109], [59, 10, 60, 90, 64], [0, 1]]
 g := ![![[114, 34, 85, 125, 81], [51, 107, 120, 63, 99], [86, 93, 106, 113, 44], [64, 11, 78, 61, 82], [6, 122, 1], []], ![[72, 117, 97, 69, 15, 91, 72, 55], [62, 107, 87, 50, 28, 112, 126, 51], [107, 82, 71, 49, 30, 52, 41, 96], [4, 97, 25, 9, 2, 68, 123, 43], [68, 5, 10, 48, 94, 17, 31, 125], [46, 61, 126, 123, 29, 122, 108, 63]], ![[19, 31, 48, 84, 33, 107, 29, 73], [14, 51, 21, 99, 1, 125, 13, 81], [81, 82, 15, 89, 3, 39, 101, 1], [36, 99, 15, 4, 76, 97, 34, 49], [20, 11, 39, 8, 20, 114, 51, 30], [80, 113, 13, 80, 70, 87, 41, 76]], ![[106, 28, 114, 46, 6, 103, 124, 108], [50, 107, 98, 106, 6, 110, 23, 20], [82, 5, 121, 73, 76, 48, 101, 51], [85, 83, 49, 77, 43, 33, 60, 102], [107, 60, 96, 8, 16, 29, 62, 23], [22, 107, 95, 56, 92, 89, 17, 10]], ![[14, 38, 81, 69, 32, 61, 99, 35], [119, 65, 45, 46, 15, 65, 119, 25], [101, 23, 53, 91, 125, 39, 112, 69], [39, 118, 109, 36, 51, 46, 0, 60], [49, 95, 47, 55, 59, 61, 100, 62], [46, 22, 60, 13, 96, 79, 51, 16]]]
 h' := ![![[81, 120, 61, 96, 51], [73, 61, 99, 27, 118], [21, 90, 116, 35, 37], [119, 51, 126, 102, 67], [31, 35, 32, 92, 35], [0, 0, 0, 1], [0, 1]], ![[38, 81, 0, 32, 30], [103, 58, 114, 114, 23], [102, 73, 101, 14, 1], [84, 31, 26, 119, 37], [59, 83, 87, 6, 71], [99, 90, 121, 67, 102], [81, 120, 61, 96, 51]], ![[71, 42, 6, 36, 109], [106, 36, 75, 105, 120], [16, 77, 20, 126, 102], [56, 8, 77, 94, 31], [86, 98, 112, 38, 37], [125, 123, 88, 12, 126], [38, 81, 0, 32, 30]], ![[59, 10, 60, 90, 64], [108, 39, 44, 26, 11], [30, 37, 122, 56, 34], [17, 24, 107, 44, 22], [92, 37, 106, 54, 29], [54, 67, 1, 97, 65], [71, 42, 6, 36, 109]], ![[0, 1], [120, 60, 49, 109, 109], [41, 104, 22, 23, 80], [101, 13, 45, 22, 97], [108, 1, 44, 64, 82], [46, 101, 44, 77, 88], [59, 10, 60, 90, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 73, 23, 45], [], [], []]
 b := ![[], [108, 33, 118, 80, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 5
  hpos := by decide
  P := [16, 71, 30, 19, 5, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7453470119700, -1796802999478, -687382534046, -19985251114, 4702815623052]
  a := ![28, -2, -10, 10, 84]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![58688741100, -14148055114, -5412460898, -157364182, 37030044276]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-373335, 117863, 7029, -51860, 37272]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-373335, 117863, 7029, -51860, 37272]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![6, 90, 113, 85, 1]] where
  M :=![![![-373335, 117863, 7029, -51860, 37272], ![-505616, -352778, 258855, -62606, -771408], ![5920840, -45355, -998974, 795310, 2334360], ![-1296556, 581953, -59589, -182675, 406332], ![1253792, -325670, -57744, 173120, -12643]]]
  hmulB := by decide  
  f := ![![![-1149, 85, -3, 284, 0]], ![![1136, -880, -483, 1106, 3408]], ![![-22840, 3235, 316, 6410, -360]], ![![2284, -1081, -753, 2255, 6132]], ![![-17550, 1500, -545, 7775, 5993]]]
  g := ![![![-4557, -24707, -32097, -24580, 37272], ![31472, 527282, 667389, 500054, -771408], ![-61720, -1604105, -2021234, -1508590, 2334360], ![-28508, -274717, -350955, -265045, 406332], ![10150, 6200, 10465, 9525, -12643]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [6, 81, 89, 34, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 38, 8, 69], [100, 121, 98, 103], [81, 102, 25, 90], [0, 1]]
 g := ![![[14, 42, 81, 80], [5, 21, 95, 3], [120, 10, 108], [98, 64, 121], [56, 22, 108], [1], []], ![[39, 12, 26, 7, 62, 93], [64, 12, 11, 18, 104, 14], [118, 1, 101], [36, 48, 27], [53, 94, 35], [12, 121, 113], [67, 98, 45]], ![[84, 39, 104, 94, 8, 128], [56, 4, 49, 86, 73, 22], [76, 109, 123], [59, 111, 34], [10, 11, 33], [72, 99, 44], [87, 82, 129]], ![[24, 33, 15, 36, 26, 56], [14, 87, 122, 13, 114, 23], [11, 18, 9], [76, 91, 63], [35, 51, 41], [129, 57, 58], [104, 8, 109]]]
 h' := ![![[47, 38, 8, 69], [101, 6, 4, 39], [119, 105, 106, 93], [70, 94, 73, 97], [93, 103, 84, 120], [125, 50, 42, 97], [0, 0, 1], [0, 1]], ![[100, 121, 98, 103], [27, 3, 11, 8], [79, 71, 17, 129], [130, 95, 23, 106], [79, 30, 13, 17], [2, 10, 35, 67], [104, 46, 77, 47], [47, 38, 8, 69]], ![[81, 102, 25, 90], [109, 86, 115, 58], [81, 11, 101, 35], [119, 16, 112, 56], [39, 112, 93, 54], [112, 105, 46, 65], [46, 24, 87, 31], [100, 121, 98, 103]], ![[0, 1], [86, 36, 1, 26], [124, 75, 38, 5], [37, 57, 54, 3], [10, 17, 72, 71], [73, 97, 8, 33], [42, 61, 97, 53], [81, 102, 25, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [106, 18, 21], []]
 b := ![[], [], [105, 15, 120, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [6, 81, 89, 34, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-335806922, 30514187, -33482702, 292571567, 373255601]
  a := ![10, 7, -2, 13, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19659088, -256202213, -322224165, -239955378, 373255601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1149, -85, 3, -284, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![1149, -85, 3, -284, 0]] 
 ![![131, 0, 0, 0, 0], ![32, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![1149, -85, 3, -284, 0], ![-1136, 880, 483, -1106, -3408], ![22840, -3235, -316, -6410, 360], ![-2284, 1081, 753, -2255, -6132], ![7616, -1520, -390, -1276, 2177]]]
  hmulB := by decide  
  f := ![![![373335, -117863, -7029, 51860, -37272]], ![![95056, -26098, -3693, 13146, -3216]], ![![23200, -21247, 6338, 3430, -24648]], ![![44096, -15239, -189, 6145, -6516]], ![![141473, -45199, -2403, 19660, -14983]]]
  g := ![![![55, -85, 3, -284, 0], ![1168, 880, 483, -1106, -3408], ![1464, -3235, -316, -6410, 360], ![2268, 1081, 753, -2255, -6132], ![-263, -1520, -390, -1276, 2177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-373335, 117863, 7029, -51860, 37272]] ![![1149, -85, 3, -284, 0]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-729, -181, -81, 174, 321]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-729, -181, -81, 174, 321]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![104, 104, 42, 62, 1]] where
  M :=![![![-729, -181, -81, 174, 321], ![-1872, -639, -208, 528, 804], ![-4320, -1580, -891, 1640, 3120], ![-904, -82, -70, 125, 318], ![-190, -190, -82, 166, 259]]]
  hmulB := by decide  
  f := ![![![1, -1, -1, 4, 9]], ![![-56, 9, 0, 24, 12]], ![![0, -20, -27, 120, 240]], ![![-116, 18, -2, 57, 42]], ![![-94, 8, -10, 84, 109]]]
  g := ![![![-249, -245, -99, -144, 321], ![-624, -615, -248, -360, 804], ![-2400, -2380, -963, -1400, 3120], ![-248, -242, -98, -143, 318], ![-198, -198, -80, -116, 259]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [118, 125, 52, 85, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 76, 9, 91], [105, 68, 131, 63], [66, 129, 134, 120], [0, 1]]
 g := ![![[37, 52, 72, 8], [117, 111, 65], [111, 68, 121], [40, 19, 53, 81], [41, 118, 101], [1], []], ![[56, 98, 39, 48, 30, 23], [112, 10, 121], [113, 84, 81], [38, 14, 77, 95, 58, 45], [20, 20, 14], [54, 75, 109], [13, 15, 61]], ![[99, 101, 91, 102, 83, 129], [3, 105, 87], [74, 97, 2], [65, 0, 11, 78, 40, 72], [25, 92, 60], [38, 124, 28], [58, 132, 133]], ![[53, 118, 5, 76, 67, 120], [20, 67, 8], [11, 123, 130], [120, 2, 95, 114, 75, 107], [126, 81, 30], [37, 0, 17], [18, 60, 15]]]
 h' := ![![[18, 76, 9, 91], [39, 1, 100, 75], [62, 91, 11, 32], [75, 37, 121, 126], [44, 39, 56, 128], [19, 12, 85, 52], [0, 0, 1], [0, 1]], ![[105, 68, 131, 63], [0, 40, 113, 43], [129, 42, 113, 11], [41, 28, 136, 9], [81, 29, 45, 31], [48, 118, 125, 98], [23, 26, 50, 66], [18, 76, 9, 91]], ![[66, 129, 134, 120], [46, 90, 41, 20], [117, 4, 82, 19], [9, 54, 20, 106], [8, 34, 27, 28], [9, 86, 109, 103], [71, 85, 75, 24], [105, 68, 131, 63]], ![[0, 1], [99, 6, 20, 136], [33, 0, 68, 75], [57, 18, 134, 33], [56, 35, 9, 87], [111, 58, 92, 21], [40, 26, 11, 47], [66, 129, 134, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [74, 98, 100], []]
 b := ![[], [], [123, 56, 7, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [118, 125, 52, 85, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1737572, -414287, -161873, -7595, 1096905]
  a := ![2, -1, -1, 1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-820004, -835711, -337459, -496465, 1096905]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, -1, 4, 9]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![1, -1, -1, 4, 9]] 
 ![![137, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![1, -1, -1, 4, 9], ![-56, 9, 0, 24, 12], ![0, -20, -27, 120, 240], ![-116, 18, -2, 57, 42], ![34, -12, -8, 22, 65]]]
  hmulB := by decide  
  f := ![![![-729, -181, -81, 174, 321]], ![![-450, -113, -50, 108, 198]], ![![-702, -178, -81, 172, 318]], ![![-560, -138, -62, 133, 246]], ![![-608, -152, -68, 146, 269]]]
  g := ![![![-9, -1, -1, 4, 9], ![-34, 9, 0, 24, 12], ![-254, -20, -27, 120, 240], ![-88, 18, -2, 57, 42], ![-56, -12, -8, 22, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-729, -181, -81, 174, 321]] ![![1, -1, -1, 4, 9]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [115, 12, 10, 43, 13, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 49, 46, 105, 97], [108, 123, 63, 110, 43], [27, 32, 12, 28, 81], [94, 73, 18, 35, 57], [0, 1]]
 g := ![![[71, 30, 9, 123, 57], [4, 21, 71, 41, 137], [22, 46, 61, 29], [72, 96, 127, 107, 131], [23, 126, 126, 1], [], []], ![[132, 37, 12, 120, 135, 4, 80, 14], [22, 58, 52, 12, 71, 45, 110, 19], [54, 137, 71, 57], [75, 126, 134, 92, 115, 128, 119, 61], [50, 24, 16, 47], [125, 56, 111, 57], [129, 60, 79, 96]], ![[35, 56, 54, 127, 131, 113, 47, 19], [124, 99, 135, 128, 111, 102, 90, 39], [82, 133, 47, 30], [113, 6, 93, 6, 88, 77, 30, 101], [66, 64, 116, 64], [46, 93, 55, 38], [89, 49, 18, 42]], ![[114, 52, 76, 73, 115, 28], [11, 48, 124, 72, 33, 112, 95, 63], [35, 3, 7, 1], [118, 82, 122, 44, 133, 4, 126, 29], [35, 130, 124, 81], [27, 67, 88, 131], [55, 108, 2, 28]], ![[83, 30, 19, 37, 105, 74, 115, 29], [62, 62, 17, 99, 118, 91, 137, 16], [22, 95, 58, 34], [101, 91, 66, 126, 110, 26, 70, 51], [131, 116, 49, 52], [129, 70, 40, 20], [124, 76, 117, 52]]]
 h' := ![![[36, 49, 46, 105, 97], [96, 135, 48, 128, 125], [97, 3, 80, 21, 50], [60, 66, 42, 127, 86], [135, 107, 31, 16, 100], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[108, 123, 63, 110, 43], [101, 88, 127, 97, 121], [100, 43, 111, 109, 119], [74, 113, 6, 29, 14], [71, 83, 54, 96, 128], [20, 27, 94, 30, 73], [83, 84, 39, 49, 125], [36, 49, 46, 105, 97]], ![[27, 32, 12, 28, 81], [28, 123, 68, 43, 6], [20, 70, 69, 36, 13], [89, 102, 128, 97, 13], [33, 10, 15, 66, 117], [123, 49, 4, 45, 131], [39, 127, 30, 10, 90], [108, 123, 63, 110, 43]], ![[94, 73, 18, 35, 57], [133, 42, 127, 9], [95, 72, 75, 7, 56], [111, 62, 51, 129, 138], [10, 109, 30, 24, 114], [137, 57, 133, 35, 130], [103, 46, 13, 39, 39], [27, 32, 12, 28, 81]], ![[0, 1], [70, 29, 47, 1, 26], [37, 90, 82, 105, 40], [64, 74, 51, 35, 27], [71, 108, 9, 76, 97], [47, 6, 47, 29, 82], [136, 21, 56, 41, 24], [94, 73, 18, 35, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 62, 112, 108], [], [], []]
 b := ![[], [12, 29, 88, 69, 82], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [115, 12, 10, 43, 13, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-106233672057166, 6566098001124, -14216193033058, 108593341562400, 150447041949420]
  a := ![51, 13, -17, 50, 150]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-764271021994, 47238115116, -102274770022, 781247061600, 1082352819780]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3899905, -1198193, -516863, 1112944, 1947262]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-3899905, -1198193, -516863, 1112944, 1947262]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![29, 64, 86, 1, 0], ![48, 99, 96, 0, 1]] where
  M :=![![![-3899905, -1198193, -516863, 1112944, 1947262], ![-11126320, -3424014, -1476819, 3177670, 5566280], ![-31819560, -9766465, -4213074, 9075050, 15866920], ![-3500356, -1082289, -466555, 1001495, 1760152], ![-2748916, -838206, -361732, 781284, 1359603]]]
  hmulB := by decide  
  f := ![![![-367557, 11167, 57951, -49496, -131518]], ![![854160, -258816, -21359, 118490, -67880]], ![![1017000, 797975, -563676, 124610, 1693400]], ![![870719, 352460, -321662, 111611, 919330]], ![![1111412, 345764, -359911, 144014, 1006443]]]
  g := ![![![-870093, -1779903, -1900451, 1112944, 1947262], ![-2486310, -5086286, -5430331, 3177670, 5566280], ![-7091330, -14506005, -15489206, 9075050, 15866920], ![-785443, -1606933, -1715233, 1001495, 1760152], ![-608504, -1244571, -1329356, 781284, 1359603]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [13, 124, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 76, 104], [48, 72, 45], [0, 1]]
 g := ![![[7, 28, 68], [107, 119], [0, 43, 54], [98, 123], [60, 95, 95], [106, 1], []], ![[123, 90, 58, 127], [25, 110], [74, 31, 70, 130], [142, 6], [70, 66, 108, 123], [37, 118], [104, 88]], ![[29, 18, 86, 80], [104, 123], [117, 8, 133, 17], [100, 118], [129, 124, 18, 102], [42, 114], [14, 88]]]
 h' := ![![[58, 76, 104], [99, 85, 98], [0, 54, 87], [100, 9, 90], [114, 144, 102], [112, 104, 86], [0, 0, 1], [0, 1]], ![[48, 72, 45], [12, 65, 102], [121, 43, 109], [71, 23, 115], [24, 43, 119], [78, 127, 22], [75, 140, 72], [58, 76, 104]], ![[0, 1], [108, 148, 98], [62, 52, 102], [47, 117, 93], [119, 111, 77], [5, 67, 41], [36, 9, 76], [48, 72, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121, 31], []]
 b := ![[], [14, 135, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [13, 124, 43, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1542021, -714744, -1265012, 6401350, 11715614]
  a := ![24, 5, -9, 21, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5030407, -10538570, -11251544, 6401350, 11715614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-367557, 11167, 57951, -49496, -131518]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-367557, 11167, 57951, -49496, -131518]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![49, 34, 1, 0, 0], ![42, 9, 0, 1, 0], ![144, 18, 0, 0, 1]] where
  M :=![![![-367557, 11167, 57951, -49496, -131518], ![854160, -258816, -21359, 118490, -67880], ![1017000, 797975, -563676, 124610, 1693400], ![-1731956, 131071, 234895, -234397, -493888], ![1049284, 4, -180950, 140824, 426591]]]
  hmulB := by decide  
  f := ![![![-3899905, -1198193, -516863, 1112944, 1947262]], ![![-11126320, -3424014, -1476819, 3177670, 5566280]], ![![-4034965, -1240902, -535243, 1152014, 2017022]], ![![-1794854, -551829, -238028, 512377, 896924]], ![![-5131604, -1577250, -680354, 1464720, 2563479]]]
  g := ![![![119532, 5729, 57951, -49496, -131518], ![44959, 4180, -21359, 118490, -67880], ![-1479504, -78119, -563676, 124610, 1693400], ![454515, 21102, 234895, -234397, -493888], ![-385422, -18750, -180950, 140824, 426591]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P1 : CertificateIrreducibleZModOfList' 149 2 2 7 [38, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 148], [0, 1]]
 g := ![![[86, 28], [49], [36, 6], [81], [145, 86], [100], [1]], ![[68, 121], [49], [96, 143], [81], [111, 63], [100], [1]]]
 h' := ![![[10, 148], [59, 112], [122, 7], [60, 119], [3, 9], [28, 91], [111, 10], [0, 1]], ![[0, 1], [136, 37], [43, 142], [58, 30], [93, 140], [44, 58], [62, 139], [10, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [17, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N1 : CertifiedPrimeIdeal' SI149N1 149 where
  n := 2
  hpos := by decide
  P := [38, 139, 1]
  hirr := P149P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-318, 559, -395, 2028, 3364]
  a := ![6, 3, -2, 7, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3695, -435, -395, 2028, 3364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N1 B_one_repr
lemma NI149N1 : Nat.card (O ⧸ I149N1) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-3899905, -1198193, -516863, 1112944, 1947262]] ![![-367557, 11167, 57951, -49496, -131518]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 5 2 7 [103, 52, 95, 65, 67, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 81, 55, 96, 107], [144, 93, 71, 31, 141], [150, 144, 55, 83, 37], [7, 134, 121, 92, 17], [0, 1]]
 g := ![![[93, 113, 120, 48, 136], [17, 14, 88, 141, 16], [88, 59, 90, 140, 19], [123, 150, 31, 125], [3, 37, 45, 84, 1], [], []], ![[98, 10, 84, 118, 3, 139, 133, 115], [99, 124, 65, 39, 93, 47, 76, 3], [85, 51, 34, 82, 38, 72, 87, 60], [36, 64, 74, 72], [126, 38, 51, 57, 116, 57, 13, 26], [94, 74, 88, 118], [125, 58, 5, 124]], ![[7, 70, 124, 67, 84, 60, 127, 92], [82, 133, 52, 136, 141, 77, 105, 146], [53, 70, 22, 29, 50, 78, 133, 79], [36, 17, 36, 118], [120, 116, 90, 68, 26, 77, 129, 15], [113, 32, 10, 98], [35, 130, 79, 100]], ![[90, 10, 77, 13, 114, 37, 77, 69], [63, 4, 41, 121, 34, 106, 72, 8], [72, 34, 107, 19, 39, 67, 55, 72], [138, 127, 64, 32], [86, 129, 40, 137, 9, 143, 127, 105], [119, 117, 104, 85], [42, 45, 36, 10]], ![[71, 77, 61, 88, 87, 117, 1, 2], [18, 138, 149, 47, 45, 144, 79, 36], [106, 29, 65, 41, 72, 94, 116, 5], [111, 77, 76, 32], [144, 6, 142, 62, 99, 48, 98, 10], [103, 129, 112, 72], [98, 76, 73, 138]]]
 h' := ![![[85, 81, 55, 96, 107], [61, 106, 128, 38, 49], [147, 87, 5, 95, 4], [64, 19, 74, 68, 87], [144, 110, 102, 96, 124], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[144, 93, 71, 31, 141], [107, 64, 147, 4, 93], [127, 145, 13, 112, 125], [126, 36, 57, 91, 9], [132, 126, 58, 51, 125], [25, 109, 37, 133, 110], [88, 88, 52, 73, 32], [85, 81, 55, 96, 107]], ![[150, 144, 55, 83, 37], [96, 101, 26, 31, 25], [15, 92, 80, 89, 23], [44, 148, 29, 49, 66], [66, 32, 36, 126, 119], [82, 79, 56, 24, 15], [68, 98, 3, 47, 131], [144, 93, 71, 31, 141]], ![[7, 134, 121, 92, 17], [113, 43, 54, 107, 132], [58, 115, 108, 92, 111], [23, 114, 88, 10, 120], [63, 67, 60, 145, 118], [21, 9, 66, 110, 39], [54, 141, 18, 29, 113], [150, 144, 55, 83, 37]], ![[0, 1], [15, 139, 98, 122, 3], [95, 14, 96, 65, 39], [85, 136, 54, 84, 20], [58, 118, 46, 35, 118], [11, 105, 143, 35, 137], [72, 126, 77, 2, 26], [7, 134, 121, 92, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 8, 114, 68], [], [], []]
 b := ![[], [20, 69, 97, 39, 29], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 5
  hpos := by decide
  P := [103, 52, 95, 65, 67, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16664167298339815, -1380177992319666, 1791813578756704, -15054551805491816, -19624613373680416]
  a := ![-115, -39, 38, -140, -352]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![110358723830065, -9140251604766, 11866315091104, -99699018579416, -129964326978016]
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



lemma PB1271I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB1271I3 : PrimesBelowBoundCertificateInterval O 103 151 1271 where
  m := 9
  g := ![2, 3, 2, 1, 2, 2, 1, 2, 1]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB1271I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
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
    · exact ![131079601, 107]
    · exact ![11881, 11881, 109]
    · exact ![1442897, 12769]
    · exact ![33038369407]
    · exact ![294499921, 131]
    · exact ![352275361, 137]
    · exact ![51888844699]
    · exact ![3307949, 22201]
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
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
  β := ![I107N1, I109N2, I131N1, I137N1]
  Il := ![[I107N1], [I109N2], [], [], [I131N1], [I137N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
