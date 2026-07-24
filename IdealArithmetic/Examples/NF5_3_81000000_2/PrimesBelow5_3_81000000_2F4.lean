
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0, 0, 0]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]] where
  M :=![![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![0, 0, 0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 5 2 7 [129, 106, 82, 72, 117, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 50, 109, 145, 156], [23, 134, 26, 17, 122], [79, 120, 47, 77, 127], [74, 9, 132, 75, 66], [0, 1]]
 g := ![![[40, 45, 27, 36, 90], [123, 103, 147, 147], [3, 135, 14, 18, 148], [26, 102, 133, 7, 46], [3, 68, 115, 40, 1], [], []], ![[138, 90, 43, 46, 126, 20, 85, 40], [40, 107, 38, 148], [40, 142, 127, 95, 99, 60, 44, 113], [66, 71, 0, 103, 86, 38, 57, 64], [23, 100, 40, 23, 101, 61, 23, 81], [122, 3], [135, 59, 64, 1]], ![[2, 2, 33, 77, 147, 131, 131, 143], [86, 109, 22, 44], [49, 75, 108, 62, 105, 1, 72, 3], [28, 70, 2, 60, 147, 123, 74, 106], [109, 75, 21, 35, 19, 7, 98, 14], [54, 46, 132, 49], [116, 56, 82, 126]], ![[137, 94, 79, 110, 19, 59, 32, 27], [153, 141, 140, 145], [90, 73, 105, 81, 119, 112, 133, 140], [85, 54, 2, 29, 48, 69, 122, 109], [139, 82, 6, 105, 74, 111, 65, 154], [47, 25, 106, 111], [12, 152, 137, 115]], ![[127, 11, 31, 79, 138, 142, 29, 134], [0, 80, 101, 140], [75, 56, 109, 67, 144, 24, 9, 103], [93, 122, 32, 25, 56, 140, 79, 119], [135, 18, 147, 120, 2, 121, 23, 5], [39, 82, 66, 57], [48, 126, 136, 117]]]
 h' := ![![[21, 50, 109, 145, 156], [138, 82, 63, 124, 54], [84, 117, 111, 94, 124], [100, 91, 62, 37, 73], [84, 16, 5, 94, 108], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[23, 134, 26, 17, 122], [2, 20, 145, 17, 91], [74, 34, 141, 78, 73], [18, 99, 5, 21, 94], [152, 102, 85, 124, 67], [129, 17, 69, 8, 95], [139, 118, 24, 72], [21, 50, 109, 145, 156]], ![[79, 120, 47, 77, 127], [1, 85, 113, 31, 122], [24, 151, 118, 51, 63], [101, 120, 64, 122, 82], [147, 69, 139, 52, 50], [23, 76, 149, 82, 38], [9, 146, 34, 4, 7], [23, 134, 26, 17, 122]], ![[74, 9, 132, 75, 66], [144, 65, 49, 153, 100], [16, 96, 92, 88, 107], [4, 5, 126, 40, 10], [30, 57, 21, 112, 70], [35, 82, 106, 105, 61], [140, 121, 88, 72, 116], [79, 120, 47, 77, 127]], ![[0, 1], [111, 62, 101, 146, 104], [41, 73, 9, 3, 104], [155, 156, 57, 94, 55], [92, 70, 64, 89, 19], [44, 139, 147, 119, 119], [69, 86, 10, 9, 34], [74, 9, 132, 75, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 59, 64, 47], [], [], []]
 b := ![[], [91, 87, 26, 132, 47], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 5
  hpos := by decide
  P := [129, 106, 82, 72, 117, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10552034957337, -28593668105449, -36570198733154, -19982279150817, -8383621514864]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-67210413741, -182125274557, -232931202122, -127275663381, -53398863152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 95388992557 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-541, -884, -623, -167, 150]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-541, -884, -623, -167, 150]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![53, 122, 132, 1, 0], ![88, 43, 70, 0, 1]] where
  M :=![![![-541, -884, -623, -167, 150], ![900, 1709, 1199, 427, -334], ![-2004, -4110, -2874, -1139, 854], ![5124, 10806, 7561, 3104, -2278], ![-5832, -12468, -8693, -3623, 2677]]]
  hmulB := by decide  
  f := ![![![329, 728, 381, -1, -50]], ![![-300, -421, -23, 31, -2]], ![![-12, -330, -420, -37, 62]], ![![-125, -340, -230, -7, 32]], ![![92, 139, 20, -8, -1]]]
  g := ![![![-30, 80, 67, -167, 150], ![47, -221, -195, 427, -334], ![-103, 602, 538, -1139, 854], ![252, -1656, -1489, 3104, -2278], ![-303, 1929, 1731, -3623, 2677]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [148, 120, 104, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 98, 133], [92, 64, 30], [0, 1]]
 g := ![![[63, 29, 22], [144, 118, 131], [70, 35], [102, 118], [91, 84], [101, 59, 1], []], ![[88, 122, 121, 96], [153, 81, 40, 62], [148, 74], [129, 16], [27, 71], [129, 19, 9, 22], [113, 85]], ![[60, 36, 33, 80], [114, 27, 136, 129], [108, 54], [17, 10], [110, 51], [46, 111, 52, 99], [53, 85]]]
 h' := ![![[130, 98, 133], [41, 110, 115], [61, 66, 72], [106, 29, 19], [83, 131, 97], [48, 12, 35], [0, 0, 1], [0, 1]], ![[92, 64, 30], [25, 80, 148], [123, 24, 20], [48, 82, 20], [118, 0, 159], [107, 81, 87], [13, 155, 64], [130, 98, 133]], ![[0, 1], [124, 136, 63], [80, 73, 71], [47, 52, 124], [66, 32, 70], [32, 70, 41], [131, 8, 98], [92, 64, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 36], []]
 b := ![[], [152, 44, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [148, 120, 104, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1020125, -2224224, -847426, -753735, 730053]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-155318, 357909, 291668, -753735, 730053]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![329, 728, 381, -1, -50]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![329, 728, 381, -1, -50]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![9, 31, 1, 0, 0], ![47, 26, 0, 1, 0], ![123, 94, 0, 0, 1]] where
  M :=![![![329, 728, 381, -1, -50], ![-300, -421, -23, 31, -2], ![-12, -330, -420, -37, 62], ![372, 918, 563, 14, -74], ![-216, -204, 121, 41, -17]]]
  hmulB := by decide  
  f := ![![![-541, -884, -623, -167, 150]], ![![900, 1709, 1199, 427, -334]], ![![129, 251, 176, 65, -50]], ![![19, 84, 58, 39, -24]], ![![75, 242, 168, 98, -63]]]
  g := ![![![19, -39, 381, -1, -50], ![-8, -2, -23, 31, -2], ![-13, 48, -420, -37, 62], ![23, -61, 563, 14, -74], ![-7, -21, 121, 41, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [66, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 162], [0, 1]]
 g := ![![[144, 49], [121, 88], [140], [152], [61], [101, 55], [1]], ![[139, 114], [122, 75], [140], [152], [61], [122, 108], [1]]]
 h' := ![![[113, 162], [1, 156], [142, 67], [55, 125], [12, 57], [17, 77], [97, 113], [0, 1]], ![[0, 1], [25, 7], [52, 96], [162, 38], [96, 106], [79, 86], [152, 50], [113, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [157, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [66, 50, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![909, 2016, 2777, 1490, 568]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1006, -1081, 2777, 1490, 568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-541, -884, -623, -167, 150]] ![![329, 728, 381, -1, -50]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3385, 4206, 3002, 216, -466]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![3385, 4206, 3002, 216, -466]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![79, 60, 32, 1, 0], ![72, 165, 103, 0, 1]] where
  M :=![![![3385, 4206, 3002, 216, -466], ![-2796, -3605, -2568, -260, 432], ![2592, 3684, 2615, 456, -520], ![-3120, -5208, -3660, -1025, 912], ![1440, 3438, 2416, 1134, -765]]]
  hmulB := by decide  
  f := ![![![-697, -1458, -698, 12, 90]], ![![540, 653, -96, -68, 24]], ![![144, 900, 945, 72, -136]], ![![-113, -294, -190, -5, 26]], ![![324, 573, 185, -18, -21]]]
  g := ![![![119, 408, 264, 216, -466], ![-80, -355, -232, -260, 432], ![24, 372, 249, 456, -520], ![73, -564, -388, -1025, 912], ![-198, 369, 269, 1134, -765]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [87, 53, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 19, 139], [56, 147, 28], [0, 1]]
 g := ![![[38, 29, 108], [78, 7, 11], [60, 87, 12], [116, 162], [46, 128], [31, 90, 1], []], ![[109, 92, 135, 136], [101, 77, 70, 156], [124, 9, 141, 60], [15, 42], [150, 116], [38, 20, 140, 156], [24, 116]], ![[64, 158, 65, 76], [22, 63, 80, 157], [74, 25, 130, 154], [49, 87], [155, 98], [131, 70, 83, 88], [135, 116]]]
 h' := ![![[34, 19, 139], [61, 112, 38], [124, 124, 126], [128, 130, 124], [130, 158, 117], [142, 46, 104], [0, 0, 1], [0, 1]], ![[56, 147, 28], [16, 152, 112], [134, 146, 20], [35, 30, 59], [165, 91, 83], [135, 142, 139], [70, 115, 147], [34, 19, 139]], ![[0, 1], [165, 70, 17], [152, 64, 21], [8, 7, 151], [51, 85, 134], [164, 146, 91], [75, 52, 19], [56, 147, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 5], []]
 b := ![[], [1, 54, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [87, 53, 77, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11935226, 32591889, 42226158, 23150883, 9993155]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15188573, -17995998, -10346689, 23150883, 9993155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![697, 1458, 698, -12, -90]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![697, 1458, 698, -12, -90]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![114, 135, 1, 0, 0], ![141, 92, 0, 1, 0], ![43, 139, 0, 0, 1]] where
  M :=![![![697, 1458, 698, -12, -90], ![-540, -653, 96, 68, -24], ![-144, -900, -945, -72, 136], ![816, 1896, 1068, 7, -144], ![-360, -222, 344, 66, -61]]]
  hmulB := by decide  
  f := ![![![-3385, -4206, -3002, -216, 466]], ![![2796, 3605, 2568, 260, -432]], ![![-66, 21, 11, 60, -28]], ![![-1299, -1534, -1098, -33, 150]], ![![1447, 1897, 1350, 154, -235]]]
  g := ![![![-439, -474, 698, -12, -90], ![-120, -99, 96, 68, -24], ![670, 685, -945, -72, 136], ![-693, -736, 1068, 7, -144], ![-277, -265, 344, 66, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [164, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 166], [0, 1]]
 g := ![![[91, 12], [35, 76], [62, 49], [87], [126], [107, 47], [1]], ![[27, 155], [75, 91], [79, 118], [87], [126], [79, 120], [1]]]
 h' := ![![[106, 166], [105, 124], [19, 57], [39, 7], [46, 134], [154, 136], [3, 106], [0, 1]], ![[0, 1], [56, 43], [49, 110], [113, 160], [55, 33], [41, 31], [50, 61], [106, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [132, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [164, 61, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4178, 13824, 23447, 14011, 8702]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-30051, -33833, 23447, 14011, 8702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![3385, 4206, 3002, 216, -466]] ![![697, 1458, 698, -12, -90]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3697, 4405, 3151, 118, -442]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![3697, 4405, 3151, 118, -442]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![66, 149, 62, 1, 0], ![30, 85, 56, 0, 1]] where
  M :=![![![3697, 4405, 3151, 118, -442], ![-2652, -2933, -2107, 57, 236], ![1416, 888, 664, -455, 114], ![684, 3126, 2143, 1462, -910], ![-3438, -6927, -4863, -1886, 1405]]]
  hmulB := by decide  
  f := ![![![185, -203, -603, -76, 92]], ![![552, 1565, 1101, 41, -152]], ![![-912, -1728, -674, 37, 82]], ![![222, 653, 474, 19, -66]], ![![12, 184, 224, 19, -33]]]
  g := ![![![53, 141, 119, 118, -442], ![-78, -182, -109, 57, 236], ![162, 341, 130, -455, 114], ![-396, -794, -217, 1462, -910], ![456, 894, 193, -1886, 1405]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [149, 86, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 111, 82], [167, 61, 91], [0, 1]]
 g := ![![[132, 151, 78], [15, 138], [106, 94, 22], [81, 26, 140], [58, 22], [142, 48, 1], []], ![[29, 96, 106, 76], [110, 25], [3, 106, 2, 3], [33, 130, 166, 141], [154, 100], [163, 38, 140, 123], [146, 150]], ![[14, 117, 53, 75], [133, 116], [7, 32, 84, 82], [131, 33, 22, 26], [69, 31], [121, 33, 62, 171], [137, 150]]]
 h' := ![![[54, 111, 82], [20, 35, 50], [122, 11, 22], [41, 81, 56], [117, 1, 113], [121, 12, 117], [0, 0, 1], [0, 1]], ![[167, 61, 91], [92, 131, 38], [96, 109, 168], [116, 74, 24], [69, 14, 55], [51, 42, 163], [19, 91, 61], [54, 111, 82]], ![[0, 1], [103, 7, 85], [5, 53, 156], [70, 18, 93], [140, 158, 5], [53, 119, 66], [37, 82, 111], [167, 61, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 149], []]
 b := ![[], [83, 63, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [149, 86, 125, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3840883, -8051808, -5165168, -2005112, 2120296]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![375073, 638640, 2400, -2005112, 2120296]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-235, -278, -200, -12, 30]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-235, -278, -200, -12, 30]] 
 ![![173, 0, 0, 0, 0], ![135, 1, 0, 0, 0], ![113, 0, 1, 0, 0], ![142, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![-235, -278, -200, -12, 30], ![180, 215, 160, 10, -24], ![-144, -180, -135, -8, 20], ![120, 156, 112, 5, -16], ![24, 30, 28, 4, -5]]]
  hmulB := by decide  
  f := ![![![49, 142, 160, 72, 22]], ![![39, 113, 128, 58, 18]], ![![37, 106, 121, 56, 18]], ![![62, 176, 208, 101, 36]], ![![89, 248, 300, 152, 57]]]
  g := ![![![333, -278, -200, -12, 30], ![-261, 215, 160, 10, -24], ![219, -180, -135, -8, 20], ![-186, 156, 112, 5, -16], ![-41, 30, 28, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 74, 53, 3, -8]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![61, 74, 53, 3, -8]] 
 ![![173, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![134, 0, 0, 0, 1]] where
  M :=![![![61, 74, 53, 3, -8], ![-48, -59, -43, -3, 6], ![36, 42, 28, -1, -6], ![-36, -54, -49, -14, -2], ![-24, -54, -63, -31, -11]]]
  hmulB := by decide  
  f := ![![![17, -310, -441, -49, 68]], ![![17, -261, -376, -42, 58]], ![![8, -214, -298, -33, 46]], ![![4, -26, -41, -4, 6]], ![![14, -238, -341, -39, 53]]]
  g := ![![![-93, 74, 53, 3, -8], ![75, -59, -43, -3, 6], ![-50, 42, 28, -1, -6], ![82, -54, -49, -14, -2], ![100, -54, -63, -31, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![3697, 4405, 3151, 118, -442]] ![![-235, -278, -200, -12, 30]]
  ![![-526087, -642723, -459145, -26700, 68532]] where
 M := ![![![-526087, -642723, -459145, -26700, 68532]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![-526087, -642723, -459145, -26700, 68532]] ![![61, 74, 53, 3, -8]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-18453391, -22552799, -16110798, -941639, 2406776]]]
 hmul := by decide  
 g := ![![![![-106667, -130363, -93126, -5443, 13912]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-221, -418, -271, -155, 102]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-221, -418, -271, -155, 102]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![147, 31, 143, 95, 1]] where
  M :=![![![-221, -418, -271, -155, 102], ![612, 1309, 957, 443, -310], ![-1860, -4038, -2898, -1213, 886], ![5316, 11430, 8039, 3304, -2426], ![-6348, -13518, -9379, -3865, 2861]]]
  hmulB := by decide  
  f := ![![![137, 170, 121, 7, -18]], ![![-108, -133, -93, -5, 14]], ![![84, 102, 72, 5, -10]], ![![-60, -66, -43, 2, 10]], ![![129, 163, 118, 10, -15]]]
  g := ![![![-85, -20, -83, -55, 102], ![258, 61, 253, 167, -310], ![-738, -176, -724, -477, 886], ![2022, 484, 1983, 1306, -2426], ![-2385, -571, -2338, -1540, 2861]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [147, 68, 121, 126, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 90, 54, 77], [53, 118, 114, 35], [3, 149, 11, 67], [0, 1]]
 g := ![![[95, 120, 38, 77], [140, 32, 97, 76], [101, 70, 22], [35, 149, 108], [92, 60, 76, 9], [53, 1], []], ![[85, 25, 149, 91, 167, 149], [67, 128, 63, 177, 9, 151], [116, 18, 95], [116, 3, 110], [104, 153, 146, 171, 117, 85], [10, 74, 9, 163, 9, 155], [66, 174, 22]], ![[64, 34, 141, 19, 109, 41], [164, 29, 123, 162, 72, 115], [52, 164, 108], [112, 150, 5], [162, 165, 20, 31, 123, 38], [160, 157, 27, 98, 26, 21], [13, 52, 151]], ![[65, 176, 66, 104, 176, 116], [129, 7, 125, 67, 121, 17], [154, 21, 89], [14, 34, 14], [148, 157, 41, 113, 153, 83], [31, 13, 38, 103, 160, 108], [159, 68, 14]]]
 h' := ![![[176, 90, 54, 77], [5, 113, 103, 16], [14, 160, 80, 75], [2, 123, 128, 102], [80, 25, 36, 114], [85, 8, 142, 3], [0, 0, 1], [0, 1]], ![[53, 118, 114, 35], [129, 125, 131, 49], [95, 138, 121, 9], [121, 87, 107, 51], [40, 141, 124, 162], [102, 122, 152, 71], [152, 3, 118, 51], [176, 90, 54, 77]], ![[3, 149, 11, 67], [21, 49, 162, 158], [163, 45, 157, 59], [17, 51, 150, 65], [27, 10, 166, 149], [48, 149, 43, 159], [3, 42, 134, 65], [53, 118, 114, 35]], ![[0, 1], [58, 71, 141, 135], [99, 15, 0, 36], [177, 97, 152, 140], [83, 3, 32, 112], [113, 79, 21, 125], [85, 134, 105, 63], [3, 149, 11, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [60, 152, 57], []]
 b := ![[], [], [43, 109, 11, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [147, 68, 121, 126, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14868691939, 40307901196, 51590571946, 28195763058, 11850935458]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9649267153, -1827212838, -9179291612, -6132084388, 11850935458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, -170, -121, -7, 18]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-137, -170, -121, -7, 18]] 
 ![![179, 0, 0, 0, 0], ![168, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![-137, -170, -121, -7, 18], ![108, 133, 93, 5, -14], ![-84, -102, -72, -5, 10], ![60, 66, 43, -2, -10], ![12, 6, -7, -11, -7]]]
  hmulB := by decide  
  f := ![![![221, 418, 271, 155, -102]], ![![204, 385, 249, 143, -94]], ![![82, 158, 104, 57, -38]], ![![95, 172, 108, 69, -44]], ![![133, 260, 172, 90, -61]]]
  g := ![![![194, -170, -121, -7, 18], ![-151, 133, 93, 5, -14], ![117, -102, -72, -5, 10], ![-70, 66, 43, -2, -10], ![6, 6, -7, -11, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-221, -418, -271, -155, 102]] ![![-137, -170, -121, -7, 18]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 101, 84, 9, -14]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![85, 101, 84, 9, -14]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![128, 179, 18, 1, 0], ![115, 82, 109, 0, 1]] where
  M :=![![![85, 101, 84, 9, -14], ![-84, -125, -100, -14, 18], ![108, 186, 131, 26, -28], ![-168, -312, -208, -65, 52], ![102, 213, 136, 65, -51]]]
  hmulB := by decide  
  f := ![![![13, 13, 0, -1, 0]], ![![0, 13, 12, 0, -2]], ![![-12, -30, -17, -2, 0]], ![![8, 19, 10, -1, -2]], ![![1, -4, -5, -2, -1]]]
  g := ![![![3, -2, 8, 9, -14], ![-2, 5, -10, -14, 18], ![0, -12, 15, 26, -28], ![12, 39, -26, -65, 52], ![-13, -40, 25, 65, -51]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [24, 169, 178, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 53, 37], [100, 127, 144], [0, 1]]
 g := ![![[87, 48, 177], [16, 152], [84, 18, 172], [145, 100], [84, 73, 14], [21, 3, 1], []], ![[169, 178, 124, 64], [174, 65], [13, 4, 60, 82], [34, 3], [155, 36, 27, 132], [177, 54, 78, 16], [65, 102]], ![[115, 30, 0, 62], [128, 101], [22, 11, 107, 60], [144, 39], [32, 35, 123, 4], [88, 99, 115, 142], [139, 102]]]
 h' := ![![[84, 53, 37], [60, 77, 38], [156, 85, 40], [41, 129, 57], [156, 53, 171], [39, 180, 75], [0, 0, 1], [0, 1]], ![[100, 127, 144], [167, 128, 73], [162, 1, 80], [159, 93, 66], [147, 134, 148], [18, 9, 76], [66, 177, 127], [84, 53, 37]], ![[0, 1], [171, 157, 70], [96, 95, 61], [19, 140, 58], [175, 175, 43], [179, 173, 30], [148, 4, 53], [100, 127, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 31], []]
 b := ![[], [114, 134, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [24, 169, 178, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![528230, 1553643, 2258381, 1275520, 694022]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1340060, -1567261, -532317, 1275520, 694022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, 95, 68, -1, -8]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![85, 95, 68, -1, -8]] 
 ![![181, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![132, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![85, 95, 68, -1, -8], ![-48, -35, -26, 12, -2], ![-12, -78, -53, -40, 24], ![144, 348, 242, 115, -80], ![-234, -489, -342, -139, 103]]]
  hmulB := by decide  
  f := ![![![-443, -1001, -532, 5, 74]], ![![-93, -212, -114, 1, 16]], ![![-264, -594, -313, 4, 44]], ![![-324, -732, -386, 7, 56]], ![![-207, -468, -242, 10, 39]]]
  g := ![![![-56, 95, 68, -1, -8], ![15, -35, -26, 12, -2], ![66, -78, -53, -40, 24], ![-264, 348, 242, 115, -80], ![360, -489, -342, -139, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, -111, -49, 2, 6]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-55, -111, -49, 2, 6]] 
 ![![181, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![151, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-55, -111, -49, 2, 6], ![36, 35, -19, -7, 4], ![24, 96, 88, 9, -14], ![-84, -186, -105, -10, 18], ![42, 45, -7, 6, -3]]]
  hmulB := by decide  
  f := ![![![1721, 2121, 1533, 112, -212]], ![![1172, 1445, 1045, 77, -144]], ![![93, 117, 87, 9, -10]], ![![1439, 1785, 1302, 108, -170]], ![![1310, 1641, 1213, 118, -145]]]
  g := ![![![72, -111, -49, 2, 6], ![-20, 35, -19, -7, 4], ![-67, 96, 88, 9, -14], ![127, -186, -105, -10, 18], ![-33, 45, -7, 6, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![85, 101, 84, 9, -14]] ![![85, 95, 68, -1, -8]]
  ![![5941, 7966, 5668, 748, -1028]] where
 M := ![![![5941, 7966, 5668, 748, -1028]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![5941, 7966, 5668, 748, -1028]] ![![-55, -111, -49, 2, 6]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-9955, -21901, -15023, -6516, 4706]]]
 hmul := by decide  
 g := ![![![![-55, -121, -83, -36, 26]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -17, -52, -17, 16]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![11, -17, -52, -17, 16]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![0, 0, 0, 191, 0], ![132, 178, 140, 178, 1]] where
  M :=![![![11, -17, -52, -17, 16], ![96, 251, 206, 60, -34], ![-204, -414, -199, -32, 120], ![720, 1596, 1354, 641, -64], ![-90, 87, 738, 469, 581]]]
  hmulB := by decide  
  f := ![![![-263, -323, -228, -13, 34]], ![![204, 247, 174, 10, -26]], ![![-156, -186, -133, -8, 20]], ![![120, 144, 106, 7, -16]], ![![6, 5, 6, 1, -1]]]
  g := ![![![-11, -15, -12, -15, 16], ![24, 33, 26, 32, -34], ![-84, -114, -89, -112, 120], ![48, 68, 54, 63, -64], ![-402, -541, -422, -539, 581]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 4 2 7 [190, 38, 79, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 101, 182, 159], [94, 8, 112, 112], [113, 81, 88, 111], [0, 1]]
 g := ![![[136, 43, 153, 43], [159, 70, 74, 8], [120, 82, 155, 48], [148, 188, 167, 156], [86, 135, 101, 138], [152, 1], []], ![[22, 106, 38, 3, 90, 53], [92, 66, 59, 38, 53, 161], [179, 104, 96, 132, 135, 137], [149, 146, 33, 127, 160, 14], [53, 62, 73, 57, 5, 127], [20, 88, 168, 16, 59, 124], [172, 177, 69]], ![[12, 151, 91, 122, 126, 93], [138, 184, 150, 115, 170, 142], [140, 130, 137, 186, 131, 179], [81, 27, 3, 160, 180, 165], [52, 159, 74, 81, 111, 95], [24, 113, 124, 52, 30, 116], [56, 2, 129]], ![[59, 188, 177, 122, 57, 189], [143, 94, 43, 61, 59, 93], [64, 2, 172, 103, 147, 113], [133, 23, 43, 13, 163, 166], [30, 149, 83, 101, 21, 31], [170, 13, 21, 47, 32, 38], [189, 91, 97]]]
 h' := ![![[136, 101, 182, 159], [159, 24, 46, 132], [120, 45, 67, 77], [148, 50, 117, 96], [86, 107, 91, 27], [152, 146, 178, 105], [0, 0, 1], [0, 1]], ![[94, 8, 112, 112], [126, 165, 46, 183], [96, 186, 93, 107], [43, 14, 62, 173], [104, 148, 14, 38], [40, 84, 91, 134], [141, 103, 114, 163], [136, 101, 182, 159]], ![[113, 81, 88, 111], [92, 82, 21, 126], [106, 174, 48, 38], [155, 81, 155, 176], [90, 152, 161, 34], [169, 3, 127, 9], [106, 142, 132, 133], [94, 8, 112, 112]], ![[0, 1], [83, 111, 78, 132], [18, 168, 174, 160], [118, 46, 48, 128], [182, 166, 116, 92], [67, 149, 177, 134], [161, 137, 135, 86], [113, 81, 88, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [140, 184, 117], []]
 b := ![[], [], [97, 184, 3, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 4
  hpos := by decide
  P := [190, 38, 79, 39, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8797002601, 24161301150, 31596157089, 17373396844, 7690325563]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5268722365, -7040401304, -5471462941, -7075940070, 7690325563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 1330863361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 323, 228, 13, -34]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![263, 323, 228, 13, -34]] 
 ![![191, 0, 0, 0, 0], ![26, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![263, 323, 228, 13, -34], ![-204, -247, -174, -10, 26], ![156, 186, 133, 8, -20], ![-120, -144, -106, -7, 16], ![-30, -33, -22, -1, 3]]]
  hmulB := by decide  
  f := ![![![-11, 17, 52, 17, -16]], ![![-2, 1, 6, 2, -2]], ![![-4, 10, 25, 8, -8]], ![![-4, -8, -6, -3, 0]], ![![-5, 8, 22, 6, -11]]]
  g := ![![![-131, 323, 228, 13, -34], ![100, -247, -174, -10, 26], ![-76, 186, 133, 8, -20], ![60, -144, -106, -7, 16], ![13, -33, -22, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![11, -17, -52, -17, 16]] ![![263, 323, 228, 13, -34]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0, 0, 0]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]] where
  M :=![![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 5 2 7 [29, 12, 182, 6, 26, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 23, 107, 180, 73], [84, 95, 126, 75, 146], [10, 45, 2, 2, 55], [149, 29, 151, 129, 112], [0, 1]]
 g := ![![[169, 127, 63, 110, 184], [28, 67, 166, 128], [126, 146, 187, 36], [63, 67, 14, 69], [84, 91, 175, 175], [167, 1], []], ![[69, 40, 55, 68, 94, 175, 118, 30], [103, 31, 70, 31], [46, 122, 57, 165], [127, 123, 73, 100], [105, 66, 48, 169], [127, 184, 33, 16], [44, 115, 62, 176, 88, 98, 139, 122]], ![[146, 170, 79, 142, 106, 70, 30, 158], [45, 115, 163, 177], [80, 4, 111, 151], [111, 124, 22, 1], [116, 82, 58, 56], [45, 25, 14, 179], [87, 2, 23, 44, 171, 83, 150, 11]], ![[46, 102, 161, 106, 18, 177, 150, 190], [50, 110, 31, 23], [32, 63, 80, 25], [13, 153, 10, 121], [59, 11, 178, 100], [181, 151, 145, 93], [132, 29, 0, 17, 10, 121, 160, 9]], ![[25, 155, 136, 130, 72, 110, 14, 69], [77, 96, 165, 134], [163, 154, 117, 169], [191, 139, 32, 69], [94, 165, 70, 172], [107, 52, 181, 134], [135, 176, 6, 56, 162, 162, 16, 81]]]
 h' := ![![[117, 23, 107, 180, 73], [41, 116, 11, 63, 143], [9, 58, 98, 129, 30], [31, 187, 29, 19, 187], [11, 61, 75, 62, 164], [175, 90, 88, 167, 91], [0, 0, 0, 1], [0, 1]], ![[84, 95, 126, 75, 146], [26, 10, 176, 72, 137], [73, 172, 147, 9, 113], [153, 77, 71, 96, 92], [180, 113, 107, 69, 183], [152, 47, 119, 37, 180], [174, 189, 159, 32, 4], [117, 23, 107, 180, 73]], ![[10, 45, 2, 2, 55], [39, 151, 175, 106, 92], [147, 187, 120, 68, 62], [94, 172, 50, 74, 99], [15, 170, 130, 169, 192], [22, 72, 22, 72, 40], [180, 149, 162, 15, 117], [84, 95, 126, 75, 146]], ![[149, 29, 151, 129, 112], [69, 35, 78, 77, 139], [174, 6, 21, 52, 71], [152, 93, 72, 120, 188], [170, 24, 14, 161, 11], [12, 84, 69, 81, 10], [67, 74, 115, 45, 155], [10, 45, 2, 2, 55]], ![[0, 1], [71, 74, 139, 68, 68], [48, 156, 0, 128, 110], [170, 50, 164, 77, 13], [43, 18, 60, 118, 29], [35, 93, 88, 29, 65], [67, 167, 143, 100, 110], [149, 29, 151, 129, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 161, 104, 33], [], [], []]
 b := ![[], [129, 154, 28, 80, 63], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 5
  hpos := by decide
  P := [29, 12, 182, 6, 26, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4669651436266, 12657029975828, 16194969900599, 8850190885339, 3717232625889]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24195085162, 65580466196, 83911761143, 45855911323, 19260272673]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 267785184193 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀

instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -9, 60, 11, -10]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-7, -9, 60, 11, -10]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![114, 179, 182, 1, 0], ![67, 119, 76, 0, 1]] where
  M :=![![![-7, -9, 60, 11, -10], ![-60, -157, -148, -10, 22], ![132, 270, 163, 6, -20], ![-120, -168, -24, 23, 12], ![-30, -105, -64, 27, 33]]]
  hmulB := by decide  
  f := ![![![1, -9, -8, -7, 4]], ![![24, 61, 44, 20, -14]], ![![-84, -186, -129, -54, 40]], ![![-54, -119, -82, -35, 26]], ![![-19, -41, -28, -12, 9]]]
  g := ![![![-3, -4, -6, 11, -10], ![-2, -5, 0, -10, 22], ![4, 8, 3, 6, -20], ![-18, -29, -26, 23, 12], ![-27, -45, -38, 27, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [172, 22, 194, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [177, 59, 189], [23, 137, 8], [0, 1]]
 g := ![![[78, 12, 9], [131, 161], [107, 53, 40], [159, 181], [148, 63], [92, 9], [1]], ![[106, 39, 21, 80], [158, 96], [72, 56, 60, 149], [73, 93], [174, 34], [6, 16], [140, 142, 139, 79]], ![[62, 127, 42, 192], [29, 104], [74, 115, 178, 140], [74, 144], [71, 154], [135, 1], [114, 153, 63, 118]]]
 h' := ![![[177, 59, 189], [117, 101, 194], [114, 49, 113], [68, 188, 146], [69, 81, 56], [167, 56, 121], [25, 175, 3], [0, 1]], ![[23, 137, 8], [107, 174, 160], [57, 87, 117], [140, 18, 177], [132, 16, 129], [126, 101, 172], [31, 153, 193], [177, 59, 189]], ![[0, 1], [141, 119, 40], [106, 61, 164], [178, 188, 71], [62, 100, 12], [81, 40, 101], [45, 66, 1], [23, 137, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 104], []]
 b := ![[], [136, 84, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [172, 22, 194, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18034, -45408, -29979, -8845, 11261]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1197, 1004, 3675, -8845, 11261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -28, -20, -4, 4]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-19, -28, -20, -4, 4]] 
 ![![197, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-19, -28, -20, -4, 4], ![24, 41, 28, 8, -8], ![-48, -96, -71, -28, 16], ![96, 192, 116, 41, -56], ![-144, -324, -268, -124, 33]]]
  hmulB := by decide  
  f := ![![![-1895, -5428, -3900, -156, 540]], ![![-705, -2035, -1472, -60, 204]], ![![-856, -2432, -1735, -68, 240]], ![![-950, -2728, -1964, -79, 272]], ![![-216, -636, -468, -20, 65]]]
  g := ![![![21, -28, -20, -4, 4], ![-31, 41, 28, 8, -8], ![80, -96, -71, -28, 16], ![-138, 192, 116, 41, -56], ![300, -324, -268, -124, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 43, 4, -3, 0]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![29, 43, 4, -3, 0]] 
 ![![197, 0, 0, 0, 0], ![137, 1, 0, 0, 0], ![143, 0, 1, 0, 0], ![109, 0, 0, 1, 0], ![145, 0, 0, 0, 1]] where
  M :=![![![29, 43, 4, -3, 0], ![0, 29, 40, 4, -6], ![-36, -90, -57, -2, 8], ![48, 84, 28, -1, -4], ![6, 39, 40, 1, -5]]]
  hmulB := by decide  
  f := ![![![-467, -581, -416, -33, 58]], ![![-323, -402, -288, -23, 40]], ![![-341, -425, -305, -25, 42]], ![![-259, -325, -236, -22, 30]], ![![-349, -442, -324, -34, 39]]]
  g := ![![![-31, 43, 4, -3, 0], ![-47, 29, 40, 4, -6], ![99, -90, -57, -2, 8], ![-75, 84, 28, -1, -4], ![-53, 39, 40, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-7, -9, 60, 11, -10]] ![![-19, -28, -20, -4, 4]]
  ![![-467, -581, -416, -33, 58]] where
 M := ![![![-467, -581, -416, -33, 58]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-467, -581, -416, -33, 58]] ![![29, 43, 4, -3, 0]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB441I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB441I4 : PrimesBelowBoundCertificateInterval O 151 197 441 where
  m := 9
  g := ![1, 2, 2, 3, 2, 3, 2, 1, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB441I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
    · exact ![I197N0, I197N1, I197N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![95388992557]
    · exact ![4330747, 26569]
    · exact ![4657463, 27889]
    · exact ![5177717, 173, 173]
    · exact ![1026625681, 179]
    · exact ![5929741, 181, 181]
    · exact ![1330863361, 191]
    · exact ![267785184193]
    · exact ![7645373, 197, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I173N1, I173N2, I179N1, I181N1, I181N2, I191N1, I197N1, I197N2]
  Il := ![[], [], [], [I173N1, I173N2], [I179N1], [I181N1, I181N2], [I191N1], [], [I197N1, I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
