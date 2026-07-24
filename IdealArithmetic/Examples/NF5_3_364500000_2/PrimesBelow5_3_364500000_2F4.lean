
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1519, 104, 516, -30, -192]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-1519, 104, 516, -30, -192]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![154, 121, 77, 1, 0], ![37, 149, 0, 0, 1]] where
  M :=![![![-1519, 104, 516, -30, -192], ![4608, 1049, -500, -504, -120], ![1440, 2210, 1313, -980, -1008], ![9792, 5416, 1424, -2467, -1900], ![9816, 7376, 2948, -3326, -2911]]]
  hmulB := by decide  
  f := ![![![269, 112, -116, -34, 40]], ![![-960, -355, 452, 88, -136]], ![![1632, 582, -715, -92, 176]], ![![314, 119, -111, -11, 20]], ![![-835, -307, 396, 76, -119]]]
  g := ![![![65, 206, 18, -30, -192], ![552, 509, 244, -504, -120], ![1208, 1726, 489, -980, -1008], ![2930, 3739, 1219, -2467, -1900], ![4011, 5373, 1650, -3326, -2911]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [32, 82, 151, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 90, 47], [115, 66, 110], [0, 1]]
 g := ![![[77, 76, 57], [107, 86], [118, 59, 124], [142, 14, 113], [121, 145, 75], [6, 1], []], ![[123, 0, 86, 1], [14, 156], [118, 85, 60, 122], [107, 17, 124, 25], [134, 81, 87, 86], [75, 117], [48, 11]], ![[92, 119, 41, 25], [24, 64], [130, 75, 18, 19], [77, 14, 111, 37], [153, 12, 90, 106], [0, 93], [142, 11]]]
 h' := ![![[48, 90, 47], [94, 130, 34], [149, 135, 20], [9, 137, 76], [53, 8, 37], [122, 104, 111], [0, 0, 1], [0, 1]], ![[115, 66, 110], [104, 156, 33], [9, 123, 129], [112, 37, 151], [122, 34, 149], [87, 80, 125], [140, 113, 66], [48, 90, 47]], ![[0, 1], [123, 28, 90], [109, 56, 8], [106, 140, 87], [6, 115, 128], [75, 130, 78], [46, 44, 90], [115, 66, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 55], []]
 b := ![[], [17, 99, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [32, 82, 151, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8863784, 5129477, 1316278, -2276598, -1744120]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2700588, 3442495, 1124932, -2276598, -1744120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, 112, -116, -34, 40]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![269, 112, -116, -34, 40]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![141, 80, 1, 0, 0], ![24, 108, 0, 1, 0], ![71, 44, 0, 0, 1]] where
  M :=![![![269, 112, -116, -34, 40], ![-960, -355, 452, 88, -136], ![1632, 582, -715, -92, 176], ![-1632, -424, 800, -55, -116], ![1992, 552, -884, 78, 101]]]
  hmulB := by decide  
  f := ![![![-1519, 104, 516, -30, -192]], ![![4608, 1049, -500, -504, -120]], ![![993, 642, 217, -290, -240]], ![![3000, 772, -256, -367, -124]], ![![667, 388, 112, -176, -139]]]
  g := ![![![93, 72, -116, -34, 40], ![-364, -255, 452, 88, -136], ![587, 382, -715, -92, 176], ![-668, -340, 800, -55, -116], ![749, 372, -884, 78, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [11, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 156], [0, 1]]
 g := ![![[87, 100], [46], [152, 113], [50, 33], [149, 76], [68], [1]], ![[0, 57], [46], [27, 44], [26, 124], [108, 81], [68], [1]]]
 h' := ![![[142, 156], [7, 147], [55, 49], [78, 37], [88, 70], [1, 95], [146, 142], [0, 1]], ![[0, 1], [0, 10], [105, 108], [151, 120], [137, 87], [146, 62], [57, 15], [142, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [19, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [11, 15, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124805, 49744, -178844, 11953, 138064]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![97149, 44532, -178844, 11953, 138064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-1519, 104, 516, -30, -192]] ![![269, 112, -116, -34, 40]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [141, 152, 92, 52, 29, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 5, 48, 46, 92], [129, 79, 87, 134, 107], [3, 32, 37, 142, 79], [41, 46, 154, 4, 48], [0, 1]]
 g := ![![[139, 128, 62, 37, 100], [78, 75, 76, 118, 4], [86, 16, 46, 121], [142, 23, 103, 34], [67, 96, 143, 26], [1], []], ![[88, 87, 51, 108, 69, 85, 71, 63], [130, 150, 84, 39, 158, 68, 22, 94], [162, 134, 159, 83], [27, 74, 118, 152], [110, 14, 137, 85], [128, 34, 143, 141, 116, 53, 95, 114], [15, 35, 10, 151]], ![[62, 161, 156, 46, 34, 44, 156, 159], [99, 132, 74, 87, 80, 33, 92, 19], [112, 20, 128, 14], [87, 81, 97, 143], [36, 96, 40, 4], [127, 68, 61, 56, 33, 131, 39, 63], [138, 48, 161, 39]], ![[102, 57, 88, 65, 44, 62, 155, 12], [81, 75, 4, 67, 88, 93, 73, 116], [43, 34, 30, 140], [74, 129, 150, 144], [128, 141, 95, 151], [136, 43, 67, 44, 50, 4, 112, 141], [146, 64, 46, 47]], ![[122, 132, 15, 127, 150, 8, 16, 66], [145, 82, 58, 113, 37, 3, 114, 13], [82, 39, 74, 21], [133, 5, 57, 35], [10, 25, 110, 84], [129, 157, 22, 4, 116, 4, 139, 17], [25, 158, 72, 22]]]
 h' := ![![[124, 5, 48, 46, 92], [86, 104, 151, 8, 153], [82, 103, 20, 140, 2], [31, 78, 79, 6, 11], [2, 73, 142, 24, 94], [22, 11, 71, 111, 134], [0, 0, 1], [0, 1]], ![[129, 79, 87, 134, 107], [36, 13, 99, 6, 150], [112, 97, 23, 66, 23], [121, 158, 103, 91, 75], [159, 119, 80, 109, 106], [64, 26, 14, 49, 133], [58, 56, 70, 73, 105], [124, 5, 48, 46, 92]], ![[3, 32, 37, 142, 79], [8, 17, 99, 82, 19], [88, 36, 86, 57, 114], [118, 87, 102, 20, 103], [117, 43, 57, 137, 119], [125, 26, 108, 39, 2], [117, 136, 12, 72, 95], [129, 79, 87, 134, 107]], ![[41, 46, 154, 4, 48], [61, 119, 140, 116, 16], [137, 10, 18, 121, 128], [13, 60, 100, 101, 38], [34, 91, 83, 105, 151], [57, 17, 91, 19, 92], [124, 109, 125, 82, 143], [3, 32, 37, 142, 79]], ![[0, 1], [48, 73, 0, 114, 151], [132, 80, 16, 105, 59], [152, 106, 105, 108, 99], [46, 0, 127, 114, 19], [106, 83, 42, 108, 128], [112, 25, 118, 99, 146], [41, 46, 154, 4, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 38, 40, 117], [], [], []]
 b := ![[], [77, 142, 113, 90, 82], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [141, 152, 92, 52, 29, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![344209559507, 200980124211, 58275296428, -91747102091, -72553824544]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2111715089, 1233006897, 357517156, -562865657, -445115488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 115063617043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2567, -968, 1166, 235, -348]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-2567, -968, 1166, 235, -348]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![64, 158, 140, 1, 0], ![29, 97, 48, 0, 1]] where
  M :=![![![-2567, -968, 1166, 235, -348], ![8352, 2897, -3798, -452, 940], ![-11280, -3345, 5229, -38, -904], ![6672, 460, -3216, 1839, -546], ![-6540, 164, 3278, -2493, 917]]]
  hmulB := by decide  
  f := ![![![935, 658, 246, -297, -254]], ![![6096, 3381, 894, -1540, -1188]], ![![14256, 8489, 2545, -3858, -3080]], ![![18280, 10686, 3108, -4859, -3846]], ![![8081, 4683, 1342, -2130, -1679]]]
  g := ![![![-45, -26, -90, 235, -348], ![60, -101, 86, -452, 940], ![104, 541, 323, -38, -904], ![-570, -1420, -1404, 1839, -546], ![757, 1827, 1846, -2493, 917]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [163, 26, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 10, 154], [8, 156, 13], [0, 1]]
 g := ![![[89, 121, 47], [68, 162, 133], [84, 121, 62], [159, 87], [52, 93], [39, 30, 1], []], ![[138, 62, 68, 130], [1, 19, 34, 56], [124, 126, 98, 66], [8, 57], [12, 93], [123, 155, 49, 97], [134, 2]], ![[165, 24, 42, 138], [106, 61, 165, 15], [93, 80, 14, 13], [104, 33], [], [130, 122, 109, 131], [108, 2]]]
 h' := ![![[22, 10, 154], [105, 53, 106], [2, 19, 119], [160, 48, 88], [162, 151, 134], [156, 108, 60], [0, 0, 1], [0, 1]], ![[8, 156, 13], [6, 22, 149], [57, 127, 114], [128, 11, 78], [51, 162, 70], [105, 115, 107], [18, 137, 156], [22, 10, 154]], ![[0, 1], [166, 92, 79], [60, 21, 101], [104, 108, 1], [32, 21, 130], [52, 111], [162, 30, 10], [8, 156, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 64], []]
 b := ![[], [135, 85, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [163, 26, 137, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-153708645, -86960155, -23029292, 42847814, 33116312]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23091867, -60294593, -45576684, 42847814, 33116312]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![935, 658, 246, -297, -254]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![935, 658, 246, -297, -254]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![126, 27, 1, 0, 0], ![105, 86, 0, 1, 0], ![156, 90, 0, 0, 1]] where
  M :=![![![935, 658, 246, -297, -254], ![6096, 3381, 894, -1540, -1188], ![14256, 8489, 2545, -3858, -3080], ![33912, 19792, 5740, -9005, -7122], ![46812, 27550, 8102, -12533, -9951]]]
  hmulB := by decide  
  f := ![![![-2567, -968, 1166, 235, -348]], ![![8352, 2897, -3798, -452, 940]], ![![-654, -282, 297, 104, -116]], ![![2727, 886, -1242, -74, 262]], ![![2064, 658, -938, -39, 187]]]
  g := ![![![244, 254, 246, -297, -254], ![1440, 1309, 894, -1540, -1188], ![3468, 3286, 2545, -3858, -3080], ![8187, 7666, 5740, -9005, -7122], ![11343, 10672, 8102, -12533, -9951]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [79, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 166], [0, 1]]
 g := ![![[155, 9], [166, 58], [137, 1], [2], [147], [32, 77], [1]], ![[3, 158], [40, 109], [83, 166], [2], [147], [49, 90], [1]]]
 h' := ![![[113, 166], [79, 3], [32, 15], [12, 1], [105, 154], [144, 100], [88, 113], [0, 1]], ![[0, 1], [84, 164], [57, 152], [125, 166], [139, 13], [88, 67], [165, 54], [113, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [126, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [79, 54, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12446, -646, -24361, 4034, 12611]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4138, -4939, -24361, 4034, 12611]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-2567, -968, 1166, 235, -348]] ![![935, 658, 246, -297, -254]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1025, 9, 292, 6, -92]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-1025, 9, 292, 6, -92]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![92, 77, 57, 109, 1]] where
  M :=![![![-1025, 9, 292, 6, -92], ![2208, 291, -362, -152, 24], ![-288, 639, 491, -266, -304], ![2544, 1362, 478, -649, -544], ![2016, 2101, 888, -906, -813]]]
  hmulB := by decide  
  f := ![![![83, 65, 30, -10, -12]], ![![288, 225, 102, -36, -40]], ![![480, 379, 181, -58, -72]], ![![720, 556, 242, -89, -96]], ![![788, 613, 275, -97, -109]]]
  g := ![![![43, 41, 32, 58, -92], ![0, -9, -10, -16, 24], ![160, 139, 103, 190, -304], ![304, 250, 182, 339, -544], ![444, 374, 273, 507, -813]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [18, 30, 13, 108, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 146, 128, 61], [158, 35, 88, 38], [70, 164, 130, 74], [0, 1]]
 g := ![![[134, 43, 94, 122], [113, 131, 150], [134, 108, 142, 136], [66, 134, 126, 84], [31, 115, 140], [65, 1], []], ![[82, 122, 58, 159, 102, 162], [117, 55, 164], [68, 106, 75, 62, 167, 20], [59, 89, 167, 86, 28, 12], [150, 70, 157], [18, 38, 102, 18, 146, 71], [81, 57, 88]], ![[118, 17, 17, 76, 94, 169], [156, 69, 157], [13, 157, 163, 8, 106, 89], [24, 153, 33, 57, 109, 14], [8, 104, 77], [122, 6, 17, 55, 39, 55], [135, 35, 60]], ![[77, 129, 9, 152, 61, 18], [82, 148, 124], [39, 79, 41, 134, 98, 101], [103, 32, 1, 119, 48, 50], [62, 106, 149], [114, 149, 23, 118, 129, 93], [14, 116, 113]]]
 h' := ![![[10, 146, 128, 61], [142, 78, 64, 128], [10, 101, 123, 91], [23, 65, 25, 89], [85, 147, 146, 118], [41, 108, 163, 60], [0, 0, 1], [0, 1]], ![[158, 35, 88, 38], [5, 154, 171, 138], [30, 141, 59, 67], [92, 56, 115, 51], [82, 63, 123, 90], [35, 56, 28, 26], [26, 156, 153, 171], [10, 146, 128, 61]], ![[70, 164, 130, 74], [43, 37, 121, 3], [16, 170, 155, 147], [120, 143, 99, 169], [76, 65, 7, 125], [77, 22, 1, 58], [44, 152, 63, 122], [158, 35, 88, 38]], ![[0, 1], [75, 77, 163, 77], [72, 107, 9, 41], [4, 82, 107, 37], [81, 71, 70, 13], [32, 160, 154, 29], [150, 38, 129, 53], [70, 164, 130, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 22, 53], []]
 b := ![[], [], [106, 59, 37, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [18, 30, 13, 108, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-704383326, -934612928, 228906888, 848668700, -542118648]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![284222730, 235887416, 179940288, 346471684, -542118648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -65, -30, 10, 12]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-83, -65, -30, 10, 12]] 
 ![![173, 0, 0, 0, 0], ![83, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![137, 0, 0, 1, 0], ![151, 0, 0, 0, 1]] where
  M :=![![![-83, -65, -30, 10, 12], ![-288, -225, -102, 36, 40], ![-480, -379, -181, 58, 72], ![-720, -556, -242, 89, 96], ![-672, -537, -266, 82, 105]]]
  hmulB := by decide  
  f := ![![![1025, -9, -292, -6, 92]], ![![479, -6, -138, -2, 44]], ![![606, -9, -175, -2, 56]], ![![797, -15, -234, -1, 76]], ![![883, -20, -260, 0, 85]]]
  g := ![![![30, -65, -30, 10, 12], ![103, -225, -102, 36, 40], ![177, -379, -181, 58, 72], ![251, -556, -242, 89, 96], ![254, -537, -266, 82, 105]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-1025, 9, 292, 6, -92]] ![![-83, -65, -30, 10, 12]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3899, -2289, -670, 1042, 826]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-3899, -2289, -670, 1042, 826]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![155, 70, 104, 1, 0], ![174, 50, 86, 0, 1]] where
  M :=![![![-3899, -2289, -670, 1042, 826], ![-19824, -11571, -3358, 5268, 4168], ![-50016, -29247, -8503, 13314, 10536], ![-116520, -68108, -19810, 31007, 24544], ![-162360, -94913, -27586, 43206, 34191]]]
  hmulB := by decide  
  f := ![![![71, 41, 8, -10, -2]], ![![48, 81, 94, 0, -40]], ![![480, 291, 1, -66, 0]], ![![359, 237, 46, -47, -18]], ![![318, 205, 34, -42, -13]]]
  g := ![![![-1727, -651, -1006, 1042, 826], ![-8724, -3289, -5082, 5268, 4168], ![-22050, -8313, -12845, 13314, 10536], ![-51359, -19362, -29918, 31007, 24544], ![-71556, -26977, -41684, 43206, 34191]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [144, 130, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 111, 175], [12, 67, 4], [0, 1]]
 g := ![![[54, 169, 47], [162, 17, 121], [138, 125], [86, 173], [55, 96, 74], [63, 112, 1], []], ![[66, 107, 63, 18], [142, 88, 177, 78], [89, 151], [11, 14], [113, 69, 114, 122], [116, 171, 46, 123], [9, 16]], ![[51, 12, 96, 19], [61, 84, 50, 76], [110, 158], [7, 110], [140, 66, 145, 144], [31, 149, 177, 59], [1, 16]]]
 h' := ![![[100, 111, 175], [121, 147, 88], [57, 174, 11], [113, 60, 150], [135, 175, 129], [57, 26, 49], [0, 0, 1], [0, 1]], ![[12, 67, 4], [154, 42, 117], [73, 118, 41], [1, 69, 144], [42, 142, 67], [90, 42, 136], [112, 110, 67], [100, 111, 175]], ![[0, 1], [95, 169, 153], [176, 66, 127], [117, 50, 64], [87, 41, 162], [11, 111, 173], [0, 69, 111], [12, 67, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 43], []]
 b := ![[], [111, 87, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [144, 130, 67, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13962246, 8169852, 1510666, -3855752, -2236678]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5590982, 2178248, 3323258, -3855752, -2236678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59507, 2548, -15046, -1708, 4116]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![59507, 2548, -15046, -1708, 4116]] 
 ![![179, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![121, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![59507, 2548, -15046, -1708, 4116], ![-98784, -4231, 24976, 2836, -6832], ![81984, 3508, -20731, -2352, 5672], ![-18672, -806, 4716, 539, -1288], ![98112, 4192, -24814, -2812, 6791]]]
  hmulB := by decide  
  f := ![![![-1535, -436, 822, 36, -188]], ![![-112, -31, 64, 4, -16]], ![![-447, -120, 243, 4, -52]], ![![-1069, -314, 574, 39, -140]], ![![-1312, -352, 714, 12, -153]]]
  g := ![![![1867, 2548, -15046, -1708, 4116], ![-3100, -4231, 24976, 2836, -6832], ![2571, 3508, -20731, -2352, 5672], ![-589, -806, 4716, 539, -1288], ![3074, 4192, -24814, -2812, 6791]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![805427, 34506, -203634, -23132, 55696]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![805427, 34506, -203634, -23132, 55696]] 
 ![![179, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![805427, 34506, -203634, -23132, 55696], ![-1336704, -57127, 338060, 38300, -92528], ![1110336, 47882, -280483, -32052, 76600], ![-250848, -9862, 64104, 6767, -17840], ![1330560, 58262, -335426, -38804, 91331]]]
  hmulB := by decide  
  f := ![![![-70271, 92458, 44770, -133996, 72800]], ![![-62366, 63101, 37672, -96556, 51504]], ![![-23347, 95416, 21911, -120856, 68920]], ![![-92671, -26204, 42930, -1925, -6416]], ![![73160, 90506, -26298, -80860, 53339]]]
  g := ![![![125523, 34506, -203634, -23132, 55696], ![-208458, -57127, 338060, 38300, -92528], ![172711, 47882, -280483, -32052, 76600], ![-40043, -9862, 64104, 6767, -17840], ![205994, 58262, -335426, -38804, 91331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-3899, -2289, -670, 1042, 826]] ![![59507, 2548, -15046, -1708, 4116]]
  ![![753791, 22487, -198232, -17346, 57194]] where
 M := ![![![753791, 22487, -198232, -17346, 57194]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![753791, 22487, -198232, -17346, 57194]] ![![805427, 34506, -203634, -23132, 55696]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![437412293005, 18737255853, -110591117846, -12558445606, 30250933054]]]
 hmul := by decide  
 g := ![![![![2443644095, 104677407, -617827474, -70158914, 168999626]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-479, 340, 414, -72, -166]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-479, 340, 414, -72, -166]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![137, 83, 100, 140, 1]] where
  M :=![![![-479, 340, 414, -72, -166], ![3984, 1617, 160, -500, -288], ![3456, 3156, 1541, -992, -1000], ![10008, 6198, 2068, -2209, -1840], ![10776, 7744, 3054, -2892, -2565]]]
  hmulB := by decide  
  f := ![![![-155, -60, 70, 16, -22]], ![![528, 189, -240, -36, 64]], ![![-768, -244, 353, 16, -72]], ![![600, 110, -284, 83, 0]], ![![161, -9, -80, 68, -27]]]
  g := ![![![123, 78, 94, 128, -166], ![240, 141, 160, 220, -288], ![776, 476, 561, 768, -1000], ![1448, 878, 1028, 1411, -1840], ![2001, 1219, 1434, 1968, -2565]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 4 2 7 [27, 142, 44, 22, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [157, 43, 33, 62], [90, 113, 58, 154], [93, 24, 90, 146], [0, 1]]
 g := ![![[21, 125, 15, 64], [114, 99, 116], [126, 65, 54, 142], [13, 126, 145], [0, 90, 76, 111], [159, 1], []], ![[145, 53, 85, 54, 8, 36], [98, 155, 169], [14, 28, 142, 156, 171, 38], [65, 180, 116], [34, 51, 1, 22, 119, 45], [16, 123, 25, 129, 141, 117], [115, 69, 43]], ![[167, 52, 150, 10, 128, 154], [11, 167, 14], [154, 139, 106, 78, 110, 39], [79, 171, 55], [82, 111, 66, 87, 45, 5], [139, 177, 168, 36, 149, 138], [129, 16, 5]], ![[128, 162, 108, 22, 55, 150], [120, 13, 75], [65, 67, 151, 115, 117, 109], [113, 89, 13], [141, 178, 58, 169, 164, 174], [179, 46, 149, 41, 1, 31], [21, 54, 139]]]
 h' := ![![[157, 43, 33, 62], [101, 143, 126, 173], [37, 22, 80, 72], [11, 1, 165, 93], [0, 171, 59, 114], [51, 20, 102, 78], [0, 0, 1], [0, 1]], ![[90, 113, 58, 154], [156, 141, 30, 53], [79, 104, 39, 168], [21, 167, 79, 56], [50, 148, 157, 109], [54, 27, 95, 99], [5, 15, 174, 136], [157, 43, 33, 62]], ![[93, 24, 90, 146], [99, 148, 3, 1], [45, 51, 27, 106], [120, 121, 113, 21], [9, 82, 111, 69], [160, 95, 74, 71], [92, 142, 103, 14], [90, 113, 58, 154]], ![[0, 1], [119, 111, 22, 135], [61, 4, 35, 16], [78, 73, 5, 11], [41, 142, 35, 70], [112, 39, 91, 114], [118, 24, 84, 31], [93, 24, 90, 146]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [118, 176, 132], []]
 b := ![[], [], [35, 176, 27, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 4
  hpos := by decide
  P := [27, 142, 44, 22, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30211688, -18899582, 11119687, 11377810, -7816109]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5749145, 3479765, 4379727, 6108470, -7816109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 1073283121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![155, 60, -70, -16, 22]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![155, 60, -70, -16, 22]] 
 ![![181, 0, 0, 0, 0], ![164, 1, 0, 0, 0], ![127, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![171, 0, 0, 0, 1]] where
  M :=![![![155, 60, -70, -16, 22], ![-528, -189, 240, 36, -64], ![768, 244, -353, -16, 72], ![-600, -110, 284, -83, 0], ![648, 96, -310, 116, -15]]]
  hmulB := by decide  
  f := ![![![479, -340, -414, 72, 166]], ![![412, -317, -376, 68, 152]], ![![317, -256, -299, 56, 122]], ![![-50, -38, -16, 13, 12]], ![![393, -364, -408, 84, 171]]]
  g := ![![![-25, 60, -70, -16, 22], ![60, -189, 240, 36, -64], ![-37, 244, -353, -16, 72], ![-102, -110, 284, -83, 0], ![147, 96, -310, 116, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-479, 340, 414, -72, -166]] ![![155, 60, -70, -16, 22]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-109291, -68450, -22138, 31074, 25368]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-109291, -68450, -22138, 31074, 25368]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![181, 170, 92, 1, 0], ![78, 32, 150, 0, 1]] where
  M :=![![![-109291, -68450, -22138, 31074, 25368], ![-608832, -348329, -97576, 158668, 124296], ![-1491552, -878164, -258405, 399608, 317336], ![-3503616, -2046554, -594312, 931605, 737068], ![-4863768, -2850534, -832426, 1297450, 1028125]]]
  hmulB := by decide  
  f := ![![![11971, 1214, -5782, 2810, -672]], ![![16128, 19201, -5880, -16940, 11240]], ![![-134880, -73636, 58621, 39080, -33880]], ![![-37183, -16298, 16594, 6051, -6572]], ![![-101010, -55294, 43884, 29442, -25475]]]
  g := ![![![-40379, -32266, -35006, 31074, 25368], ![-204308, -163871, -174552, 158668, 124296], ![-516088, -413436, -443051, 399608, 317336], ![-1202175, -963380, -1030692, 931605, 737068], ![-1674848, -1341974, -1436736, 1297450, 1028125]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [184, 60, 151, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 56, 170], [27, 134, 21], [0, 1]]
 g := ![![[111, 126, 180], [149, 20, 96], [59, 132, 24], [139, 24, 23], [80, 135, 9], [12, 40, 1], []], ![[71, 2, 175, 97], [60, 87, 149, 170], [97, 182, 81, 156], [125, 81, 3, 154], [133, 78, 16, 134], [144, 104, 107, 149], [8, 59]], ![[36, 29, 48, 61], [130, 95, 155, 76], [79, 159, 42, 148], [65, 119, 56, 41], [63, 32, 47, 188], [55, 14, 119, 152], [157, 59]]]
 h' := ![![[13, 56, 170], [88, 183, 84], [31, 0, 67], [18, 19, 129], [178, 145, 126], [84, 133, 188], [0, 0, 1], [0, 1]], ![[27, 134, 21], [166, 100, 155], [17, 46, 1], [67, 132, 79], [44, 156, 87], [183, 34, 52], [34, 52, 134], [13, 56, 170]], ![[0, 1], [51, 99, 143], [76, 145, 123], [76, 40, 174], [64, 81, 169], [101, 24, 142], [109, 139, 56], [27, 134, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 62], []]
 b := ![[], [106, 35, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [184, 60, 151, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1684706, -1204932, -1006934, 707584, 794540]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1003830, -769212, -970082, 707584, 794540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11971, -1214, 5782, -2810, 672]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-11971, -1214, 5782, -2810, 672]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![148, 99, 1, 0, 0], ![55, 110, 0, 1, 0], ![147, 110, 0, 0, 1]] where
  M :=![![![-11971, -1214, 5782, -2810, 672], ![-16128, -19201, 5880, 16940, -11240], ![134880, 73636, -58621, -39080, 33880], ![-398496, -177690, 177536, 68429, -72540], ![510744, 224878, -227850, -84322, 90989]]]
  hmulB := by decide  
  f := ![![![109291, 68450, 22138, -31074, -25368]], ![![608832, 348329, 97576, -158668, -124296]], ![![408068, 238185, 69083, -108412, -85744]], ![![400451, 231034, 65682, -105205, -82748]], ![![460215, 268214, 77592, -122088, -96491]]]
  g := ![![![-4251, -1772, 5782, -2810, 672], ![-868, -6431, 5880, 16940, -11240], ![31308, 33765, -58621, -39080, 33880], ![-103529, -90584, 177536, 68429, -72540], ![133481, 115438, -227850, -84322, 90989]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [50, 173, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 190], [0, 1]]
 g := ![![[183, 149], [69, 67], [66, 49], [156, 4], [73, 12], [21, 133], [1]], ![[0, 42], [129, 124], [184, 142], [37, 187], [98, 179], [123, 58], [1]]]
 h' := ![![[18, 190], [179, 128], [138, 81], [31, 184], [170, 189], [96, 48], [141, 18], [0, 1]], ![[0, 1], [0, 63], [68, 110], [96, 7], [134, 2], [5, 143], [83, 173], [18, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154]]
 b := ![[], [71, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [50, 173, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![572, -1039, -8058, 1756, 6506]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![734, -587, -8058, 1756, 6506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-109291, -68450, -22138, 31074, 25368]] ![![-11971, -1214, 5782, -2810, 672]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-447133, -19142, 113058, 12834, -30928]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-447133, -19142, 113058, 12834, -30928]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![66, 164, 113, 1, 0], ![131, 188, 66, 0, 1]] where
  M :=![![![-447133, -19142, 113058, 12834, -30928], ![742272, 31801, -187664, -21308, 51336], ![-616032, -26352, 155781, 17680, -42616], ![140256, 6042, -35432, -4029, 9692], ![-737304, -31538, 186450, 21162, -51005]]]
  hmulB := by decide  
  f := ![![![203, 70, -94, -10, 24]], ![![-576, -175, 256, 4, -40]], ![![480, 64, -259, 96, 8]], ![![-138, -86, 33, 55, -20]], ![![-263, -104, 98, 32, -21]]]
  g := ![![![14287, 19122, 3648, 12834, -30928], ![-23712, -31735, -6052, -21308, 51336], ![19688, 26352, 5029, 17680, -42616], ![-4474, -5986, -1139, -4029, 9692], ![23563, 31538, 6018, 21162, -51005]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [186, 139, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [15, 156, 159], [11, 36, 34], [0, 1]]
 g := ![![[140, 177, 12], [176, 50], [56, 168], [31, 54], [136, 59], [119, 97], [1]], ![[115, 128, 28, 127], [169, 190], [52, 59], [191, 93], [83, 46], [64, 172], [155, 25, 60, 68]], ![[156, 53, 18, 51], [125, 175], [44, 92], [162, 151], [59, 161], [178, 175], [54, 56, 139, 125]]]
 h' := ![![[15, 156, 159], [106, 61, 165], [15, 66, 126], [190, 110, 19], [121, 177, 61], [110, 141, 32], [7, 54, 26], [0, 1]], ![[11, 36, 34], [67, 176, 6], [87, 23, 169], [130, 7, 32], [181, 151, 38], [117, 136, 25], [21, 168, 65], [15, 156, 159]], ![[0, 1], [44, 149, 22], [83, 104, 91], [57, 76, 142], [184, 58, 94], [100, 109, 136], [165, 164, 102], [11, 36, 34]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183, 16], []]
 b := ![[], [34, 19, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [186, 139, 167, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![55210, 22080, -24232, -6668, 8435]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3159, -2436, 894, -6668, 8435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143, 157, 154, -14, -60]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![143, 157, 154, -14, -60]] 
 ![![193, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![143, 157, 154, -14, -60], ![1440, 929, 102, -172, -56], ![672, 907, 989, -122, -344], ![3408, 2136, 290, -301, -216], ![912, 1357, 1446, -262, -445]]]
  hmulB := by decide  
  f := ![![![-14545, -24575, -15016, 10914, 11364]], ![![-5332, -7309, -4178, 3256, 3288]], ![![-17184, -26149, -15489, 11630, 11936]], ![![-6864, -3986, -1146, 1815, 1432]], ![![-14518, -14453, -7124, 6478, 6139]]]
  g := ![![![-173, 157, 154, -14, -60], ![-324, 929, 102, -172, -56], ![-1100, 907, 989, -122, -344], ![-768, 2136, 290, -301, -216], ![-1638, 1357, 1446, -262, -445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 116, 30, -32, -24]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![223, 116, 30, -32, -24]] 
 ![![193, 0, 0, 0, 0], ![108, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![223, 116, 30, -32, -24], ![576, 453, 200, -132, -128], ![1536, 960, 329, -312, -264], ![2880, 1846, 644, -661, -560], ![3840, 2344, 758, -888, -729]]]
  hmulB := by decide  
  f := ![![![24415, 10532, -10914, -3776, 4200]], ![![13140, 5685, -5872, -2052, 2272]], ![![20041, 8588, -8965, -3032, 3408]], ![![10309, 4578, -4594, -1749, 1864]], ![![22934, 9728, -10270, -3352, 3831]]]
  g := ![![![-51, 116, 30, -32, -24], ![-232, 453, 200, -132, -128], ![-407, 960, 329, -312, -264], ![-717, 1846, 644, -661, -560], ![-824, 2344, 758, -888, -729]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-447133, -19142, 113058, 12834, -30928]] ![![143, 157, 154, -14, -60]]
  ![![2413, 4935, 3368, -688, -1204]] where
 M := ![![![2413, 4935, 3368, -688, -1204]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![2413, 4935, 3368, -688, -1204]] ![![223, 116, 30, -32, -24]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![1949107, 1656519, 811758, -255532, -315748]]]
 hmul := by decide  
 g := ![![![![10099, 8583, 4206, -1324, -1636]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4349, 186, -1100, -126, 300]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![4349, 186, -1100, -126, 300]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![179, 49, 1, 0, 0], ![94, 53, 0, 1, 0], ![74, 129, 0, 0, 1]] where
  M :=![![![4349, 186, -1100, -126, 300], ![-7200, -303, 1824, 200, -504], ![6048, 284, -1511, -192, 400], ![-1200, 28, 364, -11, -132], ![7416, 442, -1780, -278, 441]]]
  hmulB := by decide  
  f := ![![![-215, -186, 84, 142, -100]], ![![2400, 1253, -1056, -632, 568]], ![![367, 127, -171, -22, 44]], ![![614, 277, -276, -111, 116]], ![![1402, 715, -620, -350, 321]]]
  g := ![![![969, 112, -1100, -126, 300], ![-1600, -179, 1824, 200, -504], ![1345, 167, -1511, -192, 400], ![-282, -1, 364, -11, -132], ![1622, 231, -1780, -278, 441]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [1, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [129, 196], [0, 1]]
 g := ![![[68, 1], [76], [185, 160], [85], [196], [190], [129, 1]], ![[0, 196], [76], [140, 37], [85], [196], [190], [61, 196]]]
 h' := ![![[129, 196], [68, 1], [12, 43], [61, 102], [151, 26], [100, 183], [68, 92], [0, 1]], ![[0, 1], [0, 196], [43, 154], [20, 95], [156, 171], [67, 14], [116, 105], [129, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [59, 135]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [1, 68, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-212606, -114648, -23791, 62428, 45909]
  a := ![7, -21, -1, -23, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26495, -41522, -23791, 62428, 45909]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -34, 32, 14, -14]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-73, -34, 32, 14, -14]] 
 ![![197, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![149, 0, 1, 0, 0], ![107, 0, 0, 1, 0], ![160, 0, 0, 0, 1]] where
  M :=![![![-73, -34, 32, 14, -14], ![336, 141, -152, -48, 56], ![-672, -264, 301, 72, -96], ![984, 344, -452, -59, 116], ![-1200, -418, 544, 66, -135]]]
  hmulB := by decide  
  f := ![![![5011, 66, -1384, -86, 418]], ![![1984, 21, -552, -32, 168]], ![![3811, 42, -1059, -62, 322]], ![![2677, 14, -756, -37, 234]], ![![4064, 26, -1144, -58, 353]]]
  g := ![![![-7, -34, 32, 14, -14], ![40, 141, -152, -48, 56], ![-85, -264, 301, 72, -96], ![145, 344, -452, -59, 116], ![-174, -418, 544, 66, -135]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-95, -108, -62, 17, 24]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-95, -108, -62, 17, 24]] 
 ![![197, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![152, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![-95, -108, -62, 17, 24], ![-576, -387, -154, 68, 68], ![-816, -671, -319, 118, 136], ![-1344, -1004, -440, 191, 202], ![-1332, -1048, -478, 209, 225]]]
  hmulB := by decide  
  f := ![![![-8851, -3606, 3982, 1115, -1374]], ![![-4011, -1639, 1804, 511, -626]], ![![-5124, -2071, 2307, 626, -784]], ![![-6544, -2704, 2940, 869, -1042]], ![![-5630, -2246, 2538, 653, -841]]]
  g := ![![![57, -108, -62, 17, 24], ![171, -387, -154, 68, 68], ![315, -671, -319, 118, 136], ![440, -1004, -440, 191, 202], ![454, -1048, -478, 209, 225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2

def I197N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-385, -186, 170, 83, -80]] i)))

def SI197N3: IdealEqSpanCertificate' Table ![![-385, -186, 170, 83, -80]] 
 ![![197, 0, 0, 0, 0], ![123, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![186, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![-385, -186, 170, 83, -80], ![1920, 831, -858, -300, 332], ![-3984, -1595, 1795, 470, -600], ![6240, 2260, -2836, -455, 774], ![-7596, -2718, 3458, 515, -921]]]
  hmulB := by decide  
  f := ![![![2995, -3320, -3618, 345, 1190]], ![![1725, -2139, -2272, 227, 750]], ![![220, -443, -431, 50, 144]], ![![2622, -3288, -3484, 349, 1150]], ![![1985, -2492, -2640, 264, 871]]]
  g := ![![![75, -186, 170, 83, -80], ![-373, 831, -858, -300, 332], ![773, -1595, 1795, 470, -600], ![-1208, 2260, -2836, -455, 774], ![1471, -2718, 3458, 515, -921]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N3 : Nat.card (O ⧸ I197N3) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N3)

lemma isPrimeI197N3 : Ideal.IsPrime I197N3 := prime_ideal_of_norm_prime hp197.out _ NI197N3
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![4349, 186, -1100, -126, 300]] ![![-73, -34, 32, 14, -14]]
  ![![235, 16, -52, -8, 14]] where
 M := ![![![235, 16, -52, -8, 14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![235, 16, -52, -8, 14]] ![![-95, -108, -62, 17, 24]]
  ![![2995, -3320, -3618, 345, 1190]] where
 M := ![![![2995, -3320, -3618, 345, 1190]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N2 : IdealMulLeCertificate' Table 
  ![![2995, -3320, -3618, 345, 1190]] ![![-385, -186, 170, 83, -80]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2, I197N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
    exact isPrimeI197N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1 ⊙ MulI197N2)


lemma PB934I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB934I4 : PrimesBelowBoundCertificateInterval O 151 197 934 where
  m := 9
  g := ![2, 1, 2, 2, 3, 2, 2, 3, 4]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB934I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
    · exact ![I197N0, I197N1, I197N2, I197N3]
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
    · exact ![3869893, 24649]
    · exact ![115063617043]
    · exact ![4657463, 27889]
    · exact ![895745041, 173]
    · exact ![5735339, 179, 179]
    · exact ![1073283121, 181]
    · exact ![6967871, 36481]
    · exact ![7189057, 193, 193]
    · exact ![38809, 197, 197, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
      exact NI197N3
  β := ![I173N1, I179N1, I179N2, I181N1, I193N1, I193N2, I197N1, I197N2, I197N3]
  Il := ![[], [], [], [I173N1], [I179N1, I179N2], [I181N1], [], [I193N1, I193N2], [I197N1, I197N2, I197N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
