
import IdealArithmetic.Examples.NF5_1_48600000_4.RI5_1_48600000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![259, -219, -166, 5, 22]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![259, -219, -166, 5, 22]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![76, 40, 21, 93, 1]] where
  M :=![![![259, -219, -166, 5, 22], ![132, -71, -104, -12, 10], ![60, -18, -33, -34, -24], ![-144, 420, -172, -201, -68], ![-234, 447, -44, -307, -189]]]
  hmulB := by decide  
  f := ![![![-5, 9, 2, -1, 0]], ![![0, -5, 8, 2, -2]], ![![-12, 30, -13, -6, 4]], ![![24, -72, 44, 15, -12]], ![![10, -35, 27, 8, -7]]]
  g := ![![![-9, -7, -4, -13, 22], ![-4, -3, -2, -6, 10], ![12, 6, 3, 14, -24], ![32, 20, 8, 39, -68], ![90, 51, 25, 110, -189]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [1, 14, 119, 141, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 5, 106, 5], [119, 35, 128, 102], [123, 116, 80, 50], [0, 1]]
 g := ![![[69, 82, 7, 37], [11, 22, 93], [136, 123, 149, 71], [79, 94, 87, 11], [62, 103, 131, 99], [1], []], ![[100, 51, 55, 39, 13, 149], [68, 37, 105], [82, 134, 117, 82, 149, 55], [91, 66, 46, 75, 103, 34], [70, 50, 67, 73, 8, 116], [1, 79, 47], [114, 47, 25]], ![[121, 116, 116, 72, 115, 74], [17, 132, 1], [25, 94, 133, 106, 126, 22], [69, 35, 79, 36, 80, 50], [151, 104, 102, 44, 135, 54], [134, 141, 16], [91, 94, 42]], ![[107, 24, 84, 22, 11, 72], [52, 128, 52], [18, 130, 85, 93, 111, 94], [136, 105, 114, 147, 132, 53], [126, 74, 46, 69, 29, 20], [6, 78, 68], [73, 115, 145]]]
 h' := ![![[88, 5, 106, 5], [116, 30, 122, 42], [21, 132, 25, 90], [78, 132, 47, 68], [95, 129, 26, 110], [156, 143, 38, 16], [0, 0, 1], [0, 1]], ![[119, 35, 128, 102], [33, 34, 24, 76], [130, 77, 41, 24], [74, 39, 144, 110], [147, 59, 0, 130], [43, 118, 14, 137], [94, 22, 36, 19], [88, 5, 106, 5]], ![[123, 116, 80, 50], [27, 132, 140, 103], [94, 1, 99, 156], [1, 7, 46, 38], [29, 54, 49, 16], [12, 138, 54, 126], [97, 54, 34, 153], [119, 35, 128, 102]], ![[0, 1], [53, 118, 28, 93], [133, 104, 149, 44], [116, 136, 77, 98], [26, 72, 82, 58], [93, 72, 51, 35], [141, 81, 86, 142], [123, 116, 80, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [90, 34, 26], []]
 b := ![[], [], [23, 129, 50, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [1, 14, 119, 141, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1190982565, -2683351427, 721389226, 1563743076, 777365799]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-368718587, -215146391, -99384029, -450517683, 777365799]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -9, -2, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![5, -9, -2, 1, 0]] 
 ![![157, 0, 0, 0, 0], ![128, 1, 0, 0, 0], ![101, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![5, -9, -2, 1, 0], ![0, 5, -8, -2, 2], ![12, -30, 13, 6, -4], ![-24, 72, -44, -15, 12], ![30, -87, 52, 17, -13]]]
  hmulB := by decide  
  f := ![![![-259, 219, 166, -5, -22]], ![![-212, 179, 136, -4, -18]], ![![-167, 141, 107, -3, -14]], ![![-169, 141, 110, -2, -14]], ![![-48, 39, 32, 1, -3]]]
  g := ![![![8, -9, -2, 1, 0], ![2, 5, -8, -2, 2], ![13, -30, 13, 6, -4], ![-23, 72, -44, -15, 12], ![29, -87, 52, 17, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![259, -219, -166, 5, 22]] ![![5, -9, -2, 1, 0]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1657, 2310, 2004, 248, -96]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-1657, 2310, 2004, 248, -96]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![146, 17, 49, 1, 0], ![9, 64, 31, 0, 1]] where
  M :=![![![-1657, 2310, 2004, 248, -96], ![-576, -217, 2078, 1332, 496], ![2976, -8016, 3595, 5550, 2664], ![15984, -36984, 10854, 22243, 11100], ![31812, -71250, 18582, 41502, 20911]]]
  hmulB := by decide  
  f := ![![![-379, 1230, -1176, 224, 0]], ![![0, -379, 1454, -1176, 448]], ![![2688, -6720, 685, 4590, -2352]], ![![382, -725, -781, 1361, -604]], ![![651, -1804, 843, 564, -361]]]
  g := ![![![-227, 26, -44, 248, -96], ![-1224, -335, -482, 1332, 496], ![-5100, -1674, -2153, 5550, 2664], ![-20438, -6905, -8731, 22243, 11100], ![-38133, -12976, -16339, 41502, 20911]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [160, 136, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 52, 99], [149, 110, 64], [0, 1]]
 g := ![![[15, 141, 55], [90, 158, 90], [7, 111], [156, 39], [80, 81], [10, 31, 1], []], ![[55, 131, 155, 141], [61, 160, 127, 108], [37, 145], [8, 135], [27, 97], [100, 124, 80, 13], [26, 21]], ![[153, 68, 11, 24], [88, 88], [154, 115], [27, 25], [130, 150], [65, 56, 34, 113], [61, 21]]]
 h' := ![![[45, 52, 99], [107, 30, 50], [95, 135, 47], [143, 136, 130], [162, 59, 56], [30, 37, 9], [0, 0, 1], [0, 1]], ![[149, 110, 64], [5, 133, 157], [39, 16, 116], [108, 4, 54], [128, 81, 102], [84, 73, 89], [147, 66, 110], [45, 52, 99]], ![[0, 1], [55, 0, 119], [44, 12], [76, 23, 142], [22, 23, 5], [152, 53, 65], [53, 97, 52], [149, 110, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 43], []]
 b := ![[], [22, 154, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [160, 136, 132, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1467161, 4045160, -1385362, -1497925, 874707]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1284402, -162401, 275442, -1497925, 874707]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, -60, -37, 3, 6]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![41, -60, -37, 3, 6]] 
 ![![163, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![13, 0, 0, 1, 0], ![70, 0, 0, 0, 1]] where
  M :=![![![41, -60, -37, 3, 6], ![36, -49, -27, 5, 6], ![36, -54, -14, 15, 10], ![60, -114, 11, 56, 30], ![72, -168, 53, 103, 51]]]
  hmulB := by decide  
  f := ![![![-301, 792, -381, -199, 134]], ![![-32, 83, -39, -21, 14]], ![![-179, 474, -231, -118, 80]], ![![17, -54, 36, 9, -8]], ![![-178, 480, -245, -113, 79]]]
  g := ![![![25, -60, -37, 3, 6], ![18, -49, -27, 5, 6], ![9, -54, -14, 15, 10], ![-9, -114, 11, 56, 30], ![-38, -168, 53, 103, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33181, 94398, -52299, -21225, 15538]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-33181, 94398, -52299, -21225, 15538]] 
 ![![163, 0, 0, 0, 0], ![94, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![-33181, 94398, -52299, -21225, 15538], ![93228, -266251, 150863, 56467, -42450], ![-254700, 729978, -422034, -146287, 112934], ![677604, -1948710, 1148361, 368504, -292574], ![-750372, 2168118, -1310521, -376685, 312037]]]
  hmulB := by decide  
  f := ![![![-95335, 134130, 31477, -40639, -26502]], ![![-55954, 79205, 17913, -24381, -15782]], ![![-78441, 112656, 23327, -35892, -22864]], ![![-69243, 106824, 12442, -39497, -23556]], ![![-74107, 121908, 4988, -50270, -28665]]]
  g := ![![![-9035, 94398, -52299, -21225, 15538], ![24124, -266251, 150863, 56467, -42450], ![-62729, 729978, -422034, -146287, 112934], ![158651, -1948710, 1148361, 368504, -292574], ![-163189, 2168118, -1310521, -376685, 312037]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-1657, 2310, 2004, 248, -96]] ![![41, -60, -37, 3, 6]]
  ![![95335, -134130, -31477, 40639, 26502]] where
 M := ![![![95335, -134130, -31477, 40639, 26502]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![95335, -134130, -31477, 40639, 26502]] ![![-33181, 94398, -52299, -21225, 15538]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1225, -1029, -1223, 18, 180]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1225, -1029, -1223, 18, 180]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![0, 0, 0, 167, 0], ![30, 75, 150, 117, 1]] where
  M :=![![![1225, -1029, -1223, 18, 180], ![1080, -1475, -111, 37, 36], ![216, 540, -1258, 141, 74], ![444, -894, 1051, -740, 282], ![738, -2163, 517, 1442, -777]]]
  hmulB := by decide  
  f := ![![![-469, 1053, -279, -616, -310]], ![![-1860, 4181, -1113, -2449, -1232]], ![![-7392, 16620, -4428, -9737, -4898]], ![![-29388, 66078, -17607, -38714, -19474]], ![![-28476, 64026, -17059, -37511, -18869]]]
  g := ![![![-25, -87, -169, -126, 180], ![0, -25, -33, -25, 36], ![-12, -30, -74, -51, 74], ![-48, -132, -247, -202, 282], ![144, 336, 701, 553, -777]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 4 2 7 [93, 108, 153, 93, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 6, 47, 66], [73, 161, 40, 161], [81, 166, 80, 107], [0, 1]]
 g := ![![[26, 143, 95, 127], [43, 103, 22, 96], [41, 131, 32, 141], [145, 128, 19], [148, 4, 107], [74, 1], []], ![[55, 84, 53, 147, 92, 126], [79, 153, 138, 146, 74, 36], [141, 61, 146, 146, 40, 98], [115, 37, 121], [152, 80, 57], [32, 90, 121, 56, 163, 157], [48, 59, 14]], ![[58, 144, 121, 156, 117, 60], [133, 72, 28, 83, 137, 103], [163, 67, 31, 69, 40, 165], [108, 118, 2], [103, 99, 38], [85, 16, 162, 78, 8, 111], [132, 13, 36]], ![[130, 82, 22, 41, 34, 130], [132, 119, 33, 144, 44, 32], [79, 115, 102, 107, 145, 100], [141, 166, 126], [60, 17, 31], [61, 144, 17, 131, 132, 126], [76, 121, 93]]]
 h' := ![![[87, 6, 47, 66], [9, 88, 164, 131], [28, 120, 112, 116], [71, 75, 93, 59], [153, 164, 127, 112], [132, 98, 93, 146], [0, 0, 1], [0, 1]], ![[73, 161, 40, 161], [148, 95, 34, 107], [83, 7, 82, 150], [155, 159, 114, 63], [117, 107, 164, 11], [15, 25, 11, 70], [99, 59, 43, 51], [87, 6, 47, 66]], ![[81, 166, 80, 107], [24, 34, 29, 149], [38, 46, 63, 150], [0, 112, 81, 132], [109, 135, 153, 13], [154, 35, 12, 47], [67, 25, 133, 30], [73, 161, 40, 161]], ![[0, 1], [72, 117, 107, 114], [2, 161, 77, 85], [37, 155, 46, 80], [142, 95, 57, 31], [82, 9, 51, 71], [161, 83, 157, 86], [81, 166, 80, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [48, 107, 158], []]
 b := ![[], [], [99, 111, 91, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 4
  hpos := by decide
  P := [93, 108, 153, 93, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48562828, -109286229, 29270071, 63849005, 32031554]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5463376, -15039837, -28595587, -22058939, 32031554]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 777796321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-469, 1053, -279, -616, -310]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-469, 1053, -279, -616, -310]] 
 ![![167, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![-469, 1053, -279, -616, -310], ![-1860, 4181, -1113, -2449, -1232], ![-7392, 16620, -4428, -9737, -4898], ![-29388, 66078, -17607, -38714, -19474], ![-54726, 123051, -32789, -72094, -36265]]]
  hmulB := by decide  
  f := ![![![1225, -1029, -1223, 18, 180]], ![![740, -625, -733, 11, 108]], ![![148, -120, -154, 3, 22]], ![![32, -30, -23, -4, 6]], ![![914, -777, -905, 22, 129]]]
  g := ![![![-355, 1053, -279, -616, -310], ![-1408, 4181, -1113, -2449, -1232], ![-5596, 16620, -4428, -9737, -4898], ![-22248, 66078, -17607, -38714, -19474], ![-41430, 123051, -32789, -72094, -36265]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1225, -1029, -1223, 18, 180]] ![![-469, 1053, -279, -616, -310]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0, 0, 0]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]] where
  M :=![![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![0, 0, 0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 5 2 7 [133, 128, 74, 74, 66, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 169, 86, 45, 168], [44, 86, 1, 23, 115], [15, 71, 133, 62, 56], [51, 19, 126, 43, 7], [0, 1]]
 g := ![![[134, 12, 44, 104, 6], [71, 126, 132, 137], [84, 154, 108, 121, 136], [130, 21, 45, 52, 95], [157, 154, 110, 31], [1], []], ![[97, 129, 42, 43, 33, 109, 6, 79], [166, 40, 3, 24], [139, 0, 3, 74, 162, 115, 158, 131], [49, 148, 23, 4, 162, 92, 65, 80], [51, 56, 90, 118], [128, 48, 84, 41, 102, 21, 28, 147], [99, 34, 149, 25]], ![[124, 100, 124, 9, 53, 161, 117, 5], [114, 140, 122, 135], [53, 6, 41, 11, 66, 113, 95, 154], [54, 40, 121, 161, 146, 28, 50, 26], [148, 50, 125, 135], [40, 43, 137, 50, 152, 64, 92, 69], [36, 17, 35, 77]], ![[157, 23, 141, 37, 21, 172, 109, 29], [131, 122, 29, 67], [44, 114, 118, 49, 131, 23, 16, 51], [99, 38, 159, 15, 27, 150, 69, 24], [41, 122, 101, 126], [11, 148, 51, 29, 143, 141, 105, 60], [94, 121, 129, 22]], ![[132, 66, 170, 169, 50, 8, 152, 127], [116, 11, 106, 169], [126, 89, 48, 112, 125, 78, 65, 70], [82, 119, 116, 62, 121, 16, 167, 80], [143, 31, 146, 106], [97, 104, 30, 34, 102, 133, 120, 45], [64, 7, 136, 49]]]
 h' := ![![[170, 169, 86, 45, 168], [38, 115, 152, 49, 51], [73, 6, 149, 82, 134], [10, 145, 101, 49, 84], [95, 44, 142, 6, 152], [40, 45, 99, 99, 107], [0, 0, 1], [0, 1]], ![[44, 86, 1, 23, 115], [150, 56, 138, 66, 61], [118, 148, 3, 66, 71], [118, 112, 79, 49, 40], [21, 29, 144, 153, 26], [149, 29, 67, 164, 139], [163, 130, 10, 19, 52], [170, 169, 86, 45, 168]], ![[15, 71, 133, 62, 56], [31, 163, 85, 149, 136], [90, 171, 15, 146, 57], [130, 131, 148, 3, 24], [130, 26, 169, 106, 152], [145, 148, 10, 14, 57], [89, 7, 65, 161, 73], [44, 86, 1, 23, 115]], ![[51, 19, 126, 43, 7], [159, 104, 68, 22, 162], [52, 102, 43, 6, 97], [94, 88, 103, 170, 2], [160, 147, 156, 55, 132], [115, 6, 49, 25, 68], [6, 128, 51, 103, 134], [15, 71, 133, 62, 56]], ![[0, 1], [163, 81, 76, 60, 109], [59, 92, 136, 46, 160], [47, 43, 88, 75, 23], [99, 100, 81, 26, 57], [61, 118, 121, 44, 148], [144, 81, 46, 63, 87], [51, 19, 126, 43, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 47, 35, 108], [], [], []]
 b := ![[], [72, 106, 158, 70, 160], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 5
  hpos := by decide
  P := [133, 128, 74, 74, 66, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3835387188566, -8622750849580, 2293885308969, 5055872870775, 2540381178883]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![22169868142, -49842490460, 13259452653, 29224698675, 14684284271]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 154963892093 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-448553, 1007364, -268014, -590018, -296836]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-448553, 1007364, -268014, -590018, -296836]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![172, 22, 1, 0, 0], ![154, 46, 0, 1, 0], ![75, 97, 0, 0, 1]] where
  M :=![![![-448553, 1007364, -268014, -590018, -296836], ![-1781016, 4003987, -1066834, -2345866, -1180036], ![-7080216, 15919524, -4242059, -9327086, -4691732], ![-28150392, 63295764, -16866222, -37084183, -18654172], ![-52422408, 117871332, -31408610, -69059170, -34738317]]]
  hmulB := by decide  
  f := ![![![419525, -1213356, 737234, 206934, -173060]], ![![-1038360, 3015425, -1871722, -474186, 413868]], ![![289372, -835778, 504117, 146290, -120724]], ![![62302, -175634, 92022, 44845, -31076]], ![![-359475, 1044091, -648618, -163646, 143083]]]
  g := ![![![887013, 351048, -268014, -590018, -296836], ![3527824, 1395797, -1066834, -2345866, -1180036], ![14026844, 5549658, -4242059, -9327086, -4691732], ![55770206, 22065250, -16866222, -37084183, -18654172], ![103856673, 41090499, -31408610, -69059170, -34738317]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [159, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 178], [0, 1]]
 g := ![![[134, 49], [103, 155], [108], [95], [5, 3], [33, 25], [1]], ![[68, 130], [44, 24], [108], [95], [169, 176], [87, 154], [1]]]
 h' := ![![[174, 178], [91, 7], [69, 79], [86, 65], [100, 128], [123, 19], [20, 174], [0, 1]], ![[0, 1], [56, 172], [32, 100], [119, 114], [176, 51], [28, 160], [45, 5], [174, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121]]
 b := ![[], [17, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [159, 5, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-631, 5604, -6219, 2839, 7496]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![389, -3996, -6219, 2839, 7496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![327769, -736960, 196352, 431762, 217188]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![327769, -736960, 196352, 431762, 217188]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![114, 87, 1, 0, 0], ![106, 63, 0, 1, 0], ![111, 133, 0, 0, 1]] where
  M :=![![![327769, -736960, 196352, 431762, 217188], ![1303128, -2930051, 780742, 1716668, 863524], ![5181144, -11649732, 3104237, 6825410, 3433336], ![20600016, -46318896, 12342358, 27137589, 13650820], ![38361888, -86256276, 22984278, 50536344, 25420921]]]
  hmulB := by decide  
  f := ![![![4139, -12352, 8300, 1466, -1524]], ![![-9144, 26999, -18506, -2368, 2932]], ![![-1710, 4959, -3489, -206, 428]], ![![-926, 2683, -2016, 69, 152]], ![![-4209, 12301, -8392, -986, 1281]]]
  g := ![![![-513581, -412886, 196352, 431762, 217188], ![-2042008, -1641639, 780742, 1716668, 863524], ![-8118970, -6527111, 3104237, 6825410, 3433336], ![-32280750, -25951571, 12342358, 27137589, 13650820], ![-60114081, -48327713, 22984278, 50536344, 25420921]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P1 : CertificateIrreducibleZModOfList' 179 2 2 7 [27, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 178], [0, 1]]
 g := ![![[59, 126], [134, 138], [156], [51], [144, 46], [27, 145], [1]], ![[0, 53], [112, 41], [156], [51], [77, 133], [131, 34], [1]]]
 h' := ![![[18, 178], [141, 22], [158, 73], [49, 131], [50, 87], [166, 164], [152, 18], [0, 1]], ![[0, 1], [0, 157], [40, 106], [80, 48], [5, 92], [75, 15], [118, 161], [18, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116]]
 b := ![[], [15, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N1 : CertifiedPrimeIdeal' SI179N1 179 where
  n := 2
  hpos := by decide
  P := [27, 161, 1]
  hirr := P179P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9933, 27792, -12860, -9742, 6458]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9899, 5036, -12860, -9742, 6458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N1 B_one_repr
lemma NI179N1 : Nat.card (O ⧸ I179N1) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-917, 732, 579, -21, -84]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-917, 732, 579, -21, -84]] 
 ![![179, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![36, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![-917, 732, 579, -21, -84], ![-504, 343, 291, -9, -42], ![-252, 126, 124, -3, -18], ![-108, 18, 33, -2, -6], ![108, -72, -69, -3, 7]]]
  hmulB := by decide  
  f := ![![![-1063, 3000, -1581, -759, 528]], ![![-398, 1123, -591, -285, 198]], ![![-716, 2022, -1070, -507, 354]], ![![-72, 198, -87, -68, 42]], ![![-856, 2424, -1305, -585, 415]]]
  g := ![![![-595, 732, 579, -21, -84], ![-290, 343, 291, -9, -42], ![-116, 126, 124, -3, -18], ![-24, 18, 33, -2, -6], ![68, -72, -69, -3, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-448553, 1007364, -268014, -590018, -296836]] ![![327769, -736960, 196352, 431762, 217188]]
  ![![-23764486288337, 53434179318428, -14238336396738, -31306336227160, -15747793473648]] where
 M := ![![![-23764486288337, 53434179318428, -14238336396738, -31306336227160, -15747793473648]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-23764486288337, 53434179318428, -14238336396738, -31306336227160, -15747793473648]] ![![-917, 732, 579, -21, -84]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![129590939274589, -291383764817092, 77643561705345, 170717660254703, 85874835035040]]]
 hmul := by decide  
 g := ![![![![723971727791, -1627842261548, 433762914555, 953729945557, 479747681760]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -50, -50, 0, 8]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![53, -50, -50, 0, 8]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![79, 41, 1, 0, 0], ![19, 27, 0, 1, 0], ![161, 69, 0, 0, 1]] where
  M :=![![![53, -50, -50, 0, 8], ![48, -67, -10, 6, 0], ![0, 48, -61, -10, 12], ![72, -180, 98, 23, -20], ![-60, 162, -98, -16, 17]]]
  hmulB := by decide  
  f := ![![![-31, 26, 34, 8, 0]], ![![0, -31, 34, 34, 16]], ![![-13, 3, 23, 12, 4]], ![![-1, -7, 10, 9, 4]], ![![-23, 1, 46, 26, 9]]]
  g := ![![![15, 8, -50, 0, 8], ![4, 1, -10, 6, 0], ![17, 11, -61, -10, 12], ![-27, -19, 98, 23, -20], ![29, 19, -98, -16, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [173, 167, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 180], [0, 1]]
 g := ![![[47, 167], [33], [87, 87], [15], [133, 14], [72, 15], [1]], ![[32, 14], [33], [38, 94], [15], [148, 167], [101, 166], [1]]]
 h' := ![![[14, 180], [143, 23], [153, 24], [61, 102], [159, 167], [33, 106], [8, 14], [0, 1]], ![[0, 1], [103, 158], [127, 157], [41, 79], [144, 14], [69, 75], [23, 167], [14, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [8, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [173, 167, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2819, 1217, -3565, 2744, 3208]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1570, -818, -3565, 2744, 3208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3353, -7544, 2014, 4422, 2224]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![3353, -7544, 2014, 4422, 2224]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![110, 146, 1, 0, 0], ![49, 152, 0, 1, 0], ![92, 168, 0, 0, 1]] where
  M :=![![![3353, -7544, 2014, 4422, 2224], ![13344, -30007, 7998, 17582, 8844], ![53064, -119316, 31795, 69906, 35164], ![210984, -474396, 126410, 277943, 139812], ![392904, -883440, 235406, 517594, 260361]]]
  hmulB := by decide  
  f := ![![![413, -328, -590, -46, 112]], ![![672, -1267, 186, 194, -92]], ![![790, -1210, -217, 126, -4]], ![![689, -1188, 16, 157, -52]], ![![820, -1304, -150, 150, -23]]]
  g := ![![![-3533, -7444, 2014, 4422, 2224], ![-14042, -29591, 7998, 17582, 8844], ![-55828, -117650, 31795, 69906, 35164], ![-221967, -467768, 126410, 277943, 139812], ![-413354, -871092, 235406, 517594, 260361]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [113, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 180], [0, 1]]
 g := ![![[93, 33], [176], [95, 82], [106], [1, 70], [69, 121], [1]], ![[92, 148], [176], [98, 99], [106], [136, 111], [5, 60], [1]]]
 h' := ![![[170, 180], [81, 157], [125, 151], [67, 25], [68, 58], [167, 147], [68, 170], [0, 1]], ![[0, 1], [164, 24], [93, 30], [154, 156], [154, 123], [179, 34], [8, 11], [170, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [23, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [113, 11, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-287, 1383, -969, -20, 932]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![119, -59, -969, -20, 932]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 22, 4, -2, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-25, 22, 4, -2, 0]] 
 ![![181, 0, 0, 0, 0], ![175, 1, 0, 0, 0], ![145, 0, 1, 0, 0], ![146, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-25, 22, 4, -2, 0], ![0, -25, 20, 4, -4], ![-24, 60, -41, -8, 8], ![48, -144, 92, 15, -16], ![-36, 114, -84, -6, 11]]]
  hmulB := by decide  
  f := ![![![-541, 1202, -340, -718, -360]], ![![-535, 1189, -336, -710, -356]], ![![-481, 1070, -301, -638, -320]], ![![-626, 1396, -388, -829, -416]], ![![-634, 1418, -388, -838, -421]]]
  g := ![![![-23, 22, 4, -2, 0], ![7, -25, 20, 4, -4], ![-23, 60, -41, -8, 8], ![62, -144, 92, 15, -16], ![-44, 114, -84, -6, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![53, -50, -50, 0, 8]] ![![3353, -7544, 2014, 4422, 2224]]
  ![![541, -1202, 340, 718, 360]] where
 M := ![![![541, -1202, 340, 718, 360]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![541, -1202, 340, 718, 360]] ![![-25, 22, 4, -2, 0]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![397, -367, -255, 14, 36]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![397, -367, -255, 14, 36]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![106, 31, 125, 1, 0], ![60, 121, 130, 0, 1]] where
  M :=![![![397, -367, -255, 14, 36], ![216, -143, -173, -3, 28], ![168, -204, -6, 23, -6], ![-36, 258, -211, -48, 46], ![54, -261, 223, 44, -45]]]
  hmulB := by decide  
  f := ![![![-1, -1, 5, 4, 2]], ![![12, -31, 13, 19, 8]], ![![48, -108, 28, 69, 38]], ![![34, -79, 24, 52, 28]], ![![42, -98, 30, 63, 33]]]
  g := ![![![-17, -27, -35, 14, 36], ![-6, -18, -18, -3, 28], ![-10, -1, -11, 23, -6], ![12, -20, -1, -48, 46], ![-10, 20, 3, 44, -45]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [80, 145, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 99, 150], [150, 91, 41], [0, 1]]
 g := ![![[171, 157, 80], [143, 165, 92], [21, 66, 60], [9, 137, 10], [107, 13, 54], [52, 31, 1], []], ![[91, 148, 158, 12], [81, 121, 185, 24], [133, 69, 65, 162], [165, 164, 143, 80], [165, 142, 67, 6], [61, 53, 54, 77], [63, 153]], ![[15, 128, 97, 74], [107, 32, 51, 57], [164, 77, 56, 37], [176, 61, 81, 189], [97, 175, 27, 148], [184, 0, 189, 168], [172, 153]]]
 h' := ![![[72, 99, 150], [20, 56, 56], [39, 105, 130], [44, 38, 92], [35, 107, 34], [42, 103, 93], [0, 0, 1], [0, 1]], ![[150, 91, 41], [83, 149, 126], [152, 6, 76], [175, 124, 129], [29, 39, 44], [31, 13, 38], [144, 139, 91], [72, 99, 150]], ![[0, 1], [114, 177, 9], [68, 80, 176], [175, 29, 161], [5, 45, 113], [136, 75, 60], [145, 52, 99], [150, 91, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 38], []]
 b := ![[], [170, 96, 150], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [80, 145, 160, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1569058, 5861898, -4650452, 485192, 3522760]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1384110, -2279754, -2739572, 485192, 3522760]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17227, 49722, -29877, -8817, 7228]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-17227, 49722, -29877, -8817, 7228]] 
 ![![191, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![183, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![163, 0, 0, 0, 1]] where
  M :=![![![-17227, 49722, -29877, -8817, 7228], ![43368, -125647, 77045, 20719, -17634], ![-105804, 307878, -193098, -46393, 41438], ![248628, -727374, 468675, 96968, -92786], ![-225456, 666270, -450619, -67217, 76249]]]
  hmulB := by decide  
  f := ![![![90106147, -202602018, 53986127, 118701589, 59709600]], ![![38201209, -85894729, 22887850, 50324480, 25314358]], ![![93789759, -210884604, 56193155, 123554244, 62150594]], ![![49937195, -112283076, 29919458, 65785059, 33091374]], ![![132114719, -297057912, 79155344, 174041986, 87547065]]]
  g := ![![![4307, 49722, -29877, -8817, 7228], ![-12553, -125647, 77045, 20719, -17634], ![35419, 307878, -193098, -46393, 41438], ![-97155, -727374, 468675, 96968, -92786], ![112025, 666270, -450619, -67217, 76249]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-213557, 617945, -376407, -104432, 87750]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-213557, 617945, -376407, -104432, 87750]] 
 ![![191, 0, 0, 0, 0], ![180, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![189, 0, 0, 0, 1]] where
  M :=![![![-213557, 617945, -376407, -104432, 87750], ![526500, -1529807, 952263, 237843, -208864], ![-1253184, 3659460, -2336284, -509785, 475686], ![2854116, -8388474, 5528105, 993518, -1019570], ![-2432118, 7244103, -5078261, -549550, 755675]]]
  hmulB := by decide  
  f := ![![![555521, -102001, -201599, -6750, 25096]], ![![524316, -95189, -189901, -6497, 23580]], ![![203170, -35534, -73436, -2881, 8926]], ![![15822, 444, -6249, -1664, -26]], ![![547473, -96564, -200650, -9284, 23517]]]
  g := ![![![-529075, 617945, -376407, -104432, 87750], ![1294668, -1529807, 952263, 237843, -208864], ![-3053728, 3659460, -2336284, -509785, 475686], ![6871988, -8388474, 5528105, 993518, -1019570], ![-5708993, 7244103, -5078261, -549550, 755675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![397, -367, -255, 14, 36]] ![![-17227, 49722, -29877, -8817, 7228]]
  ![![-410779, 1145677, -557528, -336267, 220464]] where
 M := ![![![-410779, 1145677, -557528, -336267, 220464]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-410779, 1145677, -557528, -336267, 220464]] ![![-213557, 617945, -376407, -104432, 87750]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-106330647169, 371075971976, -430343363083, 144365830213, -31097923996]]]
 hmul := by decide  
 g := ![![![![-556704959, 1942806136, -2253106613, 755842043, -162816356]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29671, 32958, 22964, -1092, -3374]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-29671, 32958, 22964, -1092, -3374]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![180, 125, 137, 74, 1]] where
  M :=![![![-29671, 32958, 22964, -1092, -3374], ![-20244, 20939, 14996, -654, -2184], ![-13104, 12516, 9365, -292, -1308], ![-7848, 6516, 5684, 209, -584], ![4800, -5802, -2780, 944, 863]]]
  hmulB := by decide  
  f := ![![![-175, 498, -276, -112, 82]], ![![492, -1405, 796, 298, -224]], ![![-1344, 3852, -2227, -772, 596]], ![![3576, -10284, 6060, 1945, -1544]], ![![552, -1595, 965, 276, -229]]]
  g := ![![![2993, 2356, 2514, 1288, -3374], ![1932, 1523, 1628, 834, -2184], ![1152, 912, 977, 500, -1308], ![504, 412, 444, 225, -584], ![-780, -589, -627, -326, 863]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [84, 76, 113, 99, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 137, 63, 26], [185, 62, 105, 131], [71, 186, 25, 36], [0, 1]]
 g := ![![[126, 10, 104, 124], [114, 131, 3], [75, 136, 69], [90, 54, 108], [178, 116, 32], [38, 94, 1], []], ![[106, 139, 136, 5, 115, 159], [103, 74, 55], [24, 136, 107], [118, 15, 187], [106, 154, 126], [40, 123, 75], [85, 112, 48, 39, 62, 13]], ![[160, 116, 123, 151, 68, 165], [154, 176, 168], [155, 180, 86], [78, 169, 121], [14, 111, 172], [8, 30, 27], [107, 42, 80, 10, 7, 27]], ![[91, 86, 159, 19, 120, 9], [43, 61, 21], [166, 191, 23], [88, 148, 64], [131, 88, 14], [58, 57, 69], [95, 114, 102, 157, 53, 143]]]
 h' := ![![[31, 137, 63, 26], [18, 141, 94, 33], [41, 98, 95, 179], [101, 5, 190, 29], [110, 107, 126, 84], [89, 24, 58, 15], [0, 0, 0, 1], [0, 1]], ![[185, 62, 105, 131], [27, 12, 115, 111], [103, 42, 57, 172], [31, 177, 181, 140], [183, 107, 0, 90], [189, 137, 17, 133], [70, 51, 87, 70], [31, 137, 63, 26]], ![[71, 186, 25, 36], [105, 33, 3, 145], [127, 169, 157, 174], [122, 88, 158, 146], [150, 142, 96, 11], [19, 13, 68, 65], [150, 51, 85, 151], [185, 62, 105, 131]], ![[0, 1], [23, 7, 174, 97], [136, 77, 77, 54], [143, 116, 50, 71], [89, 30, 164, 8], [51, 19, 50, 173], [22, 91, 21, 164], [71, 186, 25, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [157, 191, 169], []]
 b := ![[], [], [32, 74, 60, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [84, 76, 113, 99, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![623466115, -1346730666, 275603587, 890794603, 506952263]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-469574825, -335314837, -358429308, -189759963, 506952263]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-175, 498, -276, -112, 82]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-175, 498, -276, -112, 82]] 
 ![![193, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![167, 0, 0, 0, 1]] where
  M :=![![![-175, 498, -276, -112, 82], ![492, -1405, 796, 298, -224], ![-1344, 3852, -2227, -772, 596], ![3576, -10284, 6060, 1945, -1544], ![-3960, 11442, -6916, -1988, 1647]]]
  hmulB := by decide  
  f := ![![![-29671, 32958, 22964, -1092, -3374]], ![![-7023, 7793, 5432, -258, -798]], ![![-15134, 16800, 11709, -556, -1720]], ![![-4499, 4986, 3480, -163, -510]], ![![-25649, 28488, 19856, -940, -2915]]]
  g := ![![![-31, 498, -276, -112, 82], ![75, -1405, 796, 298, -224], ![-174, 3852, -2227, -772, 596], ![383, -10284, 6060, 1945, -1544], ![-303, 11442, -6916, -1988, 1647]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-29671, 32958, 22964, -1092, -3374]] ![![-175, 498, -276, -112, 82]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21551, 67218, -56601, 4509, 3124]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-21551, 67218, -56601, 4509, 3124]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![72, 47, 134, 1, 0], ![101, 39, 108, 0, 1]] where
  M :=![![![-21551, 67218, -56601, 4509, 3124], ![18744, -68411, 87347, -34733, 9018], ![54108, -116526, -58054, 150473, -69466], ![-416796, 1096098, -313383, -544316, 300946], ![875784, -2407230, 1057283, 821383, -509583]]]
  hmulB := by decide  
  f := ![![![26117, -20262, -16283, 533, 2336]], ![![14016, -8923, -8049, 69, 1066]], ![![6396, -1974, -3524, -587, 138]], ![![17244, -10855, -10278, -201, 1196]], ![![19637, -13185, -11875, -59, 1471]]]
  g := ![![![-3359, -1353, -5067, 4509, 3124], ![8166, 6154, 19125, -34733, 9018], ![-19106, -22739, -64564, 150473, -69466], ![42530, 75848, 203669, -544316, 300946], ![-34497, -107302, -273975, 821383, -509583]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [31, 159, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 100, 81], [133, 96, 116], [0, 1]]
 g := ![![[37, 128, 59], [56, 1], [146, 39, 96], [173, 171], [166, 63], [2, 53], [1]], ![[80, 180, 129, 150], [82, 7], [189, 165, 138, 22], [64, 187], [74, 25], [149, 150], [158, 46, 185, 132]], ![[30, 83, 144, 34], [193, 190], [109, 175, 29, 193], [42, 116], [89, 60], [113, 93], [108, 164, 29, 65]]]
 h' := ![![[35, 100, 81], [62, 158, 181], [5, 141, 1], [147, 55, 117], [83, 52, 163], [111, 17, 76], [166, 38, 168], [0, 1]], ![[133, 96, 116], [157, 182, 33], [170, 178, 91], [113, 103, 124], [179, 35, 160], [75, 139, 5], [153, 142, 97], [35, 100, 81]], ![[0, 1], [19, 54, 180], [17, 75, 105], [86, 39, 153], [3, 110, 71], [2, 41, 116], [64, 17, 129], [133, 96, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 128], []]
 b := ![[], [66, 67, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [31, 159, 29, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6703, -16668, 10919, 1897, -3451]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1110, 146, 657, 1897, -3451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![269, -760, 404, 188, -132]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![269, -760, 404, 188, -132]] 
 ![![197, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![136, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![140, 0, 0, 0, 1]] where
  M :=![![![269, -760, 404, 188, -132], ![-792, 2249, -1232, -520, 376], ![2256, -6432, 3609, 1400, -1040], ![-6240, 17856, -10232, -3671, 2800], ![7272, -20904, 12288, 3984, -3151]]]
  hmulB := by decide  
  f := ![![![-17543, 15512, 11852, -412, -1692]], ![![-7888, 6969, 5328, -184, -760]], ![![-12136, 10720, 8201, -280, -1168]], ![![-4363, 3832, 2964, -83, -412]], ![![-12428, 10952, 8432, -256, -1183]]]
  g := ![![![109, -760, 404, 188, -132], ![-296, 2249, -1232, -520, 376], ![784, -6432, 3609, 1400, -1040], ![-2021, 17856, -10232, -3671, 2800], ![2140, -20904, 12288, 3984, -3151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14735, 41605, -22017, -10402, 7272]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![-14735, 41605, -22017, -10402, 7272]] 
 ![![197, 0, 0, 0, 0], ![172, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-14735, 41605, -22017, -10402, 7272], ![43632, -123815, 67563, 28887, -20804], ![-124824, 355692, -198948, -78065, 57774], ![346644, -991434, 566497, 205470, -156130], ![-405978, 1166451, -683833, -224174, 176583]]]
  hmulB := by decide  
  f := ![![![-65263, 93697, 44881, -13292, -12710]], ![![-57368, 82443, 39271, -11829, -11232]], ![![-54809, 79163, 36873, -11857, -10964]], ![![-47409, 70113, 29296, -12504, -10428]], ![![-14688, 24993, 3925, -8338, -5107]]]
  g := ![![![-12162, 41605, -22017, -10402, 7272], ![35794, -123815, 67563, 28887, -20804], ![-101877, 355692, -198948, -78065, 57774], ![281623, -991434, 566497, 205470, -156130], ![-327943, 1166451, -683833, -224174, 176583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-21551, 67218, -56601, 4509, 3124]] ![![269, -760, 404, 188, -132]]
  ![![-192144163, 546818282, -303540565, -122352871, 89765216]] where
 M := ![![![-192144163, 546818282, -303540565, -122352871, 89765216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-192144163, 546818282, -303540565, -122352871, 89765216]] ![![-14735, 41605, -22017, -10402, 7272]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-14276424468583, 42346108142005, -29133041366658, -3772354433569, 4643932391784]]]
 hmul := by decide  
 g := ![![![![-72469159739, 214954863665, -147883458714, -19149007277, 23573260872]]]]
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


lemma PB434I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB434I4 : PrimesBelowBoundCertificateInterval O 151 197 434 where
  m := 9
  g := ![2, 3, 2, 1, 3, 3, 3, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB434I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
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
    · exact ![607573201, 157]
    · exact ![4330747, 163, 163]
    · exact ![777796321, 167]
    · exact ![154963892093]
    · exact ![32041, 32041, 179]
    · exact ![32761, 32761, 181]
    · exact ![6967871, 191, 191]
    · exact ![1387488001, 193]
    · exact ![7645373, 197, 197]
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
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I157N1, I163N1, I163N2, I167N1, I179N2, I181N2, I191N1, I191N2, I193N1, I197N1, I197N2]
  Il := ![[I157N1], [I163N1, I163N2], [I167N1], [], [I179N2], [I181N2], [I191N1, I191N2], [I193N1], [I197N1, I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
