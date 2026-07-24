
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54211, 48200, -40312, 67870, -35016]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-54211, 48200, -40312, 67870, -35016]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![72, 94, 24, 85, 1]] where
  M :=![![![-54211, 48200, -40312, 67870, -35016], ![210096, -186817, 156382, -263162, 135740], ![-814440, 724096, -606361, 1020424, -526324], ![851200, -756732, 633634, -1066447, 550088], ![-1563596, 1390048, -1163852, 1958922, -1010459]]]
  hmulB := by decide  
  f := ![![![-479, -240, -116, 50, 72]], ![![-432, -197, -74, 134, 100]], ![![-600, -192, 11, 512, 268]], ![![-880, -236, 82, 933, 464]], ![![-1052, -386, -50, 695, 389]]]
  g := ![![![15713, 21272, 5096, 19390, -35016], ![-60912, -82461, -19754, -75166, 135740], ![236184, 319736, 76595, 291452, -526324], ![-246848, -334172, -80054, -304611, 550088], ![453436, 613842, 147052, 559541, -1010459]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [147, 99, 39, 106, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 47, 65, 68], [18, 131, 1, 19], [8, 135, 91, 70], [0, 1]]
 g := ![![[81, 109, 129, 68], [41, 106, 67], [105, 67, 43, 106], [121, 142, 77, 110], [85, 78, 90, 89], [1], []], ![[48, 100, 52, 1, 1, 42], [49, 145, 132], [139, 58, 12, 53, 28, 14], [155, 45, 0, 119, 98, 33], [91, 91, 105, 69, 75, 106], [130, 65, 27], [130, 58, 71]], ![[148, 56, 107, 85, 65, 140], [35, 88, 108], [23, 6, 59, 112, 0, 117], [40, 137, 13, 118, 113, 14], [103, 137, 78, 25, 128, 145], [133, 3, 56], [4, 80, 47]], ![[38, 8, 100, 103, 49, 88], [85, 4, 4], [114, 91, 101, 137, 107, 152], [150, 141, 137, 110, 153, 78], [55, 42, 118, 79, 81, 53], [44, 101, 51], [17, 136, 33]]]
 h' := ![![[25, 47, 65, 68], [142, 73, 30, 15], [108, 84, 8, 58], [111, 103, 21, 48], [65, 1, 129, 96], [10, 58, 118, 51], [0, 0, 1], [0, 1]], ![[18, 131, 1, 19], [125, 88, 2, 56], [109, 155, 106, 140], [28, 142, 120, 88], [68, 45, 123, 100], [155, 90, 114, 66], [41, 108, 67, 98], [25, 47, 65, 68]], ![[8, 135, 91, 70], [107, 18, 48, 54], [68, 48, 150, 118], [84, 84, 72, 149], [43, 34, 58, 3], [62, 74, 40, 125], [50, 96, 14, 128], [18, 131, 1, 19]], ![[0, 1], [38, 135, 77, 32], [82, 27, 50, 155], [149, 142, 101, 29], [19, 77, 4, 115], [89, 92, 42, 72], [77, 110, 75, 88], [8, 135, 91, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 12, 4], []]
 b := ![[], [], [47, 18, 61, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [147, 99, 39, 106, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13564357869, -3425028159, 4875166309, 21284391385, 11509868433]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5364808185, -6913074273, -1728418319, -6095888060, 11509868433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![479, 240, 116, -50, -72]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![479, 240, 116, -50, -72]] 
 ![![157, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![145, 0, 1, 0, 0], ![149, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![479, 240, 116, -50, -72], ![432, 197, 74, -134, -100], ![600, 192, -11, -512, -268], ![880, 236, -82, -933, -464], ![868, 136, -224, -1326, -617]]]
  hmulB := by decide  
  f := ![![![54211, -48200, 40312, -67870, 35016]], ![![48384, -43019, 35978, -60574, 31252]], ![![55255, -49128, 41093, -69182, 35692]], ![![46027, -40924, 34222, -57619, 29728]], ![![20318, -18064, 15116, -25446, 13127]]]
  g := ![![![-263, 240, 116, -50, -72], ![-100, 197, 74, -134, -100], ![375, 192, -11, -512, -268], ![839, 236, -82, -933, -464], ![1464, 136, -224, -1326, -617]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-54211, 48200, -40312, 67870, -35016]] ![![479, 240, 116, -50, -72]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2045, -239, -612, -2395, -1088]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![2045, -239, -612, -2395, -1088]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![137, 57, 133, 44, 1]] where
  M :=![![![2045, -239, -612, -2395, -1088], ![6528, 1788, -2022, -10759, -4790], ![28740, 4939, -6949, -45565, -21518], ![54792, 7809, -14216, -83948, -39146], ![78936, 12279, -21390, -121359, -56011]]]
  hmulB := by decide  
  f := ![![![16223, 8359, 4258, -821, -2092]], ![![12552, 6510, 3280, -599, -1642]], ![![9852, 4945, 2631, -611, -1198]], ![![9864, 5231, 2538, -372, -1354]], ![![28729, 14749, 7559, -1500, -3675]]]
  g := ![![![927, 379, 884, 279, -1088], ![4066, 1686, 3896, 1227, -4790], ![18262, 7555, 17515, 5529, -21518], ![33238, 13737, 31854, 10052, -39146], ![47561, 19662, 45571, 14375, -56011]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 4 2 7 [109, 133, 152, 70, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 97, 67, 133], [106, 154, 82, 35], [42, 74, 14, 158], [0, 1]]
 g := ![![[2, 119, 138, 61], [53, 53, 46, 100], [99, 60, 104], [128, 19, 47], [61, 153, 115], [93, 1], []], ![[82, 17, 45, 62, 58, 93], [104, 111, 46, 56, 162, 134], [145, 36, 81], [102, 37, 84], [140, 51, 62], [65, 47, 4, 83, 105, 88], [27, 136, 85]], ![[77, 62, 0, 54, 140, 146], [137, 53, 135, 159, 86, 14], [93, 141, 96], [119, 115, 126], [78, 24, 121], [21, 162, 33, 135, 153, 71], [29, 23, 84]], ![[74, 89, 126, 151, 156, 46], [115, 42, 150, 41, 91, 111], [64, 42, 9], [145, 44, 135], [28, 109, 90], [33, 108, 104, 156, 36, 56], [1, 66, 25]]]
 h' := ![![[108, 97, 67, 133], [91, 100, 126, 77], [156, 149, 153, 153], [29, 140, 97, 58], [17, 24, 88, 79], [132, 73, 75, 21], [0, 0, 1], [0, 1]], ![[106, 154, 82, 35], [17, 63, 43, 33], [161, 26, 97, 107], [127, 78, 9, 154], [18, 79, 146, 128], [114, 145, 54, 15], [82, 92, 85, 35], [108, 97, 67, 133]], ![[42, 74, 14, 158], [141, 84, 107, 96], [147, 94, 5, 149], [129, 3, 108, 111], [95, 145, 95, 17], [152, 92, 149, 11], [88, 41, 27, 4], [106, 154, 82, 35]], ![[0, 1], [18, 79, 50, 120], [28, 57, 71, 80], [141, 105, 112, 3], [61, 78, 160, 102], [159, 16, 48, 116], [25, 30, 50, 124], [42, 74, 14, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [101, 74, 78], []]
 b := ![[], [], [53, 19, 95, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 4
  hpos := by decide
  P := [109, 133, 152, 70, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-322164439950939, -190401461949450, 221241660687878, 535735190858348, 416168081181536]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-351761911422217, -146699276621454, -338215418015070, -109053131172572, 416168081181536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 705911761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16223, -8359, -4258, 821, 2092]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-16223, -8359, -4258, 821, 2092]] 
 ![![163, 0, 0, 0, 0], ![75, 1, 0, 0, 0], ![80, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-16223, -8359, -4258, 821, 2092], ![-12552, -6510, -3280, 599, 1642], ![-9852, -4945, -2631, 611, 1198], ![-9864, -5231, -2538, 372, 1354], ![-480, 15, -216, 249, -83]]]
  hmulB := by decide  
  f := ![![![-2045, 239, 612, 2395, 1088]], ![![-981, 99, 294, 1168, 530]], ![![-1180, 87, 343, 1455, 666]], ![![-1114, 43, 320, 1426, 654]], ![![-547, -68, 150, 818, 377]]]
  g := ![![![5460, -8359, -4258, 821, 2092], ![4250, -6510, -3280, 599, 1642], ![3237, -4945, -2631, 611, 1198], ![3409, -5231, -2538, 372, 1354], ![4, 15, -216, 249, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![2045, -239, -612, -2395, -1088]] ![![-16223, -8359, -4258, 821, 2092]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1457, -264, 423, 2257, 1100]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-1457, -264, 423, 2257, 1100]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![100, 32, 1, 0, 0], ![80, 92, 0, 1, 0], ![153, 92, 0, 0, 1]] where
  M :=![![![-1457, -264, 423, 2257, 1100], ![-6600, -837, 1570, 10126, 4514], ![-27084, -4754, 7719, 41920, 20252], ![-51732, -7186, 12912, 79545, 36202], ![-72498, -12240, 20193, 112077, 53575]]]
  hmulB := by decide  
  f := ![![![1157, 156, -2531, -311, 1130]], ![![-6780, 7389, 2376, -1124, -622]], ![![-584, 1450, -1037, -388, 544]], ![![-3160, 4122, 86, -765, 202]], ![![-2727, 4296, -1014, -920, 699]]]
  g := ![![![-2351, -1932, 423, 2257, 1100], ![-9966, -8371, 1570, 10126, 4514], ![-43420, -35758, 7719, 41920, 20252], ![-79314, -66282, 12912, 79545, 36202], ![-115299, -95200, 20193, 112077, 53575]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [28, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 166], [0, 1]]
 g := ![![[125, 6], [118, 7], [149, 98], [58], [31], [118, 49], [1]], ![[0, 161], [0, 160], [0, 69], [58], [31], [127, 118], [1]]]
 h' := ![![[7, 166], [36, 138], [3, 95], [31, 91], [94, 152], [36, 71], [139, 7], [0, 1]], ![[0, 1], [0, 29], [0, 72], [0, 76], [156, 15], [32, 96], [21, 160], [7, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [37, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [28, 160, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6507, -7094, 7539, 11532, 11316]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20445, -14074, 7539, 11532, 11316]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 266, -168, -88, 102]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-53, 266, -168, -88, 102]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![156, 149, 1, 0, 0], ![153, 49, 0, 1, 0], ![115, 84, 0, 0, 1]] where
  M :=![![![-53, 266, -168, -88, 102], ![-612, 509, 346, 20, -176], ![1056, -1506, 183, 2, 40], ![68, -2, -386, 271, -44], ![-736, 1034, 602, -702, 185]]]
  hmulB := by decide  
  f := ![![![10333, 5098, 2376, -1468, -1710]], ![![10260, 4295, 1254, -4600, -2936]], ![![18912, 8623, 3329, -5586, -4272]], ![![12643, 5969, 2520, -2897, -2526]], ![![12465, 5700, 2218, -3614, -2789]]]
  g := ![![![167, 126, -168, -88, 102], ![-224, -223, 346, 20, -176], ![-194, -193, 183, 2, 40], ![143, 287, -386, 271, -44], ![-51, -418, 602, -702, 185]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [140, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [154, 166], [0, 1]]
 g := ![![[49, 65], [89, 65], [12, 27], [32], [93], [107, 2], [1]], ![[39, 102], [79, 102], [162, 140], [32], [93], [81, 165], [1]]]
 h' := ![![[154, 166], [65, 30], [157, 137], [30, 148], [1, 115], [50, 60], [27, 154], [0, 1]], ![[0, 1], [9, 137], [46, 30], [110, 19], [9, 52], [105, 107], [29, 13], [154, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [135, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [140, 13, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91612, -253823, 264745, 199648, 384814]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-695758, -489868, 264745, 199648, 384814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-193, 0, 292, 32, -128]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-193, 0, 292, 32, -128]] 
 ![![167, 0, 0, 0, 0], ![153, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![148, 0, 0, 0, 1]] where
  M :=![![![-193, 0, 292, 32, -128], ![768, -901, -260, 140, 64], ![-384, 1080, -501, -256, 280], ![-432, 464, 188, -65, -56], ![960, -1584, 132, 312, -145]]]
  hmulB := by decide  
  f := ![![![-51047, -26144, -13452, 2720, 6496]], ![![-47001, -24077, -12384, 2500, 5984]], ![![-42378, -21688, -11173, 2272, 5384]], ![![-22489, -11536, -5920, 1183, 2872]], ![![-45268, -23152, -11940, 2440, 5743]]]
  g := ![![![-143, 0, 292, 32, -128], ![927, -901, -260, 140, 64], ![-714, 1080, -501, -256, 280], ![-505, 464, 188, -65, -56], ![1340, -1584, 132, 312, -145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-1457, -264, 423, 2257, 1100]] ![![-53, 266, -168, -88, 102]]
  ![![29353, -26090, 21839, -36771, 18962]] where
 M := ![![![29353, -26090, 21839, -36771, 18962]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![29353, -26090, 21839, -36771, 18962]] ![![-193, 0, 292, 32, -128]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, -4342, 3173, 2171, -2338]]]
 hmul := by decide  
 g := ![![![![1, -26, 19, 13, -14]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, 30, 104, 410, 174]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-137, 30, 104, 410, 174]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![141, 82, 1, 0, 0], ![172, 24, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![-137, 30, 104, 410, 174], ![-1044, -129, 336, 1766, 820], ![-4920, -686, 1301, 7694, 3532], ![-9052, -1378, 2448, 14083, 6580], ![-13276, -1954, 3422, 20448, 9437]]]
  hmulB := by decide  
  f := ![![![403, -4846, 4244, 1370, -2130]], ![![12780, -11601, -7720, 1322, 2740]], ![![6291, -9290, -215, 1712, -422]], ![![2136, -6398, 3176, 1543, -1748]], ![![463, -4124, 3430, 1146, -1733]]]
  g := ![![![-635, -106, 104, 410, 174], ![-2704, -405, 336, 1766, 820], ![-11617, -1688, 1301, 7694, 3532], ![-21412, -3122, 2448, 14083, 6580], ![-30887, -4470, 3422, 20448, 9437]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [69, 171, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 172], [0, 1]]
 g := ![![[10, 140], [121], [10, 52], [131, 1], [35], [78, 4], [1]], ![[117, 33], [121], [114, 121], [133, 172], [35], [86, 169], [1]]]
 h' := ![![[2, 172], [132, 113], [2, 11], [130, 158], [22, 172], [154, 143], [104, 2], [0, 1]], ![[0, 1], [12, 60], [24, 162], [100, 15], [20, 1], [94, 30], [108, 171], [2, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [159, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [69, 171, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5377, -27421, 24894, 339, 29790]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-44875, -12005, 24894, 339, 29790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3561, 1828, 953, -157, -436]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![3561, 1828, 953, -157, -436]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![67, 61, 1, 0, 0], ![44, 13, 0, 1, 0], ![28, 107, 0, 0, 1]] where
  M :=![![![3561, 1828, 953, -157, -436], ![2616, 1457, 718, 86, -314], ![1884, 870, 825, 356, 172], ![1156, 1182, 648, 1435, 190], ![-782, -476, 607, 1407, 1097]]]
  hmulB := by decide  
  f := ![![![29009, -40960, -2879, 7337, -1014]], ![![6084, 21509, -30744, -7384, 14674]], ![![12871, -7769, -11696, 171, 4696]], ![![7848, -8909, -2954, 1341, 800]], ![![8858, 6415, -19827, -3369, 9049]]]
  g := ![![![-238, -44, 953, -157, -436], ![-234, -57, 718, 86, -314], ![-427, -419, 825, 356, 172], ![-640, -447, 648, 1435, 190], ![-775, -1001, 607, 1407, 1097]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [141, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 172], [0, 1]]
 g := ![![[130, 9], [167], [24, 60], [162, 78], [15], [159, 64], [1]], ![[29, 164], [167], [158, 113], [94, 95], [15], [152, 109], [1]]]
 h' := ![![[8, 172], [48, 170], [76, 72], [167, 38], [158, 50], [71, 19], [32, 8], [0, 1]], ![[0, 1], [24, 3], [133, 101], [125, 135], [39, 123], [50, 154], [96, 165], [8, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [137, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [141, 165, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20229, -17852, 17864, -28878, 15114]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1903, -13580, 17864, -28878, 15114]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4909, 2515, 1263, -316, -662]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![4909, 2515, 1263, -316, -662]] 
 ![![173, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![60, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![4909, 2515, 1263, -316, -662], ![3972, 1976, 936, -499, -632], ![3792, 1639, 541, -1483, -998], ![4584, 1785, 364, -2610, -1532], ![2394, 393, -579, -3558, -1661]]]
  hmulB := by decide  
  f := ![![![46877, -37053, -33827, 3218, 12772]], ![![7686, -5756, -5866, 433, 2252]], ![![37170, -29763, -26439, 2665, 9938]], ![![16536, -13235, -11768, 1184, 4424]], ![![14400, -10821, -10953, 822, 4201]]]
  g := ![![![-1099, 2515, 1263, -316, -662], ![-696, 1976, 936, -499, -632], ![132, 1639, 541, -1483, -998], ![810, 1785, 364, -2610, -1532], ![2160, 393, -579, -3558, -1661]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-137, 30, 104, 410, 174]] ![![3561, 1828, 953, -157, -436]]
  ![![124451, 285550, 348077, 894281, 336978]] where
 M := ![![![124451, 285550, 348077, 894281, 336978]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![124451, 285550, 348077, 894281, 336978]] ![![4909, 2515, 1263, -316, -662]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![7971151979, 3176463207, 743174092, -4231055291, -2539993958]]]
 hmul := by decide  
 g := ![![![![46076023, 18361059, 4295804, -24456967, -14682046]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![441, -442, 373, -535, 350]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![441, -442, 373, -535, 350]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![12, 100, 110, 134, 1]] where
  M :=![![![441, -442, 373, -535, 350], ![-2100, 1653, -1350, 2684, -1070], ![6420, -6644, 5687, -7786, 5368], ![-9296, 6544, -5260, 12127, -3758], ![11662, -12842, 11077, -13929, 10787]]]
  hmulB := by decide  
  f := ![![![1127, 570, 291, -55, -144]], ![![864, 459, 224, -46, -110]], ![![660, 356, 189, -34, -92]], ![![692, 348, 182, -33, -90]], ![![1482, 774, 397, -75, -195]]]
  g := ![![![-21, -198, -213, -265, 350], ![60, 607, 650, 816, -1070], ![-324, -3036, -3267, -4062, 5368], ![200, 2136, 2280, 2881, -3758], ![-658, -6098, -6567, -8153, 10787]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 4 2 7 [146, 133, 103, 58, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 166, 122, 135], [121, 161, 42, 118], [93, 30, 15, 105], [0, 1]]
 g := ![![[46, 42, 14, 88], [8, 69, 4, 156], [46, 37, 12], [53, 103, 171], [150, 104, 72, 89], [121, 1], []], ![[163, 146, 9, 111, 110, 88], [77, 72, 79, 57, 178, 171], [74, 25, 42], [132, 76, 147], [140, 133, 14, 59, 135, 172], [145, 98, 37, 57, 111, 100], [10, 128, 146]], ![[41, 12, 176, 52, 80, 41], [160, 2, 110, 97, 55, 32], [107, 49, 65], [160, 148, 47], [66, 3, 64, 66, 114, 128], [29, 51, 154, 85, 31, 154], [24, 123, 141]], ![[52, 37, 178, 75, 120, 166], [45, 58, 25, 149, 112, 166], [25, 101, 14], [53, 92, 3], [14, 110, 82, 36, 18, 162], [118, 102, 138, 140, 136, 54], [157, 45, 106]]]
 h' := ![![[86, 166, 122, 135], [85, 84, 48, 154], [53, 102, 122, 131], [44, 128, 12, 38], [117, 111, 74, 156], [55, 50, 113, 39], [0, 0, 1], [0, 1]], ![[121, 161, 42, 118], [133, 26, 39, 78], [144, 171, 145, 7], [108, 79, 113, 159], [103, 10, 175, 133], [141, 5, 144, 17], [29, 121, 41, 112], [86, 166, 122, 135]], ![[93, 30, 15, 105], [153, 4, 61, 67], [17, 24, 30, 100], [31, 123, 126, 94], [168, 136, 116, 88], [91, 178, 145, 21], [39, 91, 69, 137], [121, 161, 42, 118]], ![[0, 1], [68, 65, 31, 59], [170, 61, 61, 120], [132, 28, 107, 67], [129, 101, 172, 160], [80, 125, 135, 102], [47, 146, 68, 109], [93, 30, 15, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [37, 132, 91], []]
 b := ![[], [], [53, 122, 99, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 4
  hpos := by decide
  P := [146, 133, 103, 58, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14078027443, -28633439897, 29312995927, 29035929701, 44787661585]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3081172997, -25181003343, -27359384237, -33365981691, 44787661585]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 1026625681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1127, 570, 291, -55, -144]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![1127, 570, 291, -55, -144]] 
 ![![179, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![134, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![73, 0, 0, 0, 1]] where
  M :=![![![1127, 570, 291, -55, -144], ![864, 459, 224, -46, -110], ![660, 356, 189, -34, -92], ![692, 348, 182, -33, -90], ![26, 14, -7, -3, 3]]]
  hmulB := by decide  
  f := ![![![441, -442, 373, -535, 350]], ![![210, -213, 180, -254, 170]], ![![366, -368, 311, -444, 292]], ![![224, -240, 204, -267, 198]], ![![245, -252, 214, -296, 203]]]
  g := ![![![-405, 570, 291, -55, -144], ![-320, 459, 224, -46, -110], ![-258, 356, 189, -34, -92], ![-250, 348, 182, -33, -90], ![-1, 14, -7, -3, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![441, -442, 373, -535, 350]] ![![1127, 570, 291, -55, -144]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![537, -487, -123, -136, -94]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![537, -487, -123, -136, -94]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![73, 87, 84, 1, 0], ![87, 120, 55, 0, 1]] where
  M :=![![![537, -487, -123, -136, -94], ![564, 514, -500, -1069, -272], ![1632, 1317, -55, -4201, -2138], ![5008, 435, -1128, -7488, -3604], ![7774, 787, -2621, -10938, -4753]]]
  hmulB := by decide  
  f := ![![![4513, 1945, 1315, -554, -372]], ![![2232, 2636, 76, 1159, -1108]], ![![6648, -2327, 3719, -5261, 2318]], ![![5969, 1000, 2279, -2079, 376]], ![![5713, 1937, 1845, -1151, -181]]]
  g := ![![![103, 125, 91, -136, -94], ![565, 697, 576, -1069, -272], ![2731, 3444, 2599, -4201, -2138], ![4780, 5991, 4564, -7488, -3604], ![6739, 8413, 6506, -10938, -4753]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [169, 163, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 55, 79], [171, 125, 102], [0, 1]]
 g := ![![[46, 146, 87], [1, 73], [8, 38, 143], [32, 101], [80, 70, 82], [19, 180, 1], []], ![[145, 80, 116, 132], [162, 145], [52, 130, 41, 81], [89, 14], [22, 22, 98, 167], [134, 3, 118, 136], [96, 87]], ![[0, 166, 91, 38], [55, 60], [89, 156, 85, 99], [31, 34], [130, 97, 38, 129], [11, 91, 174, 126], [73, 87]]]
 h' := ![![[9, 55, 79], [178, 18, 102], [96, 52, 39], [151, 0, 18], [55, 145, 61], [47, 149, 156], [0, 0, 1], [0, 1]], ![[171, 125, 102], [130, 89, 54], [143, 72, 114], [82, 22, 78], [10, 166, 75], [66, 120, 139], [147, 142, 125], [9, 55, 79]], ![[0, 1], [0, 74, 25], [173, 57, 28], [162, 159, 85], [40, 51, 45], [40, 93, 67], [71, 39, 55], [171, 125, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 146], []]
 b := ![[], [160, 108, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [169, 163, 1, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![257862, 123101, -149070, -420661, -295289]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![313018, 398648, 284129, -420661, -295289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, 133, -47, -30, 28]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-57, 133, -47, -30, 28]] 
 ![![181, 0, 0, 0, 0], ![142, 1, 0, 0, 0], ![108, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![-57, 133, -47, -30, 28], ![-168, 104, 150, -3, -60], ![360, -495, -49, 87, -6], ![76, -29, -86, -4, 36], ![-410, 451, 169, -66, -49]]]
  hmulB := by decide  
  f := ![![![-2345, -1243, -613, 72, 310]], ![![-1850, -980, -484, 57, 244]], ![![-1404, -747, -367, 39, 186]], ![![-2080, -1101, -546, 62, 272]], ![![-2079, -1108, -544, 54, 275]]]
  g := ![![![-75, 133, -47, -30, 28], ![-116, 104, 150, -3, -60], ![348, -495, -49, 87, -6], ![46, -29, -86, -4, 36], ![-355, 451, 169, -66, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -38, 19, 9, -10]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-3, -38, 19, 9, -10]] 
 ![![181, 0, 0, 0, 0], ![148, 1, 0, 0, 0], ![178, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![-3, -38, 19, 9, -10], ![60, -61, -48, 6, 18], ![-108, 156, -7, -30, 12], ![-40, 20, 26, -1, -10], ![134, -166, -37, 27, 7]]]
  hmulB := by decide  
  f := ![![![-211, 90, -69, 279, -16]], ![![-172, 71, -54, 228, -10]], ![![-226, 96, -73, 300, -16]], ![![-164, 56, -40, 221, 6]], ![![-240, 98, -73, 321, -11]]]
  g := ![![![15, -38, 19, 9, -10], ![76, -61, -48, 6, 18], ![-110, 156, -7, -30, 12], ![-32, 20, 26, -1, -10], ![146, -166, -37, 27, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![537, -487, -123, -136, -94]] ![![-57, 133, -47, -30, 28]]
  ![![35131, 43208, -96452, -18602, 44704]] where
 M := ![![![35131, 43208, -96452, -18602, 44704]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![35131, 43208, -96452, -18602, 44704]] ![![-3, -38, 19, 9, -10]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![19638319, -26810082, -2869031, 4694597, -232042]]]
 hmul := by decide  
 g := ![![![![108499, -148122, -15851, 25937, -1282]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2643, 1355, 686, -149, -348]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![2643, 1355, 686, -149, -348]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![8, 116, 75, 1, 0], ![51, 37, 141, 0, 1]] where
  M :=![![![2643, 1355, 686, -149, -348], ![2088, 1062, 520, -179, -298], ![1788, 853, 363, -407, -358], ![2008, 891, 322, -684, -490], ![616, 109, -140, -873, -409]]]
  hmulB := by decide  
  f := ![![![101, -87, 64, -119, 64]], ![![-384, 348, -270, 457, -238]], ![![1428, -1285, 1075, -1781, 914]], ![![324, -290, 255, -417, 212]], ![![1021, -917, 769, -1276, 655]]]
  g := ![![![113, 165, 319, -149, -348], ![98, 172, 293, -179, -298], ![122, 321, 426, -407, -358], ![170, 515, 632, -684, -490], ![149, 610, 644, -873, -409]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [21, 1, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 157, 16], [23, 33, 175], [0, 1]]
 g := ![![[14, 21, 117], [178, 66, 128], [129, 179, 97], [98, 67, 144], [89, 179, 170], [96, 111, 1], []], ![[188, 47, 70, 50], [180, 117, 7, 125], [179, 142, 81, 162], [181, 150, 189, 118], [126, 14, 20, 18], [64, 159, 16, 43], [15, 65]], ![[140, 155, 114, 111], [119, 105, 80, 126], [52, 48, 26, 187], [87, 7, 125, 182], [49, 143, 169, 111], [172, 24, 106, 31], [47, 65]]]
 h' := ![![[88, 157, 16], [82, 43, 58], [156, 62, 117], [43, 176, 111], [41, 130, 179], [85, 56, 19], [0, 0, 1], [0, 1]], ![[23, 33, 175], [32, 30, 119], [25, 6, 78], [132, 13, 176], [70, 99, 156], [49, 93, 186], [171, 85, 33], [88, 157, 16]], ![[0, 1], [101, 118, 14], [139, 123, 187], [48, 2, 95], [123, 153, 47], [120, 42, 177], [115, 106, 157], [23, 33, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 53], []]
 b := ![[], [160, 120, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [21, 1, 80, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1026273, -531526, 634382, 1686398, 1230532]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-404579, -1265358, -1567280, 1686398, 1230532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, 87, -64, 119, -64]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-101, 87, -64, 119, -64]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![97, 156, 1, 0, 0], ![18, 185, 0, 1, 0], ![138, 115, 0, 0, 1]] where
  M :=![![![-101, 87, -64, 119, -64], ![384, -348, 270, -457, 238], ![-1428, 1285, -1075, 1781, -914], ![1480, -1313, 1112, -1868, 962], ![-2720, 2401, -2030, 3435, -1773]]]
  hmulB := by decide  
  f := ![![![-2643, -1355, -686, 149, 348]], ![![-2088, -1062, -520, 179, 298]], ![![-3057, -1560, -775, 224, 422]], ![![-2282, -1161, -570, 191, 324]], ![![-3170, -1619, -808, 220, 433]]]
  g := ![![![67, -24, -64, 119, -64], ![-264, 77, 270, -457, 238], ![1031, -290, -1075, 1781, -914], ![-1076, 315, 1112, -1868, 962], ![1974, -589, -2030, 3435, -1773]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [169, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 190], [0, 1]]
 g := ![![[160, 26], [27, 2], [48, 46], [127, 109], [69, 25], [121, 39], [1]], ![[0, 165], [0, 189], [0, 145], [88, 82], [18, 166], [72, 152], [1]]]
 h' := ![![[82, 190], [21, 44], [101, 57], [120, 115], [181, 49], [179, 186], [22, 82], [0, 1]], ![[0, 1], [0, 147], [0, 134], [0, 76], [188, 142], [151, 5], [61, 109], [82, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [136, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [169, 109, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2065, -15095, 15589, 400, 20512]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22764, -25549, 15589, 400, 20512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![2643, 1355, 686, -149, -348]] ![![-101, 87, -64, 119, -64]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112659, 118933, 51374, -16595, -15914]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-112659, 118933, 51374, -16595, -15914]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![87, 159, 34, 1, 0], ![55, 40, 49, 0, 1]] where
  M :=![![![-112659, 118933, 51374, -16595, -15914], ![95484, -195180, 50964, 42043, -33190], ![199140, -97093, -204101, -4205, 84086], ![-69964, 122477, -16778, -24718, 14162], ![-59332, -103273, 193190, 40443, -90437]]]
  hmulB := by decide  
  f := ![![![-1603, -831, -300, 293, 354]], ![![-2124, -534, -238, 1517, 586]], ![![-3516, -1645, 1221, 4319, 3034]], ![![-3133, -1108, -112, 2198, 1198]], ![![-1829, -779, 193, 1557, 1031]]]
  g := ![![![11432, 17586, 7230, -16595, -15914], ![-8999, -28769, 1284, 42043, -33190], ![-21035, -14466, -21665, -4205, 84086], ![6744, 18063, 672, -24718, 14162], ![7234, -15110, 16837, 40443, -90437]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [39, 148, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [173, 97, 37], [76, 95, 156], [0, 1]]
 g := ![![[50, 191, 85], [15, 101], [95, 97], [55, 1], [35, 166], [8, 48], [1]], ![[169, 45, 85, 149], [44, 118], [2, 86], [123, 14], [4, 109], [161, 18], [18, 107, 74, 87]], ![[162, 49, 129, 182], [176, 25], [99, 55], [143, 168], [152, 81], [26, 157], [147, 57, 65, 106]]]
 h' := ![![[173, 97, 37], [144, 151, 144], [27, 124, 115], [79, 5, 26], [78, 97, 192], [51, 189, 72], [154, 45, 56], [0, 1]], ![[76, 95, 156], [129, 40, 160], [109, 37, 73], [90, 43, 146], [86, 162, 20], [186, 125, 130], [176, 132, 37], [173, 97, 37]], ![[0, 1], [116, 2, 82], [178, 32, 5], [76, 145, 21], [153, 127, 174], [171, 72, 184], [151, 16, 100], [76, 95, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156, 123], []]
 b := ![[], [5, 19, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [39, 148, 137, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7423, -5686, 3578, -3820, 3472]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![771, 2398, -190, -3820, 3472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1603, -831, -300, 293, 354]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-1603, -831, -300, 293, 354]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![80, 90, 1, 0, 0], ![7, 187, 0, 1, 0], ![100, 38, 0, 0, 1]] where
  M :=![![![-1603, -831, -300, 293, 354], ![-2124, -534, -238, 1517, 586], ![-3516, -1645, 1221, 4319, 3034], ![-7948, -711, 812, 10674, 4086], ![-7588, -2677, 3440, 12075, 7407]]]
  hmulB := by decide  
  f := ![![![-112659, 118933, 51374, -16595, -15914]], ![![95484, -195180, 50964, 42043, -33190]], ![![-1140, -42221, 44003, 12705, -21638]], ![![88067, -184164, 51156, 40006, -32662]], ![![-39880, 22659, 37654, -111, -15249]]]
  g := ![![![-78, -218, -300, 293, 354], ![-271, -1477, -238, 1517, 586], ![-2253, -5360, 1221, 4319, 3034], ![-2882, -11529, 812, 10674, 4086], ![-5741, -14776, 3440, 12075, 7407]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [72, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 192], [0, 1]]
 g := ![![[69, 126], [181], [144], [93], [145], [192], [50, 1]], ![[0, 67], [181], [144], [93], [145], [192], [100, 192]]]
 h' := ![![[50, 192], [88, 60], [162, 145], [84, 12], [5, 38], [122, 97], [67, 112], [0, 1]], ![[0, 1], [0, 133], [78, 48], [105, 181], [168, 155], [147, 96], [70, 81], [50, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [122, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [72, 143, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-38000, -9627, 16206, 56477, 33428]
  a := ![7, 21, 7, -50, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26283, -68910, 16206, 56477, 33428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-112659, 118933, 51374, -16595, -15914]] ![![-1603, -831, -300, 293, 354]]
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

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78955, 40578, 20759, -4085, -10124]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![78955, 40578, 20759, -4085, -10124]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![118, 35, 36, 1, 0], ![70, 103, 8, 0, 1]] where
  M :=![![![78955, 40578, 20759, -4085, -10124], ![60744, 31909, 15734, -2552, -8170], ![49020, 23052, 13623, -4370, -5104], ![46796, 26472, 11472, -349, -7338], ![4478, -1978, 2645, -3897, 1787]]]
  hmulB := by decide  
  f := ![![![979, -878, -601, 97, 214]], ![![-1284, 2125, -180, -422, 194]], ![![-1164, -100, 1883, 202, -844]], ![![150, -173, -48, 21, 8]], ![![-372, 805, -239, -181, 147]]]
  g := ![![![6445, 6225, 1263, -4085, -10124], ![4740, 4887, 878, -2552, -8170], ![4680, 3562, 1075, -4370, -5104], ![3054, 4033, 420, -349, -7338], ![1722, -252, 653, -3897, 1787]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [53, 148, 159, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 88, 123], [140, 108, 74], [0, 1]]
 g := ![![[106, 178, 16], [38, 10], [123, 168, 24], [80, 133], [151, 175], [87, 65], [1]], ![[38, 183, 166, 57], [114, 156], [104, 158, 10, 167], [112, 81], [4, 22], [119, 161], [54, 65, 71, 5]], ![[153, 71, 179, 119], [68, 54], [109, 44, 0, 77], [85, 63], [67, 25], [129, 109], [116, 26, 49, 192]]]
 h' := ![![[95, 88, 123], [83, 94, 4], [179, 111, 73], [69, 29, 157], [127, 166, 112], [168, 155, 136], [144, 49, 38], [0, 1]], ![[140, 108, 74], [81, 70, 174], [193, 50, 64], [145, 59, 35], [34, 76, 9], [7, 131, 66], [124, 71, 84], [95, 88, 123]], ![[0, 1], [172, 33, 19], [128, 36, 60], [91, 109, 5], [159, 152, 76], [19, 108, 192], [143, 77, 75], [140, 108, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 175], []]
 b := ![[], [25, 138, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [53, 148, 159, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1084573, -491650, 328713, -1467399, 49194]
  a := ![1, 6, 4, -15, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![866975, 232489, 267825, -1467399, 49194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -5, 5, -8, 4]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![7, -5, 5, -8, 4]] 
 ![![197, 0, 0, 0, 0], ![126, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![90, 0, 0, 0, 1]] where
  M :=![![![7, -5, 5, -8, 4], ![-24, 22, -18, 31, -16], ![96, -85, 71, -119, 62], ![-100, 89, -74, 126, -64], ![182, -163, 137, -228, 119]]]
  hmulB := by decide  
  f := ![![![7, 99, 119, -2, -50]], ![![6, 62, 76, -1, -32]], ![![3, 42, 48, -1, -20]], ![![0, 9, 10, 0, -4]], ![![4, 43, 55, 0, -23]]]
  g := ![![![0, -5, 5, -8, 4], ![-2, 22, -18, 31, -16], ![7, -85, 71, -119, 62], ![-8, 89, -74, 126, -64], ![13, -163, 137, -228, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 9, -3, 4, -6]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![3, 9, -3, 4, -6]] 
 ![![197, 0, 0, 0, 0], ![159, 1, 0, 0, 0], ![132, 0, 1, 0, 0], ![193, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![3, 9, -3, 4, -6], ![36, -16, 16, -41, 8], ![-48, 85, -73, 55, -82], ![160, -69, 52, -214, 12], ![-74, 163, -149, 66, -175]]]
  hmulB := by decide  
  f := ![![![-1957, 3945, -961, -842, 640]], ![![-1599, 3193, -755, -679, 508]], ![![-1260, 2577, -655, -553, 430]], ![![-1909, 3864, -953, -826, 632]], ![![-432, 817, -159, -170, 115]]]
  g := ![![![-8, 9, -3, 4, -6], ![41, -16, 16, -41, 8], ![-58, 85, -73, 55, -82], ![229, -69, 52, -214, 12], ![-63, 163, -149, 66, -175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![78955, 40578, 20759, -4085, -10124]] ![![7, -5, 5, -8, 4]]
  ![![137609, 20073, 53562, -50481, 10314]] where
 M := ![![![137609, 20073, 53562, -50481, 10314]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![137609, 20073, 53562, -50481, 10314]] ![![3, 9, -3, 4, -6]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-10275717, 10634454, -8163483, 14157011, -7467876]]]
 hmul := by decide  
 g := ![![![![-52161, 53982, -41439, 71863, -37908]]]]
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


lemma PB1705I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB1705I4 : PrimesBelowBoundCertificateInterval O 151 197 1705 where
  m := 9
  g := ![2, 2, 3, 3, 2, 3, 2, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB1705I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
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
    · exact ![705911761, 163]
    · exact ![27889, 27889, 167]
    · exact ![29929, 29929, 173]
    · exact ![1026625681, 179]
    · exact ![5929741, 181, 181]
    · exact ![6967871, 36481]
    · exact ![7189057, 37249]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
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
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I157N1, I163N1, I167N2, I173N2, I179N1, I181N1, I181N2, I197N1, I197N2]
  Il := ![[I157N1], [I163N1], [I167N2], [I173N2], [I179N1], [I181N1, I181N2], [], [], [I197N1, I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
