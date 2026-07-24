
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1328079, -403998, -271505, 338403, -624494]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![1328079, -403998, -271505, 338403, -624494]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![45, 175, 83, 3, 1]] where
  M :=![![![1328079, -403998, -271505, 338403, -624494], ![-4319146, 1313493, 882716, -1100606, 2030418], ![14042132, -4272050, -2871041, 3577960, -6603636], ![-11983394, 3642980, 2448182, -3053815, 5631514], ![1744078, -531034, -356902, 444330, -820821]]]
  hmulB := by decide  
  f := ![![![983, 44, -133, -29, 232]], ![![1798, 1319, 90, -196, -174]], ![![-1784, 1338, 641, -100, -1176]], ![![-3198, -348, 376, 117, -650]], ![![1011, 1715, 320, -218, -597]]]
  g := ![![![147891, 547148, 259103, 11115, -624494], ![-480844, -1778943, -842422, -36140, 2030418], ![1563848, 5785750, 2739853, 117532, -6603636], ![-1333676, -4934030, -2336520, -100243, 5631514], ![194377, 719159, 340559, 14607, -820821]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [161, 142, 114, 122, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 173, 55, 166], [151, 29, 130, 42], [91, 195, 14, 190], [0, 1]]
 g := ![![[158, 11, 135, 25], [20, 61, 143, 126], [117, 66, 82, 65], [124, 195, 175], [50, 62, 8], [44, 77, 1], []], ![[176, 14, 92, 7, 9, 164], [40, 126, 162, 105, 32, 30], [165, 139, 47, 68, 171, 75], [16, 68, 72], [52, 46, 62], [157, 94, 140], [24, 118, 122, 148, 133, 82]], ![[83, 112, 95, 20, 20, 60], [174, 41, 146, 14, 125, 34], [76, 67, 2, 6, 99, 12], [74, 52, 80], [94, 55, 66], [18, 59, 40], [71, 105, 82, 108, 60, 60]], ![[63, 86, 140, 85, 50, 152], [66, 133, 0, 44, 196, 146], [30, 87, 179, 185, 13, 170], [132, 172, 86], [174, 120, 26], [99, 28, 40], [26, 183, 3, 137, 4, 67]]]
 h' := ![![[34, 173, 55, 166], [163, 122, 20, 5], [68, 146, 145, 153], [116, 170, 182, 57], [141, 41, 154, 37], [80, 61, 8, 40], [0, 0, 0, 1], [0, 1]], ![[151, 29, 130, 42], [6, 55, 186, 63], [51, 88, 177, 141], [61, 104, 13, 98], [100, 190, 119, 79], [121, 154, 149, 103], [18, 60, 66, 109], [34, 173, 55, 166]], ![[91, 195, 14, 190], [46, 139, 116, 42], [167, 27, 74, 129], [166, 14, 151, 121], [90, 32, 96, 105], [189, 132, 165, 71], [163, 132, 174, 144], [151, 29, 130, 42]], ![[0, 1], [136, 82, 76, 89], [180, 137, 2, 174], [35, 110, 52, 122], [81, 135, 29, 177], [193, 51, 76, 184], [150, 7, 158, 144], [91, 195, 14, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [105, 113, 11], []]
 b := ![[], [], [120, 59, 14, 194], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 4
  hpos := by decide
  P := [161, 142, 114, 122, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![102119523598, 36178666319, 26648154046, 36405240734, 49156790367]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10602693683, -43046530894, -20368670585, -558116233, 49156790367]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-983, -44, 133, 29, -232]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-983, -44, 133, 29, -232]] 
 ![![199, 0, 0, 0, 0], ![181, 1, 0, 0, 0], ![74, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-983, -44, 133, 29, -232], ![-1798, -1319, -90, 196, 174], ![1784, -1338, -641, 100, 1176], ![3198, 348, -376, -117, 650], ![30, 1530, 416, -172, -765]]]
  hmulB := by decide  
  f := ![![![-1328079, 403998, 271505, -338403, 624494]], ![![-1186247, 360855, 242511, -302263, 557804]], ![![-564422, 171698, 115389, -143818, 265408]], ![![-814045, 247642, 166427, -207422, 382800]], ![![-269041, 81844, 55003, -68553, 126513]]]
  g := ![![![12, -44, 133, 29, -232], ![1061, -1319, -90, 196, 174], ![1168, -1338, -641, 100, 1176], ![-211, 348, -376, -117, 650], ![-1283, 1530, 416, -172, -765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![1328079, -403998, -271505, 338403, -624494]] ![![-983, -44, 133, 29, -232]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7311, 2213, 1491, -1866, 3458]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-7311, 2213, 1491, -1866, 3458]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![193, 113, 125, 1, 0], ![3, 69, 148, 0, 1]] where
  M :=![![![-7311, 2213, 1491, -1866, 3458], ![23932, -7210, -4876, 6065, -11196], ![-77438, 23677, 15861, -19759, 36390], ![66032, -20067, -13492, 16840, -31120], ![-9718, 2844, 1958, -2442, 4545]]]
  hmulB := by decide  
  f := ![![![7549, -2623, -327, 1028, -2548]], ![![-18328, 6356, 788, -2501, 6168]], ![![44342, -15449, -1935, 6031, -15006]], ![![23229, -8103, -1018, 3156, -7874]], ![![25187, -8785, -1103, 3423, -8535]]]
  g := ![![![1623, -121, -1313, -1866, 3458], ![-5275, 379, 4237, 6065, -11196], ![17189, -1206, -13744, -19759, 36390], ![-14648, 1063, 11788, 16840, -31120], ![2123, -165, -1732, -2442, 4545]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [6, 25, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 88, 71], [71, 122, 140], [0, 1]]
 g := ![![[19, 162, 171], [24, 210, 120], [140, 95], [134, 54], [158, 9, 36], [80, 161], [1]], ![[41, 107, 1, 78], [97, 178, 79, 70], [171, 203], [127, 188], [47, 36, 40, 117], [205, 199], [165, 117, 3, 55]], ![[176, 41, 167, 91], [86, 61, 66, 28], [47, 201], [36, 4], [136, 24, 28, 63], [158, 73], [92, 162, 66, 156]]]
 h' := ![![[97, 88, 71], [67, 76, 148], [167, 77, 139], [95, 114, 112], [107, 67, 138], [189, 77, 6], [205, 186, 168], [0, 1]], ![[71, 122, 140], [189, 72, 31], [134, 89, 59], [152, 178, 25], [131, 92, 71], [19, 1, 80], [163, 110, 153], [97, 88, 71]], ![[0, 1], [23, 63, 32], [80, 45, 13], [183, 130, 74], [71, 52, 2], [35, 133, 125], [136, 126, 101], [71, 122, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 159], []]
 b := ![[], [155, 204, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [6, 25, 43, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-144448331196, -67265665757, -49412614647, -53833191571, -93087645813]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![49879718386, 58952286933, 96951222332, -53833191571, -93087645813]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -4, 0, 0, 0]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-13, -4, 0, 0, 0]] 
 ![![211, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![208, 0, 0, 0, 1]] where
  M :=![![![-13, -4, 0, 0, 0], ![0, -13, -4, 0, 0], ![0, 4, -9, -12, 0], ![-8, -4, -12, -17, -24], ![-32, -4, 0, -4, -13]]]
  hmulB := by decide  
  f := ![![![-9823, 2988, 2000, -2496, 4608]], ![![-2456, 747, 500, -624, 1152]], ![![-1841, 560, 375, -468, 864]], ![![-5168, 1572, 1052, -1313, 2424]], ![![-9744, 2964, 1984, -2476, 4571]]]
  g := ![![![1, -4, 0, 0, 0], ![4, -13, -4, 0, 0], ![7, 4, -9, -12, 0], ![36, -4, -12, -17, -24], ![16, -4, 0, -4, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -9, -7, 0, 12]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![29, -9, -7, 0, 12]] 
 ![![211, 0, 0, 0, 0], ![201, 1, 0, 0, 0], ![111, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![130, 0, 0, 0, 1]] where
  M :=![![![29, -9, -7, 0, 12], ![96, 48, -2, -9, 0], ![-18, 89, 23, -15, -54], ![-128, 9, 14, -8, -48], ![-62, -84, -16, 8, 23]]]
  hmulB := by decide  
  f := ![![![-6175, 1943, 1023, -1398, 2706]], ![![-5793, 1823, 959, -1311, 2538]], ![![-3525, 1108, 588, -801, 1548]], ![![-1296, 409, 210, -290, 564]], ![![-3828, 1204, 636, -868, 1679]]]
  g := ![![![5, -9, -7, 0, 12], ![-42, 48, -2, -9, 0], ![-60, 89, 23, -15, -54], ![15, 9, 14, -8, -48], ![72, -84, -16, 8, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-7311, 2213, 1491, -1866, 3458]] ![![-13, -4, 0, 0, 0]]
  ![![-685, 71, 121, -2, -170]] where
 M := ![![![-685, 71, 121, -2, -170]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![-685, 71, 121, -2, -170]] ![![29, -9, -7, 0, 12]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-4431, 34604, 10128, -3798, -18568]]]
 hmul := by decide  
 g := ![![![![-21, 164, 48, -18, -88]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, -46, 13, 49, -32]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![197, -46, 13, 49, -32]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![121, 38, 97, 1, 0], ![207, 199, 176, 0, 1]] where
  M :=![![![197, -46, 13, 49, -32], ![-158, 201, 88, 56, 294], ![2464, 104, 281, 614, 336], ![2074, 1146, 678, 821, 1438], ![574, 348, 216, 246, 375]]]
  hmulB := by decide  
  f := ![![![14397, -4380, -2943, 3669, -6770]], ![![-46822, 14239, 9570, -11930, 22014]], ![![152252, -46308, -31121, 38794, -71580]], ![![65477, -19916, -13384, 16684, -30784]], ![![91829, -27933, -18771, 23399, -43173]]]
  g := ![![![4, 20, 4, 49, -32], ![-304, -271, -256, 56, 294], ![-634, -404, -531, 614, 336], ![-1771, -1418, -1489, 821, 1438], ![-479, -375, -402, 246, 375]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [159, 75, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [212, 130, 166], [121, 92, 57], [0, 1]]
 g := ![![[73, 116, 171], [127, 186, 199], [20, 203, 178], [115, 218, 162], [158, 88, 33], [138, 58], [1]], ![[53, 148, 38, 197], [131, 204, 89, 162], [161, 52, 116, 162], [100, 211, 20, 116], [109, 198, 62, 41], [102, 188], [103, 157, 67, 120]], ![[20, 103, 128, 123], [94, 132, 154, 214], [114, 219, 84, 154], [9, 205, 21, 96], [156, 92, 90, 107], [51, 100], [78, 97, 221, 103]]]
 h' := ![![[212, 130, 166], [100, 168, 174], [165, 120, 140], [1, 106, 160], [77, 62, 135], [217, 41, 207], [64, 148, 110], [0, 1]], ![[121, 92, 57], [209, 122, 188], [71, 143, 19], [45, 97, 204], [179, 76, 189], [91, 209, 205], [132, 7, 123], [212, 130, 166]], ![[0, 1], [10, 156, 84], [133, 183, 64], [19, 20, 82], [173, 85, 122], [81, 196, 34], [135, 68, 213], [121, 92, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 217], []]
 b := ![[], [153, 161, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [159, 75, 113, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47482010, -18489256, -13497321, -17151998, -25136026]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32426310, 25270654, 27238507, -17151998, -25136026]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![481, 141, -33, -28, 56]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![481, 141, -33, -28, 56]] 
 ![![223, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![117, 0, 1, 0, 0], ![205, 0, 0, 1, 0], ![164, 0, 0, 0, 1]] where
  M :=![![![481, 141, -33, -28, 56], ![392, 542, 90, -71, -168], ![-1486, 63, 239, 31, -426], ![-1480, -505, 82, 94, -136], ![614, -352, -188, 24, 339]]]
  hmulB := by decide  
  f := ![![![-1383, -1043, -643, -642, -1354]], ![![-290, -190, -120, -127, -248]], ![![-899, -626, -392, -403, -816]], ![![-1673, -1086, -687, -730, -1418]], ![![-1130, -806, -502, -512, -1049]]]
  g := ![![![-20, 141, -33, -28, 56], ![51, 542, 90, -71, -168], ![142, 63, 239, 31, -426], ![50, -505, 82, 94, -136], ![-110, -352, -188, 24, 339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50243, 15281, 10270, -12803, 23622]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-50243, 15281, 10270, -12803, 23622]] 
 ![![223, 0, 0, 0, 0], ![116, 1, 0, 0, 0], ![147, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![212, 0, 0, 0, 1]] where
  M :=![![![-50243, 15281, 10270, -12803, 23622], ![163370, -49694, -33398, 41629, -76818], ![-531286, 161579, 108591, -135383, 249774], ![453170, -137867, -92656, 115470, -213114], ![-66028, 20074, 13490, -16826, 31031]]]
  hmulB := by decide  
  f := ![![![-34761, -9817, 2500, 1991, -4290]], ![![-18218, -5284, 1272, 1059, -2178]], ![![-22439, -6502, 1569, 1304, -2688]], ![![-7781, -2174, 566, 443, -972]], ![![-33236, -9212, 2438, 1884, -4189]]]
  g := ![![![-34358, 15281, 10270, -12803, 23622], ![111733, -49694, -33398, 41629, -76818], ![-363292, 161579, 108591, -135383, 249774], ![309984, -137867, -92656, 115470, -213114], ![-45132, 20074, 13490, -16826, 31031]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![197, -46, 13, 49, -32]] ![![481, 141, -33, -28, 56]]
  ![![-34761, -9817, 2500, 1991, -4290]] where
 M := ![![![-34761, -9817, 2500, 1991, -4290]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-34761, -9817, 2500, 1991, -4290]] ![![-50243, 15281, 10270, -12803, 23622]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8513, 2582, 1738, -2170, 4012]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-8513, 2582, 1738, -2170, 4012]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![217, 128, 115, 1, 0], ![123, 89, 181, 0, 1]] where
  M :=![![![-8513, 2582, 1738, -2170, 4012], ![27756, -8409, -5666, 7056, -13020], ![-90048, 27458, 18425, -22962, 42336], ![76824, -23350, -15698, 19581, -36152], ![-11244, 3362, 2284, -2846, 5271]]]
  hmulB := by decide  
  f := ![![![677, -226, -26, 94, -220]], ![![-1572, 577, 82, -204, 564]], ![![4104, -1294, -117, 606, -1224]], ![![1831, -542, -37, 281, -508]], ![![3021, -927, -75, 454, -873]]]
  g := ![![![-137, -338, -2092, -2170, 4012], ![432, 1089, 6782, 7056, -13020], ![-1386, -3530, -22043, -22962, 42336], ![1209, 3030, 18837, 19581, -36152], ![-185, -447, -2751, -2846, 5271]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [144, 86, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 92, 149], [28, 134, 78], [0, 1]]
 g := ![![[222, 181, 203], [96, 7, 10], [197, 207], [83, 205], [160, 29], [0, 41, 176], [1]], ![[121, 155, 172, 38], [133, 177, 95, 15], [217, 219], [70, 90], [56, 30], [187, 25, 218, 52], [205, 140, 63, 105]], ![[173, 138, 141, 27], [52, 171, 14, 186], [210, 30], [28, 73], [141, 36], [125, 165, 8, 59], [48, 20, 72, 122]]]
 h' := ![![[39, 92, 149], [23, 106, 138], [116, 103, 64], [136, 113, 52], [114, 224, 81], [0, 77, 211], [83, 141, 67], [0, 1]], ![[28, 134, 78], [65, 61, 9], [212, 60, 88], [208, 135, 197], [181, 150, 192], [181, 131, 22], [62, 192, 23], [39, 92, 149]], ![[0, 1], [144, 60, 80], [140, 64, 75], [125, 206, 205], [170, 80, 181], [147, 19, 221], [58, 121, 137], [28, 134, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 74], []]
 b := ![[], [100, 155, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [144, 86, 160, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9456035404, 4561278161, 3358372909, 3545720284, 6337397125]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6781784637, -4463961508, -6834662288, 3545720284, 6337397125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![677, -226, -26, 94, -220]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![677, -226, -26, 94, -220]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![141, 108, 1, 0, 0], ![192, 205, 0, 1, 0], ![150, 113, 0, 0, 1]] where
  M :=![![![677, -226, -26, 94, -220], ![-1572, 577, 82, -204, 564], ![4104, -1294, -117, 606, -1224], ![-2016, 962, 202, -189, 992], ![-420, 230, 52, -34, 237]]]
  hmulB := by decide  
  f := ![![![-8513, 2582, 1738, -2170, 4012]], ![![27756, -8409, -5666, 7056, -13020]], ![![7521, -2276, -1535, 1908, -3516]], ![![18204, -5513, -3716, 4623, -8524]], ![![8142, -2465, -1662, 2066, -3807]]]
  g := ![![![85, 36, -26, 94, -220], ![-258, -133, 82, -204, 564], ![387, 112, -117, 606, -1224], ![-630, -415, 202, -189, 992], ![-162, -111, 52, -34, 237]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [80, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [220, 226], [0, 1]]
 g := ![![[54, 43], [205, 57], [34], [203], [97], [94, 53], [220, 1]], ![[207, 184], [33, 170], [34], [203], [97], [177, 174], [213, 226]]]
 h' := ![![[220, 226], [171, 161], [77, 113], [181, 48], [118, 138], [198, 209], [106, 196], [0, 1]], ![[0, 1], [179, 66], [194, 114], [72, 179], [60, 89], [97, 18], [96, 31], [220, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [222, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [80, 7, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21058, 78883, 63735, 15926, 123610]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-134647, -105891, 63735, 15926, 123610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-8513, 2582, 1738, -2170, 4012]] ![![677, -226, -26, 94, -220]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93207, 28138, 18903, -23783, 43518]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-93207, 28138, 18903, -23783, 43518]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![114, 25, 216, 90, 1]] where
  M :=![![![-93207, 28138, 18903, -23783, 43518], ![300578, -92375, -62114, 76444, -142698], ![-988696, 296438, 199071, -252596, 458664], ![825334, -259212, -174488, 209043, -399870], ![-125714, 35832, 23998, -32404, 55633]]]
  hmulB := by decide  
  f := ![![![323, -56, -3, 35, -120]], ![![-890, 241, 52, -94, 210]], ![![1492, -826, -93, 272, -564]], ![![-1122, 236, 14, -131, 426]], ![![1030, -687, -78, 212, -401]]]
  g := ![![![-22071, -4628, -40965, -17207, 43518], ![72350, 15175, 134326, 56416, -142698], ![-232648, -48778, -431757, -181364, 458664], ![202666, 42522, 376408, 158067, -399870], ![-28244, -5917, -52370, -22006, 55633]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 4 2 7 [53, 119, 58, 81, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 164, 108, 19], [70, 74, 66, 106], [38, 219, 55, 104], [0, 1]]
 g := ![![[198, 56, 201, 203], [171, 206, 178], [96, 39, 214, 70], [75, 175, 26], [156, 137, 68], [185, 91, 148, 1], []], ![[226, 21, 121, 117, 18, 68], [158, 24, 5], [35, 29, 16, 153], [136, 31, 151], [24, 162, 14], [17, 111, 71, 56, 176, 148], [33, 180, 148, 217, 149, 218]], ![[81, 17, 133, 97, 70, 128], [57, 80, 62], [41, 124, 65, 20, 74, 152], [175, 37, 187], [167, 46, 228], [67, 152, 139, 80, 207, 152], [181, 176, 217, 182, 130, 216]], ![[221, 9, 197, 154, 225, 3], [115, 65, 192], [96, 184, 45, 48, 228, 53], [100, 168, 209], [47, 37, 186], [182, 50, 225, 71, 94, 184], [143, 3, 103, 138, 121, 16]]]
 h' := ![![[40, 164, 108, 19], [78, 131, 192, 165], [179, 57, 98, 112], [138, 217, 210, 38], [137, 165, 5, 22], [42, 184, 138, 86], [0, 0, 0, 1], [0, 1]], ![[70, 74, 66, 106], [24, 107, 179, 219], [29, 115, 54, 163], [191, 39, 15], [206, 209, 205, 193], [44, 135, 101, 181], [192, 171, 133, 96], [40, 164, 108, 19]], ![[38, 219, 55, 104], [14, 223, 147, 88], [150, 210, 82, 73], [172, 203, 68, 6], [150, 198, 3, 88], [191, 201, 155, 107], [212, 98, 187, 223], [70, 74, 66, 106]], ![[0, 1], [5, 226, 169, 215], [72, 76, 224, 110], [118, 228, 165, 185], [193, 115, 16, 155], [169, 167, 64, 84], [119, 189, 138, 138], [38, 219, 55, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 196, 185], []]
 b := ![[], [], [192, 112, 81, 143], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 4
  hpos := by decide
  P := [53, 119, 58, 81, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-35142856521, 10664043950, 7508741386, -9176856910, 16828987206]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8531211345, -1790657800, -15840840590, -6654086050, 16828987206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 2750058481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![323, -56, -3, 35, -120]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![323, -56, -3, 35, -120]] 
 ![![229, 0, 0, 0, 0], ![147, 1, 0, 0, 0], ![146, 0, 1, 0, 0], ![119, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![323, -56, -3, 35, -120], ![-890, 241, 52, -94, 210], ![1492, -826, -93, 272, -564], ![-1122, 236, 14, -131, 426], ![6, 212, 8, -54, 85]]]
  hmulB := by decide  
  f := ![![![-93207, 28138, 18903, -23783, 43518]], ![![-58519, 17659, 11863, -14933, 27312]], ![![-63742, 19234, 12921, -16266, 29748]], ![![-44831, 13490, 9061, -11446, 20868]], ![![-24563, 7406, 4975, -6269, 11455]]]
  g := ![![![52, -56, -3, 35, -120], ![-197, 241, 52, -94, 210], ![600, -826, -93, 272, -564], ![-207, 236, 14, -131, 426], ![-135, 212, 8, -54, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-93207, 28138, 18903, -23783, 43518]] ![![323, -56, -3, 35, -120]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![765, 327, 220, 291, 430]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![765, 327, 220, 291, 430]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![37, 88, 201, 89, 1]] where
  M :=![![![765, 327, 220, 291, 430], ![4022, 1266, 980, 1381, 1746], ![16730, 6169, 4429, 6067, 8286], ![33058, 11363, 8450, 11696, 15478], ![9736, 3332, 2474, 3444, 4539]]]
  hmulB := by decide  
  f := ![![![25, 7, -2, -1, 2]], ![![14, 28, 6, -5, -6]], ![![-58, -3, 7, 7, -30]], ![![-90, -21, 8, 0, 2]], ![![-75, 1, 11, 4, -27]]]
  g := ![![![-65, -161, -370, -163, 430], ![-260, -654, -1502, -661, 1746], ![-1244, -3103, -7129, -3139, 8286], ![-2316, -5797, -13316, -5862, 15478], ![-679, -1700, -3905, -1719, 4539]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 4 2 7 [155, 50, 75, 231, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [157, 93, 0, 110], [93, 3, 92, 85], [218, 136, 141, 38], [0, 1]]
 g := ![![[5, 138, 154, 98], [200, 197, 124], [54, 89, 110], [39, 80, 60, 107], [37, 31, 50], [124, 162, 2, 1], []], ![[133, 109, 68, 86, 12, 81], [31, 219, 177], [57, 189, 19], [81, 229, 126, 83, 17, 182], [91, 104, 51], [141, 75, 95, 61, 44, 13], [131, 220, 160, 35, 208, 104]], ![[107, 99, 211, 155, 52, 197], [176, 220, 152], [1, 61, 8], [112, 30, 66, 199, 211, 184], [184, 79, 37], [194, 219, 60, 98, 87, 196], [41, 101, 69, 44, 193, 170]], ![[87, 150, 20, 190, 212, 101], [36, 115, 181], [103, 123, 50], [109, 159, 172, 22, 224, 204], [232, 179, 102], [170, 166, 7, 85, 23, 203], [144, 200, 18, 24, 120, 117]]]
 h' := ![![[157, 93, 0, 110], [8, 68, 222, 129], [187, 12, 209, 103], [13, 142, 27, 209], [38, 128, 86, 56], [119, 145, 231, 192], [0, 0, 0, 1], [0, 1]], ![[93, 3, 92, 85], [220, 72, 210, 146], [150, 197, 188, 118], [36, 145, 146, 46], [127, 177, 13, 122], [46, 219, 126, 135], [195, 201, 183, 109], [157, 93, 0, 110]], ![[218, 136, 141, 38], [129, 40, 165, 69], [71, 158, 206, 131], [172, 213, 216, 170], [114, 134, 115, 36], [21, 131, 59, 81], [210, 22, 40, 117], [93, 3, 92, 85]], ![[0, 1], [75, 53, 102, 122], [210, 99, 96, 114], [129, 199, 77, 41], [89, 27, 19, 19], [213, 204, 50, 58], [168, 10, 10, 6], [218, 136, 141, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [16, 105, 105], []]
 b := ![[], [], [46, 91, 89, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 4
  hpos := by decide
  P := [155, 50, 75, 231, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11592172219, 4085931632, 3010494906, 4128999403, 5548480311]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-831337336, -2078027192, -4773536685, -2101655572, 5548480311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 2947295521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -7, 2, 1, -2]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-25, -7, 2, 1, -2]] 
 ![![233, 0, 0, 0, 0], ![165, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![184, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![-25, -7, 2, 1, -2], ![-14, -28, -6, 5, 6], ![58, 3, -7, -7, 30], ![90, 21, -8, 0, -2], ![-36, 18, 10, -2, -15]]]
  hmulB := by decide  
  f := ![![![-765, -327, -220, -291, -430]], ![![-559, -237, -160, -212, -312]], ![![-190, -77, -53, -71, -102]], ![![-746, -307, -210, -280, -406]], ![![-137, -55, -38, -51, -73]]]
  g := ![![![4, -7, 2, 1, -2], ![16, -28, -6, 5, 6], ![1, 3, -7, -7, 30], ![-13, 21, -8, 0, -2], ![-11, 18, 10, -2, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![765, 327, 220, 291, 430]] ![![-25, -7, 2, 1, -2]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4621, -1540, -180, 626, -1606]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![4621, -1540, -180, 626, -1606]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![44, 109, 140, 177, 1]] where
  M :=![![![4621, -1540, -180, 626, -1606], ![-11596, 3821, 518, -1520, 3756], ![27008, -9878, -1257, 3790, -9120], ![-16656, 5626, 670, -2277, 5792], ![-3372, 1576, 178, -550, 1227]]]
  hmulB := by decide  
  f := ![![![51, 16, 12, 18, 22]], ![![212, 79, 58, 76, 108]], ![![1016, 338, 249, 358, 456]], ![![1864, 666, 490, 665, 904]], ![![2084, 731, 538, 741, 991]]]
  g := ![![![315, 726, 940, 1192, -1606], ![-740, -1697, -2198, -2788, 3756], ![1792, 4118, 5337, 6770, -9120], ![-1136, -2618, -3390, -4299, 5792], ![-240, -553, -718, -911, 1227]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 4 2 7 [147, 5, 127, 196, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 72, 189, 84], [71, 55, 88, 15], [131, 111, 201, 140], [0, 1]]
 g := ![![[84, 113, 195, 216], [53, 55, 216, 182], [72, 178, 39, 96], [120, 47, 109, 49], [191, 60, 198], [226, 49, 43, 1], []], ![[127, 85, 110, 53, 112, 43], [23, 32, 17, 94, 198, 82], [14, 93, 91, 0, 81, 156], [76, 59, 106, 47, 154, 19], [114, 107, 192], [57, 188, 28, 173, 172, 238], [11, 216, 150, 58, 160, 223]], ![[227, 26, 153, 30, 199, 98], [198, 210, 49, 185, 86, 133], [232, 104, 152, 201, 59, 71], [131, 47, 234, 169, 155, 5], [233, 80, 45], [77, 81, 183, 236, 200, 160], [152, 214, 182, 92, 180, 29]], ![[114, 78, 55, 192, 56, 14], [112, 18, 107, 172, 233, 13], [10, 46, 135, 2, 81, 152], [78, 142, 101, 160, 196, 86], [45, 85, 33], [35, 148, 19, 44, 181, 112], [141, 104, 102, 178, 101, 41]]]
 h' := ![![[80, 72, 189, 84], [96, 98, 10, 107], [171, 207, 191, 144], [46, 2, 8, 88], [126, 199, 211, 232], [238, 32, 104, 26], [0, 0, 0, 1], [0, 1]], ![[71, 55, 88, 15], [85, 212, 223, 184], [228, 100, 41, 40], [40, 32, 125, 233], [43, 150, 16, 224], [166, 200, 238, 131], [118, 4, 79, 21], [80, 72, 189, 84]], ![[131, 111, 201, 140], [107, 198, 182, 143], [47, 202, 42, 132], [106, 49, 38, 186], [167, 13, 88, 115], [140, 164, 204, 146], [11, 92, 8, 109], [71, 55, 88, 15]], ![[0, 1], [141, 209, 63, 44], [176, 208, 204, 162], [120, 156, 68, 210], [63, 116, 163, 146], [224, 82, 171, 175], [123, 143, 152, 108], [131, 111, 201, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 134, 72], []]
 b := ![[], [], [126, 146, 232, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 4
  hpos := by decide
  P := [147, 5, 127, 196, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2381136635, 805636622, 593457547, 843326823, 1090442985]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-190788095, -493944137, -636270127, -804037998, 1090442985]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 3262808641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 16, 12, 18, 22]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![51, 16, 12, 18, 22]] 
 ![![239, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![236, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![51, 16, 12, 18, 22], ![212, 79, 58, 76, 108], ![1016, 338, 249, 358, 456], ![1864, 666, 490, 665, 904], ![556, 192, 142, 198, 261]]]
  hmulB := by decide  
  f := ![![![4621, -1540, -180, 626, -1606]], ![![2523, -841, -98, 342, -878]], ![![4676, -1562, -183, 634, -1624]], ![![259, -86, -10, 35, -90]], ![![1494, -496, -58, 202, -519]]]
  g := ![![![-29, 16, 12, 18, 22], ![-141, 79, 58, 76, 108], ![-604, 338, 249, 358, 456], ![-1189, 666, 490, 665, 904], ![-344, 192, 142, 198, 261]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![4621, -1540, -180, 626, -1606]] ![![51, 16, 12, 18, 22]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37895, 11524, 7745, -9655, 17816]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-37895, 11524, 7745, -9655, 17816]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![182, 134, 227, 1, 0], ![39, 105, 50, 0, 1]] where
  M :=![![![-37895, 11524, 7745, -9655, 17816], ![123218, -37479, -25186, 31396, -57930], ![-400648, 121870, 81895, -102092, 188376], ![341798, -103956, -69864, 87091, -160702], ![-49786, 15138, 10176, -12684, 23403]]]
  hmulB := by decide  
  f := ![![![-57, 18, 3, -9, 2]], ![![-2, -67, -12, 2, -54]], ![![-428, -42, -49, -88, 12]], ![![-448, -64, -51, -89, -18]], ![![-99, -35, -15, -19, -21]]]
  g := ![![![4251, -2346, 5430, -9655, 17816], ![-13824, 7627, -17658, 31396, -57930], ![44952, -24802, 57419, -102092, 188376], ![-38346, 21160, -48981, 87091, -160702], ![5585, -3081, 7134, -12684, 23403]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [192, 205, 200, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [148, 192, 185], [134, 48, 56], [0, 1]]
 g := ![![[185, 112, 238], [214, 106], [179, 180], [69, 6], [108, 135, 150], [123, 55, 235], [1]], ![[109, 59, 22, 148], [100, 47], [184, 214], [73, 159], [119, 10, 204, 112], [15, 14, 204, 152], [227, 208, 142, 73]], ![[3, 77, 211, 203], [49, 239], [102, 144], [232, 49], [117, 43, 221, 78], [60, 122, 173, 93], [46, 125, 90, 168]]]
 h' := ![![[148, 192, 185], [217, 210, 210], [217, 184, 180], [107, 139, 105], [231, 144, 27], [2, 125, 135], [49, 36, 41], [0, 1]], ![[134, 48, 56], [178, 40, 7], [87, 217, 23], [179, 41, 148], [159, 125, 221], [29, 137, 203], [138, 161, 193], [148, 192, 185]], ![[0, 1], [72, 232, 24], [9, 81, 38], [132, 61, 229], [36, 213, 234], [32, 220, 144], [45, 44, 7], [134, 48, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 52], []]
 b := ![[], [91, 31, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [192, 205, 200, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51295780, 24003506, 17843791, 19103129, 33483330]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19632048, -25110230, -24866112, 19103129, 33483330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 11, 1, -4, 10]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-29, 11, 1, -4, 10]] 
 ![![241, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![-29, 11, 1, -4, 10], ![72, -24, -2, 9, -24], ![-174, 59, 5, -21, 54], ![96, -37, -2, 12, -32], ![30, -10, -2, 4, -9]]]
  hmulB := by decide  
  f := ![![![37, -11, -19, -10, -8]], ![![17, -5, -9, -5, -4]], ![![-2, -1, -1, -1, -2]], ![![1, -4, -5, -4, -4]], ![![19, -7, -11, -6, -5]]]
  g := ![![![-10, 11, 1, -4, 10], ![23, -24, -2, 9, -24], ![-54, 59, 5, -21, 54], ![33, -37, -2, 12, -32], ![9, -10, -2, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -17, -10, -11, -12]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-33, -17, -10, -11, -12]] 
 ![![241, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![121, 0, 0, 0, 1]] where
  M :=![![![-33, -17, -10, -11, -12], ![-118, -46, -40, -53, -66], ![-634, -197, -165, -239, -318], ![-1258, -423, -318, -448, -606], ![-400, -150, -96, -128, -173]]]
  hmulB := by decide  
  f := ![![![-188653, 57391, 38540, -48055, 88680]], ![![-129747, 39471, 26506, -33050, 60990]], ![![-100644, 30617, 20561, -25637, 47310]], ![![-83746, 25477, 17108, -21332, 39366]], ![![-95745, 29127, 19560, -24389, 45007]]]
  g := ![![![28, -17, -10, -11, -12], ![110, -46, -40, -53, -66], ![491, -197, -165, -239, -318], ![967, -423, -318, -448, -606], ![299, -150, -96, -128, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-37895, 11524, 7745, -9655, 17816]] ![![-29, 11, 1, -4, 10]]
  ![![188653, -57391, -38540, 48055, -88680]] where
 M := ![![![188653, -57391, -38540, 48055, -88680]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![188653, -57391, -38540, 48055, -88680]] ![![-33, -17, -10, -11, -12]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![-241, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![629, 301, -10, -39, -24]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![629, 301, -10, -39, -24]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![154, 134, 240, 1, 0], ![236, 73, 217, 0, 1]] where
  M :=![![![629, 301, -10, -39, -24], ![-270, 576, 194, -93, -234], ![-2058, -791, 103, 255, -558], ![-2094, -893, 56, 56, 246], ![1560, 40, -220, -30, 341]]]
  hmulB := by decide  
  f := ![![![763, -281, -40, 99, -276]], ![![-2010, 626, 56, -297, 594]], ![![4158, -1769, -321, 465, -1782]], ![![3356, -1527, -302, 344, -1554]], ![![3724, -1611, -299, 408, -1627]]]
  g := ![![![49, 29, 58, -39, -24], ![276, 120, 292, -93, -234], ![360, 23, 239, 255, -558], ![-274, -105, -266, 56, 246], ![-296, -83, -267, -30, 341]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [216, 20, 216, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 165, 111], [195, 85, 140], [0, 1]]
 g := ![![[103, 168, 135], [64, 93, 52], [71, 195], [168, 20, 12], [144, 156, 249], [28, 60, 221], [1]], ![[37, 153, 161, 171], [212, 34, 72, 215], [225, 175], [69, 219, 130, 159], [14, 32, 192, 43], [246, 205, 61, 193], [188, 56, 227, 183]], ![[34, 98, 151, 209], [69, 226, 85, 49], [245, 180], [170, 123, 147, 243], [169, 7, 118, 66], [42, 202, 159, 147], [28, 161, 209, 68]]]
 h' := ![![[91, 165, 111], [232, 42, 134], [129, 171, 141], [107, 250, 114], [20, 144, 152], [227, 4, 91], [35, 231, 35], [0, 1]], ![[195, 85, 140], [193, 241, 239], [12, 42, 93], [13, 26, 41], [68, 86, 39], [80, 229, 147], [123, 222, 2], [91, 165, 111]], ![[0, 1], [142, 219, 129], [126, 38, 17], [218, 226, 96], [145, 21, 60], [168, 18, 13], [60, 49, 214], [195, 85, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 155], []]
 b := ![[], [69, 176, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [216, 20, 216, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![84996960, 61596629, 45946747, 34609938, 88266867]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-103888104, -43902854, -109220512, 34609938, 88266867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, -91, -11, 36, -90]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![263, -91, -11, 36, -90]] 
 ![![251, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![188, 0, 0, 1, 0], ![146, 0, 0, 0, 1]] where
  M :=![![![263, -91, -11, 36, -90], ![-648, 220, 28, -87, 216], ![1554, -547, -69, 213, -522], ![-948, 329, 40, -130, 324], ![-210, 80, 10, -30, 71]]]
  hmulB := by decide  
  f := ![![![19, -139, -89, -6, -180]], ![![-2, -28, -18, -3, -36]], ![![-4, -13, -9, -3, -18]], ![![-20, -111, -72, -16, -144]], ![![4, -84, -54, -6, -109]]]
  g := ![![![45, -91, -11, 36, -90], ![-108, 220, 28, -87, 216], ![262, -547, -69, 213, -522], ![-162, 329, 40, -130, 324], ![-36, 80, 10, -30, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, -9, 22, 5, -38]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![-167, -9, 22, 5, -38]] 
 ![![251, 0, 0, 0, 0], ![233, 1, 0, 0, 0], ![178, 0, 1, 0, 0], ![201, 0, 0, 1, 0], ![191, 0, 0, 0, 1]] where
  M :=![![![-167, -9, 22, 5, -38], ![-294, -222, -16, 33, 30], ![306, -215, -107, 15, 198], ![542, 63, -62, -20, 106], ![-4, 252, 70, -28, -129]]]
  hmulB := by decide  
  f := ![![![-1201, -763, -564, -473, -1078]], ![![-1153, -717, -530, -452, -1012]], ![![-968, -597, -441, -379, -842]], ![![-1249, -698, -516, -479, -980]], ![![-989, -609, -450, -387, -859]]]
  g := ![![![17, -9, 22, 5, -38], ![167, -222, -16, 33, 30], ![114, -215, -107, 15, 198], ![-77, 63, -62, -20, 106], ![-163, 252, 70, -28, -129]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![629, 301, -10, -39, -24]] ![![263, -91, -11, 36, -90]]
  ![![-3149, -300, 399, 117, -714]] where
 M := ![![![-3149, -300, 399, 117, -714]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-3149, -300, 399, 117, -714]] ![![-167, -9, 22, 5, -38]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![802447, -163401, -164405, -2008, 294172]]]
 hmul := by decide  
 g := ![![![![3197, -651, -655, -8, 1172]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)


lemma PB696I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB696I5 : PrimesBelowBoundCertificateInterval O 197 251 696 where
  m := 9
  g := ![2, 3, 3, 2, 2, 2, 2, 3, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB696I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1568239201, 199]
    · exact ![9393931, 211, 211]
    · exact ![11089567, 223, 223]
    · exact ![11697083, 51529]
    · exact ![2750058481, 229]
    · exact ![2947295521, 233]
    · exact ![3262808641, 239]
    · exact ![13997521, 241, 241]
    · exact ![15813251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
  β := ![I199N1, I211N1, I211N2, I223N1, I223N2, I229N1, I233N1, I239N1, I241N1, I241N2, I251N1, I251N2]
  Il := ![[I199N1], [I211N1, I211N2], [I223N1, I223N2], [], [I229N1], [I233N1], [I239N1], [I241N1, I241N2], [I251N1, I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
