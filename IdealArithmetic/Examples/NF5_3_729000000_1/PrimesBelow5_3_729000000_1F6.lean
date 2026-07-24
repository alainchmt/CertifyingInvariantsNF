
import IdealArithmetic.Examples.NF5_3_729000000_1.RI5_3_729000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1249, 392, 84, 101, -225]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![1249, 392, 84, 101, -225]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![59, 148, 1, 0, 0], ![52, 129, 0, 1, 0], ![226, 92, 0, 0, 1]] where
  M :=![![![1249, 392, 84, 101, -225], ![-2250, -705, -136, -161, 381], ![3810, 1100, 159, 325, -585], ![540, 202, 22, -27, -54], ![2280, 706, 144, 190, -401]]]
  hmulB := by decide  
  f := ![![![-46447, -21964, -3594, -6469, 11307]], ![![113070, 53491, 8750, 15757, -27507]], ![![53381, 25256, 4131, 7440, -12984]], ![![47398, 22425, 3668, 6606, -11529]], ![![-986, -458, -76, -134, 247]]]
  g := ![![![163, -17, 84, 101, -225], ![-280, 20, -136, -161, 381], ![427, -41, 159, 325, -585], ![50, 21, 22, -27, -54], ![290, -32, 144, 190, -401]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [57, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 256], [0, 1]]
 g := ![![[164, 248], [144], [4], [255], [129], [64], [221], [1]], ![[0, 9], [144], [4], [255], [129], [64], [221], [1]]]
 h' := ![![[161, 256], [18, 209], [197, 245], [164, 255], [43, 189], [171, 30], [161, 8], [200, 161], [0, 1]], ![[0, 1], [0, 48], [64, 12], [99, 2], [146, 68], [118, 227], [164, 249], [164, 96], [161, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [234, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [57, 96, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25737, 27796, -571, 3521, 13092]
  a := ![0, -9, 16, 2, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11994, -6017, -571, 3521, 13092]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-120569, -57022, -9330, -16795, 29345]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-120569, -57022, -9330, -16795, 29345]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![99, 27, 1, 0, 0], ![221, 66, 0, 1, 0], ![111, 150, 0, 0, 1]] where
  M :=![![![-120569, -57022, -9330, -16795, 29345], ![293450, 138781, 22708, 40875, -71425], ![-714250, -337810, -55269, -99495, 173825], ![27100, 12808, 2096, 3773, -6602], ![-412520, -195112, -31922, -57468, 100389]]]
  hmulB := by decide  
  f := ![![![53847, 16714, 3488, 4455, -9595]], ![![-95950, -29803, -6246, -7955, 17135]], ![![11329, 3515, 731, 935, -2015]], ![![21731, 6740, 1400, 1794, -3863]], ![![-32359, -10056, -2114, -2687, 5788]]]
  g := ![![![4893, -12056, -9330, -16795, 29345], ![-11906, 29345, 22708, 40875, -71425], ![28993, -71411, -55269, -99495, 173825], ![-1095, 2714, 2096, 3773, -6602], ![16751, -41240, -31922, -57468, 100389]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [41, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 256], [0, 1]]
 g := ![![[103, 196], [95], [199], [239], [79], [215], [242], [1]], ![[192, 61], [95], [199], [239], [79], [215], [242], [1]]]
 h' := ![![[146, 256], [129, 14], [13, 159], [125, 126], [71, 204], [212, 183], [240, 230], [216, 146], [0, 1]], ![[0, 1], [117, 243], [97, 98], [17, 131], [43, 53], [202, 74], [153, 27], [201, 111], [146, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224]]
 b := ![[], [48, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [41, 111, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1649383, 2275303, -168003, 701128, 1473808]
  a := ![3, -125, 119, -69, -298]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1168328, -1013752, -168003, 701128, 1473808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, -38, -8, -10, 22]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![-123, -38, -8, -10, 22]] 
 ![![257, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![215, 0, 1, 0, 0], ![252, 0, 0, 1, 0], ![247, 0, 0, 0, 1]] where
  M :=![![![-123, -38, -8, -10, 22], ![220, 69, 14, 18, -38], ![-380, -110, -23, -30, 70], ![-40, -10, -2, -1, 8], ![-220, -62, -14, -16, 43]]]
  hmulB := by decide  
  f := ![![![1181, 558, 84, 162, -278]], ![![366, 173, 26, 50, -86]], ![![1015, 480, 73, 140, -240]], ![![1156, 546, 82, 159, -272]], ![![1151, 544, 82, 158, -271]]]
  g := ![![![7, -38, -8, -10, 22], ![-14, 69, 14, 18, -38], ![15, -110, -23, -30, 70], ![-2, -10, -2, -1, 8], ![5, -62, -14, -16, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![1249, 392, 84, 101, -225]] ![![-120569, -57022, -9330, -16795, 29345]]
  ![![-1181, -558, -84, -162, 278]] where
 M := ![![![-1181, -558, -84, -162, 278]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![-1181, -558, -84, -162, 278]] ![![-123, -38, -8, -10, 22]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71811, -51219, -6829, -16036, 22984]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-71811, -51219, -6829, -16036, 22984]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![125, 233, 235, 212, 1]] where
  M :=![![![-71811, -51219, -6829, -16036, 22984], ![229840, 130832, 19873, 39682, -73232], ![-732320, -436665, -61446, -133880, 164860], ![49940, -1413, 3047, -1955, -27226], ![-441520, -279751, -37323, -86626, 83605]]]
  hmulB := by decide  
  f := ![![![-5653, -3085, 289, 2598, -872]], ![![-8720, -11202, -11751, -3196, 14716]], ![![147160, 91205, 13102, -55450, -4460]], ![![-100, 16417, 31185, 18461, -41074]], ![![121025, 83353, 26573, -36272, -24471]]]
  g := ![![![-11197, -20557, -20563, -18588, 22984], ![35680, 65376, 65511, 59182, -73232], ![-81140, -147715, -147542, -133400, 164860], ![13130, 24115, 24339, 21939, -27226], ![-41415, -75132, -74846, -67722, 83605]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 4 2 8 [16, 226, 33, 226, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [254, 174, 143, 146], [164, 170, 189, 234], [145, 181, 194, 146], [0, 1]]
 g := ![![[17, 195, 82, 179], [235, 198, 111, 50], [24, 243, 94, 225], [67, 105, 68], [179, 34, 225], [82, 82, 54], [1], []], ![[229, 156, 258, 89, 170, 87], [80, 137, 164, 61, 43, 194], [61, 29, 237, 184, 67, 191], [184, 27, 8], [168, 129, 216], [8, 145, 100], [180, 165, 16], [104, 157, 13]], ![[103, 115, 1, 233, 234, 78], [86, 4, 217, 17, 255, 68], [104, 220, 135, 224, 242, 39], [5, 229, 173], [5, 105, 176], [237, 28, 99], [137, 60, 157], [79, 167, 52]], ![[17, 189, 200, 117, 184, 80], [120, 131, 252, 233, 164, 154], [58, 77, 175, 163, 204, 161], [190, 34, 74], [78, 81, 235], [245, 187, 187], [228, 34, 136], [155, 58, 13]]]
 h' := ![![[254, 174, 143, 146], [185, 180, 174, 53], [142, 226, 228, 239], [164, 119, 213, 248], [45, 197, 190, 130], [259, 12, 48, 15], [247, 37, 230, 37], [0, 0, 1], [0, 1]], ![[164, 170, 189, 234], [117, 221, 43, 100], [243, 177, 224, 219], [42, 102, 113, 124], [206, 175, 49, 220], [1, 247, 169, 74], [38, 151, 151, 10], [258, 45, 152, 259], [254, 174, 143, 146]], ![[145, 181, 194, 146], [91, 215, 138, 183], [159, 137, 104, 147], [92, 243, 21, 192], [232, 186, 261, 228], [7, 214, 8, 142], [88, 69, 164, 25], [121, 255, 4, 169], [164, 170, 189, 234]], ![[0, 1], [142, 173, 171, 190], [77, 249, 233, 184], [4, 62, 179, 225], [199, 231, 26, 211], [208, 53, 38, 32], [112, 6, 244, 191], [135, 226, 106, 98], [145, 181, 194, 146]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 170, 34], []]
 b := ![[], [], [250, 120, 235, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 4
  hpos := by decide
  P := [16, 226, 33, 226, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4268569162, 6025950554, 448435712, 1964749018, 2391853662]
  a := ![1, -9, 11, -3, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1120582276, -2096106284, -2135502566, -1920563602, 2391853662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 4784350561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5653, -3085, 289, 2598, -872]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-5653, -3085, 289, 2598, -872]] 
 ![![263, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![202, 0, 0, 0, 1]] where
  M :=![![![-5653, -3085, 289, 2598, -872], ![-8720, -11202, -11751, -3196, 14716], ![147160, 91205, 13102, -55450, -4460], ![-100, 16417, 31185, 18461, -41074], ![6560, 3951, 367, -2600, 87]]]
  hmulB := by decide  
  f := ![![![-71811, -51219, -6829, -16036, 22984]], ![![-10594, -7682, -1015, -2410, 3392]], ![![-23809, -16656, -2233, -5204, 7356]], ![![-35033, -25128, -3338, -7873, 11170]], ![![-56834, -40403, -5387, -12646, 17971]]]
  g := ![![![-218, -3085, 289, 2598, -872], ![-4539, -11202, -11751, -3196, 14716], ![12782, 91205, 13102, -55450, -4460], ![10740, 16417, 31185, 18461, -41074], ![495, 3951, 367, -2600, 87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-71811, -51219, -6829, -16036, 22984]] ![![-5653, -3085, 289, 2598, -872]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 36, 14, -19, -11]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![39, 36, 14, -19, -11]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![82, 266, 1, 0, 0], ![186, 223, 0, 1, 0], ![73, 268, 0, 0, 1]] where
  M :=![![![39, 36, 14, -19, -11], ![-110, -31, 82, 115, -125], ![-1250, -960, -501, 205, 565], ![620, 282, -142, -353, 242], ![-100, -58, -24, 8, 31]]]
  hmulB := by decide  
  f := ![![![-469, -64, -32, -9, 229]], ![![2290, 1881, 192, 605, 175]], ![![2128, 1862, 181, 603, 257]], ![![1584, 1529, 138, 500, 309]], ![![2167, 1882, 184, 609, 250]]]
  g := ![![![12, 13, 14, -19, -11], ![-71, -52, 82, 115, -125], ![-147, -241, -501, 205, 565], ![224, 193, -142, -353, 242], ![-7, -14, -24, 8, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [210, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [188, 268], [0, 1]]
 g := ![![[181, 170], [152], [96, 1], [133, 25], [45], [255], [105], [1]], ![[130, 99], [152], [15, 268], [260, 244], [45], [255], [105], [1]]]
 h' := ![![[188, 268], [47, 157], [15, 48], [46, 268], [107, 264], [45, 160], [261, 229], [59, 188], [0, 1]], ![[0, 1], [242, 112], [162, 221], [127, 1], [243, 5], [266, 109], [4, 40], [164, 81], [188, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [254]]
 b := ![[], [167, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [210, 81, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![352072, 436003, -39139, 91153, 282225]
  a := ![1, 45, -57, 10, 141]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-126377, -316418, -39139, 91153, 282225]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2481, 1174, 192, 346, -604]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![2481, 1174, 192, 346, -604]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![237, 61, 1, 0, 0], ![249, 217, 0, 1, 0], ![62, 99, 0, 0, 1]] where
  M :=![![![2481, 1174, 192, 346, -604], ![-6040, -2857, -468, -842, 1472], ![14720, 6970, 1141, 2050, -3580], ![-560, -262, -42, -75, 136], ![8500, 4026, 658, 1186, -2065]]]
  hmulB := by decide  
  f := ![![![-611, -190, -44, -54, 116]], ![![1160, 391, 88, 78, -208]], ![![-283, -81, -19, -30, 56]], ![![369, 139, 30, 13, -60]], ![![282, 99, 22, 16, -49]]]
  g := ![![![-341, -96, 192, 346, -604], ![830, 233, -468, -842, 1472], ![-2023, -569, 1141, 2050, -3580], ![73, 19, -42, -75, 136], ![-1170, -331, 658, 1186, -2065]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [22, 260, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 268], [0, 1]]
 g := ![![[183, 120], [5], [79, 93], [45, 149], [45], [61], [81], [1]], ![[187, 149], [5], [109, 176], [41, 120], [45], [61], [81], [1]]]
 h' := ![![[9, 268], [202, 89], [145, 143], [86, 30], [189, 35], [60, 109], [47, 64], [247, 9], [0, 1]], ![[0, 1], [196, 180], [87, 126], [87, 239], [235, 234], [234, 160], [85, 205], [59, 260], [9, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [114, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [22, 260, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41523, 37836, 4709, 509, 4310]
  a := ![-1, -6, 21, 13, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5459, -2924, 4709, 509, 4310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -62, -8, -19, 1]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-111, -62, -8, -19, 1]] 
 ![![269, 0, 0, 0, 0], ![211, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![101, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![-111, -62, -8, -19, 1], ![10, -159, -4, -57, -113], ![-1130, -1310, -101, -435, -455], ![-460, -628, -44, -211, -250], ![-1060, -1340, -98, -448, -503]]]
  hmulB := by decide  
  f := ![![![-2539, -1206, -174, -261, 553]], ![![-1971, -937, -136, -202, 430]], ![![-1293, -612, -89, -142, 286]], ![![-951, -450, -62, -96, 203]], ![![-813, -386, -56, -85, 178]]]
  g := ![![![59, -62, -8, -19, 1], ![183, -159, -4, -57, -113], ![1377, -1310, -101, -435, -455], ![669, -628, -44, -211, -250], ![1419, -1340, -98, -448, -503]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![39, 36, 14, -19, -11]] ![![2481, 1174, 192, 346, -604]]
  ![![2539, 1206, 174, 261, -553]] where
 M := ![![![2539, 1206, 174, 261, -553]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![2539, 1206, 174, 261, -553]] ![![-111, -62, -8, -19, 1]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![-269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![219, 127, 65, 50, -112]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![219, 127, 65, 50, -112]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![99, 258, 54, 1, 0], ![185, 10, 205, 0, 1]] where
  M :=![![![219, 127, 65, 50, -112], ![-1120, -638, -135, 152, 188], ![1880, 425, -906, -750, 1100], ![1660, 1189, 445, -467, -434], ![680, 291, 3, 52, -93]]]
  hmulB := by decide  
  f := ![![![389, 457, 35, 152, 160]], ![![1600, 2476, 161, 838, 1072]], ![![10720, 15035, 1034, 5060, 6100]], ![![3821, 5548, 374, 1871, 2306]], ![![8475, 11835, 816, 3982, 4787]]]
  g := ![![![59, -43, 75, 50, -112], ![-188, -154, -173, 152, 188], ![-470, 675, -686, -750, 1100], ![473, 465, 423, -467, -434], ![47, -45, 60, 52, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [166, 47, 239, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 150, 263], [135, 120, 8], [0, 1]]
 g := ![![[110, 93, 206], [256, 102, 156], [106, 224, 90], [154, 1, 134], [49, 22], [178, 67], [32, 1], []], ![[133, 265, 152, 133], [121, 234, 123, 6], [52, 64, 184, 251], [201, 39, 41, 264], [64, 55], [230, 213], [233, 37], [190, 64]], ![[189, 88, 154, 242], [85, 76, 64, 178], [174, 92, 61, 167], [251, 17, 122, 212], [211, 28], [176, 110], [261, 7], [174, 64]]]
 h' := ![![[168, 150, 263], [51, 123, 54], [19, 80, 88], [181, 184, 252], [0, 27, 26], [2, 5, 70], [108, 227, 164], [0, 0, 1], [0, 1]], ![[135, 120, 8], [186, 140, 76], [239, 188, 164], [60, 57, 42], [162, 92, 194], [156, 100, 230], [106, 162, 249], [207, 223, 120], [168, 150, 263]], ![[0, 1], [143, 8, 141], [189, 3, 19], [173, 30, 248], [221, 152, 51], [68, 166, 242], [4, 153, 129], [181, 48, 150], [135, 120, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [234, 13], []]
 b := ![[], [164, 215, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [166, 47, 239, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14575206, 16091194, 7110514, 1304126, -4781940]
  a := ![0, -2, -18, -26, 44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2841792, -1005734, 3383710, 1304126, -4781940]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 457, 35, 152, 160]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![389, 457, 35, 152, 160]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![139, 2, 1, 0, 0], ![189, 14, 0, 1, 0], ![138, 211, 0, 0, 1]] where
  M :=![![![389, 457, 35, 152, 160], ![1600, 2476, 161, 838, 1072], ![10720, 15035, 1034, 5060, 6100], ![5300, 7567, 515, 2549, 3110], ![11160, 15805, 1081, 5322, 6457]]]
  hmulB := by decide  
  f := ![![![219, 127, 65, 50, -112]], ![![-1120, -638, -135, 152, 188]], ![![111, 62, 29, 24, -52]], ![![101, 60, 40, 41, -70]], ![![-758, -431, -72, 144, 89]]]
  g := ![![![-204, -131, 35, 152, 160], ![-1207, -870, 161, 838, 1072], ![-7126, -4963, 1034, 5060, 6100], ![-3606, -2529, 515, 2549, 3110], ![-7513, -5252, 1081, 5322, 6457]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [270, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 270], [0, 1]]
 g := ![![[122, 206], [195, 22], [19, 128], [92, 28], [8], [7], [250], [1]], ![[51, 65], [169, 249], [188, 143], [256, 243], [8], [7], [250], [1]]]
 h' := ![![[122, 270], [195, 54], [19, 70], [92, 226], [76, 242], [136, 79], [251, 121], [1, 122], [0, 1]], ![[0, 1], [8, 217], [158, 201], [22, 45], [61, 29], [18, 192], [108, 150], [251, 149], [122, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [216, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [270, 149, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33416, 29615, 1751, 1165, 7935]
  a := ![13, -7, 18, 8, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5628, -6142, 1751, 1165, 7935]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![219, 127, 65, 50, -112]] ![![389, 457, 35, 152, 160]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47321, -22421, -3665, -6606, 11534]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-47321, -22421, -3665, -6606, 11534]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![80, 80, 1, 0, 0], ![191, 61, 0, 1, 0], ![228, 146, 0, 0, 1]] where
  M :=![![![-47321, -22421, -3665, -6606, 11534], ![115340, 54622, 8931, 16092, -28102], ![-281020, -133035, -21756, -39190, 68450], ![10780, 5085, 833, 1497, -2618], ![-162300, -76833, -12565, -22634, 39533]]]
  hmulB := by decide  
  f := ![![![-117, -57, 7, 68, -14]], ![![-140, -168, -275, -54, 394]], ![![-60, -55, -76, 0, 110]], ![![-111, -74, -53, 37, 74]], ![![-168, -133, -139, 28, 197]]]
  g := ![![![-4051, -3647, -3665, -6606, 11534], ![9872, 8886, 8931, 16092, -28102], ![-24050, -21645, -21756, -39190, 68450], ![921, 828, 833, 1497, -2618], ![-13890, -12501, -12565, -22634, 39533]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 2 2 8 [225, 274, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 276], [0, 1]]
 g := ![![[48, 261], [108], [7, 25], [88], [274, 254], [243], [9], [1]], ![[0, 16], [108], [82, 252], [88], [205, 23], [243], [9], [1]]]
 h' := ![![[3, 276], [166, 37], [87, 226], [104, 5], [121, 229], [7, 163], [125, 62], [52, 3], [0, 1]], ![[0, 1], [0, 240], [211, 51], [119, 272], [254, 48], [219, 114], [34, 215], [61, 274], [3, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [180, 157]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 2
  hpos := by decide
  P := [225, 274, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![732, -96, -352, -2405, 1438]
  a := ![-1, -3, -3, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![579, -127, -352, -2405, 1438]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, -1, 1, -1, -1]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![21, -1, 1, -1, -1]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![94, 63, 1, 0, 0], ![128, 167, 0, 1, 0], ![222, 174, 0, 0, 1]] where
  M :=![![![21, -1, 1, -1, -1], ![-10, 14, 1, 7, -7], ![-70, -75, -14, -25, 35], ![40, 15, 3, -1, -8], ![-40, -43, -5, -14, 15]]]
  hmulB := by decide  
  f := ![![![17, 3, 3, -1, -5]], ![![-50, -24, 1, 11, -11]], ![![-6, -5, 1, 2, -4]], ![![-22, -13, 2, 6, -9]], ![![-18, -13, 3, 6, -11]]]
  g := ![![![1, 1, 1, -1, -1], ![2, 0, 1, 7, -7], ![-12, -4, -14, -25, 35], ![6, 5, 3, -1, -8], ![-4, 0, -5, -14, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [100, 93, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [184, 276], [0, 1]]
 g := ![![[253, 241], [63], [16, 55], [214], [38, 228], [154], [62], [1]], ![[0, 36], [63], [164, 222], [214], [163, 49], [154], [62], [1]]]
 h' := ![![[184, 276], [37, 194], [62, 127], [196, 206], [78, 136], [102, 134], [199, 92], [177, 184], [0, 1]], ![[0, 1], [0, 83], [162, 150], [151, 71], [172, 141], [105, 143], [230, 185], [239, 93], [184, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159]]
 b := ![[], [165, 218]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : CertifiedPrimeIdeal' SI277N1 277 where
  n := 2
  hpos := by decide
  P := [100, 93, 1]
  hirr := P277P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![81588, 83580, -4172, -950, 45220]
  a := ![3, 10, -28, -15, 70]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34092, -26582, -4172, -950, 45220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N1 B_one_repr
lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 10, -2, -13, 3]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![23, 10, -2, -13, 3]] 
 ![![277, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![52, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![23, 10, -2, -13, 3], ![30, 33, 52, 5, -75], ![-750, -530, -57, 215, -45], ![-60, -148, -148, -99, 162], ![-120, -148, -10, -32, -55]]]
  hmulB := by decide  
  f := ![![![-1238581, -586750, -95920, -172871, 301851]], ![![-588272, -278683, -45558, -82107, 143367]], ![![-245647, -116360, -19023, -34282, 59862]], ![![-231496, -109668, -17928, -32311, 56418]], ![![-444588, -210608, -34430, -62050, 108347]]]
  g := ![![![-3, 10, -2, -13, 3], ![0, 33, 52, 5, -75], ![239, -530, -57, 215, -45], ![60, -148, -148, -99, 162], ![98, -148, -10, -32, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-47321, -22421, -3665, -6606, 11534]] ![![21, -1, 1, -1, -1]]
  ![![-1238581, -586750, -95920, -172871, 301851]] where
 M := ![![![-1238581, -586750, -95920, -172871, 301851]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![-1238581, -586750, -95920, -172871, 301851]] ![![23, 10, -2, -13, 3]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1, I277N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
    exact isPrimeI277N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0 ⊙ MulI277N1)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4321, 1342, 280, 357, -769]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![4321, 1342, 280, 357, -769]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![110, 148, 1, 0, 0], ![58, 41, 0, 1, 0], ![156, 16, 0, 0, 1]] where
  M :=![![![4321, 1342, 280, 357, -769], ![-7690, -2381, -498, -633, 1373], ![13730, 4290, 891, 1145, -2425], ![1420, 456, 92, 123, -242], ![7980, 2508, 518, 670, -1399]]]
  hmulB := by decide  
  f := ![![![-279, -138, -22, -17, 59]], ![![590, 243, -28, 33, -43]], ![![200, 74, -23, 9, 1]], ![![28, 7, -8, 2, 5]], ![![-124, -64, -14, -8, 31]]]
  g := ![![![259, -151, 280, 357, -769], ![-464, 268, -498, -633, 1373], ![810, -483, 891, 1145, -2425], ![78, -51, 92, 123, -242], ![464, -282, 518, 670, -1399]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [182, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [261, 280], [0, 1]]
 g := ![![[207, 169], [256], [16], [253, 58], [89, 225], [236], [119], [1]], ![[199, 112], [256], [16], [217, 223], [85, 56], [236], [119], [1]]]
 h' := ![![[261, 280], [89, 268], [218, 265], [38, 4], [100, 45], [256, 15], [226, 123], [99, 261], [0, 1]], ![[0, 1], [68, 13], [257, 16], [239, 277], [43, 236], [237, 266], [14, 158], [218, 20], [261, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [120, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [182, 20, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16383, 16070, -970, -377, 8572]
  a := ![1, 5, -13, -6, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4243, 135, -970, -377, 8572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6471, -2007, -419, -534, 1154]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-6471, -2007, -419, -534, 1154]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![203, 129, 1, 0, 0], ![107, 127, 0, 1, 0], ![178, 230, 0, 0, 1]] where
  M :=![![![-6471, -2007, -419, -534, 1154], ![11540, 3594, 749, 960, -2050], ![-20500, -6305, -1336, -1670, 3710], ![-2060, -601, -133, -165, 394], ![-11860, -3611, -767, -954, 2163]]]
  hmulB := by decide  
  f := ![![![-80231, -37943, -6207, -11176, 19526]], ![![195260, 92344, 15111, 27210, -47530]], ![![29987, 14182, 2322, 4182, -7302]], ![![57763, 27318, 4471, 8051, -14062]], ![![108022, 51087, 8361, 15056, -26297]]]
  g := ![![![-248, -518, -419, -534, 1154], ![433, 913, 749, 960, -2050], ![-822, -1691, -1336, -1670, 3710], ![-98, -189, -133, -165, 394], ![-495, -1000, -767, -954, 2163]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [74, 278, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 280], [0, 1]]
 g := ![![[224, 112], [69], [280], [241, 136], [72, 253], [231], [9], [1]], ![[279, 169], [69], [280], [87, 145], [269, 28], [231], [9], [1]]]
 h' := ![![[3, 280], [77, 127], [94, 161], [150, 53], [11, 184], [12, 147], [33, 145], [207, 3], [0, 1]], ![[0, 1], [177, 154], [15, 120], [28, 228], [1, 97], [172, 134], [187, 136], [216, 278], [3, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188]]
 b := ![[], [140, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [74, 278, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2842, 1298, 1175, 763, -2250]
  a := ![4, -1, 4, 3, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![296, 962, 1175, 763, -2250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2101, -3082, -206, -1040, -1302]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![-2101, -3082, -206, -1040, -1302]] 
 ![![281, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![265, 0, 1, 0, 0], ![173, 0, 0, 1, 0], ![139, 0, 0, 0, 1]] where
  M :=![![![-2101, -3082, -206, -1040, -1302], ![-13020, -18493, -1264, -6228, -7542], ![-75420, -108530, -7351, -36580, -44910], ![-38400, -55030, -3738, -18543, -22668], ![-79720, -114518, -7766, -38594, -47297]]]
  hmulB := by decide  
  f := ![![![-54821, -17070, -3722, -4692, 10014]], ![![-424, -129, -28, -40, 78]], ![![-52345, -16300, -3541, -4460, 9540]], ![![-33833, -10544, -2304, -2891, 6186]], ![![-27479, -8556, -1864, -2350, 5017]]]
  g := ![![![1515, -3082, -206, -1040, -1302], ![8974, -18493, -1264, -6228, -7542], ![52945, -108530, -7351, -36580, -44910], ![26801, -55030, -3738, -18543, -22668], ![55827, -114518, -7766, -38594, -47297]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![4321, 1342, 280, 357, -769]] ![![-6471, -2007, -419, -534, 1154]]
  ![![-9829591, -3052197, -637079, -811973, 1751445]] where
 M := ![![![-9829591, -3052197, -637079, -811973, 1751445]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-9829591, -3052197, -637079, -811973, 1751445]] ![![-2101, -3082, -206, -1040, -1302]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-5358389, -7841867, -526313, -2645615, -3275055]]]
 hmul := by decide  
 g := ![![![![-19069, -27907, -1873, -9415, -11655]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1, I281N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
    exact isPrimeI281N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0 ⊙ MulI281N1)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80091, -24864, -5188, -6621, 14269]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-80091, -24864, -5188, -6621, 14269]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![206, 78, 1, 0, 0], ![261, 7, 0, 1, 0], ![142, 40, 0, 0, 1]] where
  M :=![![![-80091, -24864, -5188, -6621, 14269], ![142690, 44307, 9268, 11817, -25457], ![-254570, -79180, -16601, -20965, 45445], ![-25900, -8018, -1718, -2235, 4694], ![-147560, -45826, -9568, -12186, 26295]]]
  hmulB := by decide  
  f := ![![![16087, 8620, 1266, 2603, -3037]], ![![-30370, -8387, -2226, -2091, 12581]], ![![3784, 4298, 345, 1425, 1257]], ![![14139, 7831, 1118, 2379, -2448]], ![![4098, 3422, 348, 1102, 291]]]
  g := ![![![2440, -511, -5188, -6621, 14269], ![-4367, 908, 9268, 11817, -25457], ![7717, -1609, -16601, -20965, 45445], ![865, -163, -1718, -2235, 4694], ![4488, -940, -9568, -12186, 26295]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 2 2 8 [92, 192, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 282], [0, 1]]
 g := ![![[39, 40], [174, 256], [157], [280, 23], [60, 211], [271], [74], [1]], ![[0, 243], [264, 27], [157], [109, 260], [17, 72], [271], [74], [1]]]
 h' := ![![[91, 282], [123, 235], [38, 16], [276, 231], [140, 227], [38, 87], [241, 178], [191, 91], [0, 1]], ![[0, 1], [0, 48], [79, 267], [72, 52], [138, 56], [31, 196], [25, 105], [265, 192], [91, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [249, 206]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 2
  hpos := by decide
  P := [92, 192, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![871845, 942872, -28011, 89873, 468054]
  a := ![7, -44, 91, 25, -228]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-294270, -57327, -28011, 89873, 468054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![443, -264, -980, -769, 1329]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![443, -264, -980, -769, 1329]] 
 ![![283, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![217, 0, 1, 0, 0], ![143, 0, 0, 1, 0], ![162, 0, 0, 0, 1]] where
  M :=![![![443, -264, -980, -769, 1329], ![13290, 9393, 3372, -3715, -3285], ![-32850, -9700, 17253, 24295, -25575], ![-32220, -25058, -12502, 6451, 13662], ![-1240, -258, 856, 1038, -1235]]]
  hmulB := by decide  
  f := ![![![8321, -1612, 86, -757, 3087]], ![![1344, -91, 26, -63, 453]], ![![6329, -1068, 61, -518, 2658]], ![![4441, -570, 64, -302, 1629]], ![![4874, -626, 60, -330, 2017]]]
  g := ![![![420, -264, -980, -769, 1329], ![-175, 9393, 3372, -3715, -3285], ![-9542, -9700, 17253, 24295, -25575], ![2111, -25058, -12502, 6451, 13662], ![-440, -258, 856, 1038, -1235]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -5, -1, 4, 0]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![-7, -5, -1, 4, 0]] 
 ![![283, 0, 0, 0, 0], ![175, 1, 0, 0, 0], ![222, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-7, -5, -1, 4, 0], ![0, -8, -17, -14, 24], ![240, 165, 58, -60, -60], ![-60, -15, 37, 47, -54], ![20, 11, 3, -2, -5]]]
  hmulB := by decide  
  f := ![![![23291, 7273, 1513, 1938, -4176]], ![![14255, 4451, 926, 1186, -2556]], ![![18534, 5787, 1204, 1542, -3324]], ![![10807, 3374, 702, 899, -1938]], ![![893, 278, 58, 74, -161]]]
  g := ![![![2, -5, -1, 4, 0], ![24, -8, -17, -14, 24], ![-117, 165, 58, -60, -60], ![-40, -15, 37, 47, -54], ![-8, 11, 3, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2

def I283N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -30, -54, -31, 71]] i)))

def SI283N3: IdealEqSpanCertificate' Table ![![-3, -30, -54, -31, 71]] 
 ![![283, 0, 0, 0, 0], ![271, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![-3, -30, -54, -31, 71], ![710, 477, 134, -225, -115], ![-1150, -110, 1037, 1105, -1465], ![-1820, -1336, -556, 453, 574], ![-40, 4, 50, 46, -69]]]
  hmulB := by decide  
  f := ![![![-43081, -19810, -3296, -5803, 10393]], ![![-40887, -18797, -3128, -5506, 9866]], ![![-22023, -10120, -1685, -2964, 5324]], ![![-421, -186, -32, -54, 107]], ![![-12366, -5676, -946, -1662, 2995]]]
  g := ![![![36, -30, -54, -31, 71], ![-486, 477, 134, -225, -115], ![-16, -110, 1037, 1105, -1465], ![1383, -1336, -556, 453, 574], ![-10, 4, 50, 46, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N3 : Nat.card (O ⧸ I283N3) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N3)

lemma isPrimeI283N3 : Ideal.IsPrime I283N3 := prime_ideal_of_norm_prime hp283.out _ NI283N3
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-80091, -24864, -5188, -6621, 14269]] ![![443, -264, -980, -769, 1329]]
  ![![137987, 147688, 129214, 16430, -157916]] where
 M := ![![![137987, 147688, 129214, 16430, -157916]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![137987, 147688, 129214, 16430, -157916]] ![![-7, -5, -1, 4, 0]]
  ![![25901331, 17465345, 4979891, -8180482, -4305968]] where
 M := ![![![25901331, 17465345, 4979891, -8180482, -4305968]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N2 : IdealMulLeCertificate' Table 
  ![![25901331, 17465345, 4979891, -8180482, -4305968]] ![![-3, -30, -54, -31, 71]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![21656532267, 17918041705, 10438880915, -3133697205, -11863545365]]]
 hmul := by decide  
 g := ![![![![76524849, 63314635, 36886505, -11073135, -41920655]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2, I283N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
    exact isPrimeI283N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1 ⊙ MulI283N2)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![817, 564, 66, 177, -43]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![817, 564, 66, 177, -43]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![271, 225, 191, 1, 0], ![163, 109, 260, 0, 1]] where
  M :=![![![817, 564, 66, 177, -43], ![-430, 851, -10, 311, 1019], ![10190, 11040, 937, 3665, 2885], ![3100, 4602, 298, 1569, 1978], ![8980, 10798, 832, 3596, 3501]]]
  hmulB := by decide  
  f := ![![![-36531, -11344, -2368, -3017, 6509]], ![![65090, 20211, 4216, 5373, -11593]], ![![-115930, -35980, -7501, -9585, 20645]], ![![-59417, -18439, -3845, -4916, 10583]], ![![-99211, -30791, -6420, -8204, 17669]]]
  g := ![![![-137, -118, -77, 177, -43], ![-856, -615, -1107, 311, 1019], ![-4960, -3850, -4946, 3665, 2885], ![-2541, -1925, -2777, 1569, 1978], ![-5243, -4027, -5448, 3596, 3501]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [222, 89, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 102, 232], [223, 190, 61], [0, 1]]
 g := ![![[203, 50, 65], [292, 46], [230, 187, 143], [54, 71], [256, 38], [40, 250, 22], [279, 1], []], ![[92, 188, 103, 222], [161, 25], [167, 97, 280, 216], [72, 193], [216, 97], [74, 137, 253, 189], [77, 61], [215, 205]], ![[227, 162, 137, 124], [211, 10], [248, 99, 266, 172], [28, 234], [37, 202], [31, 72, 227, 1], [227, 149], [93, 205]]]
 h' := ![![[56, 102, 232], [153, 66, 247], [215, 192, 94], [71, 263, 27], [199, 137, 207], [203, 166, 193], [178, 145, 107], [0, 0, 1], [0, 1]], ![[223, 190, 61], [71, 144, 126], [241, 154, 288], [48, 68, 221], [260, 256, 208], [63, 279, 174], [41, 241, 58], [235, 105, 190], [56, 102, 232]], ![[0, 1], [241, 83, 213], [72, 240, 204], [121, 255, 45], [188, 193, 171], [28, 141, 219], [211, 200, 128], [76, 188, 102], [223, 190, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 210], []]
 b := ![[], [25, 260, 234], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [222, 89, 14, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54164074, -64925298, -5371292, -12687894, -21900666]
  a := ![1, -9, 23, 9, -57]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23734006, 17669022, 27686654, -12687894, -21900666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27103, 8433, 1757, 2245, -4815]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![27103, 8433, 1757, 2245, -4815]] 
 ![![293, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![287, 0, 1, 0, 0], ![180, 0, 0, 1, 0], ![225, 0, 0, 0, 1]] where
  M :=![![![27103, 8433, 1757, 2245, -4815], ![-48150, -14832, -3117, -3935, 8655], ![86550, 27535, 5628, 7385, -14955], ![9120, 3173, 601, 875, -1392], ![50500, 16383, 3293, 4422, -8509]]]
  hmulB := by decide  
  f := ![![![4331, -211, -5113, -4915, 7125]], ![![864, 148, -659, -765, 945]], ![![3479, -494, -4725, -4320, 6540]], ![![2100, -587, -3399, -2931, 4668]], ![![3295, -172, -3912, -3753, 5450]]]
  g := ![![![-519, 8433, 1757, 2245, -4815], ![786, -14832, -3117, -3935, 8655], ![-2217, 27535, 5628, 7385, -14955], ![-481, 3173, 601, 875, -1392], ![-1584, 16383, 3293, 4422, -8509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-687, -214, -44, -57, 121]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![-687, -214, -44, -57, 121]] 
 ![![293, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![161, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![-687, -214, -44, -57, 121], ![1210, 367, 78, 101, -221], ![-2210, -730, -157, -205, 385], ![-220, -80, -12, -33, 26], ![-1300, -444, -86, -122, 205]]]
  hmulB := by decide  
  f := ![![![-2518339, -1191014, -194874, -350795, 612937]], ![![-829987, -392531, -64226, -115614, 202010]], ![![-1434713, -678528, -111021, -199850, 349194]], ![![-479388, -226720, -37096, -66777, 116678]], ![![-1112378, -526084, -86078, -154950, 270741]]]
  g := ![![![53, -214, -44, -57, 121], ![-87, 367, 78, 101, -221], ![199, -730, -157, -205, 385], ![28, -80, -12, -33, 26], ![128, -444, -86, -122, 205]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![817, 564, 66, 177, -43]] ![![27103, 8433, 1757, 2245, -4815]]
  ![![141591, 198975, 13707, 66964, 80038]] where
 M := ![![![141591, 198975, 13707, 66964, 80038]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![141591, 198975, 13707, 66964, 80038]] ![![-687, -214, -44, -57, 121]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![-5587217, -8176751, -548789, -2758595, -3414915]]]
 hmul := by decide  
 g := ![![![![-19069, -27907, -1873, -9415, -11655]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1, I293N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
    exact isPrimeI293N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0 ⊙ MulI293N1)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-573503, -178082, -37170, -47375, 102185]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-573503, -178082, -37170, -47375, 102185]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![76, 302, 154, 1, 0], ![154, 298, 203, 0, 1]] where
  M :=![![![-573503, -178082, -37170, -47375, 102185], ![1021850, 317307, 66228, 84415, -182065], ![-1820650, -565310, -118003, -150395, 324425], ![-186500, -57892, -12084, -15401, 33238], ![-1056320, -327972, -68462, -87248, 188235]]]
  hmulB := by decide  
  f := ![![![-3669, -1734, -284, -515, 895]], ![![8950, 4241, 706, 1255, -2195]], ![![-21950, -10410, -1719, -2975, 5335]], ![![-3112, -1478, -238, -385, 738]], ![![-7708, -3656, -597, -1013, 1856]]]
  g := ![![![-41399, -53166, -43925, -47375, 102185], ![73760, 94721, 78259, 84415, -182065], ![-131440, -168810, -139464, -150395, 324425], ![-13468, -17302, -14292, -15401, 33238], ![-76266, -97958, -80925, -87248, 188235]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [240, 77, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 86, 91], [278, 220, 216], [0, 1]]
 g := ![![[55, 172, 133], [231, 183, 119], [103, 259], [56, 299], [291, 163, 302], [290, 0, 53], [279, 1], []], ![[271, 212, 196, 157], [204, 183, 37, 31], [23, 16], [18, 54], [12, 176, 281, 51], [142, 116, 68, 207], [155, 201], [219, 299]], ![[234, 289, 298, 83], [224, 296, 107, 255], [11, 76], [37, 272], [294, 200, 77, 10], [152, 228, 232, 259], [17, 28], [94, 299]]]
 h' := ![![[1, 86, 91], [127, 96, 161], [230, 294, 160], [151, 45, 167], [156, 119, 216], [89, 9, 223], [273, 74, 93], [0, 0, 1], [0, 1]], ![[278, 220, 216], [65, 165, 255], [121, 36, 247], [280, 174, 4], [84, 218, 19], [87, 30, 145], [107, 39, 178], [245, 272, 220], [1, 86, 91]], ![[0, 1], [77, 46, 198], [193, 284, 207], [206, 88, 136], [45, 277, 72], [30, 268, 246], [162, 194, 36], [78, 35, 86], [278, 220, 216]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213, 55], []]
 b := ![[], [150, 15, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [240, 77, 28, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7010330, 10114369, 165737, 3438600, 5085418]
  a := ![3, 9, -9, 7, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3379406, -8285985, -5087031, 3438600, 5085418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3669, 1734, 284, 515, -895]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![3669, 1734, 284, 515, -895]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![80, 302, 1, 0, 0], ![40, 6, 0, 1, 0], ![69, 215, 0, 0, 1]] where
  M :=![![![3669, 1734, 284, 515, -895], ![-8950, -4241, -706, -1255, 2195], ![21950, 10410, 1719, 2975, -5335], ![-860, -396, -32, -85, 154], ![12580, 5944, 974, 1746, -3067]]]
  hmulB := by decide  
  f := ![![![573503, 178082, 37170, 47375, -102185]], ![![-1021850, -317307, -66228, -84415, 182065]], ![![-849830, -263892, -55079, -70205, 151415]], ![![55360, 17190, 3588, 4573, -9864]], ![![-583289, -181125, -37804, -48186, 103925]]]
  g := ![![![72, 343, 284, 515, -895], ![-175, -832, -706, -1255, 2195], ![435, 2021, 1719, 2975, -5335], ![-18, -76, -32, -85, 154], ![249, 1175, 974, 1746, -3067]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P1 : CertificateIrreducibleZModOfList' 307 2 2 8 [234, 200, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 306], [0, 1]]
 g := ![![[258, 164], [133, 150], [134], [145], [281, 24], [270, 251], [90], [1]], ![[0, 143], [219, 157], [134], [145], [86, 283], [111, 56], [90], [1]]]
 h' := ![![[107, 306], [192, 222], [198, 173], [213, 286], [251, 51], [62, 192], [233, 78], [73, 107], [0, 1]], ![[0, 1], [0, 85], [289, 134], [115, 21], [182, 256], [37, 115], [290, 229], [163, 200], [107, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [202, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N1 : CertifiedPrimeIdeal' SI307N1 307 where
  n := 2
  hpos := by decide
  P := [234, 200, 1]
  hirr := P307P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![307083, 297042, 4240, -2119, 111234]
  a := ![3, -18, 56, 31, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24829, -81062, 4240, -2119, 111234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N1 B_one_repr
lemma NI307N1 : Nat.card (O ⧸ I307N1) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N1
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-573503, -178082, -37170, -47375, 102185]] ![![3669, 1734, 284, 515, -895]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![-307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0)


lemma PB1321I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB1321I6 : PrimesBelowBoundCertificateInterval O 251 307 1321 where
  m := 9
  g := ![3, 2, 3, 2, 3, 3, 4, 3, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB1321I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0, I281N1, I281N2]
    · exact ![I283N0, I283N1, I283N2, I283N3]
    · exact ![I293N0, I293N1, I293N2]
    · exact ![I307N0, I307N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC257
    · exact PBC263
    · exact PBC269
    · exact PBC271
    · exact PBC277
    · exact PBC281
    · exact PBC283
    · exact PBC293
    · exact PBC307
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![66049, 66049, 257]
    · exact ![4784350561, 263]
    · exact ![72361, 72361, 269]
    · exact ![19902511, 73441]
    · exact ![76729, 76729, 277]
    · exact ![78961, 78961, 281]
    · exact ![80089, 283, 283, 283]
    · exact ![25153757, 293, 293]
    · exact ![28934443, 94249]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
      exact NI257N2
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
      exact NI281N2
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
      exact NI283N3
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
  β := ![I257N2, I263N1, I269N2, I277N2, I281N2, I283N1, I283N2, I283N3, I293N1, I293N2]
  Il := ![[I257N2], [I263N1], [I269N2], [], [I277N2], [I281N2], [I283N1, I283N2, I283N3], [I293N1, I293N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
