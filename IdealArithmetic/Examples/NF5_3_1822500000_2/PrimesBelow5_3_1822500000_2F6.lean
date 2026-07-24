
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-628609, 221878, 2650, -32964, -86394]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-628609, 221878, 2650, -32964, -86394]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![77, 160, 37, 1, 0], ![28, 2, 134, 0, 1]] where
  M :=![![![-628609, 221878, 2650, -32964, -86394], ![-299952, -642199, -197432, -263246, -888612], ![2372976, 1379652, 578919, 858060, 2837732], ![-6325248, -2573172, -1249804, -1921793, -6313120], ![1320504, 200958, 171610, 289956, 937097]]]
  hmulB := by decide  
  f := ![![![-689, -4214, 1858, 2600, 7830]], ![![-720, -8759, 5496, 6578, 19300]], ![![10416, -16548, 27535, 25596, 74324]], ![![1075, -9270, 8497, 9019, 26338]], ![![5276, -9060, 14396, 13500, 39249]]]
  g := ![![![16843, 22058, 49802, -32964, -86394], ![174518, 168305, 500454, -263246, -888612], ![-557020, -550916, -1600877, 858060, 2837732], ![1238989, 1235564, 3563481, -1921793, -6313120], ![-183832, -187028, -529680, 289956, 937097]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [238, 33, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 222, 171], [104, 34, 86], [0, 1]]
 g := ![![[169, 173, 129], [168, 68], [96, 199], [162, 173], [40, 169], [228, 193], [231, 1], []], ![[154, 4, 130, 212], [214, 62], [240, 30], [79, 70], [65, 129], [138, 22], [112, 128], [49, 200]], ![[218, 117, 69, 250], [100, 168], [185, 11], [46, 88], [1, 32], [44, 111], [67, 197], [134, 200]]]
 h' := ![![[127, 222, 171], [126, 183, 30], [77, 184, 117], [201, 231, 126], [174, 76, 78], [106, 126, 244], [20, 106, 129], [0, 0, 1], [0, 1]], ![[104, 34, 86], [93, 41, 188], [216, 144, 233], [252, 73, 95], [251, 16, 228], [185, 27, 30], [167, 4, 153], [98, 232, 34], [127, 222, 171]], ![[0, 1], [80, 33, 39], [218, 186, 164], [72, 210, 36], [212, 165, 208], [129, 104, 240], [249, 147, 232], [255, 25, 222], [104, 34, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182, 63], []]
 b := ![[], [7, 211, 189], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [238, 33, 26, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3265428746, -410200914, -4249345726, -3179151720, -9239683738]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1946460694, 2049546466, 5258742758, -3179151720, -9239683738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-689, -4214, 1858, 2600, 7830]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-689, -4214, 1858, 2600, 7830]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![136, 220, 1, 0, 0], ![149, 52, 0, 1, 0], ![145, 105, 0, 0, 1]] where
  M :=![![![-689, -4214, 1858, 2600, 7830], ![-720, -8759, 5496, 6578, 19300], ![10416, -16548, 27535, 25596, 74324], ![59136, -44196, 142508, 118151, 327968], ![-19080, 24522, -52934, -46320, -130263]]]
  hmulB := by decide  
  f := ![![![-628609, 221878, 2650, -32964, -86394]], ![![-299952, -642199, -197432, -263246, -888612]], ![![-580184, -426960, -165353, -239452, -795356]], ![![-449749, -11314, -43274, -79853, -254450]], ![![-472073, -136411, -78500, -125022, -408149]]]
  g := ![![![-6911, -5332, 1858, 2600, 7830], ![-17614, -13955, 5496, 6578, 19300], ![-71304, -59180, 27535, 25596, 74324], ![-328723, -280064, 142508, 118151, 327968], ![128287, 108001, -52934, -46320, -130263]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [115, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 256], [0, 1]]
 g := ![![[153, 128], [88], [208], [117], [157], [46], [26], [1]], ![[84, 129], [88], [208], [117], [157], [46], [26], [1]]]
 h' := ![![[138, 256], [162, 34], [60, 49], [74, 145], [57, 173], [76, 97], [212, 118], [142, 138], [0, 1]], ![[0, 1], [228, 223], [140, 208], [38, 112], [30, 84], [98, 160], [48, 139], [168, 119], [138, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167]]
 b := ![[], [21, 212]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [115, 119, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2478967, 626173, 2479504, 1817797, 5598252]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5514910, -4775123, 2479504, 1817797, 5598252]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-628609, 221878, 2650, -32964, -86394]] ![![-689, -4214, 1858, 2600, 7830]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-481, -1939, 626, 1019, 3094]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-481, -1939, 626, 1019, 3094]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![86, 21, 1, 0, 0], ![35, 171, 0, 1, 0], ![43, 42, 0, 0, 1]] where
  M :=![![![-481, -1939, 626, 1019, 3094], ![-888, -3871, 1286, 2072, 6302], ![-2064, -7878, 2439, 4054, 12276], ![-2736, -15252, 5716, 8723, 26732], ![2088, 9723, -3374, -5323, -16235]]]
  hmulB := by decide  
  f := ![![![577, 59, 648, 523, 1484]], ![![2040, -227, 4106, 3054, 8434]], ![![418, -1, 649, 498, 1390]], ![![1837, -160, 3502, 2620, 7250]], ![![269, -20, 504, 378, 1047]]]
  g := ![![![-848, -1214, 626, 1019, 3094], ![-1730, -2471, 1286, 2072, 6302], ![-3352, -4821, 2439, 4054, 12276], ![-7411, -10455, 5716, 8723, 26732], ![4474, 6360, -3374, -5323, -16235]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [200, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 262], [0, 1]]
 g := ![![[256, 96], [93, 2], [244, 223], [34], [207], [179], [124], [1]], ![[0, 167], [0, 261], [0, 40], [34], [207], [179], [124], [1]]]
 h' := ![![[85, 262], [73, 126], [118, 110], [33, 111], [235, 214], [254, 162], [209, 210], [63, 85], [0, 1]], ![[0, 1], [0, 137], [0, 153], [0, 152], [15, 49], [85, 101], [175, 53], [187, 178], [85, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [249]]
 b := ![[], [166, 256]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [200, 178, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![475, -732, 1076, 761, 2151]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-803, -927, 1076, 761, 2151]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -17, 5, 8, 24]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-1, -17, 5, 8, 24]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![33, 59, 1, 0, 0], ![157, 234, 0, 1, 0], ![138, 172, 0, 0, 1]] where
  M :=![![![-1, -17, 5, 8, 24], ![0, -25, 15, 21, 64], ![-24, -72, 36, 41, 118], ![120, -102, 207, 198, 578], ![-24, 75, -80, -83, -243]]]
  hmulB := by decide  
  f := ![![![49, -11, -3, 4, 10]], ![![48, 55, 51, 37, 132]], ![![15, 10, 10, 8, 28]], ![![83, 47, 50, 40, 140]], ![![54, 29, 30, 25, 87]]]
  g := ![![![-18, -24, 5, 8, 24], ![-48, -64, 15, 21, 64], ![-91, -122, 36, 41, 118], ![-447, -601, 207, 198, 578], ![187, 251, -80, -83, -243]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [57, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [237, 262], [0, 1]]
 g := ![![[245, 6], [94, 11], [210, 36], [50], [2], [43], [150], [1]], ![[89, 257], [71, 252], [63, 227], [50], [2], [43], [150], [1]]]
 h' := ![![[237, 262], [165, 163], [128, 96], [36, 257], [247, 239], [19, 153], [222, 116], [206, 237], [0, 1]], ![[0, 1], [135, 100], [262, 167], [192, 6], [82, 24], [249, 110], [99, 147], [93, 26], [237, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [88, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [57, 26, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2516712, 604104, 2596031, 1914242, 5839454]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4522939, -6102207, 2596031, 1914242, 5839454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -12, -29, -27, -80]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![-47, -12, -29, -27, -80]] 
 ![![263, 0, 0, 0, 0], ![183, 1, 0, 0, 0], ![175, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![208, 0, 0, 0, 1]] where
  M :=![![![-47, -12, -29, -27, -80], ![-24, 25, -143, -99, -266], ![-744, -6, -1084, -837, -2342], ![-4056, 246, -7241, -5462, -15146], ![1464, -66, 2510, 1902, 5283]]]
  hmulB := by decide  
  f := ![![![-33481, -139692, 45541, 73941, 224632]], ![![-23553, -98267, 32036, 52014, 158018]], ![![-22793, -95094, 31001, 50334, 152914]], ![![-8795, -36702, 11968, 19429, 59026]], ![![-25832, -107778, 35136, 57048, 173311]]]
  g := ![![![97, -12, -29, -27, -80], ![311, 25, -143, -99, -266], ![2769, -6, -1084, -837, -2342], ![17877, 246, -7241, -5462, -15146], ![-6238, -66, 2510, 1902, 5283]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-481, -1939, 626, 1019, 3094]] ![![-1, -17, 5, 8, 24]]
  ![![33481, 139692, -45541, -73941, -224632]] where
 M := ![![![33481, 139692, -45541, -73941, -224632]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![33481, 139692, -45541, -73941, -224632]] ![![-47, -12, -29, -27, -80]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC263 : ContainsPrimesAboveP 263 ![I263N0, I263N1, I263N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
    exact isPrimeI263N1
    exact isPrimeI263N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 263 (by decide) (𝕀 ⊙ MulI263N0 ⊙ MulI263N1)
instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6323, 25244, -8013, -13171, -39946]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![6323, 25244, -8013, -13171, -39946]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![265, 242, 117, 1, 0], ![83, 187, 195, 0, 1]] where
  M :=![![![6323, 25244, -8013, -13171, -39946], ![10392, 49733, -17481, -27427, -83718], ![34488, 105606, -26924, -49343, -147566], ![-11112, 178350, -102415, -133018, -417894], ![-14016, -120762, 51660, 74636, 230571]]]
  hmulB := by decide  
  f := ![![![-7313, -1564, -1073, -1757, -5706]], ![![10440, 1873, 1413, 2373, 7694]], ![![-13800, -1854, -1860, -3041, -9766]], ![![-3757, -658, -592, -910, -2918]], ![![-4991, -521, -694, -1093, -3479]]]
  g := ![![![25324, 39712, 34656, -13171, -39946], ![52889, 83057, 72552, -27427, -83718], ![94269, 147366, 128333, -49343, -147566], ![259940, 410836, 360409, -133018, -417894], ![-144721, -227879, -199413, 74636, 230571]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [214, 143, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [167, 126, 195], [63, 142, 74], [0, 1]]
 g := ![![[184, 240, 58], [59, 92], [81, 115, 212], [268, 29, 9], [214, 225], [254, 13], [230, 1], []], ![[158, 192, 183, 69], [104, 62], [176, 131, 240, 171], [89, 219, 90, 237], [108, 248], [2, 138], [5, 258], [204, 96]], ![[107, 210, 2, 33], [26, 118], [67, 200, 67, 209], [142, 174, 123, 32], [196, 133], [179, 253], [257, 5], [56, 96]]]
 h' := ![![[167, 126, 195], [222, 137, 70], [151, 188, 19], [214, 67, 181], [88, 153, 3], [31, 201, 15], [7, 252, 33], [0, 0, 1], [0, 1]], ![[63, 142, 74], [253, 40, 71], [167, 268, 84], [99, 26, 31], [127, 148, 133], [188, 154, 168], [62, 207, 26], [104, 169, 142], [167, 126, 195]], ![[0, 1], [60, 92, 128], [128, 82, 166], [133, 176, 57], [208, 237, 133], [69, 183, 86], [213, 79, 210], [55, 100, 126], [63, 142, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 47], []]
 b := ![[], [9, 159, 266], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [214, 143, 39, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32591594867, -6486691084, -36722790216, -27246531059, -81508071840]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![51869550552, 81149380146, 70799982723, -27246531059, -81508071840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7313, 1564, 1073, 1757, 5706]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![7313, 1564, 1073, 1757, 5706]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![221, 152, 1, 0, 0], ![33, 251, 0, 1, 0], ![194, 57, 0, 0, 1]] where
  M :=![![![7313, 1564, 1073, 1757, 5706], ![-10440, -1873, -1413, -2373, -7694], ![13800, 1854, 1860, 3041, 9766], ![-15432, -1110, -771, -2346, -7822], ![-3120, -942, -842, -1058, -3339]]]
  hmulB := by decide  
  f := ![![![-6323, -25244, 8013, 13171, 39946]], ![![-10392, -49733, 17481, 27427, 83718]], ![![-11195, -49234, 16561, 26502, 80672]], ![![-10431, -50165, 17675, 27702, 84570]], ![![-6710, -28295, 9291, 15033, 45691]]]
  g := ![![![-5185, -3449, 1073, 1757, 5706], ![6962, 4636, -1413, -2373, -7694], ![-8893, -5951, 1860, 3041, 9766], ![6505, 4278, -771, -2346, -7822], ![3218, 2167, -842, -1058, -3339]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [176, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 268], [0, 1]]
 g := ![![[129, 188], [30], [203, 253], [119, 211], [224], [182], [97], [1]], ![[0, 81], [30], [48, 16], [196, 58], [224], [182], [97], [1]]]
 h' := ![![[161, 268], [80, 200], [49, 90], [38, 210], [186, 178], [41, 61], [185, 102], [93, 161], [0, 1]], ![[0, 1], [0, 69], [13, 179], [223, 59], [61, 91], [178, 208], [198, 167], [190, 108], [161, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [177, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [176, 108, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1862336, 725568, 1269188, 898932, 3092060]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3376032, -2208440, 1269188, 898932, 3092060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![6323, 25244, -8013, -13171, -39946]] ![![7313, 1564, 1073, 1757, 5706]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![-269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 6, 29, 21, 62]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![25, 6, 29, 21, 62]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![4, 242, 1, 0, 0], ![116, 247, 0, 1, 0], ![86, 201, 0, 0, 1]] where
  M :=![![![25, 6, 29, 21, 62], ![24, -29, 113, 87, 218], ![1032, 150, 1308, 975, 2846], ![1896, -1182, 5867, 4522, 11750], ![-816, 336, -2120, -1626, -4291]]]
  hmulB := by decide  
  f := ![![![5431, 966, 739, 1233, 3994]], ![![-7080, -923, -887, -1515, -4886]], ![![-6212, -808, -778, -1329, -4286]], ![![-4156, -425, -494, -857, -2756]], ![![-3538, -381, -425, -735, -2365]]]
  g := ![![![-29, -91, 29, 21, 62], ![-108, -342, 113, 87, 218], ![-1336, -4167, 1308, 975, 2846], ![-5744, -18080, 5867, 4522, 11750], ![2086, 6559, -2120, -1626, -4291]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [225, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [184, 270], [0, 1]]
 g := ![![[4, 53], [72, 141], [131, 74], [124, 7], [63], [103], [252], [1]], ![[0, 218], [0, 130], [197, 197], [57, 264], [63], [103], [252], [1]]]
 h' := ![![[184, 270], [60, 253], [64, 35], [13, 138], [199, 121], [163, 92], [158, 153], [46, 184], [0, 1]], ![[0, 1], [0, 18], [0, 236], [202, 133], [241, 150], [18, 179], [126, 118], [27, 87], [184, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [179]]
 b := ![[], [167, 225]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [225, 87, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8977879, 1589666, 10614549, 7893655, 23375406]
  a := ![619, 214, 629, 437, 1358]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10920403, -34004873, 10614549, 7893655, 23375406]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![911, -40, 1552, 1176, 3268]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![911, -40, 1552, 1176, 3268]] 
 ![![271, 0, 0, 0, 0], ![68, 1, 0, 0, 0], ![254, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![90, 0, 0, 0, 1]] where
  M :=![![![911, -40, 1552, 1176, 3268], ![6240, -277, 10644, 8064, 22408], ![42816, -1896, 73011, 55316, 153712], ![293664, -13008, 500796, 379419, 1054328], ![-101328, 4488, -172796, -130916, -363789]]]
  hmulB := by decide  
  f := ![![![-3007, -1256, -224, -344, -1196]], ![![-740, -317, -52, -80, -280]], ![![-2846, -1192, -213, -324, -1128]], ![![-744, -336, -28, -61, -216]], ![![-1002, -408, -84, -124, -429]]]
  g := ![![![-2839, -40, 1552, 1176, 3268], ![-19468, -277, 10644, 8064, 22408], ![-133542, -1896, 73011, 55316, 153712], ![-915984, -13008, 500796, 379419, 1054328], ![316054, 4488, -172796, -130916, -363789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-937, -246, -145, -237, -774]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![-937, -246, -145, -237, -774]] 
 ![![271, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![212, 0, 0, 0, 1]] where
  M :=![![![-937, -246, -145, -237, -774], ![1512, 341, 255, 389, 1254], ![-2088, -438, -104, -359, -1238], ![3864, 438, 1829, 1754, 5178], ![-48, 120, -444, -298, -789]]]
  hmulB := by decide  
  f := ![![![26105, 106890, -34479, -56249, -170770]], ![![9812, 40229, -12987, -21179, -64302]], ![![3045, 12264, -3915, -6418, -19472]], ![![1358, 6978, -2535, -3920, -11990]], ![![20044, 81660, -26258, -42900, -130217]]]
  g := ![![![716, -246, -145, -237, -774], ![-1141, 341, 255, 389, 1254], ![1146, -438, -104, -359, -1238], ![-4445, 438, 1829, 1754, 5178], ![628, 120, -444, -298, -789]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2

def I271N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 14, 21, 15, 54]] i)))

def SI271N3: IdealEqSpanCertificate' Table ![![35, 14, 21, 15, 54]] 
 ![![271, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![262, 0, 0, 1, 0], ![261, 0, 0, 0, 1]] where
  M :=![![![35, 14, 21, 15, 54], ![-216, -91, -133, -93, -330], ![1224, 522, 710, 497, 1806], ![-7560, -3102, -4735, -3336, -11774], ![2112, 864, 1334, 940, 3307]]]
  hmulB := by decide  
  f := ![![![2549, 3766, 1235, 1687, 5666]], ![![1188, 1805, 589, 803, 2698]], ![![1933, 2708, 897, 1230, 4128]], ![![2186, 3550, 1145, 1554, 5226]], ![![2487, 3630, 1193, 1631, 5477]]]
  g := ![![![-88, 14, 21, 15, 54], ![545, -91, -133, -93, -330], ![-2970, 522, 710, 497, 1806], ![19385, -3102, -4735, -3336, -11774], ![-5447, 864, 1334, 940, 3307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N3 : Nat.card (O ⧸ I271N3) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N3)

lemma isPrimeI271N3 : Ideal.IsPrime I271N3 := prime_ideal_of_norm_prime hp271.out _ NI271N3
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![25, 6, 29, 21, 62]] ![![911, -40, 1552, 1176, 3268]]
  ![![1186487, -52558, 2023347, 1532955, 4259766]] where
 M := ![![![1186487, -52558, 2023347, 1532955, 4259766]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![1186487, -52558, 2023347, 1532955, 4259766]] ![![-937, -246, -145, -237, -774]]
  ![![302914801, -13417856, 516567598, 391368748, 1087533360]] where
 M := ![![![302914801, -13417856, 516567598, 391368748, 1087533360]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N2 : IdealMulLeCertificate' Table 
  ![![302914801, -13417856, 516567598, 391368748, 1087533360]] ![![35, 14, 21, 15, 54]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-16098263677, 713085010, -27452739291, -20799106099, -57796443710]]]
 hmul := by decide  
 g := ![![![![-59403187, 2631310, -101301621, -76749469, -213271010]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1, I271N2, I271N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
    exact isPrimeI271N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0 ⊙ MulI271N1 ⊙ MulI271N2)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11977, 2673, 1782, 2911, 9462]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![11977, 2673, 1782, 2911, 9462]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![229, 122, 1, 0, 0], ![39, 26, 0, 1, 0], ![190, 205, 0, 0, 1]] where
  M :=![![![11977, 2673, 1782, 2911, 9462], ![-17496, -3317, -2450, -4060, -13162], ![23568, 3522, 3029, 5142, 16620], ![-28656, -2604, -3372, -5791, -18564], ![-4440, -1521, -762, -1227, -4033]]]
  hmulB := by decide  
  f := ![![![1621, 4701, -1128, -2135, -6360]], ![![-1080, 7621, -4874, -6118, -19330]], ![![949, 7337, -3059, -4465, -13772]], ![![-249, 1337, -904, -1116, -3536]], ![![406, 8830, -4286, -5901, -18365]]]
  g := ![![![-8330, -8051, 1782, 2911, 9462], ![11562, 11189, -2450, -4060, -13162], ![-14543, -14104, 3029, 5142, 16620], ![16233, 15758, -3372, -5791, -18564], ![3553, 3430, -762, -1227, -4033]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 2 2 8 [257, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 276], [0, 1]]
 g := ![![[157, 102], [90], [96, 16], [90], [249, 249], [192], [62], [1]], ![[225, 175], [90], [199, 261], [90], [138, 28], [192], [62], [1]]]
 h' := ![![[93, 276], [222, 42], [258, 190], [174, 273], [271, 190], [169, 183], [255, 68], [20, 93], [0, 1]], ![[0, 1], [250, 235], [200, 87], [79, 4], [213, 87], [14, 94], [208, 209], [82, 184], [93, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [264, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 2
  hpos := by decide
  P := [257, 184, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![69314, 24908, 51799, 36372, 122742]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-131885, -116976, 51799, 36372, 122742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, -22, -23, -33, -108]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-145, -22, -23, -33, -108]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![138, 147, 1, 0, 0], ![212, 135, 0, 1, 0], ![197, 179, 0, 0, 1]] where
  M :=![![![-145, -22, -23, -33, -108], ![216, 35, 53, 55, 186], ![-504, -138, -228, -173, -610], ![2184, 834, 1263, 882, 3166], ![-504, -228, -340, -226, -819]]]
  hmulB := by decide  
  f := ![![![-133, -578, 189, 309, 940]], ![![-312, -1177, 359, 599, 1822]], ![![-234, -921, 287, 476, 1448]], ![![-260, -1033, 322, 535, 1628]], ![![-293, -1161, 364, 602, 1831]]]
  g := ![![![113, 98, -23, -33, -108], ![-200, -175, 53, 55, 186], ![678, 599, -228, -173, -610], ![-3548, -3143, 1263, 882, 3166], ![923, 819, -340, -226, -819]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [187, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [181, 276], [0, 1]]
 g := ![![[239, 40], [91], [125, 201], [3], [161, 27], [13], [75], [1]], ![[0, 237], [91], [219, 76], [3], [62, 250], [13], [75], [1]]]
 h' := ![![[181, 276], [249, 219], [170, 63], [187, 66], [86, 147], [92, 164], [169, 173], [90, 181], [0, 1]], ![[0, 1], [0, 58], [216, 214], [222, 211], [101, 130], [137, 113], [181, 104], [165, 96], [181, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [59, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : CertifiedPrimeIdeal' SI277N1 277 where
  n := 2
  hpos := by decide
  P := [187, 96, 1]
  hirr := P277P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5441164, 1449414, 5281092, 3874080, 11999550]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14110346, -12439680, 5281092, 3874080, 11999550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N1 B_one_repr
lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11639, 3915, 2082, 3265, 10688]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![11639, 3915, 2082, 3265, 10688]] 
 ![![277, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![213, 0, 1, 0, 0], ![235, 0, 0, 1, 0], ![195, 0, 0, 0, 1]] where
  M :=![![![11639, 3915, 2082, 3265, 10688], ![-21432, -6193, -3564, -5676, -18530], ![36048, 9114, 5649, 9116, 29692], ![-56256, -12396, -8334, -13623, -44272], ![-384, -1035, -308, -407, -1377]]]
  hmulB := by decide  
  f := ![![![-75253, -313377, 102104, 165807, 503730]], ![![-2720, -11323, 3688, 5990, 18198]], ![![-58965, -245535, 79993, 129907, 394666]], ![![-66091, -275031, 89542, 145466, 441942]], ![![-51579, -214854, 70026, 113696, 345411]]]
  g := ![![![-11966, 3915, 2082, 3265, 10688], ![20702, -6193, -3564, -5676, -18530], ![-33113, 9114, 5649, 9116, 29692], ![49287, -12396, -8334, -13623, -44272], ![1580, -1035, -308, -407, -1377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![11977, 2673, 1782, 2911, 9462]] ![![-145, -22, -23, -33, -108]]
  ![![-468649, -145417, -80585, -127422, -416510]] where
 M := ![![![-468649, -145417, -80585, -127422, -416510]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![-468649, -145417, -80585, -127422, -416510]] ![![11639, 3915, 2082, 3265, 10688]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![2085235225, 341965918, 277534333, 466024523, 1507687732]]]
 hmul := by decide  
 g := ![![![![7527925, 1234534, 1001929, 1682399, 5442916]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, 0, 0, 0, 0]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![281, 0, 0, 0, 0]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]] where
  M :=![![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![0, 0, 0, 281, 0], ![0, 0, 0, 0, 281]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 5 2 8 [97, 171, 66, 41, 67, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [273, 198, 41, 255, 267], [251, 143, 140, 169, 25], [218, 135, 24, 178, 39], [34, 85, 76, 241, 231], [0, 1]]
 g := ![![[171, 153, 73, 257, 49], [51, 88, 93, 202], [253, 157, 238, 249], [65, 191, 254, 177, 2], [41, 215, 34, 92, 14], [277, 233, 214, 1], [], []], ![[98, 19, 156, 26, 223, 196, 13, 252], [84, 219, 57, 7], [40, 0, 9, 202], [16, 256, 212, 78, 222, 23, 93, 137], [167, 159, 108, 260, 239, 136, 151, 140], [167, 192, 172, 228], [247, 86, 33, 7], [22, 73, 241, 196]], ![[183, 46, 18, 97, 56, 98, 215, 81], [32, 175, 124, 140], [140, 133, 264, 4], [82, 129, 42, 50, 261, 44, 11, 90], [251, 85, 274, 226, 199, 172, 9, 68], [46, 0, 162, 57], [69, 258, 162, 2], [161, 6, 14, 63]], ![[260, 210, 262, 104, 211, 249, 4, 58], [21, 221, 197, 246], [200, 165, 50, 209], [232, 105, 57, 104, 56, 250, 185, 81], [258, 247, 187, 275, 141, 269, 157, 217], [155, 168, 126, 116], [236, 8, 250, 16], [193, 51, 211, 116]], ![[179, 268, 267, 55, 196, 41, 247, 271], [146, 22, 165, 267], [224, 122, 259, 124], [259, 266, 254, 36, 31, 138, 255, 155], [26, 10, 41, 3, 166, 91, 254, 50], [191, 75, 0, 175], [15, 14, 61, 32], [241, 243, 42, 252]]]
 h' := ![![[273, 198, 41, 255, 267], [43, 234, 144, 12, 7], [142, 23, 212, 166, 157], [158, 26, 68, 93, 165], [238, 162, 157, 134, 149], [107, 1, 78, 80, 24], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[251, 143, 140, 169, 25], [262, 224, 202, 225, 87], [82, 42, 115, 182, 179], [77, 260, 132, 92, 124], [134, 202, 90, 171, 140], [35, 9, 174, 135, 208], [138, 116, 159, 110, 60], [178, 39, 112, 165, 102], [273, 198, 41, 255, 267]], ![[218, 135, 24, 178, 39], [66, 76, 17, 247, 223], [172, 246, 261, 118, 126], [210, 97, 207, 148, 279], [126, 120, 58, 54, 39], [235, 13, 96, 147, 44], [117, 215, 170, 249, 30], [176, 118, 163, 67, 149], [251, 143, 140, 169, 25]], ![[34, 85, 76, 241, 231], [270, 194, 212, 38, 260], [202, 36, 15, 7, 248], [139, 113, 257, 109, 107], [271, 107, 193, 260, 229], [76, 106, 73, 87, 233], [80, 10, 51, 259, 242], [141, 116, 251, 186, 277], [218, 135, 24, 178, 39]], ![[0, 1], [208, 115, 268, 40, 266], [243, 215, 240, 89, 133], [192, 66, 179, 120, 168], [3, 252, 64, 224, 5], [105, 152, 141, 113, 53], [153, 221, 182, 225, 229], [259, 8, 35, 144, 34], [34, 85, 76, 241, 231]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 232, 37, 209], [], [], []]
 b := ![[], [50, 107, 236, 135, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 5
  hpos := by decide
  P := [97, 171, 66, 41, 67, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![304870251455381009, 20809375578002640, 438312578777726313, 329588365672721561, 940935381264032100]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1084947514076089, 74054717359440, 1559831241201873, 1172912333354881, 3348524488484100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 1751989905401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def PBC281 : ContainsPrimesAboveP 281 ![I281N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![281, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 281 (by decide) 𝕀

instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1463, 624, 875, 611, 2192]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![1463, 624, 875, 611, 2192]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![238, 268, 178, 1, 0], ![266, 206, 48, 0, 1]] where
  M :=![![![1463, 624, 875, 611, 2192], ![-8616, -3601, -5189, -3647, -13062], ![50904, 21414, 30594, 21453, 76874], ![-300360, -126090, -180619, -126740, -454126], ![83400, 34986, 50164, 35208, 126149]]]
  hmulB := by decide  
  f := ![![![-451, -24, -47, -85, -272]], ![![408, -43, 27, 55, 170]], ![![-120, 198, 62, 57, 190]], ![![-70, 62, 25, 16, 50]], ![![-146, -20, -14, -30, -99]]]
  g := ![![![-2569, -2172, -753, 611, 2192], ![15314, 12949, 4491, -3647, -13062], ![-90118, -76198, -26424, 21453, 76874], ![532372, 450142, 156103, -126740, -454126], ![-147886, -125044, -43364, 35208, 126149]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [40, 258, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 160, 170], [68, 122, 113], [0, 1]]
 g := ![![[68, 14, 203], [24, 244, 251], [37, 95], [238, 188, 216], [226, 262, 29], [129, 169], [178, 1], []], ![[6, 200, 202, 148], [62, 206, 185, 258], [205, 165], [233, 8, 252, 229], [23, 59, 155, 156], [150, 15], [51, 168], [173, 34]], ![[153, 179, 83, 236], [4, 128, 253, 280], [268, 29], [230, 214, 25, 113], [118, 207, 77, 34], [175, 111], [282, 130], [230, 34]]]
 h' := ![![[110, 160, 170], [172, 57, 130], [151, 183, 225], [102, 101, 100], [16, 182, 181], [261, 10, 38], [238, 165, 13], [0, 0, 1], [0, 1]], ![[68, 122, 113], [76, 241, 80], [11, 187, 262], [2, 274, 221], [227, 89, 101], [101, 80, 110], [262, 127, 204], [86, 243, 122], [110, 160, 170]], ![[0, 1], [72, 268, 73], [97, 196, 79], [189, 191, 245], [25, 12, 1], [249, 193, 135], [80, 274, 66], [235, 40, 160], [68, 122, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [281, 169], []]
 b := ![[], [240, 80, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [40, 258, 105, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7386445160, 568851204, 10466146365, 7864379319, 22508106258]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27743788330, -23829521892, -8727146547, 7864379319, 22508106258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-451, -24, -47, -85, -272]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-451, -24, -47, -85, -272]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![241, 105, 1, 0, 0], ![165, 253, 0, 1, 0], ![257, 86, 0, 0, 1]] where
  M :=![![![-451, -24, -47, -85, -272], ![408, -43, 27, 55, 170], ![-120, 198, 62, 57, 190], ![-456, -462, -11, -128, -494], ![360, 78, 2, 54, 195]]]
  hmulB := by decide  
  f := ![![![1463, 624, 875, 611, 2192]], ![![-8616, -3601, -5189, -3647, -13062]], ![![-1771, -729, -1072, -757, -2708]], ![![-7911, -3301, -4767, -3352, -12004]], ![![-995, -404, -605, -429, -1533]]]
  g := ![![![335, 176, -47, -85, -272], ![-208, -111, 27, 55, 170], ![-259, -131, 62, 57, 190], ![531, 267, -11, -128, -494], ![-209, -108, 2, 54, 195]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [84, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 282], [0, 1]]
 g := ![![[110, 237], [43, 251], [143], [278, 264], [243, 44], [151], [179], [1]], ![[84, 46], [271, 32], [143], [95, 19], [71, 239], [151], [179], [1]]]
 h' := ![![[99, 282], [67, 246], [248, 225], [137, 133], [247, 84], [74, 238], [227, 240], [199, 99], [0, 1]], ![[0, 1], [83, 37], [166, 58], [3, 150], [73, 199], [147, 45], [215, 43], [95, 184], [99, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [265]]
 b := ![[], [21, 274]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [84, 184, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3758141, 1071054, 3471393, 2542132, 7967256]
  a := ![-359, -113, -376, -246, -788]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11660368, -5977981, 3471393, 2542132, 7967256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![1463, 624, 875, 611, 2192]] ![![-451, -24, -47, -85, -272]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0)
instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 33, -1, 4, 18]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![25, 33, -1, 4, 18]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![178, 218, 291, 1, 0], ![206, 165, 212, 0, 1]] where
  M :=![![![25, 33, -1, 4, 18], ![-144, -41, -89, -89, -268], ![24, 132, -374, -251, -662], ![-2184, -42, -2965, -2332, -6558], ![624, -51, 1002, 773, 2157]]]
  hmulB := by decide  
  f := ![![![5, 9, 9, 4, 16]], ![![-96, -43, -67, -47, -168]], ![![648, 288, 390, 271, 974]], ![![562, 254, 335, 231, 832]], ![![422, 192, 253, 174, 627]]]
  g := ![![![-15, -13, -17, 4, 18], ![242, 217, 282, -89, -268], ![618, 560, 727, -251, -662], ![6020, 5428, 7051, -2332, -6558], ![-1984, -1790, -2325, 773, 2157]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [69, 282, 287, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 197, 264], [228, 95, 29], [0, 1]]
 g := ![![[258, 254, 269], [219, 216], [292, 253, 36], [259, 150], [142, 121], [229, 80, 158], [6, 1], []], ![[33, 265, 196, 48], [21, 102], [87, 246, 289, 181], [114, 211], [35, 61], [133, 63, 85, 99], [2, 235], [66, 255]], ![[186, 6, 87, 219], [146, 220], [82, 267, 231, 217], [39, 277], [102, 260], [231, 269, 33, 290], [211, 133], [8, 255]]]
 h' := ![![[71, 197, 264], [198, 280, 165], [69, 31, 252], [70, 119, 287], [19, 108, 210], [21, 213, 282], [172, 290, 47], [0, 0, 1], [0, 1]], ![[228, 95, 29], [227, 272, 230], [176, 264, 187], [30, 177, 81], [82, 243, 117], [118, 88, 103], [287, 97, 157], [194, 264, 95], [71, 197, 264]], ![[0, 1], [285, 34, 191], [114, 291, 147], [183, 290, 218], [185, 235, 259], [271, 285, 201], [128, 199, 89], [157, 29, 197], [228, 95, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 70], []]
 b := ![[], [122, 67, 255], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [69, 282, 287, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6010205367, -916463236, -7436418064, -5548326422, -16282060028]
  a := ![-221, -70, -227, -154, -485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14797598169, 13294056660, 17265949818, -5548326422, -16282060028]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 63, 24, 35, 116]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![83, 63, 24, 35, 116]] 
 ![![293, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![141, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![162, 0, 0, 0, 1]] where
  M :=![![![83, 63, 24, 35, 116], ![-264, -121, -50, -82, -270], ![576, 198, 103, 170, 544], ![-816, -240, 96, -101, -340], ![0, -27, -80, -47, -149]]]
  hmulB := by decide  
  f := ![![![-302081, -1258221, 410114, 665837, 2022790]], ![![-97953, -407992, 132984, 215905, 655912]], ![![-149529, -622815, 203005, 329587, 1001274]], ![![-82584, -343980, 112120, 182031, 553004]], ![![-161778, -673833, 219634, 356585, 1083293]]]
  g := ![![![-104, 63, 24, 35, 116], ![231, -121, -50, -82, -270], ![-453, 198, 103, 170, 544], ![240, -240, 96, -101, -340], ![141, -27, -80, -47, -149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10745, -44754, 14587, 23683, 71948]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![-10745, -44754, 14587, 23683, 71948]] 
 ![![293, 0, 0, 0, 0], ![202, 1, 0, 0, 0], ![216, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![290, 0, 0, 0, 1]] where
  M :=![![![-10745, -44754, 14587, 23683, 71948], ![-21576, -89885, 29301, 47569, 144514], ![-43368, -180546, 58830, 95527, 290202], ![-86904, -362538, 118279, 191948, 583166], ![54600, 227580, -74210, -120460, -365963]]]
  hmulB := by decide  
  f := ![![![-10477, -4062, -2209, -3251, -10596]], ![![-7154, -2777, -1515, -2225, -7250]], ![![-7872, -3030, -1682, -2455, -7990]], ![![-809, -288, -376, -391, -1194]], ![![-10330, -4020, -2110, -3160, -10327]]]
  g := ![![![-53168, -44754, 14587, 23683, 71948], ![-106799, -89885, 29301, 47569, 144514], ![-214427, -180546, 58830, 95527, 290202], ![-431124, -362538, 118279, 191948, 583166], ![270490, 227580, -74210, -120460, -365963]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![25, 33, -1, 4, 18]] ![![83, 63, 24, 35, 116]]
  ![![-10477, -4062, -2209, -3251, -10596]] where
 M := ![![![-10477, -4062, -2209, -3251, -10596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![-10477, -4062, -2209, -3251, -10596]] ![![-10745, -44754, 14587, 23683, 71948]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-59, -21, -35, -26, -92]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-59, -21, -35, -26, -92]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![3, 299, 1, 0, 0], ![24, 246, 0, 1, 0], ![253, 164, 0, 0, 1]] where
  M :=![![![-59, -21, -35, -26, -92], ![336, 145, 197, 137, 492], ![-1944, -804, -1170, -825, -2954], ![11496, 4842, 6913, 4844, 17350], ![-3192, -1353, -1918, -1341, -4805]]]
  hmulB := by decide  
  f := ![![![511, 213, 101, 154, 506]], ![![-1056, -347, -183, -295, -968]], ![![-1017, -334, -176, -284, -932]], ![![-816, -264, -139, -226, -742]], ![![-143, -10, -15, -31, -101]]]
  g := ![![![78, 104, -35, -26, -92], ![-417, -564, 197, 137, 492], ![2504, 3376, -1170, -825, -2954], ![-14707, -19867, 6913, 4844, 17350], ![4073, 5505, -1918, -1341, -4805]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [297, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [251, 306], [0, 1]]
 g := ![![[240, 121], [244, 17], [118], [278], [90, 219], [66, 6], [66], [1]], ![[218, 186], [213, 290], [118], [278], [106, 88], [37, 301], [66], [1]]]
 h' := ![![[251, 306], [291, 11], [35, 289], [151, 217], [286, 187], [46, 181], [146, 96], [10, 251], [0, 1]], ![[0, 1], [289, 296], [122, 18], [279, 90], [252, 120], [41, 126], [296, 211], [76, 56], [251, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [278]]
 b := ![[], [208, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 2
  hpos := by decide
  P := [297, 56, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2195586, 283926, 2846806, 2128000, 6187514]
  a := ![309, 105, 314, 221, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5286182, -7782252, 2846806, 2128000, 6187514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2119, -393, -295, -490, -1588]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-2119, -393, -295, -490, -1588]] 
 ![![307, 0, 0, 0, 0], ![49, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![300, 0, 0, 0, 1]] where
  M :=![![![-2119, -393, -295, -490, -1588], ![2832, 413, 361, 613, 1980], ![-3384, -276, -378, -669, -2146], ![3336, -126, 245, 508, 1598], ![1032, 291, 178, 279, 911]]]
  hmulB := by decide  
  f := ![![![81875, -3615, 139609, 105770, 293914]], ![![14897, -658, 25402, 19245, 53478]], ![![27215, -1203, 46407, 35159, 97700]], ![![104188, -4614, 177675, 134612, 374058]], ![![50316, -2217, 85790, 64995, 180609]]]
  g := ![![![1769, -393, -295, -490, -1588], ![-2192, 413, 361, 613, 1980], ![2346, -276, -378, -669, -2146], ![-1687, -126, 245, 508, 1598], ![-1027, 291, 178, 279, 911]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-785, -127, -104, -175, -566]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![-785, -127, -104, -175, -566]] 
 ![![307, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![182, 0, 0, 1, 0], ![86, 0, 0, 0, 1]] where
  M :=![![![-785, -127, -104, -175, -566], ![984, 109, 116, 202, 650], ![-1056, -18, -95, -184, -584], ![768, -216, -18, 49, 128], ![456, 123, 82, 121, 397]]]
  hmulB := by decide  
  f := ![![![-3707, 235, -6378, -4851, -13488]], ![![-1170, 73, -2012, -1530, -4254]], ![![-2853, 171, -4901, -3725, -10356]], ![![-6118, 314, -10466, -7941, -22072]], ![![314, 5, 520, 389, 1079]]]
  g := ![![![361, -127, -104, -175, -566], ![-402, 109, 116, 202, 650], ![333, -18, -95, -184, -584], ![12, -216, -18, 49, 128], ![-268, 123, 82, 121, 397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2

def I307N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![365, 1579, -527, -846, -2574]] i)))

def SI307N3: IdealEqSpanCertificate' Table ![![365, 1579, -527, -846, -2574]] 
 ![![307, 0, 0, 0, 0], ![176, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![365, 1579, -527, -846, -2574], ![864, 3227, -977, -1643, -4968], ![936, 6144, -2448, -3639, -11194], ![6648, 14346, -2041, -5294, -15262], ![-2928, -8481, 2032, 3849, 11465]]]
  hmulB := by decide  
  f := ![![![-11737, 101, -17275, -13310, -37176]], ![![-6944, 69, -10283, -7917, -22108]], ![![-2725, 77, -4355, -3323, -9254]], ![![-13162, 488, -21837, -16594, -46154]], ![![3433, -158, 5895, 4463, 12399]]]
  g := ![![![-616, 1579, -527, -846, -2574], ![-1293, 3227, -977, -1643, -4968], ![-2260, 6144, -2448, -3639, -11194], ![-6541, 14346, -2041, -5294, -15262], ![3583, -8481, 2032, 3849, 11465]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N3 : Nat.card (O ⧸ I307N3) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N3)

lemma isPrimeI307N3 : Ideal.IsPrime I307N3 := prime_ideal_of_norm_prime hp307.out _ NI307N3
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-59, -21, -35, -26, -92]] ![![-2119, -393, -295, -490, -1588]]
  ![![2309, 678, 308, 576, 1862]] where
 M := ![![![2309, 678, 308, 576, 1862]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![2309, 678, 308, 576, 1862]] ![![-785, -127, -104, -175, -566]]
  ![![-179221, -120275, -48432, -70265, -233124]] where
 M := ![![![-179221, -120275, -48432, -70265, -233124]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N2 : IdealMulLeCertificate' Table 
  ![![-179221, -120275, -48432, -70265, -233124]] ![![365, 1579, -527, -846, -2574]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![799735, 419362, 222575, 165473, 606632]]]
 hmul := by decide  
 g := ![![![![2605, 1366, 725, 539, 1976]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2, I307N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
    exact isPrimeI307N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1 ⊙ MulI307N2)


lemma PB2088I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB2088I6 : PrimesBelowBoundCertificateInterval O 251 307 2088 where
  m := 9
  g := ![2, 3, 2, 4, 3, 1, 2, 3, 4]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB2088I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1, I271N2, I271N3]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0]
    · exact ![I283N0, I283N1]
    · exact ![I293N0, I293N1, I293N2]
    · exact ![I307N0, I307N1, I307N2, I307N3]
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
    · exact ![16974593, 66049]
    · exact ![69169, 69169, 263]
    · exact ![19465109, 72361]
    · exact ![73441, 271, 271, 271]
    · exact ![76729, 76729, 277]
    · exact ![1751989905401]
    · exact ![22665187, 80089]
    · exact ![25153757, 293, 293]
    · exact ![94249, 307, 307, 307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
      exact NI257N1
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
      exact NI271N3
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
      exact NI277N2
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
      exact NI307N3
  β := ![I263N2, I271N1, I271N2, I271N3, I277N2, I293N1, I293N2, I307N1, I307N2, I307N3]
  Il := ![[], [I263N2], [], [I271N1, I271N2, I271N3], [I277N2], [], [], [I293N1, I293N2], [I307N1, I307N2, I307N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
