
import IdealArithmetic.Examples.NF5_3_364500000_2.RI5_3_364500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![295, -9, -84, -3, 22]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![295, -9, -84, -3, 22]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![200, 220, 218, 1, 0], ![281, 72, 139, 0, 1]] where
  M :=![![![295, -9, -84, -3, 22], ![-528, -37, 76, 8, -12], ![144, -152, -69, 28, 16], ![72, -4, -186, -9, 62], ![-36, -261, -8, 41, 5]]]
  hmulB := by decide  
  f := ![![![41, 23, 6, -11, -8]], ![![192, 113, 36, -52, -44]], ![![528, 304, 77, -140, -104]], ![![536, 310, 84, -143, -110]], ![![323, 186, 49, -86, -65]]]
  g := ![![![-17, -3, -8, -3, 22], ![4, -3, 0, 8, -12], ![-32, -24, -27, 28, 16], ![-50, -8, -22, -9, 62], ![-31, -31, -31, 41, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 3 2 8 [177, 232, 214, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [287, 3, 237], [121, 307, 74], [0, 1]]
 g := ![![[153, 15, 280], [117, 262, 267], [132, 147, 5], [275, 175], [253, 216, 56], [159, 172, 84], [97, 1], []], ![[136, 98, 137, 60], [178, 158, 36, 182], [130, 195, 41, 32], [193, 193], [141, 310, 220, 70], [116, 207, 285, 254], [4, 16], [162, 189]], ![[231, 29, 150, 286], [87, 54, 61, 231], [22, 271, 147, 304], [32, 98], [124, 231, 145, 110], [15, 17, 104, 132], [23, 9], [14, 189]]]
 h' := ![![[287, 3, 237], [128, 155, 88], [272, 67, 122], [161, 275, 117], [3, 188, 78], [158, 208, 131], [247, 22, 158], [0, 0, 1], [0, 1]], ![[121, 307, 74], [277, 77, 307], [105, 172, 152], [207, 295, 19], [129, 107, 82], [300, 4, 256], [71, 161, 228], [203, 38, 307], [287, 3, 237]], ![[0, 1], [105, 79, 227], [87, 72, 37], [94, 52, 175], [212, 16, 151], [235, 99, 235], [195, 128, 236], [34, 273, 3], [121, 307, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 254], []]
 b := ![[], [250, 281, 264], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 3
  hpos := by decide
  P := [177, 232, 214, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7721613, 4485701, 1105780, -1911672, -1454095]
  a := ![0, -7, 2, -4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2568028, 1703371, 1993471, -1911672, -1454095]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 30080231 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 23, 6, -11, -8]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![41, 23, 6, -11, -8]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![50, 93, 1, 0, 0], ![15, 240, 0, 1, 0], ![245, 9, 0, 0, 1]] where
  M :=![![![41, 23, 6, -11, -8], ![192, 113, 36, -52, -44], ![528, 304, 77, -140, -104], ![1152, 678, 218, -313, -258], ![1716, 991, 258, -451, -343]]]
  hmulB := by decide  
  f := ![![![295, -9, -84, -3, 22]], ![![-528, -37, 76, 8, -12]], ![![-110, -13, 9, 2, 0]], ![![-393, -29, 54, 6, -8]], ![![217, -9, -64, -2, 17]]]
  g := ![![![6, 7, 6, -11, -8], ![32, 31, 36, -52, -44], ![78, 89, 77, -140, -104], ![187, 186, 218, -313, -258], ![256, 284, 258, -451, -343]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [8, 248, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 310], [0, 1]]
 g := ![![[31, 39], [45, 282], [47, 26], [5], [216, 3], [122, 208], [237], [1]], ![[0, 272], [84, 29], [130, 285], [5], [94, 308], [164, 103], [237], [1]]]
 h' := ![![[63, 310], [262, 139], [246, 110], [33, 56], [138, 194], [268, 25], [34, 239], [303, 63], [0, 1]], ![[0, 1], [0, 172], [23, 201], [140, 255], [231, 117], [288, 286], [163, 72], [229, 248], [63, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [284, 223]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N1 : CertifiedPrimeIdeal' SI311N1 311 where
  n := 2
  hpos := by decide
  P := [8, 248, 1]
  hirr := P311P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125501, 35298, -179077, -3192, 139229]
  a := ![3, -62, -1, -65, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80334, 52098, -179077, -3192, 139229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N1 B_one_repr
lemma NI311N1 : Nat.card (O ⧸ I311N1) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![295, -9, -84, -3, 22]] ![![41, 23, 6, -11, -8]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-437, -253, -72, 117, 92]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![-437, -253, -72, 117, 92]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![180, 208, 1, 0, 0], ![120, 177, 0, 1, 0], ![123, 37, 0, 0, 1]] where
  M :=![![![-437, -253, -72, 117, 92], ![-2208, -1287, -372, 592, 468], ![-5616, -3272, -943, 1500, 1184], ![-13104, -7648, -2218, 3497, 2766], ![-18300, -10681, -3092, 4877, 3855]]]
  hmulB := by decide  
  f := ![![![-317, 25, 74, -17, -6]], ![![144, -211, 60, 100, -68]], ![![-84, -124, 81, 56, -48]], ![![-48, -113, 66, 51, -42]], ![![-99, -11, 32, 4, -9]]]
  g := ![![![-41, -30, -72, 117, 92], ![-204, -147, -372, 592, 468], ![-516, -372, -943, 1500, 1184], ![-1194, -855, -2218, 3497, 2766], ![-1665, -1193, -3092, 4877, 3855]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 2 2 8 [235, 212, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 312], [0, 1]]
 g := ![![[222, 4], [169], [78], [69, 269], [95, 181], [289, 121], [185], [1]], ![[0, 309], [169], [78], [7, 44], [222, 132], [303, 192], [185], [1]]]
 h' := ![![[101, 312], [111, 2], [102, 13], [61, 169], [211, 274], [6, 206], [169, 11], [78, 101], [0, 1]], ![[0, 1], [0, 311], [163, 300], [228, 144], [28, 39], [154, 107], [28, 302], [263, 212], [101, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [237, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 2
  hpos := by decide
  P := [235, 212, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8000, -5702, -619, 1424, 1014]
  a := ![1, -6, 1, -5, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-614, -532, -619, 1424, 1014]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, -2, 58, -40, 14]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-121, -2, 58, -40, 14]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![222, 274, 1, 0, 0], ![207, 312, 0, 1, 0], ![222, 248, 0, 0, 1]] where
  M :=![![![-121, -2, 58, -40, 14], ![-336, -297, 132, 228, -160], ![1920, 1006, -845, -508, 456], ![-5304, -2330, 2360, 865, -936], ![6744, 2922, -3022, -1060, 1173]]]
  hmulB := by decide  
  f := ![![![1967, 1258, 418, -576, -474]], ![![11376, 6447, 1772, -2956, -2304]], ![![11442, 6588, 1863, -3020, -2372]], ![![12849, 7380, 2078, -3383, -2654]], ![![10698, 6170, 1750, -2828, -2223]]]
  g := ![![![-25, -22, 58, -40, 14], ![-132, -217, 132, 228, -160], ![618, 888, -845, -508, 456], ![-1599, -2194, 2360, 865, -936], ![2034, 2782, -3022, -1060, 1173]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P1 : CertificateIrreducibleZModOfList' 313 2 2 8 [276, 267, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 312], [0, 1]]
 g := ![![[52, 83], [294], [263], [166, 289], [3, 216], [76, 238], [238], [1]], ![[114, 230], [294], [263], [1, 24], [236, 97], [69, 75], [238], [1]]]
 h' := ![![[46, 312], [84, 108], [180, 234], [195, 289], [111, 17], [308, 23], [159, 267], [37, 46], [0, 1]], ![[0, 1], [44, 205], [302, 79], [30, 24], [267, 296], [114, 290], [234, 46], [275, 267], [46, 312]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [185, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N1 : CertifiedPrimeIdeal' SI313N1 313 where
  n := 2
  hpos := by decide
  P := [276, 267, 1]
  hirr := P313P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100196, -45329, -10288, 34740, 26334]
  a := ![1, 25, -3, 18, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34676, -46633, -10288, 34740, 26334]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N1 B_one_repr
lemma NI313N1 : Nat.card (O ⧸ I313N1) = 97969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -7, 44, 5, -12]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![-173, -7, 44, 5, -12]] 
 ![![313, 0, 0, 0, 0], ![288, 1, 0, 0, 0], ![157, 0, 1, 0, 0], ![97, 0, 0, 1, 0], ![306, 0, 0, 0, 1]] where
  M :=![![![-173, -7, 44, 5, -12], ![288, 13, -72, -8, 20], ![-240, -10, 61, 8, -16], ![48, 0, -14, 1, 6], ![-300, -19, 72, 13, -17]]]
  hmulB := by decide  
  f := ![![![475, 203, -194, -57, 66]], ![![432, 185, -176, -52, 60]], ![![247, 105, -101, -29, 34]], ![![139, 61, -56, -18, 20]], ![![474, 201, -194, -55, 65]]]
  g := ![![![-6, -7, 44, 5, -12], ![8, 13, -72, -8, 20], ![-9, -10, 61, 8, -16], ![1, 0, -14, 1, 6], ![-7, -19, 72, 13, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![-437, -253, -72, 117, 92]] ![![-121, -2, 58, -40, 14]]
  ![![-475, -203, 194, 57, -66]] where
 M := ![![![-475, -203, 194, 57, -66]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![-475, -203, 194, 57, -66]] ![![-173, -7, 44, 5, -12]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 13, -26, -4, 8]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![43, 13, -26, -4, 8]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![164, 138, 1, 0, 0], ![192, 217, 0, 1, 0], ![40, 202, 0, 0, 1]] where
  M :=![![![43, 13, -26, -4, 8], ![-192, -79, 66, 12, -16], ![192, 37, -123, 2, 24], ![-192, -56, 50, -33, 12], ![120, -27, -94, 44, -13]]]
  hmulB := by decide  
  f := ![![![10295, 441, -2604, -296, 712]], ![![-17088, -733, 4322, 488, -1184]], ![![-2068, -89, 523, 58, -144]], ![![-5472, -235, 1384, 155, -380]], ![![-9536, -409, 2412, 272, -661]]]
  g := ![![![15, 9, -26, -4, 8], ![-40, -27, 66, 12, -16], ![60, 37, -123, 2, 24], ![-8, -7, 50, -33, 12], ![24, 19, -94, 44, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 2 2 8 [48, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 316], [0, 1]]
 g := ![![[228, 110], [223], [54, 165], [58, 60], [81, 223], [179, 173], [294], [1]], ![[37, 207], [223], [243, 152], [242, 257], [152, 94], [308, 144], [294], [1]]]
 h' := ![![[151, 316], [40, 136], [261, 240], [69, 254], [233, 80], [284, 240], [238, 100], [269, 151], [0, 1]], ![[0, 1], [288, 181], [46, 77], [66, 63], [267, 237], [69, 77], [122, 217], [246, 166], [151, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [174]]
 b := ![[], [247, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 2
  hpos := by decide
  P := [48, 166, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12303, -1430, -23801, 4594, 10483]
  a := ![-1, -7, 5, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8247, 532, -23801, 4594, 10483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![629, 245, -320, -87, 116]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![629, 245, -320, -87, 116]] 
 ![![317, 0, 0, 0, 0], ![173, 1, 0, 0, 0], ![93, 0, 1, 0, 0], ![111, 0, 0, 1, 0], ![152, 0, 0, 0, 1]] where
  M :=![![![629, 245, -320, -87, 116], ![-2784, -1141, 1128, 288, -348], ![4176, 1374, -2125, -264, 576], ![-5520, -1836, 2226, 35, -354], ![5604, 1425, -2916, 129, 497]]]
  hmulB := by decide  
  f := ![![![-591647, -336817, -93506, 153483, 119942]], ![![-331967, -189170, -52610, 86199, 67394]], ![![-196815, -112359, -31351, 51195, 40062]], ![![-261117, -149481, -41916, 68102, 53364]], ![![-358964, -205453, -57590, 93603, 73339]]]
  g := ![![![-63, 245, -320, -87, 116], ![349, -1141, 1128, 288, -348], ![-297, 1374, -2125, -264, 576], ![489, -1836, 2226, 35, -354], ![-188, 1425, -2916, 129, 497]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1349, -389, 626, -18, -100]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![-1349, -389, 626, -18, -100]] 
 ![![317, 0, 0, 0, 0], ![199, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![133, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-1349, -389, 626, -18, -100], ![2400, 341, -1142, 452, -72], ![864, 1477, -255, -1430, 904], ![-12048, -6268, 5286, 3135, -2824], ![16176, 8211, -7082, -3946, 3623]]]
  hmulB := by decide  
  f := ![![![143975, 98883, 35960, -44762, -37924]], ![![93253, 63676, 23002, -28830, -24372]], ![![12228, 7769, 2563, -3526, -2896]], ![![76495, 50877, 17810, -23055, -19292]], ![![34046, 21185, 6788, -9622, -7833]]]
  g := ![![![232, -389, 626, -18, -100], ![-347, 341, -1142, 452, -72], ![-389, 1477, -255, -1430, 904], ![2613, -6268, 5286, 3135, -2824], ![-3477, 8211, -7082, -3946, 3623]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2

def I317N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-403, -309, -140, 49, 56]] i)))

def SI317N3: IdealEqSpanCertificate' Table ![![-403, -309, -140, 49, 56]] 
 ![![317, 0, 0, 0, 0], ![303, 1, 0, 0, 0], ![219, 0, 1, 0, 0], ![272, 0, 0, 1, 0], ![276, 0, 0, 0, 1]] where
  M :=![![![-403, -309, -140, 49, 56], ![-1344, -1061, -492, 168, 196], ![-2352, -1828, -837, 292, 336], ![-3360, -2620, -1202, 423, 486], ![-3420, -2649, -1208, 433, 493]]]
  hmulB := by decide  
  f := ![![![4873, 1801, -2230, -373, 618]], ![![4611, 1706, -2110, -355, 586]], ![![3423, 1259, -1567, -255, 430]], ![![4168, 1554, -1906, -335, 538]], ![![4248, 1553, -1946, -305, 527]]]
  g := ![![![300, -309, -140, 49, 56], ![1035, -1061, -492, 168, 196], ![1775, -1828, -837, 292, 336], ![2538, -2620, -1202, 423, 486], ![2555, -2649, -1208, 433, 493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N3 : Nat.card (O ⧸ I317N3) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N3)

lemma isPrimeI317N3 : Ideal.IsPrime I317N3 := prime_ideal_of_norm_prime hp317.out _ NI317N3
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![43, 13, -26, -4, 8]] ![![629, 245, -320, -87, 116]]
  ![![-50809, -21278, 23922, 7759, -9120]] where
 M := ![![![-50809, -21278, 23922, 7759, -9120]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![-50809, -21278, 23922, 7759, -9120]] ![![-1349, -389, 626, -18, -100]]
  ![![-202862803, -75676035, 91994846, 17400431, -26714772]] where
 M := ![![![-202862803, -75676035, 91994846, 17400431, -26714772]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N2 : IdealMulLeCertificate' Table 
  ![![-202862803, -75676035, 91994846, 17400431, -26714772]] ![![-403, -309, -140, 49, 56]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![-10505063, -11397418, -10157948, 1529842, 3675298]]]
 hmul := by decide  
 g := ![![![![-33139, -35954, -32044, 4826, 11594]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2, I317N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
    exact isPrimeI317N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1 ⊙ MulI317N2)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 53, 12, -24, -16]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![79, 53, 12, -24, -16]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![0, 0, 331, 0, 0], ![246, 72, 17, 1, 0], ![226, 199, 222, 0, 1]] where
  M :=![![![79, 53, 12, -24, -16], ![384, 219, 90, -104, -96], ![1152, 661, 131, -294, -208], ![2304, 1382, 494, -649, -540], ![3624, 2081, 496, -928, -705]]]
  hmulB := by decide  
  f := ![![![-59, -17, 2, 4, 0]], ![![0, -49, -42, 4, 16]], ![![-192, -105, -21, 22, 8]], ![![-54, -29, -9, 5, 4]], ![![-170, -112, -38, 20, 15]]]
  g := ![![![29, 15, 12, -24, -16], ![144, 81, 70, -104, -96], ![364, 191, 155, -294, -208], ![858, 470, 397, -649, -540], ![1182, 632, 522, -928, -705]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 3 2 8 [219, 258, 298, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 13, 70], [295, 317, 261], [0, 1]]
 g := ![![[240, 82, 25], [89, 114, 100], [156, 25], [230, 34, 84], [36, 172], [119, 215], [169, 33, 1], []], ![[170, 186, 221, 58], [150, 61, 194, 171], [319, 259], [87, 26, 216, 165], [85, 186], [33, 183], [49, 245, 11, 149], [6, 266]], ![[248, 198, 245, 221], [162, 8, 94, 275], [293, 87], [224, 278, 199, 154], [8, 259], [267, 241], [270, 257, 17, 86], [146, 266]]]
 h' := ![![[69, 13, 70], [38, 25, 5], [314, 271, 10], [273, 100, 326], [149, 109, 282], [168, 145, 186], [61, 145, 154], [0, 0, 1], [0, 1]], ![[295, 317, 261], [131, 241, 25], [192, 45, 294], [199, 60, 119], [295, 188, 41], [238, 18, 264], [50, 26, 50], [137, 248, 317], [69, 13, 70]], ![[0, 1], [325, 65, 301], [214, 15, 27], [120, 171, 217], [17, 34, 8], [245, 168, 212], [88, 160, 127], [105, 83, 13], [295, 317, 261]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 205], []]
 b := ![[], [117, 291, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 3
  hpos := by decide
  P := [219, 258, 298, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34688571, 13103200, -15469748, -3081692, 4631140]
  a := ![0, -4, -2, -18, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-766927, -2074356, -2994544, -3081692, 4631140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 36264691 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16591, -1306, 8054, -4339, 1192]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![-16591, -1306, 8054, -4339, 1192]] 
 ![![331, 0, 0, 0, 0], ![63, 1, 0, 0, 0], ![167, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![320, 0, 0, 0, 1]] where
  M :=![![![-16591, -1306, 8054, -4339, 1192], ![-28608, -30327, 10834, 25644, -17356], ![208272, 112215, -90683, -58590, 51288], ![-601152, -266716, 267964, 101647, -108502], ![769452, 337178, -343442, -125139, 135969]]]
  hmulB := by decide  
  f := ![![![-587341, -85188, 101614, 42953, -9778]], ![![-111081, -17097, 18448, 8553, -1342]], ![![-302561, -45549, 51045, 22855, -4178]], ![![-16516, -6784, -568, 3129, 1990]], ![![-583940, -90496, 96498, 45247, -6725]]]
  g := ![![![-4965, -1306, 8054, -4339, 1192], ![16689, -30327, 10834, 25644, -17356], ![-23852, 112215, -90683, -58590, 51288], ![17420, -266716, 267964, 101647, -108502], ![-18512, 337178, -343442, -125139, 135969]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N1 : Nat.card (O ⧸ I331N1) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N1)

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := prime_ideal_of_norm_prime hp331.out _ NI331N1

def I331N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42509, 2039, -10570, -1269, 2862]] i)))

def SI331N2: IdealEqSpanCertificate' Table ![![42509, 2039, -10570, -1269, 2862]] 
 ![![331, 0, 0, 0, 0], ![234, 1, 0, 0, 0], ![95, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![133, 0, 0, 0, 1]] where
  M :=![![![42509, 2039, -10570, -1269, 2862], ![-68688, -2081, 18064, 1756, -5076], ![60912, 4362, -13989, -2240, 3512], ![-7800, 2946, 4594, -819, -1942], ![76452, 7351, -16086, -3585, 3475]]]
  hmulB := by decide  
  f := ![![![1788767, 642411, -813792, -124033, 218300]], ![![1248738, 449093, -568040, -87326, 152828]], ![![531379, 188701, -241981, -34325, 63372]], ![![118190, 47338, -53238, -13967, 17806]], ![![715877, 250930, -326356, -42362, 83101]]]
  g := ![![![655, 2039, -10570, -1269, 2862], ![-1998, -2081, 18064, 1756, -5076], ![-147, 4362, -13989, -2240, 3512], ![-2590, 2946, 4594, -819, -1942], ![-1507, 7351, -16086, -3585, 3475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N2 : Nat.card (O ⧸ I331N2) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N2)

lemma isPrimeI331N2 : Ideal.IsPrime I331N2 := prime_ideal_of_norm_prime hp331.out _ NI331N2
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![79, 53, 12, -24, -16]] ![![-16591, -1306, 8054, -4339, 1192]]
  ![![1788767, 642411, -813792, -124033, 218300]] where
 M := ![![![1788767, 642411, -813792, -124033, 218300]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI331N1 : IdealMulLeCertificate' Table 
  ![![1788767, 642411, -813792, -124033, 218300]] ![![42509, 2039, -10570, -1269, 2862]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![331, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC331 : ContainsPrimesAboveP 331 ![I331N0, I331N1, I331N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI331N0
    exact isPrimeI331N1
    exact isPrimeI331N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 331 (by decide) (𝕀 ⊙ MulI331N0 ⊙ MulI331N1)
instance hp337 : Fact (Nat.Prime 337) := {out := by norm_num}

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2515, -1472, 1140, 879, -742]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![-2515, -1472, 1140, 879, -742]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![161, 24, 60, 1, 0], ![225, 94, 65, 0, 1]] where
  M :=![![![-2515, -1472, 1140, 879, -742], ![17808, 8545, -7670, -3656, 3516], ![-42192, -17925, 19233, 6394, -7312], ![78840, 30858, -35108, -8187, 11030], ![-96180, -36728, 44004, 9531, -13601]]]
  hmulB := by decide  
  f := ![![![-205699, -8846, 51980, 5921, -14208]], ![![340992, 14411, -86366, -9704, 23684]], ![![-284208, -12653, 71483, 8370, -19408]], ![![-124403, -5448, 31360, 3624, -8542]], ![![-98055, -4375, 24655, 2892, -6691]]]
  g := ![![![68, 140, -10, 879, -742], ![-548, -695, -50, -3656, 3516], ![1702, 1531, 329, 6394, -7312], ![-3219, -2402, -774, -8187, 11030], ![4242, 3006, 1057, 9531, -13601]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 3 2 8 [324, 40, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [263, 81, 170], [317, 255, 167], [0, 1]]
 g := ![![[98, 144, 216], [281, 131], [136, 273], [156, 129], [49, 155, 316], [305, 310], [34, 243, 1], []], ![[130, 3, 236, 112], [249, 103], [20, 1], [165, 2], [325, 304, 160, 55], [249, 21], [61, 163, 217, 313], [200, 255]], ![[240, 139, 71, 289], [228, 170], [223, 265], [283, 94], [182, 135, 63, 167], [260, 230], [284, 68, 98, 100], [203, 255]]]
 h' := ![![[263, 81, 170], [118, 335, 280], [138, 26, 145], [27, 204, 164], [300, 13, 265], [162, 268, 84], [105, 114, 240], [0, 0, 1], [0, 1]], ![[317, 255, 167], [276, 196, 290], [181, 137, 281], [150, 57, 1], [202, 104, 26], [216, 180, 254], [247, 153, 37], [325, 177, 255], [263, 81, 170]], ![[0, 1], [153, 143, 104], [151, 174, 248], [301, 76, 172], [282, 220, 46], [24, 226, 336], [276, 70, 60], [6, 160, 81], [317, 255, 167]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [305, 77], []]
 b := ![[], [165, 143, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 3
  hpos := by decide
  P := [324, 40, 94, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13881903, 8020794, 1149532, -3726494, -2011471]
  a := ![13, -7, 4, 2, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3164476, 850252, 1054851, -3726494, -2011471]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 38272753 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-755, 33, 242, -7, -86]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-755, 33, 242, -7, -86]] 
 ![![337, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![144, 0, 1, 0, 0], ![335, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-755, 33, 242, -7, -86], ![2064, 419, -264, -204, -28], ![336, 850, 567, -376, -408], ![3864, 2110, 542, -963, -738], ![3564, 2865, 1214, -1291, -1153]]]
  hmulB := by decide  
  f := ![![![114397, 89731, 41564, -14029, -16440]], ![![3547, 2780, 1284, -435, -508]], ![![50880, 39910, 18487, -6240, -7312]], ![![116579, 91437, 42346, -14296, -16750]], ![![27300, 21415, 9920, -3349, -3923]]]
  g := ![![![-81, 33, 242, -7, -86], ![319, 419, -264, -204, -28], ![202, 850, 567, -376, -408], ![851, 2110, 542, -963, -738], ![962, 2865, 1214, -1291, -1153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1

def I337N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -6, 0, 2, 2]] i)))

def SI337N2: IdealEqSpanCertificate' Table ![![-13, -6, 0, 2, 2]] 
 ![![337, 0, 0, 0, 0], ![210, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![292, 0, 0, 1, 0], ![163, 0, 0, 0, 1]] where
  M :=![![![-13, -6, 0, 2, 2], ![-48, -31, -8, 16, 8], ![-96, -56, -31, 24, 32], ![-360, -200, -12, 89, 44], ![-288, -182, -112, 86, 101]]]
  hmulB := by decide  
  f := ![![![1115, 1838, 1208, -258, -438]], ![![726, 1165, 760, -164, -276]], ![![672, 1080, 705, -152, -256]], ![![1028, 1640, 1068, -231, -388]], ![![593, 936, 608, -132, -221]]]
  g := ![![![1, -6, 0, 2, 2], ![6, -31, -8, 16, 8], ![16, -56, -31, 24, 32], ![32, -200, -12, 89, 44], ![53, -182, -112, 86, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N2 : Nat.card (O ⧸ I337N2) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N2)

lemma isPrimeI337N2 : Ideal.IsPrime I337N2 := prime_ideal_of_norm_prime hp337.out _ NI337N2
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![-2515, -1472, 1140, 879, -742]] ![![-755, 33, 242, -7, -86]]
  ![![-4375, -1903, 1988, 698, -790]] where
 M := ![![![-4375, -1903, 1988, 698, -790]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI337N1 : IdealMulLeCertificate' Table 
  ![![-4375, -1903, 1988, 698, -790]] ![![-13, -6, 0, 2, 2]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![-66389, -21905, 33700, 2696, -9436]]]
 hmul := by decide  
 g := ![![![![-197, -65, 100, 8, -28]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1, I337N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
    exact isPrimeI337N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0 ⊙ MulI337N1)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![347, 0, 0, 0, 0]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![347, 0, 0, 0, 0]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![0, 0, 0, 347, 0], ![0, 0, 0, 0, 347]] where
  M :=![![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![0, 0, 0, 347, 0], ![0, 0, 0, 0, 347]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 5 2 8 [250, 111, 41, 182, 202, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 288, 6, 176, 246], [65, 193, 172, 284, 164], [46, 185, 72, 283, 233], [309, 27, 97, 298, 51], [0, 1]]
 g := ![![[244, 326, 239, 275, 147], [80, 167, 284, 223, 131], [308, 67, 262, 11], [238, 177, 93, 281, 156], [105, 267, 61, 48, 176], [84, 256, 194, 205], [1], []], ![[137, 64, 214, 82, 190, 111, 187, 121], [22, 216, 323, 214, 215, 300, 43, 34], [4, 19, 220, 61], [330, 287, 279, 339, 175, 337, 337, 53], [81, 163, 302, 271, 56, 39, 178, 328], [303, 194, 240, 40], [125, 311, 194, 98, 160, 119, 143, 332], [74, 312, 73, 138]], ![[75, 322, 62, 199, 265, 124, 27, 337], [166, 163, 307, 318, 177, 267, 26, 186], [282, 226, 277, 292], [150, 212, 146, 143, 184, 185, 31, 32], [95, 305, 249, 15, 254, 30, 161, 72], [307, 97, 14, 85], [212, 49, 244, 231, 13, 118, 141, 103], [99, 326, 143, 177]], ![[73, 22, 68, 169, 315, 74, 315, 335], [50, 247, 325, 37, 261, 71, 159, 101], [281, 91, 296, 224], [324, 251, 41, 246, 289, 239, 149, 320], [158, 102, 314, 306, 254, 109, 177, 273], [2, 115, 206, 35], [124, 150, 249, 52, 263, 328, 118, 214], [61, 147, 228, 157]], ![[193, 48, 155, 13, 182, 105, 134, 331], [314, 156, 312, 75, 153, 167, 2, 237], [1, 245, 232, 340], [258, 280, 85, 342, 308, 24, 202, 111], [211, 27, 181, 295, 229, 245, 48, 221], [191, 78, 2, 87], [344, 278, 331, 2, 162, 314, 35, 57], [271, 115, 163, 172]]]
 h' := ![![[72, 288, 6, 176, 246], [126, 302, 242, 279, 318], [231, 79, 163, 106, 265], [184, 83, 119, 26, 288], [122, 185, 248, 266, 230], [207, 220, 0, 146, 236], [97, 236, 306, 165, 145], [0, 0, 1], [0, 1]], ![[65, 193, 172, 284, 164], [283, 52, 106, 38, 200], [55, 39, 340, 181, 110], [328, 328, 64, 53, 282], [56, 186, 265, 96, 78], [236, 145, 280, 179, 168], [198, 192, 314, 322, 250], [217, 21, 132, 189, 295], [72, 288, 6, 176, 246]], ![[46, 185, 72, 283, 233], [279, 272, 137, 97, 295], [202, 123, 309, 130, 28], [221, 195, 294, 338, 197], [217, 167, 160, 265, 253], [122, 81, 169, 225, 141], [269, 284, 88, 234, 99], [295, 266, 270, 7, 168], [65, 193, 172, 284, 164]], ![[309, 27, 97, 298, 51], [8, 307, 155, 235, 44], [258, 64, 36, 278, 60], [121, 64, 321, 117, 76], [152, 110, 183, 14, 281], [140, 142, 207, 242, 342], [41, 135, 273, 199, 27], [52, 218, 78, 137, 243], [46, 185, 72, 283, 233]], ![[0, 1], [337, 108, 54, 45, 184], [20, 42, 193, 346, 231], [231, 24, 243, 160, 198], [106, 46, 185, 53, 199], [273, 106, 38, 249, 154], [22, 194, 60, 121, 173], [318, 189, 213, 14, 335], [309, 27, 97, 298, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 69, 15, 18], [], [], []]
 b := ![[], [205, 127, 214, 168, 330], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 5
  hpos := by decide
  P := [250, 111, 41, 182, 202, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17023075685, -7757088534, 7203075621, 3077027358, -2917969845]
  a := ![-1, -1, -1, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-49057855, -22354722, 20758143, 8867514, -8409135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 5030919566507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def PBC347 : ContainsPrimesAboveP 347 ![I347N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![347, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 347 (by decide) 𝕀

instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![811, 2646, 1962, -354, -692]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![811, 2646, 1962, -354, -692]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![0, 0, 0, 349, 0], ![77, 92, 327, 290, 1]] where
  M :=![![![811, 2646, 1962, -354, -692], ![16608, 9677, 3232, -1612, -1416], ![16992, 16096, 8457, -2432, -3224], ![30384, 23186, 10464, -3633, -4156], ![25128, 23034, 11866, -3490, -4537]]]
  hmulB := by decide  
  f := ![![![-41, -14, 18, 2, -4]], ![![96, 25, -48, 4, 8]], ![![-96, -16, 37, -16, 8]], ![![-144, -102, 40, 67, -36]], ![![-193, -96, 59, 42, -21]]]
  g := ![![![155, 190, 654, 574, -692], ![360, 401, 1336, 1172, -1416], ![760, 896, 3045, 2672, -3224], ![1004, 1162, 3924, 3443, -4156], ![1073, 1262, 4285, 3760, -4537]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 4 2 8 [9, 16, 168, 48, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [177, 321, 119, 77], [347, 172, 298, 185], [126, 204, 281, 87], [0, 1]]
 g := ![![[213, 80, 23, 207], [202, 329, 23], [112, 133, 108, 81], [201, 128, 182, 56], [95, 3, 290, 272], [216, 154, 19], [301, 1], []], ![[138, 336, 157, 310, 56, 36], [4, 107, 106], [335, 15, 324, 249, 222, 271], [218, 69, 311, 327, 20, 301], [41, 112, 246, 322, 170, 115], [92, 213, 73], [273, 86, 9, 249, 275, 233], [90, 21, 345]], ![[194, 167, 245, 62, 212, 301], [262, 25, 226], [60, 11, 168, 232, 95, 198], [50, 313, 285, 308, 337, 257], [320, 315, 248, 262], [224, 338, 205], [265, 121, 181, 203, 305, 226], [304, 268, 23]], ![[280, 328, 274, 58, 102, 142], [128, 121, 26], [12, 195, 244, 264, 92, 334], [99, 143, 80, 110, 129, 262], [77, 167, 125, 220, 258, 126], [329, 309, 346], [165, 307, 152, 89, 296, 4], [57, 31, 240]]]
 h' := ![![[177, 321, 119, 77], [52, 232, 202, 143], [39, 60, 314, 164], [285, 39, 222, 9], [192, 189, 77, 209], [59, 49, 43, 212], [83, 61, 21, 42], [0, 0, 1], [0, 1]], ![[347, 172, 298, 185], [108, 302, 91, 287], [337, 250, 91, 111], [69, 224, 17, 304], [258, 297, 219, 227], [98, 35, 305, 253], [100, 59, 73, 90], [156, 325, 268, 246], [177, 321, 119, 77]], ![[126, 204, 281, 87], [94, 167, 102, 205], [346, 283, 180, 227], [193, 235, 20, 167], [319, 173, 16, 49], [147, 170, 74], [187, 216, 323, 113], [60, 63, 47, 257], [347, 172, 298, 185]], ![[0, 1], [225, 346, 303, 63], [221, 105, 113, 196], [303, 200, 90, 218], [169, 39, 37, 213], [250, 95, 276, 233], [152, 13, 281, 104], [7, 310, 33, 195], [126, 204, 281, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [84, 249, 185], []]
 b := ![[], [], [203, 303, 73, 348], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 4
  hpos := by decide
  P := [9, 16, 168, 48, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-687171882, -400908612, -101233944, 186692730, 133264803]
  a := ![3, 3, 0, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31371237, -36278712, -125154225, -110200860, 133264803]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 14835483601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -14, 18, 2, -4]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-41, -14, 18, 2, -4]] 
 ![![349, 0, 0, 0, 0], ![236, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![111, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-41, -14, 18, 2, -4], ![96, 25, -48, 4, 8], ![-96, -16, 37, -16, 8], ![-144, -102, 40, 67, -36], ![120, 86, -78, -62, 67]]]
  hmulB := by decide  
  f := ![![![811, 2646, 1962, -354, -692]], ![![596, 1817, 1336, -244, -472]], ![![216, 592, 429, -80, -152]], ![![345, 908, 654, -123, -232]], ![![72, 66, 34, -10, -13]]]
  g := ![![![5, -14, 18, 2, -4], ![-8, 25, -48, 4, 8], ![8, -16, 37, -16, 8], ![39, -102, 40, 67, -36], ![-22, 86, -78, -62, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI349N1 : Nat.card (O ⧸ I349N1) = 349 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI349N1)

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := prime_ideal_of_norm_prime hp349.out _ NI349N1
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![811, 2646, 1962, -354, -692]] ![![-41, -14, 18, 2, -4]]
  ![![349, 0, 0, 0, 0]] where
 M := ![![![349, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC349 : ContainsPrimesAboveP 349 ![I349N0, I349N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI349N0
    exact isPrimeI349N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 349 (by decide) (𝕀 ⊙ MulI349N0)
instance hp353 : Fact (Nat.Prime 353) := {out := by norm_num}

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1099, -873, -400, 148, 150]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![-1099, -873, -400, 148, 150]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![328, 193, 1, 0, 0], ![236, 157, 0, 1, 0], ![185, 8, 0, 0, 1]] where
  M :=![![![-1099, -873, -400, 148, 150], ![-3600, -2853, -1442, 400, 592], ![-7104, -5377, -2069, 926, 800], ![-7800, -6634, -3982, 931, 1556], ![-11088, -8021, -2540, 1384, 1035]]]
  hmulB := by decide  
  f := ![![![84109, 3423, -21406, -2336, 5910]], ![![-141840, -6979, 35158, 4468, -9344]], ![![920, -628, -753, 266, 408]], ![![-6956, -835, 1340, 435, -204]], ![![41221, 1630, -10528, -1124, 2921]]]
  g := ![![![191, 147, -400, 148, 150], ![752, 589, -1442, 400, 592], ![864, 686, -2069, 926, 800], ![2240, 1709, -3982, 931, 1556], ![861, 727, -2540, 1384, 1035]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 2 2 8 [331, 352, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 352], [0, 1]]
 g := ![![[337, 16], [345], [289], [177], [218], [231, 21], [45, 1], [1]], ![[0, 337], [345], [289], [177], [218], [252, 332], [46, 352], [1]]]
 h' := ![![[1, 352], [349, 4], [284, 92], [120, 336], [39, 260], [140, 159], [284, 198], [22, 1], [0, 1]], ![[0, 1], [0, 349], [23, 261], [103, 17], [299, 93], [299, 194], [129, 155], [23, 352], [1, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [230]]
 b := ![[], [119, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 2
  hpos := by decide
  P := [331, 352, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1032, -144, -8595, 1398, 8475]
  a := ![1, 5, -3, -2, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2613, 3885, -8595, 1398, 8475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, -62, -28, 11, 12]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![-79, -62, -28, 11, 12]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![332, 53, 1, 0, 0], ![54, 5, 0, 1, 0], ![42, 261, 0, 0, 1]] where
  M :=![![![-79, -62, -28, 11, 12], ![-288, -217, -98, 40, 44], ![-528, -395, -169, 78, 80], ![-816, -602, -264, 131, 134], ![-924, -662, -268, 155, 149]]]
  hmulB := by decide  
  f := ![![![265, 8, -60, -15, 22]], ![![-528, -67, 134, 56, -60]], ![![172, -2, -37, -6, 12]], ![![30, -1, -6, -1, 2]], ![![-354, -47, 90, 39, -41]]]
  g := ![![![23, -5, -28, 11, 12], ![80, -19, -98, 40, 44], ![136, -36, -169, 78, 80], ![210, -63, -264, 131, 134], ![208, -74, -268, 155, 149]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P1 : CertificateIrreducibleZModOfList' 353 2 2 8 [239, 324, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 352], [0, 1]]
 g := ![![[313, 82], [44], [182], [315], [68], [215, 349], [290, 135], [1]], ![[220, 271], [44], [182], [315], [68], [99, 4], [322, 218], [1]]]
 h' := ![![[29, 352], [49, 105], [143, 165], [135, 270], [97, 149], [153, 189], [231, 84], [114, 29], [0, 1]], ![[0, 1], [270, 248], [339, 188], [199, 83], [182, 204], [339, 164], [196, 269], [249, 324], [29, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175]]
 b := ![[], [55, 264]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N1 : CertifiedPrimeIdeal' SI353N1 353 where
  n := 2
  hpos := by decide
  P := [239, 324, 1]
  hirr := P353P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1875, 134, -152, 286, -273]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![137, 221, -152, 286, -273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N1 B_one_repr
lemma NI353N1 : Nat.card (O ⧸ I353N1) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N1

def I353N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![941, 809, 362, -364, -332]] i)))

def SI353N2: IdealEqSpanCertificate' Table ![![941, 809, 362, -364, -332]] 
 ![![353, 0, 0, 0, 0], ![214, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![159, 0, 0, 1, 0], ![235, 0, 0, 0, 1]] where
  M :=![![![941, 809, 362, -364, -332], ![7968, 4227, 1018, -1932, -1456], ![17472, 10569, 3247, -4806, -3864], ![42384, 24692, 7138, -11243, -8884], ![58056, 34361, 10198, -15636, -12447]]]
  hmulB := by decide  
  f := ![![![26245, 12081, -11692, -4976, 5068]], ![![15566, 7179, -6934, -2968, 3016]], ![![4171, 1872, -1863, -734, 772]], ![![10827, 5093, -4814, -2183, 2168]], ![![18671, 8456, -8332, -3376, 3509]]]
  g := ![![![-151, 809, 362, -364, -332], ![-836, 4227, 1018, -1932, -1456], ![-2053, 10569, 3247, -4806, -3864], ![-4821, 24692, 7138, -11243, -8884], ![-6695, 34361, 10198, -15636, -12447]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N2 : Nat.card (O ⧸ I353N2) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N2)

lemma isPrimeI353N2 : Ideal.IsPrime I353N2 := prime_ideal_of_norm_prime hp353.out _ NI353N2
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![-1099, -873, -400, 148, 150]] ![![-79, -62, -28, 11, 12]]
  ![![290077, 227183, 104654, -35571, -41418]] where
 M := ![![![290077, 227183, 104654, -35571, -41418]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N1 : IdealMulLeCertificate' Table 
  ![![290077, 227183, 104654, -35571, -41418]] ![![941, 809, 362, -364, -332]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![-533383, -420070, -194856, 63893, 75542]]]
 hmul := by decide  
 g := ![![![![-1511, -1190, -552, 181, 214]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1, I353N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
    exact isPrimeI353N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0 ⊙ MulI353N1)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1523, 64, -386, -43, 106]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![1523, 64, -386, -43, 106]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![1, 81, 1, 0, 0], ![278, 261, 0, 1, 0], ![229, 310, 0, 0, 1]] where
  M :=![![![1523, 64, -386, -43, 106], ![-2544, -115, 638, 76, -172], ![2064, 69, -535, -50, 152], ![-552, -64, 104, 35, -14], ![2388, 36, -650, -39, 197]]]
  hmulB := by decide  
  f := ![![![133, 82, -18, -27, 12]], ![![-288, -71, 266, 60, -108]], ![![-61, -14, 59, 13, -24]], ![![-110, 11, 182, 23, -70]], ![![-157, -6, 216, 34, -85]]]
  g := ![![![-29, 27, -386, -43, 106], ![42, -51, 638, 76, -172], ![-51, 26, -535, -50, 152], ![-20, -37, 104, 35, -14], ![-87, 5, -650, -39, 197]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 2 2 8 [23, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [304, 358], [0, 1]]
 g := ![![[18, 281], [335, 202], [113, 20], [73], [133], [67, 270], [218, 153], [1]], ![[0, 78], [354, 157], [90, 339], [73], [133], [295, 89], [60, 206], [1]]]
 h' := ![![[304, 358], [193, 121], [273, 90], [73, 296], [68, 198], [254, 301], [12, 98], [336, 304], [0, 1]], ![[0, 1], [0, 238], [349, 269], [307, 63], [307, 161], [213, 58], [7, 261], [130, 55], [304, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [253]]
 b := ![[], [158, 306]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 2
  hpos := by decide
  P := [23, 55, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-212675, -114375, -23778, 62727, 46182]
  a := ![7, -21, -1, -23, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78559, -80436, -23778, 62727, 46182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-89, -23, 8, 14, 6]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![-89, -23, 8, 14, 6]] 
 ![![359, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![351, 0, 0, 1, 0], ![353, 0, 0, 0, 1]] where
  M :=![![![-89, -23, 8, 14, 6], ![-144, -119, -50, 64, 56], ![-672, -341, -71, 174, 128], ![-1464, -842, -234, 409, 320], ![-2184, -1211, -316, 578, 445]]]
  hmulB := by decide  
  f := ![![![401, -717, -278, 994, -550]], ![![144, -169, -90, 252, -136]], ![![-67, -182, 13, 192, -118]], ![![705, -569, -412, 927, -486]], ![![-1, -870, -96, 1032, -605]]]
  g := ![![![-15, -23, 8, 14, 6], ![-78, -119, -50, 64, 56], ![-195, -341, -71, 174, 128], ![-455, -842, -234, 409, 320], ![-633, -1211, -316, 578, 445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N1 : Nat.card (O ⧸ I359N1) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N1)

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := prime_ideal_of_norm_prime hp359.out _ NI359N1

def I359N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-769, -318, -28, 147, 94]] i)))

def SI359N2: IdealEqSpanCertificate' Table ![![-769, -318, -28, 147, 94]] 
 ![![359, 0, 0, 0, 0], ![208, 1, 0, 0, 0], ![267, 0, 1, 0, 0], ![130, 0, 0, 1, 0], ![270, 0, 0, 0, 1]] where
  M :=![![![-769, -318, -28, 147, 94], ![-2256, -1537, -554, 696, 588], ![-7056, -3943, -1057, 1798, 1392], ![-15576, -9146, -2680, 4163, 3302], ![-22212, -12766, -3604, 5815, 4565]]]
  hmulB := by decide  
  f := ![![![16273, 12888, 6028, -2081, -2328]], ![![9584, 7589, 3550, -1224, -1372]], ![![12381, 9801, 4577, -1583, -1768]], ![![6254, 4958, 2332, -797, -902]], ![![12654, 10008, 4660, -1617, -1801]]]
  g := ![![![79, -318, -28, 147, 94], ![602, -1537, -554, 696, 588], ![1353, -3943, -1057, 1798, 1392], ![3258, -9146, -2680, 4163, 3302], ![4476, -12766, -3604, 5815, 4565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N2 : Nat.card (O ⧸ I359N2) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N2)

lemma isPrimeI359N2 : Ideal.IsPrime I359N2 := prime_ideal_of_norm_prime hp359.out _ NI359N2

def I359N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 35, -48, -18, 6]] i)))

def SI359N3: IdealEqSpanCertificate' Table ![![263, 35, -48, -18, 6]] 
 ![![359, 0, 0, 0, 0], ![252, 1, 0, 0, 0], ![199, 0, 1, 0, 0], ![289, 0, 0, 1, 0], ![255, 0, 0, 0, 1]] where
  M :=![![![263, 35, -48, -18, 6], ![-144, 113, 130, -48, -72], ![864, 341, 17, -158, -96], ![1224, 754, 242, -343, -280], ![2184, 1079, 212, -494, -355]]]
  hmulB := by decide  
  f := ![![![32497, 25481, 11810, -3974, -4678]], ![![23124, 18131, 8402, -2828, -3328]], ![![18545, 14542, 6741, -2268, -2670]], ![![26927, 21111, 9780, -3293, -3874]], ![![23841, 18696, 8668, -2916, -3433]]]
  g := ![![![13, 35, -48, -18, 6], ![-62, 113, 130, -48, -72], ![-51, 341, 17, -158, -96], ![-185, 754, 242, -343, -280], ![-219, 1079, 212, -494, -355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI359N3 : Nat.card (O ⧸ I359N3) = 359 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI359N3)

lemma isPrimeI359N3 : Ideal.IsPrime I359N3 := prime_ideal_of_norm_prime hp359.out _ NI359N3
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![1523, 64, -386, -43, 106]] ![![-89, -23, 8, 14, 6]]
  ![![-53923, -3179, 12956, 1935, -3276]] where
 M := ![![![-53923, -3179, 12956, 1935, -3276]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI359N1 : IdealMulLeCertificate' Table 
  ![![-53923, -3179, 12956, 1935, -3276]] ![![-769, -318, -28, 147, 94]]
  ![![-151973, -4927965, -3802578, 2161088, 2531168]] where
 M := ![![![-151973, -4927965, -3802578, 2161088, 2531168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI359N2 : IdealMulLeCertificate' Table 
  ![![-151973, -4927965, -3802578, 2161088, 2531168]] ![![263, 35, -48, -18, 6]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![5557473293, 2501732426, 361606340, -1151565018, -784720150]]]
 hmul := by decide  
 g := ![![![![15480427, 6968614, 1007260, -3207702, -2185850]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1, I359N2, I359N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
    exact isPrimeI359N2
    exact isPrimeI359N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0 ⊙ MulI359N1 ⊙ MulI359N2)


lemma PB934I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB934I7 : PrimesBelowBoundCertificateInterval O 307 359 934 where
  m := 9
  g := ![2, 3, 4, 3, 3, 1, 2, 3, 4]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB934I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0, I317N1, I317N2, I317N3]
    · exact ![I331N0, I331N1, I331N2]
    · exact ![I337N0, I337N1, I337N2]
    · exact ![I347N0]
    · exact ![I349N0, I349N1]
    · exact ![I353N0, I353N1, I353N2]
    · exact ![I359N0, I359N1, I359N2, I359N3]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
    · exact PBC331
    · exact PBC337
    · exact PBC347
    · exact PBC349
    · exact PBC353
    · exact PBC359
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![30080231, 96721]
    · exact ![97969, 97969, 313]
    · exact ![100489, 317, 317, 317]
    · exact ![36264691, 331, 331]
    · exact ![38272753, 337, 337]
    · exact ![5030919566507]
    · exact ![14835483601, 349]
    · exact ![124609, 124609, 353]
    · exact ![128881, 359, 359, 359]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
      exact NI317N3
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
      exact NI331N2
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
      exact NI337N2
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
      exact NI353N2
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
      exact NI359N2
      exact NI359N3
  β := ![I313N2, I317N1, I317N2, I317N3, I331N1, I331N2, I337N1, I337N2, I349N1, I353N2, I359N1, I359N2, I359N3]
  Il := ![[], [I313N2], [I317N1, I317N2, I317N3], [I331N1, I331N2], [I337N1, I337N2], [], [I349N1], [I353N2], [I359N1, I359N2, I359N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
