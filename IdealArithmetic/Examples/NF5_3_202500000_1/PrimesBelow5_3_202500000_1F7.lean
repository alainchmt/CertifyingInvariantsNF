
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![807, -343, -61, 90, -344]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![807, -343, -61, 90, -344]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![27, 275, 32, 1, 0], ![134, 63, 42, 0, 1]] where
  M :=![![![807, -343, -61, 90, -344], ![-2572, 614, -12, -437, 540], ![3446, -2457, -685, 67, -2622], ![-6656, -89, -756, -1660, -560], ![-1754, -98, -228, -462, -231]]]
  hmulB := by decide  
  f := ![![![-113, 45, 29, -4, -46]], ![![-376, -192, 4, 37, -24]], ![![-118, -367, -85, 25, 222]], ![![-353, -204, -3, 35, -2]], ![![-140, -68, 2, 9, 5]]]
  g := ![![![143, -11, 37, 90, -344], ![-203, 279, -28, -437, 540], ![1135, 464, 345, 67, -2622], ![364, 1581, 244, -1660, -560], ![134, 455, 78, -462, -231]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 3 2 8 [44, 101, 202, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 149, 215], [86, 161, 96], [0, 1]]
 g := ![![[261, 112, 78], [175, 238, 98], [279, 57, 13], [75, 300], [64, 174, 113], [89, 47, 200], [109, 1], []], ![[202, 164, 226, 264], [239, 225, 205, 99], [277, 174, 247, 296], [196, 147], [217, 118, 200, 255], [172, 222, 27, 185], [121, 108], [18, 197]], ![[107, 183, 212, 200], [278, 136, 247, 107], [222, 109, 220, 212], [137, 245], [128, 62, 184, 193], [90, 289, 266, 147], [74, 120], [137, 197]]]
 h' := ![![[23, 149, 215], [75, 304, 155], [164, 262, 151], [99, 176, 293], [294, 143, 61], [127, 195, 51], [180, 143, 273], [0, 0, 1], [0, 1]], ![[86, 161, 96], [201, 151, 125], [65, 24, 92], [173, 166, 110], [291, 39, 136], [218, 256, 65], [90, 91, 58], [48, 100, 161], [23, 149, 215]], ![[0, 1], [33, 167, 31], [57, 25, 68], [252, 280, 219], [252, 129, 114], [207, 171, 195], [302, 77, 291], [124, 211, 149], [86, 161, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 138], []]
 b := ![[], [157, 102, 293], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 3
  hpos := by decide
  P := [44, 101, 202, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-71151226, -26076885, -18979602, -25425431, -35216634]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17152297, 29532362, 7311038, -25425431, -35216634]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 30080231 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-113, 45, 29, -4, -46]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![-113, 45, 29, -4, -46]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![171, 214, 1, 0, 0], ![299, 309, 0, 1, 0], ![233, 222, 0, 0, 1]] where
  M :=![![![-113, 45, 29, -4, -46], ![-376, -192, 4, 37, -24], ![-118, -367, -85, 25, 222], ![444, -115, -96, 18, 116], ![246, 332, 54, -46, -93]]]
  hmulB := by decide  
  f := ![![![807, -343, -61, 90, -344]], ![![-2572, 614, -12, -437, 540]], ![![-1315, 226, -44, -251, 174]], ![![-1801, 280, -73, -353, 204]], ![![-1237, 181, -55, -246, 127]]]
  g := ![![![22, 17, 29, -4, -46], ![-21, -23, 4, 37, -24], ![-144, -126, -85, 25, 222], ![-50, -35, -96, 18, 116], ![85, 76, 54, -46, -93]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P1 : CertificateIrreducibleZModOfList' 311 2 2 8 [38, 224, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 310], [0, 1]]
 g := ![![[55, 254], [185, 47], [214, 128], [32], [294, 100], [196, 292], [105], [1]], ![[72, 57], [231, 264], [154, 183], [32], [286, 211], [98, 19], [105], [1]]]
 h' := ![![[87, 310], [123, 253], [265, 83], [293, 217], [24, 264], [16, 301], [253, 35], [273, 87], [0, 1]], ![[0, 1], [53, 58], [22, 228], [201, 94], [289, 47], [79, 10], [188, 276], [67, 224], [87, 310]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [278]]
 b := ![[], [18, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N1 : CertifiedPrimeIdeal' SI311N1 311 where
  n := 2
  hpos := by decide
  P := [38, 224, 1]
  hirr := P311P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5034870, 4885939, 3785748, 2243542, 7243413]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9649075, -9988927, 3785748, 2243542, 7243413]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N1 B_one_repr
lemma NI311N1 : Nat.card (O ⧸ I311N1) = 96721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N1
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![807, -343, -61, 90, -344]] ![![-113, 45, 29, -4, -46]]
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

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3935, 329, -455, 226, -434]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![3935, 329, -455, 226, -434]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![0, 0, 0, 313, 0], ![296, 287, 309, 24, 1]] where
  M :=![![![3935, 329, -455, 226, -434], ![-3020, 4182, 1462, -1573, 1356], ![7702, -4699, -1999, 4169, -9438], ![-20828, 1305, 3090, -2890, 5644], ![5374, -2202, -1350, 588, 807]]]
  hmulB := by decide  
  f := ![![![2361, -813, -99, 324, -788]], ![![-5656, 1996, 258, -761, 1944]], ![![14030, -4731, -545, 1957, -4566]], ![![-8080, 3077, 466, -1016, 3040]], ![![10272, -3371, -359, 1462, -3235]]]
  g := ![![![423, 399, 427, 34, -434], ![-1292, -1230, -1334, -109, 1356], ![8950, 8639, 9311, 737, -9438], ![-5404, -5171, -5562, -442, 5644], ![-746, -747, -801, -60, 807]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 4 2 8 [249, 16, 164, 155, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 294, 224, 223], [152, 39, 204, 162], [285, 292, 198, 241], [0, 1]]
 g := ![![[69, 46, 209, 26], [94, 300, 263], [83, 137, 286], [120, 224, 174, 278], [233, 268, 188, 49], [102, 217, 20, 237], [1], []], ![[60, 46, 115, 208, 53, 138], [12, 142, 87], [135, 195, 83], [26, 257, 52, 203, 239, 239], [179, 67, 205, 47, 219, 135], [186, 25, 312, 157, 125, 159], [129, 143, 158], [45, 0, 275]], ![[296, 120, 111, 99, 261, 261], [178, 22, 156], [173, 98, 72], [48, 71, 252, 293, 273, 25], [136, 194, 192, 245, 116, 286], [303, 92, 68, 266, 75, 108], [237, 17, 312], [278, 294, 265]], ![[207, 10, 164, 112, 243, 255], [305, 115, 278], [66, 251, 142], [92, 185, 223, 172, 32, 200], [217, 294, 278, 125, 109, 2], [69, 161, 57, 293, 262, 35], [31, 8, 305], [101, 235, 176]]]
 h' := ![![[34, 294, 224, 223], [216, 238, 1, 85], [45, 279, 223, 24], [168, 233, 31, 278], [201, 112, 252, 61], [268, 76, 3, 306], [64, 297, 149, 158], [0, 0, 1], [0, 1]], ![[152, 39, 204, 162], [120, 269, 287, 139], [164, 30, 121, 293], [188, 254, 154, 205], [188, 172, 200, 35], [0, 234, 199, 239], [268, 282, 243, 48], [280, 179, 147, 285], [34, 294, 224, 223]], ![[285, 292, 198, 241], [268, 130, 123, 216], [12, 248, 305, 248], [258, 280, 50, 219], [55, 222, 262, 71], [277, 43, 197, 129], [12, 267, 286, 123], [206, 245, 153, 288], [152, 39, 204, 162]], ![[0, 1], [85, 302, 215, 186], [270, 69, 290, 61], [134, 172, 78, 237], [7, 120, 225, 146], [95, 273, 227, 265], [3, 93, 261, 297], [49, 202, 12, 53], [285, 292, 198, 241]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [245, 53, 149], []]
 b := ![[], [], [167, 206, 102, 229], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 4
  hpos := by decide
  P := [249, 16, 164, 155, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54726438241, 19426852168, 14304947741, 19516674413, 26396404950]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24787889543, -24141665714, -26013367993, -1961651899, 26396404950]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 9597924961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2361, 813, 99, -324, 788]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![-2361, 813, 99, -324, 788]] 
 ![![313, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![235, 0, 1, 0, 0], ![251, 0, 0, 1, 0], ![255, 0, 0, 0, 1]] where
  M :=![![![-2361, 813, 99, -324, 788], ![5656, -1996, -258, 761, -1944], ![-14030, 4731, 545, -1957, 4566], ![8080, -3077, -466, 1016, -3040], ![1798, -704, -112, 220, -699]]]
  hmulB := by decide  
  f := ![![![-3935, -329, 455, -226, 434]], ![![-2115, -191, 241, -117, 230]], ![![-2979, -232, 348, -183, 356]], ![![-3089, -268, 355, -172, 330]], ![![-3223, -261, 375, -186, 351]]]
  g := ![![![-903, 813, 99, -324, 788], ![2263, -1996, -258, 761, -1944], ![-5159, 4731, 545, -1957, 4566], ![3699, -3077, -466, 1016, -3040], ![863, -704, -112, 220, -699]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![3935, 329, -455, 226, -434]] ![![-2361, 813, 99, -324, 788]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![-313, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6833, -2371, -294, 931, -2302]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![6833, -2371, -294, 931, -2302]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![181, 300, 46, 1, 0], ![298, 258, 298, 0, 1]] where
  M :=![![![6833, -2371, -294, 931, -2302], ![-16554, 5756, 716, -2253, 5586], ![40182, -13937, -1719, 5481, -13518], ![-24518, 8561, 1074, -3322, 8318], ![-5540, 1940, 246, -752, 1887]]]
  hmulB := by decide  
  f := ![![![25, -15, -8, -1, 22]], ![![174, 54, -10, -3, -6]], ![![-54, 175, 55, -39, -18]], ![![171, 68, -6, -9, 4]], ![![114, 194, 36, -40, -1]]]
  g := ![![![1654, 985, 2028, 931, -2302], ![-4017, -2396, -4922, -2253, 5586], ![9705, 5771, 11907, 5481, -13518], ![-6000, -3599, -7334, -3322, 8318], ![-1362, -818, -1664, -752, 1887]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [293, 223, 186, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 189, 104], [287, 127, 213], [0, 1]]
 g := ![![[152, 311, 259], [201, 213], [277, 214, 53], [51, 176, 24], [200, 182, 135], [84, 211, 66], [131, 1], []], ![[136, 310, 174, 103], [278, 232], [251, 148, 135, 179], [297, 296, 67, 205], [179, 119, 91, 131], [74, 254, 16, 240], [179, 279], [227, 38]], ![[282, 268, 60, 264], [136, 228], [16, 124, 70, 39], [276, 200, 29, 100], [143, 19, 92, 232], [59, 121, 191, 274], [90, 217], [118, 38]]]
 h' := ![![[161, 189, 104], [150, 211, 24], [308, 142, 119], [273, 265, 147], [45, 26, 138], [114, 5, 120], [291, 292, 137], [0, 0, 1], [0, 1]], ![[287, 127, 213], [183, 282, 266], [265, 296, 83], [304, 12, 264], [80, 3, 259], [190, 134, 227], [54, 137, 217], [303, 54, 127], [161, 189, 104]], ![[0, 1], [17, 141, 27], [160, 196, 115], [125, 40, 223], [107, 288, 237], [200, 178, 287], [53, 205, 280], [245, 263, 189], [287, 127, 213]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [237, 170], []]
 b := ![[], [120, 61, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [293, 223, 186, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9476695891, 4582248939, 3374894598, 3554934651, 6369049444]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7987202556, -8533479189, -6492519980, 3554934651, 6369049444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2503, -780, -525, 635, -1204]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![2503, -780, -525, 635, -1204]] 
 ![![317, 0, 0, 0, 0], ![240, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![305, 0, 0, 1, 0], ![184, 0, 0, 0, 1]] where
  M :=![![![2503, -780, -525, 635, -1204], ![-8362, 2459, 1650, -2144, 3810], ![26192, -8346, -5623, 6616, -12864], ![-23950, 6560, 4384, -6215, 10214], ![3002, -1126, -764, 732, -1719]]]
  hmulB := by decide  
  f := ![![![24981, 11774, -539, -1983, 850]], ![![18922, 8991, -388, -1510, 606]], ![![7090, 3434, -129, -574, 200]], ![![23803, 11206, -517, -1888, 816]], ![![14674, 6822, -342, -1154, 545]]]
  g := ![![![842, -780, -525, 635, -1204], ![-2526, 2459, 1650, -2144, 3810], ![9170, -8346, -5623, 6616, -12864], ![-6291, 6560, 4384, -6215, 10214], ![1382, -1126, -764, 732, -1719]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N1 : Nat.card (O ⧸ I317N1) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N1)

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := prime_ideal_of_norm_prime hp317.out _ NI317N1

def I317N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![591, -282, -58, 56, -288]] i)))

def SI317N2: IdealEqSpanCertificate' Table ![![591, -282, -58, 56, -288]] 
 ![![317, 0, 0, 0, 0], ![255, 1, 0, 0, 0], ![277, 0, 1, 0, 0], ![196, 0, 0, 1, 0], ![227, 0, 0, 0, 1]] where
  M :=![![![591, -282, -58, 56, -288], ![-2192, 417, -56, -406, 336], ![1876, -2206, -745, -238, -2436], ![-6760, -614, -992, -1851, -1176], ![-1828, -236, -296, -524, -397]]]
  hmulB := by decide  
  f := ![![![10715, 29306, 6434, -3568, -11880]], ![![8297, 23539, 5214, -2858, -9624]], ![![8847, 25192, 5585, -3058, -10308]], ![![6580, 17854, 3912, -2175, -7224]], ![![8153, 21242, 4606, -2596, -8509]]]
  g := ![![![451, -282, -58, 56, -288], ![-283, 417, -56, -406, 336], ![4323, -2206, -745, -238, -2436], ![3326, -614, -992, -1851, -1176], ![1051, -236, -296, -524, -397]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI317N2 : Nat.card (O ⧸ I317N2) = 317 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI317N2)

lemma isPrimeI317N2 : Ideal.IsPrime I317N2 := prime_ideal_of_norm_prime hp317.out _ NI317N2
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![6833, -2371, -294, 931, -2302]] ![![2503, -780, -525, 635, -1204]]
  ![![20799, -6893, -6081, 6046, -12054]] where
 M := ![![![20799, -6893, -6081, 6046, -12054]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI317N1 : IdealMulLeCertificate' Table 
  ![![20799, -6893, -6081, 6046, -12054]] ![![591, -282, -58, 56, -288]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![-2842539, 3807487, 1280363, 535730, 4182498]]]
 hmul := by decide  
 g := ![![![![-8967, 12011, 4039, 1690, 13194]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1, I317N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
    exact isPrimeI317N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0 ⊙ MulI317N1)
instance hp331 : Fact (Nat.Prime 331) := {out := by norm_num}

def I331N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![185, 136, 10, -20, -22]] i)))

def SI331N0: IdealEqSpanCertificate' Table ![![185, 136, 10, -20, -22]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![226, 170, 1, 0, 0], ![288, 318, 0, 1, 0], ![329, 113, 0, 0, 1]] where
  M :=![![![185, 136, 10, -20, -22], ![-216, 133, 66, -12, -120], ![-984, -414, 31, 66, -72], ![-548, -434, -50, 47, 68], ![664, 148, -62, -38, 99]]]
  hmulB := by decide  
  f := ![![![-16909, 5140, 3466, -4316, 7958]], ![![55032, -16733, -11274, 14040, -25896]], ![![16178, -4920, -3313, 4126, -7612]], ![![38620, -11744, -7910, 9851, -18172]], ![![1913, -583, -390, 486, -899]]]
  g := ![![![33, 22, 10, -20, -22], ![84, 19, 66, -12, -120], ![-10, -56, 31, 66, -72], ![-76, -44, -50, 47, 68], ![-21, 35, -62, -38, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P0 : CertificateIrreducibleZModOfList' 331 2 2 8 [202, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [306, 330], [0, 1]]
 g := ![![[241, 195], [300, 328], [68], [67, 268], [82], [183], [102, 294], [1]], ![[0, 136], [44, 3], [68], [318, 63], [82], [183], [34, 37], [1]]]
 h' := ![![[306, 330], [304, 224], [211, 268], [37, 125], [63, 277], [210, 134], [249, 50], [129, 306], [0, 1]], ![[0, 1], [0, 107], [131, 63], [222, 206], [89, 54], [170, 197], [323, 281], [92, 25], [306, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [96, 246]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N0 : CertifiedPrimeIdeal' SI331N0 331 where
  n := 2
  hpos := by decide
  P := [202, 25, 1]
  hirr := P331P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20604, 78451, 62835, 16070, 121900]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-177986, -89089, 62835, 16070, 121900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N0 : Ideal.IsPrime I331N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N0 B_one_repr
lemma NI331N0 : Nat.card (O ⧸ I331N0) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N0

def I331N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 56, 11, -9, -14]] i)))

def SI331N1: IdealEqSpanCertificate' Table ![![3, 56, 11, -9, -14]] 
 ![![331, 0, 0, 0, 0], ![0, 331, 0, 0, 0], ![189, 303, 1, 0, 0], ![172, 123, 0, 1, 0], ![85, 155, 0, 0, 1]] where
  M :=![![![3, 56, 11, -9, -14], ![-130, -31, 18, 10, -54], ![-412, -192, -19, 10, 60], ![-14, -182, -48, 11, 22], ![262, 124, -6, -24, -9]]]
  hmulB := by decide  
  f := ![![![-19945, 6066, 4075, -5081, 9376]], ![![64846, -19725, -13252, 16520, -30486]], ![![47335, -14399, -9674, 12059, -22254]], ![![14276, -4343, -2918, 3637, -6712]], ![![25165, -7655, -5143, 6411, -11831]]]
  g := ![![![2, 0, 11, -9, -14], ![-2, 5, 18, 10, -54], ![-11, -15, -19, 10, 60], ![16, 29, -48, 11, 22], ![19, 19, -6, -24, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P331P1 : CertificateIrreducibleZModOfList' 331 2 2 8 [80, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [227, 330], [0, 1]]
 g := ![![[233, 120], [83, 74], [49], [41, 304], [265], [89], [295, 224], [1]], ![[0, 211], [0, 257], [49], [201, 27], [265], [89], [169, 107], [1]]]
 h' := ![![[227, 330], [311, 38], [290, 111], [30, 324], [80, 142], [33, 179], [232, 168], [251, 227], [0, 1]], ![[0, 1], [0, 293], [0, 220], [96, 7], [207, 189], [284, 152], [303, 163], [144, 104], [227, 330]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [139, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI331N1 : CertifiedPrimeIdeal' SI331N1 331 where
  n := 2
  hpos := by decide
  P := [80, 104, 1]
  hirr := P331P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-66012, 23684, 22888, -24352, 42780]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11600, -31864, 22888, -24352, 42780]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI331N1 : Ideal.IsPrime I331N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI331N1 B_one_repr
lemma NI331N1 : Nat.card (O ⧸ I331N1) = 109561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI331N1

def I331N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-85, -34, -24, -32, -46]] i)))

def SI331N2: IdealEqSpanCertificate' Table ![![-85, -34, -24, -32, -46]] 
 ![![331, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-85, -34, -24, -32, -46], ![-432, -139, -106, -150, -192], ![-1836, -668, -483, -660, -900], ![-3596, -1240, -918, -1273, -1684], ![-1052, -364, -270, -374, -495]]]
  hmulB := by decide  
  f := ![![![-17767, 5394, 3632, -4544, 8414]], ![![-9969, 3027, 2038, -2550, 4722]], ![![-2019, 614, 413, -516, 954]], ![![-910, 276, 186, -233, 432]], ![![-6781, 2058, 1386, -1734, 3211]]]
  g := ![![![41, -34, -24, -32, -46], ![171, -139, -106, -150, -192], ![807, -668, -483, -660, -900], ![1508, -1240, -918, -1273, -1684], ![443, -364, -270, -374, -495]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI331N2 : Nat.card (O ⧸ I331N2) = 331 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI331N2)

lemma isPrimeI331N2 : Ideal.IsPrime I331N2 := prime_ideal_of_norm_prime hp331.out _ NI331N2
def MulI331N0 : IdealMulLeCertificate' Table 
  ![![185, 136, 10, -20, -22]] ![![3, 56, 11, -9, -14]]
  ![![-26729, 5136, 5385, 103, -9576]] where
 M := ![![![-26729, 5136, 5385, 103, -9576]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI331N1 : IdealMulLeCertificate' Table 
  ![![-26729, 5136, 5385, 103, -9576]] ![![-85, -34, -24, -32, -46]]
  ![![331, 0, 0, 0, 0]] where
 M := ![![![-130083, -44354, -12909, -18867, -36410]]]
 hmul := by decide  
 g := ![![![![-393, -134, -39, -57, -110]]]]
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

def I337N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3747, 1218, 783, -1003, 1866]] i)))

def SI337N0: IdealEqSpanCertificate' Table ![![-3747, 1218, 783, -1003, 1866]] 
 ![![337, 0, 0, 0, 0], ![0, 337, 0, 0, 0], ![0, 0, 337, 0, 0], ![0, 0, 0, 337, 0], ![199, 57, 157, 95, 1]] where
  M :=![![![-3747, 1218, 783, -1003, 1866], ![12922, -3667, -2574, 3212, -6018], ![-41720, 12690, 8543, -10528, 19272], ![34774, -10832, -7156, 9019, -16638], ![-5018, 1384, 986, -1288, 2537]]]
  hmulB := by decide  
  f := ![![![-389, 136, 17, -53, 132]], ![![950, -327, -40, 130, -318]], ![![-2284, 802, 103, -308, 780]], ![![1430, -480, -54, 201, -462]], ![![-729, 263, 36, -96, 257]]]
  g := ![![![-1113, -312, -867, -529, 1866], ![3592, 1007, 2796, 1706, -6018], ![-11504, -3222, -8953, -5464, 19272], ![9928, 2782, 7730, 4717, -16638], ![-1513, -425, -1179, -719, 2537]]]
  hle1 := by decide   
  hle2 := by decide  


def P337P0 : CertificateIrreducibleZModOfList' 337 4 2 8 [210, 303, 53, 205, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 187, 285, 265], [48, 328, 161, 318], [9, 158, 228, 91], [0, 1]]
 g := ![![[120, 191, 192, 168], [230, 230, 225], [167, 247, 172], [114, 198, 312], [109, 175, 295, 324], [109, 230, 156], [132, 1], []], ![[82, 180, 53, 201, 19, 211], [112, 336, 112], [284, 147, 321], [284, 280, 72], [137, 3, 294, 191, 318, 128], [220, 43, 239], [148, 56, 35, 235, 223, 331], [181, 252, 129]], ![[77, 296, 87, 63, 311, 174], [303, 245, 18], [102, 257, 107], [112, 184, 187], [165, 38, 279, 99, 301, 132], [299, 247, 64], [214, 79, 20, 218, 21, 205], [225, 83, 24]], ![[277, 4, 242, 260, 103, 193], [60, 137, 47], [41, 286, 283], [129, 179, 295], [336, 138, 252, 317, 12, 6], [313, 41, 253], [207, 195, 171, 109, 116, 145], [198, 246, 193]]]
 h' := ![![[75, 187, 285, 265], [256, 264, 328, 98], [99, 56, 141, 15], [326, 73, 335, 138], [26, 46, 195, 66], [8, 82, 215, 18], [251, 234, 115, 184], [0, 0, 1], [0, 1]], ![[48, 328, 161, 318], [27, 188, 143, 109], [235, 293, 302, 139], [30, 72, 165, 255], [37, 237, 5, 156], [309, 154, 76, 85], [45, 311, 200, 313], [304, 156, 65, 176], [75, 187, 285, 265]], ![[9, 158, 228, 91], [253, 247, 130, 231], [223, 219, 180, 259], [225, 88, 174, 118], [250, 299, 318, 290], [332, 206, 55, 329], [56, 308, 14, 8], [212, 140, 46, 164], [48, 328, 161, 318]], ![[0, 1], [36, 312, 73, 236], [29, 106, 51, 261], [302, 104, 0, 163], [203, 92, 156, 162], [83, 232, 328, 242], [182, 158, 8, 169], [289, 41, 225, 334], [9, 158, 228, 91]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 137, 290], []]
 b := ![[], [], [154, 134, 99, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI337N0 : CertifiedPrimeIdeal' SI337N0 337 where
  n := 4
  hpos := by decide
  P := [210, 303, 53, 205, 1]
  hirr := P337P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11270148282, 3970299832, 2925358788, 4013985398, 5391360026]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3150179516, -900110450, -2503021262, -1507908656, 5391360026]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI337N0 : Ideal.IsPrime I337N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI337N0 B_one_repr
lemma NI337N0 : Nat.card (O ⧸ I337N0) = 12897917761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI337N0

def I337N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-389, 136, 17, -53, 132]] i)))

def SI337N1: IdealEqSpanCertificate' Table ![![-389, 136, 17, -53, 132]] 
 ![![337, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![305, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![-389, 136, 17, -53, 132], ![950, -327, -40, 130, -318], ![-2284, 802, 103, -308, 780], ![1430, -480, -54, 201, -462], ![326, -108, -12, 46, -103]]]
  hmulB := by decide  
  f := ![![![-3747, 1218, 783, -1003, 1866]], ![![-1118, 365, 234, -300, 558]], ![![-3515, 1140, 734, -939, 1746]], ![![-8, 4, 2, -3, 6]], ![![-1805, 586, 377, -483, 899]]]
  g := ![![![-120, 136, 17, -53, 132], ![288, -327, -40, 130, -318], ![-711, 802, 103, -308, 780], ![416, -480, -54, 201, -462], ![93, -108, -12, 46, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI337N1 : Nat.card (O ⧸ I337N1) = 337 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI337N1)

lemma isPrimeI337N1 : Ideal.IsPrime I337N1 := prime_ideal_of_norm_prime hp337.out _ NI337N1
def MulI337N0 : IdealMulLeCertificate' Table 
  ![![-3747, 1218, 783, -1003, 1866]] ![![-389, 136, 17, -53, 132]]
  ![![337, 0, 0, 0, 0]] where
 M := ![![![337, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC337 : ContainsPrimesAboveP 337 ![I337N0, I337N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI337N0
    exact isPrimeI337N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 337 (by decide) (𝕀 ⊙ MulI337N0)
instance hp347 : Fact (Nat.Prime 347) := {out := by norm_num}

def I347N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3557, -1089, -703, 888, -1650]] i)))

def SI347N0: IdealEqSpanCertificate' Table ![![3557, -1089, -703, 888, -1650]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![0, 0, 347, 0, 0], ![6, 297, 48, 1, 0], ![318, 334, 270, 0, 1]] where
  M :=![![![3557, -1089, -703, 888, -1650], ![-11424, 3498, 2278, -2871, 5328], ![36882, -11245, -7393, 9291, -17226], ![-31256, 9531, 6302, -7898, 14616], ![4342, -1326, -910, 1124, -2059]]]
  hmulB := by decide  
  f := ![![![73, 31, 15, 18, 24]], ![![228, 100, 70, 87, 108]], ![![1038, 353, 291, 405, 522]], ![![346, 137, 102, 133, 168]], ![![1096, 400, 308, 416, 533]]]
  g := ![![![1507, 825, 1159, 888, -1650], ![-4866, -2661, -3742, -2871, 5328], ![15732, 8596, 12097, 9291, -17226], ![-13348, -7281, -10262, -7898, 14616], ![1880, 1016, 1444, 1124, -2059]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P0 : CertificateIrreducibleZModOfList' 347 3 2 8 [278, 49, 344, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 222, 150], [285, 124, 197], [0, 1]]
 g := ![![[11, 150, 35], [291, 336, 56], [191, 222], [259, 294, 75], [294, 144, 10], [325, 340], [307, 3, 1], []], ![[19, 289, 166, 309], [205, 57, 267, 288], [230, 95], [231, 63, 283, 170], [239, 259, 323, 248], [293, 16], [72, 309, 218, 238], [158, 292]], ![[140, 304, 126, 330], [190, 84, 235, 46], [312, 85], [307, 292, 158, 236], [108, 14, 96, 342], [335, 205], [67, 281, 164, 235], [111, 292]]]
 h' := ![![[65, 222, 150], [300, 57, 320], [80, 290, 309], [174, 230, 48], [160, 302, 219], [126, 192, 125], [16, 85, 149], [0, 0, 1], [0, 1]], ![[285, 124, 197], [178, 197, 344], [345, 170, 271], [28, 143, 200], [15, 59, 280], [186, 38, 231], [147, 273, 343], [206, 320, 124], [65, 222, 150]], ![[0, 1], [220, 93, 30], [250, 234, 114], [208, 321, 99], [111, 333, 195], [274, 117, 338], [65, 336, 202], [52, 27, 222], [285, 124, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 81], []]
 b := ![[], [250, 260, 284], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N0 : CertifiedPrimeIdeal' SI347N0 347 where
  n := 3
  hpos := by decide
  P := [278, 49, 344, 1]
  hirr := P347P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3378138, -669203, -423890, -1121231, -741934]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![689580, 1671880, 731174, -1121231, -741934]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N0 : Ideal.IsPrime I347N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N0 B_one_repr
lemma NI347N0 : Nat.card (O ⧸ I347N0) = 41781923 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N0

def I347N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 31, 15, 18, 24]] i)))

def SI347N1: IdealEqSpanCertificate' Table ![![73, 31, 15, 18, 24]] 
 ![![347, 0, 0, 0, 0], ![0, 347, 0, 0, 0], ![339, 202, 1, 0, 0], ![189, 343, 0, 1, 0], ![141, 66, 0, 0, 1]] where
  M :=![![![73, 31, 15, 18, 24], ![228, 100, 70, 87, 108], ![1038, 353, 291, 405, 522], ![2084, 709, 546, 764, 1020], ![686, 232, 156, 220, 307]]]
  hmulB := by decide  
  f := ![![![3557, -1089, -703, 888, -1650]], ![![-11424, 3498, 2278, -2871, 5328]], ![![-3069, 940, 618, -777, 1440]], ![![-9445, 2892, 1887, -2377, 4410]], ![![-715, 219, 145, -182, 337]]]
  g := ![![![-34, -31, 15, 18, 24], ![-159, -147, 70, 87, 108], ![-714, -668, 291, 405, 522], ![-1358, -1265, 546, 764, 1020], ![-395, -366, 156, 220, 307]]]
  hle1 := by decide   
  hle2 := by decide  


def P347P1 : CertificateIrreducibleZModOfList' 347 2 2 8 [93, 192, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 346], [0, 1]]
 g := ![![[114, 250], [115, 100], [282], [41, 56], [228, 143], [332], [189, 82], [1]], ![[0, 97], [0, 247], [282], [46, 291], [185, 204], [332], [60, 265], [1]]]
 h' := ![![[155, 346], [62, 69], [162, 337], [4, 87], [310, 309], [180, 181], [120, 129], [254, 155], [0, 1]], ![[0, 1], [0, 278], [0, 10], [303, 260], [319, 38], [128, 166], [336, 218], [336, 192], [155, 346]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [213]]
 b := ![[], [161, 280]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI347N1 : CertifiedPrimeIdeal' SI347N1 347 where
  n := 2
  hpos := by decide
  P := [93, 192, 1]
  hirr := P347P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30441, 22997, 20866, 11676, 39753]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42810, -31183, 20866, 11676, 39753]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI347N1 : Ideal.IsPrime I347N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI347N1 B_one_repr
lemma NI347N1 : Nat.card (O ⧸ I347N1) = 120409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI347N1
def MulI347N0 : IdealMulLeCertificate' Table 
  ![![3557, -1089, -703, 888, -1650]] ![![73, 31, 15, 18, 24]]
  ![![347, 0, 0, 0, 0]] where
 M := ![![![347, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC347 : ContainsPrimesAboveP 347 ![I347N0, I347N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI347N0
    exact isPrimeI347N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 347 (by decide) (𝕀 ⊙ MulI347N0)
instance hp349 : Fact (Nat.Prime 349) := {out := by norm_num}

def I349N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![595, 197, 139, 194, 248]] i)))

def SI349N0: IdealEqSpanCertificate' Table ![![595, 197, 139, 194, 248]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![0, 0, 349, 0, 0], ![195, 195, 198, 1, 0], ![265, 148, 258, 0, 1]] where
  M :=![![![595, 197, 139, 194, 248], ![2372, 898, 640, 859, 1164], ![11030, 3755, 2835, 3943, 5154], ![20840, 7315, 5408, 7468, 9992], ![6230, 2170, 1580, 2190, 2949]]]
  hmulB := by decide  
  f := ![![![-3903, 1187, 799, -996, 1838]], ![![12712, -3860, -2600, 3239, -5976]], ![![-41330, 12575, 8457, -10537, 19434]], ![![-18425, 5610, 3771, -4699, 8666]], ![![-28141, 8565, 5759, -7176, 13235]]]
  g := ![![![-295, -213, -293, 194, 248], ![-1357, -971, -1346, 859, 1164], ![-6085, -4378, -6039, 3943, 5154], ![-11700, -8389, -11608, 7468, 9992], ![-3445, -2468, -3418, 2190, 2949]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P0 : CertificateIrreducibleZModOfList' 349 3 2 8 [340, 13, 321, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 182, 8], [16, 166, 341], [0, 1]]
 g := ![![[234, 331, 226], [281, 25], [209, 82, 104], [119, 182, 77], [49, 184, 280], [97, 344], [73, 28, 1], []], ![[131, 244, 32, 179], [57, 192], [188, 124, 196, 63], [174, 315], [128, 66, 17, 113], [46, 77], [55, 201, 333, 229], [167, 64]], ![[147, 323, 259, 39], [233, 279], [137, 188, 5, 325], [213, 25, 312, 82], [24, 34, 83, 117], [89, 308], [120, 219, 216, 248], [183, 64]]]
 h' := ![![[12, 182, 8], [85, 252, 227], [136, 342, 5], [24, 179, 306], [92, 78, 135], [111, 8, 45], [308, 1, 293], [0, 0, 1], [0, 1]], ![[16, 166, 341], [58, 20, 261], [260, 27, 76], [104, 240, 227], [13, 114], [334, 252, 205], [224, 199, 135], [251, 330, 166], [12, 182, 8]], ![[0, 1], [197, 77, 210], [116, 329, 268], [282, 279, 165], [334, 157, 214], [20, 89, 99], [201, 149, 270], [158, 19, 182], [16, 166, 341]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [280, 210], []]
 b := ![[], [181, 236, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N0 : CertifiedPrimeIdeal' SI349N0 349 where
  n := 3
  hpos := by decide
  P := [340, 13, 321, 1]
  hirr := P349P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![86873056, 66269948, 49712943, 35757413, 95559355]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-92289546, -60312923, -90786729, 35757413, 95559355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N0 : Ideal.IsPrime I349N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N0 B_one_repr
lemma NI349N0 : Nat.card (O ⧸ I349N0) = 42508549 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N0

def I349N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3903, 1187, 799, -996, 1838]] i)))

def SI349N1: IdealEqSpanCertificate' Table ![![-3903, 1187, 799, -996, 1838]] 
 ![![349, 0, 0, 0, 0], ![0, 349, 0, 0, 0], ![236, 103, 1, 0, 0], ![3, 299, 0, 1, 0], ![278, 176, 0, 0, 1]] where
  M :=![![![-3903, 1187, 799, -996, 1838], ![12712, -3860, -2600, 3239, -5976], ![-41330, 12575, 8457, -10537, 19434], ![35260, -10725, -7212, 8990, -16588], ![-5150, 1560, 1050, -1310, 2421]]]
  hmulB := by decide  
  f := ![![![595, 197, 139, 194, 248]], ![![2372, 898, 640, 859, 1164]], ![![1134, 409, 291, 396, 526]], ![![2097, 792, 565, 759, 1028]], ![![1688, 616, 438, 594, 793]]]
  g := ![![![-2007, -306, 799, -996, 1838], ![6527, 995, -2600, 3239, -5976], ![-21227, -3233, 8457, -10537, 19434], ![18114, 2761, -7212, 8990, -16588], ![-2642, -404, 1050, -1310, 2421]]]
  hle1 := by decide   
  hle2 := by decide  


def P349P1 : CertificateIrreducibleZModOfList' 349 2 2 8 [95, 348, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 348], [0, 1]]
 g := ![![[180, 169], [12], [32, 280], [147, 271], [236, 169], [256], [160, 1], [1]], ![[0, 180], [12], [312, 69], [69, 78], [56, 180], [256], [161, 348], [1]]]
 h' := ![![[1, 348], [336, 13], [101, 330], [344, 304], [265, 142], [16, 13], [156, 16], [254, 1], [0, 1]], ![[0, 1], [0, 336], [82, 19], [299, 45], [58, 207], [29, 336], [172, 333], [255, 348], [1, 348]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163]]
 b := ![[], [221, 256]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI349N1 : CertifiedPrimeIdeal' SI349N1 349 where
  n := 2
  hpos := by decide
  P := [95, 348, 1]
  hirr := P349P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14406, 10549, 11207, 4740, 22173]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25240, -18520, 11207, 4740, 22173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI349N1 : Ideal.IsPrime I349N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI349N1 B_one_repr
lemma NI349N1 : Nat.card (O ⧸ I349N1) = 121801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI349N1
def MulI349N0 : IdealMulLeCertificate' Table 
  ![![595, 197, 139, 194, 248]] ![![-3903, 1187, 799, -996, 1838]]
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

def I353N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5581, -1940, -242, 760, -1884]] i)))

def SI353N0: IdealEqSpanCertificate' Table ![![5581, -1940, -242, 760, -1884]] 
 ![![353, 0, 0, 0, 0], ![0, 353, 0, 0, 0], ![171, 183, 1, 0, 0], ![216, 133, 0, 1, 0], ![89, 102, 0, 0, 1]] where
  M :=![![![5581, -1940, -242, 760, -1884], ![-13552, 4699, 582, -1850, 4560], ![32780, -11424, -1433, 4456, -11100], ![-20220, 6948, 842, -2779, 6732], ![-4572, 1566, 188, -630, 1517]]]
  hmulB := by decide  
  f := ![![![621, -60, -98, 88, -156]], ![![-1072, 651, 302, -362, 528]], ![![-245, 305, 107, -142, 192]], ![![-36, 211, 56, -85, 108]], ![![-151, 172, 62, -82, 113]]]
  g := ![![![143, 378, -242, 760, -1884], ![-338, -909, 582, -1850, 4560], ![859, 2239, -1433, 4456, -11100], ![-462, -1315, 842, -2779, 6732], ![-101, -294, 188, -630, 1517]]]
  hle1 := by decide   
  hle2 := by decide  


def P353P0 : CertificateIrreducibleZModOfList' 353 2 2 8 [196, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [203, 352], [0, 1]]
 g := ![![[62, 344], [84], [303], [65], [97], [348, 324], [235, 261], [1]], ![[0, 9], [84], [303], [65], [97], [109, 29], [268, 92], [1]]]
 h' := ![![[203, 352], [191, 126], [8, 310], [54, 123], [290, 199], [274, 34], [183, 18], [157, 203], [0, 1]], ![[0, 1], [0, 227], [104, 43], [313, 230], [92, 154], [116, 319], [307, 335], [65, 150], [203, 352]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [167, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI353N0 : CertifiedPrimeIdeal' SI353N0 353 where
  n := 2
  hpos := by decide
  P := [196, 150, 1]
  hirr := P353P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43450, 52443, 42333, -23678, 74489]
  a := ![10, 24, 24, -50, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24922, -34400, 42333, -23678, 74489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI353N0 : Ideal.IsPrime I353N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI353N0 B_one_repr
lemma NI353N0 : Nat.card (O ⧸ I353N0) = 124609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI353N0

def I353N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1695, -524, -349, 431, -786]] i)))

def SI353N1: IdealEqSpanCertificate' Table ![![1695, -524, -349, 431, -786]] 
 ![![353, 0, 0, 0, 0], ![70, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![234, 0, 0, 1, 0], ![258, 0, 0, 0, 1]] where
  M :=![![![1695, -524, -349, 431, -786], ![-5426, 1689, 1118, -1402, 2586], ![17884, -5360, -3635, 4538, -8412], ![-15254, 4658, 3124, -3881, 7134], ![2158, -724, -458, 572, -1033]]]
  hmulB := by decide  
  f := ![![![10817, -9102, -2775, -211, -9876]], ![![1920, -1795, -570, -94, -1962]], ![![1154, -1344, -457, -140, -1488]], ![![6140, -6262, -2048, -465, -6882]], ![![7616, -6724, -2090, -248, -7321]]]
  g := ![![![439, -524, -349, 431, -786], ![-1444, 1689, 1118, -1402, 2586], ![4686, -5360, -3635, 4538, -8412], ![-3980, 4658, 3124, -3881, 7134], ![580, -724, -458, 572, -1033]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N1 : Nat.card (O ⧸ I353N1) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N1)

lemma isPrimeI353N1 : Ideal.IsPrime I353N1 := prime_ideal_of_norm_prime hp353.out _ NI353N1

def I353N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -58, -15, 7, 26]] i)))

def SI353N2: IdealEqSpanCertificate' Table ![![-1, -58, -15, 7, 26]] 
 ![![353, 0, 0, 0, 0], ![105, 1, 0, 0, 0], ![271, 0, 1, 0, 0], ![289, 0, 0, 1, 0], ![272, 0, 0, 0, 1]] where
  M :=![![![-1, -58, -15, 7, 26], ![222, 47, -22, -12, 42], ![312, 274, 33, -36, -72], ![-38, 164, 48, -19, -82], ![-302, -184, -6, 28, 15]]]
  hmulB := by decide  
  f := ![![![-11903, 3672, 2479, -3031, 5680]], ![![-3429, 1059, 715, -873, 1638]], ![![-9493, 2930, 1978, -2417, 4532]], ![![-9429, 2916, 1969, -2400, 4510]], ![![-9214, 2844, 1920, -2346, 4399]]]
  g := ![![![3, -58, -15, 7, 26], ![-19, 47, -22, -12, 42], ![-21, 274, 33, -36, -72], ![-7, 164, 48, -19, -82], ![24, -184, -6, 28, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N2 : Nat.card (O ⧸ I353N2) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N2)

lemma isPrimeI353N2 : Ideal.IsPrime I353N2 := prime_ideal_of_norm_prime hp353.out _ NI353N2

def I353N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -75, -23, 8, 42]] i)))

def SI353N3: IdealEqSpanCertificate' Table ![![17, -75, -23, 8, 42]] 
 ![![353, 0, 0, 0, 0], ![348, 1, 0, 0, 0], ![328, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![293, 0, 0, 0, 1]] where
  M :=![![![17, -75, -23, 8, 42], ![352, 90, -28, -19, 48], ![346, 409, 61, -55, -114], ![-108, 205, 72, -20, -132], ![-402, -284, -18, 42, 37]]]
  hmulB := by decide  
  f := ![![![1863, 475, 433, 590, 708]], ![![1856, 476, 432, 589, 708]], ![![1826, 473, 427, 581, 702]], ![![526, 151, 126, 174, 216]], ![![1597, 413, 373, 508, 613]]]
  g := ![![![59, -75, -23, 8, 42], ![-98, 90, -28, -19, 48], ![-354, 409, 61, -55, -114], ![-156, 205, 72, -20, -132], ![257, -284, -18, 42, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI353N3 : Nat.card (O ⧸ I353N3) = 353 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI353N3)

lemma isPrimeI353N3 : Ideal.IsPrime I353N3 := prime_ideal_of_norm_prime hp353.out _ NI353N3
def MulI353N0 : IdealMulLeCertificate' Table 
  ![![5581, -1940, -242, 760, -1884]] ![![1695, -524, -349, 431, -786]]
  ![![-405, 112, 93, -113, 210]] where
 M := ![![![-405, 112, 93, -113, 210]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N1 : IdealMulLeCertificate' Table 
  ![![-405, 112, 93, -113, 210]] ![![-1, -58, -15, 7, 26]]
  ![![-4841, -2936, -4, 500, -106]] where
 M := ![![![-4841, -2936, -4, 500, -106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI353N2 : IdealMulLeCertificate' Table 
  ![![-4841, -2936, -4, 500, -106]] ![![17, -75, -23, 8, 42]]
  ![![353, 0, 0, 0, 0]] where
 M := ![![![-1128541, 229803, 231215, 2824, -413716]]]
 hmul := by decide  
 g := ![![![![-3197, 651, 655, 8, -1172]]]]
 hle2 := by decide  


def PBC353 : ContainsPrimesAboveP 353 ![I353N0, I353N1, I353N2, I353N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI353N0
    exact isPrimeI353N1
    exact isPrimeI353N2
    exact isPrimeI353N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 353 (by decide) (𝕀 ⊙ MulI353N0 ⊙ MulI353N1 ⊙ MulI353N2)
instance hp359 : Fact (Nat.Prime 359) := {out := by norm_num}

def I359N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251389, -76497, -51411, 64052, -118246]] i)))

def SI359N0: IdealEqSpanCertificate' Table ![![251389, -76497, -51411, 64052, -118246]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![0, 0, 359, 0, 0], ![181, 38, 75, 1, 0], ![243, 202, 161, 0, 1]] where
  M :=![![![251389, -76497, -51411, 64052, -118246], ![-817864, 248606, 167070, -208427, 384312], ![2657642, -809049, -543745, 677095, -1250562], ![-2270176, 689159, 463102, -578678, 1065440], ![329750, -100690, -67682, 83964, -155607]]]
  hmulB := by decide  
  f := ![![![597, 563, 7, -114, 100]], ![![572, 576, 214, 7, -684]], ![![-5458, -319, 383, -35, 42]], ![![-783, 273, 106, -63, -14]], ![![-1715, 562, 296, -89, -297]]]
  g := ![![![48445, 59541, 39505, 64052, -118246], ![-157327, -193488, -128343, -208427, 384312], ![512507, 629735, 417868, 677095, -1250562], ![-435742, -536323, -355632, -578678, 1065440], ![63913, 78388, 52055, 83964, -155607]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P0 : CertificateIrreducibleZModOfList' 359 3 2 8 [142, 47, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 53, 150], [321, 305, 209], [0, 1]]
 g := ![![[48, 235, 111], [184, 351, 147], [193, 57, 301], [271, 289], [61, 51], [206, 248, 88], [324, 326, 1], []], ![[131, 340, 292, 79], [93, 206, 181, 96], [300, 90, 328, 288], [61, 301], [149, 15], [186, 11, 306, 146], [123, 340, 37, 138], [16, 242]], ![[95, 173, 322, 249], [196, 314, 295, 35], [82, 32, 202, 343], [71, 270], [82, 191], [94, 39, 309, 39], [63, 221, 169, 116], [316, 242]]]
 h' := ![![[5, 53, 150], [79, 192, 199], [237, 136, 64], [147, 340, 115], [86, 204, 17], [186, 241, 236], [303, 228, 51], [0, 0, 1], [0, 1]], ![[321, 305, 209], [123, 258, 104], [350, 118, 71], [127, 41, 274], [243, 122, 244], [265, 136, 71], [290, 118, 213], [266, 237, 305], [5, 53, 150]], ![[0, 1], [357, 268, 56], [81, 105, 224], [339, 337, 329], [60, 33, 98], [86, 341, 52], [98, 13, 95], [11, 122, 53], [321, 305, 209]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 65], []]
 b := ![[], [7, 197, 203], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N0 : CertifiedPrimeIdeal' SI359N0 359 where
  n := 3
  hpos := by decide
  P := [142, 47, 33, 1]
  hirr := P359P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3594471, 617040, 466473, -1072430, 1023390]
  a := ![3, 8, 8, -15, 8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-162029, -460600, -233613, -1072430, 1023390]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N0 : Ideal.IsPrime I359N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N0 B_one_repr
lemma NI359N0 : Nat.card (O ⧸ I359N0) = 46268279 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N0

def I359N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![597, 563, 7, -114, 100]] i)))

def SI359N1: IdealEqSpanCertificate' Table ![![597, 563, 7, -114, 100]] 
 ![![359, 0, 0, 0, 0], ![0, 359, 0, 0, 0], ![327, 133, 1, 0, 0], ![331, 240, 0, 1, 0], ![224, 313, 0, 0, 1]] where
  M :=![![![597, 563, 7, -114, 100], ![572, 576, 214, 7, -684], ![-5458, -319, 383, -35, 42], ![-1540, -1859, -70, 376, -284], ![2438, -44, -328, -28, 483]]]
  hmulB := by decide  
  f := ![![![251389, -76497, -51411, 64052, -118246]], ![![-817864, 248606, 167070, -208427, 384312]], ![![-66613, 20170, 13552, -16988, 31188]], ![![-321303, 97588, 65579, -81894, 150866]], ![![-555294, 168740, 113396, -141521, 260855]]]
  g := ![![![38, -12, 7, -114, 100], ![227, 514, 214, 7, -684], ![-358, -156, 383, -35, 42], ![-110, 17, -70, 376, -284], ![30, -281, -328, -28, 483]]]
  hle1 := by decide   
  hle2 := by decide  


def P359P1 : CertificateIrreducibleZModOfList' 359 2 2 8 [236, 339, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 358], [0, 1]]
 g := ![![[6, 185], [356, 23], [308, 22], [37], [328], [328, 144], [355, 41], [1]], ![[116, 174], [98, 336], [30, 337], [37], [328], [336, 215], [98, 318], [1]]]
 h' := ![![[20, 358], [349, 77], [189, 89], [103, 205], [323, 162], [136, 317], [226, 347], [123, 20], [0, 1]], ![[0, 1], [94, 282], [174, 270], [254, 154], [332, 197], [14, 42], [345, 12], [164, 339], [20, 358]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [29, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI359N1 : CertifiedPrimeIdeal' SI359N1 359 where
  n := 2
  hpos := by decide
  P := [236, 339, 1]
  hirr := P359P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![90916, 33838, 29607, 37021, 58164]
  a := ![16, 5, 17, 17, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-97140, -86335, 29607, 37021, 58164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI359N1 : Ideal.IsPrime I359N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI359N1 B_one_repr
lemma NI359N1 : Nat.card (O ⧸ I359N1) = 128881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI359N1
def MulI359N0 : IdealMulLeCertificate' Table 
  ![![251389, -76497, -51411, 64052, -118246]] ![![597, 563, 7, -114, 100]]
  ![![359, 0, 0, 0, 0]] where
 M := ![![![359, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC359 : ContainsPrimesAboveP 359 ![I359N0, I359N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI359N0
    exact isPrimeI359N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 359 (by decide) (𝕀 ⊙ MulI359N0)


lemma PB696I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317, 331, 337, 347, 349, 353, 359] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 359 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 359 (by omega)

def PB696I7 : PrimesBelowBoundCertificateInterval O 307 359 696 where
  m := 9
  g := ![2, 2, 3, 3, 2, 2, 2, 4, 2]
  P := ![311, 313, 317, 331, 337, 347, 349, 353, 359]
  hP := PB696I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1]
    · exact ![I313N0, I313N1]
    · exact ![I317N0, I317N1, I317N2]
    · exact ![I331N0, I331N1, I331N2]
    · exact ![I337N0, I337N1]
    · exact ![I347N0, I347N1]
    · exact ![I349N0, I349N1]
    · exact ![I353N0, I353N1, I353N2, I353N3]
    · exact ![I359N0, I359N1]
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
    · exact ![9597924961, 313]
    · exact ![31855013, 317, 317]
    · exact ![109561, 109561, 331]
    · exact ![12897917761, 337]
    · exact ![41781923, 120409]
    · exact ![42508549, 121801]
    · exact ![124609, 353, 353, 353]
    · exact ![46268279, 128881]
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
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
      exact NI317N2
    · dsimp ; intro j
      fin_cases j
      exact NI331N0
      exact NI331N1
      exact NI331N2
    · dsimp ; intro j
      fin_cases j
      exact NI337N0
      exact NI337N1
    · dsimp ; intro j
      fin_cases j
      exact NI347N0
      exact NI347N1
    · dsimp ; intro j
      fin_cases j
      exact NI349N0
      exact NI349N1
    · dsimp ; intro j
      fin_cases j
      exact NI353N0
      exact NI353N1
      exact NI353N2
      exact NI353N3
    · dsimp ; intro j
      fin_cases j
      exact NI359N0
      exact NI359N1
  β := ![I313N1, I317N1, I317N2, I331N2, I337N1, I353N1, I353N2, I353N3]
  Il := ![[], [I313N1], [I317N1, I317N2], [I331N2], [I337N1], [], [], [I353N1, I353N2, I353N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
