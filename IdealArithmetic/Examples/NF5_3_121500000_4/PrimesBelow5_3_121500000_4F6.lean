
import IdealArithmetic.Examples.NF5_3_121500000_4.RI5_3_121500000_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29300, 11292, -7318, -2825, 6369]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![29300, 11292, -7318, -2825, 6369]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![156, 37, 250, 156, 1]] where
  M :=![![![29300, 11292, -7318, -2825, 6369], ![-67953, -26145, 16942, 6577, -14793], ![157785, 60756, -39299, -15433, 34545], ![-150144, -58148, 37340, 15107, -33384], ![20031, 7830, -4996, -2071, 4532]]]
  hmulB := by decide  
  f := ![![![70, 66, 16, -3, -27]], ![![333, 305, 72, -13, -117]], ![![1443, 1354, 331, -51, -507]], ![![2952, 2788, 692, -93, -1008]], ![![3294, 3101, 764, -110, -1141]]]
  g := ![![![-3752, -873, -6224, -3877, 6369], ![8715, 2028, 14456, 9005, -14793], ![-20355, -4737, -33757, -21029, 34545], ![19680, 4580, 32620, 20323, -33384], ![-2673, -622, -4428, -2759, 4532]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 4 2 8 [231, 209, 11, 185, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [177, 246, 67, 154], [19, 5, 201, 147], [133, 5, 246, 213], [0, 1]]
 g := ![![[76, 121, 95, 104], [86, 202, 226], [22, 151, 42], [250, 46, 211], [145, 173, 88], [64, 42, 44], [1], []], ![[212, 95, 110, 179, 190, 151], [133, 33, 89], [177, 86, 128], [68, 194, 118], [177, 96, 193], [42, 55, 184], [109, 196, 248], [211, 120, 72]], ![[221, 49, 87, 43, 81, 103], [58, 88, 189], [31, 118, 168], [179, 97, 244], [0, 102, 26], [252, 81, 168], [24, 112, 113], [35, 211, 21]], ![[143, 237, 254, 215, 63, 84], [150, 40, 162], [61, 32, 92], [125, 126, 169], [234, 156, 58], [50], [196, 126, 32], [139, 38, 137]]]
 h' := ![![[177, 246, 67, 154], [52, 65, 39, 238], [227, 91, 107, 45], [13, 59, 53, 82], [130, 247, 221, 89], [27, 235, 76, 208], [26, 48, 246, 72], [0, 0, 1], [0, 1]], ![[19, 5, 201, 147], [238, 162, 171, 253], [11, 52, 148, 54], [158, 15, 36, 223], [184, 48, 60, 115], [145, 159, 179, 128], [248, 254, 206, 21], [64, 102, 109, 209], [177, 246, 67, 154]], ![[133, 5, 246, 213], [156, 20, 110, 174], [31, 18, 75, 184], [225, 95, 223, 93], [222, 95, 185, 66], [215, 162, 245, 138], [49, 98, 19, 164], [243, 160, 219, 65], [19, 5, 201, 147]], ![[0, 1], [109, 10, 194, 106], [8, 96, 184, 231], [96, 88, 202, 116], [50, 124, 48, 244], [205, 215, 14, 40], [226, 114, 43], [229, 252, 185, 240], [133, 5, 246, 213]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [131, 22, 253], []]
 b := ![[], [], [17, 114, 68, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 4
  hpos := by decide
  P := [231, 209, 11, 185, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-168536864099, -197596778584, -82435172576, -15813183380, 110601270920]
  a := ![17, 4, 8, 14, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-67791187267, -16691999232, -107909544368, -67196931700, 110601270920]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 4362470401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, -66, -16, 3, 27]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-70, -66, -16, 3, 27]] 
 ![![257, 0, 0, 0, 0], ![181, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![28, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-70, -66, -16, 3, 27], ![-333, -305, -72, 13, 117], ![-1443, -1354, -331, 51, 507], ![-2952, -2788, -692, 93, 1008], ![-2055, -1948, -486, 63, 698]]]
  hmulB := by decide  
  f := ![![![-29300, -11292, 7318, 2825, -6369]], ![![-20371, -7851, 5088, 1964, -4428]], ![![-16005, -6168, 3997, 1544, -3480]], ![![-2608, -1004, 652, 249, -564]], ![![-15583, -6006, 3892, 1503, -3388]]]
  g := ![![![40, -66, -16, 3, 27], ![188, -305, -72, 13, 117], ![848, -1354, -331, 51, 507], ![1772, -2788, -692, 93, 1008], ![1243, -1948, -486, 63, 698]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![29300, 11292, -7318, -2825, 6369]] ![![-70, -66, -16, 3, 27]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![-257, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1718, 331, -313, -99, 249]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![1718, 331, -313, -99, 249]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![253, 183, 229, 101, 1]] where
  M :=![![![1718, 331, -313, -99, 249], ![-2691, -488, 529, 169, -441], ![4785, 1197, -826, -331, 705], ![-2388, -431, 665, 291, -708], ![1041, 438, -90, -73, 80]]]
  hmulB := by decide  
  f := ![![![10, 3, -3, -1, 3]], ![![-33, -16, 5, 3, -3]], ![![27, -7, -22, -5, 27]], ![![-138, -95, -1, 11, 12]], ![![-43, -51, -19, 1, 29]]]
  g := ![![![-233, -172, -218, -96, 249], ![414, 305, 386, 170, -441], ![-660, -486, -617, -272, 705], ![672, 491, 619, 273, -708], ![-73, -54, -70, -31, 80]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 4 2 8 [247, 157, 211, 107, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 181, 252, 90], [115, 24, 77, 193], [242, 57, 197, 243], [0, 1]]
 g := ![![[234, 50, 80, 111], [5, 135, 258, 11], [56, 188, 104, 100], [81, 124, 138], [191, 244, 92], [157, 192, 140], [1], []], ![[95, 262, 66, 41, 2, 131], [86, 35, 3, 24, 1, 120], [66, 225, 80, 11, 99, 142], [157, 108, 103], [222, 70, 95], [102, 13, 203], [130, 154, 13], [52, 9, 210]], ![[52, 111, 251, 117, 166, 155], [11, 82, 56, 204, 217, 56], [65, 249, 28, 163, 261, 107], [189, 207, 6], [57, 199, 50], [113, 170, 66], [14, 193, 26], [193, 125, 166]], ![[252, 112, 123, 230, 89, 92], [236, 127, 36, 70, 71, 68], [242, 227, 158, 26, 99, 26], [110, 119, 61], [156, 232, 78], [140, 184, 234], [47, 139, 72], [221, 79, 137]]]
 h' := ![![[62, 181, 252, 90], [80, 200, 116, 30], [107, 186, 165, 96], [45, 89, 172, 10], [8, 249, 25, 140], [138, 225, 261, 108], [16, 106, 52, 156], [0, 0, 1], [0, 1]], ![[115, 24, 77, 193], [63, 218, 173, 36], [65, 197, 96, 160], [178, 51, 150, 98], [159, 16, 171, 41], [246, 245, 197, 44], [184, 223, 120, 27], [205, 222, 17, 146], [62, 181, 252, 90]], ![[242, 57, 197, 243], [32, 259, 130, 105], [215, 189, 201, 169], [24, 192, 178, 150], [141, 41, 237, 100], [67, 8, 120, 239], [10, 186, 132, 131], [7, 100, 44, 246], [115, 24, 77, 193]], ![[0, 1], [79, 112, 107, 92], [199, 217, 64, 101], [248, 194, 26, 5], [131, 220, 93, 245], [153, 48, 211, 135], [198, 11, 222, 212], [32, 204, 201, 134], [242, 57, 197, 243]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [82, 258, 153], []]
 b := ![[], [], [32, 224, 63, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 4
  hpos := by decide
  P := [247, 157, 211, 107, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1315288474795995, -1285727685112369, -346492643695605, 22033429955120, 458628480254818]
  a := ![113, -4, 57, 50, -449]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-446191231860323, -324010416622601, -400655568905129, -176043509793846, 458628480254818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 4784350561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -3, 3, 1, -3]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-10, -3, 3, 1, -3]] 
 ![![263, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![257, 0, 1, 0, 0], ![250, 0, 0, 1, 0], ![156, 0, 0, 0, 1]] where
  M :=![![![-10, -3, 3, 1, -3], ![33, 16, -5, -3, 3], ![-27, 7, 22, 5, -27], ![138, 95, 1, -11, -12], ![45, 46, 14, -1, -22]]]
  hmulB := by decide  
  f := ![![![-1718, -331, 313, 99, -249]], ![![-643, -124, 117, 37, -93]], ![![-1697, -328, 309, 98, -246]], ![![-1624, -313, 295, 93, -234]], ![![-1023, -198, 186, 59, -148]]]
  g := ![![![-1, -3, 3, 1, -3], ![0, 16, -5, -3, 3], ![-13, 7, 22, 5, -27], ![-19, 95, 1, -11, -12], ![-17, 46, 14, -1, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![1718, 331, -313, -99, 249]] ![![-10, -3, 3, 1, -3]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 5, 7, 2, -10]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![11, 5, 7, 2, -10]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![53, 103, 41, 1, 0], ![144, 47, 142, 0, 1]] where
  M :=![![![11, 5, 7, 2, -10], ![114, 96, 1, -12, -6], ![108, 175, 120, 26, -162], ![876, 701, 61, -75, -84], ![352, 354, 108, 0, -147]]]
  hmulB := by decide  
  f := ![![![21, -3, -3, 0, 2]], ![![-24, 2, -3, -2, 6]], ![![-66, -73, 6, 12, -6]], ![![-15, -11, -1, 1, 2]], ![![-28, -40, 1, 6, -1]]]
  g := ![![![5, 1, 5, 2, -10], ![6, 6, 5, -12, -6], ![82, 19, 82, 26, -162], ![63, 46, 56, -75, -84], ![80, 27, 78, 0, -147]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [145, 250, 179, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 49, 18], [55, 219, 251], [0, 1]]
 g := ![![[176, 34, 21], [156, 185], [76, 82, 244], [159, 202, 150], [214, 265], [123, 249], [90, 1], []], ![[30, 46], [104, 172], [37, 70, 143, 75], [223, 149, 151, 94], [107, 220], [23, 56], [193, 79], [258, 55]], ![[198, 6, 263, 160], [133, 233], [80, 117, 124, 82], [80, 13, 13, 68], [63, 188], [180, 66], [67, 249], [25, 55]]]
 h' := ![![[35, 49, 18], [57, 248, 57], [9, 99, 202], [79, 138, 141], [109, 11, 227], [133, 200, 105], [131, 220, 49], [0, 0, 1], [0, 1]], ![[55, 219, 251], [7, 221], [144, 31, 21], [105, 71, 7], [145, 71, 146], [70, 210, 233], [213, 28, 165], [130, 88, 219], [35, 49, 18]], ![[0, 1], [210, 69, 212], [193, 139, 46], [3, 60, 121], [90, 187, 165], [50, 128, 200], [47, 21, 55], [207, 181, 49], [55, 219, 251]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 184], []]
 b := ![[], [50, 57, 199], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [145, 250, 179, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60899918, 60215400, 17510406, -375125, -25757355]
  a := ![10, 1, 5, 6, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14088627, 4867840, 13719089, -375125, -25757355]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2599, -995, 645, 254, -568]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-2599, -995, 645, 254, -568]] 
 ![![269, 0, 0, 0, 0], ![199, 1, 0, 0, 0], ![211, 0, 1, 0, 0], ![157, 0, 0, 1, 0], ![222, 0, 0, 0, 1]] where
  M :=![![![-2599, -995, 645, 254, -568], ![6054, 2336, -1503, -608, 1344], ![-14304, -5593, 3552, 1506, -3264], ![14298, 5759, -3551, -1667, 3468], ![-2006, -824, 498, 250, -507]]]
  hmulB := by decide  
  f := ![![![-8793, -8507, -2213, 168, 2696]], ![![-6627, -6415, -1670, 126, 2032]], ![![-7353, -7130, -1861, 136, 2248]], ![![-5877, -5730, -1508, 99, 1780]], ![![-7744, -7524, -1970, 138, 2357]]]
  g := ![![![541, -995, 645, 254, -568], ![-1281, 2336, -1503, -608, 1344], ![3113, -5593, 3552, 1506, -3264], ![-3311, 5759, -3551, -1667, 3468], ![484, -824, 498, 250, -507]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -66, -14, 6, 38]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-73, -66, -14, 6, 38]] 
 ![![269, 0, 0, 0, 0], ![257, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![218, 0, 0, 1, 0], ![180, 0, 0, 0, 1]] where
  M :=![![![-73, -66, -14, 6, 38], ![-474, -397, -78, 30, 186], ![-2322, -2070, -457, 126, 918], ![-5460, -4926, -1122, 257, 2040], ![-3914, -3556, -820, 178, 1455]]]
  hmulB := by decide  
  f := ![![![49791, 18658, -12362, -4462, 10370]], ![![47157, 17673, -11708, -4228, 9824]], ![![24033, 8992, -5967, -2140, 4988]], ![![39642, 14890, -9842, -3587, 8300]], ![![33398, 12508, -8292, -2986, 6947]]]
  g := ![![![39, -66, -14, 6, 38], ![265, -397, -78, 30, 186], ![1465, -2070, -457, 126, 918], ![3634, -4926, -1122, 257, 2040], ![2646, -3556, -820, 178, 1455]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![11, 5, 7, 2, -10]] ![![-2599, -995, 645, 254, -568]]
  ![![-49791, -18658, 12362, 4462, -10370]] where
 M := ![![![-49791, -18658, 12362, 4462, -10370]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![-49791, -18658, 12362, 4462, -10370]] ![![-73, -66, -14, 6, 38]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![758, 311, -183, -87, 177]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![758, 311, -183, -87, 177]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![117, 182, 265, 1, 0], ![146, 56, 143, 0, 1]] where
  M :=![![![758, 311, -183, -87, 177], ![-1863, -754, 485, 249, -513], ![5409, 2477, -1252, -803, 1449], ![-6558, -2939, 1799, 1277, -2388], ![1365, 782, -222, -233, 326]]]
  hmulB := by decide  
  f := ![![![-7894, -1373, 1435, 427, -1125]], ![![12219, 2114, -2227, -661, 1749]], ![![-19005, -3339, 3436, 1027, -2685]], ![![-13755, -2433, 2478, 743, -1932]], ![![-11768, -2067, 2128, 636, -1663]]]
  g := ![![![-55, 23, -9, -87, 177], ![162, -64, 29, 249, -513], ![-414, 249, 16, -803, 1449], ![711, -375, 18, 1277, -2388], ![-70, 92, 55, -233, 326]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [24, 230, 156, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [270, 112, 183], [116, 158, 88], [0, 1]]
 g := ![![[192, 79, 245], [28, 51, 252], [20, 28, 57], [19, 9, 67], [208, 18], [178, 169], [115, 1], []], ![[24, 87, 187, 253], [172, 198, 161, 150], [221, 90, 21, 203], [139, 218, 58, 194], [7, 9], [37, 166], [190, 32], [125, 156]], ![[268, 231, 14, 11], [105, 245, 127, 134], [33, 72, 265, 248], [23, 14, 194, 68], [128, 196], [30, 134], [206, 78], [220, 156]]]
 h' := ![![[270, 112, 183], [141, 245, 40], [62, 227, 184], [86, 52, 190], [64, 155, 164], [125, 262, 254], [221, 84, 258], [0, 0, 1], [0, 1]], ![[116, 158, 88], [260, 8, 207], [46, 103, 153], [137, 182, 241], [209, 64, 77], [169, 190, 3], [100, 58, 39], [253, 73, 158], [270, 112, 183]], ![[0, 1], [49, 18, 24], [170, 212, 205], [224, 37, 111], [114, 52, 30], [196, 90, 14], [153, 129, 245], [46, 198, 112], [116, 158, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [209, 21], []]
 b := ![[], [137, 96, 262], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [24, 230, 156, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15270084832, -15639030684, -5201074020, -296560392, 8214788464]
  a := ![-61, -8, -30, -43, 245]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4353991272, -1556063444, -4063938452, -296560392, 8214788464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, -107, 25, 16, -14]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![-203, -107, 25, 16, -14]] 
 ![![271, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![166, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-203, -107, 25, 16, -14], ![120, -82, -139, -26, 150], ![-1722, -1193, -30, 100, 138], ![-1038, -1437, -627, -29, 732], ![-1312, -1216, -282, 36, 369]]]
  hmulB := by decide  
  f := ![![![25281, 9207, -5431, -4034, 7250]], ![![3735, 1335, -798, -582, 1052]], ![![5484, 2147, -1204, -958, 1686]], ![![13578, 4599, -2857, -1975, 3632]], ![![376, 202, -92, -96, 157]]]
  g := ![![![2, -107, 25, 16, -14], ![54, -82, -139, -26, 150], ![127, -1193, -30, 100, 138], ![353, -1437, -627, -29, 732], ![216, -1216, -282, 36, 369]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![950, 610, -316, -139, 291]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![950, 610, -316, -139, 291]] 
 ![![271, 0, 0, 0, 0], ![240, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![950, 610, -316, -139, 291], ![-3075, -1555, 888, 367, -795], ![8439, 3806, -2289, -915, 2019], ![-9204, -3766, 2374, 919, -2064], ![921, 446, -260, -105, 230]]]
  hmulB := by decide  
  f := ![![![-14248, -13500, -3366, 437, 4833]], ![![-12837, -12165, -3034, 393, 4353]], ![![-7359, -6988, -1749, 220, 2484]], ![![-2980, -2870, -736, 74, 975]], ![![-12911, -12268, -3074, 383, 4352]]]
  g := ![![![-621, 610, -316, -139, 291], ![1586, -1555, 888, 367, -795], ![-3885, 3806, -2289, -915, 2019], ![3845, -3766, 2374, 919, -2064], ![-454, 446, -260, -105, 230]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![758, 311, -183, -87, 177]] ![![-203, -107, 25, 16, -14]]
  ![![56654, 21498, -14154, -5363, 12413]] where
 M := ![![![56654, 21498, -14154, -5363, 12413]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![56654, 21498, -14154, -5363, 12413]] ![![950, 610, -316, -139, 291]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-70937231, -27007318, 17626924, 6733808, -15257300]]]
 hmul := by decide  
 g := ![![![![-261761, -99658, 65044, 24848, -56300]]]]
 hle2 := by decide  


def PBC271 : ContainsPrimesAboveP 271 ![I271N0, I271N1, I271N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
    exact isPrimeI271N1
    exact isPrimeI271N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 271 (by decide) (𝕀 ⊙ MulI271N0 ⊙ MulI271N1)
instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1195, 916, 122, -146, -696]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![1195, 916, 122, -146, -696]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![173, 134, 163, 200, 1]] where
  M :=![![![1195, 916, 122, -146, -696], ![8790, 7031, 1208, -710, -3840], ![48210, 41428, 8451, -3134, -20040], ![120546, 106542, 23244, -6533, -46944], ![87780, 78178, 17318, -4568, -33839]]]
  hmulB := by decide  
  f := ![![![487, 200, -122, -58, 120]], ![![-1266, -537, 316, 170, -336]], ![![3522, 1568, -877, -550, 1032]], ![![-4734, -2262, 1176, 895, -1584]], ![![-1651, -844, 409, 368, -623]]]
  g := ![![![439, 340, 410, 502, -696], ![2430, 1883, 2264, 2770, -3840], ![12690, 9844, 11823, 14458, -20040], ![29754, 23094, 27708, 33871, -46944], ![21451, 16652, 19975, 24416, -33839]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [148, 261, 168, 224, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 45, 13, 188], [86, 119, 224, 71], [70, 112, 40, 18], [0, 1]]
 g := ![![[40, 254, 68, 87], [131, 109, 188], [118, 216, 272, 252], [177, 127, 85], [21, 0, 253, 9], [151, 48, 39], [1], []], ![[133, 204, 196, 19, 215, 243], [179, 91, 122], [115, 194, 237, 51, 255, 19], [109, 19, 213], [206, 52, 179, 76, 126, 264], [89, 240, 256], [176, 58, 71], [28, 60, 165]], ![[260, 116, 206, 129, 157, 264], [242, 194, 117], [75, 12, 165, 113, 28, 39], [90, 201, 19], [96, 235, 160, 97, 225, 144], [23, 87, 40], [261, 190, 89], [149, 98, 55]], ![[68, 207, 268, 159, 263, 80], [85, 257, 71], [71, 48, 24, 139, 173, 145], [253, 244, 90], [219, 186, 121, 149, 236, 129], [53, 74, 164], [120, 203, 190], [268, 53, 47]]]
 h' := ![![[174, 45, 13, 188], [171, 51, 82, 126], [264, 172, 244, 36], [239, 39, 113, 23], [216, 248, 89, 75], [110, 271, 222, 274], [129, 16, 109, 53], [0, 0, 1], [0, 1]], ![[86, 119, 224, 71], [60, 100, 9, 106], [121, 264, 64, 251], [9, 234, 244, 55], [96, 102, 257, 74], [183, 98, 138, 81], [239, 228, 1, 261], [94, 26, 268, 252], [174, 45, 13, 188]], ![[70, 112, 40, 18], [222, 21, 274, 249], [100, 134, 161, 242], [106, 69, 144, 124], [31, 69, 78, 41], [66, 171, 86, 66], [223, 116, 82, 219], [25, 38, 33, 221], [86, 119, 224, 71]], ![[0, 1], [40, 105, 189, 73], [175, 261, 85, 25], [35, 212, 53, 75], [19, 135, 130, 87], [141, 14, 108, 133], [176, 194, 85, 21], [138, 213, 252, 81], [70, 112, 40, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [182, 83, 166], []]
 b := ![[], [], [25, 269, 106, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [148, 261, 168, 224, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![582130194981, -78987503150, -621476807406, -387554974575, 941863002879]
  a := ![29, 11, 15, 32, -117]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-586137795318, -455915631368, -556480672479, -681444604875, 941863002879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 200, -122, -58, 120]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![487, 200, -122, -58, 120]] 
 ![![277, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![210, 0, 1, 0, 0], ![200, 0, 0, 1, 0], ![185, 0, 0, 0, 1]] where
  M :=![![![487, 200, -122, -58, 120], ![-1266, -537, 316, 170, -336], ![3522, 1568, -877, -550, 1032], ![-4734, -2262, 1176, 895, -1584], ![780, 386, -194, -160, 277]]]
  hmulB := by decide  
  f := ![![![1195, 916, 122, -146, -696]], ![![420, 323, 44, -50, -240]], ![![1080, 844, 123, -122, -600]], ![![1298, 1046, 172, -129, -672]], ![![1115, 894, 144, -114, -587]]]
  g := ![![![-9, 200, -122, -58, 120], ![32, -537, 316, 170, -336], ![-124, 1568, -877, -550, 1032], ![238, -2262, 1176, 895, -1584], ![-45, 386, -194, -160, 277]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![1195, 916, 122, -146, -696]] ![![487, 200, -122, -58, 120]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC277 : ContainsPrimesAboveP 277 ![I277N0, I277N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI277N0
    exact isPrimeI277N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 277 (by decide) (𝕀 ⊙ MulI277N0)
instance hp281 : Fact (Nat.Prime 281) := {out := by norm_num}

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6128, -2328, 1522, 581, -1317]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-6128, -2328, 1522, 581, -1317]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![179, 105, 1, 0, 0], ![16, 57, 0, 1, 0], ![120, 26, 0, 0, 1]] where
  M :=![![![-6128, -2328, 1522, 581, -1317], ![14061, 5349, -3490, -1333, 3021], ![-32253, -12264, 8015, 3061, -6933], ![29976, 11408, -7448, -2843, 6456], ![-3987, -1518, 988, 379, -848]]]
  hmulB := by decide  
  f := ![![![878, 522, -220, -249, 399]], ![![-4041, -2285, 1020, 1105, -1791]], ![![-886, -485, 225, 237, -387]], ![![-905, -509, 228, 246, -399]], ![![27, 26, -6, -11, 16]]]
  g := ![![![-462, -573, 1522, 581, -1317], ![1059, 1314, -3490, -1333, 3021], ![-2434, -3018, 8015, 3061, -6933], ![2256, 2803, -7448, -2843, 6456], ![-303, -373, 988, 379, -848]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [259, 242, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 280], [0, 1]]
 g := ![![[270, 155], [163], [280], [86, 98], [203, 175], [273], [116], [1]], ![[133, 126], [163], [280], [255, 183], [3, 106], [273], [116], [1]]]
 h' := ![![[39, 280], [222, 118], [264, 43], [206, 228], [251, 81], [39, 52], [226, 58], [22, 39], [0, 1]], ![[0, 1], [47, 163], [255, 238], [106, 53], [38, 200], [100, 229], [240, 223], [138, 242], [39, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [244, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [259, 242, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![411067, 229476, -113604, -135272, 225168]
  a := ![-18, -16, -8, -38, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14625, 49872, -113604, -135272, 225168]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-66, -59, -13, 3, 23]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-66, -59, -13, 3, 23]] 
 ![![281, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![236, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![199, 0, 0, 0, 1]] where
  M :=![![![-66, -59, -13, 3, 23], ![-285, -266, -65, 11, 105], ![-1293, -1201, -288, 47, 447], ![-2610, -2469, -615, 83, 900], ![-1829, -1730, -430, 57, 622]]]
  hmulB := by decide  
  f := ![![![-9946, -2009, 1871, 663, -1597]], ![![-1921, -386, 361, 127, -307]], ![![-8473, -1723, 1596, 571, -1369]], ![![-3708, -723, 693, 233, -576]], ![![-7071, -1433, 1331, 474, -1139]]]
  g := ![![![5, -59, -13, 3, 23], ![28, -266, -65, 11, 105], ![142, -1201, -288, 47, 447], ![330, -2469, -615, 83, 900], ![237, -1730, -430, 57, 622]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 8, 2, 0, -2]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![9, 8, 2, 0, -2]] 
 ![![281, 0, 0, 0, 0], ![165, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![228, 0, 0, 1, 0], ![266, 0, 0, 0, 1]] where
  M :=![![![9, 8, 2, 0, -2], ![24, 27, 8, 0, -6], ![72, 80, 27, 4, -18], ![90, 106, 32, 3, 0], ![38, 54, 22, 6, -1]]]
  hmulB := by decide  
  f := ![![![5005, 1676, -1170, -428, 994]], ![![2901, 971, -678, -248, 576]], ![![652, 220, -153, -56, 130]], ![![3990, 1334, -932, -341, 792]], ![![4748, 1590, -1110, -406, 943]]]
  g := ![![![-3, 8, 2, 0, -2], ![-11, 27, 8, 0, -6], ![-36, 80, 27, 4, -18], ![-68, 106, 32, 3, 0], ![-38, 54, 22, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2

def I281N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 40, 10, -2, -18]] i)))

def SI281N3: IdealEqSpanCertificate' Table ![![41, 40, 10, -2, -18]] 
 ![![281, 0, 0, 0, 0], ![236, 1, 0, 0, 0], ![223, 0, 1, 0, 0], ![263, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![41, 40, 10, -2, -18], ![222, 197, 44, -10, -78], ![966, 900, 217, -38, -354], ![2070, 1928, 466, -75, -720], ![1446, 1356, 332, -50, -505]]]
  hmulB := by decide  
  f := ![![![70525, 26920, -17550, -6702, 15186]], ![![58654, 22389, -14596, -5574, 12630]], ![![57293, 21868, -14257, -5444, 12336]], ![![64777, 24728, -16120, -6157, 13950]], ![![2170, 828, -540, -206, 467]]]
  g := ![![![-39, 40, 10, -2, -18], ![-188, 197, 44, -10, -78], ![-879, 900, 217, -38, -354], ![-1891, 1928, 466, -75, -720], ![-1336, 1356, 332, -50, -505]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N3 : Nat.card (O ⧸ I281N3) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N3)

lemma isPrimeI281N3 : Ideal.IsPrime I281N3 := prime_ideal_of_norm_prime hp281.out _ NI281N3
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-6128, -2328, 1522, 581, -1317]] ![![-66, -59, -13, 3, 23]]
  ![![-7635, -3201, 1643, 696, -1324]] where
 M := ![![![-7635, -3201, 1643, 696, -1324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-7635, -3201, 1643, 696, -1324]] ![![9, 8, 2, 0, -2]]
  ![![-14915, -13787, -3373, 716, 6226]] where
 M := ![![![-14915, -13787, -3373, 716, 6226]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N2 : IdealMulLeCertificate' Table 
  ![![-14915, -13787, -3373, 716, 6226]] ![![41, 40, 10, -2, -18]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![3554369, 3474565, 912969, -69126, -1121752]]]
 hmul := by decide  
 g := ![![![![12649, 12365, 3249, -246, -3992]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1, I281N2, I281N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
    exact isPrimeI281N2
    exact isPrimeI281N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0 ⊙ MulI281N1 ⊙ MulI281N2)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2289, -1243, 563, 594, -968]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-2289, -1243, 563, 594, -968]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![219, 146, 264, 83, 1]] where
  M :=![![![-2289, -1243, 563, 594, -968], ![9834, 5424, -2431, -2592, 4224], ![-42912, -23797, 10608, 11362, -18432], ![88632, 49183, -22045, -23571, 38412], ![-17266, -9624, 4222, 4554, -7327]]]
  hmulB := by decide  
  f := ![![![35, 19, -9, -4, 8]], ![![-84, -34, 27, 10, -24]], ![![258, 125, -54, -24, 48]], ![![-210, -61, 73, 25, -60]], ![![163, 96, -22, -13, 21]]]
  g := ![![![741, 495, 905, 286, -968], ![-3234, -2160, -3949, -1248, 4224], ![14112, 9425, 17232, 5446, -18432], ![-29412, -19643, -35911, -11349, 38412], ![5609, 3746, 6850, 2165, -7327]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 4 2 8 [36, 118, 20, 271, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 205, 25, 56], [36, 178, 232, 176], [206, 182, 26, 51], [0, 1]]
 g := ![![[85, 199, 58, 106], [22, 11, 254, 41], [97, 165, 136], [233, 229, 196, 160], [42, 168, 129, 228], [42, 116, 144], [1], []], ![[208, 266, 62, 48, 20, 79], [173, 226, 145, 192, 70, 205], [250, 5, 70], [158, 7, 199, 139, 118, 187], [273, 83, 21, 244, 273, 20], [210, 259, 228], [236, 258, 144], [41, 246, 23]], ![[19, 123, 204, 40, 192, 238], [194, 23, 62, 72, 156, 116], [170, 277, 169], [107, 188, 132, 193, 169, 169], [241, 228, 171, 205, 271, 54], [52, 247, 95], [125, 121, 275], [254, 10, 129]], ![[221, 112, 161, 245, 93, 64], [93, 234, 215, 86, 151, 86], [217, 183, 163], [147, 192, 30, 175, 113, 176], [12, 78, 221, 204, 15, 77], [272, 209, 266], [173, 185, 266], [28, 187, 54]]]
 h' := ![![[53, 205, 25, 56], [57, 88, 57, 39], [120, 101, 72, 18], [102, 273, 65, 226], [186, 277, 121, 187], [67, 213, 180, 47], [247, 165, 263, 12], [0, 0, 1], [0, 1]], ![[36, 178, 232, 176], [203, 259, 41, 118], [207, 157, 6, 123], [240, 275, 38, 97], [33, 119, 233, 96], [180, 90, 160, 108], [209, 247, 73, 47], [201, 112, 132, 271], [53, 205, 25, 56]], ![[206, 182, 26, 51], [3, 268, 172, 164], [38, 161, 149, 257], [201, 180, 100, 270], [70, 151, 78, 3], [186, 255, 191, 10], [144, 170, 187, 183], [76, 30, 128, 254], [36, 178, 232, 176]], ![[0, 1], [193, 234, 13, 245], [211, 147, 56, 168], [74, 121, 80, 256], [274, 19, 134, 280], [60, 8, 35, 118], [212, 267, 43, 41], [110, 141, 22, 41], [206, 182, 26, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [142, 10, 41], []]
 b := ![[], [], [86, 218, 218, 249], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 4
  hpos := by decide
  P := [36, 118, 20, 271, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-413858946979, -390518592924, -96721943842, 13296749647, 142047126345]
  a := ![-3, 8, -1, 11, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-111385793698, -74662187418, -132852167134, -41613479636, 142047126345]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 6414247921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -19, 9, 4, -8]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-35, -19, 9, 4, -8]] 
 ![![283, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![181, 0, 0, 0, 1]] where
  M :=![![![-35, -19, 9, 4, -8], ![84, 34, -27, -10, 24], ![-258, -125, 54, 24, -48], ![210, 61, -73, -25, 60], ![-46, -34, 0, 2, -3]]]
  hmulB := by decide  
  f := ![![![2289, 1243, -563, -594, 968]], ![![1041, 565, -256, -270, 440]], ![![1284, 699, -316, -334, 544]], ![![528, 283, -129, -135, 220]], ![![1525, 829, -375, -396, 645]]]
  g := ![![![8, -19, 9, 4, -8], ![-14, 34, -27, -10, 24], ![53, -125, 54, 24, -48], ![-21, 61, -73, -25, 60], ![17, -34, 0, 2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-2289, -1243, 563, 594, -968]] ![![-35, -19, 9, 4, -8]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![-283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1284, -104, 194, 49, -145]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-1284, -104, 194, 49, -145]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![67, 250, 1, 0, 0], ![122, 135, 0, 1, 0], ![69, 203, 0, 0, 1]] where
  M :=![![![-1284, -104, 194, 49, -145], ![1593, 21, -202, -49, 153], ![-1689, 216, 119, 49, -129], ![-96, -304, 160, -59, 24], ![-503, -70, 76, 47, -92]]]
  hmulB := by decide  
  f := ![![![2450, 2370, 612, -57, -793]], ![![9687, 9463, 2484, -191, -3063]], ![![8953, 8742, 2293, -178, -2834]], ![![5705, 5569, 1460, -114, -1807]], ![![7436, 7263, 1906, -147, -2352]]]
  g := ![![![-35, -88, 194, 49, -145], ![36, 89, -202, -49, 153], ![-23, -34, 119, 49, -129], ![-18, -127, 160, -59, 24], ![-17, -23, 76, 47, -92]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 2 2 8 [148, 254, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 292], [0, 1]]
 g := ![![[267, 196], [257], [282, 228], [145], [43], [43, 256], [56], [1]], ![[0, 97], [257], [91, 65], [145], [43], [65, 37], [56], [1]]]
 h' := ![![[39, 292], [253, 279], [163, 51], [23, 195], [67, 261], [82, 120], [138, 16], [145, 39], [0, 1]], ![[0, 1], [0, 14], [101, 242], [10, 98], [284, 32], [74, 173], [176, 277], [201, 254], [39, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [164]]
 b := ![[], [159, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 2
  hpos := by decide
  P := [148, 254, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5040, 894, -3278, -4588, 8022]
  a := ![-1, -4, 0, -7, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![788, -644, -3278, -4588, 8022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![626, 239, -155, -59, 135]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![626, 239, -155, -59, 135]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![230, 193, 1, 0, 0], ![73, 243, 0, 1, 0], ![38, 195, 0, 0, 1]] where
  M :=![![![626, 239, -155, -59, 135], ![-1443, -550, 357, 137, -303], ![3225, 1201, -824, -303, 735], ![-3234, -1313, 725, 297, -564], ![255, 28, -124, -27, 146]]]
  hmulB := by decide  
  f := ![![![-24098, -4187, 4385, 1305, -3441]], ![![37377, 6510, -6797, -2027, 5337]], ![![5506, 967, -999, -300, 786]], ![![25085, 4372, -4561, -1361, 3582]], ![![21718, 3784, -3949, -1178, 3101]]]
  g := ![![![121, 62, -155, -59, 135], ![-280, -149, 357, 137, -303], ![638, 309, -824, -303, 735], ![-581, -353, 725, 297, -564], ![86, 7, -124, -27, 146]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [159, 243, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 292], [0, 1]]
 g := ![![[289, 24], [141], [230, 59], [16], [135], [104, 268], [156], [1]], ![[24, 269], [141], [250, 234], [16], [135], [26, 25], [156], [1]]]
 h' := ![![[50, 292], [237, 84], [55, 235], [131, 135], [193, 289], [165, 253], [184, 104], [134, 50], [0, 1]], ![[0, 1], [42, 209], [85, 58], [142, 158], [286, 4], [216, 40], [110, 189], [290, 243], [50, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [6, 199]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [159, 243, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5730, -136500, -200892, -113007, 398331]
  a := ![-27, -11, -10, -32, 111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![134211, -39516, -200892, -113007, 398331]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![591, 225, -147, -56, 128]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![591, 225, -147, -56, 128]] 
 ![![293, 0, 0, 0, 0], ![143, 1, 0, 0, 0], ![61, 0, 1, 0, 0], ![255, 0, 0, 1, 0], ![221, 0, 0, 0, 1]] where
  M :=![![![591, 225, -147, -56, 128], ![-1368, -524, 337, 130, -288], ![3066, 1143, -784, -292, 696], ![-3054, -1235, 695, 285, -564], ![274, 50, -116, -30, 127]]]
  hmulB := by decide  
  f := ![![![-4843, -7, 739, -198, -64]], ![![-2359, -15, 362, -90, -40]], ![![-923, 68, 129, -76, 40]], ![![-4485, -166, 712, -95, -180]], ![![-3605, 25, 545, -164, -25]]]
  g := ![![![-125, 225, -147, -56, 128], ![285, -524, 337, 130, -288], ![-655, 1143, -784, -292, 696], ![625, -1235, 695, 285, -564], ![-69, 50, -116, -30, 127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-1284, -104, 194, 49, -145]] ![![626, 239, -155, -59, 135]]
  ![![-223503, -85079, 55541, 21194, -48044]] where
 M := ![![![-223503, -85079, 55541, 21194, -48044]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![-223503, -85079, 55541, 21194, -48044]] ![![591, 225, -147, -56, 128]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![76695973, 29199794, -19057892, -7280464, 16495900]]]
 hmul := by decide  
 g := ![![![![261761, 99658, -65044, -24848, 56300]]]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![68457, 28371, -17001, -8756, 17588]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![68457, 28371, -17001, -8756, 17588]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![31, 167, 285, 12, 1]] where
  M :=![![![68457, 28371, -17001, -8756, 17588], ![-184788, -80492, 45883, 27442, -52308], ![545370, 252117, -135376, -95176, 172380], ![-799122, -396689, 198293, 166047, -286332], ![137650, 70214, -34148, -30438, 51649]]]
  hmulB := by decide  
  f := ![![![-227, -251, -73, 6, 100]], ![![-1218, -1106, -263, 36, 372]], ![![-4572, -4493, -1178, 110, 1548]], ![![-8844, -8569, -2225, 187, 2796]], ![![-5295, -5152, -1336, 130, 1765]]]
  g := ![![![-1553, -9475, -16383, -716, 17588], ![4680, 28192, 48709, 2134, -52308], ![-15630, -92949, -160468, -7048, 172380], ![26310, 154465, 266459, 11733, -286332], ![-4767, -27867, -48059, -2118, 51649]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 4 2 8 [283, 173, 200, 131, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 125, 260, 203], [0, 172, 151, 204], [135, 9, 203, 207], [0, 1]]
 g := ![![[168, 204, 32, 70], [165, 293, 228, 104], [104, 33, 167], [32, 200, 99], [239, 227, 92, 184], [197, 200, 280, 276], [1], []], ![[8, 233, 246, 187, 54, 74], [266, 136, 285, 259, 174, 116], [161, 26, 25], [136, 52, 81], [90, 225, 288, 153, 75, 172], [11, 276, 51, 280, 200, 163], [53, 157, 70], [173, 168, 71]], ![[44, 232, 219, 19, 255, 18], [22, 11, 7, 62, 190, 52], [32, 217, 176], [81, 263, 287], [198, 104, 92, 296, 224, 128], [150, 105, 99, 93, 255, 161], [177, 294, 93], [133, 218, 171]], ![[8, 53, 245, 14, 255, 48], [106, 77, 25, 152, 195, 20], [133, 272, 294], [152, 220, 262], [75, 262, 59, 119, 2, 283], [123, 274, 48, 242], [223, 269, 114], [113, 200, 176]]]
 h' := ![![[41, 125, 260, 203], [276, 26, 304, 206], [7, 280, 174, 248], [46, 190, 91, 144], [210, 106, 53, 75], [123, 153, 245, 201], [24, 134, 107, 176], [0, 0, 1], [0, 1]], ![[0, 172, 151, 204], [133, 102, 273, 289], [285, 182, 4, 207], [64, 135, 238, 5], [22, 28, 166, 9], [127, 217, 246, 298], [44, 125, 245, 5], [0, 10, 159, 206], [41, 125, 260, 203]], ![[135, 9, 203, 207], [221, 164, 18, 105], [182, 295, 138, 265], [221, 41, 210, 100], [147, 231, 14, 168], [223, 130, 254, 280], [98, 89, 258, 126], [122, 29, 74, 20], [0, 172, 151, 204]], ![[0, 1], [229, 15, 19, 14], [166, 164, 298, 201], [257, 248, 75, 58], [39, 249, 74, 55], [26, 114, 176, 142], [170, 266, 4], [61, 268, 73, 81], [135, 9, 203, 207]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [243, 147, 114], []]
 b := ![[], [], [1, 268, 260, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 4
  hpos := by decide
  P := [283, 173, 200, 131, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-73845136062, -182113516158, -151670782246, -63227451357, 223717727903]
  a := ![-19, -6, -10, -19, 77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22830927365, -122289817837, -208179880243, -8950619499, 223717727903]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 8882874001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![227, 251, 73, -6, -100]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![227, 251, 73, -6, -100]] 
 ![![307, 0, 0, 0, 0], ![160, 1, 0, 0, 0], ![188, 0, 1, 0, 0], ![230, 0, 0, 1, 0], ![182, 0, 0, 0, 1]] where
  M :=![![![227, 251, 73, -6, -100], ![1218, 1106, 263, -36, -372], ![4572, 4493, 1178, -110, -1548], ![8844, 8569, 2225, -187, -2796], ![5974, 5848, 1538, -118, -1899]]]
  hmulB := by decide  
  f := ![![![-68457, -28371, 17001, 8756, -17588]], ![![-35076, -14524, 8711, 4474, -8996]], ![![-43698, -18195, 10852, 5672, -11332]], ![![-48684, -19963, 12091, 6019, -12244]], ![![-41032, -17048, 10190, 5290, -10595]]]
  g := ![![![-111, 251, 73, -6, -100], ![-486, 1106, 263, -36, -372], ![-2048, 4493, 1178, -110, -1548], ![-4002, 8569, 2225, -187, -2796], ![-2756, 5848, 1538, -118, -1899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![68457, 28371, -17001, -8756, 17588]] ![![227, 251, 73, -6, -100]]
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


lemma PB539I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB539I6 : PrimesBelowBoundCertificateInterval O 251 307 539 where
  m := 9
  g := ![2, 2, 3, 3, 2, 4, 2, 3, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB539I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2, I281N3]
    · exact ![I283N0, I283N1]
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
    · exact ![4362470401, 257]
    · exact ![4784350561, 263]
    · exact ![19465109, 269, 269]
    · exact ![19902511, 271, 271]
    · exact ![5887339441, 277]
    · exact ![78961, 281, 281, 281]
    · exact ![6414247921, 283]
    · exact ![85849, 85849, 293]
    · exact ![8882874001, 307]
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
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
      exact NI269N2
    · dsimp ; intro j
      fin_cases j
      exact NI271N0
      exact NI271N1
      exact NI271N2
    · dsimp ; intro j
      fin_cases j
      exact NI277N0
      exact NI277N1
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
      exact NI281N2
      exact NI281N3
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
  β := ![I257N1, I263N1, I269N1, I269N2, I271N1, I271N2, I277N1, I281N1, I281N2, I281N3, I283N1, I293N2, I307N1]
  Il := ![[I257N1], [I263N1], [I269N1, I269N2], [I271N1, I271N2], [I277N1], [I281N1, I281N2, I281N3], [I283N1], [I293N2], [I307N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
