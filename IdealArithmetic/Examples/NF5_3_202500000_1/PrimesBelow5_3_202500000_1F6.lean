
import IdealArithmetic.Examples.NF5_3_202500000_1.RI5_3_202500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, 59, 0, -15, 20]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![87, 59, 0, -15, 20]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![41, 241, 8, 1, 0], ![215, 158, 6, 0, 1]] where
  M :=![![![87, 59, 0, -15, 20], ![130, 92, 14, 5, -90], ![-710, 31, 93, -43, 30], ![-142, -231, -28, 76, -106], ![212, -36, -40, -6, 87]]]
  hmulB := by decide  
  f := ![![![-37, -5, -6, -11, -8]], ![![-86, -50, -32, -37, -66]], ![![-602, -157, -129, -199, -222]], ![![-109, -54, -36, -44, -72]], ![![-99, -39, -28, -37, -53]]]
  g := ![![![-14, 2, 0, -15, 20], ![75, 51, 2, 5, -90], ![-21, 22, 1, -43, 30], ![76, -7, 0, 76, -106], ![-71, -48, -2, -6, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [77, 40, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 196, 148], [81, 60, 109], [0, 1]]
 g := ![![[68, 11, 253], [37, 121], [66, 140], [243, 222], [64, 249], [100, 44], [242, 1], []], ![[96, 185, 46, 149], [247, 42], [181, 222], [188, 146], [218, 128], [31, 221], [37, 2], [77, 59]], ![[154, 102, 152, 101], [216, 168], [123, 32], [70, 178], [165, 124], [210, 62], [232, 123], [116, 59]]]
 h' := ![![[161, 196, 148], [57, 61, 225], [74, 56, 246], [4, 14, 59], [89, 15, 42], [205, 38, 121], [127, 9, 185], [0, 0, 1], [0, 1]], ![[81, 60, 109], [41, 99, 169], [175, 178, 175], [100, 102, 215], [236, 175, 114], [46, 39, 34], [67, 79, 96], [203, 234, 60], [161, 196, 148]], ![[0, 1], [172, 97, 120], [108, 23, 93], [29, 141, 240], [153, 67, 101], [120, 180, 102], [149, 169, 233], [199, 23, 196], [81, 60, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190, 244], []]
 b := ![[], [139, 244, 172], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [77, 40, 15, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79659217, -31191660, -22917854, -28817306, -42613674]
  a := ![-17, -10, -24, -5, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![39936927, 53100154, 1802734, -28817306, -42613674]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -5, -6, -11, -8]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-37, -5, -6, -11, -8]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![143, 232, 1, 0, 0], ![40, 2, 0, 1, 0], ![3, 113, 0, 0, 1]] where
  M :=![![![-37, -5, -6, -11, -8], ![-86, -50, -32, -37, -66], ![-602, -157, -129, -199, -222], ![-954, -367, -262, -348, -494], ![-288, -106, -76, -104, -141]]]
  hmulB := by decide  
  f := ![![![87, 59, 0, -15, 20]], ![![130, 92, 14, 5, -90]], ![![163, 116, 13, -4, -70]], ![![14, 9, 0, -2, 2]], ![![59, 41, 6, 2, -39]]]
  g := ![![![5, 9, -6, -11, -8], ![24, 58, -32, -37, -66], ![103, 215, -129, -199, -222], ![202, 455, -262, -348, -494], ![59, 131, -76, -104, -141]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [44, 231, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 256], [0, 1]]
 g := ![![[198, 111], [120], [124], [134], [58], [205], [162], [1]], ![[0, 146], [120], [124], [134], [58], [205], [162], [1]]]
 h' := ![![[26, 256], [121, 25], [2, 190], [33, 102], [77, 205], [109, 40], [205, 125], [213, 26], [0, 1]], ![[0, 1], [0, 232], [59, 67], [115, 155], [10, 52], [121, 217], [114, 132], [118, 231], [26, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [145, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [44, 231, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5033196, 4884672, 3783221, 2243535, 7238352]
  a := ![-240, -181, -361, -1, -723]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2519159, -6596278, 3783221, 2243535, 7238352]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![87, 59, 0, -15, 20]] ![![-37, -5, -6, -11, -8]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, 31, 9, -26, 36]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-123, 31, 9, -26, 36]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![41, 96, 152, 1, 0], ![165, 209, 205, 0, 1]] where
  M :=![![![-123, 31, 9, -26, 36], ![236, -122, -56, 37, -156], ![-1174, 173, 45, -287, 222], ![88, -411, -248, -60, -552], ![-182, -54, -32, -70, -65]]]
  hmulB := by decide  
  f := ![![![-11, -37, -9, 4, 18]], ![![152, 20, -16, -5, 24]], ![![182, 187, 21, -29, -30]], ![![159, 110, 5, -18, -6]], ![![255, 138, -2, -24, 7]]]
  g := ![![![-19, -19, -13, -26, 36], ![93, 110, 100, 37, -156], ![-99, -71, -7, -287, 222], ![356, 459, 464, -60, -552], ![51, 77, 91, -70, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [25, 257, 156, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 210, 41], [83, 52, 222], [0, 1]]
 g := ![![[241, 238, 186], [124, 212, 169], [4, 175, 218], [156, 143], [158, 190], [85, 13], [107, 1], []], ![[112, 250, 104, 246], [185, 101, 213, 30], [108, 184, 133, 58], [41, 61], [79, 64], [44, 196], [33, 74], [100, 103]], ![[88, 109, 75, 151], [249, 258, 176, 122], [186, 44, 137, 31], [58, 83], [168, 109], [210, 89], [126, 179], [182, 103]]]
 h' := ![![[24, 210, 41], [56, 184, 221], [163, 132, 13], [46, 252, 84], [1, 262, 77], [163, 148, 106], [218, 91, 146], [0, 0, 1], [0, 1]], ![[83, 52, 222], [68, 154, 100], [148, 7, 39], [174, 233, 235], [161, 39, 18], [177, 218, 8], [15, 4, 14], [180, 215, 52], [24, 210, 41]], ![[0, 1], [198, 188, 205], [235, 124, 211], [200, 41, 207], [129, 225, 168], [11, 160, 149], [1, 168, 103], [235, 48, 210], [83, 52, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [175, 178], []]
 b := ![[], [15, 177, 233], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [25, 257, 156, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-46134459, -17575950, -12792900, -16601456, -23804346]
  a := ![-15, -10, -22, -3, -46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17346929, 24909780, 28100834, -16601456, -23804346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![211, 89, 61, 80, 118]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![211, 89, 61, 80, 118]] 
 ![![263, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![114, 0, 1, 0, 0], ![193, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![211, 89, 61, 80, 118], ![1104, 348, 268, 381, 480], ![4602, 1697, 1223, 1665, 2286], ![9108, 3125, 2320, 3222, 4252], ![2670, 920, 682, 946, 1251]]]
  hmulB := by decide  
  f := ![![![12515, -3883, -2573, 3262, -6076]], ![![3742, -1164, -770, 977, -1820]], ![![5940, -1841, -1221, 1545, -2874]], ![![8749, -2716, -1799, 2282, -4252]], ![![5251, -1627, -1079, 1368, -2549]]]
  g := ![![![-161, 89, 61, 80, 118], ![-699, 348, 268, 381, 480], ![-3211, 1697, 1223, 1665, 2286], ![-6072, 3125, 2320, 3222, 4252], ![-1785, 920, 682, 946, 1251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2931, -897, -603, 746, -1386]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![2931, -897, -603, 746, -1386]] 
 ![![263, 0, 0, 0, 0], ![250, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![259, 0, 0, 1, 0], ![79, 0, 0, 0, 1]] where
  M :=![![![2931, -897, -603, 746, -1386], ![-9596, 2894, 1944, -2449, 4476], ![30910, -9513, -6397, 7859, -14694], ![-26840, 7951, 5336, -6872, 12312], ![3766, -1208, -814, 950, -1861]]]
  hmulB := by decide  
  f := ![![![3923, 1895, 283, -100, -1260]], ![![3690, 1810, 274, -97, -1200]], ![![1380, 629, 99, -25, -462]], ![![3819, 1846, 275, -98, -1224]], ![![1221, 589, 83, -34, -373]]]
  g := ![![![761, -897, -603, 746, -1386], ![-2415, 2894, 1944, -2449, 4476], ![8121, -9513, -6397, 7859, -14694], ![-6498, 7951, 5336, -6872, 12312], ![1077, -1208, -814, 950, -1861]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-123, 31, 9, -26, 36]] ![![211, 89, 61, 80, 118]]
  ![![-90999, -33016, -23956, -32760, -44576]] where
 M := ![![![-90999, -33016, -23956, -32760, -44576]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![-90999, -33016, -23956, -32760, -44576]] ![![2931, -897, -603, 746, -1386]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![21028691, 7344275, 5413329, 7480246, 9969278]]]
 hmul := by decide  
 g := ![![![![79957, 27925, 20583, 28442, 37906]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-881, -1059, -159, 140, 304]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-881, -1059, -159, 140, 304]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![188, 71, 239, 1, 0], ![99, 193, 200, 0, 1]] where
  M :=![![![-881, -1059, -159, 140, 304], ![2712, -278, -480, -33, 840], ![6654, 3999, 103, -633, -198], ![2172, 3147, 540, -396, -1052], ![-5382, -2094, 228, 370, -363]]]
  hmulB := by decide  
  f := ![![![437, -117, -3, 70, -106]], ![![-708, 404, 96, -45, 420]], ![![3270, -429, 173, 663, -270]], ![![3026, -352, 179, 628, -198]], ![![2085, -71, 197, 487, 63]]]
  g := ![![![-213, -259, -351, 140, 304], ![-276, -595, -597, -33, 840], ![540, 324, 710, -633, -198], ![672, 871, 1136, -396, -1052], ![-145, 155, -58, 370, -363]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [18, 253, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 119, 69], [83, 149, 200], [0, 1]]
 g := ![![[43, 174, 182], [25, 97], [266, 149, 66], [59, 221, 93], [189, 185], [95, 215], [116, 1], []], ![[62, 77, 154, 50], [149, 53], [73, 232, 14, 98], [5, 178, 67, 194], [75, 47], [263, 70], [204, 143], [32, 188]], ![[265, 38, 119, 146], [164, 61], [225, 207, 130, 76], [45, 116, 35, 200], [236, 182], [223, 96], [198, 173], [170, 188]]]
 h' := ![![[33, 119, 69], [45, 169, 102], [54, 156, 108], [14, 12, 214], [244, 73, 239], [234, 229, 202], [64, 224, 22], [0, 0, 1], [0, 1]], ![[83, 149, 200], [113, 228, 228], [81, 59, 225], [171, 184, 165], [175, 183, 29], [51, 117, 169], [181, 146, 173], [244, 140, 149], [33, 119, 69]], ![[0, 1], [54, 141, 208], [169, 54, 205], [235, 73, 159], [109, 13, 1], [225, 192, 167], [136, 168, 74], [63, 129, 119], [83, 149, 200]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182, 66], []]
 b := ![[], [129, 23, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [18, 253, 153, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9450492860, 4555646862, 3353954733, 3543239289, 6328935085]
  a := ![98, 72, 147, -1, 293]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4770420323, -5459103398, -7841142202, 3543239289, 6328935085]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-437, 117, 3, -70, 106]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-437, 117, 3, -70, 106]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![160, 89, 1, 0, 0], ![59, 222, 0, 1, 0], ![43, 267, 0, 0, 1]] where
  M :=![![![-437, 117, 3, -70, 106], ![708, -404, -96, 45, -420], ![-3270, 429, -173, -663, 270], ![-576, -1155, -552, -510, -1376], ![-246, -312, -162, -158, -381]]]
  hmulB := by decide  
  f := ![![![881, 1059, 159, -140, -304]], ![![-2712, 278, 480, 33, -840]], ![![-398, 707, 253, -70, -458]], ![![-2053, 450, 429, -2, -756]], ![![-2531, 453, 501, 9, -881]]]
  g := ![![![-5, -48, 3, -70, 106], ![117, 410, -96, 45, -420], ![193, 338, -173, -663, 270], ![658, 1965, -552, -510, -1376], ![191, 561, -162, -158, -381]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [206, 215, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 268], [0, 1]]
 g := ![![[193, 93], [81], [258, 70], [57, 70], [220], [211], [226], [1]], ![[104, 176], [81], [3, 199], [71, 199], [220], [211], [226], [1]]]
 h' := ![![[54, 268], [76, 239], [114, 9], [94, 173], [237, 96], [74, 233], [184, 178], [63, 54], [0, 1]], ![[0, 1], [70, 30], [62, 260], [21, 96], [41, 173], [13, 36], [112, 91], [20, 215], [54, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [26, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [206, 215, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14528, 73891, 53335, 17590, 103850]
  a := ![-32, -24, -50, 8, -95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52128, -134966, 53335, 17590, 103850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-881, -1059, -159, 140, 304]] ![![-437, 117, 3, -70, 106]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5639, -1764, -1161, 1463, -2706]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![5639, -1764, -1161, 1463, -2706]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![258, 101, 184, 27, 1]] where
  M :=![![![5639, -1764, -1161, 1463, -2706], ![-18722, 5557, 3786, -4726, 8778], ![60772, -18456, -12407, 15410, -28356], ![-51326, 15778, 10520, -13161, 24294], ![7414, -2192, -1498, 1904, -3593]]]
  hmulB := by decide  
  f := ![![![-9, -10, -5, -5, -12]], ![![-106, -21, -20, -32, -30]], ![![-304, -148, -97, -122, -192]], ![![-730, -230, -178, -253, -318]], ![![-328, -141, -96, -125, -185]]]
  g := ![![![2597, 1002, 1833, 275, -2706], ![-8426, -3251, -5946, -892, 8778], ![27220, 10500, 19207, 2882, -28356], ![-23318, -8996, -16456, -2469, 24294], ![3448, 1331, 2434, 365, -3593]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [128, 74, 11, 178, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 36, 209, 22], [85, 199, 204, 36], [177, 35, 129, 213], [0, 1]]
 g := ![![[122, 236, 129, 162], [175, 80, 106, 32], [202, 262, 76, 103], [21, 264, 139, 82], [257, 270, 11], [111, 151, 248], [1], []], ![[16, 102, 59, 215, 2, 89], [66, 182, 168, 264, 35, 74], [185, 236, 75, 89, 47, 242], [235, 44, 229, 190, 182, 163], [217, 85, 213], [240, 202, 136], [235, 111, 185], [35, 8, 213]], ![[246, 203, 192, 261, 182, 153], [54, 42, 137, 255, 103, 217], [20, 30, 114, 167, 168, 247], [21, 205, 113, 106, 149, 220], [77, 91, 265], [154, 14, 69], [108, 86, 89], [100, 258, 212]], ![[213, 202, 144, 54, 4, 103], [55, 182, 50, 143, 157, 32], [253, 74, 217, 9, 74, 56], [237, 231, 72, 9, 6, 61], [225, 134, 62], [216, 204, 67], [227, 13, 153], [34, 59, 112]]]
 h' := ![![[102, 36, 209, 22], [93, 242, 5, 51], [160, 238, 124, 113], [22, 210, 255, 153], [230, 180, 115, 176], [8, 74, 196, 108], [143, 197, 260, 93], [0, 0, 1], [0, 1]], ![[85, 199, 204, 36], [214, 235, 5, 224], [69, 78, 99, 29], [150, 102, 53, 163], [6, 63, 232, 152], [144, 42, 143, 22], [90, 95, 124, 223], [233, 207, 244, 166], [102, 36, 209, 22]], ![[177, 35, 129, 213], [40, 3, 1, 237], [27, 155, 98, 245], [103, 114, 108, 198], [196, 220, 22, 167], [266, 32, 259, 52], [174, 228, 38, 119], [116, 181, 124, 38], [85, 199, 204, 36]], ![[0, 1], [116, 62, 260, 30], [90, 71, 221, 155], [105, 116, 126, 28], [266, 79, 173, 47], [119, 123, 215, 89], [165, 22, 120, 107], [148, 154, 173, 67], [177, 35, 129, 213]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [208, 53, 31], []]
 b := ![[], [], [63, 230, 86, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [128, 74, 11, 178, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40068507624, 12161321104, 8627436932, -10509244516, 19254196776]
  a := ![14, 18, 30, -26, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18478417992, -7131042632, -13041124612, -1957094308, 19254196776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 10, 5, 5, 12]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![9, 10, 5, 5, 12]] 
 ![![271, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![153, 0, 0, 0, 1]] where
  M :=![![![9, 10, 5, 5, 12], ![106, 21, 20, 32, 30], ![304, 148, 97, 122, 192], ![730, 230, 178, 253, 318], ![214, 68, 52, 74, 95]]]
  hmulB := by decide  
  f := ![![![-5639, 1764, 1161, -1463, 2706]], ![![-2199, 689, 453, -571, 1056]], ![![-1119, 348, 230, -289, 534]], ![![-310, 98, 64, -81, 150]], ![![-3211, 1004, 661, -833, 1541]]]
  g := ![![![-12, 10, 5, 5, 12], ![-31, 21, 20, 32, 30], ![-193, 148, 97, 122, 192], ![-320, 230, 178, 253, 318], ![-95, 68, 52, 74, 95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![5639, -1764, -1161, 1463, -2706]] ![![9, 10, 5, 5, 12]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![-271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7579, -3002, -292, 1158, -2898]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![7579, -3002, -292, 1158, -2898]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![208, 251, 28, 1, 0], ![193, 260, 195, 0, 1]] where
  M :=![![![7579, -3002, -292, 1158, -2898], ![-20868, 6131, 764, -2616, 6948], ![50352, -17300, -2481, 6624, -15696], ![-27612, 10864, 1112, -4169, 10332], ![-7236, 3058, 566, -984, 1765]]]
  hmulB := by decide  
  f := ![![![-12857, 3950, 2656, -3270, 6102]], ![![42276, -12681, -8516, 10800, -19620]], ![![-135360, 41972, 28235, -34368, 64800]], ![![15400, -4407, -2952, 3967, -6840]], ![![-64625, 20416, 13747, -16350, 31483]]]
  g := ![![![1177, 1660, 1922, 1158, -2898], ![-2952, -4129, -4624, -2616, 6948], ![6144, 8668, 10371, 6624, -15696], ![-4168, -5881, -6848, -4169, 10332], ![-517, -754, -1141, -984, 1765]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [11, 105, 238, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 40, 214], [161, 236, 63], [0, 1]]
 g := ![![[137, 234, 22], [234, 92], [250, 174, 62], [48, 276], [161, 13, 123], [75, 130], [39, 1], []], ![[256, 183, 23, 9], [6, 225], [247, 104, 15, 264], [26, 85], [153, 219, 184, 189], [6, 213], [122, 19], [171, 91]], ![[271, 14, 202, 186], [21, 203], [103, 179, 114, 16], [104, 225], [37, 244, 251, 1], [136, 222], [194, 215], [45, 91]]]
 h' := ![![[155, 40, 214], [42, 264, 24], [20, 106, 107], [273, 256, 93], [168, 160, 60], [119, 175, 257], [125, 49, 31], [0, 0, 1], [0, 1]], ![[161, 236, 63], [136, 26, 112], [57, 234, 15], [239, 237, 3], [186, 9, 202], [141, 174, 44], [22, 103, 74], [261, 92, 236], [155, 40, 214]], ![[0, 1], [158, 264, 141], [77, 214, 155], [85, 61, 181], [11, 108, 15], [92, 205, 253], [122, 125, 172], [219, 185, 40], [161, 236, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 20], []]
 b := ![[], [252, 256, 163], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [11, 105, 238, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16122099, 6053834, 4485098, 5821974, 8293708]
  a := ![12, 6, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10092181, -13038360, -6410842, 5821974, 8293708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, 23, 5, -6, 6]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-41, 23, 5, -6, 6]] 
 ![![277, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![230, 0, 1, 0, 0], ![180, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-41, 23, 5, -6, 6], ![36, -46, 0, 15, -36], ![-258, 15, -1, -21, 90], ![152, -73, -16, 20, -24], ![86, 32, 2, -2, -17]]]
  hmulB := by decide  
  f := ![![![-3587, -1315, -967, -1284, -1788]], ![![-294, -106, -78, -105, -144]], ![![-3244, -1187, -873, -1161, -1614]], ![![-2848, -1033, -760, -1018, -1404]], ![![-811, -295, -217, -290, -401]]]
  g := ![![![-3, 23, 5, -6, 6], ![0, -46, 0, 15, -36], ![-4, 15, -1, -21, 90], ![10, -73, -16, 20, -24], ![1, 32, 2, -2, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-379, 134, 82, -104, 188]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![-379, 134, 82, -104, 188]] 
 ![![277, 0, 0, 0, 0], ![174, 1, 0, 0, 0], ![194, 0, 1, 0, 0], ![43, 0, 0, 1, 0], ![236, 0, 0, 0, 1]] where
  M :=![![![-379, 134, 82, -104, 188], ![1296, -377, -260, 330, -624], ![-4332, 1262, 873, -1074, 1980], ![3552, -1138, -740, 927, -1696], ![-468, 164, 100, -136, 261]]]
  hmulB := by decide  
  f := ![![![430409, -149462, -18586, 58672, -145108]], ![![266598, -92577, -11512, 36342, -89880]], ![![310582, -107850, -13411, 42338, -104708]], ![![61223, -21256, -2642, 8347, -20636]], ![![365440, -126900, -15780, 49816, -123203]]]
  g := ![![![-287, 134, 82, -104, 188], ![904, -377, -260, 330, -624], ![-2940, 1262, 873, -1074, 1980], ![2547, -1138, -740, 927, -1696], ![-376, 164, 100, -136, 261]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![7579, -3002, -292, 1158, -2898]] ![![-41, 23, 5, -6, 6]]
  ![![-416687, 130759, 13863, -55416, 148740]] where
 M := ![![![-416687, 130759, 13863, -55416, 148740]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![-416687, 130759, 13863, -55416, 148740]] ![![-379, 134, 82, -104, 188]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![885569, -180327, -181435, -2216, 324644]]]
 hmul := by decide  
 g := ![![![![3197, -651, -655, -8, 1172]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2145, 104, -232, -30, 286]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![2145, 104, -232, -30, 286]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![245, 206, 178, 1, 0], ![213, 189, 10, 0, 1]] where
  M :=![![![2145, 104, -232, -30, 286], ![2228, 2633, 246, -440, -180], ![-2320, 1362, 1067, 118, -2640], ![-6992, -638, 654, 119, -704], ![340, -2420, -762, 234, 1491]]]
  hmulB := by decide  
  f := ![![![-1967, 516, 344, -514, 806]], ![![5420, -2019, -1370, 1324, -3084]], ![![-22024, 5030, 3323, -5870, 7944]], ![![-11651, 2132, 1384, -3187, 3438]], ![![1357, -787, -542, 288, -1179]]]
  g := ![![![-183, -170, 8, -30, 286], ![528, 453, 286, -440, -180], ![1890, 1694, 23, 118, -2640], ![405, 384, -48, 119, -704], ![-1333, -1183, -204, 234, 1491]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [275, 41, 109, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 112, 1], [72, 168, 280], [0, 1]]
 g := ![![[204, 174, 246], [185, 136], [94, 217], [269, 7, 225], [49, 197, 196], [54, 39], [172, 1], []], ![[189, 89, 19, 212], [176, 136], [120, 1], [34, 63, 239, 280], [74, 178, 45, 160], [161, 165], [155, 124], [115, 1]], ![[11, 20, 244, 50], [], [45, 213], [236, 71, 6, 242], [32, 102, 230, 180], [83, 191], [209, 180], [117, 1]]]
 h' := ![![[100, 112, 1], [72, 102, 248], [128, 186, 97], [209, 141, 143], [13, 44, 266], [77, 198, 14], [189, 260, 38], [0, 0, 1], [0, 1]], ![[72, 168, 280], [41, 18, 178], [222, 279, 184], [8, 26, 280], [18, 50, 53], [94, 90, 21], [231, 2, 181], [12, 269, 168], [100, 112, 1]], ![[0, 1], [43, 161, 136], [263, 97], [67, 114, 139], [34, 187, 243], [73, 274, 246], [74, 19, 62], [266, 12, 112], [72, 168, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 240], []]
 b := ![[], [280, 169, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [275, 41, 109, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5059737, -1879170, -1359807, -1814943, -2526105]
  a := ![-8, -6, -11, -1, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3479223, 3022893, 1234737, -1814943, -2526105]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![367, -128, -16, 50, -124]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![367, -128, -16, 50, -124]] 
 ![![281, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![226, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![367, -128, -16, 50, -124], ![-892, 309, 38, -122, 300], ![2156, -752, -95, 292, -732], ![-1336, 456, 54, -185, 440], ![-304, 102, 12, -42, 99]]]
  hmulB := by decide  
  f := ![![![-873, 360, 204, -234, 364]], ![![-128, 53, 30, -34, 52]], ![![-131, 48, 29, -34, 56]], ![![-674, 280, 158, -181, 280]], ![![-341, 142, 80, -92, 143]]]
  g := ![![![31, -128, -16, 50, -124], ![-74, 309, 38, -122, 300], ![185, -752, -95, 292, -732], ![-104, 456, 54, -185, 440], ![-23, 102, 12, -42, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -51, 24, 19, -74]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![-151, -51, 24, 19, -74]] 
 ![![281, 0, 0, 0, 0], ![264, 1, 0, 0, 0], ![273, 0, 1, 0, 0], ![40, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-151, -51, 24, 19, -74], ![-554, -230, -18, 17, 114], ![946, -405, -161, 77, 102], ![454, 217, -64, -70, 226], ![-128, 334, 98, -42, -153]]]
  hmulB := by decide  
  f := ![![![1039389, -316187, -212494, 264843, -488758]], ![![964478, -293400, -197180, 245755, -453534]], ![![1048907, -319084, -214441, 267268, -493236]], ![![114578, -34863, -23430, 29194, -53890]], ![![252683, -76869, -51660, 64385, -118823]]]
  g := ![![![39, -51, 24, 19, -74], ![202, -230, -18, 17, 114], ![505, -405, -161, 77, 102], ![-184, 217, -64, -70, 226], ![-367, 334, 98, -42, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![2145, 104, -232, -30, 286]] ![![367, -128, -16, 50, -124]]
  ![![147391, -52468, -6516, 20356, -49842]] where
 M := ![![![147391, -52468, -6516, 20356, -49842]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![147391, -52468, -6516, 20356, -49842]] ![![-151, -51, 24, 19, -74]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![16268495, -5040297, -656416, 2075185, -5326636]]]
 hmul := by decide  
 g := ![![![![57895, -17937, -2336, 7385, -18956]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12643, -4400, -530, 1712, -4252]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![12643, -4400, -530, 1712, -4252]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![94, 103, 197, 281, 1]] where
  M :=![![![12643, -4400, -530, 1712, -4252], ![-30592, 10633, 1266, -4130, 10272], ![73916, -25716, -3023, 9940, -24780], ![-45012, 15672, 1790, -6033, 15044], ![-10524, 3642, 476, -1450, 3555]]]
  hmulB := by decide  
  f := ![![![-15, 0, 2, 0, -4]], ![![-32, -21, -2, 2, 0]], ![![4, -28, -13, -4, 12]], ![![20, -8, -14, -11, -4]], ![![6, -35, -23, -13, 3]]]
  g := ![![![1457, 1532, 2958, 4228, -4252], ![-3520, -3701, -7146, -10214, 10272], ![8492, 8928, 17239, 24640, -24780], ![-5156, -5420, -10466, -14959, 15044], ![-1218, -1281, -2473, -3535, 3555]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 4 2 8 [55, 250, 143, 122, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [227, 275, 77, 52], [272, 124, 120, 125], [228, 166, 86, 106], [0, 1]]
 g := ![![[248, 105, 227, 92], [183, 73, 118, 275], [216, 279, 41], [238, 257, 8, 275], [231, 143, 136, 99], [245, 246, 168], [1], []], ![[80, 27, 231, 16, 241, 141], [189, 163, 103, 126, 207, 11], [280, 37, 117], [14, 180, 27, 221, 241, 251], [161, 38, 211, 185, 45, 269], [238, 226, 81], [112, 136, 49], [189, 174, 157]], ![[241, 81, 94, 101, 175, 242], [150, 191, 81, 147, 91, 205], [231, 8, 23], [196, 137, 94, 67, 62, 118], [50, 206, 196, 26, 265, 188], [34, 147, 16], [266, 153, 121], [244, 40, 60]], ![[212, 22, 98, 219, 136, 228], [58, 14, 32, 191, 143, 275], [163, 104, 63], [86, 94, 156, 79, 268, 95], [140, 127, 198, 83, 222, 94], [146, 98, 105], [131, 19, 16], [95, 180, 199]]]
 h' := ![![[227, 275, 77, 52], [123, 203, 31, 171], [96, 0, 34, 29], [211, 279, 97, 265], [30, 199, 198, 29], [21, 264, 189, 209], [228, 33, 140, 161], [0, 0, 1], [0, 1]], ![[272, 124, 120, 125], [33, 264, 12, 263], [20, 258, 143, 16], [103, 138, 187, 263], [235, 9, 81, 160], [240, 278, 183, 27], [245, 167, 27, 9], [99, 110, 8, 276], [227, 275, 77, 52]], ![[228, 166, 86, 106], [82, 48, 176, 80], [133, 259, 192, 230], [195, 213, 81, 227], [187, 137, 34, 24], [4, 75, 227, 130], [90, 124, 56, 279], [2, 11, 202, 11], [272, 124, 120, 125]], ![[0, 1], [141, 51, 64, 52], [115, 49, 197, 8], [249, 219, 201, 94], [166, 221, 253, 70], [193, 232, 250, 200], [4, 242, 60, 117], [64, 162, 72, 279], [228, 166, 86, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [254, 16, 212], []]
 b := ![[], [], [35, 121, 183, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 4
  hpos := by decide
  P := [55, 250, 143, 122, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61630072421, 23045327072, 16956260158, 22147949306, 31429043982]
  a := ![16, 10, 23, 2, 45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10221554989, -11357407078, -21818252312, -31128669292, 31429043982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 6414247921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 0, -2, 0, 4]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![15, 0, -2, 0, 4]] 
 ![![283, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![249, 0, 0, 1, 0], ![144, 0, 0, 0, 1]] where
  M :=![![![15, 0, -2, 0, 4], ![32, 21, 2, -2, 0], ![-4, 28, 13, 4, -12], ![-20, 8, 14, 11, 4], ![4, -22, -4, 6, 15]]]
  hmulB := by decide  
  f := ![![![-12643, 4400, 530, -1712, 4252]], ![![-428, 149, 18, -58, 144]], ![![-6471, 2252, 271, -876, 2176]], ![![-10965, 3816, 460, -1485, 3688]], ![![-6396, 2226, 268, -866, 2151]]]
  g := ![![![-1, 0, -2, 0, 4], ![0, 21, 2, -2, 0], ![-5, 28, 13, 4, -12], ![-19, 8, 14, 11, 4], ![-10, -22, -4, 6, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![12643, -4400, -530, 1712, -4252]] ![![15, 0, -2, 0, 4]]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 9, 1, -2, 12]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-15, 9, 1, -2, 12]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![85, 21, 1, 0, 0], ![117, 181, 0, 1, 0], ![60, 78, 0, 0, 1]] where
  M :=![![![-15, 9, 1, -2, 12], ![92, -6, 2, 13, -12], ![-70, 91, 31, 7, 78], ![220, 23, 38, 66, 36], ![58, -4, 8, 20, 19]]]
  hmulB := by decide  
  f := ![![![-821, 259, 169, -212, 390]], ![![2696, -812, -546, 685, -1272]], ![![-75, 26, 16, -20, 36]], ![![1363, -406, -275, 345, -642]], ![![546, -162, -110, 138, -257]]]
  g := ![![![-2, -2, 1, -2, 12], ![-3, -5, 2, 13, -12], ![-28, -27, 31, 7, 78], ![-44, -53, 38, 66, 36], ![-14, -18, 8, 20, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 2 2 8 [119, 273, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 292], [0, 1]]
 g := ![![[54, 153], [209], [7, 267], [54], [100], [127, 289], [107], [1]], ![[184, 140], [209], [73, 26], [54], [100], [47, 4], [107], [1]]]
 h' := ![![[20, 292], [99, 118], [46, 217], [56, 248], [6, 126], [123, 283], [256, 17], [174, 20], [0, 1]], ![[0, 1], [115, 175], [284, 76], [35, 45], [182, 167], [216, 10], [10, 276], [281, 273], [20, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [46, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 2
  hpos := by decide
  P := [119, 273, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24539, 49423, 45972, 9563, 88840]
  a := ![24, 18, 37, -5, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35264, -32684, 45972, 9563, 88840]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -5, -1, 4, -12]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![25, -5, -1, 4, -12]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![46, 198, 1, 0, 0], ![7, 198, 0, 1, 0], ![265, 172, 0, 0, 1]] where
  M :=![![![25, -5, -1, 4, -12], ![-88, 18, 8, -11, 24], ![170, -83, -23, 37, -66], ![-124, 33, 12, -24, 60], ![14, 18, 0, -2, -1]]]
  hmulB := by decide  
  f := ![![![27, -3, 3, 10, 6]], ![![68, 40, 24, 25, 60]], ![![52, 27, 17, 19, 42]], ![![49, 28, 17, 18, 42]], ![![65, 21, 17, 24, 41]]]
  g := ![![![11, 5, -1, 4, -12], ![-23, -12, 8, -11, 24], ![63, 29, -23, 37, -66], ![-56, -27, 12, -24, 60], ![1, 2, 0, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [131, 233, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 292], [0, 1]]
 g := ![![[174, 77], [262], [158, 278], [239], [57], [132, 137], [84], [1]], ![[106, 216], [262], [137, 15], [239], [57], [148, 156], [84], [1]]]
 h' := ![![[60, 292], [143, 91], [105, 153], [253, 82], [176, 101], [288, 244], [4, 161], [162, 60], [0, 1]], ![[0, 1], [36, 202], [202, 140], [192, 211], [83, 192], [278, 49], [288, 132], [246, 233], [60, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [173, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [131, 233, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13177, 9744, 9597, 4625, 18838]
  a := ![11, 7, 14, 1, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-18610, -20636, 9597, 4625, 18838]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1

def I293N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, -12, -8, 10, -18]] i)))

def SI293N2: IdealEqSpanCertificate' Table ![![39, -12, -8, 10, -18]] 
 ![![293, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![252, 0, 0, 1, 0], ![162, 0, 0, 0, 1]] where
  M :=![![![39, -12, -8, 10, -18], ![-124, 39, 26, -32, 60], ![416, -122, -83, 106, -192], ![-344, 110, 74, -87, 168], ![52, -16, -10, 14, -23]]]
  hmulB := by decide  
  f := ![![![-581, 304, 40, -98, 198]], ![![-142, 75, 10, -24, 48]], ![![-195, 98, 13, -32, 66]], ![![-492, 258, 34, -83, 168]], ![![-318, 168, 22, -54, 109]]]
  g := ![![![7, -12, -8, 10, -18], ![-24, 39, 26, -32, 60], ![73, -122, -83, 106, -192], ![-70, 110, 74, -87, 168], ![8, -16, -10, 14, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N2 : Nat.card (O ⧸ I293N2) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N2)

lemma isPrimeI293N2 : Ideal.IsPrime I293N2 := prime_ideal_of_norm_prime hp293.out _ NI293N2
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-15, 9, 1, -2, 12]] ![![25, -5, -1, 4, -12]]
  ![![-581, 304, 40, -98, 198]] where
 M := ![![![-581, 304, 40, -98, 198]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI293N1 : IdealMulLeCertificate' Table 
  ![![-581, 304, 40, -98, 198]] ![![39, -12, -8, 10, -18]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1634583, 497179, 334127, -416512, 768540]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-1634583, 497179, 334127, -416512, 768540]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![208, 107, 197, 171, 1]] where
  M :=![![![-1634583, 497179, 334127, -416512, 768540], ![5315296, -1616682, -1086484, 1354409, -2499072], ![-17283758, 5257117, 3533029, -4404115, 8126454], ![14744980, -4484671, -3013904, 3757240, -6932436], ![-2147474, 653222, 439000, -547198, 1009751]]]
  hmulB := by decide  
  f := ![![![13, 99, 21, -14, -30]], ![![-268, -52, 36, 19, -84]], ![![-634, -369, -31, 43, 114]], ![![32, -289, -68, 42, 96]], ![![-472, -348, -31, 48, 77]]]
  g := ![![![-526029, -266243, -492079, -429436, 768540], ![1710496, 865746, 1600100, 1396403, -2499072], ![-5562170, -2815223, -5203187, -4540807, 8126454], ![4744924, 2401583, 4438684, 3873628, -6932436], ![-691126, -349805, -646521, -564217, 1009751]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 4 2 8 [294, 13, 212, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 154, 261, 246], [129, 251, 104, 98], [94, 208, 249, 270], [0, 1]]
 g := ![![[289, 132, 74, 191], [193, 8, 186, 112], [14, 85, 25], [293, 211, 184], [68, 127, 140, 96], [138, 107, 263, 121], [1], []], ![[256, 299, 113, 182, 269, 17], [103, 151, 186, 299, 225, 273], [165, 54, 276], [277, 49, 49], [117, 229, 10, 245, 0, 176], [27, 39, 287, 127, 128, 276], [111, 68, 60], [198, 293, 37]], ![[101, 24, 287, 166, 145, 172], [252, 194, 271, 122, 171, 161], [70, 260, 227], [225, 280, 1], [200, 203, 27, 123, 45, 123], [65, 209, 36, 204, 49, 157], [298, 143, 145], [98, 86, 87]], ![[156, 236, 205, 122, 245, 56], [221, 94, 175, 141, 142, 158], [137, 27, 90], [272, 150, 264], [149, 229, 36, 144, 280, 180], [182, 271, 174, 275, 142, 242], [229, 228, 87], [74, 285, 141]]]
 h' := ![![[73, 154, 261, 246], [53, 185, 101, 67], [21, 154, 194, 135], [266, 88, 271, 302], [270, 1, 235, 106], [259, 73, 64, 230], [13, 294, 95, 296], [0, 0, 1], [0, 1]], ![[129, 251, 104, 98], [105, 268, 144, 14], [129, 213, 284, 284], [146, 258, 171, 176], [42, 148, 42, 7], [124, 215, 12, 161], [9, 2, 226, 136], [228, 80, 247, 260], [73, 154, 261, 246]], ![[94, 208, 249, 270], [134, 105, 160, 114], [221, 4, 71, 97], [132, 193, 74, 29], [225, 269, 8, 306], [95, 264, 270, 191], [98, 52, 155, 282], [109, 132, 302, 256], [129, 251, 104, 98]], ![[0, 1], [77, 56, 209, 112], [15, 243, 65, 98], [136, 75, 98, 107], [99, 196, 22, 195], [293, 62, 268, 32], [276, 266, 138, 207], [281, 95, 64, 98], [94, 208, 249, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [109, 60, 15], []]
 b := ![[], [], [199, 271, 135, 216], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 4
  hpos := by decide
  P := [294, 13, 212, 11, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14046658884, 35563171626, 25542169614, 856290450, 52202981139]
  a := ![10, 24, 24, -50, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35414549628, -18078683421, -33415130667, -29074441317, 52202981139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 8882874001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -99, -21, 14, 30]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-13, -99, -21, 14, 30]] 
 ![![307, 0, 0, 0, 0], ![202, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![305, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-13, -99, -21, 14, 30], ![268, 52, -36, -19, 84], ![634, 369, 31, -43, -114], ![-32, 289, 68, -42, -96], ![-494, -248, 2, 38, 7]]]
  hmulB := by decide  
  f := ![![![1634583, -497179, -334127, 416512, -768540]], ![![1058210, -321868, -216310, 269645, -497544]], ![![200057, -60850, -40894, 50977, -94062]], ![![1575905, -479332, -322133, 401560, -740952]], ![![390350, -118730, -79792, 99466, -183533]]]
  g := ![![![46, -99, -21, 14, 30], ![-31, 52, -36, -19, 84], ![-174, 369, 31, -43, -114], ![-132, 289, 68, -42, -96], ![122, -248, 2, 38, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-1634583, 497179, 334127, -416512, 768540]] ![![-13, -99, -21, 14, 30]]
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


lemma PB696I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB696I6 : PrimesBelowBoundCertificateInterval O 251 307 696 where
  m := 9
  g := ![2, 3, 2, 2, 3, 3, 2, 3, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB696I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1, I277N2]
    · exact ![I281N0, I281N1, I281N2]
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
    · exact ![16974593, 66049]
    · exact ![18191447, 263, 263]
    · exact ![19465109, 72361]
    · exact ![5393580481, 271]
    · exact ![21253933, 277, 277]
    · exact ![22188041, 281, 281]
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
      exact NI263N2
    · dsimp ; intro j
      fin_cases j
      exact NI269N0
      exact NI269N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
      exact NI293N2
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
  β := ![I263N1, I263N2, I271N1, I277N1, I277N2, I281N1, I281N2, I283N1, I293N2, I307N1]
  Il := ![[], [I263N1, I263N2], [], [I271N1], [I277N1, I277N2], [I281N1, I281N2], [I283N1], [I293N2], [I307N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
