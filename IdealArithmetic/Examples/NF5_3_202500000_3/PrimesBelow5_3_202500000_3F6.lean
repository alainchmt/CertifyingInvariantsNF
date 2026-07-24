
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 6, -283, 161, 492]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-53, 6, -283, 161, 492]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![112, 124, 92, 1, 0], ![16, 253, 67, 0, 1]] where
  M :=![![![-53, 6, -283, 161, 492], ![108, -166, 633, -334, -932], ![840, 477, -48, -102, -904], ![-3642, 129, -5015, 3007, 10238], ![1818, 139, 1935, -1216, -4385]]]
  hmulB := by decide  
  f := ![![![401, 258, 337, -241, -642]], ![![972, 578, 831, -618, -1628]], ![![2712, 1411, 2340, -1834, -4760]], ![![1630, 903, 1399, -1071, -2798]], ![![1690, 954, 1450, -1102, -2885]]]
  g := ![![![-101, -562, -187, 161, 492], ![204, 1078, 365, -334, -932], ![104, 941, 272, -102, -904], ![-1962, -11529, -3765, 3007, 10238], ![810, 4904, 1586, -1216, -4385]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [98, 113, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [224, 211, 163], [194, 45, 94], [0, 1]]
 g := ![![[218, 50, 50], [206, 64], [191, 15], [134, 190], [239, 95], [10, 99], [161, 1], []], ![[213, 165, 135, 28], [81, 199], [249, 26], [184, 213], [30, 187], [126, 1], [54, 226], [11, 98]], ![[41, 245, 139, 174], [214, 223], [214, 221], [250, 168], [27, 59], [204, 59], [111, 60], [80, 98]]]
 h' := ![![[224, 211, 163], [31, 158, 43], [78, 85, 249], [99, 26, 234], [155, 172, 31], [226, 112, 98], [156, 213, 108], [0, 0, 1], [0, 1]], ![[194, 45, 94], [173, 211, 190], [12, 239, 131], [16, 99, 119], [217, 8, 133], [178, 113, 50], [226, 111, 1], [11, 156, 45], [224, 211, 163]], ![[0, 1], [183, 145, 24], [248, 190, 134], [114, 132, 161], [131, 77, 93], [83, 32, 109], [172, 190, 148], [241, 101, 211], [194, 45, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [232, 110], []]
 b := ![[], [136, 24, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [98, 113, 96, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![171102626, 47305030, 164485230, -137830970, -357543188]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82991682, 418664482, 143191938, -137830970, -357543188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![401, 258, 337, -241, -642]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![401, 258, 337, -241, -642]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![184, 73, 1, 0, 0], ![223, 255, 0, 1, 0], ![206, 208, 0, 0, 1]] where
  M :=![![![401, 258, 337, -241, -642], ![972, 578, 831, -618, -1628], ![2712, 1411, 2340, -1834, -4760], ![3966, 1691, 3475, -2895, -7390], ![294, 279, 235, -126, -369]]]
  hmulB := by decide  
  f := ![![![-53, 6, -283, 161, 492]], ![![108, -166, 633, -334, -932]], ![![-4, -41, -23, 20, 84]], ![![47, -159, 363, -180, -458]], ![![52, -129, 293, -146, -377]]]
  g := ![![![484, 664, 337, -241, -642], ![1250, 1697, 831, -618, -1628], ![3742, 5013, 2340, -1834, -4760], ![5963, 7873, 3475, -2895, -7390], ![238, 358, 235, -126, -369]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [174, 216, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 256], [0, 1]]
 g := ![![[81, 137], [168], [173], [21], [139], [34], [139], [1]], ![[44, 120], [168], [173], [21], [139], [34], [139], [1]]]
 h' := ![![[41, 256], [133, 213], [239, 164], [23, 179], [183, 147], [168, 216], [179, 169], [83, 41], [0, 1]], ![[0, 1], [128, 44], [24, 93], [166, 78], [42, 110], [29, 41], [169, 88], [222, 216], [41, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [11, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [174, 216, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-336483, 156830, -890703, 555580, 1370030]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-943843, -1406463, -890703, 555580, 1370030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-53, 6, -283, 161, 492]] ![![401, 258, 337, -241, -642]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-187, -129, -163, 114, 306]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-187, -129, -163, 114, 306]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![255, 68, 1, 0, 0], ![9, 183, 0, 1, 0], ![180, 106, 0, 0, 1]] where
  M :=![![![-187, -129, -163, 114, 306], ![-432, -272, -363, 262, 696], ![-1080, -623, -926, 698, 1832], ![-1356, -649, -1179, 951, 2448], ![-192, -157, -161, 100, 279]]]
  hmulB := by decide  
  f := ![![![91, -25, 87, -50, -170]], ![![-240, 108, -495, 274, 840]], ![![27, 2, -39, 20, 46]], ![![-159, 76, -339, 187, 570]], ![![-36, 25, -139, 76, 223]]]
  g := ![![![-56, -161, -163, 114, 306], ![-135, -370, -363, 262, 696], ![-384, -987, -926, 698, 1832], ![-570, -1346, -1179, 951, 2448], ![-39, -141, -161, 100, 279]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [195, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [241, 262], [0, 1]]
 g := ![![[224, 26], [244, 11], [34, 258], [96], [33], [244], [221], [1]], ![[178, 237], [2, 252], [144, 5], [96], [33], [244], [221], [1]]]
 h' := ![![[241, 262], [23, 246], [208, 96], [55, 28], [188, 126], [92, 159], [190, 36], [68, 241], [0, 1]], ![[0, 1], [134, 17], [200, 167], [228, 235], [46, 137], [13, 104], [187, 227], [26, 22], [241, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [176, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [195, 22, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15819, -5795, -12949, 12085, 30193]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8583, -17252, -12949, 12085, 30193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 4, -6, 4, 12]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-13, 4, -6, 4, 12]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![59, 164, 1, 0, 0], ![159, 258, 0, 1, 0], ![85, 84, 0, 0, 1]] where
  M :=![![![-13, 4, -6, 4, 12], ![0, -15, 16, -4, -16], ![-48, 8, -91, 64, 144], ![-288, -54, -292, 215, 648], ![72, 20, 62, -44, -161]]]
  hmulB := by decide  
  f := ![![![1117, 804, 958, -652, -1764]], ![![2304, 1615, 1920, -1308, -3536]], ![![1705, 1200, 1427, -972, -2628]], ![![2949, 2080, 2474, -1685, -4556]], ![![1103, 780, 928, -632, -1709]]]
  g := ![![![-5, -4, -6, 4, 12], ![4, -1, 16, -4, -16], ![-65, -52, -91, 64, 144], ![-275, -236, -292, 215, 648], ![65, 56, 62, -44, -161]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [204, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 262], [0, 1]]
 g := ![![[122, 156], [156, 96], [145, 69], [36], [206], [24], [204], [1]], ![[0, 107], [0, 167], [0, 194], [36], [206], [24], [204], [1]]]
 h' := ![![[97, 262], [262, 141], [139, 126], [20, 73], [0, 6], [101, 224], [0, 200], [59, 97], [0, 1]], ![[0, 1], [0, 122], [0, 137], [0, 190], [56, 257], [0, 39], [201, 63], [0, 166], [97, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208]]
 b := ![[], [216, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [204, 166, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-751605, -249672, -629127, 581268, 1451612]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-682288, -642492, -629127, 581268, 1451612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -1, -3, 2, 6]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![-7, -1, -3, 2, 6]] 
 ![![263, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![91, 0, 1, 0, 0], ![152, 0, 0, 1, 0], ![218, 0, 0, 0, 1]] where
  M :=![![![-7, -1, -3, 2, 6], ![0, -8, 5, -2, -8], ![-24, 1, -46, 26, 72], ![-36, -21, -11, 11, 48], ![0, 7, -17, 8, 15]]]
  hmulB := by decide  
  f := ![![![-545, -153, -425, 382, 954]], ![![-73, -21, -58, 52, 130]], ![![-229, -66, -183, 164, 410]], ![![-404, -117, -325, 291, 728]], ![![-446, -125, -347, 312, 779]]]
  g := ![![![-5, -1, -3, 2, 6], ![7, -8, 5, -2, -8], ![-59, 1, -46, 26, 72], ![-40, -21, -11, 11, 48], ![-12, 7, -17, 8, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-187, -129, -163, 114, 306]] ![![-13, 4, -6, 4, 12]]
  ![![-545, -153, -425, 382, 954]] where
 M := ![![![-545, -153, -425, 382, 954]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![-545, -153, -425, 382, 954]] ![![-7, -1, -3, 2, 6]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2923, 931, 2578, -2291, -5752]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![2923, 931, 2578, -2291, -5752]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![4, 246, 159, 1, 0], ![230, 22, 254, 0, 1]] where
  M :=![![![2923, 931, 2578, -2291, -5752], ![13452, 4331, 11994, -10636, -26708], ![62400, 20010, 55623, -49284, -123856], ![137250, 44202, 122050, -108323, -272014], ![-8874, -2912, -7818, 6986, 17491]]]
  hmulB := by decide  
  f := ![![![7037, 4957, 5886, -4013, -10846]], ![![14316, 10103, 12006, -8184, -22124]], ![![29136, 20566, 24399, -16636, -44960]], ![![30502, 21528, 25559, -17425, -47098]], ![![34736, 24510, 29084, -19830, -53593]]]
  g := ![![![4963, 2569, 6795, -2291, -5752], ![23044, 11927, 31550, -10636, -26708], ![106864, 55274, 146287, -49284, -123856], ![234698, 121472, 321327, -108323, -272014], ![-15092, -7830, -20674, 6986, 17491]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [70, 71, 120, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 238, 120], [124, 30, 149], [0, 1]]
 g := ![![[211, 167, 80], [167, 169], [179, 206, 87], [253, 62, 212], [187, 216], [230, 73], [149, 1], []], ![[139, 241, 258, 224], [190, 100], [17, 217, 9, 253], [173, 253, 8, 218], [161, 228], [158, 89], [76, 93], [148, 143]], ![[145, 44, 267, 25], [85, 9], [171, 230, 152, 61], [250, 156, 14, 119], [262, 20], [90, 79], [268, 154], [119, 143]]]
 h' := ![![[25, 238, 120], [3, 21, 34], [113, 93, 256], [44, 30, 25], [116, 11, 181], [264, 172, 158], [61, 111, 72], [0, 0, 1], [0, 1]], ![[124, 30, 149], [139, 85, 43], [142, 206, 10], [57, 165, 46], [37, 1, 25], [3, 82, 94], [240, 143, 147], [218, 259, 30], [25, 238, 120]], ![[0, 1], [71, 163, 192], [209, 239, 3], [222, 74, 198], [132, 257, 63], [218, 15, 17], [84, 15, 50], [52, 10, 238], [124, 30, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [189, 71], []]
 b := ![[], [181, 174, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [70, 71, 120, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1524791416, 419618286, 1405637044, -1157583470, -3167787762]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2731398924, 1319243430, 3680592938, -1157583470, -3167787762]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7037, 4957, 5886, -4013, -10846]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![7037, 4957, 5886, -4013, -10846]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![12, 220, 1, 0, 0], ![25, 151, 0, 1, 0], ![211, 165, 0, 0, 1]] where
  M :=![![![7037, 4957, 5886, -4013, -10846], ![14316, 10103, 12006, -8184, -22124], ![29136, 20566, 24399, -16636, -44960], ![22530, 15872, 18910, -12885, -34834], ![9978, 7050, 8338, -5688, -15369]]]
  hmulB := by decide  
  f := ![![![2923, 931, 2578, -2291, -5752]], ![![13452, 4331, 11994, -10636, -26708]], ![![11364, 3658, 10131, -8984, -22560]], ![![8333, 2682, 7426, -6586, -16538]], ![![10511, 3376, 9350, -8295, -20829]]]
  g := ![![![8644, 4110, 5886, -4013, -10846], ![17632, 8383, 12006, -8184, -22124], ![35832, 17038, 24399, -16636, -44960], ![27761, 13193, 18910, -12885, -34834], ![12249, 5827, 8338, -5688, -15369]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [89, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 268], [0, 1]]
 g := ![![[222, 133], [218], [25, 127], [251, 118], [222], [211], [115], [1]], ![[0, 136], [218], [260, 142], [230, 151], [222], [211], [115], [1]]]
 h' := ![![[148, 268], [184, 86], [196, 73], [257, 76], [64, 103], [202, 130], [107, 91], [180, 148], [0, 1]], ![[0, 1], [0, 183], [240, 196], [207, 193], [244, 166], [74, 139], [125, 178], [26, 121], [148, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [192]]
 b := ![[], [159, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [89, 121, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![58067, 31538, 1544, -8942, -72542]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![57879, 48370, 1544, -8942, -72542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![2923, 931, 2578, -2291, -5752]] ![![7037, 4957, 5886, -4013, -10846]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![269, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36299, -25465, -30212, 20609, 55686]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![-36299, -25465, -30212, 20609, 55686]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![218, 45, 265, 1, 0], ![235, 128, 72, 0, 1]] where
  M :=![![![-36299, -25465, -30212, 20609, 55686], ![-73692, -52043, -61894, 42204, 114076], ![-150432, -105918, -126007, 85980, 232336], ![-116778, -82010, -97874, 66891, 180666], ![-51378, -36202, -42948, 29272, 79123]]]
  hmulB := by decide  
  f := ![![![145, -161, 544, -287, -812]], ![![588, 451, -238, 24, -420]], ![![-5904, -118, -7349, 4492, 15648]], ![![-5512, -183, -6699, 4115, 14418]], ![![-1193, 47, -1640, 983, 3343]]]
  g := ![![![-65001, -29818, -35059, 20609, 55686], ![-133144, -61081, -71806, 42204, 114076], ![-271192, -124406, -146269, 85980, 232336], ![-210906, -96743, -113771, 66891, 180666], ![-92349, -42366, -49804, 29272, 79123]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [252, 233, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 162, 121], [131, 108, 150], [0, 1]]
 g := ![![[205, 168, 2], [32, 3, 16], [193, 185, 31], [5, 87, 36], [145, 129], [104, 153], [232, 1], []], ![[212, 158, 216, 36], [215, 191, 82, 176], [267, 118, 205, 77], [233, 117, 211, 57], [151, 164], [236, 170], [69, 11], [178, 7]], ![[19, 35, 96, 199], [35, 156, 201, 251], [76, 236, 191, 38], [199, 42, 236, 71], [15, 259], [202, 219], [117, 228], [149, 7]]]
 h' := ![![[101, 162, 121], [66, 58, 175], [144, 91, 267], [95, 222, 207], [33, 192, 6], [114, 250, 251], [72, 163, 204], [0, 0, 1], [0, 1]], ![[131, 108, 150], [46, 51, 173], [260, 159, 10], [80, 195, 167], [111, 269, 32], [43, 105, 177], [232, 228, 21], [33, 55, 108], [101, 162, 121]], ![[0, 1], [66, 162, 194], [118, 21, 265], [83, 125, 168], [152, 81, 233], [229, 187, 114], [105, 151, 46], [209, 216, 162], [131, 108, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 264], []]
 b := ![[], [263, 253, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [252, 233, 39, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1249552635, -409540492, -1095728928, 980362256, 2457664964]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2924427273, -1325117924, -1615659056, 980362256, 2457664964]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, -161, 544, -287, -812]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![145, -161, 544, -287, -812]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![40, 12, 1, 0, 0], ![31, 84, 0, 1, 0], ![19, 75, 0, 0, 1]] where
  M :=![![![145, -161, 544, -287, -812], ![588, 451, -238, 24, -420], ![-5904, -118, -7349, 4492, 15648], ![12738, -3520, 24174, -13729, -43526], ![-7554, 1340, -12688, 7342, 23877]]]
  hmulB := by decide  
  f := ![![![-36299, -25465, -30212, 20609, 55686]], ![![-73692, -52043, -61894, 42204, 114076]], ![![-9176, -6454, -7665, 5228, 14128]], ![![-27425, -19347, -23002, 15686, 42396]], ![![-23129, -16322, -19406, 13233, 35767]]]
  g := ![![![10, 289, 544, -287, -812], ![64, 121, -238, 24, -420], ![-548, -5398, -7349, 4492, 15648], ![1101, 15218, 24174, -13729, -43526], ![-669, -8317, -12688, 7342, 23877]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [225, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [171, 270], [0, 1]]
 g := ![![[151, 53], [8, 141], [136, 229], [237, 220], [242], [16], [244], [1]], ![[0, 218], [0, 130], [0, 42], [188, 51], [242], [16], [244], [1]]]
 h' := ![![[171, 270], [97, 253], [23, 236], [62, 212], [28, 189], [121, 243], [61, 4], [46, 171], [0, 1]], ![[0, 1], [0, 18], [0, 35], [0, 59], [98, 82], [211, 28], [203, 267], [19, 100], [171, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [233]]
 b := ![[], [134, 252]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [225, 100, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2054, 2818, -4999, 2192, 3376]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![258, -1382, -4999, 2192, 3376]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![-36299, -25465, -30212, 20609, 55686]] ![![145, -161, 544, -287, -812]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2657, 1846, 3449, -2089, -6126]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-2657, 1846, 3449, -2089, -6126]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![100, 190, 1, 0, 0], ![195, 144, 0, 1, 0], ![53, 148, 0, 0, 1]] where
  M :=![![![-2657, 1846, 3449, -2089, -6126], ![1692, -1156, -2165, 1310, 3844], ![-1032, 751, 1398, -850, -2488], ![-474, 367, 679, -417, -1214], ![-1338, 935, 1747, -1058, -3103]]]
  hmulB := by decide  
  f := ![![![-23, 10, -31, 17, 76]], ![![300, -12, 461, -278, -868]], ![![196, -3, 300, -182, -560]], ![![141, -1, 224, -136, -406]], ![![155, -3, 236, -143, -443]]]
  g := ![![![1388, 2000, 3449, -2089, -6126], ![-870, -1254, -2165, 1310, 3844], ![566, 815, 1398, -850, -2488], ![279, 401, 679, -417, -1214], ![703, 1013, 1747, -1058, -3103]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 2 2 8 [266, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [180, 276], [0, 1]]
 g := ![![[243, 254], [256], [73, 194], [116], [252, 165], [141], [268], [1]], ![[258, 23], [256], [91, 83], [116], [36, 112], [141], [268], [1]]]
 h' := ![![[180, 276], [276, 163], [249, 261], [172, 191], [2, 160], [96, 89], [22, 124], [11, 180], [0, 1]], ![[0, 1], [254, 114], [139, 16], [204, 86], [271, 117], [50, 188], [182, 153], [2, 97], [180, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [174]]
 b := ![[], [203, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 2
  hpos := by decide
  P := [266, 97, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-152500, -59543, -117082, 117731, 276180]
  a := ![-165, -7, -203, 151, 422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-94005, -128671, -117082, 117731, 276180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -17, -38, 27, 74]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![7, -17, -38, 27, 74]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![140, 175, 1, 0, 0], ![215, 270, 0, 1, 0], ![16, 197, 0, 0, 1]] where
  M :=![![![7, -17, -38, 27, 74], ![-84, -11, -48, 48, 116], ![-336, -112, -315, 280, 704], ![-774, -248, -700, 621, 1558], ![66, 12, 38, -36, -87]]]
  hmulB := by decide  
  f := ![![![49, 5, 66, -39, -116]], ![![12, 77, -96, 44, 124]], ![![32, 51, -27, 8, 20]], ![![53, 79, -38, 10, 22]], ![![10, 55, -66, 30, 85]]]
  g := ![![![-6, -55, -38, 27, 74], ![-20, -99, -48, 48, 116], ![-100, -575, -315, 280, 704], ![-221, -1272, -700, 621, 1558], ![14, 73, 38, -36, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [35, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 276], [0, 1]]
 g := ![![[3, 41], [41], [176, 157], [34], [134, 131], [156], [222], [1]], ![[130, 236], [41], [34, 120], [34], [229, 146], [156], [222], [1]]]
 h' := ![![[172, 276], [151, 128], [211, 128], [2, 218], [19, 158], [163, 193], [103, 106], [242, 172], [0, 1]], ![[0, 1], [7, 149], [67, 149], [103, 59], [49, 119], [119, 84], [53, 171], [187, 105], [172, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [171, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : CertifiedPrimeIdeal' SI277N1 277 where
  n := 2
  hpos := by decide
  P := [35, 105, 1]
  hirr := P277P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169581, -82463, -111297, 132266, 270848]
  a := ![-241, -13, -298, 214, 616]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-62667, -251532, -111297, 132266, 270848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N1 B_one_repr
lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N1

def I277N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, 12, 11, 3, -4]] i)))

def SI277N2: IdealEqSpanCertificate' Table ![![-73, 12, 11, 3, -4]] 
 ![![277, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![147, 0, 0, 0, 1]] where
  M :=![![![-73, 12, 11, 3, -4], ![-156, -72, -187, 158, 404], ![-840, -255, -718, 642, 1608], ![-1830, -581, -1615, 1435, 3602], ![102, 51, 129, -108, -277]]]
  hmulB := by decide  
  f := ![![![353, 180, 235, -171, -602]], ![![237, 124, 154, -113, -398]], ![![36, 3, 50, -30, -96]], ![![12, 29, -35, 15, 34]], ![![201, 87, 162, -111, -379]]]
  g := ![![![-7, 12, 11, 3, -4], ![-168, -72, -187, 158, 404], ![-693, -255, -718, 642, 1608], ![-1545, -581, -1615, 1435, 3602], ![114, 51, 129, -108, -277]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N2 : Nat.card (O ⧸ I277N2) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N2)

lemma isPrimeI277N2 : Ideal.IsPrime I277N2 := prime_ideal_of_norm_prime hp277.out _ NI277N2
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-2657, 1846, 3449, -2089, -6126]] ![![7, -17, -38, 27, 74]]
  ![![-119957, 83135, 155435, -94144, -276086]] where
 M := ![![![-119957, 83135, 155435, -94144, -276086]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI277N1 : IdealMulLeCertificate' Table 
  ![![-119957, 83135, 155435, -94144, -276086]] ![![-73, 12, 11, 3, -4]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![9345149, -6443851, -12040636, 7285377, 21374982]]]
 hmul := by decide  
 g := ![![![![33737, -23263, -43468, 26301, 77166]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1447, 993, 1858, -1123, -3296]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-1447, 993, 1858, -1123, -3296]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![143, 222, 63, 1, 0], ![90, 73, 190, 0, 1]] where
  M :=![![![-1447, 993, 1858, -1123, -3296], ![876, -639, -1208, 740, 2156], ![-768, 344, 557, -296, -912], ![-582, 54, 140, 11, -102], ![-738, 518, 902, -554, -1607]]]
  hmulB := by decide  
  f := ![![![-341, -241, -286, 195, 526]], ![![-708, -491, -600, 408, 1108]], ![![-1392, -1016, -1123, 776, 2080]], ![![-1049, -741, -875, 598, 1616]], ![![-1236, -893, -1008, 694, 1865]]]
  g := ![![![1622, 1747, 2487, -1123, -3296], ![-1064, -1147, -1628, 740, 2156], ![440, 472, 685, -296, -912], ![25, 18, 67, 11, -102], ![794, 857, 1214, -554, -1607]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [153, 17, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 223, 148], [38, 57, 133], [0, 1]]
 g := ![![[168, 137, 238], [48, 25], [5, 202], [200, 189, 272], [76, 179, 218], [265, 256], [186, 1], []], ![[98, 116, 209, 23], [120, 10], [135, 172], [153, 226, 98, 91], [68, 8, 189, 235], [158, 5], [28, 158], [179, 267]], ![[94, 26, 76, 198], [196, 123], [262, 29], [158, 25, 215, 174], [111, 48, 78, 216], [52, 132], [173, 273], [194, 267]]]
 h' := ![![[148, 223, 148], [118, 5, 111], [76, 123, 276], [29, 207, 157], [174, 263, 159], [228, 96, 201], [204, 57, 16], [0, 0, 1], [0, 1]], ![[38, 57, 133], [48, 110, 42], [173, 35, 216], [189, 220, 245], [185, 174, 217], [104, 108, 94], [154, 111, 75], [137, 196, 57], [148, 223, 148]], ![[0, 1], [164, 166, 128], [101, 123, 70], [279, 135, 160], [28, 125, 186], [23, 77, 267], [162, 113, 190], [143, 85, 223], [38, 57, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 255], []]
 b := ![[], [150, 193, 247], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [153, 17, 95, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-198063676, -62081493, -179273139, 157696003, 396647271]
  a := ![-127, -3, -157, 121, 325]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-207995895, -227849982, -304188978, 157696003, 396647271]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1079, -767, -913, 622, 1682]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-1079, -767, -913, 622, 1682]] 
 ![![281, 0, 0, 0, 0], ![167, 1, 0, 0, 0], ![211, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![257, 0, 0, 0, 1]] where
  M :=![![![-1079, -767, -913, 622, 1682], ![-2208, -1554, -1845, 1258, 3400], ![-4488, -3169, -3764, 2566, 6936], ![-3468, -2447, -2909, 1983, 5360], ![-1536, -1087, -1291, 880, 2379]]]
  hmulB := by decide  
  f := ![![![-79, -109, 35, 30, 42]], ![![-49, -65, 18, 20, 30]], ![![-77, -86, 9, 36, 70]], ![![-11, -12, 4, 5, 2]], ![![-79, -98, 20, 34, 61]]]
  g := ![![![-403, -767, -913, 622, 1682], ![-813, -1554, -1845, 1258, 3400], ![-1659, -3169, -3764, 2566, 6936], ![-1283, -2447, -2909, 1983, 5360], ![-569, -1087, -1291, 880, 2379]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 2, -13, 7, 24]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![-7, 2, -13, 7, 24]] 
 ![![281, 0, 0, 0, 0], ![269, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![266, 0, 0, 1, 0], ![91, 0, 0, 0, 1]] where
  M :=![![![-7, 2, -13, 7, 24], ![36, -10, 71, -42, -124], ![24, 67, -104, 38, 104], ![-78, -21, -25, 5, 146], ![54, 41, -23, 4, -39]]]
  hmulB := by decide  
  f := ![![![12715, -9458, -17457, 10601, 31030]], ![![12139, -9036, -16676, 10127, 29642]], ![![6211, -4629, -8541, 5187, 15182]], ![![12040, -8963, -16541, 10045, 29402]], ![![4139, -3081, -5686, 3453, 10107]]]
  g := ![![![-10, 2, -13, 7, 24], ![55, -10, 71, -42, -124], ![-83, 67, -104, 38, 104], ![-20, -21, -25, 5, 146], ![-19, 41, -23, 4, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-1447, 993, 1858, -1123, -3296]] ![![-1079, -767, -913, 622, 1682]]
  ![![-12715, 9458, 17457, -10601, -31030]] where
 M := ![![![-12715, 9458, 17457, -10601, -31030]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-12715, 9458, 17457, -10601, -31030]] ![![-7, 2, -13, 7, 24]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17161, 11369, 13255, -9088, -24470]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![17161, 11369, 13255, -9088, -24470]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![257, 146, 80, 1, 0], ![140, 65, 71, 0, 1]] where
  M :=![![![17161, 11369, 13255, -9088, -24470], ![33528, 24122, 28809, -19606, -53056], ![69144, 48493, 57496, -39214, -105960], ![53328, 37493, 44477, -30325, -81956], ![23892, 16483, 19453, -13288, -35869]]]
  hmulB := by decide  
  f := ![![![91, 1, 113, -68, -242]], ![![-456, 98, -811, 470, 1488]], ![![936, -719, 2756, -1462, -4376]], ![![113, -148, 456, -229, -682]], ![![176, -160, 568, -296, -885]]]
  g := ![![![20419, 10349, 8755, -9088, -24470], ![44170, 22386, 18955, -19606, -53056], ![88274, 44739, 37872, -39214, -105960], ![68271, 34601, 29291, -30325, -81956], ![29896, 15152, 12824, -13288, -35869]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [108, 118, 258, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [267, 260, 193], [41, 22, 90], [0, 1]]
 g := ![![[84, 281, 235], [16, 226, 143], [239, 278], [262, 227, 215], [61, 29, 60], [163, 85], [25, 1], []], ![[234, 251, 199, 39], [266, 28, 197, 69], [263, 90], [227, 8, 226, 82], [183, 277, 90, 31], [50, 201], [160, 201], [50, 176]], ![[35, 239, 148, 252], [77, 281, 108, 281], [240, 216], [14, 265, 96, 42], [54, 149, 19, 106], [199, 52], [202, 246], [153, 176]]]
 h' := ![![[267, 260, 193], [253, 174, 210], [240, 197, 133], [4, 51, 109], [204, 224, 82], [145, 36, 125], [130, 55, 224], [0, 0, 1], [0, 1]], ![[41, 22, 90], [270, 11, 280], [60, 1, 195], [247, 224, 72], [161, 253, 39], [111, 112, 76], [219, 261, 261], [233, 166, 22], [267, 260, 193]], ![[0, 1], [244, 98, 76], [199, 85, 238], [138, 8, 102], [106, 89, 162], [179, 135, 82], [256, 250, 81], [156, 117, 260], [41, 22, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99, 224], []]
 b := ![[], [226, 99, 166], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [108, 118, 258, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5524885, -7217533, 23160792, -12104691, -33679228]
  a := ![-85, -9, -108, 65, 218]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27673224, 13954831, 11953220, -12104691, -33679228]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![91, 1, 113, -68, -242]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![91, 1, 113, -68, -242]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![107, 123, 1, 0, 0], ![70, 272, 0, 1, 0], ![65, 264, 0, 0, 1]] where
  M :=![![![91, 1, 113, -68, -242], ![-456, 98, -811, 470, 1488], ![936, -719, 2756, -1462, -4376], ![288, 1071, -2067, 1009, 2020], ![252, -741, 1963, -996, -2599]]]
  hmulB := by decide  
  f := ![![![17161, 11369, 13255, -9088, -24470]], ![![33528, 24122, 28809, -19606, -53056]], ![![21305, 14954, 17736, -12096, -32686]], ![![36658, 26129, 31125, -21199, -57336]], ![![35303, 25172, 29988, -20424, -55241]]]
  g := ![![![30, 242, 113, -68, -242], ![-153, -1487, -811, 470, 1488], ![328, 4287, 2756, -1462, -4376], ![69, -1952, -2067, 1009, 2020], ![102, 2526, 1963, -996, -2599]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [197, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [264, 282], [0, 1]]
 g := ![![[240, 157], [97, 275], [96], [2, 164], [158, 179], [42], [78], [1]], ![[87, 126], [249, 8], [96], [282, 119], [153, 104], [42], [78], [1]]]
 h' := ![![[264, 282], [135, 231], [201, 254], [172, 215], [4, 36], [68, 99], [237, 61], [86, 264], [0, 1]], ![[0, 1], [274, 52], [186, 29], [49, 68], [169, 247], [168, 184], [210, 222], [164, 19], [264, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [228]]
 b := ![[], [234, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [197, 19, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47989, -20186, -35092, 36136, 84226]
  a := ![92, 5, 113, -85, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15185, -98122, -35092, 36136, 84226]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![17161, 11369, 13255, -9088, -24470]] ![![91, 1, 113, -68, -242]]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, 0, 0, 0, 0]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![293, 0, 0, 0, 0]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![0, 0, 0, 0, 293]] where
  M :=![![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![0, 0, 0, 0, 293]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 5 2 8 [41, 137, 50, 196, 70, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 68, 174, 76, 249], [22, 124, 192, 68, 193], [195, 124, 129, 50, 212], [153, 269, 91, 99, 225], [0, 1]]
 g := ![![[268, 153, 42, 180, 257], [127, 175, 23, 87], [13, 250, 147, 89, 22], [245, 106, 110, 239], [194, 62, 69, 196], [141, 244, 16, 223, 1], [], []], ![[5, 149, 136, 262, 146, 44, 78, 89], [78, 99, 119, 121], [145, 118, 198, 188, 228, 86, 102, 85], [130, 102, 117, 77], [39, 13, 31, 40], [191, 285, 31, 189, 161, 25, 153, 165], [151, 43, 51, 216], [25, 290, 190, 178]], ![[263, 197, 88, 161, 161, 292, 124, 289], [143, 80, 195, 33], [262, 255, 216, 52, 29, 77, 20, 226], [216, 108, 61, 71], [276, 99, 124, 9], [42, 86, 53, 174, 212, 46, 27, 132], [274, 17, 220, 257], [238, 277, 148, 38]], ![[85, 143, 9, 44, 160, 129, 192, 167], [43, 243, 221, 83], [263, 13, 281, 51, 98, 167, 28, 153], [218, 110, 145, 276], [137, 118, 4, 83], [104, 209, 82, 152, 213, 36, 217, 269], [273, 142, 50, 178], [100, 188, 258, 115]], ![[266, 98, 40, 36, 201, 280, 107, 40], [134, 221, 272, 258], [21, 7, 208, 95, 244, 148, 207, 169], [41, 56, 289, 160], [41, 266, 47, 210], [139, 237, 204, 72, 254, 287, 42, 232], [213, 228, 109, 253], [85, 109, 99, 229]]]
 h' := ![![[146, 68, 174, 76, 249], [239, 253, 236, 247, 242], [53, 143, 96, 160, 183], [184, 211, 24, 239, 107], [45, 85, 82, 111, 192], [79, 272, 179, 104, 279], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[22, 124, 192, 68, 193], [194, 68, 28, 11, 177], [280, 5, 121, 129, 282], [102, 265, 76, 191, 75], [246, 290, 198, 151, 91], [110, 52, 22, 124, 178], [164, 37, 248, 194, 252], [74, 146, 216, 160, 41], [146, 68, 174, 76, 249]], ![[195, 124, 129, 50, 212], [56, 19, 237, 282, 117], [135, 215, 253, 194, 196], [189, 276, 155, 246, 181], [264, 25, 44, 249, 86], [118, 108, 15, 28, 3], [49, 50, 109, 94, 216], [102, 169, 137, 213, 51], [22, 124, 192, 68, 193]], ![[153, 269, 91, 99, 225], [147, 88, 18, 286, 140], [200, 264, 107, 42, 159], [63, 42, 254, 63, 144], [176, 196, 58, 28, 154], [149, 14, 272, 256, 159], [101, 59, 259, 67, 107], [230, 289, 33, 11, 249], [195, 124, 129, 50, 212]], ![[0, 1], [89, 158, 67, 53, 203], [289, 252, 9, 61, 59], [145, 85, 77, 140, 79], [274, 283, 204, 47, 63], [37, 140, 98, 74, 260], [57, 147, 263, 231, 10], [0, 275, 199, 202, 245], [153, 269, 91, 99, 225]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [288, 183, 100, 19], [], [], []]
 b := ![[], [174, 34, 183, 276, 87], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 5
  hpos := by decide
  P := [41, 137, 50, 196, 70, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3236708591527693, -1041150434027265, -2880776677824735, 2555524216522380, 6418162093891220]
  a := ![-183, -2, -226, 179, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11046787001801, -3553414450605, -9832002313395, 8721925653660, 21904990081540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 2159424884693 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def PBC293 : ContainsPrimesAboveP 293 ![I293N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![293, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 293 (by decide) 𝕀

instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-337, 223, 412, -247, -728]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-337, 223, 412, -247, -728]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![179, 304, 1, 0, 0], ![115, 239, 0, 1, 0], ![56, 148, 0, 0, 1]] where
  M :=![![![-337, 223, 412, -247, -728], ![156, -159, -310, 200, 572], ![-336, 18, -7, 60, 96], ![-582, -104, -418, 373, 938], ![-114, 120, 276, -174, -505]]]
  hmulB := by decide  
  f := ![![![8399, 5927, 7040, -4799, -12970]], ![![17124, 12067, 14362, -9788, -26468]], ![![21967, 15485, 18421, -12555, -33946]], ![![16565, 11676, 13892, -9468, -25600]], ![![9826, 6926, 8240, -5616, -15185]]]
  g := ![![![-16, 136, 412, -247, -728], ![2, -125, -310, 200, 572], ![-37, -86, -7, 60, 96], ![-69, -329, -418, 373, 938], ![-4, 106, 276, -174, -505]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [22, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [218, 306], [0, 1]]
 g := ![![[18, 49], [226, 294], [305], [119], [163, 134], [141, 112], [246], [1]], ![[262, 258], [155, 13], [305], [119], [210, 173], [304, 195], [246], [1]]]
 h' := ![![[218, 306], [247, 7], [143, 249], [232, 108], [98, 147], [275, 286], [291, 135], [285, 218], [0, 1]], ![[0, 1], [238, 300], [86, 58], [137, 199], [216, 160], [302, 21], [249, 172], [224, 89], [218, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [272]]
 b := ![[], [219, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 2
  hpos := by decide
  P := [22, 89, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-254348, -237481, -48718, 221757, 161304]
  a := ![519, 35, 641, -451, -1326]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-84915, -202932, -48718, 221757, 161304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![133, 115, -82, 19, -62]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![133, 115, -82, 19, -62]] 
 ![![307, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![282, 0, 0, 1, 0], ![276, 0, 0, 0, 1]] where
  M :=![![![133, 115, -82, 19, -62], ![-1428, -49, -1732, 1064, 3732], ![6480, -1556, 11783, -6736, -21536], ![-7254, 5124, -20640, 11155, 32854], ![5634, -2688, 13186, -7284, -22177]]]
  hmulB := by decide  
  f := ![![![-71939, 77627, 135562, -83365, -241880]], ![![-11864, 13111, 22828, -14048, -40740]], ![![-13675, 15191, 26433, -16269, -47176]], ![![-65928, 71492, 124772, -76741, -222638]], ![![-64734, 69958, 122146, -75118, -217945]]]
  g := ![![![35, 115, -82, 19, -62], ![-3996, -49, -1732, 1064, 3732], ![23569, -1556, 11783, -6736, -21536], ![-36708, 5124, -20640, 11155, 32854], ![24568, -2688, 13186, -7284, -22177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 6, -7, 3, 6]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![-1, 6, -7, 3, 6]] 
 ![![307, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![213, 0, 0, 1, 0], ![136, 0, 0, 0, 1]] where
  M :=![![![-1, 6, -7, 3, 6], ![-36, -8, -33, 22, 84], ![216, -29, 346, -202, -664], ![-330, 155, -765, 423, 1290], ![222, -73, 451, -254, -795]]]
  hmulB := by decide  
  f := ![![![-1009, -98, -849, 851, 2072]], ![![-216, -24, -183, 182, 444]], ![![-372, -55, -318, 310, 760]], ![![-921, -137, -786, 766, 1878]], ![![-430, -37, -361, 364, 885]]]
  g := ![![![-4, 6, -7, 3, 6], ![-42, -8, -33, 22, 84], ![346, -29, 346, -202, -664], ![-687, 155, -765, 423, 1290], ![420, -73, 451, -254, -795]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2

def I307N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 10, -6, -20]] i)))

def SI307N3: IdealEqSpanCertificate' Table ![![7, 0, 10, -6, -20]] 
 ![![307, 0, 0, 0, 0], ![198, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![275, 0, 0, 0, 1]] where
  M :=![![![7, 0, 10, -6, -20], ![-24, 9, -50, 28, 88], ![48, -42, 157, -84, -240], ![84, 62, -26, -1, -68], ![-12, -42, 78, -36, -77]]]
  hmulB := by decide  
  f := ![![![-275, 528, 914, -582, -1660]], ![![-174, 341, 590, -376, -1072]], ![![-76, 162, 281, -180, -512]], ![![9, 10, 20, -15, -40]], ![![-247, 474, 820, -522, -1489]]]
  g := ![![![15, 0, 10, -6, -20], ![-70, 9, -50, 28, 88], ![196, -42, 157, -84, -240], ![29, 62, -26, -1, -68], ![73, -42, 78, -36, -77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N3 : Nat.card (O ⧸ I307N3) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N3)

lemma isPrimeI307N3 : Ideal.IsPrime I307N3 := prime_ideal_of_norm_prime hp307.out _ NI307N3
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-337, 223, 412, -247, -728]] ![![133, 115, -82, 19, -62]]
  ![![-3319, 482, -5334, 3104, 10216]] where
 M := ![![![-3319, 482, -5334, 3104, 10216]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![-3319, 482, -5334, 3104, 10216]] ![![-1, 6, -7, 3, 6]]
  ![![77455, -133732, 394619, -203757, -555210]] where
 M := ![![![77455, -133732, 394619, -203757, -555210]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N2 : IdealMulLeCertificate' Table 
  ![![77455, -133732, 394619, -203757, -555210]] ![![7, 0, 10, -6, -20]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![12240397, -7091700, 31407635, -17165905, -51419430]]]
 hmul := by decide  
 g := ![![![![39871, -23100, 102305, -55915, -167490]]]]
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


lemma PB696I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB696I6 : PrimesBelowBoundCertificateInterval O 251 307 696 where
  m := 9
  g := ![2, 3, 2, 2, 3, 3, 2, 1, 4]
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
    · exact ![I293N0]
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
    · exact ![19902511, 73441]
    · exact ![76729, 76729, 277]
    · exact ![22188041, 281, 281]
    · exact ![22665187, 80089]
    · exact ![2159424884693]
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
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
      exact NI307N3
  β := ![I263N2, I277N2, I281N1, I281N2, I307N1, I307N2, I307N3]
  Il := ![[], [I263N2], [], [], [I277N2], [I281N1, I281N2], [], [], [I307N1, I307N2, I307N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
