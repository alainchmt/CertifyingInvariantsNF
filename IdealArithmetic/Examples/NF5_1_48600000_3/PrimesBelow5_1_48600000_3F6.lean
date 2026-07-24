
import IdealArithmetic.Examples.NF5_1_48600000_3.RI5_1_48600000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 0, 0, 0, 0]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![257, 0, 0, 0, 0]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![0, 0, 0, 0, 257]] where
  M :=![![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![0, 0, 0, 0, 257]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 5 2 8 [167, 183, 138, 114, 21, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 246, 234, 55, 17], [213, 152, 7, 181, 193], [242, 63, 50, 40, 185], [167, 52, 223, 238, 119], [0, 1]]
 g := ![![[247, 73, 118, 90, 120], [218, 180, 239, 31], [256, 15, 42, 211], [151, 78, 173, 196], [228, 151, 195, 79], [15, 70, 236, 1], [], []], ![[250, 204, 115, 44, 229, 36, 158, 213], [133, 9, 146, 95], [10, 222, 210, 50], [3, 172, 180, 141], [46, 88, 205, 42], [83, 192, 184, 235], [13, 92, 176, 128], [161, 165, 170, 32]], ![[95, 136, 236, 165, 145, 9, 150, 50], [41, 3, 227, 244], [217, 7, 244, 81], [150, 141, 163, 200], [96, 142, 52, 118], [130, 93, 127, 129], [120, 169, 68, 122], [30, 189, 41, 241]], ![[95, 134, 204, 237, 90, 119, 109, 213], [203, 50, 191, 200], [240, 33, 94, 32], [151, 254, 116, 4], [14, 34, 183, 92], [168, 106, 48, 52], [148, 177, 44, 157], [141, 220, 255, 44]], ![[239, 65, 234, 43, 249, 75, 200, 106], [219, 120, 15, 120], [150, 224, 5, 44], [57, 199, 57, 122], [21, 106, 28, 195], [194, 204, 57, 197], [188, 194, 254, 46], [191, 129, 72, 26]]]
 h' := ![![[128, 246, 234, 55, 17], [29, 218, 131, 203, 190], [202, 77, 208, 213, 206], [158, 106, 11, 67, 89], [73, 200, 168, 113, 243], [65, 214, 192, 16, 74], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[213, 152, 7, 181, 193], [192, 87, 89, 218, 79], [72, 164, 222, 125, 98], [171, 251, 14, 75, 214], [186, 107, 37, 172, 107], [186, 117, 39, 27, 82], [13, 102, 15, 117, 135], [34, 47, 39, 230, 223], [128, 246, 234, 55, 17]], ![[242, 63, 50, 40, 185], [154, 118, 164, 31, 171], [233, 227, 60, 160, 191], [135, 256, 65, 208, 9], [16, 148, 232, 248, 86], [63, 133, 203, 11, 115], [106, 77, 27, 13, 30], [10, 200, 44, 183, 76], [213, 152, 7, 181, 193]], ![[167, 52, 223, 238, 119], [24, 49, 148, 23, 103], [256, 99, 108, 33, 86], [191, 57, 130, 83, 17], [215, 71, 33, 50, 2], [92, 203, 83, 121, 116], [69, 8, 134, 1, 56], [65, 74, 139, 0, 97], [242, 63, 50, 40, 185]], ![[0, 1], [204, 42, 239, 39, 228], [138, 204, 173, 240, 190], [60, 101, 37, 81, 185], [29, 245, 44, 188, 76], [127, 104, 254, 82, 127], [237, 70, 81, 126, 35], [104, 193, 34, 101, 118], [167, 52, 223, 238, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 163, 52, 145], [], [], []]
 b := ![[], [227, 101, 90, 162, 188], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 5
  hpos := by decide
  P := [167, 183, 138, 114, 21, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3350073547167, -7254036869258, 4188780997979, 13822327286849, -8693873350061]
  a := ![0, -1, -4, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13035305631, -28225824394, 16298758747, 53783374657, -33828300973]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 1121154893057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def PBC257 : ContainsPrimesAboveP 257 ![I257N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![257, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 257 (by decide) 𝕀

instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5002537, -15388520, -15014218, -1064812, -4341748]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-5002537, -15388520, -15014218, -1064812, -4341748]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![201, 189, 48, 257, 1]] where
  M :=![![![-5002537, -15388520, -15014218, -1064812, -4341748], ![-8683496, -26711277, -26060990, -1848324, -7536184], ![-15072368, -46364416, -45236083, -3208228, -13081156], ![-5544972, -17056866, -16641630, -1180273, -4812342], ![-6904876, -21240138, -20723138, -1469736, -5992615]]]
  hmulB := by decide  
  f := ![![![-15, -8, 18, 12, -28]], ![![-56, -155, 38, 180, 8]], ![![16, -16, -125, -332, 548]], ![![540, 1386, -282, -1271, -498]], ![![479, 1235, -256, -1161, -409]]]
  g := ![![![3299197, 3061604, 735322, 4238648, -4341748], ![5726576, 5314173, 1276334, 7357228, -7536184], ![9940076, 9224236, 2215435, 12770528, -13081156], ![3656790, 3393444, 815022, 4698067, -4812342], ![4553653, 4225719, 1014914, 5850313, -5992615]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 4 2 8 [254, 214, 113, 139, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 185, 98, 243], [232, 74, 248, 45], [93, 3, 180, 238], [0, 1]]
 g := ![![[153, 181, 246, 52], [146, 230, 84, 66], [130, 46, 125, 172], [99, 42, 176], [223, 137, 162], [25, 254, 122], [1], []], ![[128, 163, 86, 193, 182, 8], [136, 106, 113, 131, 144, 132], [68, 150, 2, 158, 226, 23], [164, 84, 39], [190, 8, 148], [191, 221, 233], [154, 25, 216], [225, 181, 137]], ![[203, 130, 88, 9, 250, 94], [86, 201, 37, 241, 82, 167], [47, 109, 24, 70, 169, 168], [231, 37, 100], [175, 169, 111], [244, 4, 206], [197, 18, 203], [256, 163, 184]], ![[228, 93, 78, 30, 137, 125], [27, 170, 181, 19, 232, 182], [13, 17, 258, 232, 24, 14], [196, 74, 44], [243, 231, 136], [259, 115, 124], [205, 229, 105], [175, 120, 99]]]
 h' := ![![[62, 185, 98, 243], [262, 4, 147, 29], [118, 14, 210, 131], [133, 246, 61, 31], [174, 192, 123, 121], [43, 185, 40, 201], [9, 49, 150, 124], [0, 0, 1], [0, 1]], ![[232, 74, 248, 45], [99, 258, 201, 90], [33, 161, 171, 109], [101, 81, 143, 46], [236, 98, 168, 61], [34, 111, 131, 197], [122, 190, 164, 93], [83, 89, 20, 74], [62, 185, 98, 243]], ![[93, 3, 180, 238], [40, 150, 243, 116], [175, 158, 229, 130], [43, 1, 100, 12], [130, 114, 184, 10], [50, 200, 146, 30], [241, 5, 260, 224], [109, 218, 8, 236], [232, 74, 248, 45]], ![[0, 1], [101, 114, 198, 28], [129, 193, 179, 156], [130, 198, 222, 174], [101, 122, 51, 71], [67, 30, 209, 98], [41, 19, 215, 85], [230, 219, 234, 216], [93, 3, 180, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [117, 28, 6], []]
 b := ![[], [], [229, 185, 86, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 4
  hpos := by decide
  P := [254, 214, 113, 139, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-244133757, -571294460, 211824193, 706618137, -161803385]
  a := ![3, -64, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![122731356, 114104735, 30336071, 160798814, -161803385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 4784350561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 8, -18, -12, 28]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![15, 8, -18, -12, 28]] 
 ![![263, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![237, 0, 1, 0, 0], ![234, 0, 0, 1, 0], ![145, 0, 0, 0, 1]] where
  M :=![![![15, 8, -18, -12, 28], ![56, 155, -38, -180, -8], ![-16, 16, 125, 332, -548], ![-540, -1386, 282, 1271, 498], ![-28, -274, -346, -808, 1769]]]
  hmulB := by decide  
  f := ![![![5002537, 15388520, 15014218, 1064812, 4341748]], ![![356375, 1096259, 1069592, 75856, 309300]], ![![4565299, 14043512, 13701923, 971744, 3962264]], ![![4472010, 13756542, 13421934, 951887, 3881298]], ![![2784307, 8564926, 8356596, 592652, 2416525]]]
  g := ![![![11, 8, -18, -12, 28], ![189, 155, -38, -180, -8], ![-107, 16, 125, 332, -548], ![-1572, -1386, 282, 1271, 498], ![73, -274, -346, -808, 1769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-5002537, -15388520, -15014218, -1064812, -4341748]] ![![15, 8, -18, -12, 28]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, -545, 278, -82, 105]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![43, -545, 278, -82, 105]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![185, 7, 259, 1, 0], ![191, 113, 105, 0, 1]] where
  M :=![![![43, -545, 278, -82, 105], ![210, 568, -372, 90, -141], ![-282, -495, 337, -78, 129], ![270, 429, -312, 67, -117], ![102, 181, -130, 26, -50]]]
  hmulB := by decide  
  f := ![![![-1, -5, -4, 2, -3]], ![![-6, -16, -6, 6, 3]], ![![6, 9, -25, -42, 21]], ![![5, 5, -27, -39, 18]], ![![-1, -7, -15, -12, 7]]]
  g := ![![![-18, -44, 39, -82, 105], ![39, 59, -33, 90, -141], ![-39, -54, 26, -78, 129], ![38, 49, -20, 67, -117], ![18, 21, -6, 26, -50]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [59, 8, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 210, 266], [166, 58, 3], [0, 1]]
 g := ![![[82, 265, 148], [233, 87], [73, 120, 204], [264, 123, 249], [133, 52], [126, 45], [170, 1], []], ![[133, 66, 121, 162], [234, 65], [252, 237, 113, 129], [11, 12, 125, 77], [138, 9], [22, 212], [263, 136], [1, 9]], ![[102, 190, 237, 116], [191, 115], [13, 89, 100, 266], [47, 221, 81, 201], [29, 203], [227, 73], [108, 253], [264, 9]]]
 h' := ![![[4, 210, 266], [250, 230, 95], [266, 6, 244], [26, 47, 136], [268, 143, 49], [109, 201, 66], [192, 195, 109], [0, 0, 1], [0, 1]], ![[166, 58, 3], [44, 137, 247], [20, 173, 146], [15, 149, 215], [78, 128, 261], [227, 232, 266], [51, 153, 88], [226, 65, 58], [4, 210, 266]], ![[0, 1], [193, 171, 196], [83, 90, 148], [243, 73, 187], [127, 267, 228], [208, 105, 206], [107, 190, 72], [144, 204, 210], [166, 58, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [230, 23], []]
 b := ![[], [172, 234, 187], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [59, 8, 99, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-162661, -271893, 352662, 1018830, -1104507]
  a := ![1, -3, -2, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![82954, 436452, -548517, 1018830, -1104507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 5, 4, -2, 3]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![1, 5, 4, -2, 3]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![173, 21, 1, 0, 0], ![249, 259, 0, 1, 0], ![115, 236, 0, 0, 1]] where
  M :=![![![1, 5, 4, -2, 3], ![6, 16, 6, -6, -3], ![-6, -9, 25, 42, -21], ![-18, -51, 6, 25, 63], ![30, 65, -32, -122, 88]]]
  hmulB := by decide  
  f := ![![![-43, 545, -278, 82, -105]], ![![-210, -568, 372, -90, 141]], ![![-43, 308, -151, 46, -57]], ![![-243, -44, 102, -11, 39]], ![![-203, -266, 208, -44, 79]]]
  g := ![![![-2, -1, 4, -2, 3], ![3, 8, 6, -6, -3], ![-46, -24, 25, 42, -21], ![-54, -80, 6, 25, 63], ![96, 43, -32, -122, 88]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [99, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [219, 268], [0, 1]]
 g := ![![[63, 125], [264], [38, 6], [254, 67], [188], [217], [79], [1]], ![[0, 144], [264], [7, 263], [132, 202], [188], [217], [79], [1]]]
 h' := ![![[219, 268], [242, 177], [4, 159], [140, 153], [103, 41], [31, 200], [97, 32], [170, 219], [0, 1]], ![[0, 1], [0, 92], [124, 110], [22, 116], [205, 228], [253, 69], [111, 237], [249, 50], [219, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [214, 213]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [99, 50, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3176, 6762, -4170, -15799, 16023]
  a := ![1, 19, 3, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10468, 1505, -4170, -15799, 16023]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![43, -545, 278, -82, 105]] ![![1, 5, 4, -2, 3]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-399, -988, 264, 1080, 88]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![-399, -988, 264, 1080, 88]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![253, 20, 163, 1, 0], ![47, 2, 72, 0, 1]] where
  M :=![![![-399, -988, 264, 1080, 88], ![176, 41, -812, -2160, 3328], ![6656, 16816, -4099, -17272, -3152], ![-6480, -12960, 9984, 31265, -25908], ![-21592, -53980, 14300, 58472, 5357]]]
  hmulB := by decide  
  f := ![![![-29569, -90716, -88456, -6280, -25576]], ![![-51152, -157449, -153596, -10896, -44416]], ![![-88832, -273232, -266629, -18904, -77104]], ![![-84931, -261024, -254649, -18063, -73636]], ![![-29257, -89950, -87764, -6224, -25379]]]
  g := ![![![-1025, -84, -672, 1080, 88], ![1440, 135, 412, -2160, 3328], ![16696, 1360, 11211, -17272, -3152], ![-24719, -2164, -11885, 31265, -25908], ![-55597, -4554, -36540, 58472, 5357]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 3 2 8 [152, 30, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [166, 254, 260], [268, 16, 11], [0, 1]]
 g := ![![[31, 129, 139], [32, 188, 175], [73, 201, 122], [172, 68, 136], [149, 178], [35, 90], [163, 1], []], ![[143, 25, 65, 93], [91, 259, 41, 19], [77, 141, 177, 21], [0, 198, 171, 117], [40, 155], [95, 158], [123, 256], [43, 121]], ![[232, 19, 148, 128], [207, 192, 154, 177], [172, 45, 73, 158], [208, 254, 33, 72], [245, 241], [58, 158], [107, 18], [21, 121]]]
 h' := ![![[166, 254, 260], [14, 228, 117], [15, 173, 63], [143, 253, 193], [64, 106, 223], [46, 226, 125], [156, 107, 252], [0, 0, 1], [0, 1]], ![[268, 16, 11], [208, 161, 177], [161, 150, 189], [126, 144, 34], [18, 37, 234], [48, 24, 56], [106, 247, 145], [153, 148, 16], [166, 254, 260]], ![[0, 1], [86, 153, 248], [49, 219, 19], [235, 145, 44], [228, 128, 85], [134, 21, 90], [150, 188, 145], [69, 123, 254], [268, 16, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258, 106], []]
 b := ![[], [167, 54, 256], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 3
  hpos := by decide
  P := [152, 30, 108, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4746451, -10380228, 5762733, 19150089, -11428629]
  a := ![-1, 0, -2, 9, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15913555, -1367250, -8460666, 19150089, -11428629]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 19902511 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29569, 90716, 88456, 6280, 25576]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![29569, 90716, 88456, 6280, 25576]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![181, 217, 1, 0, 0], ![54, 150, 0, 1, 0], ![200, 108, 0, 0, 1]] where
  M :=![![![29569, 90716, 88456, 6280, 25576], ![51152, 157449, 153596, 10896, 44416], ![88832, 273232, 266629, 18904, 77104], ![32688, 100560, 98064, 6961, 28356], ![40696, 125196, 122132, 8664, 35317]]]
  hmulB := by decide  
  f := ![![![399, 988, -264, -1080, -88]], ![![-176, -41, 812, 2160, -3328]], ![![101, 565, 489, 1072, -2712]], ![![6, 222, 360, 865, -1764]], ![![304, 912, 76, -152, -1411]]]
  g := ![![![-79097, -84164, 88456, 6280, 25576], ![-137348, -146141, 153596, 10896, 44416], ![-238423, -253683, 266629, 18904, 77104], ![-87690, -93306, 98064, 6961, 28356], ![-109212, -116204, 122132, 8664, 35317]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [197, 232, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 270], [0, 1]]
 g := ![![[158, 138], [116, 4], [161, 195], [98, 244], [87], [162], [166], [1]], ![[120, 133], [1, 267], [178, 76], [129, 27], [87], [162], [166], [1]]]
 h' := ![![[39, 270], [183, 42], [261, 2], [206, 174], [167, 100], [222, 241], [145, 51], [74, 39], [0, 1]], ![[0, 1], [195, 229], [68, 269], [217, 97], [2, 171], [136, 30], [237, 220], [240, 232], [39, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [30, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [197, 232, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2307, -6512, 52, 4340, 1004]
  a := ![0, 0, -6, -6, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1649, -2868, 52, 4340, 1004]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![-399, -988, 264, 1080, 88]] ![![29569, 90716, 88456, 6280, 25576]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81, -96, 41, -20, 23]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-81, -96, 41, -20, 23]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![141, 44, 62, 240, 1]] where
  M :=![![![-81, -96, 41, -20, 23], ![46, 34, -78, -16, -37], ![-74, -139, -7, 98, -85], ![-48, -180, -27, 101, 147], ![66, 109, -136, -312, 248]]]
  hmulB := by decide  
  f := ![![![31, 36, -29, 6, -11]], ![![-22, -24, 18, -4, 7]], ![![14, 13, -13, 2, -5]], ![![-12, -12, 9, -1, 3]], ![![5, 7, -7, 2, -3]]]
  g := ![![![-12, -4, -5, -20, 23], ![19, 6, 8, 32, -37], ![43, 13, 19, 74, -85], ![-75, -24, -33, -127, 147], ![-126, -39, -56, -216, 248]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [230, 30, 245, 190, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 33, 143, 227], [30, 247, 265, 53], [255, 273, 146, 274], [0, 1]]
 g := ![![[261, 262, 186, 136], [102, 147, 16], [18, 48, 197, 155], [81, 37, 47], [127, 140, 174, 203], [79, 102, 90], [1], []], ![[27, 179, 83, 98, 45, 107], [244, 191, 30], [235, 265, 131, 4, 125, 221], [200, 139, 194], [242, 142, 275, 236, 189, 18], [228, 157, 160], [53, 116, 67], [182, 159, 7]], ![[175, 165, 165, 259, 120, 260], [180, 72, 228], [128, 91, 21, 189, 219, 31], [270, 24, 67], [229, 63, 110, 110, 81, 35], [118, 54, 211], [42, 57, 203], [196, 182, 39]], ![[70, 102, 125, 257, 66, 47], [5, 215, 130], [148, 13, 95, 276, 63, 40], [265, 38, 241], [263, 91, 136, 21, 276, 130], [212, 16, 207], [160, 243, 70], [241, 184, 9]]]
 h' := ![![[79, 33, 143, 227], [33, 219, 149, 39], [15, 156, 121, 273], [42, 40, 76, 175], [152, 222, 226, 18], [105, 158, 127, 122], [47, 247, 32, 87], [0, 0, 1], [0, 1]], ![[30, 247, 265, 53], [45, 165, 66, 262], [52, 252, 33, 169], [105, 259, 270, 20], [20, 7, 75, 86], [261, 264, 7, 241], [252, 144, 35, 116], [114, 25, 136, 90], [79, 33, 143, 227]], ![[255, 273, 146, 274], [14, 36, 138, 240], [124, 254, 20, 143], [39, 56, 107, 194], [214, 252, 37, 90], [199, 200, 88, 198], [245, 163, 109, 52], [140, 43, 55, 122], [30, 247, 265, 53]], ![[0, 1], [118, 134, 201, 13], [116, 169, 103, 246], [49, 199, 101, 165], [239, 73, 216, 83], [44, 209, 55, 270], [69, 0, 101, 22], [177, 209, 85, 65], [255, 273, 146, 274]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [247, 28, 171], []]
 b := ![[], [], [110, 206, 197, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [230, 30, 245, 190, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2593406396, 6029703138, -2512246208, -8938127268, 3199732256]
  a := ![13, -1, -2, 7, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1619382100, -486492838, -725255040, -2804598804, 3199732256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -36, 29, -6, 11]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-31, -36, 29, -6, 11]] 
 ![![277, 0, 0, 0, 0], ![110, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![206, 0, 0, 0, 1]] where
  M :=![![![-31, -36, 29, -6, 11], ![22, 24, -18, 4, -7], ![-14, -13, 13, -2, 5], ![12, 12, -9, 1, -3], ![6, 7, -4, 0, -2]]]
  hmulB := by decide  
  f := ![![![81, 96, -41, 20, -23]], ![![32, 38, -16, 8, -9]], ![![26, 31, -13, 6, -7]], ![![30, 36, -15, 7, -9]], ![![60, 71, -30, 16, -18]]]
  g := ![![![-1, -36, 29, -6, 11], ![0, 24, -18, 4, -7], ![-2, -13, 13, -2, 5], ![0, 12, -9, 1, -3], ![0, 7, -4, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-81, -96, 41, -20, 23]] ![![-31, -36, 29, -6, 11]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![-277, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1169, 1843, -2749, -8124, 9360]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![1169, 1843, -2749, -8124, 9360]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![182, 251, 123, 1, 0], ![184, 159, 143, 0, 1]] where
  M :=![![![1169, 1843, -2749, -8124, 9360], ![18720, 47969, -10266, -45410, -15012], ![-30024, -56340, 52715, 160360, -151242], ![-136230, -364947, 47451, 265901, 240540], ![69540, 112192, -154378, -449446, 506441]]]
  hmulB := by decide  
  f := ![![![133321309, 410111335, 400129715, 28378086, 115707570]], ![![231415140, 711859159, 694533480, 49257838, 200841828]], ![![401683656, 1235624280, 1205550811, 85500316, 348615342]], ![![469411180, 1443961802, 1408817672, 99916449, 407395068]], ![![423312836, 1302158071, 1270465245, 90104192, 367386983]]]
  g := ![![![-863, 1967, -1217, -8124, 9360], ![39308, 49227, 27480, -45410, -15012], ![-4936, -57862, 6961, 160360, -151242], ![-330212, -374918, -238632, 265901, 240540], ![-40272, 115299, -61543, -449446, 506441]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [97, 20, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [248, 36, 108], [275, 244, 173], [0, 1]]
 g := ![![[38, 74, 118], [250, 56], [262, 274], [263, 226, 245], [170, 214, 14], [165, 224], [242, 1], []], ![[146, 3, 265, 44], [211, 153], [73, 25], [129, 173, 32, 260], [25, 81, 222, 139], [40, 39], [137, 245], [232, 143]], ![[191, 24, 270, 270], [94, 136], [270, 191], [212, 8, 157, 142], [10, 152, 242, 152], [193, 273], [269, 172], [167, 143]]]
 h' := ![![[248, 36, 108], [54, 124, 250], [104, 121, 233], [60, 128, 214], [89, 183, 244], [52, 250, 24], [130, 121, 96], [0, 0, 1], [0, 1]], ![[275, 244, 173], [39, 41, 208], [67, 109, 232], [70, 161, 5], [167, 194, 58], [221, 24, 260], [27, 205, 243], [222, 188, 244], [248, 36, 108]], ![[0, 1], [183, 116, 104], [204, 51, 97], [82, 273, 62], [178, 185, 260], [106, 7, 278], [0, 236, 223], [135, 93, 36], [275, 244, 173]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 261], []]
 b := ![[], [103, 30, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [97, 20, 39, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![168431, 338352, -256612, -806628, 660794]
  a := ![-1, -3, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![90351, 347814, 15890, -806628, 660794]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133321309, -410111335, -400129715, -28378086, -115707570]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-133321309, -410111335, -400129715, -28378086, -115707570]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![247, 36, 1, 0, 0], ![67, 160, 0, 1, 0], ![172, 176, 0, 0, 1]] where
  M :=![![![-133321309, -410111335, -400129715, -28378086, -115707570], ![-231415140, -711859159, -694533480, -49257838, -200841828], ![-401683656, -1235624280, -1205550811, -85500316, -348615342], ![-147773514, -454568043, -443504469, -31454311, -128250474], ![-184015992, -566053990, -552276992, -39168698, -159704785]]]
  hmulB := by decide  
  f := ![![![-1169, -1843, 2749, 8124, -9360]], ![![-18720, -47969, 10266, 45410, 15012]], ![![-3319, -7565, 3544, 12388, -5766]], ![![-10453, -26454, 6332, 26847, 5460]], ![![-12688, -31572, 8662, 35014, 1871]]]
  g := ![![![428831858, 138432685, -400129715, -28378086, -115707570], ![744353822, 240287409, -694533480, -49257838, -200841828], ![1292027497, 417083828, -1205550811, -85500316, -348615342], ![475317974, 153439025, -443504469, -31454311, -128250474], ![591892978, 191071002, -552276992, -39168698, -159704785]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [254, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [173, 280], [0, 1]]
 g := ![![[277, 183], [212], [9], [243, 49], [115, 137], [218], [143], [1]], ![[183, 98], [212], [9], [9, 232], [212, 144], [218], [143], [1]]]
 h' := ![![[173, 280], [248, 203], [12, 178], [98, 3], [14, 7], [110, 207], [94, 80], [27, 173], [0, 1]], ![[0, 1], [242, 78], [177, 103], [55, 278], [101, 274], [234, 74], [165, 201], [170, 108], [173, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [116, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [254, 108, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2217, 2878, -2762, -10297, 11823]
  a := ![3, 0, 3, -7, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2346, -1178, -2762, -10297, 11823]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![1169, 1843, -2749, -8124, 9360]] ![![-133321309, -410111335, -400129715, -28378086, -115707570]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC281 : ContainsPrimesAboveP 281 ![I281N0, I281N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI281N0
    exact isPrimeI281N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 281 (by decide) (𝕀 ⊙ MulI281N0)
instance hp283 : Fact (Nat.Prime 283) := {out := by norm_num}

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-57, -75, 56, -12, 23]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-57, -75, 56, -12, 23]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![197, 187, 1, 0, 0], ![160, 208, 0, 1, 0], ![32, 56, 0, 0, 1]] where
  M :=![![![-57, -75, 56, -12, 23], ![46, 58, -42, -2, -13], ![-26, -19, 29, -2, -19], ![-6, -51, 0, 89, -3], ![-6, -41, -16, 6, 86]]]
  hmulB := by decide  
  f := ![![![-1043, -3285, -3266, -224, -947]], ![![-1894, -5778, -5604, -402, -1619]], ![![-1989, -6140, -6011, -424, -1739]], ![![-1986, -6117, -5978, -423, -1729]], ![![-498, -1531, -1494, -106, -432]]]
  g := ![![![-35, -33, 56, -12, 23], ![32, 32, -42, -2, -13], ![-17, -14, 29, -2, -19], ![-50, -65, 0, 89, -3], ![-2, -11, -16, 6, 86]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 2 2 8 [68, 137, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 282], [0, 1]]
 g := ![![[156, 93], [130, 4], [155], [47, 137], [136, 218], [42], [91], [1]], ![[150, 190], [148, 279], [155], [239, 146], [268, 65], [42], [91], [1]]]
 h' := ![![[146, 282], [216, 248], [28, 2], [200, 167], [91, 234], [101, 255], [134, 222], [215, 146], [0, 1]], ![[0, 1], [200, 35], [37, 281], [244, 116], [12, 49], [258, 28], [1, 61], [23, 137], [146, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [179, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 2
  hpos := by decide
  P := [68, 137, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1096, 1757, -1483, -5666, 6532]
  a := ![1, 1, 1, -5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3501, 3858, -1483, -5666, 6532]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-553, -110, 218, -26, 84]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-553, -110, 218, -26, 84]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![106, 209, 1, 0, 0], ![190, 182, 0, 1, 0], ![205, 146, 0, 0, 1]] where
  M :=![![![-553, -110, 218, -26, 84], ![168, -133, 24, -16, 6], ![12, 198, -115, 44, -42], ![-48, -198, 120, -55, 66], ![12, -38, 32, -52, 11]]]
  hmulB := by decide  
  f := ![![![-33931, -104374, -101834, -7222, -29448]], ![![-58896, -181171, -176760, -12536, -51114]], ![![-56566, -174003, -169767, -12040, -49092]], ![![-60790, -186996, -182444, -12939, -52758]], ![![-55129, -169582, -165454, -11734, -47845]]]
  g := ![![![-127, -188, 218, -26, 84], ![-2, -11, 24, -16, 6], ![44, 79, -115, 44, -42], ![-56, -88, 120, -55, 66], ![15, 4, 32, -52, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [240, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [204, 282], [0, 1]]
 g := ![![[268, 204], [232, 71], [185], [181, 275], [142, 228], [195], [15], [1]], ![[0, 79], [0, 212], [185], [247, 8], [242, 55], [195], [15], [1]]]
 h' := ![![[204, 282], [71, 223], [102, 141], [142, 40], [163, 29], [157, 47], [230, 228], [43, 204], [0, 1]], ![[0, 1], [0, 60], [0, 142], [95, 243], [136, 254], [123, 236], [47, 55], [58, 79], [204, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [104, 171]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [240, 79, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![594, 52, -20, 14, -66]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![48, 40, -20, 14, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2174975, -6690469, -6527632, -462954, -1887629]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![-2174975, -6690469, -6527632, -462954, -1887629]] 
 ![![283, 0, 0, 0, 0], ![170, 1, 0, 0, 0], ![249, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![216, 0, 0, 0, 1]] where
  M :=![![![-2174975, -6690469, -6527632, -462954, -1887629], ![-3775258, -11613120, -11330472, -803582, -3276491], ![-6552982, -20157713, -19667101, -1394834, -5687237], ![-2410746, -7415727, -7235238, -513139, -2092251], ![-3001998, -9234485, -9009730, -638990, -2605390]]]
  hmulB := by decide  
  f := ![![![-20445, -28835, 21370, -4610, 8129]], ![![-12224, -17250, 12782, -2758, 4863]], ![![-18029, -25414, 18839, -4068, 7166]], ![![-5529, -7810, 5786, -1241, 2194]], ![![-15594, -22003, 16300, -3502, 6200]]]
  g := ![![![11321415, -6690469, -6527632, -462954, -1887629], ![19651380, -11613120, -11330472, -803582, -3276491], ![34110289, -20157713, -19667101, -1394834, -5687237], ![12548675, -7415727, -7235238, -513139, -2092251], ![15626324, -9234485, -9009730, -638990, -2605390]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-57, -75, 56, -12, 23]] ![![-553, -110, 218, -26, 84]]
  ![![20445, 28835, -21370, 4610, -8129]] where
 M := ![![![20445, 28835, -21370, 4610, -8129]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![20445, 28835, -21370, 4610, -8129]] ![![-2174975, -6690469, -6527632, -462954, -1887629]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![-283, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC283 : ContainsPrimesAboveP 283 ![I283N0, I283N1, I283N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
    exact isPrimeI283N1
    exact isPrimeI283N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 283 (by decide) (𝕀 ⊙ MulI283N0 ⊙ MulI283N1)
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


def P293P0 : CertificateIrreducibleZModOfList' 293 5 2 8 [235, 191, 42, 274, 105, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 22, 255, 179, 26], [43, 60, 283, 223, 217], [183, 30, 59, 70, 51], [145, 180, 282, 114, 292], [0, 1]]
 g := ![![[12, 141, 98, 231, 69], [248, 32, 38, 141], [253, 16, 267, 260, 240], [88, 182, 229, 199], [137, 64, 75, 170], [8, 88, 203, 188, 1], [], []], ![[106, 37, 206, 225, 266, 114, 262, 143], [70, 112, 181, 279], [282, 172, 2, 287, 246, 48, 96, 17], [145, 154, 20, 53], [215, 165, 10, 222], [25, 103, 35, 187, 132, 92, 240, 234], [104, 245, 98, 54], [72, 98, 151, 90]], ![[138, 19, 107, 170, 38, 217, 54, 217], [34, 68, 163, 109], [268, 248, 265, 16, 230, 17, 37, 218], [215, 158, 131, 212], [94, 115, 21, 126], [85, 131, 245, 37, 29, 22, 132, 42], [159, 25, 20, 60], [141, 218, 122, 209]], ![[79, 154, 229, 196, 84, 198, 215, 99], [39, 17, 39, 33], [244, 188, 262, 292, 113, 243, 155, 44], [93, 267, 93, 283], [27, 115, 241, 244], [132, 61, 243, 238, 179, 221, 168, 241], [172, 64, 72, 107], [16, 181, 79, 257]], ![[37, 63, 70, 205, 290, 94, 129, 254], [11, 40, 188, 135], [268, 253, 245, 161, 142, 224, 192, 67], [63, 160, 41, 277], [19, 42, 151, 71], [80, 94, 107, 76, 222, 55, 249, 199], [234, 225, 17, 53], [115, 243, 253, 1]]]
 h' := ![![[110, 22, 255, 179, 26], [17, 44, 143, 235, 77], [24, 241, 7, 181, 58], [113, 193, 127, 36, 142], [269, 116, 211, 230, 130], [171, 60, 197, 231, 113], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[43, 60, 283, 223, 217], [250, 289, 253, 250, 93], [155, 249, 146, 172, 239], [22, 122, 267, 239, 244], [160, 146, 156, 17, 35], [17, 43, 126, 253, 148], [16, 61, 66, 195, 290], [161, 288, 236, 205, 167], [110, 22, 255, 179, 26]], ![[183, 30, 59, 70, 51], [93, 41, 118, 10, 292], [240, 111, 154, 15, 133], [110, 32, 60, 267, 248], [101, 58, 56, 229, 70], [252, 219, 183, 256, 205], [262, 228, 291, 21, 100], [65, 249, 53, 28, 71], [43, 60, 283, 223, 217]], ![[145, 180, 282, 114, 292], [120, 115, 266, 60, 149], [219, 205, 209, 284, 196], [36, 5, 230, 87, 96], [76, 42, 279, 35, 24], [189, 93, 226, 173, 206], [51, 58, 263, 28, 128], [136, 256, 37, 290, 20], [183, 30, 59, 70, 51]], ![[0, 1], [109, 97, 99, 31, 268], [244, 73, 70, 227, 253], [112, 234, 195, 250, 149], [248, 224, 177, 75, 34], [5, 171, 147, 259, 207], [63, 239, 259, 49, 67], [153, 86, 259, 63, 35], [145, 180, 282, 114, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 289, 269, 158], [], [], []]
 b := ![[], [167, 193, 131, 210, 39], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 5
  hpos := by decide
  P := [235, 191, 42, 274, 105, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8011801022333178, -16770360229466450, 11033074800283194, 35504743737752443, -25701102505010420]
  a := ![7, 2, -24, 23, -94]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-27344030792946, -57236724332650, 37655545393458, 121176599787551, -87717073395940]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 555, 542, 38, 155]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![179, 555, 542, 38, 155]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![126, 264, 79, 1, 0], ![202, 129, 202, 0, 1]] where
  M :=![![![179, 555, 542, 38, 155], ![310, 954, 942, 78, 269], ![538, 1655, 1627, 114, 503], ![234, 699, 576, -53, 171], ![270, 829, 752, 42, 118]]]
  hmulB := by decide  
  f := ![![![-15, 357, -188, 54, -71]], ![![-142, -370, 240, -58, 91]], ![![182, 313, -221, 50, -83]], ![![-82, -92, 73, -15, 28]], ![![50, 285, -168, 44, -63]]]
  g := ![![![-117, -96, -110, 38, 155], ![-208, -177, -194, 78, 269], ![-376, -304, -355, 114, 503], ![-90, -24, -97, -53, 171], ![-94, -83, -86, 42, 118]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [92, 304, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 200, 226], [141, 106, 81], [0, 1]]
 g := ![![[102, 105, 272], [4, 290, 127], [48, 183], [158, 11], [50, 102, 1], [267, 17, 76], [274, 1], []], ![[11, 233, 167, 45], [139, 76, 35, 124], [283, 275], [137, 101], [107, 253, 288, 23], [140, 205, 279, 130], [227, 184], [64, 114]], ![[163, 13, 173, 246], [135, 113, 111, 269], [149, 260], [196, 153], [273, 23, 139, 305], [82, 291, 27, 17], [107, 90], [209, 114]]]
 h' := ![![[133, 200, 226], [246, 148, 235], [159, 235, 197], [225, 303, 45], [5, 299, 25], [303, 86, 306], [273, 116, 171], [0, 0, 1], [0, 1]], ![[141, 106, 81], [79, 74, 28], [293, 100, 5], [242, 78, 182], [167, 184, 228], [247, 84, 296], [104, 73, 134], [135, 231, 106], [133, 200, 226]], ![[0, 1], [193, 85, 44], [146, 279, 105], [188, 233, 80], [159, 131, 54], [110, 137, 12], [273, 118, 2], [39, 76, 200], [141, 106, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 104], []]
 b := ![[], [247, 85, 187], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [92, 304, 33, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6017222, -6816459, 18428384, 51147628, -68427519]
  a := ![1, 3, -8, 8, -33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![24012184, -15252900, 31922230, 51147628, -68427519]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -51, 34, -8, 13]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-23, -51, 34, -8, 13]] 
 ![![307, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![166, 0, 1, 0, 0], ![223, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-23, -51, 34, -8, 13], ![26, 42, -30, 6, -11], ![-22, -29, 23, -6, 7], ![18, 21, -18, 11, -9], ![6, 5, -8, 6, 2]]]
  hmulB := by decide  
  f := ![![![-1845, -5745, -5644, -396, -1633]], ![![-233, -725, -712, -50, -206]], ![![-1016, -3163, -3107, -218, -899]], ![![-1347, -4194, -4120, -289, -1192]], ![![-363, -1130, -1110, -78, -321]]]
  g := ![![![-9, -51, 34, -8, 13], ![9, 42, -30, 6, -11], ![-6, -29, 23, -6, 7], ![1, 21, -18, 11, -9], ![-1, 5, -8, 6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -12, 10, -2, 4]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![-23, -12, 10, -2, 4]] 
 ![![307, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![125, 0, 1, 0, 0], ![243, 0, 0, 1, 0], ![219, 0, 0, 0, 1]] where
  M :=![![![-23, -12, 10, -2, 4], ![8, -3, -6, 0, -2], ![-4, -2, -7, 0, -2], ![0, -6, 0, -1, 0], ![0, -4, -2, 0, -1]]]
  hmulB := by decide  
  f := ![![![3, 36, -22, -6, -16]], ![![1, 13, -8, -2, -6]], ![![1, 14, -9, -2, -6]], ![![3, 30, -18, -7, -12]], ![![3, 28, -16, -6, -13]]]
  g := ![![![-1, -12, 10, -2, 4], ![5, -3, -6, 0, -2], ![5, -2, -7, 0, -2], ![3, -6, 0, -1, 0], ![3, -4, -2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![179, 555, 542, 38, 155]] ![![-23, -51, 34, -8, 13]]
  ![![3, 36, -22, -6, -16]] where
 M := ![![![3, 36, -22, -6, -16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![3, 36, -22, -6, -16]] ![![-23, -12, 10, -2, 4]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC307 : ContainsPrimesAboveP 307 ![I307N0, I307N1, I307N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI307N0
    exact isPrimeI307N1
    exact isPrimeI307N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 307 (by decide) (𝕀 ⊙ MulI307N0 ⊙ MulI307N1)


lemma PB434I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB434I6 : PrimesBelowBoundCertificateInterval O 251 307 434 where
  m := 9
  g := ![1, 2, 2, 2, 2, 2, 3, 1, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB434I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1]
    · exact ![I283N0, I283N1, I283N2]
    · exact ![I293N0]
    · exact ![I307N0, I307N1, I307N2]
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
    · exact ![1121154893057]
    · exact ![4784350561, 263]
    · exact ![19465109, 72361]
    · exact ![19902511, 73441]
    · exact ![5887339441, 277]
    · exact ![22188041, 78961]
    · exact ![80089, 80089, 283]
    · exact ![2159424884693]
    · exact ![28934443, 307, 307]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI257N0
    · dsimp ; intro j
      fin_cases j
      exact NI263N0
      exact NI263N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I263N1, I277N1, I283N2, I307N1, I307N2]
  Il := ![[], [I263N1], [], [], [I277N1], [], [I283N2], [], [I307N1, I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
