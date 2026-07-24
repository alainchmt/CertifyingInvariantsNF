
import IdealArithmetic.Examples.NF5_3_125000000_1.RI5_3_125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-349, -96, -76, -47, 102]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-349, -96, -76, -47, 102]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![0, 0, 0, 257, 0], ![115, 120, 95, 123, 1]] where
  M :=![![![-349, -96, -76, -47, 102], ![2040, 799, -192, -254, -94], ![-940, 360, 799, -145, -254], ![-3560, -1994, 456, 1053, -98], ![-980, -2140, -1994, 505, 1053]]]
  hmulB := by decide  
  f := ![![![-173, -178, -100, -51, -28]], ![![-560, -609, -356, -172, -102]], ![![-1020, -1070, -609, -305, -172]], ![![-1440, -1542, -892, -437, -254]], ![![-1415, -1508, -869, -428, -247]]]
  g := ![![![-47, -48, -38, -49, 102], ![50, 47, 34, 44, -94], ![110, 120, 97, 121, -254], ![30, 38, 38, 51, -98], ![-475, -500, -397, -502, 1053]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 4 2 8 [192, 188, 36, 72, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 49, 94, 206], [202, 90, 238, 122], [99, 117, 182, 186], [0, 1]]
 g := ![![[188, 251, 122, 60], [65, 1, 187], [203, 204, 133], [201, 64, 153], [35, 173, 61], [109, 217, 44], [1], []], ![[101, 202, 46, 252, 54, 126], [65, 227, 133], [18, 195, 228], [138, 27, 234], [176, 245, 226], [183, 157, 137], [175, 129, 136], [8, 2, 31]], ![[116, 210, 240, 148, 206, 73], [68, 155, 222], [191, 162, 190], [9, 54, 146], [193, 25, 140], [157, 231, 227], [220, 59, 117], [249, 32, 235]], ![[243, 28, 158, 248, 36, 112], [67, 187, 42], [240, 214, 60], [231, 86, 123], [177, 173, 104], [161, 6, 187], [72, 192, 9], [129, 45, 158]]]
 h' := ![![[141, 49, 94, 206], [46, 32, 2, 211], [31, 209, 19, 50], [86, 19, 140, 90], [223, 91, 96, 47], [2, 13, 112, 33], [65, 69, 221, 185], [0, 0, 1], [0, 1]], ![[202, 90, 238, 122], [226, 198, 163, 40], [192, 16, 144, 167], [214, 69, 100, 182], [204, 33, 12, 157], [103, 71, 95, 45], [162, 251, 146, 44], [98, 108, 191, 176], [141, 49, 94, 206]], ![[99, 117, 182, 186], [164, 214, 246, 212], [192, 193, 123, 215], [192, 86, 16, 31], [11, 225, 256, 114], [109, 94, 69, 198], [21, 219, 38, 235], [192, 109, 205, 84], [202, 90, 238, 122]], ![[0, 1], [2, 70, 103, 51], [4, 96, 228, 82], [9, 83, 1, 211], [97, 165, 150, 196], [160, 79, 238, 238], [177, 232, 109, 50], [196, 40, 117, 254], [99, 117, 182, 186]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [71, 58, 139], []]
 b := ![[], [], [117, 256, 230, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 4
  hpos := by decide
  P := [192, 188, 36, 72, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10537912, 11307689, 6410501, 1775956, 761709]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-299839, -311663, -256622, -357643, 761709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 4362470401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -178, -100, -51, -28]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![-173, -178, -100, -51, -28]] 
 ![![257, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![224, 0, 0, 0, 1]] where
  M :=![![![-173, -178, -100, -51, -28], ![-560, -609, -356, -172, -102], ![-1020, -1070, -609, -305, -172], ![-1440, -1542, -892, -437, -254], ![-2540, -2690, -1542, -765, -437]]]
  hmulB := by decide  
  f := ![![![-349, -96, -76, -47, 102]], ![![-7, -1, -4, -3, 4]], ![![-96, -24, -17, -13, 26]], ![![-22, -10, 0, 3, 2]], ![![-308, -92, -74, -39, 93]]]
  g := ![![![59, -178, -100, -51, -28], ![211, -609, -356, -172, -102], ![360, -1070, -609, -305, -172], ![528, -1542, -892, -437, -254], ![912, -2690, -1542, -765, -437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N1 : Nat.card (O ⧸ I257N1) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N1)

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := prime_ideal_of_norm_prime hp257.out _ NI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-349, -96, -76, -47, 102]] ![![-173, -178, -100, -51, -28]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![263, 0, 0, 0, 0]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![263, 0, 0, 0, 0]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![0, 0, 0, 0, 263]] where
  M :=![![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![0, 0, 0, 263, 0], ![0, 0, 0, 0, 263]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 5 2 8 [13, 130, 190, 60, 98, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 2, 20, 84, 72], [199, 47, 148, 238, 48], [61, 234, 2, 33, 220], [94, 242, 93, 171, 186], [0, 1]]
 g := ![![[55, 152, 51, 246, 151], [246, 130, 217, 181, 169], [63, 141, 210, 249, 136], [98, 261, 213, 108], [124, 143, 201, 100], [83, 76, 165, 1], [], []], ![[149, 12, 174, 160, 248, 110, 233, 124], [126, 0, 82, 120, 244, 11, 5, 2], [6, 35, 98, 176, 252, 22, 80, 151], [214, 65, 44, 147], [249, 228, 5, 244], [139, 135, 197, 207], [125, 122, 148, 35], [242, 148, 82, 187]], ![[223, 152, 69, 65, 129, 196, 174, 133], [258, 251, 134, 11, 232, 260, 225, 184], [99, 196, 121, 120, 211, 157, 201, 44], [22, 199, 230, 244], [50, 110, 3, 198], [230, 62, 209, 12], [250, 11, 31, 210], [125, 129, 92, 200]], ![[257, 87, 5, 176, 38, 241, 157, 55], [91, 116, 81, 215, 106, 22, 162, 194], [35, 29, 61, 95, 260, 111, 258, 215], [207, 85, 4, 62], [246, 29, 116, 9], [253, 255, 63, 81], [256, 228, 50, 61], [186, 80, 60, 8]], ![[261, 192, 144, 170, 52, 203, 142, 16], [218, 228, 241, 147, 56, 84, 255, 149], [51, 18, 42, 189, 213, 206, 91, 153], [2, 77, 132, 62], [108, 82, 224, 44], [184, 106, 220, 122], [74, 38, 204, 143], [96, 189, 154, 143]]]
 h' := ![![[74, 2, 20, 84, 72], [221, 105, 9, 203, 199], [233, 251, 33, 54, 250], [198, 213, 8, 26, 165], [169, 246, 29, 82, 138], [236, 57, 83, 145, 10], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[199, 47, 148, 238, 48], [32, 215, 257, 180, 34], [180, 40, 210, 169, 44], [222, 96, 177, 8, 236], [233, 165, 140, 236, 161], [83, 57, 103, 29, 36], [7, 30, 110, 35, 101], [226, 50, 61, 176, 185], [74, 2, 20, 84, 72]], ![[61, 234, 2, 33, 220], [64, 144, 42, 66, 211], [230, 228, 28, 36, 111], [195, 233, 45, 131, 158], [84, 134, 29, 198, 227], [205, 130, 212, 192, 143], [202, 256, 104, 178, 46], [104, 253, 198, 261, 173], [199, 47, 148, 238, 48]], ![[94, 242, 93, 171, 186], [234, 126, 27, 203, 132], [215, 93, 67, 196, 148], [87, 181, 242, 98, 28], [66, 110, 89, 51, 204], [125, 173, 135, 254, 3], [235, 130, 140, 213, 254], [251, 172, 64, 154, 245], [61, 234, 2, 33, 220]], ![[0, 1], [201, 199, 191, 137, 213], [102, 177, 188, 71, 236], [106, 66, 54, 0, 202], [55, 134, 239, 222, 59], [12, 109, 256, 169, 71], [33, 110, 172, 100, 124], [224, 51, 202, 198, 186], [94, 242, 93, 171, 186]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 24, 170, 121], [], [], []]
 b := ![[], [197, 90, 122, 146, 170], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 5
  hpos := by decide
  P := [13, 130, 190, 60, 98, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20244271503206, -18893773431415, -9414395493066, -4276467336514, -1122588837323]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-76974416362, -71839442705, -35796180582, -16260332078, -4268398621]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 1258284197543 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def PBC263 : ContainsPrimesAboveP 263 ![I263N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI263N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![263, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 263 (by decide) 𝕀

instance hp269 : Fact (Nat.Prime 269) := {out := by norm_num}

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -40, -8, 17, 6]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-51, -40, -8, 17, 6]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![67, 63, 1, 0, 0], ![83, 100, 0, 1, 0], ![25, 63, 0, 0, 1]] where
  M :=![![![-51, -40, -8, 17, 6], ![120, 13, -80, -22, 34], ![340, 224, 13, -97, -22], ![-280, 38, 264, 35, -114], ![-1140, -692, 38, 321, 35]]]
  hmulB := by decide  
  f := ![![![1641, 410, -336, 217, -184]], ![![-3680, -903, 820, -488, 434]], ![![-437, -105, 105, -58, 54]], ![![-873, -212, 204, -116, 106]], ![![-695, -169, 158, -92, 83]]]
  g := ![![![-4, -6, -8, 17, 6], ![24, 19, -80, -22, 34], ![30, 39, 13, -97, -22], ![-67, -48, 264, 35, -114], ![-116, -139, 38, 321, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [189, 240, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 268], [0, 1]]
 g := ![![[266, 232], [244], [218, 225], [121, 6], [244], [260], [34], [1]], ![[0, 37], [244], [18, 44], [26, 263], [244], [260], [34], [1]]]
 h' := ![![[29, 268], [25, 129], [224, 128], [265, 15], [205, 116], [225, 128], [243, 246], [80, 29], [0, 1]], ![[0, 1], [0, 140], [170, 141], [162, 254], [72, 153], [171, 141], [114, 23], [114, 240], [29, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193]]
 b := ![[], [13, 231]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [189, 240, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![550, -498, 315, -920, -404]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![245, 361, 315, -920, -404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-301, -87, 70, -42, 36]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-301, -87, 70, -42, 36]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![226, 89, 1, 0, 0], ![61, 128, 0, 1, 0], ![124, 71, 0, 0, 1]] where
  M :=![![![-301, -87, 70, -42, 36], ![720, 201, -174, 104, -84], ![-840, -231, 201, -132, 104], ![680, 204, -144, 97, -90], ![-900, -272, 204, -99, 97]]]
  hmulB := by decide  
  f := ![![![111, -83, -84, -14, -36]], ![![-720, -405, -166, -132, -28]], ![![-146, -206, -127, -56, -40]], ![![-321, -215, -100, -67, -22]], ![![-144, -151, -86, -43, -25]]]
  g := ![![![-67, -13, 70, -42, 36], ![164, 31, -174, 104, -84], ![-190, -32, 201, -132, 104], ![143, 26, -144, 97, -90], ![-197, -47, 204, -99, 97]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [9, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 268], [0, 1]]
 g := ![![[14, 30], [36], [86, 216], [62, 115], [248], [38], [5], [1]], ![[0, 239], [36], [39, 53], [98, 154], [248], [38], [5], [1]]]
 h' := ![![[143, 268], [227, 179], [33, 263], [249, 111], [9, 121], [147, 168], [36, 24], [260, 143], [0, 1]], ![[0, 1], [0, 90], [251, 6], [251, 158], [96, 148], [230, 101], [240, 245], [265, 126], [143, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165]]
 b := ![[], [221, 217]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [9, 126, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3136, 8881, 7402, 5660, 2155]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8484, -5678, 7402, 5660, 2155]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -8, -10, 3, 4]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![1, -8, -10, 3, 4]] 
 ![![269, 0, 0, 0, 0], ![234, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![126, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![1, -8, -10, 3, 4], ![80, 39, -16, -24, 6], ![60, 68, 39, -19, -24], ![-280, -114, 76, 63, -22], ![-220, -234, -114, 87, 63]]]
  hmulB := by decide  
  f := ![![![-3531, -2202, -1002, -705, -194]], ![![-3086, -1941, -888, -620, -174]], ![![-840, -538, -249, -171, -50]], ![![-1714, -1098, -508, -349, -102]], ![![-807, -550, -264, -172, -57]]]
  g := ![![![7, -8, -10, 3, 4], ![-20, 39, -16, -24, 6], ![-54, 68, 39, -19, -24], ![56, -114, 76, 63, -22], ![175, -234, -114, 87, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-51, -40, -8, 17, 6]] ![![-301, -87, 70, -42, 36]]
  ![![-569, 81, 558, 93, -256]] where
 M := ![![![-569, 81, 558, 93, -256]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![-569, 81, 558, 93, -256]] ![![1, -8, -10, 3, 4]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![69671, 94957, 62408, -30666, -33356]]]
 hmul := by decide  
 g := ![![![![259, 353, 232, -114, -124]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 160, 50, 26, 42]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![199, 160, 50, 26, 42]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![37, 249, 27, 220, 1]] where
  M :=![![![199, 160, 50, 26, 42], ![840, 753, 320, 58, 52], ![520, 892, 753, 294, 58], ![160, 608, 732, 695, 268], ![2680, 2054, 608, 598, 695]]]
  hmulB := by decide  
  f := ![![![-871, -92, 102, -70, 78]], ![![1560, 167, -184, 126, -140]], ![![-1400, -152, 167, -114, 126]], ![![480, 56, -60, 41, -44]], ![![1563, 171, -187, 128, -141]]]
  g := ![![![-5, -38, -4, -34, 42], ![-4, -45, -4, -42, 52], ![-6, -50, -3, -46, 58], ![-36, -244, -24, -215, 268], ![-85, -631, -67, -562, 695]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [54, 50, 265, 63, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 167, 217, 227], [134, 72, 109, 130], [254, 31, 216, 185], [0, 1]]
 g := ![![[184, 89, 212, 265], [226, 219, 183, 217], [66, 203, 188, 44], [30, 114, 30, 233], [268, 228, 129], [3, 143, 175], [1], []], ![[109, 217, 114, 170, 165, 102], [168, 145, 85, 55, 175, 54], [239, 123, 198, 46, 52, 263], [121, 255, 168, 270, 237, 143], [255, 233, 154], [199, 165, 245], [51, 10, 82], [236, 127, 39]], ![[35, 80, 165, 132, 39, 91], [229, 114, 123, 112, 176, 104], [162, 186, 1, 188, 152, 266], [165, 98, 30, 96, 171, 59], [146, 181, 174], [72, 12, 35], [244, 259, 32], [29, 215, 98]], ![[5, 64, 76, 261, 109, 126], [267, 265, 43, 88, 249, 211], [235, 268, 41, 172, 47, 144], [249, 145, 207, 4, 99, 177], [170, 173, 57], [217, 95, 82], [57, 38, 53], [17, 147, 79]]]
 h' := ![![[91, 167, 217, 227], [262, 235, 184, 219], [230, 137, 138, 115], [6, 225, 224, 55], [201, 110, 2, 222], [44, 238, 175, 20], [217, 221, 6, 208], [0, 0, 1], [0, 1]], ![[134, 72, 109, 130], [30, 61, 35, 84], [153, 232, 16, 76], [36, 174, 93, 31], [53, 242, 30, 147], [96, 232, 180, 69], [96, 218, 195, 40], [144, 83, 181, 176], [91, 167, 217, 227]], ![[254, 31, 216, 185], [267, 164, 241, 176], [122, 88, 120, 230], [154, 157, 261, 61], [10, 226, 199, 239], [199, 53, 137, 101], [201, 68, 58, 199], [130, 3, 100, 113], [134, 72, 109, 130]], ![[0, 1], [4, 82, 82, 63], [144, 85, 268, 121], [133, 257, 235, 124], [112, 235, 40, 205], [112, 19, 50, 81], [155, 35, 12, 95], [184, 185, 260, 253], [254, 31, 216, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [108, 48, 214], []]
 b := ![[], [], [3, 50, 165, 236], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [54, 50, 265, 63, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2839667, -4548570, -7144982, 5888535, 7084881]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-956830, -6526509, -732239, -5729835, 7084881]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-871, -92, 102, -70, 78]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![-871, -92, 102, -70, 78]] 
 ![![271, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![218, 0, 1, 0, 0], ![213, 0, 0, 1, 0], ![248, 0, 0, 0, 1]] where
  M :=![![![-871, -92, 102, -70, 78], ![1560, 167, -184, 126, -140], ![-1400, -152, 167, -114, 126], ![480, 56, -60, 41, -44], ![-440, -54, 56, -38, 41]]]
  hmulB := by decide  
  f := ![![![199, 160, 50, 26, 42]], ![![78, 63, 20, 10, 16]], ![![162, 132, 43, 22, 34]], ![![157, 128, 42, 23, 34]], ![![192, 154, 48, 26, 41]]]
  g := ![![![-67, -92, 102, -70, 78], ![120, 167, -184, 126, -140], ![-108, -152, 167, -114, 126], ![37, 56, -60, 41, -44], ![-34, -54, 56, -38, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![199, 160, 50, 26, 42]] ![![-871, -92, 102, -70, 78]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![561, 260, -82, -48, -36]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![561, 260, -82, -48, -36]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![146, 239, 110, 186, 1]] where
  M :=![![![561, 260, -82, -48, -36], ![-720, 47, 520, -128, -96], ![-960, -676, 47, 568, -128], ![-920, -1248, -936, 175, 616], ![6160, 2768, -1248, -1244, 175]]]
  hmulB := by decide  
  f := ![![![37, 60, 38, 16, 12]], ![![240, 219, 120, 64, 32]], ![![320, 372, 219, 104, 64]], ![![520, 544, 312, 155, 88]], ![![706, 737, 422, 210, 119]]]
  g := ![![![21, 32, 14, 24, -36], ![48, 83, 40, 64, -96], ![64, 108, 51, 88, -128], ![-328, -536, -248, -413, 616], ![-70, -141, -74, -122, 175]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [82, 275, 37, 16, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 216, 53, 96], [75, 168, 261, 257], [78, 169, 240, 201], [0, 1]]
 g := ![![[73, 152, 56, 10], [23, 206, 203], [224, 236, 67, 175], [144, 152, 122], [129, 122, 272, 198], [199, 135, 256], [1], []], ![[255, 108, 45, 144, 18, 56], [89, 29, 225], [222, 69, 66, 174, 181, 96], [139, 27, 86], [149, 254, 2, 204, 250, 97], [263, 128, 220], [123, 258, 19], [103, 112, 75]], ![[72, 62, 114, 133, 244, 38], [133, 101, 274], [193, 168, 46, 0, 259, 170], [191, 118, 248], [155, 197, 243, 66, 58, 115], [172, 54, 207], [43, 274, 121], [261, 57, 123]], ![[270, 33, 228, 136, 44, 206], [249, 84, 91], [171, 264, 172, 119, 143, 39], [47, 150, 189], [224, 261, 185, 187, 78, 55], [15, 255, 13], [252, 198, 69], [260, 186, 236]]]
 h' := ![![[108, 216, 53, 96], [247, 95, 130, 248], [191, 193, 197, 155], [37, 59, 89, 27], [225, 178, 130, 251], [101, 80, 147, 72], [195, 2, 240, 261], [0, 0, 1], [0, 1]], ![[75, 168, 261, 257], [220, 243, 81, 160], [224, 105, 241, 15], [113, 235, 176, 276], [185, 71, 111, 45], [142, 93, 125, 42], [42, 255, 165, 142], [171, 6, 169, 41], [108, 216, 53, 96]], ![[78, 169, 240, 201], [125, 171, 12, 68], [134, 106, 73, 44], [42, 141, 74, 246], [209, 173, 199, 91], [63, 118, 67, 57], [219, 236, 62, 255], [12, 273, 101, 266], [75, 168, 261, 257]], ![[0, 1], [171, 45, 54, 78], [63, 150, 43, 63], [99, 119, 215, 5], [96, 132, 114, 167], [234, 263, 215, 106], [112, 61, 87, 173], [276, 275, 6, 247], [78, 169, 240, 201]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 52, 25], []]
 b := ![[], [], [120, 249, 77, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [82, 275, 37, 16, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-235834318, -41728930, 114688812, 11981620, -23016426]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11280014, 19708292, 9554136, 15498328, -23016426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -60, -38, -16, -12]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-37, -60, -38, -16, -12]] 
 ![![277, 0, 0, 0, 0], ![182, 1, 0, 0, 0], ![58, 0, 1, 0, 0], ![171, 0, 0, 1, 0], ![228, 0, 0, 0, 1]] where
  M :=![![![-37, -60, -38, -16, -12], ![-240, -219, -120, -64, -32], ![-320, -372, -219, -104, -64], ![-520, -544, -312, -155, -88], ![-880, -944, -544, -268, -155]]]
  hmulB := by decide  
  f := ![![![-561, -260, 82, 48, 36]], ![![-366, -171, 52, 32, 24]], ![![-114, -52, 17, 8, 8]], ![![-343, -156, 54, 29, 20]], ![![-484, -224, 72, 44, 29]]]
  g := ![![![67, -60, -38, -16, -12], ![234, -219, -120, -64, -32], ![406, -372, -219, -104, -64], ![589, -544, -312, -155, -88], ![1024, -944, -544, -268, -155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![561, 260, -82, -48, -36]] ![![-37, -60, -38, -16, -12]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![979, 275, -232, 138, -114]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![979, 275, -232, 138, -114]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![0, 0, 281, 0, 0], ![186, 13, 131, 1, 0], ![81, 1, 274, 0, 1]] where
  M :=![![![979, 275, -232, 138, -114], ![-2280, -621, 550, -350, 276], ![2760, 791, -621, 412, -350], ![-2360, -720, 516, -271, 274], ![2740, 722, -720, 379, -271]]]
  hmulB := by decide  
  f := ![![![979, 103, -110, 78, -86]], ![![-1720, -163, 206, -134, 156]], ![![1560, 179, -163, 128, -134]], ![![1294, 144, -139, 105, -112]], ![![1799, 204, -190, 147, -155]]]
  g := ![![![-55, -5, 46, 138, -114], ![144, 13, -104, -350, 276], ![-162, -15, 147, 412, -350], ![92, 9, -139, -271, 274], ![-163, -14, 85, 379, -271]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 3 2 8 [202, 143, 193, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [246, 223, 33], [123, 57, 248], [0, 1]]
 g := ![![[277, 65, 273], [202, 118], [215, 225], [211, 103, 118], [200, 62, 195], [93, 196], [88, 1], []], ![[130, 29, 230, 263], [189, 162], [254, 101], [230, 15, 144, 231], [169, 179, 158, 264], [98, 59], [53, 158], [117, 246]], ![[10, 252, 168, 250], [74, 33], [193, 119], [159, 18, 190, 280], [181, 71, 142, 246], [146, 219], [95, 273], [183, 246]]]
 h' := ![![[246, 223, 33], [97, 198, 58], [76, 8, 31], [90, 44, 266], [64, 20, 31], [31, 10, 241], [208, 140, 14], [0, 0, 1], [0, 1]], ![[123, 57, 248], [95, 15, 5], [30, 125, 64], [14, 254, 35], [160, 272, 179], [213, 65, 17], [236, 14, 79], [71, 19, 57], [246, 223, 33]], ![[0, 1], [206, 68, 218], [199, 148, 186], [72, 264, 261], [258, 270, 71], [269, 206, 23], [16, 127, 188], [81, 262, 223], [123, 57, 248]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193, 8], []]
 b := ![[], [30, 182, 136], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 3
  hpos := by decide
  P := [202, 143, 193, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61135, 27700, -12725, 16323, 47045]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24148, -824, -53528, 16323, 47045]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 22188041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, -4, 0, 2]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![1, -2, -4, 0, 2]] 
 ![![281, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![267, 0, 1, 0, 0], ![79, 0, 0, 1, 0], ![190, 0, 0, 0, 1]] where
  M :=![![![1, -2, -4, 0, 2], ![40, 21, -4, -10, 0], ![0, 18, 21, -4, -10], ![-120, -60, 20, 31, -4], ![-40, -74, -60, 22, 31]]]
  hmulB := by decide  
  f := ![![![441, 278, -124, 112, -54]], ![![117, 75, -32, 30, -14]], ![![427, 268, -119, 108, -52]], ![![119, 78, -32, 31, -14]], ![![310, 194, -84, 78, -37]]]
  g := ![![![3, -2, -4, 0, 2], ![1, 21, -4, -10, 0], ![-17, 18, 21, -4, -10], ![-9, -60, 20, 31, -4], ![50, -74, -60, 22, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 12, 16, -2, -8]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![1, 12, 16, -2, -8]] 
 ![![281, 0, 0, 0, 0], ![223, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![145, 0, 0, 1, 0], ![271, 0, 0, 0, 1]] where
  M :=![![![1, 12, 16, -2, -8], ![-160, -79, 24, 40, -4], ![-40, -92, -79, 26, 40], ![480, 220, -104, -119, 28], ![280, 356, 220, -118, -119]]]
  hmulB := by decide  
  f := ![![![10201, 10844, 6304, 3074, 1792]], ![![8223, 8741, 5080, 2478, 1444]], ![![364, 388, 225, 110, 64]], ![![5585, 5936, 3448, 1683, 980]], ![![10391, 11048, 6420, 3132, 1825]]]
  g := ![![![-1, 12, 16, -2, -8], ![45, -79, 24, 40, -4], ![22, -92, -79, 26, 40], ![-137, 220, -104, -119, 28], ![-109, 356, 220, -118, -119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![979, 275, -232, 138, -114]] ![![1, -2, -4, 0, 2]]
  ![![-21, -203, -288, -52, 192]] where
 M := ![![![-21, -203, -288, -52, 192]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-21, -203, -288, -52, 192]] ![![1, 12, 16, -2, -8]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![72779, 99193, 65192, -32034, -34844]]]
 hmul := by decide  
 g := ![![![![259, 353, 232, -114, -124]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![283, 0, 0, 0, 0]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![283, 0, 0, 0, 0]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![0, 0, 0, 0, 283]] where
  M :=![![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![0, 0, 0, 0, 283]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 5 2 8 [135, 55, 135, 144, 138, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 173, 256, 24, 5], [139, 101, 221, 85, 45], [57, 173, 134, 173, 156], [189, 118, 238, 1, 77], [0, 1]]
 g := ![![[159, 184, 144, 236, 41], [151, 3, 74, 64, 225], [110, 122, 95, 164], [79, 5, 209, 276, 159], [74, 191, 249, 96, 61], [138, 222, 145, 1], [], []], ![[62, 65, 189, 93, 258, 212, 271, 67], [248, 280, 60, 270, 271, 172, 264, 184], [151, 119, 37, 257], [164, 2, 248, 47, 3, 176, 53, 2], [62, 104, 113, 38, 129, 187, 219, 209], [153, 16, 77, 157], [121, 192, 264, 11], [220, 187, 186, 25]], ![[107, 210, 111, 90, 240, 40, 45, 3], [161, 206, 105, 144, 83, 117, 209, 167], [268, 210, 115, 49], [134, 160, 150, 90, 125, 235, 58, 184], [65, 126, 255, 158, 45, 11, 140, 193], [268, 202, 249, 78], [152, 75, 102, 237], [67, 266, 163, 44]], ![[4, 19, 28, 15, 271, 74, 17, 182], [175, 40, 154, 195, 136, 74, 8, 272], [209, 99, 119, 237], [274, 48, 144, 33, 44, 258, 121, 200], [212, 259, 46, 169, 101, 65, 230, 76], [20, 161, 30, 94], [55, 35, 179, 150], [251, 132, 199, 281]], ![[37, 8, 135, 76, 166, 46, 229, 266], [177, 179, 181, 274, 42, 84, 83, 168], [279, 173, 21, 110], [77, 56, 176, 16, 75, 270, 28, 185], [267, 72, 113, 51, 20, 149, 149, 136], [122, 188, 207, 211], [139, 212, 206, 230], [192, 124, 105, 269]]]
 h' := ![![[43, 173, 256, 24, 5], [274, 154, 259, 135, 265], [146, 89, 241, 207, 15], [89, 224, 202, 270, 247], [198, 183, 169, 54, 190], [48, 79, 242, 63, 108], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[139, 101, 221, 85, 45], [229, 198, 186, 163, 97], [84, 154, 17, 265, 85], [248, 248, 204, 13, 92], [243, 144, 181, 55, 118], [183, 203, 198, 147, 116], [184, 240, 263, 239, 52], [166, 173, 151, 17, 119], [43, 173, 256, 24, 5]], ![[57, 173, 134, 173, 156], [245, 191, 76, 210, 240], [199, 62, 166, 239, 24], [167, 97, 260, 188, 7], [15, 6, 159, 133, 66], [27, 265, 138, 70, 127], [242, 47, 143, 193, 19], [88, 86, 206, 168, 37], [139, 101, 221, 85, 45]], ![[189, 118, 238, 1, 77], [242, 22, 147, 197, 37], [215, 88, 201, 32, 280], [160, 223, 143, 88, 246], [253, 50, 18, 176, 208], [93, 142, 26, 217, 79], [23, 75, 156, 146, 124], [211, 266, 118, 32, 198], [57, 173, 134, 173, 156]], ![[0, 1], [77, 1, 181, 144, 210], [170, 173, 224, 106, 162], [269, 57, 40, 7, 257], [182, 183, 39, 148, 267], [3, 160, 245, 69, 136], [258, 204, 4, 271, 87], [179, 41, 90, 66, 212], [189, 118, 238, 1, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165, 18, 110, 70], [], [], []]
 b := ![[], [48, 192, 54, 264, 269], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 5
  hpos := by decide
  P := [135, 55, 135, 144, 138, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15569528, 110846855, 82765614, -106325930, 2024299]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![55016, 391685, 292458, -375710, 7153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 1815232161643 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def PBC283 : ContainsPrimesAboveP 283 ![I283N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI283N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![283, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 283 (by decide) 𝕀

instance hp293 : Fact (Nat.Prime 293) := {out := by norm_num}

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-307, -59, 28, -13, 30]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-307, -59, 28, -13, 30]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![81, 124, 223, 1, 0], ![103, 42, 205, 0, 1]] where
  M :=![![![-307, -59, 28, -13, 30], ![600, 81, -118, 26, -26], ![-260, 85, 81, -105, 26], ![-40, 26, 144, 55, -92], ![-920, -500, 26, 190, 55]]]
  hmulB := by decide  
  f := ![![![161, 183, 110, 51, 32]], ![![640, 655, 366, 188, 102]], ![![1020, 1115, 655, 315, 188]], ![![1097, 1182, 687, 335, 196]], ![![871, 948, 555, 268, 159]]]
  g := ![![![-8, 1, -11, -13, 30], ![4, -7, -2, 26, -26], ![19, 41, 62, -105, 26], ![17, -10, 23, 55, -92], ![-75, -90, -183, 190, 55]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [190, 285, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [285, 120, 54], [253, 172, 239], [0, 1]]
 g := ![![[145, 204, 61], [173, 267], [285, 94, 186], [169, 202], [161, 235], [114, 183, 145], [245, 1], []], ![[74, 174, 230, 220], [186, 160], [127, 128, 86, 212], [117, 262], [243, 100], [214, 225, 0, 203], [212, 284], [154, 279]], ![[263, 265, 221, 88], [282, 237], [32, 134, 53, 237], [55, 254], [131, 184], [197, 42, 8, 289], [195, 43], [262, 279]]]
 h' := ![![[285, 120, 54], [41, 257, 103], [55, 102, 45], [175, 20, 123], [73, 33, 74], [22, 34, 95], [37, 12, 261], [0, 0, 1], [0, 1]], ![[253, 172, 239], [200, 142, 243], [110, 188, 63], [208, 8, 261], [180, 165, 153], [254, 91, 10], [129, 159, 125], [104, 214, 172], [285, 120, 54]], ![[0, 1], [17, 187, 240], [177, 3, 185], [39, 265, 202], [122, 95, 66], [273, 168, 188], [137, 122, 200], [165, 79, 120], [253, 172, 239]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 174], []]
 b := ![[], [74, 162, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [190, 285, 48, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-112636, 36925, 86442, -143435, 83574]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![9889, 48849, 50989, -143435, 83574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![161, 183, 110, 51, 32]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![161, 183, 110, 51, 32]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![177, 70, 1, 0, 0], ![209, 170, 0, 1, 0], ![89, 71, 0, 0, 1]] where
  M :=![![![161, 183, 110, 51, 32], ![640, 655, 366, 188, 102], ![1020, 1115, 655, 315, 188], ![1560, 1638, 932, 467, 264], ![2640, 2830, 1638, 800, 467]]]
  hmulB := by decide  
  f := ![![![-307, -59, 28, -13, 30]], ![![600, 81, -118, 26, -26]], ![![-43, -16, -11, -2, 12]], ![![129, 5, -48, 6, 6]], ![![49, 0, -20, 3, 3]]]
  g := ![![![-112, -63, 110, 51, 32], ![-384, -219, 366, 188, 102], ![-674, -381, 655, 315, 188], ![-971, -552, 932, 467, 264], ![-1693, -959, 1638, 800, 467]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [102, 214, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 292], [0, 1]]
 g := ![![[117, 158], [170], [292, 258], [90], [189], [136, 115], [88], [1]], ![[0, 135], [170], [164, 35], [90], [189], [138, 178], [88], [1]]]
 h' := ![![[79, 292], [96, 47], [102, 180], [232, 59], [6, 267], [192, 90], [256, 212], [191, 79], [0, 1]], ![[0, 1], [0, 246], [258, 113], [205, 234], [3, 26], [270, 203], [10, 81], [279, 214], [79, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [149, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [102, 214, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![437, 97, 438, -92, 1391]
  a := ![1, 0, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-620, -388, 438, -92, 1391]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-307, -59, 28, -13, 30]] ![![161, 183, 110, 51, 32]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC293 : ContainsPrimesAboveP 293 ![I293N0, I293N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI293N0
    exact isPrimeI293N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 293 (by decide) (𝕀 ⊙ MulI293N0)
instance hp307 : Fact (Nat.Prime 307) := {out := by norm_num}

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2547, -263, 292, -201, 226]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-2547, -263, 292, -201, 226]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![134, 87, 235, 1, 0], ![131, 155, 122, 0, 1]] where
  M :=![![![-2547, -263, 292, -201, 226], ![4520, 457, -526, 358, -402], ![-4020, -415, 457, -325, 358], ![1320, 138, -152, 99, -124], ![-1240, -160, 138, -90, 99]]]
  hmulB := by decide  
  f := ![![![-41, -11, 10, -7, 4]], ![![80, 17, -22, 16, -14]], ![![-140, -55, 17, -15, 16]], ![![-102, -42, 11, -10, 10]], ![![-33, -18, 0, -1, 1]]]
  g := ![![![-17, -58, 65, -201, 226], ![30, 103, -116, 358, -402], ![-24, -90, 108, -325, 358], ![14, 35, -27, 99, -124], ![-7, -25, 30, -90, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 3 2 8 [126, 215, 255, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 113, 226], [51, 193, 81], [0, 1]]
 g := ![![[134, 17, 63], [248, 86, 103], [278, 37], [16, 252], [214, 19, 58], [40, 261, 168], [52, 1], []], ![[260, 282, 158, 78], [102, 56, 244, 231], [120, 9], [149, 167], [233, 29, 55, 111], [181, 105, 299, 300], [25, 102], [209, 114]], ![[177, 94, 223, 215], [172, 251, 148, 79], [43, 294], [227, 122], [267, 296, 257, 235], [89, 25, 240, 46], [243, 182], [47, 114]]]
 h' := ![![[1, 113, 226], [66, 267, 129], [227, 4, 32], [74, 62, 61], [52, 215, 258], [179, 239, 241], [202, 53, 33], [0, 0, 1], [0, 1]], ![[51, 193, 81], [24, 22, 200], [290, 8, 19], [47, 58, 304], [263, 223, 144], [162, 216, 138], [76, 197, 234], [69, 178, 193], [1, 113, 226]], ![[0, 1], [31, 18, 285], [74, 295, 256], [205, 187, 249], [291, 176, 212], [76, 159, 235], [148, 57, 40], [56, 129, 113], [51, 193, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [276, 110], []]
 b := ![[], [223, 64, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 3
  hpos := by decide
  P := [126, 215, 255, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4750, 3343, 4735, -5484, 1123]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1899, 998, 3767, -5484, 1123]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 28934443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -6, -2, -2, 0]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-13, -6, -2, -2, 0]] 
 ![![307, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![245, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-13, -6, -2, -2, 0], ![0, -15, -12, -4, -4], ![-40, -30, -15, -10, -4], ![-40, -44, -24, -11, -8], ![-80, -80, -44, -20, -11]]]
  hmulB := by decide  
  f := ![![![-1599, -422, 362, -234, 192]], ![![-300, -79, 68, -44, 36]], ![![-234, -62, 53, -34, 28]], ![![-1265, -334, 286, -185, 152]], ![![-106, -28, 24, -16, 13]]]
  g := ![![![3, -6, -2, -2, 0], ![8, -15, -12, -4, -4], ![16, -30, -15, -10, -4], ![21, -44, -24, -11, -8], ![38, -80, -44, -20, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-203, -57, 48, -29, 24]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![-203, -57, 48, -29, 24]] 
 ![![307, 0, 0, 0, 0], ![84, 1, 0, 0, 0], ![156, 0, 1, 0, 0], ![160, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-203, -57, 48, -29, 24], ![480, 133, -114, 72, -58], ![-580, -165, 133, -85, 72], ![480, 142, -108, 61, -56], ![-560, -150, 142, -80, 61]]]
  hmulB := by decide  
  f := ![![![11391, 1231, -1250, 917, -994]], ![![3052, 331, -334, 246, -266]], ![![5848, 633, -641, 471, -510]], ![![5920, 642, -648, 477, -516]], ![![1282, 142, -138, 104, -111]]]
  g := ![![![3, -57, 48, -29, 24], ![-8, 133, -114, 72, -58], ![12, -165, 133, -85, 72], ![-8, 142, -108, 61, -56], ![2, -150, 142, -80, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-2547, -263, 292, -201, 226]] ![![-13, -6, -2, -2, 0]]
  ![![11391, 1231, -1250, 917, -994]] where
 M := ![![![11391, 1231, -1250, 917, -994]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![11391, 1231, -1250, 917, -994]] ![![-203, -57, 48, -29, 24]]
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


lemma PB547I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB547I6 : PrimesBelowBoundCertificateInterval O 251 307 547 where
  m := 9
  g := ![2, 1, 3, 2, 2, 3, 1, 2, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB547I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2]
    · exact ![I283N0]
    · exact ![I293N0, I293N1]
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
    · exact ![4362470401, 257]
    · exact ![1258284197543]
    · exact ![72361, 72361, 269]
    · exact ![5393580481, 271]
    · exact ![5887339441, 277]
    · exact ![22188041, 281, 281]
    · exact ![1815232161643]
    · exact ![25153757, 85849]
    · exact ![28934443, 307, 307]
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
    · dsimp ; intro j
      fin_cases j
      exact NI281N0
      exact NI281N1
      exact NI281N2
    · dsimp ; intro j
      fin_cases j
      exact NI283N0
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I257N1, I269N2, I271N1, I277N1, I281N1, I281N2, I307N1, I307N2]
  Il := ![[I257N1], [], [I269N2], [I271N1], [I277N1], [I281N1, I281N2], [], [], [I307N1, I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
