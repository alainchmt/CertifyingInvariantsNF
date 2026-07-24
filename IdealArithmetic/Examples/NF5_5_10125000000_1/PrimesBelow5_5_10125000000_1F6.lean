
import IdealArithmetic.Examples.NF5_5_10125000000_1.RI5_5_10125000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17221, -10378, -1920, 366, 204]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-17221, -10378, -1920, 366, 204]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![48, 94, 65, 1, 0], ![123, 40, 199, 0, 1]] where
  M :=![![![-17221, -10378, -1920, 366, 204], ![-5388, -23603, -13328, -330, 1464], ![-19596, 11870, 12671, 910, -1392], ![24484, -5910, -10216, -843, 1088], ![-3648, 19624, 13088, 332, -1369]]]
  hmulB := by decide  
  f := ![![![126755, -172846, -212080, -126158, -50572]], ![![1264844, -1724759, -2116256, -1258870, -504632]], ![![5678188, -7742870, -9500401, -5651390, -2265424]], ![![2030192, -2768402, -3396793, -2020609, -809984]], ![![4960853, -6764700, -8300199, -4937440, -1979229]]]
  g := ![![![-233, -206, -258, 366, 204], ![-660, -199, -1102, -330, 1464], ![420, -70, 897, 910, -1392], ![-268, 116, -669, -843, 1088], ![579, 168, 1027, 332, -1369]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [73, 165, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 193, 153], [208, 63, 104], [0, 1]]
 g := ![![[149, 190, 88], [70, 244], [187, 242], [46, 123], [207, 9], [65, 58], [125, 1], []], ![[227, 111, 13, 153], [247, 211], [160, 239], [223, 95], [207, 133], [54, 133], [44, 114], [128, 22]], ![[190, 8, 111, 92], [81, 124], [86, 23], [224, 84], [31, 116], [13, 187], [196, 241], [177, 22]]]
 h' := ![![[174, 193, 153], [163, 168, 208], [90, 7, 66], [190, 125, 146], [174, 14, 196], [76, 104, 3], [127, 119, 40], [0, 0, 1], [0, 1]], ![[208, 63, 104], [116, 141, 1], [160, 90, 89], [180, 207, 53], [221, 250, 98], [13, 214, 167], [247, 202, 167], [115, 234, 63], [174, 193, 153]], ![[0, 1], [93, 205, 48], [98, 160, 102], [145, 182, 58], [250, 250, 220], [171, 196, 87], [116, 193, 50], [17, 23, 193], [208, 63, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 71], []]
 b := ![[], [42, 145, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [73, 165, 132, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51183221317, -72189065457, -88040708108, -53763006667, -22662837492]
  a := ![-25, -17, 5, -1, -50]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![21086912657, 22910688953, 30803343915, -53763006667, -22662837492]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![126755, -172846, -212080, -126158, -50572]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![126755, -172846, -212080, -126158, -50572]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![194, 193, 1, 0, 0], ![80, 210, 0, 1, 0], ![179, 131, 0, 0, 1]] where
  M :=![![![126755, -172846, -212080, -126158, -50572], ![1264844, -1724759, -2116256, -1258870, -504632], ![5678188, -7742870, -9500401, -5651390, -2265424], ![27697548, -37768810, -46341832, -27566799, -11050464], ![78795184, -107446352, -131835264, -78423236, -31436841]]]
  hmulB := by decide  
  f := ![![![-17221, -10378, -1920, 366, 204]], ![![-5388, -23603, -13328, -330, 1464]], ![![-17122, -25513, -11409, 32, 1248]], ![![-9668, -22540, -11528, -159, 1264]], ![![-14755, -19183, -8080, 88, 883]]]
  g := ![![![235079, 287458, -212080, -126158, -50572], ![2345748, 2868413, -2116256, -1258870, -504632], ![10530654, 12877031, -9500401, -5651390, -2265424], ![51367276, 62812620, -46341832, -27566799, -11050464], ![146131867, 178692083, -131835264, -78423236, -31436841]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [122, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 256], [0, 1]]
 g := ![![[73, 158], [46], [36], [16], [225], [21], [211], [1]], ![[0, 99], [46], [36], [16], [225], [21], [211], [1]]]
 h' := ![![[89, 256], [106, 71], [249, 139], [23, 6], [113, 253], [249, 15], [193, 147], [135, 89], [0, 1]], ![[0, 1], [0, 186], [27, 118], [43, 251], [14, 4], [42, 242], [169, 110], [89, 168], [89, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [214, 180]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [122, 168, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1854803, 4038157, 4588552, 3603574, 2169334]
  a := ![-37, -48, -6, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6103621, -7480489, 4588552, 3603574, 2169334]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-17221, -10378, -1920, 366, 204]] ![![126755, -172846, -212080, -126158, -50572]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207, -314, -162, -14, 22]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-207, -314, -162, -14, 22]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![7, 101, 55, 1, 0], ![7, 50, 195, 0, 1]] where
  M :=![![![-207, -314, -162, -14, 22], ![-688, -45, 280, 108, -56], ![1292, -1016, -1413, -360, 244], ![-3676, 2992, 4084, 1031, -692], ![5536, -3770, -5544, -1418, 969]]]
  hmulB := by decide  
  f := ![![![-1577, 1174, 1106, 74, -122]], ![![3808, -2835, -2680, -180, 296]], ![![-6524, 4856, 4605, 312, -508]], ![![79, -59, -53, -3, 6]], ![![-4173, 3106, 2947, 200, -325]]]
  g := ![![![-1, 0, -14, -14, 22], ![-4, -31, 20, 108, -56], ![8, 88, -111, -360, 244], ![-23, -253, 313, 1031, -692], ![33, 346, -443, -1418, 969]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [188, 86, 196, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 213, 23], [202, 49, 240], [0, 1]]
 g := ![![[156], [255, 143, 61], [206, 259, 75], [174, 145], [170, 162], [206, 153], [67, 1], []], ![[237, 2, 63, 244], [0, 211, 37, 187], [205, 102, 178, 256], [1, 204], [183, 190], [43, 9], [182, 34], [5, 3]], ![[248, 241, 111, 19], [190, 67, 17, 40], [195, 154, 69, 15], [124, 256], [137, 95], [8, 44], [4, 133], [51, 3]]]
 h' := ![![[128, 213, 23], [189, 122], [196, 168, 245], [33, 7, 148], [50, 62, 150], [191, 92, 62], [28, 99, 195], [0, 0, 1], [0, 1]], ![[202, 49, 240], [25, 212, 176], [133, 36, 89], [119, 70, 49], [192, 240, 97], [77, 182, 157], [43, 181, 260], [190, 145, 49], [128, 213, 23]], ![[0, 1], [111, 192, 87], [85, 59, 192], [242, 186, 66], [161, 224, 16], [77, 252, 44], [23, 246, 71], [182, 118, 213], [202, 49, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183, 108], []]
 b := ![[], [136, 163, 224], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [188, 86, 196, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2123575118, -2972983248, -3630793051, -2204752214, -919456868]
  a := ![-8, -7, 1, -1, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![91228284, 1010189482, 1128991133, -2204752214, -919456868]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1577, 1174, 1106, 74, -122]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-1577, 1174, 1106, 74, -122]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![234, 209, 1, 0, 0], ![12, 199, 0, 1, 0], ![113, 57, 0, 0, 1]] where
  M :=![![![-1577, 1174, 1106, 74, -122], ![3808, -2835, -2680, -180, 296], ![-6524, 4856, 4605, 312, -508], ![6028, -4480, -4276, -287, 476], ![-4680, 3490, 3344, 242, -361]]]
  hmulB := by decide  
  f := ![![![-207, -314, -162, -14, 22]], ![![-688, -45, 280, 108, -56]], ![![-726, -319, 73, 72, -24]], ![![-544, -37, 220, 85, -44]], ![![-217, -159, -30, 12, 1]]]
  g := ![![![-941, -904, 1106, 74, -122], ![2280, 2191, -2680, -180, 296], ![-3918, -3767, 4605, 312, -508], ![3636, 3495, -4276, -287, 476], ![-2849, -2749, 3344, 242, -361]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [224, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [153, 262], [0, 1]]
 g := ![![[186, 256], [99, 70], [143, 88], [66], [26], [176], [2], [1]], ![[167, 7], [26, 193], [194, 175], [66], [26], [176], [2], [1]]]
 h' := ![![[153, 262], [179, 16], [54, 99], [257, 80], [24, 131], [204, 17], [21, 142], [39, 153], [0, 1]], ![[0, 1], [260, 247], [210, 164], [136, 183], [79, 132], [175, 246], [181, 121], [41, 110], [153, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [243]]
 b := ![[], [239, 253]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [224, 110, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3001318, 6805062, 7681326, 6117306, 3769958]
  a := ![52, 39, -8, -1, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8744656, -11524044, 7681326, 6117306, 3769958]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-207, -314, -162, -14, 22]] ![![-1577, 1174, 1106, 74, -122]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4735, 4900, 1852, -22, -212]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![4735, 4900, 1852, -22, -212]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![51, 162, 85, 1, 0], ![65, 224, 188, 0, 1]] where
  M :=![![![4735, 4900, 1852, -22, -212], ![6316, 5339, 1364, -302, -88], ![-2140, 2564, 3199, 830, -560], ![6072, -8978, -10148, -2385, 1704], ![-15892, 5678, 11880, 3446, -2133]]]
  hmulB := by decide  
  f := ![![![451, -584, -708, -402, -156]], ![![3876, -5365, -6604, -3978, -1608]], ![![18204, -24680, -30245, -17902, -7152]], ![![8497, -11584, -14213, -8453, -3388]], ![![16987, -23122, -28360, -16844, -6745]]]
  g := ![![![73, 208, 162, -22, -212], ![102, 275, 162, -302, -88], ![-30, -24, 141, 830, -560], ![63, -16, -475, -2385, 1704], ![-197, -278, 446, 3446, -2133]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [237, 232, 232, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [228, 192, 6], [78, 76, 263], [0, 1]]
 g := ![![[108, 232, 143], [154, 78], [26, 67, 224], [247, 52, 126], [34, 67], [56, 224], [37, 1], []], ![[108, 28, 31, 255], [143, 207], [141, 201, 29, 213], [41, 134, 221, 55], [149, 232], [52, 222], [69, 127], [139, 36]], ![[63, 236, 253, 23], [93, 53], [181, 26, 238, 265], [171, 230, 149, 203], [28, 117], [205, 166], [13, 11], [151, 36]]]
 h' := ![![[228, 192, 6], [173, 193, 120], [25, 265, 207], [103, 195, 61], [48, 118, 156], [6, 85, 41], [108, 56, 61], [0, 0, 1], [0, 1]], ![[78, 76, 263], [95, 158, 56], [19, 264, 106], [137, 127, 157], [150, 136, 190], [61, 131, 129], [192, 70, 130], [211, 235, 76], [228, 192, 6]], ![[0, 1], [53, 187, 93], [263, 9, 225], [81, 216, 51], [232, 15, 192], [120, 53, 99], [4, 143, 78], [156, 34, 192], [78, 76, 263]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 3], []]
 b := ![[], [70, 90, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [237, 232, 232, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124541270084, -176628968070, -215204311108, -131968287722, -56057059481]
  a := ![-35, -20, 10, 2, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![39028374759, 125498196902, 80077425010, -131968287722, -56057059481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, -73, -100, -25, 16]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![97, -73, -100, -25, 16]] 
 ![![269, 0, 0, 0, 0], ![159, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![124, 0, 0, 1, 0], ![175, 0, 0, 0, 1]] where
  M :=![![![97, -73, -100, -25, 16], ![-530, 388, 544, 129, -100], ![1894, -1443, -2013, -535, 308], ![-4890, 3491, 4980, 1116, -1020], ![7884, -6312, -8724, -2610, 1007]]]
  hmulB := by decide  
  f := ![![![-75091, -62503, -18392, 1347, 1976]], ![![-44595, -37311, -11052, 794, 1188]], ![![-53794, -44517, -13001, 973, 1396]], ![![-34282, -28825, -8592, 606, 924]], ![![-48833, -40355, -11764, 885, 1263]]]
  g := ![![![116, -73, -100, -25, 16], ![-614, 388, 544, 129, -100], ![2343, -1443, -2013, -535, 308], ![-5487, 3491, 4980, 1116, -1020], ![10535, -6312, -8724, -2610, 1007]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1037, 770, 722, 52, -81]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-1037, 770, 722, 52, -81]] 
 ![![269, 0, 0, 0, 0], ![210, 1, 0, 0, 0], ![172, 0, 1, 0, 0], ![127, 0, 0, 1, 0], ![243, 0, 0, 0, 1]] where
  M :=![![![-1037, 770, 722, 52, -81], ![2534, -1894, -1804, -147, 208], ![-4534, 3381, 3315, 319, -398], ![5022, -3743, -3996, -552, 534], ![-4774, 3562, 4042, 672, -577]]]
  hmulB := by decide  
  f := ![![![9597, -7132, -7848, -696, 851]], ![![7392, -5496, -6048, -539, 654]], ![![6346, -4721, -5197, -469, 558]], ![![4349, -3267, -3604, -366, 359]], ![![9013, -6790, -7498, -792, 726]]]
  g := ![![![-1018, 770, 722, 52, -81], ![2523, -1894, -1804, -147, 208], ![-4567, 3381, 3315, 319, -398], ![5274, -3743, -3996, -552, 534], ![-5179, 3562, 4042, 672, -577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![4735, 4900, 1852, -22, -212]] ![![97, -73, -100, -25, 16]]
  ![![-193845, 144451, 203952, 51673, -34868]] where
 M := ![![![-193845, 144451, 203952, 51673, -34868]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![-193845, 144451, 203952, 51673, -34868]] ![![-1037, 770, 722, 52, -81]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![68299369, -50900987, -71866578, -18208341, 12286575]]]
 hmul := by decide  
 g := ![![![![253901, -189223, -267162, -67689, 45675]]]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 0, 0, 0, 0]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![271, 0, 0, 0, 0]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![0, 0, 0, 0, 271]] where
  M :=![![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![0, 0, 0, 0, 271]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 5 2 8 [249, 22, 105, 71, 35, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 11, 65, 232, 218], [1, 213, 255, 37, 156], [256, 66, 172, 121, 122], [142, 251, 50, 152, 46], [0, 1]]
 g := ![![[202, 190, 252, 234, 259], [197, 86, 136, 10, 121], [48, 51, 231, 247, 39], [206, 110, 33, 252, 259], [18, 37, 176, 233], [201, 70, 236, 1], [], []], ![[173, 181, 3, 163, 249, 197, 35, 192], [155, 203, 159, 58, 96, 217, 117, 235], [10, 135, 262, 125, 254, 242, 37, 84], [231, 207, 41, 41, 167, 185, 150, 215], [166, 221, 126, 160], [153, 136, 105, 248], [141, 219, 162, 233], [177, 230, 127, 99]], ![[194, 182, 60, 217, 209, 107, 267, 155], [14, 9, 98, 14, 28, 103, 44, 2], [138, 122, 72, 110, 50, 83, 107, 2], [128, 256, 264, 192, 23, 172, 257, 88], [138, 245, 137, 224], [237, 155, 233, 79], [3, 88, 190, 166], [153, 206, 155, 217]], ![[221, 36, 225, 166, 167, 103, 52, 49], [231, 162, 188, 57, 163, 8, 235, 124], [221, 263, 195, 85, 220, 119, 151, 247], [78, 124, 29, 236, 163, 131, 260, 233], [195, 3, 150, 22], [70, 20, 67, 248], [246, 34, 194, 85], [120, 109, 178, 250]], ![[217, 230, 19, 140, 100, 13, 203, 267], [130, 80, 77, 82, 266, 47, 201, 182], [208, 78, 197, 77, 269, 137, 0, 97], [91, 188, 10, 40, 243, 23, 13, 54], [254, 167, 215, 164], [180, 0, 194, 252], [267, 237, 151, 144], [224, 202, 86, 219]]]
 h' := ![![[108, 11, 65, 232, 218], [269, 239, 198, 65, 157], [243, 0, 90, 115, 260], [196, 209, 135, 6, 44], [204, 102, 80, 15, 157], [86, 99, 162, 38, 49], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 213, 255, 37, 156], [71, 50, 81, 113, 206], [95, 182, 150, 22, 181], [116, 263, 224, 116, 134], [82, 257, 154, 251, 245], [148, 157, 72, 31, 206], [247, 243, 191, 199, 178], [111, 19, 85, 117, 222], [108, 11, 65, 232, 218]], ![[256, 66, 172, 121, 122], [18, 215, 149, 102, 24], [184, 168, 143, 42, 196], [20, 51, 113, 148, 196], [105, 96, 129, 191, 60], [209, 110, 190, 82, 123], [12, 12, 143, 71, 86], [115, 237, 237, 69, 232], [1, 213, 255, 37, 156]], ![[142, 251, 50, 152, 46], [245, 96, 14, 137, 191], [257, 155, 187, 235, 47], [6, 25, 76, 51, 89], [83, 135, 54, 32, 253], [20, 48, 97, 84, 70], [169, 5, 245, 31, 93], [155, 217, 38, 151, 76], [256, 66, 172, 121, 122]], ![[0, 1], [267, 213, 100, 125, 235], [17, 37, 243, 128, 129], [97, 265, 265, 221, 79], [153, 223, 125, 53, 98], [255, 128, 21, 36, 94], [38, 11, 234, 241, 184], [160, 69, 181, 205, 12], [142, 251, 50, 152, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 107, 246, 108], [], [], []]
 b := ![[], [144, 143, 172, 224, 181], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 5
  hpos := by decide
  P := [249, 22, 105, 71, 35, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41254767408976815, 57052450890651916, 69825492524338208, 41999271907129740, 17205166098280272]
  a := ![8, -2, -6, -10, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-152231614055265, 210525649042996, 257658644001248, 154978863125940, 63487697779632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 1461660310351 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def PBC271 : ContainsPrimesAboveP 271 ![I271N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI271N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![271, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 271 (by decide) 𝕀

instance hp277 : Fact (Nat.Prime 277) := {out := by norm_num}

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37309, 28816, 26312, 1688, -2892]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-37309, 28816, 26312, 1688, -2892]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![249, 106, 126, 1, 0], ![234, 186, 179, 0, 1]] where
  M :=![![![-37309, 28816, 26312, 1688, -2892], ![90136, -66049, -61424, -4012, 6752], ![-150360, 112260, 103715, 6732, -11400], ![132664, -99468, -91760, -5945, 10088], ![-101992, 75352, 69880, 4560, -7677]]]
  hmulB := by decide  
  f := ![![![3815, -2800, -3080, -248, 348]], ![![-10936, 8027, 8816, 700, -992]], ![![21048, -15444, -16921, -1308, 1896]], ![![8731, -6406, -7022, -545, 788]], ![![9550, -7006, -7671, -588, 859]]]
  g := ![![![791, 1400, 1196, 1688, -2892], ![-1772, -3237, -2760, -4012, 6752], ![3036, 5484, 4679, 6732, -11400], ![-2699, -4858, -4146, -5945, 10088], ![2018, 3682, 3139, 4560, -7677]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 3 2 8 [63, 47, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 164, 102], [158, 112, 175], [0, 1]]
 g := ![![[131, 122, 188], [276, 237], [147, 163, 144], [122, 92], [20, 242, 146], [28, 190], [215, 1], []], ![[12, 56, 182, 267], [49, 136], [150, 71, 224, 237], [60, 186], [28, 134, 264, 47], [66, 164], [90, 79], [24, 155]], ![[205, 263, 121, 79], [60, 116], [154, 216, 186, 121], [3, 198], [242, 99, 263, 229], [159, 276], [84, 27], [228, 155]]]
 h' := ![![[57, 164, 102], [59, 275, 241], [157, 245, 121], [183, 21, 12], [125, 198, 170], [128, 114, 223], [28, 81, 196], [0, 0, 1], [0, 1]], ![[158, 112, 175], [15, 196, 196], [206, 162, 39], [64, 130, 162], [62, 20, 179], [83, 92, 40], [232, 59, 21], [75, 47, 112], [57, 164, 102]], ![[0, 1], [126, 83, 117], [177, 147, 117], [234, 126, 103], [223, 59, 205], [17, 71, 14], [184, 137, 60], [74, 230, 164], [158, 112, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92, 217], []]
 b := ![[], [83, 103, 245], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 3
  hpos := by decide
  P := [63, 47, 62, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-123069931285, 173958628239, 212069153224, 129715102233, 54851902311]
  a := ![40, 24, -6, 1, 67]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-163384388188, -85842223965, -93684203039, 129715102233, 54851902311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 21253933 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3815, 2800, 3080, 248, -348]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-3815, 2800, 3080, 248, -348]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![77, 152, 1, 0, 0], ![207, 2, 0, 1, 0], ![83, 46, 0, 0, 1]] where
  M :=![![![-3815, 2800, 3080, 248, -348], ![10936, -8027, -8816, -700, 992], ![-21048, 15444, 16921, 1308, -1896], ![24280, -17820, -19376, -1395, 2120], ![-19144, 14008, 15064, 912, -1639]]]
  hmulB := by decide  
  f := ![![![37309, -28816, -26312, -1688, 2892]], ![![-90136, 66049, 61424, 4012, -6752]], ![![-38547, 27828, 26017, 1708, -2860]], ![![26751, -20698, -18888, -1211, 2076]], ![![-3421, 2062, 2064, 144, -227]]]
  g := ![![![-951, -1624, 3080, 248, -348], ![2716, 4649, -8816, -700, 992], ![-5189, -8924, 16921, 1308, -1896], ![5881, 10226, -19376, -1395, 2120], ![-4447, -7950, 15064, 912, -1639]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P1 : CertificateIrreducibleZModOfList' 277 2 2 8 [111, 198, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 276], [0, 1]]
 g := ![![[159, 171], [36], [182, 157], [63], [75, 34], [30], [147], [1]], ![[95, 106], [36], [120, 120], [63], [268, 243], [30], [147], [1]]]
 h' := ![![[79, 276], [243, 123], [19, 271], [157, 59], [262, 127], [68, 158], [159, 169], [166, 79], [0, 1]], ![[0, 1], [265, 154], [99, 6], [109, 218], [46, 150], [85, 119], [214, 108], [36, 198], [79, 276]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [93, 194]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N1 : CertifiedPrimeIdeal' SI277N1 277 where
  n := 2
  hpos := by decide
  P := [111, 198, 1]
  hirr := P277P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12927, 41870, 45094, 39914, 28954]
  a := ![4, 1, -2, -1, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-51085, -29690, 45094, 39914, 28954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N1 B_one_repr
lemma NI277N1 : Nat.card (O ⧸ I277N1) = 76729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-37309, 28816, 26312, 1688, -2892]] ![![-3815, 2800, 3080, 248, -348]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5303, 3986, 3290, 172, -353]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-5303, 3986, 3290, 172, -353]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![196, 252, 1, 0, 0], ![64, 86, 0, 1, 0], ![257, 27, 0, 0, 1]] where
  M :=![![![-5303, 3986, 3290, 172, -353], ![10934, -8264, -6492, -299, 688], ![-16086, 12197, 9041, 343, -942], ![9006, -6951, -3740, 70, 342], ![-5670, 4426, 1850, -160, -139]]]
  hmulB := by decide  
  f := ![![![9571, -13096, -16052, -9544, -3825]], ![![95662, -130502, -160104, -95235, -38176]], ![![93994, -128253, -157335, -93585, -37514]], ![![38914, -53091, -65132, -38742, -15530]], ![![39159, -53444, -65558, -38993, -15630]]]
  g := ![![![-2030, -2955, 3290, 172, -353], ![4006, 5818, -6492, -299, 688], ![-5580, -8079, 9041, 343, -942], ![2312, 3275, -3740, 70, 342], ![-1147, -1581, 1850, -160, -139]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [193, 220, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 280], [0, 1]]
 g := ![![[138, 273], [128], [163], [183, 49], [229, 109], [81], [68], [1]], ![[212, 8], [128], [163], [81, 232], [134, 172], [81], [68], [1]]]
 h' := ![![[61, 280], [49, 58], [276, 213], [87, 238], [201, 7], [98, 59], [240, 272], [88, 61], [0, 1]], ![[0, 1], [215, 223], [62, 68], [274, 43], [66, 274], [44, 222], [253, 9], [156, 220], [61, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [190]]
 b := ![[], [53, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [193, 220, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2215024, 5431099, 6065308, 4976506, 3175394]
  a := ![49, 29, -10, -4, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8276114, -7248191, 6065308, 4976506, 3175394]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9631, -7182, -6638, -432, 730]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![9631, -7182, -6638, -432, 730]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![266, 225, 1, 0, 0], ![3, 201, 0, 1, 0], ![26, 11, 0, 0, 1]] where
  M :=![![![9631, -7182, -6638, -432, 730], ![-22764, 16981, 15700, 1026, -1728], ![38328, -28588, -26455, -1742, 2916], ![-34100, 25434, 23624, 1605, -2620], ![26276, -19600, -18288, -1288, 2043]]]
  hmulB := by decide  
  f := ![![![-41, 162, 138, 40, 6]], ![![-100, 433, 484, 350, 160]], ![![-126, 509, 529, 324, 136]], ![![-99, 349, 394, 279, 126]], ![![-90, 143, 168, 98, 39]]]
  g := ![![![6255, 5570, -6638, -432, 730], ![-14794, -13177, 15700, 1026, -1728], ![24928, 22213, -26455, -1742, 2916], ![-22259, -19871, 23624, 1605, -2620], ![17230, 15415, -18288, -1288, 2043]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [23, 194, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 280], [0, 1]]
 g := ![![[265, 18], [144], [247], [245, 249], [73, 106], [175], [263], [1]], ![[145, 263], [144], [247], [271, 32], [22, 175], [175], [263], [1]]]
 h' := ![![[87, 280], [261, 166], [164, 12], [266, 182], [7, 116], [74, 54], [100, 52], [258, 87], [0, 1]], ![[0, 1], [91, 115], [84, 269], [83, 99], [264, 165], [276, 227], [128, 229], [240, 194], [87, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [247, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [23, 194, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-492847, 1151110, 1292862, 1039442, 652718]
  a := ![22, 13, -6, -1, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1297093, -1800180, 1292862, 1039442, 652718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -13, -14, -5, -2]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![13, -13, -14, -5, -2]] 
 ![![281, 0, 0, 0, 0], ![172, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![103, 0, 0, 0, 1]] where
  M :=![![![13, -13, -14, -5, -2], ![50, -72, -96, -61, -20], ![214, -313, -363, -225, -112], ![1430, -1819, -2280, -1284, -440], ![3116, -4462, -5412, -3340, -1449]]]
  hmulB := by decide  
  f := ![![![156405, 155033, 55406, -1977, -6038]], ![![96366, 95578, 34172, -1217, -3724]], ![![8449, 8312, 2955, -108, -322]], ![![15819, 15730, 5634, -199, -614]], ![![56955, 56399, 20142, -721, -2195]]]
  g := ![![![10, -13, -14, -5, -2], ![63, -72, -96, -61, -20], ![276, -313, -363, -225, -112], ![1534, -1819, -2280, -1284, -440], ![3907, -4462, -5412, -3340, -1449]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-5303, 3986, 3290, 172, -353]] ![![9631, -7182, -6638, -432, 730]]
  ![![-30852005, 23011340, 21263556, 1380076, -2337177]] where
 M := ![![![-30852005, 23011340, 21263556, 1380076, -2337177]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-30852005, 23011340, 21263556, 1380076, -2337177]] ![![13, -13, -14, -5, -2]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-9242933, 6892087, 6397246, 421781, -705029]]]
 hmul := by decide  
 g := ![![![![-32893, 24527, 22766, 1501, -2509]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5769, 4254, 4694, 410, -514]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-5769, 4254, 4694, 410, -514]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![231, 203, 219, 1, 0], ![163, 201, 18, 0, 1]] where
  M :=![![![-5769, 4254, 4694, 410, -514], ![16240, -11727, -12872, -788, 1640], ![-33508, 25464, 28297, 3496, -2396], ![31316, -18752, -19516, 4181, 6172], ![-50240, 48926, 57176, 21102, 4783]]]
  hmulB := by decide  
  f := ![![![1085, 1014, 362, -6, -42]], ![![1248, 1243, 360, -68, -24]], ![![-332, 456, 651, 200, -124]], ![![1529, 2065, 1049, 99, -146]], ![![1477, 1501, 516, -36, -51]]]
  g := ![![![-59, 86, -268, 410, -514], ![-244, -641, 460, -788, 1640], ![-1592, -716, -2453, 3496, -2396], ![-6857, -7449, -3697, 4181, 6172], ![-20157, -18361, -16432, 21102, 4783]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [148, 129, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [268, 148, 22], [175, 134, 261], [0, 1]]
 g := ![![[220, 170, 168], [149, 256, 90], [103, 275], [131, 278, 10], [57, 195, 155], [185, 1], [160, 1], []], ![[209, 1, 232, 202], [236, 40, 234, 213], [187, 96], [82, 152, 234, 224], [208, 85, 204, 68], [60, 28], [277, 127], [184, 201]], ![[188, 116, 176, 236], [200, 279, 270, 265], [238, 70], [32, 163, 79, 11], [27, 37, 105, 25], [53, 281], [200, 113], [228, 201]]]
 h' := ![![[268, 148, 22], [22, 264, 122], [115, 59, 72], [139, 58, 29], [54, 55, 24], [45, 78, 167], [92, 154, 1], [0, 0, 1], [0, 1]], ![[175, 134, 261], [139, 83, 82], [68, 2, 192], [259, 186, 68], [263, 136, 181], [9, 139, 39], [207, 243, 126], [161, 91, 134], [268, 148, 22]], ![[0, 1], [210, 219, 79], [103, 222, 19], [210, 39, 186], [196, 92, 78], [241, 66, 77], [151, 169, 156], [277, 192, 148], [175, 134, 261]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67, 38], []]
 b := ![[], [95, 203, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [148, 129, 123, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9225411024, 13019145222, 15875598125, 9698643031, 4092284340]
  a := ![16, 10, -3, 1, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10306198935, -9817507217, -7709499448, 9698643031, 4092284340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1085, -1014, -362, 6, 42]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-1085, -1014, -362, 6, 42]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![173, 65, 1, 0, 0], ![75, 281, 0, 1, 0], ![208, 186, 0, 0, 1]] where
  M :=![![![-1085, -1014, -362, 6, 42], ![-1248, -1243, -360, 68, 24], ![332, -456, -651, -200, 124], ![-1436, 2032, 2404, 593, -412], ![3736, -1450, -2944, -858, 531]]]
  hmulB := by decide  
  f := ![![![5769, -4254, -4694, -410, 514]], ![![-16240, 11727, 12872, 788, -1640]], ![![-85, 3, -13, -82, -54]], ![![-14707, 10583, 11606, 659, -1514]], ![![-6256, 4408, 4808, 142, -717]]]
  g := ![![![185, 46, -362, 6, 42], ![180, -5, -360, 68, 24], ![361, 265, -651, -200, 124], ![-1329, -863, 2404, 593, -412], ![1650, 1174, -2944, -858, 531]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P1 : CertificateIrreducibleZModOfList' 283 2 2 8 [179, 188, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 282], [0, 1]]
 g := ![![[205, 117], [145, 207], [150], [160, 110], [195, 269], [57], [252], [1]], ![[0, 166], [0, 76], [150], [139, 173], [280, 14], [57], [252], [1]]]
 h' := ![![[95, 282], [81, 20], [171, 168], [226, 198], [187, 257], [122, 77], [234, 118], [104, 95], [0, 1]], ![[0, 1], [0, 263], [0, 115], [75, 85], [264, 26], [79, 206], [124, 165], [73, 188], [95, 282]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [37, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N1 : CertifiedPrimeIdeal' SI283N1 283 where
  n := 2
  hpos := by decide
  P := [179, 188, 1]
  hirr := P283P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13707234, 30542006, 34573954, 27377676, 16693966]
  a := ![-105, -72, 16, 0, -217]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-40709088, -45989292, 34573954, 27377676, 16693966]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N1 B_one_repr
lemma NI283N1 : Nat.card (O ⧸ I283N1) = 80089 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-5769, 4254, 4694, 410, -514]] ![![-1085, -1014, -362, 6, 42]]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-859, 509, 612, 51, -70]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-859, 509, 612, 51, -70]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![209, 89, 8, 196, 1]] where
  M :=![![![-859, 509, 612, 51, -70], ![2202, -1768, -1884, -157, 204], ![-4318, 3117, 3411, 211, -416], ![5350, -4043, -4472, -568, 320], ![-3076, 1822, 1744, -636, -661]]]
  hmulB := by decide  
  f := ![![![289, -217, -200, -13, 22]], ![![-686, 510, 472, 31, -52]], ![![1154, -861, -797, -53, 88]], ![![-1030, 769, 716, 50, -80]], ![![-657, 489, 456, 32, -51]]]
  g := ![![![47, 23, 4, 47, -70], ![-138, -68, -12, -137, 204], ![282, 137, 23, 279, -416], ![-210, -111, -24, -216, 320], ![461, 207, 24, 440, -661]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [198, 259, 6, 199, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [179, 157, 182, 122], [126, 223, 189, 91], [82, 205, 215, 80], [0, 1]]
 g := ![![[116, 74, 184, 216], [237, 17, 21], [194, 53, 154, 253], [49, 201, 277], [251, 130, 277], [262, 98, 266, 46], [1], []], ![[199, 120, 253, 103, 122, 86], [113, 287, 14], [161, 284, 219, 34, 234, 192], [212, 196, 167], [284, 234, 237], [164, 107, 83, 288, 249, 70], [69, 31, 49], [198, 186, 234]], ![[3, 66, 74, 267, 156, 149], [240, 126, 59], [16, 4, 188, 147, 253, 292], [212, 10, 255], [49, 178, 90], [52, 94, 70, 256, 37, 91], [290, 153, 240], [141, 30, 77]], ![[169, 240, 277, 85, 123, 195], [88, 158, 272], [14, 210, 13, 43, 36, 114], [50, 164, 132], [122, 211, 253], [194, 46, 236, 195, 4, 259], [145, 235, 226], [178, 190, 247]]]
 h' := ![![[179, 157, 182, 122], [209, 201, 212, 41], [264, 133, 109, 30], [145, 72, 63, 245], [44, 261, 255, 259], [278, 287, 88, 259], [95, 34, 287, 94], [0, 0, 1], [0, 1]], ![[126, 223, 189, 91], [208, 121, 206, 169], [263, 116, 199, 166], [161, 91, 36, 178], [112, 80, 171, 162], [214, 116, 77, 108], [276, 161, 211, 268], [162, 33, 264, 286], [179, 157, 182, 122]], ![[82, 205, 215, 80], [260, 52, 267, 16], [30, 183, 121, 135], [161, 62, 105, 194], [112, 215, 110, 264], [261, 264, 148, 267], [263, 290, 23, 1], [264, 259, 245, 151], [126, 223, 189, 91]], ![[0, 1], [59, 212, 194, 67], [279, 154, 157, 255], [265, 68, 89, 262], [221, 30, 50, 194], [75, 212, 273, 245], [136, 101, 65, 223], [194, 1, 76, 149], [82, 205, 215, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [220, 166, 61], []]
 b := ![[], [], [131, 163, 71, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [198, 259, 6, 199, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9518440228476472, 13032888172489305, 15979313001195771, 9536446541238471, 3847538855770335]
  a := ![-38, -25, 7, -1, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2776976317694459, -1124225494850070, -50515351006713, -2541232659350673, 3847538855770335]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![289, -217, -200, -13, 22]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![289, -217, -200, -13, 22]] 
 ![![293, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![128, 0, 1, 0, 0], ![172, 0, 0, 1, 0], ![271, 0, 0, 0, 1]] where
  M :=![![![289, -217, -200, -13, 22], ![-686, 510, 472, 31, -52], ![1154, -861, -797, -53, 88], ![-1030, 769, 716, 50, -80], ![800, -596, -560, -42, 63]]]
  hmulB := by decide  
  f := ![![![-859, 509, 612, 51, -70]], ![![-271, 159, 192, 16, -22]], ![![-390, 233, 279, 23, -32]], ![![-486, 285, 344, 28, -40]], ![![-805, 477, 572, 45, -67]]]
  g := ![![![146, -217, -200, -13, 22], ![-344, 510, 472, 31, -52], ![581, -861, -797, -53, 88], ![-521, 769, 716, 50, -80], ![407, -596, -560, -42, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-859, 509, 612, 51, -70]] ![![289, -217, -200, -13, 22]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159, 106, 98, 16, 4]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-159, 106, 98, 16, 4]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![0, 0, 307, 0, 0], ![0, 0, 0, 307, 0], ![37, 180, 178, 4, 1]] where
  M :=![![![-159, 106, 98, 16, 4], ![-88, 161, 340, 256, 64], ![-660, 1054, 1015, 692, 480], ![-6464, 7584, 9792, 5101, 1352], ![-9456, 14900, 17668, 11656, 5677]]]
  hmulB := by decide  
  f := ![![![1083, -802, -882, -72, 100]], ![![-3144, 2299, 2540, 208, -288]], ![![6100, -4478, -4939, -404, 560]], ![![-7232, 5312, 5856, 479, -664]], ![![1749, -1290, -1420, -116, 161]]]
  g := ![![![-1, -2, -2, 0, 4], ![-8, -37, -36, 0, 64], ![-60, -278, -275, -4, 480], ![-184, -768, -752, -1, 1352], ![-715, -3280, -3234, -36, 5677]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 4 2 8 [207, 219, 232, 47, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 227, 146, 7], [173, 101, 18, 205], [0, 285, 143, 95], [0, 1]]
 g := ![![[182, 113, 208, 66], [16, 112, 194, 175], [123, 206, 113], [135, 231, 65], [238, 261, 264, 222], [204, 24, 261, 60], [1], []], ![[165, 274, 263, 183, 278, 54], [46, 76, 132, 109, 65, 225], [100, 80, 168], [245, 274, 289], [97, 299, 230, 50, 47, 11], [142, 61, 100, 249, 296, 250], [253, 107, 89], [125, 48, 49]], ![[99, 169, 295, 261, 275, 228], [167, 73, 228, 137, 204, 161], [84, 191, 134], [293], [256, 10, 248, 42, 228, 195], [279, 55, 21, 182, 131, 84], [105, 155, 277], [47, 75, 273]], ![[0, 63, 299, 173, 215, 297], [66, 258, 158, 65, 127, 208], [163, 199, 259], [133, 92, 222], [16, 89, 99, 142, 300, 207], [128, 117, 247, 62, 128, 224], [47, 134, 19], [20, 253, 122]]]
 h' := ![![[87, 227, 146, 7], [65, 165, 46, 56], [295, 167, 271, 92], [125, 306, 54, 179], [161, 83, 28, 267], [138, 266, 19, 23], [100, 88, 75, 260], [0, 0, 1], [0, 1]], ![[173, 101, 18, 205], [289, 301, 235, 278], [270, 129, 146, 171], [44, 135, 28, 274], [248, 151, 236, 17], [269, 118, 203, 22], [228, 183, 231, 116], [114, 38, 262, 157], [87, 227, 146, 7]], ![[0, 285, 143, 95], [52, 292, 143, 101], [151, 148, 218, 207], [276, 108, 1, 21], [270, 264, 268], [91, 205, 28, 120], [222, 217, 33, 49], [245, 225, 129, 82], [173, 101, 18, 205]], ![[0, 1], [153, 163, 190, 179], [91, 170, 286, 144], [26, 65, 224, 140], [65, 116, 82, 23], [213, 25, 57, 142], [192, 126, 275, 189], [158, 44, 222, 68], [0, 285, 143, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [76, 244, 64], []]
 b := ![[], [], [193, 22, 305, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 4
  hpos := by decide
  P := [207, 219, 232, 47, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9351905491117300, 12794845727168901, 15689671083921860, 9357785345564734, 3770845585138582]
  a := ![39, 28, -6, 5, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-484928964629462, -2169242213673537, -2135247045833048, -18650153078142, 3770845585138582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 8882874001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1083, 802, 882, 72, -100]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-1083, 802, 882, 72, -100]] 
 ![![307, 0, 0, 0, 0], ![291, 1, 0, 0, 0], ![187, 0, 1, 0, 0], ![276, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![-1083, 802, 882, 72, -100], ![3144, -2299, -2540, -208, 288], ![-6100, 4478, 4939, 404, -560], ![7232, -5312, -5856, -479, 664], ![-5920, 4340, 4788, 392, -543]]]
  hmulB := by decide  
  f := ![![![159, -106, -98, -16, -4]], ![![151, -101, -94, -16, -4]], ![![99, -68, -63, -12, -4]], ![![164, -120, -120, -31, -8]], ![![51, -62, -70, -40, -19]]]
  g := ![![![-1353, 802, 882, 72, -100], ![3887, -2299, -2540, -208, 288], ![-7565, 4478, 4939, 404, -560], ![8972, -5312, -5856, -479, 664], ![-7333, 4340, 4788, 392, -543]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-159, 106, 98, 16, 4]] ![![-1083, 802, 882, 72, -100]]
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


lemma PB3864I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB3864I6 : PrimesBelowBoundCertificateInterval O 251 307 3864 where
  m := 9
  g := ![2, 2, 3, 1, 2, 3, 2, 2, 2]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB3864I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2]
    · exact ![I283N0, I283N1]
    · exact ![I293N0, I293N1]
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
    · exact ![18191447, 69169]
    · exact ![19465109, 269, 269]
    · exact ![1461660310351]
    · exact ![21253933, 76729]
    · exact ![78961, 78961, 281]
    · exact ![22665187, 80089]
    · exact ![7370050801, 293]
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
      exact NI283N1
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
  β := ![I269N1, I269N2, I281N2, I293N1, I307N1]
  Il := ![[], [], [I269N1, I269N2], [], [], [I281N2], [], [I293N1], [I307N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
