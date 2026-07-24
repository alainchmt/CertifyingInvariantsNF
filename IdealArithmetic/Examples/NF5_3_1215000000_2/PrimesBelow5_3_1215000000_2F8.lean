
import IdealArithmetic.Examples.NF5_3_1215000000_2.RI5_3_1215000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, 19, 6, 5, -6]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![-23, 19, 6, 5, -6]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![0, 0, 367, 0, 0], ![184, 83, 361, 1, 0], ![96, 66, 361, 0, 1]] where
  M :=![![![-23, 19, 6, 5, -6], ![36, -52, 18, -13, 10], ![-60, 61, -83, 101, -26], ![44, -49, 60, -72, 62], ![-160, 89, -70, 219, -85]]]
  hmulB := by decide  
  f := ![![![-145, -71, -36, 7, 18]], ![![-108, -62, -28, 7, 14]], ![![-84, -45, -27, 7, 14]], ![![-180, -94, -51, 12, 26]], ![![-140, -74, -41, 10, 21]]]
  g := ![![![-1, 0, 1, 5, -6], ![4, 1, 3, -13, 10], ![-44, -18, -74, 101, -26], ![20, 5, 10, -72, 62], ![-88, -34, -132, 219, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 3 2 8 [105, 159, 258, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 271, 313], [332, 95, 54], [0, 1]]
 g := ![![[93, 41, 92], [184, 156, 134], [171, 233, 137], [270, 168, 148], [303, 101], [61, 352, 256], [345, 109, 1], []], ![[346, 205, 103, 74], [97, 160, 117, 328], [116, 22, 332, 148], [48, 60, 20, 110], [114, 134], [220, 283, 165, 2], [109, 145, 336, 26], [114, 347]], ![[227, 190, 189, 27], [185, 341, 225, 189], [80, 282, 178, 254], [164, 103, 242, 19], [127, 73], [64, 275, 222, 11], [32, 60, 340, 12], [6, 347]]]
 h' := ![![[144, 271, 313], [131, 289, 184], [28, 300, 190], [276, 91, 258], [145, 159, 176], [201, 237, 44], [108, 127, 351], [0, 0, 1], [0, 1]], ![[332, 95, 54], [255, 331, 39], [16, 3, 15], [342, 181, 145], [235, 341, 60], [185, 325, 190], [351, 302, 63], [325, 366, 95], [144, 271, 313]], ![[0, 1], [39, 114, 144], [185, 64, 162], [131, 95, 331], [210, 234, 131], [103, 172, 133], [89, 305, 320], [228, 1, 271], [332, 95, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 3], []]
 b := ![[], [64, 57, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 3
  hpos := by decide
  P := [105, 159, 258, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9800125, 3178113, -4160538, -15613671, -9190598]
  a := ![0, 7, -7, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![10258891, 5192622, 24387413, -15613671, -9190598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 49430863 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, 71, 36, -7, -18]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![145, 71, 36, -7, -18]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![24, 17, 1, 0, 0], ![239, 284, 0, 1, 0], ![314, 307, 0, 0, 1]] where
  M :=![![![145, 71, 36, -7, -18], ![108, 62, 28, -7, -14], ![84, 45, 27, -7, -14], ![92, 43, 22, -8, -14], ![8, 5, -4, -9, -1]]]
  hmulB := by decide  
  f := ![![![23, -19, -6, -5, 6]], ![![-36, 52, -18, 13, -10]], ![![0, 1, -1, 0, 0]], ![![-13, 28, -18, 7, -4]], ![![-10, 27, -20, 6, -3]]]
  g := ![![![18, 19, 36, -7, -18], ![15, 16, 28, -7, -14], ![15, 16, 27, -7, -14], ![16, 17, 22, -8, -14], ![7, 8, -4, -9, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P1 : CertificateIrreducibleZModOfList' 367 2 2 8 [219, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [363, 366], [0, 1]]
 g := ![![[119, 37], [215, 31], [244, 325], [151, 322], [13], [161, 41], [220, 16], [1]], ![[338, 330], [91, 336], [45, 42], [331, 45], [13], [364, 326], [156, 351], [1]]]
 h' := ![![[363, 366], [258, 88], [146, 201], [328, 159], [84, 286], [340, 252], [264, 271], [148, 363], [0, 1]], ![[0, 1], [273, 279], [76, 166], [59, 208], [41, 81], [66, 115], [281, 96], [164, 4], [363, 366]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [268]]
 b := ![[], [268, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N1 : CertifiedPrimeIdeal' SI367N1 367 where
  n := 2
  hpos := by decide
  P := [219, 4, 1]
  hirr := P367P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-698450, -1713320, 1796534, 1464419, 2633063]
  a := ![3, 62, -124, -1, -249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3325867, -3423705, 1796534, 1464419, 2633063]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N1 B_one_repr
lemma NI367N1 : Nat.card (O ⧸ I367N1) = 134689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N1
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![-23, 19, 6, 5, -6]] ![![145, 71, 36, -7, -18]]
  ![![367, 0, 0, 0, 0]] where
 M := ![![![-367, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC367 : ContainsPrimesAboveP 367 ![I367N0, I367N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
    exact isPrimeI367N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 367 (by decide) (𝕀 ⊙ MulI367N0)
instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, 135, -19, -54, 34]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![-61, 135, -19, -54, 34]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![0, 0, 373, 0, 0], ![166, 351, 249, 1, 0], ![207, 353, 362, 0, 1]] where
  M :=![![![-61, 135, -19, -54, 34], ![-204, 114, 100, 93, -108], ![648, -721, 107, -255, 186], ![-224, 249, -292, 340, -144], ![118, -59, 583, -696, 265]]]
  hmulB := by decide  
  f := ![![![-821, -425, -217, 36, 104]], ![![-624, -328, -172, 9, 72]], ![![-432, -245, -147, -75, 18]], ![![-1242, -662, -357, -26, 126]], ![![-1465, -784, -426, -45, 143]]]
  g := ![![![5, 19, 3, -54, 34], ![18, 15, 43, 93, -108], ![12, 62, -10, -255, 186], ![-72, -183, -88, 340, -144], ![163, 404, 209, -696, 265]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 3 2 8 [65, 362, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 30, 20], [75, 342, 353], [0, 1]]
 g := ![![[15, 295, 12], [104, 250], [87, 117, 70], [115, 37], [140, 297, 307], [230, 0, 152], [228, 219, 1], []], ![[46, 171, 130, 174], [241, 111], [116, 348, 228, 43], [296, 89], [243, 173, 162, 195], [121, 270, 197, 145], [349, 305, 264, 197], [26, 27]], ![[206, 262, 66, 246], [205, 124], [228, 320, 344, 18], [195, 327], [0, 268, 216, 313], [99, 163, 286, 133], [221, 295, 29, 277], [66, 27]]]
 h' := ![![[144, 30, 20], [197, 260, 111], [313, 189, 37], [255, 160, 280], [225, 293, 339], [343, 221, 230], [100, 209, 56], [0, 0, 1], [0, 1]], ![[75, 342, 353], [279, 339, 267], [32, 199, 22], [268, 345, 115], [232, 339, 200], [157, 213, 274], [152, 157, 206], [23, 84, 342], [144, 30, 20]], ![[0, 1], [32, 147, 368], [100, 358, 314], [0, 241, 351], [309, 114, 207], [204, 312, 242], [269, 7, 111], [216, 289, 30], [75, 342, 353]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [294, 359], []]
 b := ![[], [160, 38, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 3
  hpos := by decide
  P := [65, 362, 154, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9647034, 4867500, -5781396, -15848637, -11342472]
  a := ![1, 6, -8, -3, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13373760, 25661211, 21572397, -15848637, -11342472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 51895117 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![821, 425, 217, -36, -104]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![821, 425, 217, -36, -104]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![54, 371, 1, 0, 0], ![54, 140, 0, 1, 0], ![269, 284, 0, 0, 1]] where
  M :=![![![821, 425, 217, -36, -104], ![624, 328, 172, -9, -72], ![432, 245, 147, 75, -18], ![388, 243, 164, 158, 20], ![-158, -17, 49, 264, 121]]]
  hmulB := by decide  
  f := ![![![61, -135, 19, 54, -34]], ![![204, -114, -100, -93, 108]], ![![210, -131, -97, -84, 102]], ![![86, -63, -34, -28, 36]], ![![199, -184, -64, -30, 57]]]
  g := ![![![51, -122, 217, -36, -104], ![30, -112, 172, -9, -72], ![-18, -160, 147, 75, -18], ![-60, -237, 164, 158, 20], ![-133, -240, 49, 264, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P1 : CertificateIrreducibleZModOfList' 373 2 2 8 [336, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [313, 372], [0, 1]]
 g := ![![[200, 252], [249], [127, 366], [88], [135, 314], [269, 318], [3, 243], [1]], ![[0, 121], [249], [174, 7], [88], [318, 59], [212, 55], [343, 130], [1]]]
 h' := ![![[313, 372], [8, 25], [223, 205], [327, 64], [146, 284], [255, 114], [111, 109], [37, 313], [0, 1]], ![[0, 1], [0, 348], [232, 168], [217, 309], [264, 89], [129, 259], [285, 264], [280, 60], [313, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [207]]
 b := ![[], [121, 290]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N1 : CertifiedPrimeIdeal' SI373N1 373 where
  n := 2
  hpos := by decide
  P := [336, 60, 1]
  hirr := P373P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91369, -254998, 267001, 199601, 389279]
  a := ![1, -25, 48, -1, 95]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-348536, -637565, 267001, 199601, 389279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N1 B_one_repr
lemma NI373N1 : Nat.card (O ⧸ I373N1) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N1
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![-61, 135, -19, -54, 34]] ![![821, 425, 217, -36, -104]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![-373, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC373 : ContainsPrimesAboveP 373 ![I373N0, I373N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI373N0
    exact isPrimeI373N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 373 (by decide) (𝕀 ⊙ MulI373N0)
instance hp379 : Fact (Nat.Prime 379) := {out := by norm_num}

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![379, 0, 0, 0, 0]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![379, 0, 0, 0, 0]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![0, 0, 0, 379, 0], ![0, 0, 0, 0, 379]] where
  M :=![![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![0, 0, 0, 379, 0], ![0, 0, 0, 0, 379]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 5 2 8 [366, 343, 143, 153, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [369, 259, 322, 337, 197], [98, 141, 258, 187, 265], [360, 150, 220, 354, 290], [288, 207, 337, 259, 6], [0, 1]]
 g := ![![[145, 360, 356, 38, 5], [53, 51, 20, 155, 25], [337, 110, 373, 151], [189, 84, 338, 349, 327], [306, 371, 117, 67, 191], [108, 31, 111, 253, 105], [1], []], ![[63, 7, 170, 181, 20, 62, 192, 104], [267, 110, 80, 358, 179, 320, 124, 58], [202, 238, 263, 271], [343, 291, 218, 274, 206, 211, 363, 179], [139, 373, 292, 291, 40, 313, 45, 97], [137, 221, 213, 46, 231, 240, 133, 195], [328, 33, 294, 191, 87, 34, 266, 307], [278, 320, 217, 151]], ![[176, 61, 112, 315, 127, 145, 156, 18], [58, 184, 352, 25, 99, 32, 182, 71], [130, 192, 292, 217], [7, 158, 157, 298, 148, 230, 323, 321], [286, 43, 337, 285, 180, 67, 253, 188], [164, 158, 160, 287, 130, 376, 240, 184], [89, 363, 294, 116, 319, 212, 89, 199], [88, 15, 45, 110]], ![[138, 363, 50, 74, 263, 42, 21, 185], [235, 285, 38, 167, 213, 23, 377, 226], [263, 278, 198, 347], [160, 159, 17, 184, 292, 285, 243, 169], [30, 44, 318, 282, 215, 222, 137, 339], [360, 104, 7, 245, 166, 363, 15, 344], [355, 120, 238, 231, 290, 138, 56, 263], [292, 313, 359, 341]], ![[99, 231, 262, 89, 282, 132, 353, 146], [254, 16, 181, 232, 3, 163, 15, 221], [75, 145, 179, 191], [326, 259, 313, 47, 217, 239, 97, 218], [279, 361, 291, 256, 172, 109, 203, 251], [206, 163, 66, 253, 245, 343, 258, 371], [119, 346, 352, 300, 374, 271, 141, 311], [131, 263, 42, 36]]]
 h' := ![![[369, 259, 322, 337, 197], [310, 60, 185, 274, 39], [349, 234, 160, 119, 374], [183, 34, 225, 120, 197], [188, 337, 306, 204, 51], [267, 291, 179, 203, 116], [13, 36, 236, 226, 357], [0, 0, 1], [0, 1]], ![[98, 141, 258, 187, 265], [265, 188, 148, 298, 124], [366, 45, 362, 243, 135], [157, 48, 283, 29, 140], [49, 265, 108, 66, 329], [369, 338, 336, 281, 308], [322, 127, 53, 153, 28], [303, 271, 360, 52, 349], [369, 259, 322, 337, 197]], ![[360, 150, 220, 354, 290], [34, 301, 373, 110, 304], [320, 90, 111, 141, 4], [279, 350, 131, 337, 57], [128, 69, 142, 227, 296], [218, 191, 16, 180, 340], [250, 280, 353, 268, 140], [136, 300, 245, 204, 46], [98, 141, 258, 187, 265]], ![[288, 207, 337, 259, 6], [316, 171, 247, 174, 88], [275, 88, 185, 187, 235], [159, 300, 68, 5, 101], [289, 351, 362, 115, 99], [195, 348, 24, 138, 351], [363, 56, 337, 250, 38], [367, 164, 68, 178, 178], [360, 150, 220, 354, 290]], ![[0, 1], [264, 38, 184, 281, 203], [23, 301, 319, 68, 10], [180, 26, 51, 267, 263], [72, 115, 219, 146, 362], [60, 348, 203, 335, 22], [113, 259, 158, 240, 195], [130, 23, 84, 324, 185], [288, 207, 337, 259, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197, 102, 54, 48], [], [], []]
 b := ![[], [47, 295, 172, 180, 221], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 5
  hpos := by decide
  P := [366, 343, 143, 153, 22, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12023898811720, 58813533049073, -58256428962440, -34320818094709, -83239904710244]
  a := ![-1, 7, -17, 8, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![31725326680, 155180825987, -153710894360, -90556248271, -219630355436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 7819807277899 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def PBC379 : ContainsPrimesAboveP 379 ![I379N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![379, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 379 (by decide) 𝕀

instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, -25, 47, 260, 122]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![-167, -25, 47, 260, 122]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![0, 0, 383, 0, 0], ![85, 307, 221, 1, 0], ![122, 77, 16, 0, 1]] where
  M :=![![![-167, -25, 47, 260, 122], ![-732, -108, 188, 1133, 520], ![-3120, -493, 837, 4817, 2266], ![-5816, -859, 1504, 8958, 4140], ![-8318, -1307, 2221, 12834, 6015]]]
  hmulB := by decide  
  f := ![![![27, 77, 31, -10, -12]], ![![72, -30, 36, 11, -20]], ![![120, -35, -55, -1, 22]], ![![133, -27, 4, 6, -6]], ![![28, 17, 15, -1, -7]]]
  g := ![![![-97, -233, -155, 260, 122], ![-419, -1013, -675, 1133, 520], ![-1799, -4318, -2872, 4817, 2266], ![-3322, -8015, -5338, 8958, 4140], ![-4786, -11500, -7651, 12834, 6015]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 3 2 8 [5, 212, 292, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 65, 29], [362, 317, 354], [0, 1]]
 g := ![![[284, 352, 303], [183, 203, 76], [190, 195, 129], [235, 363, 189], [199, 26, 86], [369, 165, 113], [26, 91, 1], []], ![[105, 280, 70, 1], [332, 66, 69, 258], [362, 164, 184, 323], [70, 284, 3, 101], [24, 218, 267, 286], [125, 245, 47, 350], [18, 237, 180, 317], [254, 75]], ![[224, 15, 14, 366], [382, 8, 309, 280], [124, 349, 64, 111], [229, 151, 309, 117], [131, 255, 19, 271], [280, 9, 287, 104], [307, 141, 296, 35], [312, 75]]]
 h' := ![![[112, 65, 29], [234, 173, 332], [199, 19, 35], [357, 40, 277], [154, 116, 251], [70, 276, 219], [253, 161, 304], [0, 0, 1], [0, 1]], ![[362, 317, 354], [369, 328, 340], [129, 256, 156], [157, 6, 113], [294, 169, 203], [147, 182, 61], [113, 178, 308], [167, 169, 317], [112, 65, 29]], ![[0, 1], [50, 265, 94], [84, 108, 192], [167, 337, 376], [269, 98, 312], [78, 308, 103], [247, 44, 154], [30, 214, 65], [362, 317, 354]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [336, 211], []]
 b := ![[], [262, 29, 138], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 3
  hpos := by decide
  P := [5, 212, 292, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26565845, -23809776, 19831552, -33091744, 17140720]
  a := ![0, 4, 16, -26, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1953515, 23017024, 18430432, -33091744, 17140720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 56181887 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8819, -4549, -2313, 442, 1140]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![-8819, -4549, -2313, 442, 1140]] 
 ![![383, 0, 0, 0, 0], ![119, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![157, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![-8819, -4549, -2313, 442, 1140], ![-6840, -3528, -1794, 343, 884], ![-5304, -2737, -1391, 265, 686], ![-5420, -2795, -1422, 272, 700], ![-158, -83, -41, 6, 21]]]
  hmulB := by decide  
  f := ![![![-81, -415, 551, 124, -266]], ![![-21, -133, 169, 39, -82]], ![![-6, -3, 13, 1, -6]], ![![-35, -168, 227, 50, -110]], ![![4, -29, 25, 6, -13]]]
  g := ![![![1216, -4549, -2313, 442, 1140], ![943, -3528, -1794, 343, 884], ![732, -2737, -1391, 265, 686], ![747, -2795, -1422, 272, 700], ![23, -83, -41, 6, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N1 : Nat.card (O ⧸ I383N1) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N1)

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := prime_ideal_of_norm_prime hp383.out _ NI383N1

def I383N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-119, 6, 174, 18, -76]] i)))

def SI383N2: IdealEqSpanCertificate' Table ![![-119, 6, 174, 18, -76]] 
 ![![383, 0, 0, 0, 0], ![366, 1, 0, 0, 0], ![94, 0, 1, 0, 0], ![303, 0, 0, 1, 0], ![262, 0, 0, 0, 1]] where
  M :=![![![-119, 6, 174, 18, -76], ![456, -539, -150, 84, 36], ![-216, 630, -305, -150, 168], ![-256, 278, 110, -41, -32], ![560, -934, 86, 186, -91]]]
  hmulB := by decide  
  f := ![![![33991, 17582, 8978, -1518, -4324]], ![![32550, 16837, 8598, -1452, -4140]], ![![8390, 4342, 2219, -366, -1064]], ![![26935, 13936, 7120, -1187, -3420]], ![![23238, 12026, 6146, -1014, -2947]]]
  g := ![![![-11, 6, 174, 18, -76], ![462, -539, -150, 84, 36], ![-524, 630, -305, -150, 168], ![-239, 278, 110, -41, -32], ![788, -934, 86, 186, -91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N2 : Nat.card (O ⧸ I383N2) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N2)

lemma isPrimeI383N2 : Ideal.IsPrime I383N2 := prime_ideal_of_norm_prime hp383.out _ NI383N2
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![-167, -25, 47, 260, 122]] ![![-8819, -4549, -2313, 442, 1140]]
  ![![-33991, -17582, -8978, 1518, 4324]] where
 M := ![![![-33991, -17582, -8978, 1518, 4324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI383N1 : IdealMulLeCertificate' Table 
  ![![-33991, -17582, -8978, 1518, 4324]] ![![-119, 6, 174, 18, -76]]
  ![![383, 0, 0, 0, 0]] where
 M := ![![![-383, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC383 : ContainsPrimesAboveP 383 ![I383N0, I383N1, I383N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI383N0
    exact isPrimeI383N1
    exact isPrimeI383N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 383 (by decide) (𝕀 ⊙ MulI383N0 ⊙ MulI383N1)
instance hp389 : Fact (Nat.Prime 389) := {out := by norm_num}

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1071, -1049, -570, 133, 192]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![1071, -1049, -570, 133, 192]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![144, 318, 1, 0, 0], ![344, 159, 0, 1, 0], ![367, 326, 0, 0, 1]] where
  M :=![![![1071, -1049, -570, 133, 192], ![-1152, 2084, -346, -425, 266], ![-1596, 417, 2005, 133, -850], ![784, -1261, 68, 252, -106], ![148, 1537, -1748, -495, 863]]]
  hmulB := by decide  
  f := ![![![395, -313, -640, -2135, -884]], ![![5304, 518, -1808, -9359, -4270]], ![![4548, 317, -1733, -8545, -3866]], ![![2640, -47, -1338, -5905, -2616]], ![![4997, 166, -2166, -10134, -4541]]]
  g := ![![![-85, 248, -570, 133, 192], ![250, 239, -346, -425, 266], ![-62, -980, 2005, 133, -850], ![-146, -73, 68, 252, -106], ![271, 912, -1748, -495, 863]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 2 2 8 [354, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [234, 388], [0, 1]]
 g := ![![[329, 100], [25], [250, 137], [175], [157], [180], [252], [234, 1]], ![[0, 289], [25], [21, 252], [175], [157], [180], [252], [79, 388]]]
 h' := ![![[234, 388], [6, 379], [192, 5], [163, 332], [111, 178], [255, 119], [314, 127], [21, 331], [0, 1]], ![[0, 1], [0, 10], [195, 384], [51, 57], [140, 211], [93, 270], [79, 262], [64, 58], [234, 388]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [182]]
 b := ![[], [245, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 2
  hpos := by decide
  P := [354, 155, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3220, -21933, 20295, 5666, 25304]
  a := ![13, 7, -15, 5, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-36388, -40169, 20295, 5666, 25304]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 151321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def I389N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 6, -10, -54, -26]] i)))

def SI389N1: IdealEqSpanCertificate' Table ![![35, 6, -10, -54, -26]] 
 ![![389, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![20, 0, 0, 1, 0], ![245, 0, 0, 0, 1]] where
  M :=![![![35, 6, -10, -54, -26], ![156, 21, -38, -240, -108], ![648, 110, -181, -1002, -480], ![1228, 174, -310, -1889, -864], ![1732, 286, -476, -2676, -1271]]]
  hmulB := by decide  
  f := ![![![-14641, -8110, -4046, 810, 1966]], ![![-1310, -723, -362, 72, 176]], ![![-439, -240, -119, 24, 58]], ![![-776, -430, -214, 43, 104]], ![![-9221, -5108, -2550, 510, 1239]]]
  g := ![![![19, 6, -10, -54, -26], ![80, 21, -38, -240, -108], ![351, 110, -181, -1002, -480], ![638, 174, -310, -1889, -864], ![931, 286, -476, -2676, -1271]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N1 : Nat.card (O ⧸ I389N1) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N1)

lemma isPrimeI389N1 : Ideal.IsPrime I389N1 := prime_ideal_of_norm_prime hp389.out _ NI389N1

def I389N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 15, -8, -3, 4]] i)))

def SI389N2: IdealEqSpanCertificate' Table ![![-11, 15, -8, -3, 4]] 
 ![![389, 0, 0, 0, 0], ![183, 1, 0, 0, 0], ![354, 0, 1, 0, 0], ![369, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-11, 15, -8, -3, 4], ![-24, 12, 20, -3, -6], ![36, -59, -11, 21, -6], ![16, -13, -6, -10, 10], ![-68, 73, 10, 9, -15]]]
  hmulB := by decide  
  f := ![![![4641, 687, -1238, -7215, -3352]], ![![2235, 331, -596, -3474, -1614]], ![![4446, 659, -1185, -6909, -3210]], ![![4813, 714, -1282, -7477, -3474]], ![![640, 97, -168, -987, -459]]]
  g := ![![![3, 15, -8, -3, 4], ![-21, 12, 20, -3, -6], ![18, -59, -11, 21, -6], ![21, -13, -6, -10, 10], ![-52, 73, 10, 9, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N2 : Nat.card (O ⧸ I389N2) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N2)

lemma isPrimeI389N2 : Ideal.IsPrime I389N2 := prime_ideal_of_norm_prime hp389.out _ NI389N2

def I389N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, -83, -21, 14, 4]] i)))

def SI389N3: IdealEqSpanCertificate' Table ![![71, -83, -21, 14, 4]] 
 ![![389, 0, 0, 0, 0], ![243, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![62, 0, 0, 1, 0], ![298, 0, 0, 0, 1]] where
  M :=![![![71, -83, -21, 14, 4], ![-24, 90, -48, -25, 28], ![-168, 133, 113, -1, -50], ![36, -69, 28, 4, -8], ![78, 3, -141, 6, 47]]]
  hmulB := by decide  
  f := ![![![31255, 4781, -8143, -48028, -22346]], ![![19869, 3039, -5177, -30533, -14206]], ![![7829, 1196, -2042, -12037, -5600]], ![![7714, 1177, -2014, -11866, -5520]], ![![27884, 4261, -7271, -42866, -19943]]]
  g := ![![![51, -83, -21, 14, 4], ![-64, 90, -48, -25, 28], ![-68, 133, 113, -1, -50], ![43, -69, 28, 4, -8], ![-10, 3, -141, 6, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI389N3 : Nat.card (O ⧸ I389N3) = 389 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI389N3)

lemma isPrimeI389N3 : Ideal.IsPrime I389N3 := prime_ideal_of_norm_prime hp389.out _ NI389N3
def MulI389N0 : IdealMulLeCertificate' Table 
  ![![1071, -1049, -570, 133, 192]] ![![35, 6, -10, -54, -26]]
  ![![349, -249, -300, 37, 102]] where
 M := ![![![349, -249, -300, 37, 102]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI389N1 : IdealMulLeCertificate' Table 
  ![![349, -249, -300, 37, 102]] ![![-11, 15, -8, -3, 4]]
  ![![-15007, 26912, -3674, -6052, 3530]] where
 M := ![![![-15007, 26912, -3674, -6052, 3530]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI389N2 : IdealMulLeCertificate' Table 
  ![![-15007, 26912, -3674, -6052, 3530]] ![![71, -83, -21, 14, 4]]
  ![![389, 0, 0, 0, 0]] where
 M := ![![![-1036685, 3607197, -2058977, -882252, 1091534]]]
 hmul := by decide  
 g := ![![![![-2665, 9273, -5293, -2268, 2806]]]]
 hle2 := by decide  


def PBC389 : ContainsPrimesAboveP 389 ![I389N0, I389N1, I389N2, I389N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
    exact isPrimeI389N1
    exact isPrimeI389N2
    exact isPrimeI389N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 389 (by decide) (𝕀 ⊙ MulI389N0 ⊙ MulI389N1 ⊙ MulI389N2)
instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![459, -4173, 598, 823, -440]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![459, -4173, 598, 823, -440]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![189, 23, 1, 0, 0], ![202, 291, 0, 1, 0], ![95, 170, 0, 0, 1]] where
  M :=![![![459, -4173, 598, 823, -440], ![2640, -2282, -3948, -23, 1646], ![-9876, 11549, 1643, -1991, -46], ![-2320, -133, 1870, 216, -794], ![9800, -10243, -4624, 1407, 1459]]]
  hmulB := by decide  
  f := ![![![-31801, -3597, 7144, 48671, 21180]], ![![-127080, -24076, 37930, 197183, 97342]], ![![-23973, -3284, 5939, 36849, 16716]], ![![-111914, -19919, 32162, 173295, 84044]], ![![-65907, -11670, 18882, 102038, 49415]]]
  g := ![![![-597, -460, 598, 823, -440], ![1504, -465, -3948, -23, 1646], ![217, 1413, 1643, -1991, -46], ![-816, 73, 1870, 216, -794], ![1161, -1414, -4624, 1407, 1459]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 2 2 8 [298, 205, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [192, 396], [0, 1]]
 g := ![![[26, 4], [253], [118, 237], [338, 37], [196], [225], [176], [192, 1]], ![[0, 393], [253], [364, 160], [296, 360], [196], [225], [176], [384, 396]]]
 h' := ![![[192, 396], [13, 2], [169, 359], [114, 285], [221, 229], [238, 14], [275, 382], [349, 42], [0, 1]], ![[0, 1], [0, 395], [19, 38], [48, 112], [122, 168], [147, 383], [174, 15], [76, 355], [192, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [356]]
 b := ![[], [380, 178]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 2
  hpos := by decide
  P := [298, 205, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-512, -369, 247, 836, 70]
  a := ![-1, 1, -2, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-561, -658, 247, 836, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, -3, 2]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![1, 1, 0, -3, 2]] 
 ![![397, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![202, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![285, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, -3, 2], ![-12, 10, -2, 9, -6], ![36, -37, 21, -33, 18], ![-28, 25, -24, 38, -18], ![44, -37, 44, -69, 35]]]
  hmulB := by decide  
  f := ![![![-8155, -4223, -2134, 417, 1054]], ![![-2522, -1306, -660, 129, 326]], ![![-4162, -2155, -1089, 213, 538]], ![![-2026, -1049, -530, 104, 262]], ![![-5855, -3032, -1532, 300, 757]]]
  g := ![![![-1, 1, 0, -3, 2], ![0, 10, -2, 9, -6], ![-4, -37, 21, -33, 18], ![8, 25, -24, 38, -18], ![-19, -37, 44, -69, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N1 : Nat.card (O ⧸ I397N1) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N1)

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := prime_ideal_of_norm_prime hp397.out _ NI397N1

def I397N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-125, 188, 1, -35, 10]] i)))

def SI397N2: IdealEqSpanCertificate' Table ![![-125, 188, 1, -35, 10]] 
 ![![397, 0, 0, 0, 0], ![306, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![99, 0, 0, 1, 0], ![213, 0, 0, 0, 1]] where
  M :=![![![-125, 188, 1, -35, 10], ![-60, -61, 152, 28, -70], ![420, -450, -185, 64, 56], ![8, 66, -78, -21, 38], ![-358, 272, 269, -21, -103]]]
  hmulB := by decide  
  f := ![![![3083, 1640, 833, -37, -376]], ![![2382, 1267, 644, -28, -290]], ![![436, 234, 119, 0, -52]], ![![769, 410, 211, -2, -90]], ![![1645, 880, 448, -6, -197]]]
  g := ![![![-142, 188, 1, -35, 10], ![56, -61, 152, 28, -70], ![328, -450, -185, 64, 56], ![-55, 66, -78, -21, 38], ![-188, 272, 269, -21, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N2 : Nat.card (O ⧸ I397N2) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N2)

lemma isPrimeI397N2 : Ideal.IsPrime I397N2 := prime_ideal_of_norm_prime hp397.out _ NI397N2

def I397N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-253, 229, 196, -21, -74]] i)))

def SI397N3: IdealEqSpanCertificate' Table ![![-253, 229, 196, -21, -74]] 
 ![![397, 0, 0, 0, 0], ![343, 1, 0, 0, 0], ![260, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![363, 0, 0, 0, 1]] where
  M :=![![![-253, 229, 196, -21, -74], ![444, -650, 12, 123, -42], ![252, 183, -539, -93, 246], ![-260, 385, 34, -68, 6], ![208, -713, 400, 177, -215]]]
  hmulB := by decide  
  f := ![![![1063, -1899, 1722, -1053, 1946]], ![![889, -1625, 1476, -870, 1676]], ![![728, -1317, 1195, -717, 1354]], ![![155, -502, 470, -89, 580]], ![![1001, -1882, 1712, -966, 1955]]]
  g := ![![![-253, 229, 196, -21, -74], ![557, -650, 12, 123, -42], ![-2, 183, -539, -93, 246], ![-341, 385, 34, -68, 6], ![499, -713, 400, 177, -215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI397N3 : Nat.card (O ⧸ I397N3) = 397 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI397N3)

lemma isPrimeI397N3 : Ideal.IsPrime I397N3 := prime_ideal_of_norm_prime hp397.out _ NI397N3
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![459, -4173, 598, 823, -440]] ![![1, 1, 0, -3, 2]]
  ![![29659, -26542, -18208, 2966, 6506]] where
 M := ![![![29659, -26542, -18208, 2966, 6506]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N1 : IdealMulLeCertificate' Table 
  ![![29659, -26542, -18208, 2966, 6506]] ![![-125, 188, 1, -35, 10]]
  ![![-12067635, 17353942, 882521, -3145465, 577472]] where
 M := ![![![-12067635, 17353942, 882521, -3145465, 577472]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI397N2 : IdealMulLeCertificate' Table 
  ![![-12067635, 17353942, 882521, -3145465, 577472]] ![![-253, 229, 196, -21, -74]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![11918592271, -15504790933, -2508644985, 2621984912, 238210322]]]
 hmul := by decide  
 g := ![![![![30021643, -39054889, -6319005, 6604496, 600026]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1, I397N2, I397N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
    exact isPrimeI397N2
    exact isPrimeI397N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0 ⊙ MulI397N1 ⊙ MulI397N2)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![581, 495, 433, 770, 240]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![581, 495, 433, 770, 240]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![0, 0, 401, 0, 0], ![68, 157, 143, 1, 0], ![217, 292, 340, 0, 1]] where
  M :=![![![581, 495, 433, 770, 240], ![-1440, 98, 832, 3509, 1540], ![-9240, -1161, 2775, 15245, 7018], ![-17596, -2423, 4972, 28144, 13016], ![-26350, -3991, 6917, 40638, 18897]]]
  hmulB := by decide  
  f := ![![![9, -45, -25, 68, -34]], ![![204, -136, 48, -211, 136]], ![![-816, 775, -395, 749, -422]], ![![-208, 214, -125, 194, -102]], ![![-541, 536, -316, 522, -279]]]
  g := ![![![-259, -475, -477, 770, 240], ![-1432, -2495, -2555, 3509, 1540], ![-6406, -11082, -11380, 15245, 7018], ![-11860, -20503, -21060, 28144, 13016], ![-17183, -29681, -30497, 40638, 18897]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 3 2 8 [148, 221, 344, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [155, 225, 235], [303, 175, 166], [0, 1]]
 g := ![![[213, 231, 381], [356, 381], [72, 224], [274, 315], [228, 240, 175], [288, 195], [0, 41], [1]], ![[165, 369, 176, 373], [15, 78], [192, 47], [282, 77], [141, 215, 298, 373], [65, 183], [114, 173], [141, 355, 55, 312]], ![[386, 355, 166, 151], [236, 159], [346, 356], [274, 93], [125, 173, 66, 239], [193, 57], [192, 303], [237, 84, 284, 89]]]
 h' := ![![[155, 225, 235], [22, 230, 98], [162, 24, 98], [341, 286, 376], [341, 107, 324], [227, 123, 24], [250, 0, 51], [253, 180, 57], [0, 1]], ![[303, 175, 166], [391, 295, 223], [280, 60, 334], [15, 71, 279], [279, 258, 41], [103, 24, 223], [225, 339, 103], [173, 142, 145], [155, 225, 235]], ![[0, 1], [332, 277, 80], [209, 317, 370], [127, 44, 147], [86, 36, 36], [144, 254, 154], [275, 62, 247], [167, 79, 199], [303, 175, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [382, 235], []]
 b := ![[], [88, 343, 400], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 3
  hpos := by decide
  P := [148, 221, 344, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1389014, -887530, 1027038, 2332318, 1894976]
  a := ![3, -3, 4, 2, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1424430, -2295248, -2435876, 2332318, 1894976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 64481201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 45, 25, -68, 34]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![-9, 45, 25, -68, 34]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![354, 372, 1, 0, 0], ![332, 95, 0, 1, 0], ![85, 307, 0, 0, 1]] where
  M :=![![![-9, 45, 25, -68, 34], ![-204, 136, -48, 211, -136], ![816, -775, 395, -749, 422], ![-640, 599, -524, 810, -404], ![1022, -913, 1007, -1518, 733]]]
  hmulB := by decide  
  f := ![![![-581, -495, -433, -770, -240]], ![![1440, -98, -832, -3509, -1540]], ![![846, -525, -1161, -3973, -1658]], ![![-96, -427, -568, -1539, -596]], ![![1045, -170, -746, -2951, -1277]]]
  g := ![![![27, -33, 25, -68, 34], ![-104, 99, -48, 211, -136], ![184, -514, 395, -749, 422], ![-124, 605, -524, 810, -404], ![215, -1138, 1007, -1518, 733]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P1 : CertificateIrreducibleZModOfList' 401 2 2 8 [46, 357, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 400], [0, 1]]
 g := ![![[278, 275], [376], [256], [111], [329, 332], [64], [393], [44, 1]], ![[348, 126], [376], [256], [111], [100, 69], [64], [393], [88, 400]]]
 h' := ![![[44, 400], [4, 26], [247, 301], [96, 16], [104, 46], [380, 44], [328, 8], [382, 286], [0, 1]], ![[0, 1], [346, 375], [258, 100], [399, 385], [123, 355], [311, 357], [279, 393], [134, 115], [44, 400]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [87, 233]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N1 : CertifiedPrimeIdeal' SI401N1 401 where
  n := 2
  hpos := by decide
  P := [46, 357, 1]
  hirr := P401P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2190, -16335, 18565, -840, 25720]
  a := ![1, -5, 12, -5, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21140, -36755, 18565, -840, 25720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N1 B_one_repr
lemma NI401N1 : Nat.card (O ⧸ I401N1) = 160801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N1
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![581, 495, 433, 770, 240]] ![![-9, 45, 25, -68, 34]]
  ![![401, 0, 0, 0, 0]] where
 M := ![![![-401, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0)
instance hp409 : Fact (Nat.Prime 409) := {out := by norm_num}

def I409N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![409, 0, 0, 0, 0]] i)))

def SI409N0: IdealEqSpanCertificate' Table ![![409, 0, 0, 0, 0]] 
 ![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![0, 0, 0, 409, 0], ![0, 0, 0, 0, 409]] where
  M :=![![![409, 0, 0, 0, 0], ![0, 409, 0, 0, 0], ![0, 0, 409, 0, 0], ![0, 0, 0, 409, 0], ![0, 0, 0, 0, 409]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P409P0 : CertificateIrreducibleZModOfList' 409 5 2 8 [22, 233, 5, 21, 70, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [368, 22, 275, 307, 144], [36, 63, 55, 17, 169], [288, 212, 374, 0, 53], [56, 111, 114, 85, 43], [0, 1]]
 g := ![![[132, 304, 178, 246, 255], [167, 350, 308, 91], [232, 185, 162, 36], [204, 141, 50, 148, 218], [391, 32, 172, 308, 109], [217, 333, 128, 23], [339, 1], []], ![[211, 228, 350, 330, 276, 219, 359, 89], [91, 108, 21, 81], [263, 300, 387, 18], [262, 351, 224, 82, 112, 125, 135, 408], [240, 242, 393, 36, 248, 56, 8, 271], [333, 42, 180, 80], [52, 386, 218, 242], [82, 306, 303, 360, 253, 46, 171, 284]], ![[33, 138, 117, 235, 143, 196, 83, 197], [330, 156, 181, 136], [73, 68, 382, 256], [248, 137, 209, 304, 46, 237, 53, 34], [166, 145, 349, 254, 348, 158, 79, 103], [56, 161, 283, 206], [341, 121, 176, 406], [238, 390, 251, 373, 1, 206, 68, 200]], ![[324, 367, 276, 55, 337, 8, 326, 200], [289, 339, 134, 369], [378, 197, 0, 96], [83, 46, 231, 349, 277, 182, 142, 218], [340, 202, 102, 226, 98, 13, 315, 262], [359, 246, 70, 121], [350, 26, 332, 393], [169, 298, 79, 276, 65, 324, 339, 1]], ![[40, 109, 349, 0, 143, 357, 21, 330], [189, 341, 60, 406], [356, 68, 49, 169], [209, 237, 184, 212, 313, 80, 148, 114], [302, 304, 26, 353, 32, 219, 77, 354], [292, 176, 228, 249], [249, 83, 8, 30], [113, 36, 61, 72, 103, 211, 100, 161]]]
 h' := ![![[368, 22, 275, 307, 144], [315, 187, 121, 296, 119], [334, 157, 79, 201, 273], [11, 251, 39, 19, 6], [396, 195, 146, 22, 313], [352, 109, 208, 291, 157], [313, 337, 117, 238, 380], [0, 0, 0, 1], [0, 1]], ![[36, 63, 55, 17, 169], [290, 318, 387, 180, 15], [94, 386, 349, 161, 400], [248, 150, 187, 286, 118], [168, 64, 373, 371, 363], [121, 315, 270, 316, 105], [289, 101, 318, 407, 191], [32, 36, 242, 230, 160], [368, 22, 275, 307, 144]], ![[288, 212, 374, 0, 53], [134, 195, 127, 238, 39], [388, 274, 152, 222, 172], [78, 123, 282, 393, 16], [279, 320, 16, 165, 308], [145, 81, 92, 385, 384], [320, 359, 104, 224, 377], [111, 132, 122, 348, 302], [36, 63, 55, 17, 169]], ![[56, 111, 114, 85, 43], [309, 351, 364, 212, 124], [142, 279, 172, 13, 275], [185, 4, 71, 371, 256], [45, 126, 302, 21, 180], [12, 307, 303, 230, 24], [179, 405, 401, 351, 11], [190, 257, 22, 384, 163], [288, 212, 374, 0, 53]], ![[0, 1], [178, 176, 228, 301, 112], [277, 131, 66, 221, 107], [375, 290, 239, 158, 13], [144, 113, 390, 239, 63], [351, 6, 354, 5, 148], [244, 25, 287, 7, 268], [123, 393, 23, 264, 193], [56, 111, 114, 85, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [256, 313, 47, 349], [], [], []]
 b := ![[], [277, 398, 206, 76, 239], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 5
  hpos := by decide
  P := [22, 233, 5, 21, 70, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2185696, -2289582, 1943568, -2588970, 1838046]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5344, -5598, 4752, -6330, 4494]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI409N0 : Ideal.IsPrime I409N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI409N0 B_one_repr
lemma NI409N0 : Nat.card (O ⧸ I409N0) = 11445019581049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI409N0

def PBC409 : ContainsPrimesAboveP 409 ![I409N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI409N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![409, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 409 (by decide) 𝕀

instance hp419 : Fact (Nat.Prime 419) := {out := by norm_num}

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -59, 87, -30, -70]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![13, -59, 87, -30, -70]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![0, 0, 419, 0, 0], ![400, 333, 286, 1, 0], ![409, 331, 373, 0, 1]] where
  M :=![![![13, -59, 87, -30, -70], ![420, -254, -176, -189, -60], ![360, 605, -267, -1077, -378], ![1016, 307, -216, -1804, -864], ![2114, -361, -487, -2472, -1213]]]
  hmulB := by decide  
  f := ![![![-2141, -1117, -557, 96, 284]], ![![-1704, -828, -464, 129, 192]], ![![-1152, -793, -235, -111, 258]], ![![-4188, -2267, -1062, 119, 600]], ![![-4461, -2451, -1119, 96, 659]]]
  g := ![![![97, 79, 83, -30, -70], ![240, 197, 182, -189, -60], ![1398, 1156, 1071, -1077, -378], ![2568, 2117, 2000, -1804, -864], ![3549, 2922, 2766, -2472, -1213]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 3 2 8 [394, 317, 345, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [336, 204, 352], [157, 214, 67], [0, 1]]
 g := ![![[114, 409, 91], [164, 272, 152], [176, 417], [306, 111], [401, 123], [327, 356, 325], [63, 29], [1]], ![[74, 44, 229, 140], [194, 98, 240, 273], [127, 148], [251, 41], [47, 266], [340, 100, 335, 310], [369, 147], [77, 394, 284, 79]], ![[415, 328, 308, 303], [228, 155, 203, 385], [243, 208], [393, 114], [73, 377], [75, 163, 24, 33], [83, 52], [374, 110, 76, 340]]]
 h' := ![![[336, 204, 352], [329, 3, 133], [285, 286, 350], [145, 234, 323], [94, 157, 207], [214, 66, 388], [105, 100, 355], [25, 102, 74], [0, 1]], ![[157, 214, 67], [269, 155, 188], [354, 3, 11], [37, 177, 231], [280, 65, 259], [161, 5, 257], [72, 7, 135], [397, 196, 203], [336, 204, 352]], ![[0, 1], [175, 261, 98], [275, 130, 58], [229, 8, 284], [259, 197, 372], [23, 348, 193], [168, 312, 348], [141, 121, 142], [157, 214, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [260, 356], []]
 b := ![[], [270, 274, 318], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 3
  hpos := by decide
  P := [394, 317, 345, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![79323119, 7436783, -16798421, -120504766, -51317181]
  a := ![7, 21, 7, -50, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![165322092, 136328188, 127897072, -120504766, -51317181]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 73560059 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2141, 1117, 557, -96, -284]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![2141, 1117, 557, -96, -284]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![264, 398, 1, 0, 0], ![260, 213, 0, 1, 0], ![114, 175, 0, 0, 1]] where
  M :=![![![2141, 1117, 557, -96, -284], ![1704, 828, 464, -129, -192], ![1152, 793, 235, 111, -258], ![1468, 551, 456, -250, -76], ![-230, 259, -191, 336, -179]]]
  hmulB := by decide  
  f := ![![![-13, 59, -87, 30, 70]], ![![-420, 254, 176, 189, 60]], ![![-408, 277, 113, 201, 102]], ![![-224, 165, 36, 119, 76]], ![![-184, 123, 51, 93, 47]]]
  g := ![![![-209, -359, 557, -96, -284], ![-156, -293, 464, -129, -192], ![-144, -170, 235, 111, -258], ![-108, -273, 456, -250, -76], ![-40, 86, -191, 336, -179]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P1 : CertificateIrreducibleZModOfList' 419 2 2 8 [158, 326, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 418], [0, 1]]
 g := ![![[193, 91], [189, 352], [114], [66], [173], [333, 252], [170], [93, 1]], ![[276, 328], [243, 67], [114], [66], [173], [305, 167], [170], [186, 418]]]
 h' := ![![[93, 418], [306, 133], [291, 335], [234, 47], [38, 190], [180, 376], [378, 154], [390, 111], [0, 1]], ![[0, 1], [105, 286], [21, 84], [415, 372], [110, 229], [371, 43], [35, 265], [238, 308], [93, 418]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [389]]
 b := ![[], [69, 404]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N1 : CertifiedPrimeIdeal' SI419N1 419 where
  n := 2
  hpos := by decide
  P := [158, 326, 1]
  hirr := P419P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125, 238, 2863, -3726, 2196]
  a := ![1, 6, 4, -15, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-89, -1742, 2863, -3726, 2196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N1 B_one_repr
lemma NI419N1 : Nat.card (O ⧸ I419N1) = 175561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N1
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![13, -59, 87, -30, -70]] ![![2141, 1117, 557, -96, -284]]
  ![![419, 0, 0, 0, 0]] where
 M := ![![![-419, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC419 : ContainsPrimesAboveP 419 ![I419N0, I419N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI419N0
    exact isPrimeI419N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 419 (by decide) (𝕀 ⊙ MulI419N0)


lemma PB1705I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB1705I8 : PrimesBelowBoundCertificateInterval O 359 419 1705 where
  m := 9
  g := ![2, 2, 1, 3, 4, 4, 2, 1, 2]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB1705I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1]
    · exact ![I373N0, I373N1]
    · exact ![I379N0]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0, I389N1, I389N2, I389N3]
    · exact ![I397N0, I397N1, I397N2, I397N3]
    · exact ![I401N0, I401N1]
    · exact ![I409N0]
    · exact ![I419N0, I419N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC367
    · exact PBC373
    · exact PBC379
    · exact PBC383
    · exact PBC389
    · exact PBC397
    · exact PBC401
    · exact PBC409
    · exact PBC419
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![49430863, 134689]
    · exact ![51895117, 139129]
    · exact ![7819807277899]
    · exact ![56181887, 383, 383]
    · exact ![151321, 389, 389, 389]
    · exact ![157609, 397, 397, 397]
    · exact ![64481201, 160801]
    · exact ![11445019581049]
    · exact ![73560059, 175561]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
      exact NI389N1
      exact NI389N2
      exact NI389N3
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
      exact NI397N2
      exact NI397N3
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
  β := ![I383N1, I383N2, I389N1, I389N2, I389N3, I397N1, I397N2, I397N3]
  Il := ![[], [], [], [I383N1, I383N2], [I389N1, I389N2, I389N3], [I397N1, I397N2, I397N3], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
