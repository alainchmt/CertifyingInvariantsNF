
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp367 : Fact (Nat.Prime 367) := {out := by norm_num}

def I367N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -57, 53, 34, 174]] i)))

def SI367N0: IdealEqSpanCertificate' Table ![![25, -57, 53, 34, 174]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![201, 267, 1, 0, 0], ![141, 239, 0, 1, 0], ![194, 91, 0, 0, 1]] where
  M :=![![![25, -57, 53, 34, 174], ![-120, 128, -51, -46, -200], ![304, -97, -128, -38, -296], ![-76, -207, 329, 183, 1024], ![-154, 115, -15, -28, -103]]]
  hmulB := by decide  
  f := ![![![35, -131, 185, 66, 438]], ![![168, 718, -821, -326, -1992]], ![![141, 444, -488, -198, -1190]], ![![125, 430, -479, -193, -1166]], ![![60, 109, -106, -46, -263]]]
  g := ![![![-134, -104, 53, 34, 174], ![151, 117, -51, -46, -200], ![242, 191, -128, -38, -296], ![-792, -613, 329, 183, 1024], ![73, 55, -15, -28, -103]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P0 : CertificateIrreducibleZModOfList' 367 2 2 8 [330, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [193, 366], [0, 1]]
 g := ![![[154, 228], [10, 63], [200, 357], [273, 287], [252], [88, 144], [230, 182], [1]], ![[118, 139], [58, 304], [105, 10], [247, 80], [252], [355, 223], [124, 185], [1]]]
 h' := ![![[193, 366], [3, 154], [60, 226], [192, 298], [156, 108], [320, 282], [69, 12], [37, 193], [0, 1]], ![[0, 1], [365, 213], [5, 141], [87, 69], [81, 259], [63, 85], [183, 355], [219, 174], [193, 366]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [258]]
 b := ![[], [213, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N0 : CertifiedPrimeIdeal' SI367N0 367 where
  n := 2
  hpos := by decide
  P := [330, 174, 1]
  hirr := P367P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-544813, -329332, 647110, 339246, 1254152]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1149191, -1003584, 647110, 339246, 1254152]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N0 : Ideal.IsPrime I367N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N0 B_one_repr
lemma NI367N0 : Nat.card (O ⧸ I367N0) = 134689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N0

def I367N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 4, -8, -4, -10]] i)))

def SI367N1: IdealEqSpanCertificate' Table ![![9, 4, -8, -4, -10]] 
 ![![367, 0, 0, 0, 0], ![0, 367, 0, 0, 0], ![267, 314, 1, 0, 0], ![286, 14, 0, 1, 0], ![295, 330, 0, 0, 1]] where
  M :=![![![9, 4, -8, -4, -10], ![56, 37, -70, -40, -144], ![384, 170, -395, -204, -736], ![948, 442, -976, -535, -1792], ![-290, -124, 290, 154, 529]]]
  hmulB := by decide  
  f := ![![![1075, 804, -348, -240, -1058]], ![![1528, 1055, -430, -304, -1312]], ![![2095, 1492, -623, -436, -1898]], ![![898, 668, -288, -199, -876]], ![![2237, 1594, -666, -466, -2029]]]
  g := ![![![17, 16, -8, -4, -10], ![198, 191, -70, -40, -144], ![1039, 1008, -395, -204, -736], ![2570, 2468, -976, -535, -1792], ![-757, -730, 290, 154, 529]]]
  hle1 := by decide   
  hle2 := by decide  


def P367P1 : CertificateIrreducibleZModOfList' 367 2 2 8 [285, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [264, 366], [0, 1]]
 g := ![![[227, 283], [323, 271], [290, 350], [275, 361], [347], [209, 110], [189, 333], [1]], ![[71, 84], [302, 96], [206, 17], [159, 6], [347], [256, 257], [21, 34], [1]]]
 h' := ![![[264, 366], [62, 83], [292, 76], [163, 152], [38, 348], [256, 54], [84, 250], [82, 264], [0, 1]], ![[0, 1], [321, 284], [171, 291], [288, 215], [160, 19], [199, 313], [24, 117], [48, 103], [264, 366]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [357]]
 b := ![[], [293, 362]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI367N1 : CertifiedPrimeIdeal' SI367N1 367 where
  n := 2
  hpos := by decide
  P := [285, 103, 1]
  hirr := P367P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108144855, -72418068, 137048718, 70304380, 270576470]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-372281373, -363433820, 137048718, 70304380, 270576470]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI367N1 : Ideal.IsPrime I367N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI367N1 B_one_repr
lemma NI367N1 : Nat.card (O ⧸ I367N1) = 134689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI367N1

def I367N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36, 25, -10, -7, -31]] i)))

def SI367N2: IdealEqSpanCertificate' Table ![![36, 25, -10, -7, -31]] 
 ![![367, 0, 0, 0, 0], ![153, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![119, 0, 0, 1, 0], ![354, 0, 0, 0, 1]] where
  M :=![![![36, 25, -10, -7, -31], ![44, 35, -10, -8, -36], ![48, 42, -1, -4, -32], ![-38, -20, 66, 35, 122], ![3, -1, -14, -7, -20]]]
  hmulB := by decide  
  f := ![![![-26, -865, 974, 381, 2363]], ![![-10, -352, 396, 155, 961]], ![![-10, -219, 249, 97, 603]], ![![0, -221, 244, 96, 593]], ![![-25, -833, 938, 367, 2276]]]
  g := ![![![24, 25, -10, -7, -31], ![25, 35, -10, -8, -36], ![15, 42, -1, -4, -32], ![-135, -20, 66, 35, 122], ![25, -1, -14, -7, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI367N2 : Nat.card (O ⧸ I367N2) = 367 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI367N2)

lemma isPrimeI367N2 : Ideal.IsPrime I367N2 := prime_ideal_of_norm_prime hp367.out _ NI367N2
def MulI367N0 : IdealMulLeCertificate' Table 
  ![![25, -57, 53, 34, 174]] ![![9, 4, -8, -4, -10]]
  ![![-843, 453, 131, -26, 68]] where
 M := ![![![-843, 453, 131, -26, 68]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI367N1 : IdealMulLeCertificate' Table 
  ![![-843, 453, 131, -26, 68]] ![![36, 25, -10, -7, -31]]
  ![![367, 0, 0, 0, 0]] where
 M := ![![![-2936, 734, 1101, 367, 1101]]]
 hmul := by decide  
 g := ![![![![-8, 2, 3, 1, 3]]]]
 hle2 := by decide  


def PBC367 : ContainsPrimesAboveP 367 ![I367N0, I367N1, I367N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI367N0
    exact isPrimeI367N1
    exact isPrimeI367N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 367 (by decide) (𝕀 ⊙ MulI367N0 ⊙ MulI367N1)
instance hp373 : Fact (Nat.Prime 373) := {out := by norm_num}

def I373N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-298, -226, 97, 65, 295]] i)))

def SI373N0: IdealEqSpanCertificate' Table ![![-298, -226, 97, 65, 295]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![0, 0, 373, 0, 0], ![79, 332, 315, 1, 0], ![84, 270, 223, 0, 1]] where
  M :=![![![-298, -226, 97, 65, 295], ![-380, -256, 49, 54, 220], ![-416, -477, 148, 82, 584], ![374, 383, -831, -391, -1666], ![-35, 14, 121, 61, 182]]]
  hmulB := by decide  
  f := ![![![-36, -14, 47, 23, 135]], ![![-12, 114, -131, -78, -412]], ![![224, -309, 190, 138, 664]], ![![170, -162, 54, 52, 223]], ![![117, -105, 29, 31, 128]]]
  g := ![![![-81, -272, -231, 65, 295], ![-62, -208, -177, 54, 220], ![-150, -497, -418, 82, 584], ![459, 1555, 1324, -391, -1666], ![-54, -186, -160, 61, 182]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P0 : CertificateIrreducibleZModOfList' 373 3 2 8 [261, 278, 313, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [355, 316, 320], [78, 56, 53], [0, 1]]
 g := ![![[193, 113, 120], [86, 366], [73, 40, 89], [35, 63], [176, 96, 86], [281, 168, 324], [338, 60, 1], []], ![[119, 211, 139, 96], [], [368, 243, 239, 79], [34, 321], [285, 88, 18, 43], [148, 39, 209, 306], [16, 190, 54, 150], [18, 198]], ![[47, 342, 143, 186], [135, 366], [63, 22, 262, 76], [312, 29], [359, 34, 102, 319], [94, 322, 275, 223], [315, 142, 340, 244], [285, 198]]]
 h' := ![![[355, 316, 320], [88, 0, 150], [343, 235, 309], [82, 80, 200], [316, 74, 199], [140, 297, 210], [183, 38, 355], [0, 0, 1], [0, 1]], ![[78, 56, 53], [95, 310, 194], [29, 224], [19, 205, 246], [259, 346, 135], [175, 290, 122], [274, 184, 335], [102, 201, 56], [355, 316, 320]], ![[0, 1], [129, 63, 29], [100, 287, 64], [160, 88, 300], [341, 326, 39], [312, 159, 41], [173, 151, 56], [331, 172, 316], [78, 56, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [309, 22], []]
 b := ![[], [336, 30, 296], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N0 : CertifiedPrimeIdeal' SI373N0 373 where
  n := 3
  hpos := by decide
  P := [261, 278, 313, 1]
  hirr := P373P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1462733011, 736949284, -1582854466, -846239788, -2990249064]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![856559243, 2919720660, 2498145362, -846239788, -2990249064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N0 : Ideal.IsPrime I373N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N0 B_one_repr
lemma NI373N0 : Nat.card (O ⧸ I373N0) = 51895117 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N0

def I373N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, -14, 47, 23, 135]] i)))

def SI373N1: IdealEqSpanCertificate' Table ![![-36, -14, 47, 23, 135]] 
 ![![373, 0, 0, 0, 0], ![0, 373, 0, 0, 0], ![86, 116, 1, 0, 0], ![234, 216, 0, 1, 0], ![372, 304, 0, 0, 1]] where
  M :=![![![-36, -14, 47, 23, 135], ![-12, 114, -131, -78, -412], ![224, -309, 190, 138, 664], ![-322, 167, 71, 5, 138], ![-47, 138, -131, -83, -428]]]
  hmulB := by decide  
  f := ![![![-298, -226, 97, 65, 295]], ![![-380, -256, 49, 54, 220]], ![![-188, -133, 38, 32, 138]], ![![-406, -289, 87, 71, 308]], ![![-607, -434, 137, 109, 474]]]
  g := ![![![-160, -138, 47, 23, 135], ![490, 422, -131, -78, -412], ![-792, -681, 190, 138, 664], ![-158, -137, 71, 5, 138], ![509, 438, -131, -83, -428]]]
  hle1 := by decide   
  hle2 := by decide  


def P373P1 : CertificateIrreducibleZModOfList' 373 2 2 8 [37, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [342, 372], [0, 1]]
 g := ![![[21, 121], [290], [239, 307], [115], [191, 115], [124, 307], [105, 215], [1]], ![[0, 252], [290], [47, 66], [115], [356, 258], [305, 66], [154, 158], [1]]]
 h' := ![![[342, 372], [32, 362], [109, 214], [248, 143], [20, 130], [261, 243], [218, 230], [336, 342], [0, 1]], ![[0, 1], [0, 11], [189, 159], [291, 230], [93, 243], [188, 130], [175, 143], [178, 31], [342, 372]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [295]]
 b := ![[], [328, 334]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI373N1 : CertifiedPrimeIdeal' SI373N1 373 where
  n := 2
  hpos := by decide
  P := [37, 31, 1]
  hirr := P373P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16479046, -11047789, 20906636, 10715775, 41290517]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-52766792, -46389121, 20906636, 10715775, 41290517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI373N1 : Ideal.IsPrime I373N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI373N1 B_one_repr
lemma NI373N1 : Nat.card (O ⧸ I373N1) = 139129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI373N1
def MulI373N0 : IdealMulLeCertificate' Table 
  ![![-298, -226, 97, 65, 295]] ![![-36, -14, 47, 23, 135]]
  ![![373, 0, 0, 0, 0]] where
 M := ![![![373, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I379N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![737, 711, -343, -242, -1092]] i)))

def SI379N0: IdealEqSpanCertificate' Table ![![737, 711, -343, -242, -1092]] 
 ![![379, 0, 0, 0, 0], ![0, 379, 0, 0, 0], ![0, 0, 379, 0, 0], ![0, 0, 0, 379, 0], ![328, 319, 304, 62, 1]] where
  M :=![![![737, 711, -343, -242, -1092], ![1440, 624, -357, -190, -920], ![880, 1013, 224, -74, 280], ![728, 1503, -1627, -833, -4592], ![44, -461, 87, 110, 393]]]
  hmulB := by decide  
  f := ![![![11, 5, -11, -6, -20]], ![![64, 34, -71, -38, -136]], ![![368, 171, -382, -206, -712]], ![![1016, 509, -1095, -587, -2064]], ![![524, 253, -554, -298, -1039]]]
  g := ![![![947, 921, 875, 178, -1092], ![800, 776, 737, 150, -920], ![-240, -233, -224, -46, 280], ![3976, 3869, 3679, 749, -4592], ![-340, -332, -315, -64, 393]]]
  hle1 := by decide   
  hle2 := by decide  


def P379P0 : CertificateIrreducibleZModOfList' 379 4 2 8 [244, 260, 152, 39, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [244, 98, 343, 114], [71, 330, 117, 118], [25, 329, 298, 147], [0, 1]]
 g := ![![[378, 327, 143, 164], [59, 273, 310, 23], [213, 99, 245], [187, 353, 231, 331], [199, 285, 55, 219], [106, 208, 216, 6], [340, 1], []], ![[275, 336, 305, 52, 154, 77], [244, 337, 67, 285, 174, 224], [204, 244, 193], [7, 159, 322, 123, 13, 132], [277, 332, 258, 49, 338, 366], [274, 209, 108, 111, 129, 177], [237, 123, 158, 214, 79, 371], [126, 9, 110]], ![[221, 97, 66, 314, 52, 39], [206, 370, 49, 92, 165, 88], [264, 360, 195], [0, 202, 317, 376, 339, 361], [226, 28, 256, 276, 18, 165], [107, 219, 153, 377, 236, 19], [84, 33, 113, 224, 22, 227], [252, 16, 280]], ![[234, 25, 156, 190, 213, 60], [11, 279, 16, 343, 72, 276], [338, 293, 118], [128, 180, 369, 294, 3, 55], [63, 76, 355, 115, 251, 235], [215, 211, 240, 230, 295, 353], [373, 220, 262, 349, 82, 334], [271, 208, 6]]]
 h' := ![![[244, 98, 343, 114], [6, 123, 35, 88], [252, 299, 177, 73], [231, 213, 328, 106], [335, 126, 268, 33], [287, 306, 312, 230], [41, 42, 362, 232], [0, 0, 1], [0, 1]], ![[71, 330, 117, 118], [34, 68, 218, 377], [373, 347, 159, 194], [11, 292, 274, 268], [290, 44, 72, 151], [346, 32, 156, 350], [48, 221, 193, 252], [367, 361, 175, 50], [244, 98, 343, 114]], ![[25, 329, 298, 147], [211, 35, 101, 250], [7, 183, 22, 37], [55, 332, 357, 86], [72, 120, 222, 215], [55, 332, 170, 65], [313, 101, 308, 285], [24, 176, 328, 199], [71, 330, 117, 118]], ![[0, 1], [5, 153, 25, 43], [77, 308, 21, 75], [64, 300, 178, 298], [334, 89, 196, 359], [112, 88, 120, 113], [332, 15, 274, 368], [68, 221, 254, 130], [25, 329, 298, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [198, 209, 360], []]
 b := ![[], [], [195, 210, 288, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI379N0 : CertifiedPrimeIdeal' SI379N0 379 where
  n := 4
  hpos := by decide
  P := [244, 260, 152, 39, 1]
  hirr := P379P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13787461613400, -6956703564853, 14928735290231, 7983475160130, 28204018969694]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24445133730008, -23757358192341, -22583358922155, -4592785490662, 28204018969694]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI379N0 : Ideal.IsPrime I379N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI379N0 B_one_repr
lemma NI379N0 : Nat.card (O ⧸ I379N0) = 20632736881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI379N0

def I379N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -5, 11, 6, 20]] i)))

def SI379N1: IdealEqSpanCertificate' Table ![![-11, -5, 11, 6, 20]] 
 ![![379, 0, 0, 0, 0], ![231, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![161, 0, 0, 1, 0], ![345, 0, 0, 0, 1]] where
  M :=![![![-11, -5, 11, 6, 20], ![-64, -34, 71, 38, 136], ![-368, -171, 382, 206, 712], ![-1016, -509, 1095, 587, 2064], ![292, 141, -309, -166, -579]]]
  hmulB := by decide  
  f := ![![![-737, -711, 343, 242, 1092]], ![![-453, -435, 210, 148, 668]], ![![-154, -149, 70, 50, 224]], ![![-315, -306, 150, 105, 476]], ![![-671, -646, 312, 220, 993]]]
  g := ![![![-20, -5, 11, 6, 20], ![-134, -34, 71, 38, 136], ![-711, -171, 382, 206, 712], ![-2046, -509, 1095, 587, 2064], ![576, 141, -309, -166, -579]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI379N1 : Nat.card (O ⧸ I379N1) = 379 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI379N1)

lemma isPrimeI379N1 : Ideal.IsPrime I379N1 := prime_ideal_of_norm_prime hp379.out _ NI379N1
def MulI379N0 : IdealMulLeCertificate' Table 
  ![![737, 711, -343, -242, -1092]] ![![-11, -5, 11, 6, 20]]
  ![![379, 0, 0, 0, 0]] where
 M := ![![![-379, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC379 : ContainsPrimesAboveP 379 ![I379N0, I379N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI379N0
    exact isPrimeI379N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 379 (by decide) (𝕀 ⊙ MulI379N0)
instance hp383 : Fact (Nat.Prime 383) := {out := by norm_num}

def I383N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 44, -58, -24, -136]] i)))

def SI383N0: IdealEqSpanCertificate' Table ![![15, 44, -58, -24, -136]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![341, 30, 1, 0, 0], ![247, 104, 0, 1, 0], ![146, 329, 0, 0, 1]] where
  M :=![![![15, 44, -58, -24, -136], ![32, -131, 132, 44, 352], ![352, 736, -1011, -440, -2288], ![688, -660, 390, 23, 1408], ![-232, -146, 284, 148, 559]]]
  hmulB := by decide  
  f := ![![![-2927, -2188, 930, 648, 2840]], ![![-4192, -2949, 1260, 868, 3808]], ![![-2949, -2190, 931, 648, 2840]], ![![-3031, -2216, 944, 655, 2872]], ![![-4714, -3365, 1436, 992, 4351]]]
  g := ![![![119, 128, -58, -24, -136], ![-280, -325, 132, 44, 352], ![2057, 2166, -1011, -440, -2288], ![-897, -1248, 390, 23, 1408], ![-562, -543, 284, 148, 559]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P0 : CertificateIrreducibleZModOfList' 383 2 2 8 [313, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [240, 382], [0, 1]]
 g := ![![[277, 93], [152, 293], [308, 220], [280, 68], [312, 116], [270, 213], [277, 150], [1]], ![[0, 290], [0, 90], [254, 163], [131, 315], [193, 267], [68, 170], [275, 233], [1]]]
 h' := ![![[240, 382], [299, 211], [112, 357], [67, 37], [9, 343], [133, 196], [240, 301], [70, 240], [0, 1]], ![[0, 1], [0, 172], [0, 26], [138, 346], [367, 40], [64, 187], [93, 82], [220, 143], [240, 382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114]]
 b := ![[], [54, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N0 : CertifiedPrimeIdeal' SI383N0 383 where
  n := 2
  hpos := by decide
  P := [313, 143, 1]
  hirr := P383P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-185983, -341058, 481300, 211830, 1082164]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-978139, -1025698, 481300, 211830, 1082164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N0 : Ideal.IsPrime I383N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N0 B_one_repr
lemma NI383N0 : Nat.card (O ⧸ I383N0) = 146689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N0

def I383N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76, 32, 29, 7, 65]] i)))

def SI383N1: IdealEqSpanCertificate' Table ![![-76, 32, 29, 7, 65]] 
 ![![383, 0, 0, 0, 0], ![0, 383, 0, 0, 0], ![202, 52, 1, 0, 0], ![110, 90, 0, 1, 0], ![327, 274, 0, 0, 1]] where
  M :=![![![-76, 32, 29, 7, 65], ![92, 80, -171, -90, -508], ![128, -401, 396, 250, 1288], ![-470, 423, -123, -135, -550], ![51, 128, -203, -113, -620]]]
  hmulB := by decide  
  f := ![![![86, 76, -79, -41, -181]], ![![260, 62, -133, -90, -220]], ![![84, 51, -64, -36, -134]], ![![94, 39, -61, -37, -116]], ![![257, 108, -160, -98, -307]]]
  g := ![![![-73, -52, 29, 7, 65], ![550, 408, -171, -90, -508], ![-1380, -1035, 396, 250, 1288], ![572, 443, -123, -135, -550], ![669, 498, -203, -113, -620]]]
  hle1 := by decide   
  hle2 := by decide  


def P383P1 : CertificateIrreducibleZModOfList' 383 2 2 8 [372, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [379, 382], [0, 1]]
 g := ![![[313, 174], [100, 25], [33, 232], [103, 100], [278, 130], [228, 171], [231, 16], [1]], ![[0, 209], [0, 358], [254, 151], [86, 283], [141, 253], [310, 212], [167, 367], [1]]]
 h' := ![![[379, 382], [334, 275], [363, 378], [367, 341], [377, 373], [210, 270], [243, 139], [11, 379], [0, 1]], ![[0, 1], [0, 108], [0, 5], [152, 42], [34, 10], [279, 113], [70, 244], [27, 4], [379, 382]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [51, 217]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI383N1 : CertifiedPrimeIdeal' SI383N1 383 where
  n := 2
  hpos := by decide
  P := [372, 4, 1]
  hirr := P383P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86566, -48246, 99725, 52530, 192440]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-232212, -163682, 99725, 52530, 192440]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI383N1 : Ideal.IsPrime I383N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI383N1 B_one_repr
lemma NI383N1 : Nat.card (O ⧸ I383N1) = 146689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI383N1

def I383N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![622, 454, -191, -133, -581]] i)))

def SI383N2: IdealEqSpanCertificate' Table ![![622, 454, -191, -133, -581]] 
 ![![383, 0, 0, 0, 0], ![301, 1, 0, 0, 0], ![170, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![222, 0, 0, 0, 1]] where
  M :=![![![622, 454, -191, -133, -581], ![868, 634, -267, -186, -812], ![1216, 887, -378, -262, -1144], ![422, 303, -135, -93, -398], ![-243, -176, 77, 53, 230]]]
  hmulB := by decide  
  f := ![![![172, 302, -503, -253, -1439]], ![![136, 234, -392, -197, -1121]], ![![72, 143, -230, -116, -658]], ![![58, 85, -150, -76, -431]], ![![101, 172, -289, -145, -826]]]
  g := ![![![107, 454, -191, -133, -581], ![150, 634, -267, -186, -812], ![217, 887, -378, -262, -1144], ![82, 303, -135, -93, -398], ![-46, -176, 77, 53, 230]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI383N2 : Nat.card (O ⧸ I383N2) = 383 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI383N2)

lemma isPrimeI383N2 : Ideal.IsPrime I383N2 := prime_ideal_of_norm_prime hp383.out _ NI383N2
def MulI383N0 : IdealMulLeCertificate' Table 
  ![![15, 44, -58, -24, -136]] ![![-76, 32, 29, 7, 65]]
  ![![-172, -302, 503, 253, 1439]] where
 M := ![![![-172, -302, 503, 253, 1439]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI383N1 : IdealMulLeCertificate' Table 
  ![![-172, -302, 503, 253, 1439]] ![![622, 454, -191, -133, -581]]
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

def I389N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![389, 0, 0, 0, 0]] i)))

def SI389N0: IdealEqSpanCertificate' Table ![![389, 0, 0, 0, 0]] 
 ![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![0, 0, 389, 0, 0], ![0, 0, 0, 389, 0], ![0, 0, 0, 0, 389]] where
  M :=![![![389, 0, 0, 0, 0], ![0, 389, 0, 0, 0], ![0, 0, 389, 0, 0], ![0, 0, 0, 389, 0], ![0, 0, 0, 0, 389]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P389P0 : CertificateIrreducibleZModOfList' 389 5 2 8 [306, 382, 170, 316, 114, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [178, 244, 323, 177, 88], [356, 17, 307, 155, 194], [279, 120, 194, 269, 256], [240, 7, 343, 177, 240], [0, 1]]
 g := ![![[124, 171, 245, 24, 344], [51, 285, 303, 311], [336, 8, 253, 183, 369], [130, 34, 215, 5], [184, 132, 214, 310], [251, 38, 43, 142], [275, 1], []], ![[384, 193, 217, 220, 318, 298, 66, 273], [231, 303, 351, 223], [151, 350, 144, 144, 332, 235, 165, 285], [7, 206, 17, 100], [364, 39, 0, 324], [167, 126, 240, 322], [345, 276, 27, 262], [349, 87, 249, 39, 168, 344, 105, 333]], ![[87, 330, 43, 237, 73, 8, 95, 3], [84, 227, 7, 220], [284, 261, 82, 50, 72, 105, 145, 103], [0, 164, 247, 247], [269, 150, 201, 344], [190, 295, 282, 73], [320, 133, 289, 6], [90, 42, 224, 125, 174, 217, 325, 243]], ![[7, 287, 109, 337, 291, 383, 94, 74], [35, 99], [341, 150, 184, 340, 247, 318, 355, 64], [238, 150], [73, 83, 58, 309], [181, 383, 200, 335], [170, 313, 357, 267], [321, 215, 267, 323, 51, 86, 179, 35]], ![[210, 124, 26, 176, 83, 340, 133, 212], [256, 281, 318, 321], [232, 206, 250, 196, 361, 49, 256, 185], [194, 260, 384, 335], [347, 216, 198, 230], [136, 199, 354, 121], [58, 209, 341, 353], [133, 314, 73, 263, 368, 201, 336, 107]]]
 h' := ![![[178, 244, 323, 177, 88], [350, 256, 170, 75, 106], [269, 287, 165, 360, 356], [108, 301, 97, 87, 330], [322, 313, 204, 138, 86], [143, 316, 71, 158, 243], [263, 63, 326, 66, 232], [0, 0, 0, 1], [0, 1]], ![[356, 17, 307, 155, 194], [333, 233, 153, 123, 52], [143, 31, 387, 250, 85], [63, 78, 76, 152, 280], [250, 60, 132, 318, 10], [44, 293, 283, 248, 18], [24, 7, 244, 353, 200], [211, 58, 71, 203, 111], [178, 244, 323, 177, 88]], ![[279, 120, 194, 269, 256], [178, 226, 99, 99, 108], [347, 48, 109, 381, 61], [260, 70, 274, 130, 31], [250, 267, 185, 273, 228], [277, 101, 241, 315, 283], [340, 183, 345, 92, 292], [319, 138, 387, 66, 28], [356, 17, 307, 155, 194]], ![[240, 7, 343, 177, 240], [141, 205, 365, 141, 372], [187, 343, 259, 329], [10, 110, 11, 302, 195], [367, 336, 52, 249], [179, 2, 249, 255, 118], [150, 131, 380, 26, 65], [349, 231, 373, 7, 338], [279, 120, 194, 269, 256]], ![[0, 1], [173, 247, 380, 340, 140], [299, 69, 247, 236, 276], [13, 219, 320, 107, 331], [78, 191, 205, 189, 65], [360, 66, 323, 191, 116], [88, 5, 261, 241, 378], [254, 351, 336, 112, 301], [240, 7, 343, 177, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [244, 196, 251, 198], [], [], []]
 b := ![[], [81, 351, 37, 248, 95], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI389N0 : CertifiedPrimeIdeal' SI389N0 389 where
  n := 5
  hpos := by decide
  P := [306, 382, 170, 316, 114, 1]
  hirr := P389P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![221393028256748, 108342985586162, -235915788972204, -126792463521478, -443432402851686]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![569133748732, 278516672458, -606467323836, -325944636302, -1139929056174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI389N0 : Ideal.IsPrime I389N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI389N0 B_one_repr
lemma NI389N0 : Nat.card (O ⧸ I389N0) = 8907339520949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI389N0

def PBC389 : ContainsPrimesAboveP 389 ![I389N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI389N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![389, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 389 (by decide) 𝕀

instance hp397 : Fact (Nat.Prime 397) := {out := by norm_num}

def I397N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -28, 26, 16, 74]] i)))

def SI397N0: IdealEqSpanCertificate' Table ![![-23, -28, 26, 16, 74]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![0, 0, 397, 0, 0], ![86, 164, 312, 1, 0], ![362, 50, 8, 0, 1]] where
  M :=![![![-23, -28, 26, 16, 74], ![-88, -5, 30, 12, 32], ![-160, -158, 203, 124, 400], ![-644, -354, 738, 389, 1496], ![138, 122, -194, -110, -399]]]
  hmulB := by decide  
  f := ![![![-7, 4, -10, -4, -26]], ![![-8, -45, 42, 20, 112]], ![![-32, 102, -109, -44, -272]], ![![-30, 62, -70, -27, -172]], ![![-8, 0, -6, -2, -15]]]
  g := ![![![-71, -16, -14, 16, 74], ![-32, -9, -10, 12, 32], ![-392, -102, -105, 124, 400], ![-1450, -350, -334, 389, 1496], ![388, 96, 94, -110, -399]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P0 : CertificateIrreducibleZModOfList' 397 3 2 8 [170, 384, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [392, 332, 12], [388, 64, 385], [0, 1]]
 g := ![![[362, 14, 179], [374, 291], [141, 155, 47], [247, 207, 341], [81, 179], [87, 154], [68, 196], [1]], ![[187, 392, 335, 102], [0, 362], [26, 382, 224, 111], [289, 34, 194, 69], [324, 75], [312, 188], [363, 137], [395, 243, 132, 140]], ![[294, 244, 39, 287], [161, 364], [307, 89, 15, 224], [273, 166, 6, 188], [220, 218], [176, 124], [62, 12], [23, 34, 230, 257]]]
 h' := ![![[392, 332, 12], [208, 146, 373], [247, 224, 95], [92, 294, 368], [161, 350, 306], [6, 393, 24], [269, 65, 173], [227, 13, 383], [0, 1]], ![[388, 64, 385], [136, 23, 216], [327, 238, 34], [178, 176, 84], [145, 368, 361], [162, 275, 297], [395, 2, 339], [215, 238, 54], [392, 332, 12]], ![[0, 1], [54, 228, 205], [256, 332, 268], [171, 324, 342], [86, 76, 127], [73, 126, 76], [321, 330, 282], [125, 146, 357], [388, 64, 385]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 75], []]
 b := ![[], [249, 26, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N0 : CertifiedPrimeIdeal' SI397N0 397 where
  n := 3
  hpos := by decide
  P := [170, 384, 14, 1]
  hirr := P397P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10971992451, -5724976878, 12094223834, 6431311909, 22976802772]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22371958237, -5564988082, -5486875350, 6431311909, 22976802772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N0 : Ideal.IsPrime I397N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N0 B_one_repr
lemma NI397N0 : Nat.card (O ⧸ I397N0) = 62570773 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N0

def I397N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -4, 10, 4, 26]] i)))

def SI397N1: IdealEqSpanCertificate' Table ![![7, -4, 10, 4, 26]] 
 ![![397, 0, 0, 0, 0], ![0, 397, 0, 0, 0], ![361, 170, 1, 0, 0], ![281, 23, 0, 1, 0], ![261, 389, 0, 0, 1]] where
  M :=![![![7, -4, 10, 4, 26], ![8, 45, -42, -20, -112], ![32, -102, 109, 44, 272], ![12, 174, -190, -73, -448], ![-14, 14, -10, -6, -33]]]
  hmulB := by decide  
  f := ![![![23, 28, -26, -16, -74]], ![![88, 5, -30, -12, -32]], ![![59, 28, -37, -20, -82]], ![![23, 21, -22, -13, -58]], ![![101, 23, -46, -22, -79]]]
  g := ![![![-29, -30, 10, 4, 26], ![126, 129, -42, -20, -112], ![-309, -316, 109, 44, 272], ![519, 525, -190, -73, -448], ![35, 37, -10, -6, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P397P1 : CertificateIrreducibleZModOfList' 397 2 2 8 [221, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [327, 396], [0, 1]]
 g := ![![[356, 300], [179], [243, 19], [370, 36], [265], [92], [79], [327, 1]], ![[0, 97], [179], [104, 378], [232, 361], [265], [92], [79], [257, 396]]]
 h' := ![![[327, 396], [292, 197], [289, 373], [12, 49], [307, 6], [236, 258], [178, 253], [384, 312], [0, 1]], ![[0, 1], [0, 200], [381, 24], [155, 348], [284, 391], [41, 139], [333, 144], [379, 85], [327, 396]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [33, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI397N1 : CertifiedPrimeIdeal' SI397N1 397 where
  n := 2
  hpos := by decide
  P := [221, 70, 1]
  hirr := P397P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-420643, -307518, 563528, 284096, 1128710]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1456621, -1364508, 563528, 284096, 1128710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI397N1 : Ideal.IsPrime I397N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI397N1 B_one_repr
lemma NI397N1 : Nat.card (O ⧸ I397N1) = 157609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI397N1
def MulI397N0 : IdealMulLeCertificate' Table 
  ![![-23, -28, 26, 16, 74]] ![![7, -4, 10, 4, 26]]
  ![![397, 0, 0, 0, 0]] where
 M := ![![![-397, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC397 : ContainsPrimesAboveP 397 ![I397N0, I397N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI397N0
    exact isPrimeI397N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 397 (by decide) (𝕀 ⊙ MulI397N0)
instance hp401 : Fact (Nat.Prime 401) := {out := by norm_num}

def I401N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2482, -1797, 754, 527, 2299]] i)))

def SI401N0: IdealEqSpanCertificate' Table ![![-2482, -1797, 754, 527, 2299]] 
 ![![401, 0, 0, 0, 0], ![0, 401, 0, 0, 0], ![0, 0, 401, 0, 0], ![174, 101, 20, 1, 0], ![378, 102, 24, 0, 1]] where
  M :=![![![-2482, -1797, 754, 527, 2299], ![-3452, -2545, 1082, 744, 3268], ![-4784, -3434, 1363, 996, 4256], ![-1714, -1388, 774, 447, 2166], ![953, 705, -306, -213, -938]]]
  hmulB := by decide  
  f := ![![![12, 19, -26, -15, -57]], ![![132, 43, -122, -64, -228]], ![![624, 314, -665, -356, -1216]], ![![74, 37, -80, -43, -152]], ![![81, 47, -94, -51, -182]]]
  g := ![![![-2402, -722, -162, 527, 2299], ![-3412, -1025, -230, 744, 3268], ![-4456, -1342, -301, 996, 4256], ![-2240, -667, -150, 447, 2166], ![979, 294, 66, -213, -938]]]
  hle1 := by decide   
  hle2 := by decide  


def P401P0 : CertificateIrreducibleZModOfList' 401 3 2 8 [207, 296, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 61, 222], [332, 339, 179], [0, 1]]
 g := ![![[89, 129, 36], [245, 365], [331, 241], [130, 197], [140, 29, 4], [354, 241], [71, 111], [1]], ![[376, 267, 137, 10], [239, 356], [126, 7], [164, 156], [8, 166, 205, 82], [162, 225], [347, 186], [157, 141, 156, 164]], ![[119, 121, 325, 397], [78, 312], [211, 292], [115, 321], [144, 204, 340, 357], [357, 2], [253, 195], [60, 146, 362, 237]]]
 h' := ![![[23, 61, 222], [101, 152, 395], [118, 188, 281], [393, 45, 363], [293, 19, 263], [12, 354, 2], [82, 356, 363], [194, 105, 355], [0, 1]], ![[332, 339, 179], [256, 368, 31], [178, 204, 254], [51, 87, 316], [77, 75, 343], [312, 101, 269], [76, 211, 386], [119, 296, 97], [23, 61, 222]], ![[0, 1], [251, 282, 376], [208, 9, 267], [101, 269, 123], [249, 307, 196], [110, 347, 130], [386, 235, 53], [322, 0, 350], [332, 339, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 314], []]
 b := ![[], [131, 249, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI401N0 : CertifiedPrimeIdeal' SI401N0 401 where
  n := 3
  hpos := by decide
  P := [207, 296, 46, 1]
  hirr := P401P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40168025, -19669371, 42821855, 23010191, 80496610]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-85964239, -26320082, -5858605, 23010191, 80496610]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI401N0 : Ideal.IsPrime I401N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI401N0 B_one_repr
lemma NI401N0 : Nat.card (O ⧸ I401N0) = 64481201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI401N0

def I401N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -12, 13, 5, 31]] i)))

def SI401N1: IdealEqSpanCertificate' Table ![![0, -12, 13, 5, 31]] 
 ![![401, 0, 0, 0, 0], ![51, 1, 0, 0, 0], ![206, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![0, -12, 13, 5, 31], ![4, 42, -49, -18, -116], ![-32, -167, 206, 78, 488], ![38, 301, -363, -137, -882], ![5, 6, -9, -3, -16]]]
  hmulB := by decide  
  f := ![![![-4574, -3400, 1439, 1003, 4387]], ![![-598, -444, 188, 131, 573]], ![![-2372, -1763, 746, 520, 2274]], ![![-1548, -1151, 488, 340, 1487]], ![![-315, -234, 99, 69, 302]]]
  g := ![![![-9, -12, 13, 5, 31], ![34, 42, -49, -18, -116], ![-145, -167, 206, 78, 488], ![256, 301, -363, -137, -882], ![6, 6, -9, -3, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N1 : Nat.card (O ⧸ I401N1) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N1)

lemma isPrimeI401N1 : Ideal.IsPrime I401N1 := prime_ideal_of_norm_prime hp401.out _ NI401N1

def I401N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 13, -20, -7, -47]] i)))

def SI401N2: IdealEqSpanCertificate' Table ![![-6, 13, -20, -7, -47]] 
 ![![401, 0, 0, 0, 0], ![310, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![200, 0, 0, 1, 0], ![261, 0, 0, 0, 1]] where
  M :=![![![-6, 13, -20, -7, -47], ![-20, -81, 90, 36, 220], ![16, 266, -325, -124, -784], ![-70, -504, 600, 233, 1450], ![3, -11, 14, 5, 34]]]
  hmulB := by decide  
  f := ![![![-284, -115, 352, 175, 1005]], ![![-220, -87, 270, 134, 770]], ![![-96, -46, 127, 64, 364]], ![![-150, -56, 180, 89, 510]], ![![-185, -72, 226, 112, 645]]]
  g := ![![![31, 13, -20, -7, -47], ![-130, -81, 90, 36, 220], ![480, 266, -325, -124, -784], ![-880, -504, 600, 233, 1450], ![-21, -11, 14, 5, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI401N2 : Nat.card (O ⧸ I401N2) = 401 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI401N2)

lemma isPrimeI401N2 : Ideal.IsPrime I401N2 := prime_ideal_of_norm_prime hp401.out _ NI401N2
def MulI401N0 : IdealMulLeCertificate' Table 
  ![![-2482, -1797, 754, 527, 2299]] ![![0, -12, 13, 5, 31]]
  ![![205, 813, -881, -348, -2136]] where
 M := ![![![205, 813, -881, -348, -2136]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI401N1 : IdealMulLeCertificate' Table 
  ![![205, 813, -881, -348, -2136]] ![![-6, 13, -20, -7, -47]]
  ![![401, 0, 0, 0, 0]] where
 M := ![![![-13634, -98646, 116691, 45313, 282705]]]
 hmul := by decide  
 g := ![![![![-34, -246, 291, 113, 705]]]]
 hle2 := by decide  


def PBC401 : ContainsPrimesAboveP 401 ![I401N0, I401N1, I401N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI401N0
    exact isPrimeI401N1
    exact isPrimeI401N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 401 (by decide) (𝕀 ⊙ MulI401N0 ⊙ MulI401N1)
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


def P409P0 : CertificateIrreducibleZModOfList' 409 5 2 8 [102, 221, 115, 127, 305, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 408, 358, 186, 377], [318, 408, 216, 314, 291], [44, 366, 233, 306, 225], [78, 44, 11, 12, 334], [0, 1]]
 g := ![![[292, 173, 139, 265, 311], [354, 394, 311, 209], [118, 183, 33, 50], [106, 359, 254, 28, 81], [86, 61, 66, 247, 328], [37, 262, 405, 162], [104, 1], []], ![[341, 139, 317, 53, 364, 408, 381, 270], [49, 79, 313, 53], [115, 29, 141, 309], [313, 100, 147, 400, 214, 105, 380, 91], [119, 1, 196, 386, 305, 366, 337, 164], [100, 156, 13, 142], [91, 92, 94, 327], [94, 289, 377, 22, 253, 402, 344, 361]], ![[226, 368, 55, 11, 257, 350, 217, 201], [123, 383, 13, 361], [207, 199, 355, 121], [209, 204, 109, 254, 22, 113, 403, 264], [58, 348, 248, 192, 68, 143, 260, 43], [344, 337, 20, 123], [156, 212, 244, 159], [20, 281, 394, 271, 400, 31, 151, 330]], ![[44, 386, 395, 25, 0, 204, 364, 170], [357, 364, 253, 256], [1, 129, 300, 239], [247, 349, 334, 38, 89, 312, 52, 361], [397, 377, 378, 325, 175, 209, 315, 373], [207, 130, 148, 406], [260, 381, 177, 359], [257, 253, 58, 182, 139, 376, 161, 384]], ![[0, 4, 180, 370, 15, 88, 24, 147], [197, 1, 110, 227], [360, 213, 135, 154], [404, 332, 56, 91, 319, 118, 3, 340], [357, 196, 209, 400, 71, 323, 175, 369], [295, 306, 300, 125], [400, 269, 182, 212], [181, 287, 167, 262, 326, 294, 111, 213]]]
 h' := ![![[73, 408, 358, 186, 377], [140, 44, 50, 119, 245], [16, 200, 4, 16, 59], [231, 30, 240, 295, 333], [226, 140, 75, 397, 9], [174, 216, 134, 212, 60], [26, 227, 89, 174, 55], [0, 0, 0, 1], [0, 1]], ![[318, 408, 216, 314, 291], [314, 68, 364, 255, 28], [182, 215, 260, 145, 54], [298, 166, 25, 31, 203], [304, 296, 244, 301, 223], [351, 289, 334, 334, 359], [121, 187, 196, 392, 37], [286, 19, 179, 140, 209], [73, 408, 358, 186, 377]], ![[44, 366, 233, 306, 225], [295, 149, 115, 71, 305], [354, 259, 301, 164, 19], [257, 277, 208, 132, 11], [399, 175, 56, 170, 127], [4, 289, 152, 293, 313], [209, 74, 354, 76, 142], [221, 153, 259, 111, 74], [318, 408, 216, 314, 291]], ![[78, 44, 11, 12, 334], [263, 152, 384, 10, 367], [337, 264, 52, 339, 16], [216, 362, 205, 342, 110], [369, 220, 201, 319, 383], [23, 45, 399, 6, 139], [224, 4, 66, 113, 107], [74, 170, 10, 105, 234], [44, 366, 233, 306, 225]], ![[0, 1], [0, 405, 314, 363, 282], [355, 289, 201, 154, 261], [80, 392, 140, 18, 161], [163, 396, 242, 40, 76], [108, 388, 208, 382, 356], [262, 326, 113, 63, 68], [55, 67, 370, 52, 301], [78, 44, 11, 12, 334]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 283, 151, 98], [], [], []]
 b := ![[], [153, 0, 134, 399, 182], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI409N0 : CertifiedPrimeIdeal' SI409N0 409 where
  n := 5
  hpos := by decide
  P := [102, 221, 115, 127, 305, 1]
  hirr := P409P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41099792867642837487, 20116960941031910031, -43800319061144523262, -23539633425241851813, -82330744615377256190]
  a := ![649, 505, -992, -453, -2054]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![100488491118931143, 49185723572205159, -107091244648275118, -57554115954136557, -201297664096276910]
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

def I419N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-64419, -47085, 19821, 13794, 60292]] i)))

def SI419N0: IdealEqSpanCertificate' Table ![![-64419, -47085, 19821, 13794, 60292]] 
 ![![419, 0, 0, 0, 0], ![0, 419, 0, 0, 0], ![0, 0, 419, 0, 0], ![0, 0, 0, 419, 0], ![388, 394, 378, 315, 1]] where
  M :=![![![-64419, -47085, 19821, 13794, 60292], ![-89888, -65516, 27455, 19178, 83672], ![-125584, -92127, 39188, 27070, 118776], ![-42344, -30053, 11753, 8607, 36616], ![24796, 18091, -7605, -5290, -23115]]]
  hmulB := by decide  
  f := ![![![-17, -15, 25, 14, 52]], ![![-128, -50, 125, 66, 232]], ![![-656, -329, 702, 378, 1304]], ![![-1864, -935, 2013, 1085, 3816]], ![![-2128, -1060, 2286, 1231, 4309]]]
  g := ![![![-55985, -56807, -54345, -45294, 60292], ![-77696, -78836, -75419, -62858, 83672], ![-110288, -111909, -107060, -89230, 118776], ![-34008, -34503, -33005, -27507, 36616], ![21464, 21779, 20835, 17365, -23115]]]
  hle1 := by decide   
  hle2 := by decide  


def P419P0 : CertificateIrreducibleZModOfList' 419 4 2 8 [214, 313, 337, 329, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [252, 93, 291, 25], [397, 186, 18, 1], [279, 139, 110, 393], [0, 1]]
 g := ![![[363, 174, 109, 117], [318, 307, 336, 299], [228, 131, 205], [222, 227, 64], [162, 198, 289], [213, 122, 309, 188], [221, 90, 1], []], ![[291, 138, 204, 179, 135, 218], [206, 284, 150, 238, 400, 293], [70, 177, 161], [403, 23, 208], [393, 73, 177], [149, 67, 394, 69, 155, 386], [376, 159, 137], [159, 262, 372, 378, 173, 122]], ![[248, 264, 259, 283, 123, 343], [40, 117, 18, 69, 309, 121], [241, 61, 198], [32, 106, 178], [367, 229, 134], [167, 375, 266, 118, 275, 147], [15, 295, 169], [41, 353, 68, 326, 144, 1]], ![[318, 361, 307, 300, 132, 1], [329, 288, 74, 272, 193, 13], [181, 112, 395], [358, 89, 190], [17, 260, 236], [181, 106, 142, 330, 309, 25], [313, 358, 411], [316, 272, 202, 342, 57, 22]]]
 h' := ![![[252, 93, 291, 25], [245, 409, 112, 206], [312, 235, 92, 352], [410, 261, 196, 275], [69, 235, 47, 8], [89, 117, 276, 17], [53, 395, 213, 141], [0, 0, 0, 1], [0, 1]], ![[397, 186, 18, 1], [399, 340, 76, 152], [339, 274, 12, 30], [252, 51, 200, 202], [246, 11, 406, 284], [360, 217, 218, 201], [386, 24, 378, 148], [54, 373, 163, 239], [252, 93, 291, 25]], ![[279, 139, 110, 393], [174, 46, 362, 379], [398, 263, 180, 408], [4, 95, 22, 63], [188, 202, 190, 75], [293, 142, 271, 316], [258, 162, 347, 216], [271, 270, 203, 406], [397, 186, 18, 1]], ![[0, 1], [57, 43, 288, 101], [394, 66, 135, 48], [202, 12, 1, 298], [239, 390, 195, 52], [230, 362, 73, 304], [416, 257, 319, 333], [285, 195, 53, 192], [279, 139, 110, 393]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [260, 14, 231], []]
 b := ![[], [], [415, 183, 213, 188], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI419N0 : CertifiedPrimeIdeal' SI419N0 419 where
  n := 4
  hpos := by decide
  P := [214, 313, 337, 329, 1]
  hirr := P419P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4098009321001, -2004977394945, 4366300727456, 2346745740267, 8206666253729]
  a := ![121, 93, -185, -88, -383]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7609270920687, -7721793511609, -7393206546974, -6164088601872, 8206666253729]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI419N0 : Ideal.IsPrime I419N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI419N0 B_one_repr
lemma NI419N0 : Nat.card (O ⧸ I419N0) = 30821664721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI419N0

def I419N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -15, 25, 14, 52]] i)))

def SI419N1: IdealEqSpanCertificate' Table ![![-17, -15, 25, 14, 52]] 
 ![![419, 0, 0, 0, 0], ![378, 1, 0, 0, 0], ![414, 0, 1, 0, 0], ![337, 0, 0, 1, 0], ![246, 0, 0, 0, 1]] where
  M :=![![![-17, -15, 25, 14, 52], ![-128, -50, 125, 66, 232], ![-656, -329, 702, 378, 1304], ![-1864, -935, 2013, 1085, 3816], ![524, 267, -567, -306, -1065]]]
  hmulB := by decide  
  f := ![![![-64419, -47085, 19821, 13794, 60292]], ![![-58330, -42634, 17947, 12490, 54592]], ![![-63950, -46743, 19678, 13694, 59856]], ![![-51913, -37942, 15970, 11115, 48580]], ![![-37762, -27601, 11619, 8086, 35343]]]
  g := ![![![-53, -15, 25, 14, 52], ![-268, -50, 125, 66, 232], ![-1468, -329, 702, 378, 1304], ![-4263, -935, 2013, 1085, 3816], ![1192, 267, -567, -306, -1065]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI419N1 : Nat.card (O ⧸ I419N1) = 419 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI419N1)

lemma isPrimeI419N1 : Ideal.IsPrime I419N1 := prime_ideal_of_norm_prime hp419.out _ NI419N1
def MulI419N0 : IdealMulLeCertificate' Table 
  ![![-64419, -47085, 19821, 13794, 60292]] ![![-17, -15, 25, 14, 52]]
  ![![419, 0, 0, 0, 0]] where
 M := ![![![419, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB547I8_primes (p : ℕ) :
  p ∈ Set.range ![367, 373, 379, 383, 389, 397, 401, 409, 419] ↔ Nat.Prime p ∧ 359 < p ∧ p ≤ 419 := by
  rw [← List.mem_ofFn']
  convert primes_range 359 419 (by omega)

def PB547I8 : PrimesBelowBoundCertificateInterval O 359 419 547 where
  m := 9
  g := ![3, 2, 2, 3, 1, 2, 3, 1, 2]
  P := ![367, 373, 379, 383, 389, 397, 401, 409, 419]
  hP := PB547I8_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I367N0, I367N1, I367N2]
    · exact ![I373N0, I373N1]
    · exact ![I379N0, I379N1]
    · exact ![I383N0, I383N1, I383N2]
    · exact ![I389N0]
    · exact ![I397N0, I397N1]
    · exact ![I401N0, I401N1, I401N2]
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
    · exact ![134689, 134689, 367]
    · exact ![51895117, 139129]
    · exact ![20632736881, 379]
    · exact ![146689, 146689, 383]
    · exact ![8907339520949]
    · exact ![62570773, 157609]
    · exact ![64481201, 401, 401]
    · exact ![11445019581049]
    · exact ![30821664721, 419]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI367N0
      exact NI367N1
      exact NI367N2
    · dsimp ; intro j
      fin_cases j
      exact NI373N0
      exact NI373N1
    · dsimp ; intro j
      fin_cases j
      exact NI379N0
      exact NI379N1
    · dsimp ; intro j
      fin_cases j
      exact NI383N0
      exact NI383N1
      exact NI383N2
    · dsimp ; intro j
      fin_cases j
      exact NI389N0
    · dsimp ; intro j
      fin_cases j
      exact NI397N0
      exact NI397N1
    · dsimp ; intro j
      fin_cases j
      exact NI401N0
      exact NI401N1
      exact NI401N2
    · dsimp ; intro j
      fin_cases j
      exact NI409N0
    · dsimp ; intro j
      fin_cases j
      exact NI419N0
      exact NI419N1
  β := ![I367N2, I379N1, I383N2, I401N1, I401N2, I419N1]
  Il := ![[I367N2], [], [I379N1], [I383N2], [], [], [I401N1, I401N2], [], [I419N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
