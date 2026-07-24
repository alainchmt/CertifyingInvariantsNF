
import IdealArithmetic.Examples.NF5_3_125000000_3.RI5_3_125000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -26, 32, 16, 72]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-21, -26, 32, 16, 72]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![0, 0, 257, 0, 0], ![137, 99, 107, 1, 0], ![187, 99, 148, 0, 1]] where
  M :=![![![-21, -26, 32, 16, 72], ![-96, -5, 46, 32, 64], ![-512, -402, 699, 348, 1408], ![-1312, -394, 1112, 651, 1928], ![384, 200, -418, -224, -789]]]
  hmulB := by decide  
  f := ![![![3, -14, -4, 0, -8]], ![![-32, -33, 42, 24, 128]], ![![-64, 66, -65, -44, -224]], ![![-37, 7, -13, -9, -48]], ![![-47, 15, -24, -16, -85]]]
  g := ![![![-61, -34, -48, 16, 72], ![-64, -37, -50, 32, 64], ![-1212, -678, -953, 348, 1408], ![-1755, -995, -1377, 651, 1928], ![695, 391, 546, -224, -789]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 3 2 8 [217, 21, 142, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [231, 233, 49], [141, 23, 208], [0, 1]]
 g := ![![[115, 122, 92], [181, 9], [177, 146], [199, 255], [199, 231], [116, 157], [115, 1], []], ![[214, 169, 28, 228], [227, 134], [209, 255], [49, 231], [108, 4], [117, 11], [31, 15], [58, 88]], ![[66, 244, 202, 165], [162, 88], [84, 60], [7, 84], [40, 72], [188, 123], [200, 62], [156, 88]]]
 h' := ![![[231, 233, 49], [9, 34, 141], [42, 228, 254], [186, 207, 143], [129, 97, 189], [176, 129, 105], [231, 195, 97], [0, 0, 1], [0, 1]], ![[141, 23, 208], [81, 126, 26], [32, 69, 52], [210, 247, 68], [250, 165, 105], [175, 88, 255], [246, 173, 221], [169, 209, 23], [231, 233, 49]], ![[0, 1], [171, 97, 90], [87, 217, 208], [140, 60, 46], [84, 252, 220], [119, 40, 154], [201, 146, 196], [164, 48, 233], [141, 23, 208]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 81], []]
 b := ![[], [53, 253, 98], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 3
  hpos := by decide
  P := [217, 21, 142, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2326746337, 1176511844, -2522367964, -1348172224, -4767498430]
  a := ![174, 136, -265, -119, -551]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4196686955, 2360419870, 3296972092, -1348172224, -4767498430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 16974593 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -14, -4, 0, -8]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![3, -14, -4, 0, -8]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![85, 43, 1, 0, 0], ![100, 18, 0, 1, 0], ![182, 173, 0, 0, 1]] where
  M :=![![![3, -14, -4, 0, -8], ![-32, -33, 42, 24, 128], ![-64, 66, -65, -44, -224], ![96, -78, 4, 19, 56], ![0, -28, 42, 24, 131]]]
  hmulB := by decide  
  f := ![![![-21, -26, 32, 16, 72]], ![![-96, -5, 46, 32, 64]], ![![-25, -11, 21, 12, 40]], ![![-20, -12, 20, 11, 40]], ![![-78, -21, 52, 32, 91]]]
  g := ![![![7, 6, -4, 0, -8], ![-114, -95, 42, 24, 128], ![197, 165, -65, -44, -224], ![-48, -40, 4, 19, 56], ![-116, -97, 42, 24, 131]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [188, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 256], [0, 1]]
 g := ![![[151, 199], [226], [123], [228], [184], [213], [46], [1]], ![[56, 58], [226], [123], [228], [184], [213], [46], [1]]]
 h' := ![![[139, 256], [152, 131], [122, 212], [87, 61], [240, 182], [44, 21], [225, 133], [69, 139], [0, 1]], ![[0, 1], [114, 126], [35, 45], [85, 196], [95, 75], [136, 236], [208, 124], [115, 118], [139, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [166]]
 b := ![[], [14, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [188, 118, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108106657, -72387978, 136990368, 70278865, 270455210]
  a := ![2553, 2006, -3890, -1701, -8084]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-264603201, -210181886, 136990368, 70278865, 270455210]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-21, -26, 32, 16, 72]] ![![3, -14, -4, 0, -8]]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, -48, 38, 22, 100]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![17, -48, 38, 22, 100]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![139, 204, 209, 1, 0], ![251, 144, 7, 0, 1]] where
  M :=![![![17, -48, 38, 22, 100], ![-128, 37, 44, 28, 72], ![-384, -328, 541, 248, 976], ![-960, -344, 862, 559, 1580], ![264, 164, -300, -164, -519]]]
  hmulB := by decide  
  f := ![![![1975, 1440, -606, -422, -1844]], ![![2752, 2011, -844, -588, -2568]], ![![3840, 2808, -1181, -824, -3600]], ![![6235, 4556, -1915, -1335, -5832]], ![![3491, 2548, -1071, -746, -3259]]]
  g := ![![![-107, -72, -20, 22, 100], ![-84, -61, -24, 28, 72], ![-1064, -728, -221, 248, 976], ![-1807, -1300, -483, 559, 1580], ![583, 412, 143, -164, -519]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [189, 35, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [183, 69, 205], [209, 193, 58], [0, 1]]
 g := ![![[70, 248, 248], [250, 3, 105], [259, 38, 124], [241, 26], [118, 244], [244, 54], [129, 1], []], ![[123, 39, 201, 204], [108, 118, 183, 22], [252, 228, 244, 103], [78, 72], [57, 92], [244, 156], [158, 166], [155, 208]], ![[204, 72, 95, 146], [26, 24, 62, 71], [186, 4, 2, 76], [126, 13], [22, 222], [171, 124], [69, 27], [39, 208]]]
 h' := ![![[183, 69, 205], [90, 188, 145], [230, 228, 216], [250, 132, 85], [33, 9, 17], [207, 136, 227], [78, 30, 37], [0, 0, 1], [0, 1]], ![[209, 193, 58], [115, 196, 249], [6, 150, 60], [72, 222, 70], [127, 1, 129], [88, 146, 155], [53, 241, 141], [249, 242, 193], [183, 69, 205]], ![[0, 1], [148, 142, 132], [53, 148, 250], [5, 172, 108], [82, 253, 117], [177, 244, 144], [102, 255, 85], [16, 21, 69], [209, 193, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 127], []]
 b := ![[], [241, 90, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [189, 35, 134, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1541199534, 787025791, -1679547858, -896168455, -3179726883]
  a := ![157, 123, -239, -106, -497]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3514144724, 2439110501, 790409686, -896168455, -3179726883]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -5, -25, -10, -66]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![37, -5, -25, -10, -66]] 
 ![![263, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![168, 0, 1, 0, 0], ![227, 0, 0, 1, 0], ![181, 0, 0, 0, 1]] where
  M :=![![![37, -5, -25, -10, -66], ![-24, -62, 97, 54, 296], ![-112, 231, -190, -126, -632], ![260, -187, 11, 39, 120], ![-2, -87, 109, 64, 341]]]
  hmulB := by decide  
  f := ![![![1319, 1001, -485, -314, -1402]], ![![228, 172, -83, -54, -240]], ![![856, 651, -320, -206, -920]], ![![1151, 866, -424, -275, -1218]], ![![903, 686, -330, -214, -957]]]
  g := ![![![71, -5, -25, -10, -66], ![-302, -62, 97, 54, 296], ![626, 231, -190, -126, -632], ![-91, -187, 11, 39, 120], ![-345, -87, 109, 64, 341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N1 : Nat.card (O ⧸ I263N1) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N1)

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := prime_ideal_of_norm_prime hp263.out _ NI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 83, -100, -39, -241]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![12, 83, -100, -39, -241]] 
 ![![263, 0, 0, 0, 0], ![64, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![12, 83, -100, -39, -241], ![-28, -311, 366, 140, 892], ![208, 1246, -1515, -596, -3632], ![-98, -2100, 2424, 911, 5962], ![-55, -83, 122, 55, 268]]]
  hmulB := by decide  
  f := ![![![4018, 2549, -984, -687, -2923]], ![![996, 637, -246, -172, -732]], ![![1744, 1106, -431, -300, -1280]], ![![1018, 642, -244, -171, -724]], ![![2589, 1645, -634, -443, -1884]]]
  g := ![![![188, 83, -100, -39, -241], ![-692, -311, 366, 140, 892], ![2840, 1246, -1515, -596, -3632], ![-4604, -2100, 2424, 911, 5962], ![-219, -83, 122, 55, 268]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![17, -48, 38, 22, 100]] ![![37, -5, -25, -10, -66]]
  ![![3045, -1145, -1159, -292, -2606]] where
 M := ![![![3045, -1145, -1159, -292, -2606]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![3045, -1145, -1159, -292, -2606]] ![![12, 83, -100, -39, -241]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-526, -5786, 6575, 2367, 14991]]]
 hmul := by decide  
 g := ![![![![-2, -22, 25, 9, 57]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 16, -1, -3, -3]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![-14, 16, -1, -3, -3]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![120, 145, 142, 1, 0], ![64, 29, 217, 0, 1]] where
  M :=![![![-14, 16, -1, -3, -3], ![60, 30, -71, -38, -180], ![192, -9, -78, -30, -8], ![314, 311, -481, -283, -986], ![-109, -32, 81, 43, 90]]]
  hmulB := by decide  
  f := ![![![28, 28, -15, -9, -43]], ![![44, 12, 5, -2, 4]], ![![64, 103, -88, -38, -216]], ![![70, 73, -50, -25, -130]], ![![63, 91, -74, -33, -184]]]
  g := ![![![2, 2, 4, -3, -3], ![60, 40, 165, -38, -180], ![16, 17, 22, -30, -8], ![362, 260, 943, -283, -986], ![-41, -33, -95, 43, 90]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [174, 177, 247, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [163, 235, 87], [128, 33, 182], [0, 1]]
 g := ![![[81, 216, 190], [8, 214], [138, 11, 144], [148, 36, 224], [103, 97], [208, 99], [22, 1], []], ![[248, 192, 0, 93], [85, 66], [238, 244, 259, 67], [245, 98, 7, 84], [200, 170], [73, 9], [37, 13], [9, 37]], ![[268, 36, 38, 202], [156, 127], [7, 104, 238, 169], [231, 154, 190, 182], [207, 249], [95, 149], [134, 80], [183, 37]]]
 h' := ![![[163, 235, 87], [152, 44, 65], [198, 95, 131], [72, 59, 12], [152, 4, 61], [201, 84, 108], [207, 236, 38], [0, 0, 1], [0, 1]], ![[128, 33, 182], [227, 154, 55], [130, 54, 214], [106, 223, 149], [219, 233, 209], [7, 258, 112], [214, 245, 266], [255, 253, 33], [163, 235, 87]], ![[0, 1], [80, 71, 149], [18, 120, 193], [206, 256, 108], [33, 32, 268], [143, 196, 49], [110, 57, 234], [144, 16, 235], [128, 33, 182]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 83], []]
 b := ![[], [140, 114, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [174, 177, 247, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-370683537749, -194795437841, 410153901644, 217859000495, 780126603713]
  a := ![-995, -783, 1516, 663, 3151]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-284170506449, -202260304897, -742800361243, 217859000495, 780126603713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1184, 864, -363, -253, -1105]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![1184, 864, -363, -253, -1105]] 
 ![![269, 0, 0, 0, 0], ![65, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![90, 0, 0, 1, 0], ![233, 0, 0, 0, 1]] where
  M :=![![![1184, 864, -363, -253, -1105], ![1652, 1208, -509, -354, -1548], ![2304, 1677, -700, -490, -2136], ![782, 581, -251, -171, -758], ![-455, -332, 139, 97, 424]]]
  hmulB := by decide  
  f := ![![![466, -252, -89, 5, -145]], ![![110, -62, -18, 3, -25]], ![![134, -67, -33, -3, -67]], ![![162, -95, -23, 7, -28]], ![![403, -220, -74, 6, -115]]]
  g := ![![![944, 864, -363, -253, -1105], ![1323, 1208, -509, -354, -1548], ![1823, 1677, -700, -490, -2136], ![650, 581, -251, -171, -758], ![-362, -332, 139, 97, 424]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -8, 2, 2, 8]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![9, -8, 2, 2, 8]] 
 ![![269, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![245, 0, 0, 0, 1]] where
  M :=![![![9, -8, 2, 2, 8], ![-16, 5, 8, 4, 24], ![0, 12, -19, -16, -80], ![40, -20, -6, 11, 20], ![-12, -4, 16, 8, 49]]]
  hmulB := by decide  
  f := ![![![-6571, -4808, 2026, 1410, 6160]], ![![-4651, -3403, 1434, 998, 4360]], ![![-1416, -1036, 437, 304, 1328]], ![![-3144, -2300, 970, 675, 2948]], ![![-5975, -4372, 1842, 1282, 5601]]]
  g := ![![![-3, -8, 2, 2, 8], ![-29, 5, 8, 4, 24], ![76, 12, -19, -16, -80], ![-8, -20, -6, 11, 20], ![-49, -4, 16, 8, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![-14, 16, -1, -3, -3]] ![![1184, 864, -363, -253, -1105]]
  ![![6571, 4808, -2026, -1410, -6160]] where
 M := ![![![6571, 4808, -2026, -1410, -6160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![6571, 4808, -2026, -1410, -6160]] ![![9, -8, 2, 2, 8]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![866, 232, -1019, -489, -2903]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![866, 232, -1019, -489, -2903]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![25, 135, 46, 25, 1]] where
  M :=![![![866, 232, -1019, -489, -2903], ![124, -2474, 2949, 1750, 9284], ![-4864, 6959, -4462, -3238, -15544], ![7706, -3753, -1875, -153, -3334], ![859, -3112, 3109, 1943, 10018]]]
  hmulB := by decide  
  f := ![![![-204, -148, 61, 43, 187]], ![![-284, -212, 91, 62, 276]], ![![-384, -267, 88, 70, 296]], ![![-106, -115, 45, 25, 154]], ![![-235, -175, 70, 49, 219]]]
  g := ![![![271, 1447, 489, 266, -2903], ![-856, -4634, -1565, -850, 9284], ![1416, 7769, 2622, 1422, -15544], ![336, 1647, 559, 307, -3334], ![-921, -5002, -1689, -917, 10018]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [162, 166, 119, 188, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [266, 253, 220, 162], [65, 52, 69, 84], [23, 236, 253, 25], [0, 1]]
 g := ![![[82, 51, 22, 82], [93, 11, 151, 169], [48, 73, 234, 74], [22, 124, 156, 22], [139, 103, 61], [95, 6, 114], [1], []], ![[191, 7, 113, 266, 234, 100], [241, 177, 20, 59, 187, 70], [161, 98, 112, 212, 10, 196], [108, 23, 130, 201, 219, 122], [155, 199, 125], [133, 82, 225], [25, 26, 80], [4, 232, 228]], ![[52, 2, 75, 57, 31, 236], [118, 250, 63, 170, 230, 207], [12, 20, 246, 0, 115, 142], [124, 90, 139, 157, 269, 183], [112, 209, 195], [164, 153, 178], [215, 100, 31], [254, 227, 10]], ![[215, 96, 237, 24, 74, 85], [103, 225, 25, 36, 222, 139], [159, 83, 177, 95, 8, 187], [14, 177, 230, 225, 259, 14], [50, 110, 55], [167, 66, 187], [198, 115, 17], [152, 27, 83]]]
 h' := ![![[266, 253, 220, 162], [110, 238, 30, 176], [83, 44, 221, 258], [230, 81, 206, 133], [171, 136, 201, 70], [14, 186, 113, 50], [109, 105, 152, 83], [0, 0, 1], [0, 1]], ![[65, 52, 69, 84], [127, 203, 81, 234], [243, 98, 82, 8], [215, 28, 50, 106], [199, 34, 224, 145], [169, 170, 48, 165], [72, 179, 130, 15], [190, 143, 248, 132], [266, 253, 220, 162]], ![[23, 236, 253, 25], [75, 64, 220, 93], [39, 178, 22, 191], [17, 42, 174, 200], [139, 154, 197, 226], [111, 110, 211, 97], [11, 4, 220, 146], [204, 179, 140, 207], [65, 52, 69, 84]], ![[0, 1], [143, 37, 211, 39], [173, 222, 217, 85], [107, 120, 112, 103], [268, 218, 191, 101], [77, 76, 170, 230], [207, 254, 40, 27], [24, 220, 153, 203], [23, 236, 253, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [203, 2, 190], []]
 b := ![[], [], [182, 226, 105, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [162, 166, 119, 188, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13330001948640, -6704354420108, 14409032845968, 7709682093066, 27207643019684]
  a := ![221, 177, -336, -143, -700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2559118366940, -13578362221688, -4565101645976, -2481481156454, 27207643019684]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![204, 148, -61, -43, -187]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![204, 148, -61, -43, -187]] 
 ![![271, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![219, 0, 0, 0, 1]] where
  M :=![![![204, 148, -61, -43, -187], ![284, 212, -91, -62, -276], ![384, 267, -88, -70, -296], ![106, 115, -45, -25, -154], ![-69, -52, 13, 11, 52]]]
  hmulB := by decide  
  f := ![![![-866, -232, 1019, 489, 2903]], ![![-42, -2, 38, 17, 105]], ![![-308, -113, 400, 196, 1150]], ![![-54, 7, 37, 15, 98]], ![![-703, -176, 812, 388, 2309]]]
  g := ![![![169, 148, -61, -43, -187], ![250, 212, -91, -62, -276], ![263, 267, -88, -70, -296], ![137, 115, -45, -25, -154], ![-45, -52, 13, 11, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![866, 232, -1019, -489, -2903]] ![![204, 148, -61, -43, -187]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2879, 2130, -828, -588, -2620]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![2879, 2130, -828, -588, -2620]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![154, 125, 205, 262, 1]] where
  M :=![![![2879, 2130, -828, -588, -2620], ![3632, 2743, -698, -584, -2768], ![2944, 2958, 1095, 332, -96], ![-5992, -2698, 8140, 4235, 14768], ![1124, 272, -2058, -1052, -3457]]]
  hmulB := by decide  
  f := ![![![27, 14, -40, -20, -116]], ![![16, -97, 106, 64, 336]], ![![-192, 250, -145, -108, -512]], ![![264, -118, -80, -17, -176]], ![![130, 37, -157, -78, -457]]]
  g := ![![![1467, 1190, 1936, 2476, -2620], ![1552, 1259, 2046, 2616, -2768], ![64, 54, 75, 92, -96], ![-8232, -6674, -10900, -13953, 14768], ![1926, 1561, 2551, 3266, -3457]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [50, 182, 157, 66, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [256, 270, 1, 5], [232, 223, 107, 272], [0, 60, 169], [0, 1]]
 g := ![![[150, 47, 36, 16], [268, 87, 189], [203, 240, 53, 40], [149, 271, 186], [259, 141, 230, 171], [220, 256, 201], [1], []], ![[119, 163, 107, 174, 4, 204], [260, 186, 133], [86, 1, 276, 238, 186, 168], [20, 249, 254], [191, 59, 40, 7, 40, 98], [141, 223, 222], [180, 147, 230], [94, 22, 25]], ![[220, 260, 214, 129, 115, 263], [150, 83, 154], [168, 205, 251, 236, 161, 195], [54, 135, 69], [241, 209, 93, 270, 5, 233], [47, 271, 201], [267, 180, 100], [55, 50, 25]], ![[0, 119, 270, 6, 70], [263, 55, 248], [260, 185, 80, 146, 69], [108, 244, 196], [83, 259, 203, 131, 9], [8, 224, 215], [9, 150, 47], [30]]]
 h' := ![![[256, 270, 1, 5], [2, 97, 275, 4], [99, 273, 217, 110], [81, 231, 132, 219], [69, 194, 172, 179], [87, 262, 23, 154], [227, 95, 120, 211], [0, 0, 1], [0, 1]], ![[232, 223, 107, 272], [3, 258, 82, 255], [240, 272, 27, 166], [118, 125, 121, 221], [29, 36, 122, 114], [46, 267, 94, 181], [154, 240, 160, 172], [173, 91, 216, 249], [256, 270, 1, 5]], ![[0, 60, 169], [91, 194, 26, 13], [77, 40, 3, 92], [8, 10, 202, 133], [237, 222, 185, 247], [21, 50, 37, 27], [102, 57, 101, 211], [106, 106, 62, 10], [232, 223, 107, 272]], ![[0, 1], [230, 5, 171, 5], [19, 246, 30, 186], [165, 188, 99, 258], [5, 102, 75, 14], [135, 252, 123, 192], [33, 162, 173, 237], [162, 80, 275, 18], [0, 60, 169]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [178, 177, 239], []]
 b := ![[], [], [247, 73, 180, 214], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [50, 182, 157, 66, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-697265344670, -727971664388, 1180322279556, 560447734744, 2483991432800]
  a := ![-168, -142, 256, 94, 532]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1383508830310, -1123562818644, -1834071918572, -2347455984328, 2483991432800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -14, 40, 20, 116]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-27, -14, 40, 20, 116]] 
 ![![277, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![149, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![-27, -14, 40, 20, 116], ![-16, 97, -106, -64, -336], ![192, -250, 145, 108, 512], ![-264, 118, 80, 17, 176], ![-44, 116, -106, -68, -347]]]
  hmulB := by decide  
  f := ![![![-2879, -2130, 828, 588, 2620]], ![![-512, -379, 146, 104, 464]], ![![-1975, -1464, 561, 400, 1788]], ![![-1527, -1136, 416, 301, 1356]], ![![-1376, -1016, 402, 284, 1261]]]
  g := ![![![-91, -14, 40, 20, 116], ![250, 97, -106, -64, -336], ![-357, -250, 145, 108, 512], ![-169, 118, 80, 17, 176], ![254, 116, -106, -68, -347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![2879, 2130, -828, -588, -2620]] ![![-27, -14, 40, 20, 116]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -14, 32, 16, 58]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-31, -14, 32, 16, 58]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![34, 179, 1, 0, 0], ![48, 14, 0, 1, 0], ![263, 120, 0, 0, 1]] where
  M :=![![![-31, -14, 32, 16, 58], ![-152, -71, 156, 88, 288], ![-960, -516, 1081, 568, 2080], ![-2580, -1140, 2608, 1421, 4800], ![754, 360, -796, -426, -1495]]]
  hmulB := by decide  
  f := ![![![4829, 3526, -1472, -1028, -4482]], ![![6744, 4961, -2108, -1464, -6416]], ![![4914, 3611, -1531, -1064, -4660]], ![![1172, 858, -360, -251, -1096]], ![![7393, 5414, -2276, -1586, -6929]]]
  g := ![![![-61, -46, 32, 16, 58], ![-304, -227, 156, 88, 288], ![-2178, -1607, 1081, 568, 2080], ![-5060, -3786, 2608, 1421, 4800], ![1571, 1168, -796, -426, -1495]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [236, 258, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 280], [0, 1]]
 g := ![![[13, 256], [116], [218], [8, 7], [89, 196], [125], [248], [1]], ![[0, 25], [116], [218], [169, 274], [101, 85], [125], [248], [1]]]
 h' := ![![[23, 280], [194, 16], [34, 242], [79, 201], [71, 179], [208, 267], [259, 187], [45, 23], [0, 1]], ![[0, 1], [0, 265], [261, 39], [206, 80], [254, 102], [167, 14], [64, 94], [12, 258], [23, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [90, 151]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [236, 258, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92544, -51040, 109123, 59388, 211490]
  a := ![-23, -11, 37, 27, 75]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-221620, -162969, 109123, 59388, 211490]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-355, -248, 104, 72, 314]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![-355, -248, 104, 72, 314]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![148, 173, 1, 0, 0], ![124, 3, 0, 1, 0], ![223, 156, 0, 0, 1]] where
  M :=![![![-355, -248, 104, 72, 314], ![-472, -363, 146, 104, 448], ![-704, -510, 245, 164, 736], ![-260, -134, 48, 33, 120], ![154, 96, -54, -34, -155]]]
  hmulB := by decide  
  f := ![![![33, 344, -404, -156, -978]], ![![-168, -1319, 1574, 608, 3792]], ![![-84, -613, 735, 284, 1768]], ![![8, 105, -122, -47, -296]], ![![-67, -460, 554, 214, 1331]]]
  g := ![![![-337, -240, 104, 72, 314], ![-480, -341, 146, 104, 448], ![-788, -563, 245, 164, 736], ![-136, -97, 48, 33, 120], ![167, 120, -54, -34, -155]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [117, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [280, 280], [0, 1]]
 g := ![![[269, 272], [183], [32], [69, 10], [10, 279], [56], [1], [1]], ![[278, 9], [183], [32], [59, 271], [12, 2], [56], [1], [1]]]
 h' := ![![[280, 280], [236, 122], [65, 78], [76, 34], [235, 216], [223, 29], [84, 233], [164, 280], [0, 1]], ![[0, 1], [114, 159], [268, 203], [42, 247], [19, 65], [194, 252], [132, 48], [165, 1], [280, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [278]]
 b := ![[], [210, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [117, 1, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72046, -42175, 84590, 44241, 163425]
  a := ![59, 45, -90, -41, -187]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-194025, -143428, 84590, 44241, 163425]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, -12, -4, -28]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![-7, 6, -12, -4, -28]] 
 ![![281, 0, 0, 0, 0], ![210, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-7, 6, -12, -4, -28], ![-16, -55, 58, 24, 144], ![0, 162, -199, -76, -480], ![-40, -310, 364, 141, 880], ![4, -8, 10, 4, 25]]]
  hmulB := by decide  
  f := ![![![-143, -126, 208, 116, 476]], ![![-110, -95, 158, 88, 360]], ![![-23, -16, 29, 16, 60]], ![![-83, -56, 104, 57, 220]], ![![-7, -10, 14, 8, 37]]]
  g := ![![![1, 6, -12, -4, -28], ![12, -55, 58, 24, 144], ![-25, 162, -199, -76, -480], ![55, -310, 364, 141, 880], ![1, -8, 10, 4, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-31, -14, 32, 16, 58]] ![![-355, -248, 104, 72, 314]]
  ![![-143, -126, 208, 116, 476]] where
 M := ![![![-143, -126, 208, 116, 476]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-143, -126, 208, 116, 476]] ![![-7, 6, -12, -4, -28]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![281, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-977, 487, 217, 4, 356]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![-977, 487, 217, 4, 356]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![148, 70, 250, 1, 0], ![246, 92, 218, 0, 1]] where
  M :=![![![-977, 487, 217, 4, 356], ![1328, 588, -1861, -926, -5392], ![656, -4507, 4996, 3030, 15896], ![-5232, 5539, -2419, -2093, -9332], ![984, 1201, -2313, -1238, -6929]]]
  hmulB := by decide  
  f := ![![![-11, -59, 53, 20, 140]], ![![80, 222, -319, -134, -720]], ![![336, -573, 438, 98, 1336]], ![![316, -475, 325, 59, 1052]], ![![274, -421, 281, 50, 919]]]
  g := ![![![-315, -115, -277, 4, 356], ![5176, 1984, 4965, -926, -5392], ![-15400, -5933, -14904, 3030, 15896], ![9188, 3571, 9029, -2093, -9332], ![6674, 2563, 6423, -1238, -6929]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 3 2 8 [275, 217, 126, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 70, 55], [98, 212, 228], [0, 1]]
 g := ![![[255, 71, 271], [138, 132, 85], [126, 101], [277, 220, 117], [58, 36, 62], [242, 63], [157, 1], []], ![[142, 156, 29, 31], [146, 118, 132, 120], [143, 262], [217, 127, 231, 120], [279, 215, 46, 124], [53, 204], [119, 230], [110, 195]], ![[249, 154, 59, 275], [14, 74, 136, 51], [142, 97], [208, 71, 32, 57], [49, 129, 44, 256], [256, 24], [256, 89], [220, 195]]]
 h' := ![![[59, 70, 55], [255, 240, 178], [199, 76, 224], [235, 165, 147], [181, 8, 263], [49, 201, 104], [124, 182, 94], [0, 0, 1], [0, 1]], ![[98, 212, 228], [254, 74, 279], [103, 269, 162], [137, 214, 53], [31, 258, 162], [200, 132, 275], [258, 66, 223], [116, 100, 212], [59, 70, 55]], ![[0, 1], [194, 252, 109], [240, 221, 180], [233, 187, 83], [85, 17, 141], [268, 233, 187], [22, 35, 249], [44, 183, 70], [98, 212, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 196], []]
 b := ![[], [2, 37, 264], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 3
  hpos := by decide
  P := [275, 217, 126, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11149283777, -5842211493, 12317318385, 6545913480, 23416534772]
  a := ![-303, -239, 463, 203, 960]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23817710363, -9252216799, -23777263717, 6545913480, 23416534772]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 22665187 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 22, -29, -17, -91]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![2, 22, -29, -17, -91]] 
 ![![283, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![202, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![2, 22, -29, -17, -91], ![44, -68, 47, 34, 164], ![-160, 101, 8, -18, -40], ![114, 49, -157, -73, -446], ![63, -74, 39, 31, 146]]]
  hmulB := by decide  
  f := ![![![38332, 27982, -11757, -8193, -35789]], ![![1408, 1028, -432, -301, -1315]], ![![27624, 20165, -8472, -5904, -25790]], ![![10518, 7679, -3226, -2248, -9821]], ![![11055, 8070, -3391, -2363, -10322]]]
  g := ![![![51, 22, -29, -17, -91], ![-88, -68, 47, 34, 164], ![7, 101, 8, -18, -40], ![260, 49, -157, -73, -446], ![-76, -74, 39, 31, 146]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1

def I283N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![169, 122, -52, -36, -158]] i)))

def SI283N2: IdealEqSpanCertificate' Table ![![169, 122, -52, -36, -158]] 
 ![![283, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![147, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![112, 0, 0, 0, 1]] where
  M :=![![![169, 122, -52, -36, -158], ![232, 169, -68, -48, -208], ![320, 244, -103, -72, -320], ![108, 68, -20, -15, -72], ![-62, -48, 20, 14, 65]]]
  hmulB := by decide  
  f := ![![![239, 1658, -2004, -768, -4830]], ![![45, 311, -376, -144, -906]], ![![135, 950, -1147, -440, -2766]], ![![3, -2, 0, 1, 2]], ![![94, 652, -788, -302, -1899]]]
  g := ![![![69, 122, -52, -36, -158], ![89, 169, -68, -48, -208], ![139, 244, -103, -72, -320], ![27, 68, -20, -15, -72], ![-28, -48, 20, 14, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N2 : Nat.card (O ⧸ I283N2) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N2)

lemma isPrimeI283N2 : Ideal.IsPrime I283N2 := prime_ideal_of_norm_prime hp283.out _ NI283N2
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![-977, 487, 217, 4, 356]] ![![2, 22, -29, -17, -91]]
  ![![7638, -58841, 66214, 40005, 210287]] where
 M := ![![![7638, -58841, 66214, 40005, 210287]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI283N1 : IdealMulLeCertificate' Table 
  ![![7638, -58841, 66214, 40005, 210287]] ![![169, 122, -52, -36, -158]]
  ![![283, 0, 0, 0, 0]] where
 M := ![![![110936, -229513, 189610, 125935, 631939]]]
 hmul := by decide  
 g := ![![![![392, -811, 670, 445, 2233]]]]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![141, 135, -51, -38, -162]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![141, 135, -51, -38, -162]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![252, 21, 172, 1, 0], ![271, 195, 92, 0, 1]] where
  M :=![![![141, 135, -51, -38, -162], ![264, 164, -99, -62, -296], ![304, 159, 4, -6, 24], ![-12, 177, -63, -61, -272], ![-26, -29, -31, -12, -83]]]
  hmulB := by decide  
  f := ![![![-3, 7, -5, -2, -14]], ![![-8, -26, 33, 14, 72]], ![![-48, 47, -26, 2, -88]], ![![-32, 31, -16, 1, -56]], ![![-23, 4, 9, 8, 7]]]
  g := ![![![183, 111, 73, -38, -162], ![328, 202, 129, -62, -296], ![-16, -15, -4, -6, 24], ![304, 186, 121, -61, -272], ![87, 56, 33, -12, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 3 2 8 [25, 46, 214, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 291, 94], [70, 1, 199], [0, 1]]
 g := ![![[152, 56, 255], [186, 90], [207, 206, 289], [16, 224], [124, 95], [208, 182, 6], [79, 1], []], ![[109, 73, 114, 115], [247, 71], [269, 19, 154, 206], [213, 96], [12, 59], [10, 268, 78, 253], [54, 1], [35, 46]], ![[157, 198, 211, 25], [170, 238], [207, 86, 249, 57], [207, 158], [244, 61], [65, 7, 6, 60], [266, 4], [223, 46]]]
 h' := ![![[9, 291, 94], [170, 18, 264], [99, 250, 26], [38, 136, 17], [32, 211, 215], [74, 155, 238], [76, 150, 42], [0, 0, 1], [0, 1]], ![[70, 1, 199], [211, 180, 198], [164, 54, 86], [70, 248, 202], [282, 260, 125], [17, 231, 158], [15, 54, 78], [85, 134, 1], [9, 291, 94]], ![[0, 1], [202, 95, 124], [49, 282, 181], [134, 202, 74], [62, 115, 246], [290, 200, 190], [99, 89, 173], [204, 159, 291], [70, 1, 199]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115, 183], []]
 b := ![[], [169, 2, 263], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 3
  hpos := by decide
  P := [25, 46, 214, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1519922559, -839795468, 1728028908, 910582524, 3313632524]
  a := ![-167, -133, 254, 109, 529]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3853177927, -2273448364, -1569100196, 910582524, 3313632524]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 25153757 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -7, 5, 2, 14]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![3, -7, 5, 2, 14]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![191, 242, 1, 0, 0], ![36, 114, 0, 1, 0], ![178, 127, 0, 0, 1]] where
  M :=![![![3, -7, 5, 2, 14], ![8, 26, -33, -14, -72], ![48, -47, 26, -2, 88], ![196, 219, -351, -159, -744], ![-50, -21, 51, 28, 99]]]
  hmulB := by decide  
  f := ![![![-141, -135, 51, 38, 162]], ![![-264, -164, 99, 62, 296]], ![![-311, -224, 115, 76, 350]], ![![-120, -81, 45, 29, 136]], ![![-200, -153, 74, 50, 227]]]
  g := ![![![-12, -11, 5, 2, 14], ![67, 64, -33, -14, -72], ![-70, -59, 26, -2, 88], ![701, 675, -351, -159, -744], ![-97, -96, 51, 28, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P1 : CertificateIrreducibleZModOfList' 293 2 2 8 [206, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [273, 292], [0, 1]]
 g := ![![[185, 229], [35], [71, 184], [284], [226], [66, 172], [107], [1]], ![[0, 64], [35], [200, 109], [284], [226], [142, 121], [107], [1]]]
 h' := ![![[273, 292], [105, 225], [24, 62], [257, 188], [184, 172], [175, 144], [177, 240], [87, 273], [0, 1]], ![[0, 1], [0, 68], [249, 231], [13, 105], [260, 121], [225, 149], [65, 53], [194, 20], [273, 292]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [235, 170]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N1 : CertifiedPrimeIdeal' SI293N1 293 where
  n := 2
  hpos := by decide
  P := [206, 20, 1]
  hirr := P293P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-36746, -18316, 39836, 21317, 75122]
  a := ![-32, -23, 49, 25, 102]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-74350, -73820, 39836, 21317, 75122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N1 B_one_repr
lemma NI293N1 : Nat.card (O ⧸ I293N1) = 85849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![141, 135, -51, -38, -162]] ![![3, -7, 5, 2, 14]]
  ![![293, 0, 0, 0, 0]] where
 M := ![![![-293, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 5, -11, -6, -34]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-5, 5, -11, -6, -34]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![55, 106, 1, 0, 0], ![155, 243, 0, 1, 0], ![262, 22, 0, 0, 1]] where
  M :=![![![-5, 5, -11, -6, -34], ![8, -38, 27, 18, 88], ![-80, 45, -6, -10, -40], ![36, -9, -31, -15, -104], ![30, -29, 15, 12, 59]]]
  hmulB := by decide  
  f := ![![![-19, -5, -3, 2, -2]], ![![-56, -68, 81, 34, 184]], ![![-23, -24, 27, 12, 62]], ![![-55, -58, 65, 29, 150]], ![![-20, -9, 3, 4, 11]]]
  g := ![![![34, 11, -11, -6, -34], ![-89, -30, 27, 18, 88], ![40, 13, -6, -10, -40], ![102, 30, -31, -15, -104], ![-59, -19, 15, 12, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [88, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [283, 306], [0, 1]]
 g := ![![[84, 9], [132, 235], [36], [76], [248, 4], [301, 135], [269], [1]], ![[175, 298], [18, 72], [36], [76], [152, 303], [131, 172], [269], [1]]]
 h' := ![![[283, 306], [50, 3], [121, 34], [181, 301], [280, 171], [221, 305], [36, 224], [219, 283], [0, 1]], ![[0, 1], [285, 304], [226, 273], [18, 6], [167, 136], [269, 2], [186, 83], [181, 24], [283, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148]]
 b := ![[], [274, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 2
  hpos := by decide
  P := [88, 24, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9019527, -5251138, 10550757, 5521115, 20380454]
  a := ![649, 505, -992, -453, -2054]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22100205, -9490659, 10550757, 5521115, 20380454]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-120, -88, 35, 25, 109]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-120, -88, 35, 25, 109]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![173, 281, 1, 0, 0], ![100, 56, 0, 1, 0], ![157, 251, 0, 0, 1]] where
  M :=![![![-120, -88, 35, 25, 109], ![-164, -124, 49, 34, 156], ![-192, -137, 8, 18, 88], ![42, -25, -77, -41, -98], ![11, 16, 25, 11, 32]]]
  hmulB := by decide  
  f := ![![![98, -60, -9, 9, 11]], ![![-172, -38, 187, 82, 508]], ![![-102, -67, 164, 79, 465]], ![![2, -29, 33, 19, 102]], ![![-91, -62, 149, 72, 423]]]
  g := ![![![-84, -126, 35, 25, 109], ![-119, -179, 49, 34, 156], ![-56, -83, 8, 18, 88], ![107, 158, -77, -41, -98], ![-34, -51, 25, 11, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P1 : CertificateIrreducibleZModOfList' 307 2 2 8 [233, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [239, 306], [0, 1]]
 g := ![![[248, 112], [290, 9], [196], [46], [134, 25], [156, 9], [19], [1]], ![[0, 195], [292, 298], [196], [46], [276, 282], [158, 298], [19], [1]]]
 h' := ![![[239, 306], [277, 135], [48, 3], [202, 14], [92, 254], [185, 302], [128, 3], [74, 239], [0, 1]], ![[0, 1], [0, 172], [151, 304], [171, 293], [12, 53], [218, 5], [231, 304], [93, 68], [239, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153]]
 b := ![[], [145, 230]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N1 : CertifiedPrimeIdeal' SI307N1 307 where
  n := 2
  hpos := by decide
  P := [233, 68, 1]
  hirr := P307P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-374529, -198420, 415203, 220603, 789170]
  a := ![121, 93, -185, -88, -383]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-710634, -1066143, 415203, 220603, 789170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N1 B_one_repr
lemma NI307N1 : Nat.card (O ⧸ I307N1) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 5, -6, -3, -17]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![0, 5, -6, -3, -17]] 
 ![![307, 0, 0, 0, 0], ![227, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![217, 0, 0, 0, 1]] where
  M :=![![![0, 5, -6, -3, -17], ![4, -17, 16, 8, 44], ![-16, 44, -37, -16, -96], ![-2, -58, 62, 23, 138], ![9, -9, 4, 3, 16]]]
  hmulB := by decide  
  f := ![![![-1266, -933, 406, 281, 1233]], ![![-942, -694, 302, 209, 917]], ![![-202, -149, 65, 45, 197]], ![![-326, -240, 106, 73, 320]], ![![-893, -658, 286, 198, 869]]]
  g := ![![![10, 5, -6, -3, -17], ![-23, -17, 16, 8, 44], ![45, 44, -37, -16, -96], ![-70, -58, 62, 23, 138], ![-6, -9, 4, 3, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-5, 5, -11, -6, -34]] ![![-120, -88, 35, 25, 109]]
  ![![1266, 933, -406, -281, -1233]] where
 M := ![![![1266, 933, -406, -281, -1233]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![1266, 933, -406, -281, -1233]] ![![0, 5, -6, -3, -17]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![-307, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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
  g := ![2, 3, 3, 2, 2, 3, 3, 2, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB547I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1, I269N2]
    · exact ![I271N0, I271N1]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2]
    · exact ![I283N0, I283N1, I283N2]
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
    · exact ![16974593, 66049]
    · exact ![18191447, 263, 263]
    · exact ![19465109, 269, 269]
    · exact ![5393580481, 271]
    · exact ![5887339441, 277]
    · exact ![78961, 78961, 281]
    · exact ![22665187, 283, 283]
    · exact ![25153757, 85849]
    · exact ![94249, 94249, 307]
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
      exact NI283N1
      exact NI283N2
    · dsimp ; intro j
      fin_cases j
      exact NI293N0
      exact NI293N1
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
  β := ![I263N1, I263N2, I269N1, I269N2, I271N1, I277N1, I281N2, I283N1, I283N2, I307N2]
  Il := ![[], [I263N1, I263N2], [I269N1, I269N2], [I271N1], [I277N1], [I281N2], [I283N1, I283N2], [], [I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
