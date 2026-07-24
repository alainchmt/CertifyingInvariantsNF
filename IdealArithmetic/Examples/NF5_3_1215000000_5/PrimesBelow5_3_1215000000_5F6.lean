
import IdealArithmetic.Examples.NF5_3_1215000000_5.RI5_3_1215000000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp257 : Fact (Nat.Prime 257) := {out := by norm_num}

def I257N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-159137, -53852, 46852, 17114, 70458]] i)))

def SI257N0: IdealEqSpanCertificate' Table ![![-159137, -53852, 46852, 17114, 70458]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![165, 121, 1, 0, 0], ![169, 87, 0, 1, 0], ![37, 156, 0, 0, 1]] where
  M :=![![![-159137, -53852, 46852, 17114, 70458], ![-525432, -171635, 151516, 55472, 227584], ![-1698336, -563116, 494029, 180696, 742432], ![-2506668, -826676, 726860, 265949, 1092136], ![872298, 287752, -252984, -92562, -380121]]]
  hmulB := by decide  
  f := ![![![1091, -1572, -1444, -26, -3634]], ![![21960, 13845, -1884, 4224, 20816]], ![![10455, 5477, -1563, 1894, 7606]], ![![7927, 2675, -2068, 1283, 2718]], ![![14005, 8464, -1420, 2656, 12521]]]
  g := ![![![-52097, -70830, 46852, 17114, 70458], ![-168564, -228927, 151516, 55472, 227584], ![-549497, -746617, 494029, 180696, 742432], ![-808533, -1098395, 726860, 265949, 1092136], ![281409, 382298, -252984, -92562, -380121]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P0 : CertificateIrreducibleZModOfList' 257 2 2 8 [86, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [155, 256], [0, 1]]
 g := ![![[49, 17], [104], [95], [153], [232], [169], [124], [1]], ![[114, 240], [104], [95], [153], [232], [169], [124], [1]]]
 h' := ![![[155, 256], [169, 187], [142, 238], [49, 159], [247, 47], [47, 80], [73, 13], [171, 155], [0, 1]], ![[0, 1], [113, 70], [24, 19], [22, 98], [79, 210], [111, 177], [32, 244], [38, 102], [155, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [243]]
 b := ![[], [157, 250]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 2
  hpos := by decide
  P := [86, 102, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-621244, -58742, 255903, -53846, 175180]
  a := ![33, -74, -69, -37, -209]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-156525, -208819, 255903, -53846, 175180]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N0 : Ideal.IsPrime I257N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N0 B_one_repr
lemma NI257N0 : Nat.card (O ⧸ I257N0) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N0

def I257N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7651, -3459, 859, 190, 1558]] i)))

def SI257N1: IdealEqSpanCertificate' Table ![![7651, -3459, 859, 190, 1558]] 
 ![![257, 0, 0, 0, 0], ![0, 257, 0, 0, 0], ![59, 95, 1, 0, 0], ![153, 15, 0, 1, 0], ![184, 63, 0, 0, 1]] where
  M :=![![![7651, -3459, 859, 190, 1558], ![-10488, 4748, -1179, -258, -2128], ![14316, -6509, 1652, 350, 2964], ![-4698, 1957, -565, -133, -1178], ![1224, -484, 116, 40, 277]]]
  hmulB := by decide  
  f := ![![![222227, 79205, -60091, -22050, -92226]], ![![685656, 244390, -185395, -68030, -284544]], ![![312701, 111456, -84552, -31026, -129770]], ![![183681, 65468, -49667, -18225, -76228]], ![![322936, 115102, -87321, -32042, -134019]]]
  g := ![![![-1396, -724, 859, 190, 1558], ![1907, 991, -1179, -258, -2128], ![-2654, -1383, 1652, 350, 2964], ![1034, 513, -565, -133, -1178], ![-244, -115, 116, 40, 277]]]
  hle1 := by decide   
  hle2 := by decide  


def P257P1 : CertificateIrreducibleZModOfList' 257 2 2 8 [129, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [254, 256], [0, 1]]
 g := ![![[6, 2], [231], [136], [58], [67], [62], [9], [1]], ![[0, 255], [231], [136], [58], [67], [62], [9], [1]]]
 h' := ![![[254, 256], [77, 197], [249, 105], [211, 176], [165, 40], [228, 18], [60, 233], [128, 254], [0, 1]], ![[0, 1], [0, 60], [191, 152], [197, 81], [45, 217], [174, 239], [132, 24], [137, 3], [254, 256]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [73, 220]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N1 : CertifiedPrimeIdeal' SI257N1 257 where
  n := 2
  hpos := by decide
  P := [129, 3, 1]
  hirr := P257P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2356518, -2333519, -283437, -479783, -3867077]
  a := ![-45, 35, 95, -17, 286]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3110176, 1071656, -283437, -479783, -3867077]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI257N1 : Ideal.IsPrime I257N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI257N1 B_one_repr
lemma NI257N1 : Nat.card (O ⧸ I257N1) = 66049 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI257N1

def I257N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1238, 395, -367, -129, -557]] i)))

def SI257N2: IdealEqSpanCertificate' Table ![![1238, 395, -367, -129, -557]] 
 ![![257, 0, 0, 0, 0], ![41, 1, 0, 0, 0], ![118, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![1238, 395, -367, -129, -557], ![4116, 1422, -1153, -394, -1560], ![11724, 4081, -3306, -1550, -5612], ![19428, 4647, -6683, -2147, -11834], ![-5775, -1600, 1880, 875, 3808]]]
  hmulB := by decide  
  f := ![![![-68582906, 30990075, -7701109, -1702033, -13974959]], ![![-10575242, 4778531, -1187470, -262443, -2154867]], ![![-31991560, 14455751, -3592278, -793932, -6518798]], ![![-372518, 168237, -41787, -9231, -75838]], ![![-9113287, 4117990, -1023338, -226171, -1857016]]]
  g := ![![![185, 395, -367, -129, -557], ![528, 1422, -1153, -394, -1560], ![1667, 4081, -3306, -1550, -5612], ![3985, 4647, -6683, -2147, -11834], ![-1141, -1600, 1880, 875, 3808]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI257N2 : Nat.card (O ⧸ I257N2) = 257 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI257N2)

lemma isPrimeI257N2 : Ideal.IsPrime I257N2 := prime_ideal_of_norm_prime hp257.out _ NI257N2
def MulI257N0 : IdealMulLeCertificate' Table 
  ![![-159137, -53852, 46852, 17114, 70458]] ![![7651, -3459, 859, 190, 1558]]
  ![![23814841, -10803655, 2696047, 598144, 4887512]] where
 M := ![![![23814841, -10803655, 2696047, 598144, 4887512]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI257N1 : IdealMulLeCertificate' Table 
  ![![23814841, -10803655, 2696047, 598144, 4887512]] ![![1238, 395, -367, -129, -557]]
  ![![257, 0, 0, 0, 0]] where
 M := ![![![18744038, 6188560, -5437606, -1989437, -8170801]]]
 hmul := by decide  
 g := ![![![![72934, 24080, -21158, -7741, -31793]]]]
 hle2 := by decide  


def PBC257 : ContainsPrimesAboveP 257 ![I257N0, I257N1, I257N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI257N0
    exact isPrimeI257N1
    exact isPrimeI257N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 257 (by decide) (𝕀 ⊙ MulI257N0 ⊙ MulI257N1)
instance hp263 : Fact (Nat.Prime 263) := {out := by norm_num}

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-102383, 46270, -11500, -2542, -20868]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-102383, 46270, -11500, -2542, -20868]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![214, 126, 1, 0, 0], ![194, 191, 0, 1, 0], ![141, 195, 0, 0, 1]] where
  M :=![![![-102383, 46270, -11500, -2542, -20868], ![140460, -63457, 15766, 3484, 28612], ![-192576, 87070, -21649, -4788, -39280], ![61974, -27946, 6924, 1525, 12562], ![-15414, 6944, -1720, -378, -3121]]]
  hmulB := by decide  
  f := ![![![-38317, -13658, 10360, 3802, 15904]], ![![-118236, -42147, 31966, 11724, 49052]], ![![-89210, -31800, 24119, 8848, 37016]], ![![-116044, -41365, 31374, 11509, 48150]], ![![-107493, -38317, 29062, 10660, 44599]]]
  g := ![![![22031, 23004, -11500, -2542, -20868], ![-30204, -31539, 15766, 3484, 28612], ![41474, 43304, -21649, -4788, -39280], ![-13258, -13845, 6924, 1525, 12562], ![3293, 3439, -1720, -378, -3121]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 2 2 8 [8, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [234, 262], [0, 1]]
 g := ![![[168, 33], [149, 124], [54, 137], [111], [122], [64], [52], [1]], ![[0, 230], [235, 139], [26, 126], [111], [122], [64], [52], [1]]]
 h' := ![![[234, 262], [123, 104], [94, 178], [173, 20], [260, 30], [45, 139], [174, 8], [255, 234], [0, 1]], ![[0, 1], [0, 159], [192, 85], [119, 243], [179, 233], [222, 124], [205, 255], [44, 29], [234, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [38, 184]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 2
  hpos := by decide
  P := [8, 29, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1258, 3604, 3128, 2386, 13288]
  a := ![4, -12, -8, -8, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11434, -13070, 3128, 2386, 13288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1477, -72, 640, -196, 370]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-1477, -72, 640, -196, 370]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![138, 47, 1, 0, 0], ![176, 17, 0, 1, 0], ![19, 91, 0, 0, 1]] where
  M :=![![![-1477, -72, 640, -196, 370], ![-1044, -4865, -2424, -636, -9668], ![61824, 26936, -12497, 10672, 33840], ![-133014, 28784, 78712, -14003, 106082], ![-12936, -28784, -11216, -4624, -54823]]]
  hmulB := by decide  
  f := ![![![-100835, -31112, 28608, 10500, 42782]], ![![-319692, -106855, 94888, 34652, 142308]], ![![-114078, -36727, 33143, 12132, 49640]], ![![-94106, -29681, 27024, 9905, 40446]], ![![-115843, -38547, 34296, 12528, 51427]]]
  g := ![![![-237, -230, 640, -196, 370], ![2392, 3801, -2424, -636, -9668], ![-2794, -10063, -12497, 10672, 33840], ![-40100, -49757, 78712, -14003, 106082], ![12891, 21163, -11216, -4624, -54823]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [233, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 262], [0, 1]]
 g := ![![[4, 149], [198, 143], [218, 99], [100], [145], [216], [198], [1]], ![[0, 114], [0, 120], [0, 164], [100], [145], [216], [198], [1]]]
 h' := ![![[120, 262], [154, 82], [228, 77], [156, 25], [7, 253], [172, 113], [2, 189], [30, 120], [0, 1]], ![[0, 1], [0, 181], [0, 186], [0, 238], [122, 10], [56, 150], [64, 74], [228, 143], [120, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [50, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [233, 143, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1328581, 170252, 739480, 17820, 1193052]
  a := ![-53, 134, 111, 72, 336]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-491183, -545460, 739480, 17820, 1193052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1

def I263N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![478355, 172110, -128136, -47038, -197234]] i)))

def SI263N2: IdealEqSpanCertificate' Table ![![478355, 172110, -128136, -47038, -197234]] 
 ![![263, 0, 0, 0, 0], ![90, 1, 0, 0, 0], ![53, 0, 1, 0, 0], ![200, 0, 0, 1, 0], ![153, 0, 0, 0, 1]] where
  M :=![![![478355, 172110, -128136, -47038, -197234], ![1465632, 527661, -392346, -144032, -604040], ![4488432, 1617030, -1200723, -440804, -1848976], ![6136524, 2212750, -1640136, -602143, -2526328], ![-2318226, -835104, 620216, 227690, 955035]]]
  hmulB := by decide  
  f := ![![![-7847, 390, -1484, -606, -5850]], ![![-2538, 157, -534, -188, -1956]], ![![-1973, 268, -43, -150, -718]], ![![-7340, -886, -1188, -759, -6384]], ![![-3927, 410, -1052, -252, -3255]]]
  g := ![![![119255, 172110, -128136, -47038, -197234], ![365000, 527661, -392346, -144032, -604040], ![1116533, 1617030, -1200723, -440804, -1848976], ![1524232, 2212750, -1640136, -602143, -2526328], ![-576763, -835104, 620216, 227690, 955035]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI263N2 : Nat.card (O ⧸ I263N2) = 263 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI263N2)

lemma isPrimeI263N2 : Ideal.IsPrime I263N2 := prime_ideal_of_norm_prime hp263.out _ NI263N2
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-102383, 46270, -11500, -2542, -20868]] ![![-1477, -72, 640, -196, 370]]
  ![![7847, -390, 1484, 606, 5850]] where
 M := ![![![7847, -390, 1484, 606, 5850]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI263N1 : IdealMulLeCertificate' Table 
  ![![7847, -390, 1484, 606, 5850]] ![![478355, 172110, -128136, -47038, -197234]]
  ![![263, 0, 0, 0, 0]] where
 M := ![![![-263, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![442, 50, 78, 45, 393]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![442, 50, 78, 45, 393]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![0, 0, 269, 0, 0], ![219, 7, 132, 1, 0], ![256, 243, 174, 0, 1]] where
  M :=![![![442, 50, 78, 45, 393], ![-2628, -467, 590, -360, -648], ![6048, -4126, -4787, 316, -9792], ![29742, 22502, -462, 6133, 35704], ![-12243, -2972, 3924, -1873, -1766]]]
  hmulB := by decide  
  f := ![![![445634, 146990, -129382, -47335, -194369]], ![![1450224, 478373, -421030, -154036, -632516]], ![![4719312, 1556790, -1370059, -501244, -2058272]], ![![2742186, 904571, -796090, -291254, -1195981]], ![![4777801, 1576051, -1387064, -507465, -2083808]]]
  g := ![![![-409, -356, -276, 45, 393], ![900, 593, 598, -360, -648], ![9084, 8822, 6161, 316, -9792], ![-38861, -32329, -26106, 6133, 35704], ![3160, 1633, 2076, -1873, -1766]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 3 2 8 [160, 193, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 171, 38], [24, 97, 231], [0, 1]]
 g := ![![[134, 227, 62], [170, 260], [106, 218, 131], [145, 215, 121], [214, 248], [128, 208], [104, 1], []], ![[48, 28, 181, 149], [152, 21], [247, 58, 80, 16], [43, 228, 136, 214], [9, 84], [3, 89], [223, 263], [158, 99]], ![[181, 144, 134, 21], [99, 213], [190, 169, 223, 43], [83, 245, 19, 65], [197, 226], [136, 100], [40, 189], [234, 99]]]
 h' := ![![[80, 171, 38], [138, 3, 84], [256, 128, 246], [203, 28, 20], [126, 12, 258], [63, 92, 168], [38, 212, 132], [0, 0, 1], [0, 1]], ![[24, 97, 231], [213, 253, 192], [79, 183, 212], [98, 25, 45], [22, 139, 196], [99, 148, 155], [176, 28, 147], [219, 125, 97], [80, 171, 38]], ![[0, 1], [93, 13, 262], [84, 227, 80], [117, 216, 204], [266, 118, 84], [154, 29, 215], [177, 29, 259], [258, 144, 171], [24, 97, 231]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76, 192], []]
 b := ![[], [154, 20, 179], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 3
  hpos := by decide
  P := [160, 193, 165, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![551009018, 7125825346, 3999244143, 772352206, 14412153463]
  a := ![59, -126, -123, -55, -374]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14342399296, -13012765545, -9686490519, 772352206, 14412153463]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 19465109 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-445634, -146990, 129382, 47335, 194369]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![-445634, -146990, 129382, 47335, 194369]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![27, 5, 1, 0, 0], ![67, 136, 0, 1, 0], ![54, 216, 0, 0, 1]] where
  M :=![![![-445634, -146990, 129382, 47335, 194369], ![-1450224, -478373, 421030, 154036, 632516], ![-4719312, -1556790, 1370059, 501244, 2058272], ![-6953436, -2293898, 2018554, 738501, 3032562], ![2418555, 797820, -702132, -256879, -1054828]]]
  hmulB := by decide  
  f := ![![![-442, -50, -78, -45, -393]], ![![2628, 467, -590, 360, 648]], ![![-18, 19, -1, 1, 9]], ![![1108, 140, -316, 148, 97]], ![![2067, 376, -504, 287, 448]]]
  g := ![![![-65451, -182956, 129382, 47335, 194369], ![-212990, -595375, 421030, 154036, 632516], ![-693089, -1937409, 1370059, 501244, 2058272], ![-1021161, -2854484, 2018554, 738501, 3032562], ![355196, 992888, -702132, -256879, -1054828]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P1 : CertificateIrreducibleZModOfList' 269 2 2 8 [259, 121, 1] where
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
 g := ![![[230, 6], [93], [116, 36], [109, 222], [115], [96], [115], [1]], ![[42, 263], [93], [64, 233], [147, 47], [115], [96], [115], [1]]]
 h' := ![![[148, 268], [185, 116], [84, 239], [14, 6], [22, 130], [32, 148], [174, 74], [10, 148], [0, 1]], ![[0, 1], [137, 153], [217, 30], [95, 263], [163, 139], [147, 121], [97, 195], [125, 121], [148, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [236]]
 b := ![[], [145, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N1 : CertifiedPrimeIdeal' SI269N1 269 where
  n := 2
  hpos := by decide
  P := [259, 121, 1]
  hirr := P269P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1470299, -638918, 301692, -247504, -780330]
  a := ![-42, 82, 88, 24, 266]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![182545, 743734, 301692, -247504, -780330]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N1 B_one_repr
lemma NI269N1 : Nat.card (O ⧸ I269N1) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N1
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![442, 50, 78, 45, 393]] ![![-445634, -146990, 129382, 47335, 194369]]
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

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65648, 30576, -7844, -1783, -14127]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![-65648, 30576, -7844, -1783, -14127]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![230, 228, 1, 0, 0], ![67, 4, 0, 1, 0], ![249, 205, 0, 0, 1]] where
  M :=![![![-65648, 30576, -7844, -1783, -14127], ![95460, -40163, 9180, 1868, 17008], ![-113256, 60892, -17747, -4448, -31064], ![58806, -12204, -832, -961, 176], ![-16419, 2444, 732, 431, 744]]]
  hmulB := by decide  
  f := ![![![-920, -680, 20, -177, -1047]], ![![7344, 987, -2804, 1072, -444]], ![![5384, 328, -2291, 758, -1102]], ![![-632, -416, 44, -120, -625]], ![![4857, 133, -2164, 668, -1327]]]
  g := ![![![19836, 17425, -7844, -1783, -14127], ![-23528, -20765, 9180, 1868, 17008], ![44286, 38720, -17747, -4448, -31064], ![999, 536, -832, -961, 176], ![-1472, -1176, 732, 431, 744]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 2 2 8 [5, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 270], [0, 1]]
 g := ![![[131, 217], [160, 242], [256, 37], [165, 153], [180], [41], [32], [1]], ![[0, 54], [185, 29], [140, 234], [220, 118], [180], [41], [32], [1]]]
 h' := ![![[158, 270], [13, 156], [75, 28], [259, 120], [254, 204], [134, 198], [136, 224], [266, 158], [0, 1]], ![[0, 1], [0, 115], [163, 243], [249, 151], [237, 67], [253, 73], [27, 47], [27, 113], [158, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [239, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 2
  hpos := by decide
  P := [5, 113, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2285419, -18566, 1072936, -101616, 1202592]
  a := ![-65, 150, 140, 80, 416]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1998885, -1810970, 1072936, -101616, 1202592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-563, 721, -303, -92, -496]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![-563, 721, -303, -92, -496]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![267, 53, 1, 0, 0], ![106, 220, 0, 1, 0], ![250, 251, 0, 0, 1]] where
  M :=![![![-563, 721, -303, -92, -496], ![3528, -78, -383, -166, -520], ![4116, 3067, -2070, -722, -3188], ![9966, 2745, -2607, -965, -3894], ![-3402, -988, 916, 338, 1371]]]
  hmulB := by decide  
  f := ![![![487, 167, -135, -40, -188]], ![![1368, 584, -313, -134, -392]], ![![759, 282, -198, -68, -272]], ![![1336, 547, -319, -125, -406]], ![![1708, 694, -411, -160, -529]]]
  g := ![![![790, 596, -303, -92, -496], ![935, 691, -383, -166, -520], ![5278, 3955, -2070, -722, -3188], ![6575, 4910, -2607, -965, -3894], ![-2312, -1727, 916, 338, 1371]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P1 : CertificateIrreducibleZModOfList' 271 2 2 8 [196, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [214, 270], [0, 1]]
 g := ![![[151, 112], [185, 8], [266, 62], [252, 259], [169], [213], [268], [1]], ![[0, 159], [0, 263], [255, 209], [123, 12], [169], [213], [268], [1]]]
 h' := ![![[214, 270], [54, 58], [167, 79], [201, 89], [155, 114], [115, 258], [251, 22], [75, 214], [0, 1]], ![[0, 1], [0, 213], [0, 192], [6, 182], [161, 157], [43, 13], [81, 249], [72, 57], [214, 270]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [250]]
 b := ![[], [175, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N1 : CertifiedPrimeIdeal' SI271N1 271 where
  n := 2
  hpos := by decide
  P := [196, 57, 1]
  hirr := P271P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135004, -54238, 30614, -22004, -61458]
  a := ![-13, 24, 27, 8, 82]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![34642, 68598, 30614, -22004, -61458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N1 B_one_repr
lemma NI271N1 : Nat.card (O ⧸ I271N1) = 73441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N1

def I271N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2348, -2305, -291, -533, -3915]] i)))

def SI271N2: IdealEqSpanCertificate' Table ![![-2348, -2305, -291, -533, -3915]] 
 ![![271, 0, 0, 0, 0], ![261, 1, 0, 0, 0], ![171, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![268, 0, 0, 0, 1]] where
  M :=![![![-2348, -2305, -291, -533, -3915], ![26688, 6092, -8701, 4050, 3236], ![-43716, 57693, 54692, 426, 134484], ![-418074, -263757, 35753, -80539, -396976], ![145713, 25152, -52360, 21171, 628]]]
  hmulB := by decide  
  f := ![![![142836724, -64711543, 16125765, 3573037, 29243445]], ![![136839432, -61997323, 15450146, 3423489, 28017911]], ![![91114296, -41284242, 10289219, 2280099, 18658485]], ![![24441188, -11082860, 2764412, 613048, 5012015]], ![![141339061, -64029628, 15954932, 3535003, 28934038]]]
  g := ![![![6359, -2305, -291, -533, -3915], ![-4181, 6092, -8701, 4050, 3236], ![-223305, 57693, 54692, 426, 134484], ![636471, -263757, 35753, -80539, -396976], ![5060, 25152, -52360, 21171, 628]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N2 : Nat.card (O ⧸ I271N2) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N2)

lemma isPrimeI271N2 : Ideal.IsPrime I271N2 := prime_ideal_of_norm_prime hp271.out _ NI271N2
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![-65648, 30576, -7844, -1783, -14127]] ![![-563, 721, -303, -92, -496]]
  ![![142836724, -64711543, 16125765, 3573037, 29243445]] where
 M := ![![![142836724, -64711543, 16125765, 3573037, 29243445]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI271N1 : IdealMulLeCertificate' Table 
  ![![142836724, -64711543, 16125765, 3573037, 29243445]] ![![-2348, -2305, -291, -533, -3915]]
  ![![271, 0, 0, 0, 0]] where
 M := ![![![271, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3965, 33287, 18053, 3920, 67192]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![3965, 33287, 18053, 3920, 67192]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![111, 251, 109, 130, 1]] where
  M :=![![![3965, 33287, 18053, 3920, 67192], ![-426672, -195790, 80327, -74758, -254192], ![1973700, -301431, -1092886, 220490, -1315652], ![3498822, 4602791, 1132061, 921615, 8263362], ![-2479386, -992004, 553908, -418766, -1174829]]]
  hmulB := by decide  
  f := ![![![42845, -47045, 17931, 5316, 29940]], ![![-211536, 10124, 16747, 7878, 22368]], ![![-181476, -181847, 104660, 36026, 165156]], ![![-497778, -139613, 116859, 43643, 177842]], ![![-478887, -146560, 118228, 43868, 180475]]]
  g := ![![![-26911, -60765, -26375, -31520, 67192], ![100320, 229626, 100315, 119026, -254192], ![534336, 1191073, 513766, 618250, -1315652], ![-3298680, -7471123, -3247561, -3874785, 8263362], ![461829, 1060975, 464297, 549852, -1174829]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [75, 268, 33, 114, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [205, 241, 11, 138], [276, 83, 87, 250], [236, 229, 179, 166], [0, 1]]
 g := ![![[145, 92, 260, 258], [258, 189, 133], [118, 260, 38, 122], [229, 217, 214], [24, 172, 223, 222], [181, 174, 254], [1], []], ![[5, 5, 212, 232, 107, 200], [161, 72, 203], [32, 264, 170, 116, 67, 149], [244, 99, 202], [237, 155, 93, 0, 69, 179], [145, 276, 1], [233, 258, 74], [12, 99, 208]], ![[221, 260, 213, 102, 90, 164], [141, 2, 208], [12, 248, 193, 2, 93, 190], [224, 142, 222], [2, 37, 269, 100, 86, 121], [200, 60, 243], [254, 107, 198], [66, 5, 175]], ![[70, 13, 56, 163, 109, 18], [275, 260, 249], [224, 96, 227, 230, 157, 33], [156, 149, 164], [225, 105, 244, 191, 185, 60], [194, 2, 39], [147, 261, 90], [144, 223, 133]]]
 h' := ![![[205, 241, 11, 138], [236, 207, 139, 33], [14, 35, 264, 166], [207, 212, 151, 26], [139, 22, 269, 141], [83, 248, 133, 172], [202, 9, 244, 163], [0, 0, 1], [0, 1]], ![[276, 83, 87, 250], [153, 84, 206, 92], [58, 190, 225, 155], [167, 221, 97, 16], [49, 33, 96, 220], [214, 236, 215, 14], [274, 6, 82, 276], [129, 83, 119, 118], [205, 241, 11, 138]], ![[236, 229, 179, 166], [232, 7, 142, 195], [275, 1, 169, 139], [137, 262, 241, 158], [219, 143, 169, 172], [228, 181, 64, 254], [47, 122, 139, 62], [37, 53, 44, 72], [276, 83, 87, 250]], ![[0, 1], [122, 256, 67, 234], [183, 51, 173, 94], [99, 136, 65, 77], [89, 79, 20, 21], [79, 166, 142, 114], [262, 140, 89, 53], [22, 141, 113, 87], [236, 229, 179, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [98, 254, 120], []]
 b := ![[], [], [147, 29, 185, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [75, 268, 33, 114, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![462723439793595, 93808036585456, -157908411332012, 69048484358324, 31779868473738]
  a := ![-87, 190, 184, 89, 552]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11064411410799, -28458263358566, -13075502075702, -14665467210208, 31779868473738]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1465, -1830, -416, -376, -3260]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![-1465, -1830, -416, -376, -3260]] 
 ![![277, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![197, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-1465, -1830, -416, -376, -3260], ![21816, 6271, -6342, 3432, 5272], ![-52224, 39002, 47455, -2636, 98784], ![-299352, -220222, 6856, -60953, -349072], ![120804, 28216, -39008, 18332, 15767]]]
  hmulB := by decide  
  f := ![![![5022275, 1634198, -1475748, -539640, -2209412]], ![![1002356, 326163, -294514, -107696, -440936]], ![![1392030, 453042, -408941, -149540, -612280]], ![![3862459, 1257020, -1134736, -414945, -1698948]], ![![353243, 114902, -103844, -37972, -155453]]]
  g := ![![![999, -1830, -416, -376, -3260], ![-2504, 6271, -6342, 3432, 5272], ![-25858, 39002, 47455, -2636, 98784], ![113481, -220222, 6856, -60953, -349072], ![-10027, 28216, -39008, 18332, 15767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![3965, 33287, 18053, 3920, 67192]] ![![-1465, -1830, -416, -376, -3260]]
  ![![277, 0, 0, 0, 0]] where
 M := ![![![6721183123, 1938209165, -1950200495, 1057990420, 1636964740]]]
 hmul := by decide  
 g := ![![![![24264199, 6997145, -7040435, 3819460, 5909620]]]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-378362, -124835, 109821, 40179, 164995]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![-378362, -124835, 109821, 40179, 164995]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![266, 21, 1, 0, 0], ![17, 194, 0, 1, 0], ![182, 19, 0, 0, 1]] where
  M :=![![![-378362, -124835, 109821, 40179, 164995], ![-1231044, -406194, 357313, 130726, 536832], ![-4005348, -1321621, 1162518, 425318, 1746596], ![-5900220, -1946943, 1712441, 626513, 2572838], ![2052705, 677320, -595784, -217973, -895120]]]
  hmulB := by decide  
  f := ![![![950, 165, -357, 139, -23]], ![![-696, 2492, 1833, 166, 5420]], ![![728, 277, -185, 122, 290]], ![![-76, 1718, 1076, 166, 3593]], ![![569, 330, -75, 107, 464]]]
  g := ![![![-214601, -47547, 109821, 40179, 164995], ![-698228, -154699, 357313, 130726, 536832], ![-2271694, -503315, 1162518, 425318, 1746596], ![-3346323, -741408, 1712441, 626513, 2572838], ![1164230, 257946, -595784, -217973, -895120]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [207, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [255, 280], [0, 1]]
 g := ![![[68, 225], [245], [175], [122, 101], [216, 225], [128], [114], [1]], ![[119, 56], [245], [175], [25, 180], [267, 56], [128], [114], [1]]]
 h' := ![![[255, 280], [65, 266], [196, 37], [36, 52], [248, 35], [135, 266], [143, 213], [74, 255], [0, 1]], ![[0, 1], [174, 15], [77, 244], [89, 229], [181, 246], [244, 15], [225, 68], [188, 26], [255, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [100, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [207, 26, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-797190, -149246, 283153, -91412, 33972]
  a := ![-35, 76, 73, 34, 222]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-287348, 39121, 283153, -91412, 33972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7772, 4622, -3312, -1169, -5069]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![7772, 4622, -3312, -1169, -5069]] 
 ![![281, 0, 0, 0, 0], ![135, 1, 0, 0, 0], ![40, 0, 1, 0, 0], ![183, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![7772, 4622, -3312, -1169, -5069], ![37428, 9539, -9406, -3500, -14008], ![105048, 38554, -32461, -11796, -48952], ![163530, 52754, -46796, -17147, -70264], ![-56769, -18436, 16308, 5973, 24492]]]
  hmulB := by decide  
  f := ![![![-4652, -1710, 1124, -841, -2107]], ![![-2172, -843, 498, -399, -1081]], ![![-280, 118, 199, -36, 304]], ![![-5124, -1556, 1436, -864, -1559]], ![![-1473, -802, 200, -296, -1213]]]
  g := ![![![934, 4622, -3312, -1169, -5069], ![4403, 9539, -9406, -3500, -14008], ![12446, 38554, -32461, -11796, -48952], ![19321, 52754, -46796, -17147, -70264], ![-6708, -18436, 16308, 5973, 24492]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N1 : Nat.card (O ⧸ I281N1) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N1)

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := prime_ideal_of_norm_prime hp281.out _ NI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-148, -55, 41, 15, 63]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![-148, -55, 41, 15, 63]] 
 ![![281, 0, 0, 0, 0], ![186, 1, 0, 0, 0], ![248, 0, 1, 0, 0], ![166, 0, 0, 1, 0], ![84, 0, 0, 0, 1]] where
  M :=![![![-148, -55, 41, 15, 63], ![-468, -164, 125, 46, 192], ![-1428, -513, 388, 142, 596], ![-1980, -707, 533, 195, 814], ![741, 264, -200, -73, -306]]]
  hmulB := by decide  
  f := ![![![892, 273, -245, -89, -359]], ![![600, 184, -165, -60, -242]], ![![820, 251, -226, -82, -332]], ![![578, 179, -159, -57, -230]], ![![249, 76, -68, -25, -100]]]
  g := ![![![-28, -55, 41, 15, 63], ![-88, -164, 125, 46, 192], ![-270, -513, 388, 142, 596], ![-368, -707, 533, 195, 814], ![139, 264, -200, -73, -306]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2

def I281N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3989, 1145, -1067, -394, -1596]] i)))

def SI281N3: IdealEqSpanCertificate' Table ![![3989, 1145, -1067, -394, -1596]] 
 ![![281, 0, 0, 0, 0], ![220, 1, 0, 0, 0], ![213, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![3989, 1145, -1067, -394, -1596], ![11940, 4184, -3583, -1306, -5396], ![40212, 12963, -11488, -4210, -17252], ![58416, 19409, -16987, -6213, -25536], ![-20364, -6756, 5916, 2164, 8893]]]
  hmulB := by decide  
  f := ![![![-107, 641, 431, 30, 1292]], ![![-112, 486, 341, 18, 988]], ![![93, 484, 245, 44, 912]], ![![128, 473, 223, 59, 912]], ![![-235, 273, 271, -14, 609]]]
  g := ![![![908, 1145, -1067, -394, -1596], ![2795, 4184, -3583, -1306, -5396], ![9300, 12963, -11488, -4210, -17252], ![13571, 19409, -16987, -6213, -25536], ![-4729, -6756, 5916, 2164, 8893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N3 : Nat.card (O ⧸ I281N3) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N3)

lemma isPrimeI281N3 : Ideal.IsPrime I281N3 := prime_ideal_of_norm_prime hp281.out _ NI281N3
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![-378362, -124835, 109821, 40179, 164995]] ![![7772, 4622, -3312, -1169, -5069]]
  ![![1127393279, 372203751, -327044551, -119655016, -491431650]] where
 M := ![![![1127393279, 372203751, -327044551, -119655016, -491431650]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![1127393279, 372203751, -327044551, -119655016, -491431650]] ![![-148, -55, 41, 15, 63]]
  ![![-1259862902, -416050134, 365513998, 133727819, 549246249]] where
 M := ![![![-1259862902, -416050134, 365513998, 133727819, 549246249]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N2 : IdealMulLeCertificate' Table 
  ![![-1259862902, -416050134, 365513998, 133727819, 549246249]] ![![3989, 1145, -1067, -394, -1596]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![1331810831606, 439676753355, -386337114737, -141348529799, -580526472467]]]
 hmul := by decide  
 g := ![![![![4739540326, 1564685955, -1374865177, -503019679, -2065930507]]]]
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

def I283N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![78164, 28447, -21441, -7855, -32923]] i)))

def SI283N0: IdealEqSpanCertificate' Table ![![78164, 28447, -21441, -7855, -32923]] 
 ![![283, 0, 0, 0, 0], ![0, 283, 0, 0, 0], ![0, 0, 283, 0, 0], ![0, 0, 0, 283, 0], ![199, 204, 41, 38, 1]] where
  M :=![![![78164, 28447, -21441, -7855, -32923], ![244668, 86300, -65813, -24166, -100952], ![750708, 268505, -203692, -74718, -312596], ![1039608, 369883, -281149, -103167, -431378], ![-388173, -138152, 105000, 38529, 161110]]]
  hmulB := by decide  
  f := ![![![-28, -11, 7, 3, 9]], ![![-72, -18, 25, 14, 60]], ![![-444, -105, 150, 14, 172]], ![![-522, -391, 19, 13, -280]], ![![-205, -88, 47, 16, 37]]]
  g := ![![![23427, 23833, 4694, 4393, -32923], ![71852, 73076, 14393, 13470, -100952], ![222464, 226283, 44568, 41710, -312596], ![307010, 312265, 61503, 57559, -431378], ![-114661, -116624, -22970, -21497, 161110]]]
  hle1 := by decide   
  hle2 := by decide  


def P283P0 : CertificateIrreducibleZModOfList' 283 4 2 8 [35, 107, 163, 104, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 39, 202, 118], [114, 25, 226, 255], [218, 218, 138, 193], [0, 1]]
 g := ![![[158, 33, 36, 208], [280, 23, 239, 253], [106, 194, 96], [123, 193, 178, 152], [63, 261, 90, 29], [277, 5, 62], [1], []], ![[42, 235, 139, 212, 190, 119], [183, 95, 236, 170, 88, 242], [165, 177, 23], [256, 263, 183, 249, 38, 189], [102, 262, 95, 206, 16, 194], [253, 271, 218], [95, 98, 216], [92, 143, 57]], ![[172, 174, 198, 241, 180, 115], [181, 154, 221, 230, 250, 188], [49, 81, 201], [263, 163, 211, 132, 210, 202], [266, 261, 104, 232, 43, 186], [88, 139, 1], [105, 136, 175], [198, 47, 218]], ![[186, 33, 137, 0, 153, 45], [193, 176, 234, 148, 107, 20], [240, 55, 216], [104, 114, 80, 122, 279, 58], [129, 123, 270, 171, 273, 14], [169, 55, 143], [220, 231, 127], [86, 155, 176]]]
 h' := ![![[130, 39, 202, 118], [105, 13, 3, 121], [173, 236, 222, 128], [223, 262, 79, 68], [59, 89, 160, 172], [20, 33, 190, 245], [248, 176, 120, 179], [0, 0, 1], [0, 1]], ![[114, 25, 226, 255], [16, 134, 173, 101], [133, 119, 67, 91], [75, 173, 76, 56], [87, 87, 225, 281], [75, 261, 212, 275], [231, 46, 222, 255], [96, 102, 241, 102], [130, 39, 202, 118]], ![[218, 218, 138, 193], [204, 133, 47, 266], [184, 63, 113, 116], [22, 140, 237, 261], [133, 82, 42, 101], [160, 56, 170, 51], [134, 63, 20, 282], [123, 132, 145, 32], [114, 25, 226, 255]], ![[0, 1], [192, 3, 60, 78], [85, 148, 164, 231], [109, 274, 174, 181], [229, 25, 139, 12], [57, 216, 277, 278], [38, 281, 204, 133], [83, 49, 179, 149], [218, 218, 138, 193]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [170, 106, 90], []]
 b := ![[], [], [134, 18, 120, 266], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 4
  hpos := by decide
  P := [35, 107, 163, 104, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1094881565786, -353994645627, -717291708389, 108286763552, -1101046759607]
  a := ![-23, 53, 49, 28, 147]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![778103133313, 792436552347, 156981008606, 148226373246, -1101046759607]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI283N0 : Ideal.IsPrime I283N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI283N0 B_one_repr
lemma NI283N0 : Nat.card (O ⧸ I283N0) = 6414247921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI283N0

def I283N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -11, 7, 3, 9]] i)))

def SI283N1: IdealEqSpanCertificate' Table ![![-28, -11, 7, 3, 9]] 
 ![![283, 0, 0, 0, 0], ![260, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![154, 0, 0, 1, 0], ![266, 0, 0, 0, 1]] where
  M :=![![![-28, -11, 7, 3, 9], ![-72, -18, 25, 14, 60], ![-444, -105, 150, 14, 172], ![-522, -391, 19, 13, -280], ![285, 120, -64, 7, 28]]]
  hmulB := by decide  
  f := ![![![78164, 28447, -21441, -7855, -32923]], ![![72676, 26440, -19931, -7302, -30604]], ![![12872, 4668, -3523, -1291, -5409]], ![![46208, 16787, -12661, -4639, -19440]], ![![72097, 26250, -19782, -7247, -30376]]]
  g := ![![![-1, -11, 7, 3, 9], ![-51, -18, 25, 14, 60], ![-94, -105, 150, 14, 172], ![611, -391, 19, 13, -280], ![-131, 120, -64, 7, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI283N1 : Nat.card (O ⧸ I283N1) = 283 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI283N1)

lemma isPrimeI283N1 : Ideal.IsPrime I283N1 := prime_ideal_of_norm_prime hp283.out _ NI283N1
def MulI283N0 : IdealMulLeCertificate' Table 
  ![![78164, 28447, -21441, -7855, -32923]] ![![-28, -11, 7, 3, 9]]
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


def P293P0 : CertificateIrreducibleZModOfList' 293 5 2 8 [291, 202, 85, 212, 124, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 225, 24, 292, 165], [80, 215, 74, 217, 197], [85, 162, 200, 8, 82], [177, 276, 288, 69, 142], [0, 1]]
 g := ![![[60, 132, 246, 202, 137], [169, 149, 26, 61], [34, 253, 186, 111, 232], [267, 110, 79, 267], [259, 148, 274, 17], [191, 264, 221, 169, 1], [], []], ![[3, 252, 133, 11, 169, 192, 31, 125], [92, 137, 251, 250], [266, 28, 120, 168, 59, 44, 12, 139], [267, 127, 74, 10], [13, 22, 24, 178], [127, 191, 200, 190, 231, 86, 81, 230], [175, 175, 250, 55], [142, 173, 9, 269]], ![[228, 8, 227, 249, 245, 248, 12, 16], [257, 248, 166, 61], [44, 225, 187, 243, 275, 162, 205, 276], [115, 157, 84, 123], [239, 51, 56, 236], [123, 156, 87, 99, 152, 71, 248, 82], [256, 144, 232, 262], [89, 25, 151, 133]], ![[92, 29, 258, 4, 177, 115, 191, 238], [159, 4, 245, 25], [254, 76, 108, 178, 161, 183, 176, 222], [224, 232, 270, 25], [220, 5, 32, 102], [86, 71, 105, 110, 108, 241, 119, 272], [62, 27, 274, 137], [107, 176, 242, 278]], ![[97, 121, 280, 62, 285, 175, 287, 47], [193, 252, 155, 220], [119, 152, 28, 99, 204, 168, 210, 263], [282, 283, 214, 202], [111, 96, 91, 60], [245, 142, 44, 117, 92, 281, 129, 264], [123, 258, 13, 67], [22, 70, 91, 240]]]
 h' := ![![[120, 225, 24, 292, 165], [274, 40, 35, 165, 132], [68, 94, 292, 259, 190], [89, 135, 127, 102, 143], [235, 94, 154, 214, 248], [89, 36, 27, 2, 156], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[80, 215, 74, 217, 197], [93, 64, 246, 190, 154], [219, 252, 92, 89, 141], [206, 142, 105, 77, 48], [59, 34, 191, 42, 204], [97, 89, 280, 38, 44], [41, 68, 188, 244, 152], [34, 171, 11, 217, 73], [120, 225, 24, 292, 165]], ![[85, 162, 200, 8, 82], [30, 176, 165, 283, 87], [187, 268, 3, 157, 103], [33, 79, 126, 7, 20], [168, 160, 205, 136, 65], [154, 58, 26, 76, 270], [63, 46, 195, 187, 15], [132, 64, 44, 75, 140], [80, 215, 74, 217, 197]], ![[177, 276, 288, 69, 142], [264, 47, 277, 96, 72], [101, 33, 34, 188, 5], [3, 82, 198, 120, 156], [235, 275, 160, 249, 288], [79, 244, 23, 1, 187], [228, 208, 41, 142, 150], [114, 125, 259, 112, 132], [85, 162, 200, 8, 82]], ![[0, 1], [225, 259, 156, 145, 141], [194, 232, 165, 186, 147], [190, 148, 30, 280, 219], [70, 23, 169, 238, 74], [58, 159, 230, 176, 222], [144, 264, 162, 13, 268], [22, 226, 271, 182, 241], [177, 276, 288, 69, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 81, 212, 57], [], [], []]
 b := ![[], [29, 98, 81, 279, 282], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 5
  hpos := by decide
  P := [291, 202, 85, 212, 124, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39080417616347768502, -42116523428980179760, -7092408626580391056, -9347662419021465579, -73166010487701487451]
  a := ![157, -346, -331, -173, -992]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-133380264902210814, -143742400781502320, -24206172786963792, -31903284706557903, -249713346374407807]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-943, -336, 256, 94, 394]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-943, -336, 256, 94, 394]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![65, 17, 1, 0, 0], ![215, 42, 0, 1, 0], ![229, 56, 0, 0, 1]] where
  M :=![![![-943, -336, 256, 94, 394], ![-2928, -1041, 792, 288, 1208], ![-8976, -3224, 2415, 896, 3696], ![-12312, -4328, 3368, 1263, 5332], ![4590, 1640, -1240, -470, -1939]]]
  hmulB := by decide  
  f := ![![![-9145, -3088, 2688, 982, 4042]], ![![-30144, -9859, 8696, 3184, 13064]], ![![-3923, -1305, 1143, 418, 1718]], ![![-10997, -3666, 3208, 1173, 4822]], ![![-12157, -4048, 3544, 1296, 5327]]]
  g := ![![![-417, -100, 256, 94, 394], ![-1280, -307, 792, 288, 1208], ![-3925, -941, 2415, 896, 3696], ![-5615, -1346, 3368, 1263, 5332], ![2053, 492, -1240, -470, -1939]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [233, 225, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 306], [0, 1]]
 g := ![![[26, 112], [174, 41], [276], [149], [188, 97], [75, 107], [277], [1]], ![[0, 195], [159, 266], [276], [149], [160, 210], [253, 200], [277], [1]]]
 h' := ![![[82, 306], [289, 135], [5, 111], [173, 131], [97, 145], [24, 158], [186, 159], [74, 82], [0, 1]], ![[0, 1], [0, 172], [204, 196], [170, 176], [14, 162], [86, 149], [23, 148], [44, 225], [82, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [305, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 2
  hpos := by decide
  P := [233, 225, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1985775, -274238, 762606, -200152, 337218]
  a := ![58, -126, -122, -62, -367]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-279301, -77252, 762606, -200152, 337218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-403, -217, 59, -74, -302]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-403, -217, 59, -74, -302]] 
 ![![307, 0, 0, 0, 0], ![163, 1, 0, 0, 0], ![140, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![65, 0, 0, 0, 1]] where
  M :=![![![-403, -217, 59, -74, -302], ![2256, -98, -1105, 278, -1000], ![4332, 8765, 3238, 1458, 16564], ![-55194, -19817, 13683, -9091, -21490], ![11340, -1580, -6188, 1284, -7241]]]
  hmulB := by decide  
  f := ![![![-838345, -334163, 200199, 73882, 319806]], ![![-452809, -180539, 108094, 39892, 172694]], ![![-403664, -161219, 96156, 35490, 153732]], ![![-82569, -33646, 19166, 7083, 30912]], ![![-166319, -66141, 39833, 14698, 63569]]]
  g := ![![![156, -217, 59, -74, -302], ![756, -98, -1105, 278, -1000], ![-9723, 8765, 3238, 1458, 16564], ![9274, -19817, 13683, -9091, -21490], ![5143, -1580, -6188, 1284, -7241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N1 : Nat.card (O ⧸ I307N1) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N1)

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := prime_ideal_of_norm_prime hp307.out _ NI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1372751, 488836, -371526, -136324, -570054]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![1372751, 488836, -371526, -136324, -570054]] 
 ![![307, 0, 0, 0, 0], ![192, 1, 0, 0, 0], ![283, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![216, 0, 0, 0, 1]] where
  M :=![![![1372751, 488836, -371526, -136324, -570054], ![4238268, 1509229, -1147052, -420888, -1759988], ![13085256, 4659624, -3541427, -1299456, -5433816], ![18080682, 6438468, -4893398, -1795535, -7508222], ![-6751200, -2404080, 1827160, 670440, 2803517]]]
  hmulB := by decide  
  f := ![![![1349, 2812, 1038, 452, 5262]], ![![732, 1717, 676, 264, 3244]], ![![1637, 2452, 691, 452, 4422]], ![![1495, 1712, 328, 365, 2992]], ![![312, 1776, 904, 216, 3509]]]
  g := ![![![468511, 488836, -371526, -136324, -570054], ![1446488, 1509229, -1147052, -420888, -1759988], ![4465907, 4659624, -3541427, -1299456, -5433816], ![6170811, 6438468, -4893398, -1795535, -7508222], ![-2304136, -2404080, 1827160, 670440, 2803517]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2

def I307N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -7, 3, 1, 5]] i)))

def SI307N3: IdealEqSpanCertificate' Table ![![-4, -7, 3, 1, 5]] 
 ![![307, 0, 0, 0, 0], ![242, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![256, 0, 0, 1, 0], ![243, 0, 0, 0, 1]] where
  M :=![![![-4, -7, 3, 1, 5], ![-36, -8, 5, 2, 8], ![-60, -37, 16, 6, 28], ![-84, -35, 15, 5, 26], ![39, 16, -8, -3, -14]]]
  hmulB := by decide  
  f := ![![![20, -5, -1, -5, -7]], ![![16, -4, -1, -4, -6]], ![![8, 0, -1, -1, -1]], ![![14, -3, 1, -5, -4]], ![![15, -5, -1, -4, -7]]]
  g := ![![![0, -7, 3, 1, 5], ![-3, -8, 5, 2, 8], ![-2, -37, 16, 6, 28], ![-1, -35, 15, 5, 26], ![3, 16, -8, -3, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N3 : Nat.card (O ⧸ I307N3) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N3)

lemma isPrimeI307N3 : Ideal.IsPrime I307N3 := prime_ideal_of_norm_prime hp307.out _ NI307N3
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-943, -336, 256, 94, 394]] ![![-403, -217, 59, -74, -302]]
  ![![10729, -3919, -7299, 964, -11844]] where
 M := ![![![10729, -3919, -7299, 964, -11844]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![10729, -3919, -7299, 964, -11844]] ![![1372751, 488836, -371526, -136324, -570054]]
  ![![179891, 64089, -48705, -17880, -74766]] where
 M := ![![![179891, 64089, -48705, -17880, -74766]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N2 : IdealMulLeCertificate' Table 
  ![![179891, 64089, -48705, -17880, -74766]] ![![-4, -7, 3, 1, 5]]
  ![![307, 0, 0, 0, 0]] where
 M := ![![![-1518422, -540320, 410766, 150737, 630271]]]
 hmul := by decide  
 g := ![![![![-4946, -1760, 1338, 491, 2053]]]]
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


lemma PB1705I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB1705I6 : PrimesBelowBoundCertificateInterval O 251 307 1705 where
  m := 9
  g := ![3, 3, 2, 3, 2, 4, 2, 1, 4]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB1705I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0, I257N1, I257N2]
    · exact ![I263N0, I263N1, I263N2]
    · exact ![I269N0, I269N1]
    · exact ![I271N0, I271N1, I271N2]
    · exact ![I277N0, I277N1]
    · exact ![I281N0, I281N1, I281N2, I281N3]
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
    · exact ![66049, 66049, 257]
    · exact ![69169, 69169, 263]
    · exact ![19465109, 72361]
    · exact ![73441, 73441, 271]
    · exact ![5887339441, 277]
    · exact ![78961, 281, 281, 281]
    · exact ![6414247921, 283]
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
      exact NI257N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI307N0
      exact NI307N1
      exact NI307N2
      exact NI307N3
  β := ![I257N2, I263N2, I271N2, I277N1, I281N1, I281N2, I281N3, I283N1, I307N1, I307N2, I307N3]
  Il := ![[I257N2], [I263N2], [], [I271N2], [I277N1], [I281N1, I281N2, I281N3], [I283N1], [], [I307N1, I307N2, I307N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
