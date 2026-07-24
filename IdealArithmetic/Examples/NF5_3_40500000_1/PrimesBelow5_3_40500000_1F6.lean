
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
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


def P257P0 : CertificateIrreducibleZModOfList' 257 5 2 8 [34, 248, 67, 185, 124, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [215, 6, 88, 0, 192], [47, 89, 16, 238, 108], [152, 242, 255, 216, 33], [233, 176, 155, 60, 181], [0, 1]]
 g := ![![[228, 85, 57, 138, 228], [24, 99, 252, 239], [34, 131, 142, 81], [5, 89, 225, 240], [212, 9, 26, 185], [126, 28, 133, 1], [], []], ![[207, 181, 4, 76, 97, 4, 135, 27], [1, 184, 131, 49], [77, 62, 167, 225], [95, 1, 28, 168], [199, 69, 90, 255], [54, 232, 240, 240], [31, 57, 246, 196], [14, 205, 123, 113]], ![[171, 9, 255, 196, 203, 216, 241, 224], [112, 10, 256, 122], [159, 194, 174, 169], [200, 236, 220, 231], [227, 172, 159, 146], [252, 150, 229, 248], [87, 240, 73, 227], [46, 200, 68, 99]], ![[164, 210, 137, 36, 125, 231, 75, 138], [39, 246, 0, 58], [140, 196, 221, 25], [148, 237, 64, 120], [82, 142, 142, 244], [205, 202, 89, 211], [142, 94, 222, 95], [128, 75, 10, 61]], ![[127, 158, 247, 67, 93, 44, 128, 181], [194, 68, 17, 100], [27, 77, 221, 222], [80, 144, 144, 117], [43, 225, 147, 199], [249, 255, 79, 223], [54, 227, 168, 223], [252, 241, 167, 122]]]
 h' := ![![[215, 6, 88, 0, 192], [79, 64, 14, 119, 182], [155, 17, 170, 169, 204], [119, 146, 30, 109, 9], [17, 160, 200, 61, 92], [85, 182, 138, 135, 106], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[47, 89, 16, 238, 108], [110, 226, 242, 233, 161], [245, 255, 117, 168, 7], [251, 75, 95, 156, 15], [198, 137, 227, 73, 164], [252, 85, 202, 116, 68], [240, 256, 19, 96, 92], [3, 105, 163, 243, 243], [215, 6, 88, 0, 192]], ![[152, 242, 255, 216, 33], [170, 106, 40, 109, 161], [61, 126, 95, 250, 76], [228, 55, 145, 101, 13], [203, 206, 68, 122, 152], [168, 28, 190, 36, 143], [68, 210, 253, 119, 209], [131, 181, 177, 42, 235], [47, 89, 16, 238, 108]], ![[233, 176, 155, 60, 181], [199, 219, 65, 216, 11], [165, 67, 54, 90, 217], [175, 197, 61, 255, 5], [18, 228, 205, 180, 190], [218, 228, 24, 94, 66], [136, 213, 132, 250, 89], [248, 210, 114, 83, 159], [152, 242, 255, 216, 33]], ![[0, 1], [22, 156, 153, 94, 256], [128, 49, 78, 94, 10], [180, 41, 183, 150, 215], [178, 40, 71, 78, 173], [94, 248, 217, 133, 131], [74, 92, 110, 49, 123], [232, 18, 59, 146, 134], [233, 176, 155, 60, 181]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 220, 80, 189], [], [], []]
 b := ![[], [135, 191, 15, 172, 252], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI257N0 : CertifiedPrimeIdeal' SI257N0 257 where
  n := 5
  hpos := by decide
  P := [34, 248, 67, 185, 124, 1]
  hirr := P257P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![269944736746047, 59797247525702, 86515261235325, 15030873765466, -272314914262560]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1050368625471, 232674114886, 336635257725, 58485890138, -1059591106080]
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

def I263N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1057, -176, -340, -58, 1140]] i)))

def SI263N0: IdealEqSpanCertificate' Table ![![-1057, -176, -340, -58, 1140]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![0, 0, 263, 0, 0], ![123, 57, 110, 1, 0], ![84, 185, 236, 0, 1]] where
  M :=![![![-1057, -176, -340, -58, 1140], ![-4888, -895, -1586, -274, 5196], ![-22144, -4292, -7177, -1254, 23220], ![-46828, -9500, -15168, -2651, 48576], ![-17224, -3460, -5584, -978, 17915]]]
  hmulB := by decide  
  f := ![![![1249, 104, -452, -174, 948]], ![![-2304, -169, 818, 314, -1716]], ![![4184, 252, -1447, -562, 3060]], ![![1825, 117, -636, -247, 1344]], ![![2540, 141, -870, -340, 1847]]]
  g := ![![![-341, -790, -1000, -58, 1140], ![-1550, -3599, -4554, -274, 5196], ![-6914, -16078, -20339, -1254, 23220], ![-14453, -33631, -42538, -2651, 48576], ![-5330, -12403, -15688, -978, 17915]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P0 : CertificateIrreducibleZModOfList' 263 3 2 8 [138, 140, 261, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 25, 187], [172, 237, 76], [0, 1]]
 g := ![![[188, 243, 207], [246, 156, 122], [83, 170, 256], [112, 248], [144, 61], [252, 86], [2, 1], []], ![[39, 144, 244, 111], [85, 186, 209, 235], [251, 171, 152, 96], [178, 205], [76, 166], [217, 162], [256, 150], [125, 253]], ![[27, 112, 232, 101], [242, 106, 231, 202], [166, 57, 114, 209], [198, 172], [251, 117], [203, 216], [95, 99], [236, 253]]]
 h' := ![![[93, 25, 187], [242, 36, 162], [118, 187, 139], [5, 203, 16], [162, 248, 118], [109, 14, 245], [250, 108, 127], [0, 0, 1], [0, 1]], ![[172, 237, 76], [183, 66, 153], [210, 180, 58], [144, 132, 199], [81, 89, 176], [7, 92, 193], [212, 137, 62], [78, 102, 237], [93, 25, 187]], ![[0, 1], [108, 161, 211], [171, 159, 66], [64, 191, 48], [257, 189, 232], [210, 157, 88], [168, 18, 74], [172, 161, 25], [172, 237, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 236], []]
 b := ![[], [107, 133, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N0 : CertifiedPrimeIdeal' SI263N0 263 where
  n := 3
  hpos := by decide
  P := [138, 140, 261, 1]
  hirr := P263P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50540628382, 10447219840, 15778235578, 2817860502, -50936008932]
  a := ![379, -328, 378, 160, -1299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![15142846148, 35258520242, 44588257370, 2817860502, -50936008932]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N0 : Ideal.IsPrime I263N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N0 B_one_repr
lemma NI263N0 : Nat.card (O ⧸ I263N0) = 18191447 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N0

def I263N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1249, -104, 452, 174, -948]] i)))

def SI263N1: IdealEqSpanCertificate' Table ![![-1249, -104, 452, 174, -948]] 
 ![![263, 0, 0, 0, 0], ![0, 263, 0, 0, 0], ![138, 43, 1, 0, 0], ![189, 197, 0, 1, 0], ![167, 226, 0, 0, 1]] where
  M :=![![![-1249, -104, 452, 174, -948], ![2304, 169, -818, -314, 1716], ![-4184, -252, 1447, 562, -3060], ![2564, 108, -872, -363, 1920], ![-1920, -140, 680, 262, -1429]]]
  hmulB := by decide  
  f := ![![![1057, 176, 340, 58, -1140]], ![![4888, 895, 1586, 274, -5196]], ![![1438, 255, 465, 80, -1536]], ![![4599, 833, 1490, 257, -4896]], ![![4937, 894, 1600, 276, -5257]]]
  g := ![![![235, 610, 452, 174, -948], ![-426, -1105, -818, -314, 1716], ![764, 1971, 1447, 562, -3060], ![-491, -1235, -872, -363, 1920], ![355, 920, 680, 262, -1429]]]
  hle1 := by decide   
  hle2 := by decide  


def P263P1 : CertificateIrreducibleZModOfList' 263 2 2 8 [46, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [150, 262], [0, 1]]
 g := ![![[214, 223], [84, 31], [153, 22], [179], [83], [181], [145], [1]], ![[0, 40], [0, 232], [34, 241], [179], [83], [181], [145], [1]]]
 h' := ![![[150, 262], [81, 152], [63, 89], [56, 40], [20, 53], [141, 95], [180, 60], [217, 150], [0, 1]], ![[0, 1], [0, 111], [0, 174], [7, 223], [80, 210], [189, 168], [238, 203], [99, 113], [150, 262]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [158, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI263N1 : CertifiedPrimeIdeal' SI263N1 263 where
  n := 2
  hpos := by decide
  P := [46, 113, 1]
  hirr := P263P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54801, -15987, -16499, -578, 51287]
  a := ![40, -33, 41, 18, -137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23702, -41002, -16499, -578, 51287]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI263N1 : Ideal.IsPrime I263N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI263N1 B_one_repr
lemma NI263N1 : Nat.card (O ⧸ I263N1) = 69169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI263N1
def MulI263N0 : IdealMulLeCertificate' Table 
  ![![-1057, -176, -340, -58, 1140]] ![![-1249, -104, 452, 174, -948]]
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

def I269N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 9, 1, -2, 0]] i)))

def SI269N0: IdealEqSpanCertificate' Table ![![9, 9, 1, -2, 0]] 
 ![![269, 0, 0, 0, 0], ![0, 269, 0, 0, 0], ![56, 52, 1, 0, 0], ![158, 156, 0, 1, 0], ![60, 249, 0, 0, 1]] where
  M :=![![![9, 9, 1, -2, 0], ![28, -12, 39, 16, -96], ![256, 147, -60, -34, 96], ![-16, -35, 213, 51, -432], ![104, 53, 5, -6, -23]]]
  hmulB := by decide  
  f := ![![![777, 73, -275, -108, 576]], ![![-1368, -110, 541, 206, -1152]], ![![-92, -5, 44, 16, -96]], ![![-342, -21, 155, 57, -336]], ![![-1088, -85, 438, 166, -935]]]
  g := ![![![1, 1, 1, -2, 0], ![4, 72, 39, 16, -96], ![12, -57, -60, -34, 96], ![22, 329, 213, 51, -432], ![8, 24, 5, -6, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P269P0 : CertificateIrreducibleZModOfList' 269 2 2 8 [220, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 268], [0, 1]]
 g := ![![[239, 258], [43], [77, 244], [96, 5], [255], [224], [23], [1]], ![[0, 11], [43], [243, 25], [9, 264], [255], [224], [23], [1]]]
 h' := ![![[144, 268], [4, 127], [7, 124], [131, 128], [100, 126], [101, 229], [31, 208], [49, 144], [0, 1]], ![[0, 1], [0, 142], [109, 145], [2, 141], [221, 143], [259, 40], [124, 61], [72, 125], [144, 268]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [137, 226]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI269N0 : CertifiedPrimeIdeal' SI269N0 269 where
  n := 2
  hpos := by decide
  P := [220, 125, 1]
  hirr := P269P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2041503, -375502, -806020, -114326, 2500769]
  a := ![-240, 198, -243, -111, 823]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-330435, -2094123, -806020, -114326, 2500769]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI269N0 : Ideal.IsPrime I269N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI269N0 B_one_repr
lemma NI269N0 : Nat.card (O ⧸ I269N0) = 72361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI269N0

def I269N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63, 13, 15, 2, -50]] i)))

def SI269N1: IdealEqSpanCertificate' Table ![![63, 13, 15, 2, -50]] 
 ![![269, 0, 0, 0, 0], ![69, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![130, 0, 0, 1, 0], ![256, 0, 0, 0, 1]] where
  M :=![![![63, 13, 15, 2, -50], ![222, 50, 83, 16, -254], ![1046, 227, 318, 54, -1010], ![2036, 449, 677, 121, -2112], ![776, 169, 243, 42, -767]]]
  hmulB := by decide  
  f := ![![![939, 397, 187, 20, -494]], ![![249, 105, 52, 6, -136]], ![![317, 132, 65, 8, -172]], ![![494, 211, 103, 11, -268]], ![![912, 385, 183, 20, -483]]]
  g := ![![![39, 13, 15, 2, -50], ![197, 50, 83, 16, -254], ![785, 227, 318, 54, -1010], ![1640, 449, 677, 121, -2112], ![596, 169, 243, 42, -767]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N1 : Nat.card (O ⧸ I269N1) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N1)

lemma isPrimeI269N1 : Ideal.IsPrime I269N1 := prime_ideal_of_norm_prime hp269.out _ NI269N1

def I269N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-618, -57, 229, 90, -485]] i)))

def SI269N2: IdealEqSpanCertificate' Table ![![-618, -57, 229, 90, -485]] 
 ![![269, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![222, 0, 1, 0, 0], ![121, 0, 0, 1, 0], ![188, 0, 0, 0, 1]] where
  M :=![![![-618, -57, 229, 90, -485], ![1165, 116, -437, -172, 925], ![-2217, -239, 846, 330, -1781], ![1560, 181, -595, -223, 1224], ![-975, -97, 367, 144, -776]]]
  hmulB := by decide  
  f := ![![![21988, 4883, 7151, 1270, -22331]], ![![14163, 3145, 4606, 818, -14384]], ![![19637, 4359, 6386, 1134, -19945]], ![![12904, 2860, 4196, 745, -13111]], ![![16485, 3659, 5361, 952, -16744]]]
  g := ![![![143, -57, 229, 90, -485], ![-277, 116, -437, -172, 925], ![540, -239, 846, 330, -1781], ![-372, 181, -595, -223, 1224], ![232, -97, 367, 144, -776]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N2 : Nat.card (O ⧸ I269N2) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N2)

lemma isPrimeI269N2 : Ideal.IsPrime I269N2 := prime_ideal_of_norm_prime hp269.out _ NI269N2

def I269N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8, -2, 2, 2, -9]] i)))

def SI269N3: IdealEqSpanCertificate' Table ![![8, -2, 2, 2, -9]] 
 ![![269, 0, 0, 0, 0], ![248, 1, 0, 0, 0], ![97, 0, 1, 0, 0], ![222, 0, 0, 1, 0], ![254, 0, 0, 0, 1]] where
  M :=![![![8, -2, 2, 2, -9], ![17, 23, -14, -10, 33], ![-25, -74, 107, 42, -249], ![320, 136, -96, -35, 120], ![35, -10, 32, 12, -88]]]
  hmulB := by decide  
  f := ![![![12994, 1106, -4856, -1884, 10257]], ![![11887, 1011, -4444, -1724, 9387]], ![![4851, 412, -1815, -704, 3834]], ![![10604, 900, -3968, -1539, 8382]], ![![12343, 1050, -4614, -1790, 9746]]]
  g := ![![![8, -2, 2, 2, -9], ![-39, 23, -14, -10, 33], ![230, -74, 107, 42, -249], ![-174, 136, -96, -35, 120], ![71, -10, 32, 12, -88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI269N3 : Nat.card (O ⧸ I269N3) = 269 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI269N3)

lemma isPrimeI269N3 : Ideal.IsPrime I269N3 := prime_ideal_of_norm_prime hp269.out _ NI269N3
def MulI269N0 : IdealMulLeCertificate' Table 
  ![![9, 9, 1, -2, 0]] ![![63, 13, 15, 2, -50]]
  ![![-461, -104, -154, -26, 478]] where
 M := ![![![-461, -104, -154, -26, 478]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N1 : IdealMulLeCertificate' Table 
  ![![-461, -104, -154, -26, 478]] ![![-618, -57, 229, 90, -485]]
  ![![-1454, -53, 491, 208, -1093]] where
 M := ![![![-1454, -53, 491, 208, -1093]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI269N2 : IdealMulLeCertificate' Table 
  ![![-1454, -53, 491, 208, -1093]] ![![8, -2, 2, 2, -9]]
  ![![269, 0, 0, 0, 0]] where
 M := ![![![3497, 4573, -4573, -2152, 10222]]]
 hmul := by decide  
 g := ![![![![13, 17, -17, -8, 38]]]]
 hle2 := by decide  


def PBC269 : ContainsPrimesAboveP 269 ![I269N0, I269N1, I269N2, I269N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI269N0
    exact isPrimeI269N1
    exact isPrimeI269N2
    exact isPrimeI269N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 269 (by decide) (𝕀 ⊙ MulI269N0 ⊙ MulI269N1 ⊙ MulI269N2)
instance hp271 : Fact (Nat.Prime 271) := {out := by norm_num}

def I271N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115582, -25291, -37529, -6646, 117721]] i)))

def SI271N0: IdealEqSpanCertificate' Table ![![-115582, -25291, -37529, -6646, 117721]] 
 ![![271, 0, 0, 0, 0], ![0, 271, 0, 0, 0], ![0, 0, 271, 0, 0], ![0, 0, 0, 271, 0], ![252, 179, 171, 24, 1]] where
  M :=![![![-115582, -25291, -37529, -6646, 117721], ![-495561, -108496, -161043, -28536, 505039], ![-2125691, -465461, -690534, -122334, 2165545], ![-4309744, -943929, -1400249, -248097, 4390872], ![-1597949, -349963, -519123, -91972, 1627904]]]
  hmulB := by decide  
  f := ![![![-92, -61, 71, 26, -139]], ![![331, 126, -173, -40, 275]], ![![-815, -7, 176, -66, 5]], ![![284, -743, 573, 427, -1704]], ![![-357, -44, 114, -6, -96]]]
  g := ![![![-109894, -77850, -74420, -10450, 117721], ![-471459, -333987, -319272, -44832, 505039], ![-2021561, -1432096, -1368999, -192234, 2165545], ![-4098928, -2903727, -2775791, -389775, 4390872], ![-1519667, -1076549, -1029117, -144508, 1627904]]]
  hle1 := by decide   
  hle2 := by decide  


def P271P0 : CertificateIrreducibleZModOfList' 271 4 2 8 [76, 89, 72, 260, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 153, 159, 107], [26, 262, 270, 258], [97, 126, 113, 177], [0, 1]]
 g := ![![[30, 127, 244, 88], [246, 181, 168, 200], [203, 1, 116, 41], [76, 142, 238, 252], [127, 154, 121], [132, 18, 121], [1], []], ![[88, 168, 172, 232, 12, 165], [16, 165, 21, 18, 183, 95], [247, 260, 196, 196, 54, 236], [1, 219, 102, 76, 231, 84], [229, 227, 248], [267, 35, 81], [172, 262, 25], [95, 75, 67]], ![[229, 213, 210, 220, 66, 18], [24, 89, 50, 170, 155, 160], [27, 182, 206, 34, 99, 136], [73, 199, 95, 41, 238, 242], [36, 255, 167], [32, 151, 162], [263, 159, 158], [130, 259, 169]], ![[8, 245, 101, 195, 72, 198], [79, 267, 178, 260, 204, 114], [189, 198, 260, 24, 240, 212], [167, 13, 51, 160, 64, 28], [225, 270, 34], [190, 144, 148], [152, 73, 7], [16, 72, 164]]]
 h' := ![![[159, 153, 159, 107], [3, 212, 40, 140], [19, 193, 53, 124], [186, 59, 116, 224], [0, 95, 189, 184], [80, 141, 189, 260], [195, 182, 199, 11], [0, 0, 1], [0, 1]], ![[26, 262, 270, 258], [158, 52, 11, 151], [137, 266, 133, 30], [158, 67, 59, 5], [54, 32, 214, 32], [83, 222, 181, 178], [209, 255, 103, 9], [175, 82, 80, 5], [159, 153, 159, 107]], ![[97, 126, 113, 177], [86, 16, 124, 95], [48, 21, 177, 156], [166, 33, 31, 61], [253, 177, 116, 258], [192, 235, 129, 80], [166, 252, 194, 220], [10, 256, 31, 145], [26, 262, 270, 258]], ![[0, 1], [151, 262, 96, 156], [146, 62, 179, 232], [259, 112, 65, 252], [238, 238, 23, 68], [219, 215, 43, 24], [5, 124, 46, 31], [63, 204, 159, 121], [97, 126, 113, 177]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [198, 150, 55], []]
 b := ![[], [], [203, 25, 202, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI271N0 : CertifiedPrimeIdeal' SI271N0 271 where
  n := 4
  hpos := by decide
  P := [76, 89, 72, 260, 1]
  hirr := P271P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1064470791437, -187659519615, -426615579897, -90384737872, 1275983023037]
  a := ![135, -105, 140, 70, -463]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1190450895191, -843500445178, -806714806344, -113335709560, 1275983023037]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI271N0 : Ideal.IsPrime I271N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI271N0 B_one_repr
lemma NI271N0 : Nat.card (O ⧸ I271N0) = 5393580481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI271N0

def I271N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![92, 61, -71, -26, 139]] i)))

def SI271N1: IdealEqSpanCertificate' Table ![![92, 61, -71, -26, 139]] 
 ![![271, 0, 0, 0, 0], ![196, 1, 0, 0, 0], ![66, 0, 1, 0, 0], ![209, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![92, 61, -71, -26, 139], ![-331, -126, 173, 40, -275], ![815, 7, -176, 66, -5], ![-284, 743, -573, -427, 1704], ![263, 77, -121, -20, 172]]]
  hmulB := by decide  
  f := ![![![115582, 25291, 37529, 6646, -117721]], ![![85423, 18692, 27737, 4912, -87005]], ![![35993, 7877, 11688, 2070, -36661]], ![![105042, 22988, 34110, 6041, -106991]], ![![8029, 1758, 2608, 462, -8179]]]
  g := ![![![-9, 61, -71, -26, 139], ![22, -126, 173, 40, -275], ![-10, 7, -176, 66, -5], ![-101, 743, -573, -427, 1704], ![-13, 77, -121, -20, 172]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI271N1 : Nat.card (O ⧸ I271N1) = 271 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI271N1)

lemma isPrimeI271N1 : Ideal.IsPrime I271N1 := prime_ideal_of_norm_prime hp271.out _ NI271N1
def MulI271N0 : IdealMulLeCertificate' Table 
  ![![-115582, -25291, -37529, -6646, 117721]] ![![92, 61, -71, -26, 139]]
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

def I277N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-42791, -9383, -13891, -2460, 43564]] i)))

def SI277N0: IdealEqSpanCertificate' Table ![![-42791, -9383, -13891, -2460, 43564]] 
 ![![277, 0, 0, 0, 0], ![0, 277, 0, 0, 0], ![0, 0, 277, 0, 0], ![0, 0, 0, 277, 0], ![13, 259, 29, 78, 1]] where
  M :=![![![-42791, -9383, -13891, -2460, 43564], ![-183380, -40178, -59611, -10562, 186868], ![-786472, -172305, -255484, -45288, 801100], ![-1594044, -349423, -517787, -91695, 1623504], ![-591064, -129519, -192011, -34024, 602053]]]
  hmulB := by decide  
  f := ![![![33, -7, -31, -10, 68]], ![![-200, -40, 7, 8, -4]], ![![-92, -109, -152, -42, 356]], ![![-496, -155, -99, -9, 240]], ![![-335, -93, -39, 0, 105]]]
  g := ![![![-2199, -40767, -4611, -12276, 43564], ![-9432, -174870, -19779, -52658, 186868], ![-40436, -749665, -84792, -225744, 801100], ![-81948, -1519267, -171839, -457491, 1623504], ![-30389, -563398, -63724, -169654, 602053]]]
  hle1 := by decide   
  hle2 := by decide  


def P277P0 : CertificateIrreducibleZModOfList' 277 4 2 8 [28, 225, 210, 119, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [225, 77, 246, 185], [262, 206, 162, 5], [225, 270, 146, 87], [0, 1]]
 g := ![![[81, 90, 224, 55], [253, 26, 186], [44, 42, 245, 267], [7, 114, 264], [227, 255, 8, 66], [103, 229, 34], [1], []], ![[133, 59, 22, 245, 268, 230], [186, 73, 7], [210, 168, 113, 188, 46, 165], [42, 250, 10], [256, 266, 166, 91, 30, 22], [220, 125, 117], [214, 184, 122], [5, 120, 154]], ![[43, 222, 53, 186, 122, 118], [199, 258, 144], [33, 36, 182, 250, 245, 15], [247, 31, 218], [260, 11, 152, 75, 232, 60], [32, 60, 85], [142, 166, 36], [94, 30, 25]], ![[213, 91, 5, 236, 2, 30], [177, 80, 116], [43, 37, 247, 30, 9, 70], [145, 257, 75], [121, 232, 51, 192, 27, 215], [138, 53, 147], [213, 168, 123], [205, 13, 90]]]
 h' := ![![[225, 77, 246, 185], [259, 92, 272, 71], [153, 14, 0, 179], [29, 68, 223, 78], [15, 115, 163, 146], [116, 187, 189, 204], [249, 52, 67, 158], [0, 0, 1], [0, 1]], ![[262, 206, 162, 5], [52, 252, 32, 238], [233, 109, 207, 227], [145, 142, 75, 213], [74, 172, 128, 248], [207, 225, 6, 204], [157, 61, 13, 242], [71, 249, 59, 26], [225, 77, 246, 185]], ![[225, 270, 146, 87], [158, 205, 117, 165], [81, 141, 37, 265], [140, 106, 142, 147], [84, 269, 270, 64], [10, 242, 219, 260], [96, 10, 114, 75], [86, 84, 137, 271], [262, 206, 162, 5]], ![[0, 1], [153, 5, 133, 80], [20, 13, 33, 160], [174, 238, 114, 116], [165, 275, 270, 96], [136, 177, 140, 163], [251, 154, 83, 79], [11, 221, 80, 257], [225, 270, 146, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [55, 90, 41], []]
 b := ![[], [], [158, 13, 258, 158], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI277N0 : CertifiedPrimeIdeal' SI277N0 277 where
  n := 4
  hpos := by decide
  P := [28, 225, 210, 119, 1]
  hirr := P277P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59291655736, 11084480248, 1639301770, -11641279038, 30450105888]
  a := ![-84, 56, -86, -62, 288]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1643115640, -28431382472, -3181999166, -8616424326, 30450105888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI277N0 : Ideal.IsPrime I277N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI277N0 B_one_repr
lemma NI277N0 : Nat.card (O ⧸ I277N0) = 5887339441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI277N0

def I277N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -7, -31, -10, 68]] i)))

def SI277N1: IdealEqSpanCertificate' Table ![![33, -7, -31, -10, 68]] 
 ![![277, 0, 0, 0, 0], ![127, 1, 0, 0, 0], ![214, 0, 1, 0, 0], ![59, 0, 0, 1, 0], ![242, 0, 0, 0, 1]] where
  M :=![![![33, -7, -31, -10, 68], ![-200, -40, 7, 8, -4], ![-92, -109, -152, -42, 356], ![-496, -155, -99, -9, 240], ![-68, -59, -83, -22, 193]]]
  hmulB := by decide  
  f := ![![![-42791, -9383, -13891, -2460, 43564]], ![![-20281, -4447, -6584, -1166, 20648]], ![![-35898, -7871, -11654, -2064, 36548]], ![![-14869, -3260, -4828, -855, 15140]], ![![-39518, -8665, -12829, -2272, 40233]]]
  g := ![![![-30, -7, -31, -10, 68], ![14, -40, 7, 8, -4], ![-135, -109, -152, -42, 356], ![-62, -155, -99, -9, 240], ![-73, -59, -83, -22, 193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI277N1 : Nat.card (O ⧸ I277N1) = 277 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI277N1)

lemma isPrimeI277N1 : Ideal.IsPrime I277N1 := prime_ideal_of_norm_prime hp277.out _ NI277N1
def MulI277N0 : IdealMulLeCertificate' Table 
  ![![-42791, -9383, -13891, -2460, 43564]] ![![33, -7, -31, -10, 68]]
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

def I281N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 3, -3, -2, 4]] i)))

def SI281N0: IdealEqSpanCertificate' Table ![![5, 3, -3, -2, 4]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![123, 30, 1, 0, 0], ![122, 174, 0, 1, 0], ![14, 40, 0, 0, 1]] where
  M :=![![![5, 3, -3, -2, 4], ![8, -16, 25, 8, -68], ![228, 53, 0, -6, -92], ![268, 43, 151, 17, -432], ![150, 31, 29, 2, -121]]]
  hmulB := by decide  
  f := ![![![-1471, -129, 533, 208, -1124]], ![![2708, 226, -1001, -390, 2116]], ![![-373, -34, 133, 52, -280]], ![![1050, 85, -393, -153, 832]], ![![304, 25, -113, -44, 239]]]
  g := ![![![2, 1, -3, -2, 4], ![-11, 2, 25, 8, -68], ![8, 17, 0, -6, -92], ![-51, 35, 151, 17, -432], ![-7, 13, 29, 2, -121]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P0 : CertificateIrreducibleZModOfList' 281 2 2 8 [190, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [257, 280], [0, 1]]
 g := ![![[9, 121], [252], [218], [24, 43], [11, 66], [271], [14], [1]], ![[196, 160], [252], [218], [116, 238], [113, 215], [271], [14], [1]]]
 h' := ![![[257, 280], [43, 11], [49, 231], [217, 201], [158, 263], [215, 105], [1, 73], [91, 257], [0, 1]], ![[0, 1], [60, 270], [125, 50], [170, 80], [28, 18], [224, 176], [216, 208], [105, 24], [257, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [49, 168]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N0 : CertifiedPrimeIdeal' SI281N0 281 where
  n := 2
  hpos := by decide
  P := [190, 24, 1]
  hirr := P281P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-166635, -3098, -89522, -20111, 274000]
  a := ![-12, 22, -8, 15, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![33673, -17004, -89522, -20111, 274000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N0 : Ideal.IsPrime I281N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N0 B_one_repr
lemma NI281N0 : Nat.card (O ⧸ I281N0) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N0

def I281N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 8, -18, -6, 36]] i)))

def SI281N1: IdealEqSpanCertificate' Table ![![23, 8, -18, -6, 36]] 
 ![![281, 0, 0, 0, 0], ![0, 281, 0, 0, 0], ![26, 33, 1, 0, 0], ![133, 31, 0, 1, 0], ![28, 178, 0, 0, 1]] where
  M :=![![![23, 8, -18, -6, 36], ![-96, -25, 26, 6, -36], ![96, -40, -43, 10, 36], ![-112, 112, -144, -81, 384], ![26, -4, -34, -6, 61]]]
  hmulB := by decide  
  f := ![![![-313, -72, -114, -22, 348]], ![![-1432, -321, -438, -74, 1380]], ![![-218, -49, -69, -12, 216]], ![![-349, -79, -116, -21, 360]], ![![-954, -214, -294, -50, 925]]]
  g := ![![![1, -20, -18, -6, 36], ![-2, 19, 26, 6, -36], ![-4, -19, -43, 10, 36], ![13, -217, -144, -81, 384], ![0, -34, -34, -6, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P281P1 : CertificateIrreducibleZModOfList' 281 2 2 8 [189, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 280], [0, 1]]
 g := ![![[142, 272], [34], [191], [153, 250], [73, 80], [80], [217], [1]], ![[24, 9], [34], [191], [90, 31], [154, 201], [80], [217], [1]]]
 h' := ![![[138, 280], [45, 159], [264, 92], [26, 219], [253, 237], [15, 262], [47, 262], [92, 138], [0, 1]], ![[0, 1], [69, 122], [34, 189], [181, 62], [82, 44], [203, 19], [235, 19], [28, 143], [138, 280]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [6, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI281N1 : CertifiedPrimeIdeal' SI281N1 281 where
  n := 2
  hpos := by decide
  P := [189, 143, 1]
  hirr := P281P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5598, 4446, -6256, -2832, 13821]
  a := ![-12, 6, -13, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![562, -7692, -6256, -2832, 13821]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI281N1 : Ideal.IsPrime I281N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI281N1 B_one_repr
lemma NI281N1 : Nat.card (O ⧸ I281N1) = 78961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI281N1

def I281N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, -14, 10, 8, -31]] i)))

def SI281N2: IdealEqSpanCertificate' Table ![![6, -14, 10, 8, -31]] 
 ![![281, 0, 0, 0, 0], ![218, 1, 0, 0, 0], ![246, 0, 1, 0, 0], ![53, 0, 0, 1, 0], ![221, 0, 0, 0, 1]] where
  M :=![![![6, -14, 10, 8, -31], ![43, 73, -72, -36, 167], ![-331, -258, 279, 108, -559], ![620, 252, -344, -81, 552], ![-55, -66, 64, 30, -142]]]
  hmulB := by decide  
  f := ![![![5064, 438, -1808, -710, 3767]], ![![3897, 337, -1390, -546, 2895]], ![![4503, 390, -1603, -630, 3337]], ![![932, 82, -320, -127, 659]], ![![4017, 348, -1430, -562, 2977]]]
  g := ![![![25, -14, 10, 8, -31], ![-118, 73, -72, -36, 167], ![374, -258, 279, 108, -559], ![-311, 252, -344, -81, 552], ![101, -66, 64, 30, -142]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI281N2 : Nat.card (O ⧸ I281N2) = 281 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI281N2)

lemma isPrimeI281N2 : Ideal.IsPrime I281N2 := prime_ideal_of_norm_prime hp281.out _ NI281N2
def MulI281N0 : IdealMulLeCertificate' Table 
  ![![5, 3, -3, -2, 4]] ![![23, 8, -18, -6, 36]]
  ![![-133, -155, 269, 96, -560]] where
 M := ![![![-133, -155, 269, 96, -560]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI281N1 : IdealMulLeCertificate' Table 
  ![![-133, -155, 269, 96, -560]] ![![6, -14, 10, 8, -31]]
  ![![281, 0, 0, 0, 0]] where
 M := ![![![-6182, -17703, 16017, 8992, -39621]]]
 hmul := by decide  
 g := ![![![![-22, -63, 57, 32, -141]]]]
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


def P283P0 : CertificateIrreducibleZModOfList' 283 5 2 8 [57, 57, 235, 267, 275, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [266, 244, 64, 260, 281], [232, 82, 276, 237, 172], [85, 23, 110, 12, 271], [274, 216, 116, 57, 125], [0, 1]]
 g := ![![[184, 167, 81, 67, 195], [194, 86, 253, 143, 135], [39, 142, 19, 201], [211, 51, 214, 77, 160], [119, 32, 94, 90, 90], [250, 80, 8, 1], [], []], ![[266, 64, 211, 198, 89, 57, 30, 38], [43, 38, 32, 76, 21, 130, 110, 163], [31, 52, 73, 265], [36, 76, 35, 154, 204, 111, 268, 24], [46, 249, 104, 160, 36, 169, 274, 28], [138, 242, 118, 152], [160, 200, 81, 63], [115, 197, 124, 4]], ![[106, 83, 236, 206, 195, 226, 208, 217], [5, 151, 138, 198, 2, 226, 136, 55], [253, 92, 60, 278], [48, 38, 11, 122, 131, 6, 89, 166], [235, 263, 262, 43, 138, 275, 24, 200], [155, 208, 115, 59], [117, 123, 6, 175], [214, 174, 108, 152]], ![[242, 145, 194, 72, 269, 189, 46, 195], [254, 76, 209, 181, 122, 156, 228, 176], [133, 15, 219, 83], [80, 100, 1, 277, 263, 88, 48, 275], [143, 156, 3, 165, 269, 99, 92, 138], [14, 62, 88, 238], [143, 251, 240, 175], [174, 211, 15, 144]], ![[30, 232, 130, 194, 36, 123, 110, 276], [177, 122, 210, 223, 208, 58, 181, 75], [140, 139, 280, 264], [240, 101, 77, 172, 278, 160, 16, 153], [39, 157, 273, 48, 118, 224, 163, 268], [130, 229, 150, 159], [142, 87, 167, 63], [126, 210, 14, 60]]]
 h' := ![![[266, 244, 64, 260, 281], [262, 263, 23, 272, 55], [112, 17, 148, 124, 237], [142, 146, 4, 94, 261], [9, 261, 26, 276, 187], [183, 151, 192, 252, 211], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[232, 82, 276, 237, 172], [158, 58, 256, 227, 84], [182, 47, 254, 80, 125], [225, 32, 263, 9, 185], [106, 23, 94, 270, 105], [266, 102, 102, 91, 206], [121, 263, 117, 18, 111], [243, 239, 152, 73, 189], [266, 244, 64, 260, 281]], ![[85, 23, 110, 12, 271], [210, 206, 169, 53, 155], [250, 32, 185, 13, 278], [239, 146, 225, 241, 174], [277, 144, 166, 111, 249], [234, 150, 171, 219, 178], [182, 142, 238, 157, 25], [25, 84, 221, 217, 32], [232, 82, 276, 237, 172]], ![[274, 216, 116, 57, 125], [38, 177, 258, 162, 269], [84, 132, 13, 132, 80], [34, 126, 281, 179, 145], [159, 207, 208, 199, 100], [152, 235, 62, 35, 123], [147, 55, 241, 175, 239], [137, 77, 266, 195, 251], [85, 23, 110, 12, 271]], ![[0, 1], [248, 145, 143, 135, 3], [210, 55, 249, 217, 129], [242, 116, 76, 43, 84], [110, 214, 72, 276, 208], [152, 211, 39, 252, 131], [223, 106, 253, 216, 190], [257, 166, 209, 81, 94], [274, 216, 116, 57, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 281, 230, 57], [], [], []]
 b := ![[], [252, 2, 111, 196, 170], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI283N0 : CertifiedPrimeIdeal' SI283N0 283 where
  n := 5
  hpos := by decide
  P := [57, 57, 235, 267, 275, 1]
  hirr := P283P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1926969566117756, -420778211690197, -645724923965901, -112851025137674, 2005772746079241]
  a := ![-125, 97, -125, -66, 429]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6809079738932, -1486848804559, -2281713512247, -398766873278, 7087536205227]
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

def I293N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18, -48, -46, -14, 113]] i)))

def SI293N0: IdealEqSpanCertificate' Table ![![-18, -48, -46, -14, 113]] 
 ![![293, 0, 0, 0, 0], ![0, 293, 0, 0, 0], ![0, 0, 293, 0, 0], ![0, 0, 0, 293, 0], ![88, 137, 290, 101, 1]] where
  M :=![![![-18, -48, -46, -14, 113], ![-369, -105, -64, 6, 119], ![-679, -248, -433, -170, 1121], ![-1428, -878, 62, 159, -216], ![-365, -192, -184, -56, 452]]]
  hmulB := by decide  
  f := ![![![4, 0, 0, 0, -1]], ![![5, 3, 2, 0, -7]], ![![35, 0, 17, 4, -49]], ![![92, 22, 18, 3, -72]], ![![70, 9, 24, 5, -77]]]
  g := ![![![-34, -53, -112, -39, 113], ![-37, -56, -118, -41, 119], ![-339, -525, -1111, -387, 1121], ![60, 98, 214, 75, -216], ![-137, -212, -448, -156, 452]]]
  hle1 := by decide   
  hle2 := by decide  


def P293P0 : CertificateIrreducibleZModOfList' 293 4 2 8 [234, 269, 95, 107, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 139, 277, 142], [221, 6, 249, 2], [256, 147, 60, 149], [0, 1]]
 g := ![![[5, 140, 48, 220], [122, 218, 226], [79, 34, 76, 278], [248, 173, 161], [13, 248, 135], [150, 154, 103, 22], [1], []], ![[90, 72, 18, 67, 181, 246], [11, 105, 206], [77, 234, 184, 248, 208, 214], [123, 4, 198], [197, 202, 170], [140, 164, 85, 194, 47, 63], [178, 205, 88], [65, 248, 240]], ![[176, 272, 259, 257, 60, 200], [209, 132, 33], [11, 108, 209, 270, 196, 243], [101, 42, 126], [248, 228, 170], [19, 287, 30, 0, 79, 251], [4, 57, 81], [283, 275, 4]], ![[268, 31, 43, 0, 201, 54], [18, 54, 61], [150, 33, 0, 183, 211, 84], [192, 211, 57], [290, 112, 135], [242, 163, 4, 263, 231, 123], [57, 32, 126], [273, 144, 226]]]
 h' := ![![[2, 139, 277, 142], [16, 123, 145, 146], [266, 263, 192, 149], [180, 97, 79, 211], [265, 88, 232, 184], [60, 52, 113, 253], [59, 24, 198, 186], [0, 0, 1], [0, 1]], ![[221, 6, 249, 2], [101, 200, 7, 173], [100, 61, 281, 237], [128, 130, 131, 82], [279, 172, 239, 265], [134, 155, 1, 113], [268, 142, 218, 54], [30, 47, 85, 79], [2, 139, 277, 142]], ![[256, 147, 60, 149], [120, 60, 86, 283], [55, 12, 256, 97], [195, 273, 23, 104], [125, 278, 230, 88], [27, 145, 30, 180], [282, 174, 148, 38], [199, 178, 94, 9], [221, 6, 249, 2]], ![[0, 1], [207, 203, 55, 277], [84, 250, 150, 103], [68, 86, 60, 189], [162, 48, 178, 49], [199, 234, 149, 40], [115, 246, 22, 15], [189, 68, 113, 205], [256, 147, 60, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [88, 239, 41], []]
 b := ![[], [], [111, 279, 166, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI293N0 : CertifiedPrimeIdeal' SI293N0 293 where
  n := 4
  hpos := by decide
  P := [234, 269, 95, 107, 1]
  hirr := P293P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-315456354395, -64257717890, -108105412162, -20477381526, 336268547443]
  a := ![-86, 68, -89, -43, 295]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-102071974503, -157450678217, -333194485224, -115984985233, 336268547443]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI293N0 : Ideal.IsPrime I293N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI293N0 B_one_repr
lemma NI293N0 : Nat.card (O ⧸ I293N0) = 7370050801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI293N0

def I293N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 0, 0, 0, 1]] i)))

def SI293N1: IdealEqSpanCertificate' Table ![![-4, 0, 0, 0, 1]] 
 ![![293, 0, 0, 0, 0], ![126, 1, 0, 0, 0], ![239, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![289, 0, 0, 0, 1]] where
  M :=![![![-4, 0, 0, 0, 1], ![-5, -3, -2, 0, 7], ![-35, 0, -17, -4, 49], ![-92, -22, -18, -3, 72], ![-31, -4, -10, -2, 32]]]
  hmulB := by decide  
  f := ![![![18, 48, 46, 14, -113]], ![![9, 21, 20, 6, -49]], ![![17, 40, 39, 12, -96]], ![![12, 22, 18, 5, -44]], ![![19, 48, 46, 14, -113]]]
  g := ![![![-1, 0, 0, 0, 1], ![-4, -3, -2, 0, 7], ![-33, 0, -17, -4, 49], ![-46, -22, -18, -3, 72], ![-21, -4, -10, -2, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI293N1 : Nat.card (O ⧸ I293N1) = 293 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI293N1)

lemma isPrimeI293N1 : Ideal.IsPrime I293N1 := prime_ideal_of_norm_prime hp293.out _ NI293N1
def MulI293N0 : IdealMulLeCertificate' Table 
  ![![-18, -48, -46, -14, 113]] ![![-4, 0, 0, 0, 1]]
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

def I307N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, -19, -45, -10, 134]] i)))

def SI307N0: IdealEqSpanCertificate' Table ![![-111, -19, -45, -10, 134]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![114, 26, 1, 0, 0], ![53, 180, 0, 1, 0], ![172, 258, 0, 0, 1]] where
  M :=![![![-111, -19, -45, -10, 134], ![-530, -132, -137, -20, 458], ![-2010, -429, -748, -134, 2246], ![-4412, -927, -1387, -269, 4416], ![-1564, -335, -537, -98, 1655]]]
  hmulB := by decide  
  f := ![![![-5573, -501, 2017, 788, -4250]], ![![10218, 862, -3821, -1482, 8074]], ![![-1268, -119, 448, 176, -942]], ![![5069, 422, -1908, -739, 4034]], ![![5436, 441, -2071, -800, 4383]]]
  g := ![![![-57, -103, -45, -10, 134], ![-204, -362, -137, -20, 458], ![-964, -1747, -748, -134, 2246], ![-1927, -3439, -1387, -269, 4416], ![-716, -1289, -537, -98, 1655]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P0 : CertificateIrreducibleZModOfList' 307 2 2 8 [158, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [198, 306], [0, 1]]
 g := ![![[263, 105], [112, 209], [9], [168], [143, 145], [113, 7], [215], [1]], ![[177, 202], [49, 98], [9], [168], [302, 162], [271, 300], [215], [1]]]
 h' := ![![[198, 306], [110, 243], [61, 165], [191, 3], [124, 33], [259, 256], [204, 264], [149, 198], [0, 1]], ![[0, 1], [25, 64], [189, 142], [171, 304], [211, 274], [292, 51], [286, 43], [57, 109], [198, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [121, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N0 : CertifiedPrimeIdeal' SI307N0 307 where
  n := 2
  hpos := by decide
  P := [158, 109, 1]
  hirr := P307P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70122, -7384, -24606, -4494, 83612]
  a := ![-22, 22, -22, -3, 76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37160, -65572, -24606, -4494, 83612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N0 : Ideal.IsPrime I307N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N0 B_one_repr
lemma NI307N0 : Nat.card (O ⧸ I307N0) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N0

def I307N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -6, -14, -4, 34]] i)))

def SI307N1: IdealEqSpanCertificate' Table ![![-3, -6, -14, -4, 34]] 
 ![![307, 0, 0, 0, 0], ![0, 307, 0, 0, 0], ![108, 157, 1, 0, 0], ![118, 10, 0, 1, 0], ![284, 174, 0, 0, 1]] where
  M :=![![![-3, -6, -14, -4, 34], ![-114, -27, -14, 0, 46], ![-230, -82, -119, -28, 322], ![-552, -154, -146, -21, 432], ![-166, -54, -74, -16, 205]]]
  hmulB := by decide  
  f := ![![![-5, -30, 18, 12, -46]], ![![62, 99, -118, -48, 254]], ![![28, 39, -53, -20, 112]], ![![2, -8, 2, 3, -8]], ![![30, 28, -50, -16, 101]]]
  g := ![![![-25, -12, -14, -4, 34], ![-38, -19, -14, 0, 46], ![-246, -121, -119, -28, 322], ![-342, -170, -146, -21, 432], ![-158, -78, -74, -16, 205]]]
  hle1 := by decide   
  hle2 := by decide  


def P307P1 : CertificateIrreducibleZModOfList' 307 2 2 8 [277, 158, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 306], [0, 1]]
 g := ![![[138, 133], [114, 25], [118], [83], [43, 53], [9, 37], [97], [1]], ![[0, 174], [155, 282], [118], [83], [265, 254], [303, 270], [97], [1]]]
 h' := ![![[149, 306], [43, 146], [38, 5], [194, 90], [62, 156], [270, 214], [126, 61], [30, 149], [0, 1]], ![[0, 1], [0, 161], [169, 302], [96, 217], [281, 151], [228, 93], [5, 246], [127, 158], [149, 306]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [232]]
 b := ![[], [261, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI307N1 : CertifiedPrimeIdeal' SI307N1 307 where
  n := 2
  hpos := by decide
  P := [277, 158, 1]
  hirr := P307P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-779193, -114666, -717569, -104798, 1811590]
  a := ![245, -185, 244, 134, -839]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1385691, -656759, -717569, -104798, 1811590]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI307N1 : Ideal.IsPrime I307N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI307N1 B_one_repr
lemma NI307N1 : Nat.card (O ⧸ I307N1) = 94249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI307N1

def I307N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![253, 21, -93, -36, 196]] i)))

def SI307N2: IdealEqSpanCertificate' Table ![![253, 21, -93, -36, 196]] 
 ![![307, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![281, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![240, 0, 0, 0, 1]] where
  M :=![![![253, 21, -93, -36, 196], ![-476, -40, 169, 66, -356], ![856, 63, -318, -124, 676], ![-584, -55, 201, 83, -432], ![386, 29, -145, -56, 307]]]
  hmulB := by decide  
  f := ![![![3875, 827, 1281, 230, -4012]], ![![1620, 346, 535, 96, -1676]], ![![3781, 808, 1249, 224, -3912]], ![![667, 144, 218, 39, -684]], ![![3206, 685, 1059, 190, -3317]]]
  g := ![![![-74, 21, -93, -36, 196], ![135, -40, 169, 66, -356], ![-254, 63, -318, -124, 676], ![170, -55, 201, 83, -432], ![-115, 29, -145, -56, 307]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI307N2 : Nat.card (O ⧸ I307N2) = 307 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI307N2)

lemma isPrimeI307N2 : Ideal.IsPrime I307N2 := prime_ideal_of_norm_prime hp307.out _ NI307N2
def MulI307N0 : IdealMulLeCertificate' Table 
  ![![-111, -19, -45, -10, 134]] ![![-3, -6, -14, -4, 34]]
  ![![-3875, -827, -1281, -230, 4012]] where
 M := ![![![-3875, -827, -1281, -230, 4012]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI307N1 : IdealMulLeCertificate' Table 
  ![![-3875, -827, -1281, -230, 4012]] ![![253, 21, -93, -36, 196]]
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


lemma PB312I6_primes (p : ℕ) :
  p ∈ Set.range ![257, 263, 269, 271, 277, 281, 283, 293, 307] ↔ Nat.Prime p ∧ 251 < p ∧ p ≤ 307 := by
  rw [← List.mem_ofFn']
  convert primes_range 251 307 (by omega)

def PB312I6 : PrimesBelowBoundCertificateInterval O 251 307 312 where
  m := 9
  g := ![1, 2, 4, 2, 2, 3, 1, 2, 3]
  P := ![257, 263, 269, 271, 277, 281, 283, 293, 307]
  hP := PB312I6_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I257N0]
    · exact ![I263N0, I263N1]
    · exact ![I269N0, I269N1, I269N2, I269N3]
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
    · exact ![1121154893057]
    · exact ![18191447, 69169]
    · exact ![72361, 269, 269, 269]
    · exact ![5393580481, 271]
    · exact ![5887339441, 277]
    · exact ![78961, 78961, 281]
    · exact ![1815232161643]
    · exact ![7370050801, 293]
    · exact ![94249, 94249, 307]
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
      exact NI269N2
      exact NI269N3
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
  β := ![I269N1, I269N2, I269N3, I271N1, I277N1, I281N2, I293N1, I307N2]
  Il := ![[], [], [I269N1, I269N2, I269N3], [I271N1], [I277N1], [I281N2], [], [I293N1], [I307N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
