
import IdealArithmetic.Examples.NF5_1_145800000_5.RI5_1_145800000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![286633, -142458, 16076, -7952, 27564]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![286633, -142458, 16076, -7952, 27564]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![150, 66, 1, 0, 0], ![50, 197, 0, 1, 0], ![101, 157, 0, 0, 1]] where
  M :=![![![286633, -142458, 16076, -7952, 27564], ![-165384, 82197, -9276, 4588, -15904], ![47712, -23714, 2677, -1324, 4588], ![68928, -34256, 3864, -1911, 6628], ![-19884, 9884, -1116, 550, -1911]]]
  hmulB := by decide  
  f := ![![![-401, -570, 244, 176, 156]], ![![-936, -1405, 420, 332, 352]], ![![-618, -904, 325, 244, 236]], ![![-1030, -1539, 476, 373, 388]], ![![-943, -1401, 452, 350, 357]]]
  g := ![![![-22669, -19922, 16076, -7952, 27564], ![13080, 11495, -9276, 4588, -15904], ![-3774, -3316, 2677, -1324, 4588], ![-5450, -4791, 3864, -1911, 6628], ![1573, 1383, -1116, 550, -1911]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [23, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 198], [0, 1]]
 g := ![![[66, 26], [5, 8], [146, 49], [61], [122], [32], [74, 1]], ![[0, 173], [0, 191], [190, 150], [61], [122], [32], [148, 198]]]
 h' := ![![[74, 198], [84, 15], [25, 40], [121, 7], [23, 114], [21, 91], [89, 80], [0, 1]], ![[0, 1], [0, 184], [0, 159], [42, 192], [101, 85], [188, 108], [39, 119], [74, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72]]
 b := ![[], [61, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [23, 125, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-775, -1369, 820, -534, -506]
  a := ![0, -2, -3, -3, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-231, 649, 820, -534, -506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61, -107, -28, -8, 8]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-61, -107, -28, -8, 8]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![188, 188, 1, 0, 0], ![78, 73, 0, 1, 0], ![7, 46, 0, 0, 1]] where
  M :=![![![-61, -107, -28, -8, 8], ![-48, -153, -134, -64, -16], ![48, -27, -233, -126, -64], ![216, 240, -280, -169, -118], ![354, 440, -350, -221, -169]]]
  hmulB := by decide  
  f := ![![![-67, -45, 82, -20, -16]], ![![96, 143, -250, 180, -40]], ![![28, 93, -159, 150, -52]], ![![6, 31, -54, 57, -22]], ![![23, 37, -64, 47, -11]]]
  g := ![![![29, 27, -28, -8, 8], ![152, 153, -134, -64, -16], ![272, 281, -233, -126, -64], ![336, 355, -280, -169, -118], ![425, 453, -350, -221, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [102, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [82, 198], [0, 1]]
 g := ![![[7, 80], [138, 187], [153, 155], [52], [94], [40], [82, 1]], ![[0, 119], [149, 12], [127, 44], [52], [94], [40], [164, 198]]]
 h' := ![![[82, 198], [53, 94], [115, 171], [101, 126], [80, 101], [135, 33], [193, 55], [0, 1]], ![[0, 1], [0, 105], [8, 28], [85, 73], [4, 98], [55, 166], [126, 144], [82, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [52, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [102, 117, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1740, 3760, -29130, 38351, 4790]
  a := ![3, -65, 2, -66, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![12328, 12363, -29130, 38351, 4790]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -27, 42, -16, -4]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![-19, -27, 42, -16, -4]] 
 ![![199, 0, 0, 0, 0], ![89, 1, 0, 0, 0], ![119, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-19, -27, 42, -16, -4], ![24, 55, -94, 88, -32], ![96, 93, -105, -78, 88], ![-276, -384, 580, -193, -62], ![186, 400, -694, 611, -193]]]
  hmulB := by decide  
  f := ![![![-1834957, 911971, -102900, 50916, -176452]], ![![-815339, 405222, -45722, 22624, -78404]], ![![-1098821, 546112, -61619, 30490, -105664]], ![![-306507, 152333, -17188, 8505, -29474]], ![![-220662, 109668, -12374, 6123, -21219]]]
  g := ![![![-10, -27, 42, -16, -4], ![21, 55, -94, 88, -32], ![24, 93, -105, -78, 88], ![-137, -384, 580, -193, -62], ![159, 400, -694, 611, -193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![286633, -142458, 16076, -7952, 27564]] ![![-61, -107, -28, -8, 8]]
  ![![-1834957, 911971, -102900, 50916, -176452]] where
 M := ![![![-1834957, 911971, -102900, 50916, -176452]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![-1834957, 911971, -102900, 50916, -176452]] ![![-19, -27, 42, -16, -4]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1, I199N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
    exact isPrimeI199N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0 ⊙ MulI199N1)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2659, -4439, 7174, -4376, 636]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-2659, -4439, 7174, -4376, 636]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![7, 59, 1, 0, 0], ![9, 110, 0, 1, 0], ![74, 161, 0, 0, 1]] where
  M :=![![![-2659, -4439, 7174, -4376, 636], ![-3816, -573, -2518, 13712, -8752], ![26256, 31841, -44333, 1858, 13712], ![-39228, -63600, 101660, -58045, 6234], ![-18702, 6280, -32430, 98543, -58045]]]
  hmulB := by decide  
  f := ![![![15021311, -7465469, 842432, -416772, 1444476]], ![![-8666856, 4307935, -486178, 240388, -833544]], ![![-1913245, 951031, -107333, 53062, -184016]], ![![-3860427, 1918903, -216564, 107069, -371290]], ![![-1349900, 671331, -75796, 37395, -129903]]]
  g := ![![![-287, -231, 7174, -4376, 636], ![2550, 231, -2518, 13712, -8752], ![-3293, 1116, -44333, 1858, 13712], ![-3269, -3224, 101660, -58045, 6234], ![17141, 2015, -32430, 98543, -58045]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [155, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 210], [0, 1]]
 g := ![![[194, 80], [197, 4], [180], [82], [203, 76], [143], [103, 1]], ![[205, 131], [187, 207], [180], [82], [13, 135], [143], [206, 210]]]
 h' := ![![[103, 210], [60, 49], [1, 209], [204, 179], [185, 90], [178, 42], [71, 115], [0, 1]], ![[0, 1], [43, 162], [6, 2], [73, 32], [171, 121], [73, 169], [100, 96], [103, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [104, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [155, 108, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![108, -666, 7, -462, -20]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27, 251, 7, -462, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139781, 69472, -7840, 3878, -13442]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-139781, 69472, -7840, 3878, -13442]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![183, 25, 1, 0, 0], ![67, 100, 0, 1, 0], ![57, 171, 0, 0, 1]] where
  M :=![![![-139781, 69472, -7840, 3878, -13442], ![80652, -40085, 4524, -2238, 7756], ![-23268, 11564, -1305, 646, -2238], ![-33612, 16708, -1888, 933, -3232], ![9696, -4822, 548, -272, 933]]]
  hmulB := by decide  
  f := ![![![-287, -452, 88, 74, 90]], ![![-540, -919, -4, 86, 148]], ![![-315, -505, 75, 74, 96]], ![![-347, -580, 24, 63, 98]], ![![-513, -865, 16, 88, 143]]]
  g := ![![![8537, 10314, -7840, 3878, -13442], ![-4926, -5951, 4524, -2238, 7756], ![1421, 1717, -1305, 646, -2238], ![2055, 2480, -1888, 933, -3232], ![-595, -715, 548, -272, 933]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [210, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 210], [0, 1]]
 g := ![![[88, 49], [151, 179], [171], [122], [141, 95], [46], [88, 1]], ![[180, 162], [78, 32], [171], [122], [61, 116], [46], [176, 210]]]
 h' := ![![[88, 210], [151, 204], [36, 50], [169, 63], [141, 132], [194, 99], [88, 149], [0, 1]], ![[0, 1], [168, 7], [5, 161], [16, 148], [152, 79], [44, 112], [118, 62], [88, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [45, 186]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [210, 123, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2036, -1077, 3026, 3172, 3534]
  a := ![1, 18, 4, 17, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4596, -4731, 3026, 3172, 3534]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![583, 659, -324, -228, -194]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![583, 659, -324, -228, -194]] 
 ![![211, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![74, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![583, 659, -324, -228, -194], ![1164, 1811, -622, -454, -456], ![1368, 2095, -469, -394, -454], ![780, 1360, 136, -15, -166], ![498, 1122, 530, 219, -15]]]
  hmulB := by decide  
  f := ![![![8413, 9597, -12870, -1484, 5398]], ![![1561, 1730, -2276, -450, 1086]], ![![1039, 1290, -1821, 178, 492]], ![![3470, 3942, -5272, -669, 2254]], ![![2785, 2849, -3536, -1621, 2333]]]
  g := ![![![76, 659, -324, -228, -194], ![79, 1811, -622, -454, -456], ![-18, 2095, -469, -394, -454], ![-208, 1360, 136, -15, -166], ![-359, 1122, 530, 219, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-2659, -4439, 7174, -4376, 636]] ![![-139781, 69472, -7840, 3878, -13442]]
  ![![-8413, -9597, 12870, 1484, -5398]] where
 M := ![![![-8413, -9597, 12870, 1484, -5398]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![-8413, -9597, 12870, 1484, -5398]] ![![583, 659, -324, -228, -194]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1, I211N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
    exact isPrimeI211N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0 ⊙ MulI211N1)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19145, -27264, 41270, -15309, -3252]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-19145, -27264, 41270, -15309, -3252]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![140, 61, 1, 0, 0], ![157, 29, 0, 1, 0], ![177, 205, 0, 0, 1]] where
  M :=![![![-19145, -27264, 41270, -15309, -3252], ![19512, 48141, -87048, 85792, -30618], ![91854, 88704, -104949, -71739, 85792], ![-267132, -373786, 561188, -190741, -56430], ![169290, 372748, -655936, 589403, -190741]]]
  hmulB := by decide  
  f := ![![![-1892291, 938918, -104894, 53191, -181370]], ![![1088220, -546225, 64136, -28418, 106382]], ![![-891742, 440715, -48373, 25669, -84892]], ![![-1192781, 590985, -65614, 33816, -114046]], ![![-501003, 242781, -24258, 16084, -46099]]]
  g := ![![![-12636, -6431, 41270, -15309, -3252], ![18638, 41017, -87048, 85792, -30618], ![48711, -40432, -104949, -71739, 85792], ![-174435, -78505, 561188, -190741, -56430], ![148992, 279794, -655936, 589403, -190741]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [29, 184, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 222], [0, 1]]
 g := ![![[114, 100], [198, 115], [70, 124], [185, 41], [138, 146], [78], [39, 1]], ![[0, 123], [0, 108], [0, 99], [0, 182], [34, 77], [78], [78, 222]]]
 h' := ![![[39, 222], [56, 10], [200, 195], [210, 149], [12, 34], [1, 121], [207, 154], [0, 1]], ![[0, 1], [0, 213], [0, 28], [0, 74], [0, 189], [37, 102], [192, 69], [39, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [167, 203]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [29, 184, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2608, -2541, 2862, 1095, -2965]
  a := ![-1, 2, -4, 4, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-226, 1789, 2862, 1095, -2965]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, -21, 2, -1, 4]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![43, -21, 2, -1, 4]] 
 ![![223, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![35, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![39, 0, 0, 0, 1]] where
  M :=![![![43, -21, 2, -1, 4], ![-24, 13, -2, 0, -2], ![6, -5, 3, -1, 0], ![12, -2, -4, 3, 0], ![0, 4, -2, -4, 3]]]
  hmulB := by decide  
  f := ![![![-143, -181, 148, 95, 70]], ![![-41, -52, 42, 27, 20]], ![![-25, -32, 25, 16, 12]], ![![-13, -17, 12, 8, 6]], ![![-27, -35, 26, 17, 13]]]
  g := ![![![5, -21, 2, -1, 4], ![-3, 13, -2, 0, -2], ![1, -5, 3, -1, 0], ![1, -2, -4, 3, 0], ![-1, 4, -2, -4, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 62, -74, 8, 12]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![47, 62, -74, 8, 12]] 
 ![![223, 0, 0, 0, 0], ![92, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![170, 0, 0, 1, 0], ![208, 0, 0, 0, 1]] where
  M :=![![![47, 62, -74, 8, 12], ![-72, -123, 244, -160, 16], ![-48, 22, -43, 236, -160], ![516, 656, -900, 117, 228], ![-684, -1104, 1796, -1014, 117]]]
  hmulB := by decide  
  f := ![![![552083249, -274388242, 30964250, -15316488, 53091044]], ![![226336828, -112490579, 12694372, -6279280, 21765664]], ![![12790651, -6357020, 717379, -354852, 1230012]], ![![421465978, -209470780, 23638424, -11692763, 40530244]], ![![514775852, -255846272, 28871820, -14281466, 49503381]]]
  g := ![![![-41, 62, -74, 8, 12], ![152, -123, 244, -160, 16], ![-39, 22, -43, 236, -160], ![-550, 656, -900, 117, 228], ![1076, -1104, 1796, -1014, 117]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2

def I223N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-400386595807, 198994218158, -22456160712, 11107956533, -38503146636]] i)))

def SI223N3: IdealEqSpanCertificate' Table ![![-400386595807, 198994218158, -22456160712, 11107956533, -38503146636]] 
 ![![223, 0, 0, 0, 0], ![171, 1, 0, 0, 0], ![209, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![-400386595807, 198994218158, -22456160712, 11107956533, -38503146636], ![231018879816, -114817583431, 12956969956, -6409174788, 22215913066], ![-66647739198, 33124272622, -3738018101, 1849013423, -6409174788], ![-96281915544, 47852612218, -5400086296, 2671156687, -9258943110], ![27776829330, -13805228480, 1557896668, -770614741, 2671156687]]]
  hmulB := by decide  
  f := ![![![-35125, -62932, -4632, 489, 7678]], ![![-27141, -48711, -3772, 299, 5892]], ![![-32933, -59212, -4773, 236, 7120]], ![![-16680, -30170, -2744, -119, 3494]], ![![-20118, -36438, -3556, -99, 4189]]]
  g := ![![![-115929615523, 198994218158, -22456160712, 11107956533, -38503146636], ![66890176135, -114817583431, 12956969956, -6409174788, 22215913066], ![-19297466153, 33124272622, -3738018101, 1849013423, -6409174788], ![-27877869958, 47852612218, -5400086296, 2671156687, -9258943110], ![8042619754, -13805228480, 1557896668, -770614741, 2671156687]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N3 : Nat.card (O ⧸ I223N3) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N3)

lemma isPrimeI223N3 : Ideal.IsPrime I223N3 := prime_ideal_of_norm_prime hp223.out _ NI223N3
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-19145, -27264, 41270, -15309, -3252]] ![![43, -21, 2, -1, 4]]
  ![![-104987, -141127, 207788, -55044, -31808]] where
 M := ![![![-104987, -141127, 207788, -55044, -31808]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-104987, -141127, 207788, -55044, -31808]] ![![47, 62, -74, 8, 12]]
  ![![-11393101, 14427931, -43188402, 96591556, -53035524]] where
 M := ![![![-11393101, 14427931, -43188402, 96591556, -53035524]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N2 : IdealMulLeCertificate' Table 
  ![![-11393101, 14427931, -43188402, 96591556, -53035524]] ![![-400386595807, 198994218158, -22456160712, 11107956533, -38503146636]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![1584415, 1885465, -2597058, -8251, 885310]]]
 hmul := by decide  
 g := ![![![![7105, 8455, -11646, -37, 3970]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2, I223N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
    exact isPrimeI223N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1 ⊙ MulI223N2)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-197951, 98383, -11102, 5492, -19036]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-197951, 98383, -11102, 5492, -19036]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![226, 29, 65, 1, 0], ![65, 190, 117, 0, 1]] where
  M :=![![![-197951, 98383, -11102, 5492, -19036], ![114216, -56765, 6406, -3168, 10984], ![-32952, 16375, -1845, 914, -3168], ![-47604, 23656, -2668, 1323, -4578], ![13734, -6824, 766, -379, 1323]]]
  hmulB := by decide  
  f := ![![![35, 53, -20, -8, -12]], ![![72, 111, -14, -28, -16]], ![![48, 93, 31, -6, -28]], ![![58, 94, -13, -13, -22]], ![![95, 156, -1, -29, -31]]]
  g := ![![![-889, 15665, 8190, 5492, -19036], ![512, -9039, -4726, -3168, 10984], ![-148, 2607, 1363, 914, -3168], ![-216, 3767, 1969, 1323, -4578], ![59, -1089, -570, -379, 1323]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [165, 157, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 8, 188], [201, 218, 39], [0, 1]]
 g := ![![[132, 67, 155], [47, 197, 79], [168, 195], [12, 62], [204, 43], [112, 63, 196], [1]], ![[149, 13, 50, 103], [19, 160, 59, 213], [16, 25], [118, 222], [120, 62], [118, 71, 89, 225], [12, 116, 57, 155]], ![[210, 223, 156, 216], [104, 69, 15, 148], [163, 139], [55, 33], [35, 131], [99, 213, 156, 94], [110, 57, 147, 72]]]
 h' := ![![[12, 8, 188], [190, 178, 137], [164, 133, 144], [155, 78, 167], [186, 106, 17], [134, 154, 66], [62, 70, 213], [0, 1]], ![[201, 218, 39], [96, 138, 224], [107, 216, 100], [134, 145, 222], [38, 193, 26], [61, 11, 210], [202, 138, 120], [12, 8, 188]], ![[0, 1], [13, 138, 93], [208, 105, 210], [35, 4, 65], [22, 155, 184], [24, 62, 178], [140, 19, 121], [201, 218, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137, 219], []]
 b := ![[], [8, 110, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [165, 157, 14, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![399669, -29010, 496276, -1770540, 1050430]
  a := ![0, -10, 4, -20, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1463717, -653150, -32242, -1770540, 1050430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 53, -20, -8, -12]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![35, 53, -20, -8, -12]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![221, 162, 1, 0, 0], ![64, 199, 0, 1, 0], ![59, 28, 0, 0, 1]] where
  M :=![![![35, 53, -20, -8, -12], ![72, 111, -14, -28, -16], ![48, 93, 31, -6, -28], ![48, 96, -40, 59, 2], ![-6, -4, 106, -41, 59]]]
  hmulB := by decide  
  f := ![![![-197951, 98383, -11102, 5492, -19036]], ![![114216, -56765, 6406, -3168, 10984]], ![![-111353, 55344, -6245, 3090, -10708]], ![![44108, -21921, 2474, -1223, 4242]], ![![-37301, 18539, -2092, 1035, -3587]]]
  g := ![![![25, 23, -20, -8, -12], ![26, 37, -14, -28, -16], ![-21, -13, 31, -6, -28], ![22, -23, -40, 59, 2], ![-107, -47, 106, -41, 59]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [221, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [145, 226], [0, 1]]
 g := ![![[62, 189], [32, 192], [219], [129], [213], [202, 44], [145, 1]], ![[0, 38], [178, 35], [219], [129], [213], [226, 183], [63, 226]]]
 h' := ![![[145, 226], [192, 102], [62, 54], [164, 30], [170, 122], [77, 126], [189, 147], [0, 1]], ![[0, 1], [0, 125], [174, 173], [201, 197], [154, 105], [187, 101], [166, 80], [145, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [221, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [221, 82, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-62, -1931, 2039, 5, -1265]
  a := ![13, 0, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1658, -1312, 2039, 5, -1265]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-197951, 98383, -11102, 5492, -19036]] ![![35, 53, -20, -8, -12]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-737, -795, 1028, 287, -550]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-737, -795, 1028, 287, -550]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![158, 78, 218, 1, 0], ![135, 130, 186, 0, 1]] where
  M :=![![![-737, -795, 1028, 287, -550], ![3300, 4691, -7090, 2606, 574], ![-1722, -4191, 7561, -7377, 2606], ![-9468, -9850, 12384, 4955, -7664], ![22992, 32114, -48170, 16216, 4955]]]
  hmulB := by decide  
  f := ![![![-82169, 40847, -4598, 2285, -7900]], ![![47400, -23567, 2694, -1296, 4570]], ![![-13710, 6767, -717, 409, -1296]], ![![-53686, 26640, -2942, 1527, -5136]], ![![-32643, 16185, -1762, 943, -3113]]]
  g := ![![![123, 211, 178, 287, -550], ![-2122, -1193, -2978, 2606, 574], ![3546, 1015, 4939, -7377, 2606], ![1058, 2620, 1562, 4955, -7664], ![-14009, -8196, -19672, 16216, 4955]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [189, 184, 211, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 151, 194], [210, 77, 35], [0, 1]]
 g := ![![[41, 197, 48], [38, 68], [207, 198, 130], [87, 46], [70, 174], [125, 124, 95], [1]], ![[148, 219, 38, 59], [163, 16], [58, 61, 133, 205], [220, 193], [177, 51], [137, 227, 7, 105], [127, 215, 38, 177]], ![[106, 62, 29, 200], [175, 83], [36, 207, 115, 22], [190, 53], [54, 226], [127, 71, 39, 34], [63, 227, 180, 52]]]
 h' := ![![[37, 151, 194], [68, 208, 174], [36, 164, 143], [44, 93, 151], [122, 50, 59], [191, 48, 116], [40, 45, 18], [0, 1]], ![[210, 77, 35], [205, 148, 164], [201, 13, 4], [43, 126, 128], [113, 30, 45], [210, 148, 153], [86, 142, 40], [37, 151, 194]], ![[0, 1], [141, 102, 120], [195, 52, 82], [113, 10, 179], [38, 149, 125], [54, 33, 189], [12, 42, 171], [210, 77, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [188, 18], []]
 b := ![[], [129, 146, 151], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [189, 184, 211, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1069, 17491, -31146, 60113, -30742]
  a := ![-1, -4, 2, -5, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23357, -2947, -32392, 60113, -30742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![912065, -453288, 51152, -25305, 87706]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![912065, -453288, 51152, -25305, 87706]] 
 ![![229, 0, 0, 0, 0], ![104, 1, 0, 0, 0], ![88, 0, 1, 0, 0], ![181, 0, 0, 1, 0], ![206, 0, 0, 0, 1]] where
  M :=![![![912065, -453288, 51152, -25305, 87706], ![-526236, 261569, -29516, 14598, -50610], ![151830, -75436, 8519, -4211, 14598], ![219324, -109002, 12312, -6079, 21094], ![-63282, 31442, -3532, 1765, -6079]]]
  hmulB := by decide  
  f := ![![![-6007, -12278, 21184, -17647, 5188]], ![![-2864, -5691, 9740, -7852, 2202]], ![![-1846, -4110, 7255, -6585, 2156]], ![![-5167, -10508, 18104, -14996, 4374]], ![![-6224, -11668, 19620, -14651, 3619]]]
  g := ![![![131290, -453288, 51152, -25305, 87706], ![-75758, 261569, -29516, 14598, -50610], ![21845, -75436, 8519, -4211, 14598], ![31559, -109002, 12312, -6079, 21094], ![-9125, 31442, -3532, 1765, -6079]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, -2, 0, 0]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![1, 1, -2, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![147, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![57, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![1, 1, -2, 0, 0], ![0, -1, 2, -4, 0], ![0, 1, -1, 2, -4], ![12, 16, -20, 3, 2], ![-6, -12, 26, -21, 3]]]
  hmulB := by decide  
  f := ![![![1957, -1019, 128, -44, 200]], ![![1251, -652, 82, -28, 128]], ![![625, -326, 41, -14, 64]], ![![489, -255, 32, -11, 50]], ![![401, -209, 26, -9, 41]]]
  g := ![![![0, 1, -2, 0, 0], ![1, -1, 2, -4, 0], ![0, 1, -1, 2, -4], ![-5, 16, -20, 3, 2], ![4, -12, 26, -21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-737, -795, 1028, 287, -550]] ![![912065, -453288, 51152, -25305, 87706]]
  ![![-1957, 1019, -128, 44, -200]] where
 M := ![![![-1957, 1019, -128, 44, -200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-1957, 1019, -128, 44, -200]] ![![1, 1, -2, 0, 0]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, -189, 62, 288, -236]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-205, -189, 62, 288, -236]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![59, 47, 20, 1, 0], ![218, 148, 113, 0, 1]] where
  M :=![![![-205, -189, 62, 288, -236], ![1416, 1745, -2738, 360, 576], ![-1728, -2965, 4625, -3026, 360], ![-1788, -864, 204, 4265, -3314], ![9942, 12464, -17434, 1861, 4265]]]
  hmulB := by decide  
  f := ![![![-116106077, 57705323, -6511948, 3221140, -11165332]], ![![66991992, -33295369, 3757326, -1858564, 6442280]], ![![-19326840, 9605539, -1083969, 536186, -1858564]], ![![-17665631, 8779910, -990798, 490099, -1698814]], ![![-75417116, 37482697, -4229859, 2092303, -7252481]]]
  g := ![![![147, 91, 90, 288, -236], ![-624, -431, -322, 360, 576], ![422, 369, 105, -3026, 360], ![2013, 1241, 1242, 4265, -3314], ![-4419, -3031, -2303, 1861, 4265]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [36, 202, 210, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [70, 125, 188], [186, 107, 45], [0, 1]]
 g := ![![[11, 106, 129], [209, 74], [52, 4], [119, 123, 232], [44, 226], [46, 79, 63], [1]], ![[172, 84, 219, 222], [231, 55], [8, 60], [26, 13, 84, 221], [74, 74], [2, 26, 13, 24], [38, 206, 221, 211]], ![[10, 28, 218, 118], [4, 202], [228, 157], [66, 58, 64, 150], [48, 62], [201, 107, 193, 125], [133, 127, 228, 22]]]
 h' := ![![[70, 125, 188], [173, 30, 96], [170, 6, 128], [143, 223, 2], [206, 27, 89], [208, 111, 172], [197, 31, 23], [0, 1]], ![[186, 107, 45], [95, 10, 68], [16, 35, 145], [184, 206, 198], [4, 131, 153], [173, 223, 128], [54, 115, 134], [70, 125, 188]], ![[0, 1], [126, 193, 69], [152, 192, 193], [122, 37, 33], [38, 75, 224], [64, 132, 166], [200, 87, 76], [186, 107, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29, 155], []]
 b := ![[], [55, 92, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [36, 202, 210, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163101, 221995, -355679, 130787, 41299]
  a := ![3, -4, 7, -8, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-71058, -51662, -32782, 130787, 41299]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![116106077, -57705323, 6511948, -3221140, 11165332]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![116106077, -57705323, 6511948, -3221140, 11165332]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![8, 213, 1, 0, 0], ![160, 187, 0, 1, 0], ![135, 92, 0, 0, 1]] where
  M :=![![![116106077, -57705323, 6511948, -3221140, 11165332], ![-66991992, 33295369, -3757326, 1858564, -6442280], ![19326840, -9605539, 1083969, -536186, 1858564], ![27920304, -13876536, 1565944, -774595, 2684954], ![-8054862, 4003308, -451766, 223467, -774595]]]
  hmulB := by decide  
  f := ![![![205, 189, -62, -288, 236]], ![![-1416, -1745, 2738, -360, -576]], ![![-1280, -1576, 2481, -326, -520]], ![![-988, -1267, 2154, -505, -286]], ![![-483, -633, 1120, -317, -109]]]
  g := ![![![-3982519, -8024067, 6511948, -3221140, 11165332], ![2297872, 4629803, -3757326, 1858564, -6442280], ![-662924, -1335674, 1083969, -536186, 1858564], ![-957686, -1929567, 1565944, -774595, 2684954], ![276287, 556669, -451766, 223467, -774595]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [128, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [196, 232], [0, 1]]
 g := ![![[64, 71], [184], [29], [132, 214], [173], [84, 184], [196, 1]], ![[0, 162], [184], [29], [136, 19], [173], [33, 49], [159, 232]]]
 h' := ![![[196, 232], [182, 49], [203, 76], [113, 202], [215, 100], [199, 86], [76, 76], [0, 1]], ![[0, 1], [0, 184], [187, 157], [95, 31], [10, 133], [46, 147], [60, 157], [196, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [115]]
 b := ![[], [190, 174]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [128, 37, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![274, 46, -64, 167, -92]
  a := ![4, 1, -1, 2, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58, -39, -64, 167, -92]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-205, -189, 62, 288, -236]] ![![116106077, -57705323, 6511948, -3221140, 11165332]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-287, 278, -8, 9, -46]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-287, 278, -8, 9, -46]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![83, 73, 13, 1, 0], ![116, 55, 143, 0, 1]] where
  M :=![![![-287, 278, -8, 9, -46], ![276, 73, 96, 30, 18], ![-54, 114, 163, 87, 30], ![-228, -102, 216, 133, 78], ![-234, -318, 288, 177, 133]]]
  hmulB := by decide  
  f := ![![![11, 20, -32, 21, -4]], ![![24, 11, 0, -60, 42]], ![![-126, -156, 221, -21, -60]], ![![5, 3, -1, -11, 8]], ![![-64, -81, 117, -18, -27]]]
  g := ![![![18, 9, 27, 9, -46], ![-18, -13, -12, 30, 18], ![-45, -33, -22, 87, 30], ![-85, -59, -53, 133, 78], ![-127, -86, -88, 177, 133]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [169, 79, 226, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 80, 174], [117, 158, 65], [0, 1]]
 g := ![![[19, 34, 216], [52, 50, 147], [196, 68, 90], [168, 141, 55], [118, 27], [154, 143, 169], [1]], ![[162, 191, 158, 67], [111, 31, 237, 200], [74, 97, 200, 162], [205, 25, 19, 128], [161, 144], [181, 189, 25, 196], [61, 72, 219, 225]], ![[143, 133, 48, 23], [64, 96, 96, 230], [174, 209, 141, 117], [143, 87, 193, 65], [168, 187], [69, 171, 182, 118], [175, 14, 12, 14]]]
 h' := ![![[135, 80, 174], [55, 197, 107], [97, 42, 214], [49, 35, 114], [42, 230, 85], [25, 115, 79], [70, 160, 13], [0, 1]], ![[117, 158, 65], [210, 238, 38], [209, 40, 12], [167, 62, 202], [86, 52, 153], [7, 141, 227], [77, 43, 19], [135, 80, 174]], ![[0, 1], [53, 43, 94], [17, 157, 13], [206, 142, 162], [99, 196, 1], [17, 222, 172], [135, 36, 207], [117, 158, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 10], []]
 b := ![[], [171, 104, 184], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [169, 79, 226, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9661109, -12221816, 17053574, -1934704, -3456664]
  a := ![7, 2, -24, 2, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2309173, 1335264, 2244802, -1934704, -3456664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-353455, 175669, -19824, 9806, -33990]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-353455, 175669, -19824, 9806, -33990]] 
 ![![239, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![230, 0, 1, 0, 0], ![232, 0, 0, 1, 0], ![203, 0, 0, 0, 1]] where
  M :=![![![-353455, 175669, -19824, 9806, -33990], ![203940, -101359, 11438, -5658, 19612], ![-58836, 29241, -3299, 1632, -5658], ![-84996, 42244, -4768, 2359, -8174], ![24522, -12186, 1374, -681, 2359]]]
  hmulB := by decide  
  f := ![![![4111, 5207, -3894, -2462, -1926]], ![![1046, 1329, -982, -622, -488]], ![![4018, 5099, -3785, -2396, -1878]], ![![4040, 5132, -3796, -2403, -1886]], ![![3541, 4505, -3312, -2099, -1649]]]
  g := ![![![-5681, 175669, -19824, 9806, -33990], ![3278, -101359, 11438, -5658, 19612], ![-946, 29241, -3299, 1632, -5658], ![-1366, 42244, -4768, 2359, -8174], ![395, -12186, 1374, -681, 2359]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, -27, 34, -7, 8]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![-19, -27, 34, -7, 8]] 
 ![![239, 0, 0, 0, 0], ![155, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![46, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-19, -27, 34, -7, 8], ![-48, -49, 26, 60, -14], ![42, 45, -119, 33, 60], ![-156, -254, 332, -179, 40], ![-120, -72, -54, 312, -179]]]
  hmulB := by decide  
  f := ![![![-156714617, 77887981, -8789528, 4347745, -15070450]], ![![-101256665, 50325090, -5679102, 2809171, -9737340]], ![![-37484601, 18630042, -2102369, 1039938, -3604704]], ![![-30320326, 15069360, -1700552, 841179, -2915752]], ![![-13068704, 6495214, -732974, 362566, -1256751]]]
  g := ![![![10, -27, 34, -7, 8], ![15, -49, 26, 60, -14], ![-12, 45, -119, 33, 60], ![116, -254, 332, -179, 40], ![14, -72, -54, 312, -179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-287, 278, -8, 9, -46]] ![![-353455, 175669, -19824, 9806, -33990]]
  ![![156714617, -77887981, 8789528, -4347745, 15070450]] where
 M := ![![![156714617, -77887981, 8789528, -4347745, 15070450]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![156714617, -77887981, 8789528, -4347745, 15070450]] ![![-19, -27, 34, -7, 8]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43265, 21170, -3056, 875, -4294]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-43265, 21170, -3056, 875, -4294]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![180, 157, 153, 1, 0], ![175, 125, 125, 0, 1]] where
  M :=![![![-43265, 21170, -3056, 875, -4294], ![25764, -11969, -600, -1818, 1750], ![-5250, 5582, -3219, -1475, -1818], ![-7428, 9022, -3208, -1401, -2350], ![7050, 4082, -2728, -2033, -1401]]]
  hmulB := by decide  
  f := ![![![-1829, -1932, 2456, 857, -1432]], ![![8592, 12083, -18184, 6344, 1714]], ![![-5142, -11652, 20653, -19041, 6344]], ![![870, -1067, 3221, -7256, 3992]], ![![709, -837, 2553, -5801, 3199]]]
  g := ![![![2285, 1745, 1659, 875, -4294], ![194, 227, 244, -1818, 1750], ![2400, 1927, 1866, -1475, -1818], ![2722, 2169, 2095, -1401, -2350], ![2565, 2068, 2006, -2033, -1401]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 3 2 7 [175, 65, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 7, 153], [106, 233, 88], [0, 1]]
 g := ![![[95, 63, 121], [16, 94], [59, 20], [33, 194], [167, 219, 53], [168, 117, 50], [1]], ![[117, 193, 165, 219], [240, 205], [190, 194], [57, 107], [234, 62, 120, 66], [124, 164, 50, 227], [201, 219, 115, 76]], ![[199, 100, 200, 70], [226, 183], [210, 81], [157, 125], [4, 94, 48, 112], [174, 53, 160, 230], [150, 126, 30, 165]]]
 h' := ![![[4, 7, 153], [133, 88, 11], [102, 46, 24], [8, 145, 35], [177, 229, 215], [2, 194, 52], [66, 176, 110], [0, 1]], ![[106, 233, 88], [54, 111, 121], [222, 228, 98], [93, 175, 215], [118, 58, 59], [77, 110, 105], [75, 38, 20], [4, 7, 153]], ![[0, 1], [95, 42, 109], [230, 208, 119], [59, 162, 232], [32, 195, 208], [237, 178, 84], [13, 27, 111], [106, 233, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 141], []]
 b := ![[], [100, 153, 207], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 3
  hpos := by decide
  P := [175, 65, 131, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-494850, -633848, 847443, -96607, -165338]
  a := ![1, 2, -7, 1, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![190160, 146061, 150604, -96607, -165338]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 13997521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![138697, 154798, -204570, -36399, 94772]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![138697, 154798, -204570, -36399, 94772]] 
 ![![241, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![212, 0, 0, 1, 0], ![186, 0, 0, 0, 1]] where
  M :=![![![138697, 154798, -204570, -36399, 94772], ![-568632, -824049, 1257316, -503912, -72798], ![218394, 635534, -1188039, 1293715, -503912], ![1796052, 1942850, -2512684, -684127, 1330114], ![-3990342, -5678772, 8593420, -3177741, -684127]]]
  hmulB := by decide  
  f := ![![![153375321979045, -76228331821280, 8602238225982, -4255103511497, 14749326212094]], ![![44818057689791, -22274807505405, 2513674325822, -1243390867537, 4309925120480]], ![![6470057430952, -3215652155676, 362880903125, -179499307573, 622192582410]], ![![135072409906532, -67131689436074, 7575697529308, -3747324395369, 12989228060022]], ![![118328504031528, -58809881230198, 6636595558328, -3282796909685, 11379051620759]]]
  g := ![![![-77665, 154798, -204570, -36399, 94772], ![687699, -824049, 1257316, -503912, -72798], ![-886158, 635534, -1188039, 1293715, -503912], ![-885418, 1942850, -2512684, -684127, 1330114], ![4623224, -5678772, 8593420, -3177741, -684127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N1 : Nat.card (O ⧸ I241N1) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N1)

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := prime_ideal_of_norm_prime hp241.out _ NI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2764502777, -1373972242, 155050442, -76695816, 265848200]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![2764502777, -1373972242, 155050442, -76695816, 265848200]] 
 ![![241, 0, 0, 0, 0], ![105, 1, 0, 0, 0], ![151, 0, 1, 0, 0], ![214, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![2764502777, -1373972242, 155050442, -76695816, 265848200], ![-1595089200, 792767619, -89462484, 44252684, -153391632], ![460174896, -228709314, 25809459, -12766668, 44252684], ![664786548, -330402368, 37285348, -18443225, 63929148], ![-191787444, 95319356, -10756628, 5320774, -18443225]]]
  hmulB := by decide  
  f := ![![![3161, 3986, -3974, -1384, -1920]], ![![1425, 1797, -1778, -628, -848]], ![![2015, 2544, -2487, -908, -1228]], ![![2858, 3628, -3584, -1201, -1740]], ![![1312, 1660, -1604, -566, -705]]]
  g := ![![![479559509, -1373972242, 155050442, -76695816, 265848200], ![-276700823, 792767619, -89462484, 44252684, -153391632], ![79826741, -228709314, 25809459, -12766668, 44252684], ![115320814, -330402368, 37285348, -18443225, 63929148], ![-33269452, 95319356, -10756628, 5320774, -18443225]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-43265, 21170, -3056, 875, -4294]] ![![138697, 154798, -204570, -36399, 94772]]
  ![![-3161, -3986, 3974, 1384, 1920]] where
 M := ![![![-3161, -3986, 3974, 1384, 1920]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-3161, -3986, 3974, 1384, 1920]] ![![2764502777, -1373972242, 155050442, -76695816, 265848200]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![-241, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC241 : ContainsPrimesAboveP 241 ![I241N0, I241N1, I241N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
    exact isPrimeI241N1
    exact isPrimeI241N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 241 (by decide) (𝕀 ⊙ MulI241N0 ⊙ MulI241N1)
instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-79, 58, 416, 238, 202]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-79, 58, 416, 238, 202]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![184, 231, 173, 1, 0], ![45, 250, 171, 0, 1]] where
  M :=![![![-79, 58, 416, 238, 202], ![-1212, -1279, 2136, 630, 476], ![-1428, -1442, 1101, 1898, 630], ![-1284, -2044, 640, 471, 1660], ![-4980, -6962, 6256, -190, 471]]]
  hmulB := by decide  
  f := ![![![-361196333, 179516454, -20258128, 10020698, -34734418]], ![![208406508, -103579117, 11688728, -5781838, 20041396]], ![![-60124188, 29882034, -3372137, 1668030, -5781838]], ![![-114767188, 57039889, -6436855, 3183995, -11036578]], ![![101958621, -50673964, 5718471, -2828646, 9804843]]]
  g := ![![![-211, -420, -300, 238, 202], ![-552, -1059, -750, 630, 476], ![-1510, -2380, -1733, 1898, 630], ![-648, -2095, -1453, 471, 1660], ![35, -322, -165, -190, 471]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 3 2 7 [23, 57, 203, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [213, 146, 1], [86, 104, 250], [0, 1]]
 g := ![![[209, 209, 240], [164, 206, 28], [65, 155], [92, 36, 94], [82, 213, 124], [140, 202, 45], [1]], ![[133, 126, 74, 108], [25, 27, 67, 1], [92, 83], [188, 65, 144, 241], [28, 158, 214, 4], [111, 142, 239, 197], [100, 8, 235, 1]], ![[217, 179, 107, 199], [148, 118, 24, 54], [198, 3], [114, 91, 249, 151], [30, 10, 28, 150], [88, 53, 189, 137], [61, 117, 13, 250]]]
 h' := ![![[213, 146, 1], [244, 45, 156], [129, 201, 167], [143, 27, 54], [122, 57, 40], [43, 202, 56], [228, 194, 48], [0, 1]], ![[86, 104, 250], [97, 156, 205], [222, 189, 250], [189, 42, 121], [191, 190, 201], [14, 236, 2], [56, 92, 166], [213, 146, 1]], ![[0, 1], [70, 50, 141], [169, 112, 85], [177, 182, 76], [29, 4, 10], [131, 64, 193], [125, 216, 37], [86, 104, 250]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 187], []]
 b := ![[], [109, 127, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 3
  hpos := by decide
  P := [23, 57, 203, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80404, -124885, -39920, 114910, 158977]
  a := ![3, 5, 2, 10, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-113059, -264595, -187667, 114910, 158977]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 15813251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-151, -207, 128, 64, 74]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-151, -207, 128, 64, 74]] 
 ![![251, 0, 0, 0, 0], ![173, 1, 0, 0, 0], ![221, 0, 1, 0, 0], ![124, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-151, -207, 128, 64, 74], ![-444, -615, 326, 182, 128], ![-384, -571, 25, 262, 182], ![-324, -600, 176, -157, 198], ![-594, -866, 390, 77, -157]]]
  hmulB := by decide  
  f := ![![![-24443879861, 12148735279, -1370964214, 678148464, -2350643854]], ![![-16791583079, 8345504024, -941776004, 465850198, -1614761314]], ![![-21538511315, 10704752018, -1208013147, 597544598, -2071249308]], ![![-12099279604, 6013404820, -678602556, 335671257, -1163526306]], ![![-6518104207, 3239531653, -365575664, 180832273, -626812997]]]
  g := ![![![-22, -207, 128, 64, 74], ![11, -615, 326, 182, 128], ![192, -571, 25, 262, 182], ![282, -600, 176, -157, 198], ![255, -866, 390, 77, -157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1

def I251N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-737, -1072, 1806, -795, -130]] i)))

def SI251N2: IdealEqSpanCertificate' Table ![![-737, -1072, 1806, -795, -130]] 
 ![![251, 0, 0, 0, 0], ![234, 1, 0, 0, 0], ![232, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![-737, -1072, 1806, -795, -130], ![780, 2109, -3444, 3742, -1590], ![4770, 5028, -5841, -2649, 3742], ![-11616, -16558, 25460, -9583, -1854], ![5562, 14338, -25828, 26387, -9583]]]
  hmulB := by decide  
  f := ![![![32811801728753, -16307635919250, 1840289112042, -910300372663, 3155344426072]], ![![30514061904270, -15165647289531, 1711417628048, -846553997630, 2934382450022]], ![![30349800013174, -15084008276302, 1702204803583, -841996867183, 2918586217716]], ![![12842417933474, -6382748430374, 720282357264, -356288201647, 1234990147102]], ![![10448875772102, -5193145541520, 586037684716, -289883974915, 1004815346587]]]
  g := ![![![-321, -1072, 1806, -795, -130], ![266, 2109, -3444, 3742, -1590], ![572, 5028, -5841, -2649, 3742], ![-3810, -16558, 25460, -9583, -1854], ![3280, 14338, -25828, 26387, -9583]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N2 : Nat.card (O ⧸ I251N2) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N2)

lemma isPrimeI251N2 : Ideal.IsPrime I251N2 := prime_ideal_of_norm_prime hp251.out _ NI251N2
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-79, 58, 416, 238, 202]] ![![-151, -207, 128, 64, 74]]
  ![![-370667, -574585, 139864, 92680, 92700]] where
 M := ![![![-370667, -574585, 139864, 92680, 92700]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI251N1 : IdealMulLeCertificate' Table 
  ![![-370667, -574585, 139864, 92680, 92700]] ![![-737, -1072, 1806, -795, -130]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-68816921, -316671389, 457877714, -667994081, 424975128]]]
 hmul := by decide  
 g := ![![![![-274171, -1261639, 1824214, -2661331, 1693128]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1, I251N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
    exact isPrimeI251N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0 ⊙ MulI251N1)


lemma PB752I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB752I5 : PrimesBelowBoundCertificateInterval O 197 251 752 where
  m := 9
  g := ![3, 3, 4, 2, 3, 2, 3, 3, 3]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB752I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1, I223N2, I223N3]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0, I241N1, I241N2]
    · exact ![I251N0, I251N1, I251N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC199
    · exact PBC211
    · exact PBC223
    · exact PBC227
    · exact PBC229
    · exact PBC233
    · exact PBC239
    · exact PBC241
    · exact PBC251
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![39601, 39601, 199]
    · exact ![44521, 44521, 211]
    · exact ![49729, 223, 223, 223]
    · exact ![11697083, 51529]
    · exact ![12008989, 229, 229]
    · exact ![12649337, 54289]
    · exact ![13651919, 239, 239]
    · exact ![13997521, 241, 241]
    · exact ![15813251, 251, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
      exact NI199N2
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
      exact NI211N2
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
      exact NI223N3
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
      exact NI251N2
  β := ![I199N2, I211N2, I223N1, I223N2, I223N3, I229N1, I229N2, I239N1, I239N2, I241N1, I241N2, I251N1, I251N2]
  Il := ![[I199N2], [I211N2], [I223N1, I223N2, I223N3], [], [I229N1, I229N2], [], [I239N1, I239N2], [I241N1, I241N2], [I251N1, I251N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
