
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![99, -259, 183, 102, -222]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![99, -259, 183, 102, -222]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![13, 167, 18, 134, 1]] where
  M :=![![![99, -259, 183, 102, -222], ![-204, 1191, -1951, 423, 168], ![-846, -30, 3972, -3133, 2874], ![6266, -18608, 16437, 4490, -13050], ![1116, 4570, -16227, 8549, -5777]]]
  hmulB := by decide  
  f := ![![![1823, -4251, 721, -166, 540]], ![![332, -669, 111, -27, 84]], ![![54, -58, 6, -3, 6]], ![![6, 24, -13, 0, -6]], ![![409, -834, 133, -34, 103]]]
  g := ![![![15, 185, 21, 150, -222], ![-12, -135, -25, -111, 168], ![-192, -2412, -240, -1951, 2874], ![884, 10858, 1263, 8810, -13050], ![383, 4871, 441, 3933, -5777]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [142, 128, 51, 178, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 141, 7, 43], [110, 126, 15, 158], [89, 130, 177, 197], [0, 1]]
 g := ![![[147, 8, 122, 123], [169, 74, 61, 90], [16, 131, 127, 169], [58, 30, 43], [84, 90, 79], [191, 21, 1], []], ![[182, 181, 159, 142, 78, 139], [142, 183, 38, 111, 69, 125], [39, 173, 32, 147, 95, 23], [158, 135, 72], [57, 128, 123], [198, 53, 94], [106, 172, 130, 64, 61, 106]], ![[84, 38, 113, 51, 157, 51], [96, 25, 14, 36, 120, 124], [58, 172, 26, 144, 39, 169], [13, 192, 79], [168, 64, 28], [139, 193, 169], [104, 74, 18, 63, 11, 132]], ![[82, 57, 1, 37, 84, 87], [26, 42, 94, 110, 140, 186], [153, 77, 51, 25, 88, 190], [7, 100, 155], [74, 184, 46], [159, 133, 20], [83, 154, 12, 141, 165, 191]]]
 h' := ![![[21, 141, 7, 43], [81, 22, 40, 116], [116, 34, 165, 182], [171, 189, 101, 186], [192, 19, 35, 178], [141, 32, 165, 26], [0, 0, 0, 1], [0, 1]], ![[110, 126, 15, 158], [2, 19, 186, 164], [26, 156, 155, 143], [131, 162, 70, 187], [105, 14, 146, 120], [144, 65, 195, 83], [179, 97, 191, 33], [21, 141, 7, 43]], ![[89, 130, 177, 197], [90, 137, 101, 16], [97, 194, 86, 180], [170, 124, 124, 194], [184, 146, 55, 173], [89, 43, 93, 25], [46, 44, 24, 13], [110, 126, 15, 158]], ![[0, 1], [169, 21, 71, 102], [187, 14, 191, 92], [11, 122, 103, 30], [72, 20, 162, 126], [86, 59, 144, 65], [66, 58, 183, 152], [89, 130, 177, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [153, 17, 53], []]
 b := ![[], [], [101, 114, 186, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 4
  hpos := by decide
  P := [142, 128, 51, 178, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-898928366, 3451427268, -4265388494, 141024504, 1530412164]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-104493902, -1266971880, -159863354, -1029820128, 1530412164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1823, -4251, 721, -166, 540]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![1823, -4251, 721, -166, 540]] 
 ![![199, 0, 0, 0, 0], ![189, 1, 0, 0, 0], ![99, 0, 1, 0, 0], ![194, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![1823, -4251, 721, -166, 540], ![332, -669, 111, -27, 84], ![54, -58, 6, -3, 6], ![6, 24, -13, 0, -6], ![472, -1152, 191, -45, 145]]]
  hmulB := by decide  
  f := ![![![99, -259, 183, 102, -222]], ![![93, -240, 164, 99, -210]], ![![45, -129, 111, 35, -96]], ![![128, -346, 261, 122, -282]], ![![27, -33, -42, 65, -77]]]
  g := ![![![3733, -4251, 721, -166, 540], ![590, -669, 111, -27, 84], ![54, -58, 6, -3, 6], ![-15, 24, -13, 0, -6], ![1014, -1152, 191, -45, 145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![99, -259, 183, 102, -222]] ![![1823, -4251, 721, -166, 540]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC199 : ContainsPrimesAboveP 199 ![I199N0, I199N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI199N0
    exact isPrimeI199N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 199 (by decide) (𝕀 ⊙ MulI199N0)
instance hp211 : Fact (Nat.Prime 211) := {out := by norm_num}

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, 116, 265, -141, 68]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-49, 116, 265, -141, 68]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![21, 101, 7, 181, 1]] where
  M :=![![![-49, 116, 265, -141, 68], ![282, -603, 305, 411, -710], ![-822, 3944, -5760, 903, 1046], ![-1806, -3200, 16067, -9658, 7510], ![2918, -11326, 14125, -461, -4915]]]
  hmulB := by decide  
  f := ![![![81273, -207852, 35541, -7975, 26528]], ![![15950, -40789, 6975, -1565, 5206]], ![![3130, -8004, 1370, -307, 1022]], ![![614, -1572, 273, -60, 202]], ![![16451, -42073, 7198, -1614, 5371]]]
  g := ![![![-7, -32, -1, -59, 68], ![72, 337, 25, 611, -710], ![-108, -482, -62, -893, 1046], ![-756, -3610, -173, -6488, 7510], ![503, 2299, 230, 4214, -4915]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 4 2 7 [159, 101, 17, 153, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [162, 72, 57, 186], [74, 200, 151, 52], [33, 149, 3, 184], [0, 1]]
 g := ![![[206, 182, 159, 4], [103, 129, 50, 121], [15, 75, 185], [197, 74, 6], [103, 207, 39, 43], [182, 58, 1], []], ![[181, 41, 171, 139, 111, 202], [117, 50, 23, 107, 116, 33], [152, 142, 169], [68, 104, 65], [174, 165, 143, 162, 122, 127], [205, 172, 183], [0, 159, 75, 90, 104, 200]], ![[38, 126, 183, 35, 88, 82], [189, 21, 100, 186, 17, 46], [186, 49, 19], [209, 49, 66], [191, 104, 131, 201, 194, 95], [3, 98, 169], [169, 197, 103, 23, 171, 82]], ![[161, 109, 97, 105, 16, 136], [17, 102, 29, 160, 93, 46], [154, 140, 13], [12, 183, 9], [162, 140, 9, 75, 69, 24], [66, 138, 193], [38, 109, 200, 140, 127, 151]]]
 h' := ![![[162, 72, 57, 186], [81, 31, 140, 2], [75, 54, 182, 11], [136, 197, 133, 94], [81, 56, 75, 46], [180, 37, 173, 185], [0, 0, 0, 1], [0, 1]], ![[74, 200, 151, 52], [131, 23, 118, 85], [153, 83, 5, 92], [181, 10, 193, 198], [134, 48, 49, 109], [13, 127, 127, 73], [89, 17, 128, 129], [162, 72, 57, 186]], ![[33, 149, 3, 184], [58, 56, 171, 52], [66, 203, 94, 3], [10, 73, 10, 190], [89, 209, 38, 53], [1, 168, 2, 15], [30, 46, 65, 13], [74, 200, 151, 52]], ![[0, 1], [158, 101, 204, 72], [191, 82, 141, 105], [74, 142, 86, 151], [100, 109, 49, 3], [114, 90, 120, 149], [144, 148, 18, 68], [33, 149, 3, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [153, 156, 152], []]
 b := ![[], [], [156, 43, 92, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 4
  hpos := by decide
  P := [159, 101, 17, 153, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-656418225, 3480270888, -5458244135, 1044515093, 698144664]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-72594579, -317688816, -49029653, -593932081, 698144664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 1982119441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81273, 207852, -35541, 7975, -26528]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-81273, 207852, -35541, 7975, -26528]] 
 ![![211, 0, 0, 0, 0], ![178, 1, 0, 0, 0], ![177, 0, 1, 0, 0], ![144, 0, 0, 1, 0], ![94, 0, 0, 0, 1]] where
  M :=![![![-81273, 207852, -35541, 7975, -26528], ![-15950, 40789, -6975, 1565, -5206], ![-3130, 8004, -1370, 307, -1022], ![-614, 1572, -273, 60, -202], ![-20434, 52262, -8939, 2005, -6671]]]
  hmulB := by decide  
  f := ![![![49, -116, -265, 141, -68]], ![![40, -95, -225, 117, -54]], ![![45, -116, -195, 114, -62]], ![![42, -64, -257, 142, -82]], ![![8, 2, -185, 65, -7]]]
  g := ![![![-139540, 207852, -35541, 7975, -26528], ![-27383, 40789, -6975, 1565, -5206], ![-5372, 8004, -1370, 307, -1022], ![-1051, 1572, -273, 60, -202], ![-35083, 52262, -8939, 2005, -6671]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-49, 116, 265, -141, 68]] ![![-81273, 207852, -35541, 7975, -26528]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![-211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC211 : ContainsPrimesAboveP 211 ![I211N0, I211N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI211N0
    exact isPrimeI211N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 211 (by decide) (𝕀 ⊙ MulI211N0)
instance hp223 : Fact (Nat.Prime 223) := {out := by norm_num}

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1105, 4723, -833, 168, -614]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-1105, 4723, -833, 168, -614]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![128, 162, 1, 0, 0], ![3, 198, 0, 1, 0], ![24, 29, 0, 0, 1]] where
  M :=![![![-1105, 4723, -833, 168, -614], ![-336, 1687, -299, 59, -220], ![-118, 662, -116, 23, -86], ![-46, 272, -43, 10, -34], ![-216, 790, -135, 29, -101]]]
  hmulB := by decide  
  f := ![![![-5, 23, -31, 8, 4]], ![![-16, -5, 83, -55, 56]], ![![-14, 8, 44, -35, 42]], ![![-15, 1, 64, -46, 50]], ![![-4, 5, 6, -8, 11]]]
  g := ![![![537, 557, -833, 168, -614], ![193, 201, -299, 59, -220], ![75, 78, -116, 23, -86], ![28, 28, -43, 10, -34], ![87, 89, -135, 29, -101]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [145, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [211, 222], [0, 1]]
 g := ![![[17, 65], [131, 202], [21, 89], [115, 196], [213, 201], [1], [211, 1]], ![[129, 158], [160, 21], [68, 134], [216, 27], [31, 22], [1], [199, 222]]]
 h' := ![![[211, 222], [183, 43], [77, 47], [50, 138], [112, 14], [7, 76], [179, 222], [0, 1]], ![[0, 1], [113, 180], [182, 176], [178, 85], [167, 209], [210, 147], [191, 1], [211, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [178]]
 b := ![[], [88, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [145, 12, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![132, -140, 310, -88, 110]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-188, -162, 310, -88, 110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-61011, 389384, -69734, 13312, -51084]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-61011, 389384, -69734, 13312, -51084]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![219, 115, 1, 0, 0], ![14, 151, 0, 1, 0], ![107, 149, 0, 0, 1]] where
  M :=![![![-61011, 389384, -69734, 13312, -51084], ![-26624, 169949, -30436, 5810, -22296], ![-11620, 74180, -13285, 2536, -9732], ![-5072, 32380, -5800, 1107, -4248], ![-7712, 49204, -8812, 1682, -6455]]]
  hmulB := by decide  
  f := ![![![-13, 64, -58, 8, -36]], ![![-16, 147, -236, -2, -24]], ![![-21, 139, -179, 6, -48]], ![![-10, 103, -168, 1, -24]], ![![-17, 133, -194, 4, -35]]]
  g := ![![![91885, 62826, -69734, 13312, -51084], ![40104, 27421, -30436, 5810, -22296], ![17505, 11969, -13285, 2536, -9732], ![7642, 5225, -5800, 1107, -4248], ![11611, 7939, -8812, 1682, -6455]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P1 : CertificateIrreducibleZModOfList' 223 2 2 7 [46, 180, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 222], [0, 1]]
 g := ![![[33, 100], [17, 74], [77, 30], [154, 124], [59, 188], [138], [43, 1]], ![[96, 123], [77, 149], [29, 193], [134, 99], [115, 35], [138], [86, 222]]]
 h' := ![![[43, 222], [110, 10], [26, 175], [52, 132], [185, 74], [68, 123], [29, 19], [0, 1]], ![[0, 1], [94, 213], [192, 48], [153, 91], [22, 149], [5, 100], [177, 204], [43, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [24, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N1 : CertifiedPrimeIdeal' SI223N1 223 where
  n := 2
  hpos := by decide
  P := [46, 180, 1]
  hirr := P223P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3664, -27869, 56891, -9948, 2035]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-56206, -24087, 56891, -9948, 2035]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N1 B_one_repr
lemma NI223N1 : Nat.card (O ⧸ I223N1) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, -176, 782, 54, 268]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-107, -176, 782, 54, 268]] 
 ![![223, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![206, 0, 1, 0, 0], ![197, 0, 0, 1, 0], ![118, 0, 0, 0, 1]] where
  M :=![![![-107, -176, 782, 54, 268], ![-108, -1071, 2398, 138, 860], ![-276, -3272, 7083, 402, 2548], ![-804, -9664, 20866, 1183, 7508], ![-524, -6032, 13118, 746, 4717]]]
  hmulB := by decide  
  f := ![![![-189, 768, -570, -26, 220]], ![![-143, 577, -420, -24, 168]], ![![-166, 696, -533, -6, 180]], ![![-203, 816, -672, -19, 256]], ![![-118, 416, -242, -70, 173]]]
  g := ![![![-779, -176, 782, 54, 268], ![-1981, -1071, 2398, 138, 860], ![-5768, -3272, 7083, 402, 2548], ![-16973, -9664, 20866, 1183, 7508], ![-10704, -6032, 13118, 746, 4717]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-1105, 4723, -833, 168, -614]] ![![-61011, 389384, -69734, 13312, -51084]]
  ![![-44765465, 285836451, -51190585, 9771610, -37499726]] where
 M := ![![![-44765465, 285836451, -51190585, 9771610, -37499726]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-44765465, 285836451, -51190585, 9771610, -37499726]] ![![-107, -176, 782, 54, 268]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-158348509, 1008985131, -180689095, 34498992, -132367002]]]
 hmul := by decide  
 g := ![![![![-710083, 4524597, -810265, 154704, -593574]]]]
 hle2 := by decide  


def PBC223 : ContainsPrimesAboveP 223 ![I223N0, I223N1, I223N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI223N0
    exact isPrimeI223N1
    exact isPrimeI223N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 223 (by decide) (𝕀 ⊙ MulI223N0 ⊙ MulI223N1)
instance hp227 : Fact (Nat.Prime 227) := {out := by norm_num}

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -22, 50, -18, 6]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![1, -22, 50, -18, 6]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![205, 114, 1, 0, 0], ![11, 148, 0, 1, 0], ![103, 20, 0, 0, 1]] where
  M :=![![![1, -22, 50, -18, 6], ![36, -59, -22, 74, -96], ![-148, 568, -701, 22, 252], ![-44, -1112, 2902, -1249, 636], ![464, -1490, 1486, 230, -917]]]
  hmulB := by decide  
  f := ![![![-20485, 55566, -9542, 2110, -7110]], ![![-4220, 12175, -2094, 458, -1560]], ![![-20623, 56308, -9671, 2136, -7206]], ![![-3745, 10634, -1828, 401, -1362]], ![![-9689, 26344, -4524, 1000, -3371]]]
  g := ![![![-47, -14, 50, -18, 6], ![60, -29, -22, 74, -96], ![517, 318, -701, 22, 252], ![-2849, -704, 2902, -1249, 636], ![-935, -822, 1486, 230, -917]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [174, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 226], [0, 1]]
 g := ![![[139, 203], [42, 120], [166], [71], [181], [126, 49], [103, 1]], ![[164, 24], [144, 107], [166], [71], [181], [179, 178], [206, 226]]]
 h' := ![![[103, 226], [183, 138], [216, 44], [147, 47], [4, 170], [95, 33], [11, 220], [0, 1]], ![[0, 1], [96, 89], [208, 183], [221, 180], [35, 57], [89, 194], [198, 7], [103, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [221]]
 b := ![[], [41, 224]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [174, 124, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9094, -46751, 70673, -9868, -9731]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58890, -28407, 70673, -9868, -9731]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 254, -238, -6, -96]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-53, 254, -238, -6, -96]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![14, 169, 1, 0, 0], ![131, 55, 0, 1, 0], ![135, 185, 0, 0, 1]] where
  M :=![![![-53, 254, -238, -6, -96], ![12, 319, -628, -34, -228], ![68, 856, -1835, -104, -660], ![208, 2500, -5396, -307, -1944], ![116, 1612, -3404, -190, -1229]]]
  hmulB := by decide  
  f := ![![![1481, -9498, 1702, -326, 1248]], ![![652, -4163, 756, -142, 540]], ![![578, -3693, 669, -126, 480]], ![![1013, -6493, 1166, -223, 852]], ![![1413, -9047, 1630, -310, 1183]]]
  g := ![![![75, 258, -238, -6, -96], ![194, 663, -628, -34, -228], ![566, 1933, -1835, -104, -660], ![1667, 5687, -5396, -307, -1944], ![1051, 3589, -3404, -190, -1229]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [215, 112, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 226], [0, 1]]
 g := ![![[142, 155], [188, 62], [1], [160], [16], [16, 47], [115, 1]], ![[34, 72], [54, 165], [1], [160], [16], [200, 180], [3, 226]]]
 h' := ![![[115, 226], [213, 137], [143, 17], [178, 1], [55, 198], [192, 4], [18, 71], [0, 1]], ![[0, 1], [78, 90], [55, 210], [66, 226], [125, 29], [198, 223], [11, 156], [115, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [122, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [215, 112, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9611, -28132, 24828, 6592, -19428]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6261, -4372, 24828, 6592, -19428]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8617, -52952, 9472, -1816, 6942]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![8617, -52952, 9472, -1816, 6942]] 
 ![![227, 0, 0, 0, 0], ![171, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![8617, -52952, 9472, -1816, 6942], ![3632, -22783, 4078, -780, 2988], ![1560, -9880, 1769, -338, 1296], ![676, -4300, 770, -147, 564], ![1156, -6862, 1226, -236, 899]]]
  hmulB := by decide  
  f := ![![![35, 708, -1468, -72, -462]], ![![27, 541, -1122, -56, -354]], ![![10, 152, -323, -14, -108]], ![![14, 348, -714, -31, -216]], ![![17, 390, -798, -48, -247]]]
  g := ![![![35497, -52952, 9472, -1816, 6942], ![15271, -22783, 4078, -780, 2988], ![6622, -9880, 1769, -338, 1296], ![2882, -4300, 770, -147, 564], ![4601, -6862, 1226, -236, 899]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![1, -22, 50, -18, 6]] ![![-53, 254, -238, -6, -96]]
  ![![35, 708, -1468, -72, -462]] where
 M := ![![![35, 708, -1468, -72, -462]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![35, 708, -1468, -72, -462]] ![![8617, -52952, 9472, -1816, 6942]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] where
  M :=![![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [59, 23, 161, 133, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [115, 155, 89, 98, 20], [47, 149, 11, 196, 57], [136, 83, 216, 31, 114], [157, 70, 142, 133, 38], [0, 1]]
 g := ![![[196, 102, 35, 130, 224], [225, 60, 84, 58], [107, 53, 85, 136, 129], [148, 70, 206, 17], [197, 115, 67, 204], [105, 226, 1], []], ![[208, 194, 41, 104, 228, 38, 2, 228], [48, 227, 16, 180], [201, 92, 93, 44, 94, 18, 144, 58], [180, 11, 109, 130], [214, 184, 119, 125], [184, 128, 161, 187, 61, 134, 150, 37], [50, 218, 81, 170, 8, 50, 168, 214]], ![[133, 35, 48, 61, 156, 157, 226, 153], [149, 120, 163, 224], [192, 93, 173, 136, 12, 45, 141, 181], [8, 213, 140, 184], [224, 192, 121, 129], [16, 176, 44, 161, 207, 121, 36, 202], [11, 64, 9, 167, 162, 222, 69, 161]], ![[40, 166, 152, 149, 93, 178, 2, 8], [101, 103, 53, 220], [114, 101, 93, 151, 130, 1, 59, 164], [43, 9, 134, 70], [9, 96, 159, 55], [226, 180, 171, 95, 167, 38, 27, 65], [210, 147, 175, 125, 225, 212, 224, 143]], ![[36, 115, 3, 50, 6, 67, 76, 223], [73, 170, 107, 68], [103, 124, 81, 83, 197, 105, 83, 164], [187, 218, 112, 172], [95, 95, 89, 43], [100, 14, 140, 3, 147, 129, 162, 35], [72, 56, 112, 100, 201, 195, 27, 141]]]
 h' := ![![[115, 155, 89, 98, 20], [190, 213, 156, 82, 192], [99, 170, 64, 77, 79], [124, 57, 98, 53, 154], [200, 31, 34, 224, 43], [217, 52, 51, 6, 152], [0, 0, 0, 1], [0, 1]], ![[47, 149, 11, 196, 57], [140, 154, 5, 184, 164], [192, 96, 11, 167, 62], [168, 215, 158, 95, 74], [5, 134, 92, 148, 151], [223, 48, 173, 154, 128], [113, 16, 113, 175, 178], [115, 155, 89, 98, 20]], ![[136, 83, 216, 31, 114], [144, 126, 100, 8, 126], [2, 82, 222, 2, 37], [154, 148, 31, 143, 110], [54, 147, 93, 32, 111], [149, 158, 104, 153, 75], [124, 68, 105, 52, 32], [47, 149, 11, 196, 57]], ![[157, 70, 142, 133, 38], [169, 74, 10, 109, 199], [113, 76, 13, 82, 137], [100, 196, 106, 118, 78], [205, 136, 213, 113, 38], [7, 151, 103, 123, 46], [96, 93, 88, 102, 102], [136, 83, 216, 31, 114]], ![[0, 1], [139, 120, 187, 75, 6], [211, 34, 148, 130, 143], [203, 71, 65, 49, 42], [106, 10, 26, 170, 115], [131, 49, 27, 22, 57], [125, 52, 152, 128, 146], [157, 70, 142, 133, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [208, 19, 45, 186], [], [], []]
 b := ![[], [190, 202, 35, 20, 151], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 5
  hpos := by decide
  P := [59, 23, 161, 133, 3, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18499457919473, 44132924572560, -23322056285034, -21619097592445, 43352180112365]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-80783659037, 192720194640, -101843040546, -94406539705, 189310830185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 629763392149 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def PBC229 : ContainsPrimesAboveP 229 ![I229N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![229, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 229 (by decide) 𝕀

instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20789, -53167, 9091, -2040, 6786]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![20789, -53167, 9091, -2040, 6786]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![15, 212, 104, 1, 0], ![133, 88, 93, 0, 1]] where
  M :=![![![20789, -53167, 9091, -2040, 6786], ![4080, -10435, 1787, -401, 1332], ![802, -2050, 350, -75, 258], ![150, -380, 47, -16, 66], ![5224, -13370, 2303, -523, 1717]]]
  hmulB := by decide  
  f := ![![![-145, 923, -161, 32, -120]], ![![-64, 399, -61, 15, -48]], ![![-30, 158, 12, 5, -6]], ![![-81, 493, -60, 18, -54]], ![![-119, 741, -110, 26, -89]]]
  g := ![![![-3653, -935, -1759, -2040, 6786], ![-717, -183, -345, -401, 1332], ![-139, -38, -68, -75, 258], ![-36, -12, -19, -16, 66], ![-924, -230, -442, -523, 1717]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [198, 154, 170, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 94, 155], [30, 138, 78], [0, 1]]
 g := ![![[194, 172, 89], [42, 7], [6, 85], [100, 120, 129], [193, 55], [29, 206, 8], [1]], ![[220, 12, 138, 118], [22, 203], [16, 226], [181, 199, 224, 188], [156, 112], [14, 180, 58, 68], [5, 84, 29, 69]], ![[87, 35, 3, 212], [104, 178], [135, 157], [88, 57, 30, 186], [26, 50], [172, 190, 15, 186], [131, 105, 126, 164]]]
 h' := ![![[33, 94, 155], [76, 10, 136], [2, 102, 70], [5, 108, 205], [130, 93, 96], [83, 8, 145], [35, 79, 63], [0, 1]], ![[30, 138, 78], [192, 202, 47], [222, 128, 73], [214, 189, 61], [156, 162, 169], [88, 229, 47], [230, 77, 202], [33, 94, 155]], ![[0, 1], [99, 21, 50], [120, 3, 90], [88, 169, 200], [230, 211, 201], [187, 229, 41], [130, 77, 201], [30, 138, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 54], []]
 b := ![[], [153, 22, 162], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [198, 154, 170, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41850, 10541, -217065, 166126, -145543]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![72563, -96139, -16990, 166126, -145543]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-145, 923, -161, 32, -120]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-145, 923, -161, 32, -120]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![124, 129, 1, 0, 0], ![81, 26, 0, 1, 0], ![204, 98, 0, 0, 1]] where
  M :=![![![-145, 923, -161, 32, -120], ![-64, 399, -61, 15, -48], ![-30, 158, 12, 5, -6], ![-10, 4, 119, 14, 18], ![-20, 88, 35, 17, 5]]]
  hmulB := by decide  
  f := ![![![20789, -53167, 9091, -2040, 6786]], ![![4080, -10435, 1787, -401, 1332]], ![![13326, -34081, 5829, -1308, 4350]], ![![7683, -19649, 3360, -754, 2508]], ![![19940, -50996, 8721, -1957, 6509]]]
  g := ![![![179, 140, -161, 32, -120], ![69, 54, -61, 15, -48], ![-3, -4, 12, 5, -6], ![-84, -75, 119, 14, 18], ![-29, -23, 35, 17, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [109, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [177, 232], [0, 1]]
 g := ![![[210, 62], [141], [120], [228, 203], [8], [58, 4], [177, 1]], ![[0, 171], [141], [120], [44, 30], [8], [67, 229], [121, 232]]]
 h' := ![![[177, 232], [209, 166], [151, 181], [79, 54], [89, 73], [202, 63], [46, 231], [0, 1]], ![[0, 1], [0, 67], [34, 52], [84, 179], [195, 160], [169, 170], [158, 2], [177, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [20, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [109, 56, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10319, -54093, 81954, -9190, -10317]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-31343, -40241, 81954, -9190, -10317]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![20789, -53167, 9091, -2040, 6786]] ![![-145, 923, -161, 32, -120]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![233, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-911, 5749, -894, 155, -732]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-911, 5749, -894, 155, -732]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![236, 31, 203, 149, 1]] where
  M :=![![![-911, 5749, -894, 155, -732], ![-310, 2327, -374, 260, -534], ![-520, 2346, -1699, 174, 492], ![-348, -2140, 7296, -3031, 2028], ![954, -3166, 4278, 418, -1991]]]
  hmulB := by decide  
  f := ![![![977301, -2499535, 427400, -95903, 319014]], ![![191806, -490561, 83882, -18822, 62610]], ![![37644, -96278, 16463, -3694, 12288]], ![![7388, -18896, 3232, -725, 2412]], ![![1027520, -2627975, 449363, -100831, 335407]]]
  g := ![![![719, 119, 618, 457, -732], ![526, 79, 452, 334, -534], ![-488, -54, -425, -306, 492], ![-2004, -272, -1692, -1277, 2028], ![1970, 245, 1709, 1243, -1991]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 4 2 7 [92, 106, 202, 166, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 22, 157, 44], [82, 4, 124, 237], [175, 212, 197, 197], [0, 1]]
 g := ![![[2, 177, 44, 220], [168, 45, 110, 91], [133, 53, 10, 198], [93, 126, 136, 64], [219, 41, 32], [202, 108, 73, 1], []], ![[36, 155, 24, 0, 204, 169], [15, 180, 201, 46, 179, 48], [38, 184, 138, 222, 234, 5], [233, 89, 31, 155, 236, 155], [120, 90, 163], [231, 155, 166, 56, 116, 24], [20, 91, 115, 42, 201, 100]], ![[59, 87, 61, 67, 26, 237], [147, 225, 26, 93, 112, 154], [13, 197, 99, 121, 103, 94], [155, 187, 187, 190, 48, 78], [147, 189, 165], [188, 38, 224, 204, 194, 59], [110, 190, 98, 17, 187, 231]], ![[11, 137, 229, 68, 101, 174], [189, 96, 226, 109, 32, 109], [225, 44, 165, 220, 77, 121], [101, 121, 204, 33, 18, 180], [207, 69, 180], [53, 111, 87, 119, 65, 110], [148, 19, 15, 220, 152, 2]]]
 h' := ![![[55, 22, 157, 44], [79, 98, 26, 170], [192, 60, 147, 42], [48, 108, 237, 26], [185, 38, 75, 8], [58, 200, 65, 157], [0, 0, 0, 1], [0, 1]], ![[82, 4, 124, 237], [40, 196, 83, 105], [42, 101, 124, 142], [80, 39, 68, 7], [34, 238, 22, 18], [115, 163, 106, 101], [103, 109, 3, 98], [55, 22, 157, 44]], ![[175, 212, 197, 197], [95, 77, 12, 238], [226, 117, 84, 174], [183, 97, 67, 131], [201, 27, 103, 205], [126, 185, 162, 167], [152, 163, 75, 125], [82, 4, 124, 237]], ![[0, 1], [56, 107, 118, 204], [166, 200, 123, 120], [5, 234, 106, 75], [125, 175, 39, 8], [232, 169, 145, 53], [46, 206, 161, 15], [175, 212, 197, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [167, 110, 178], []]
 b := ![[], [], [142, 151, 32, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 4
  hpos := by decide
  P := [92, 106, 202, 166, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2817814204, 10583646105, -12857061901, 336631094, 4905501815]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4855716496, -591995440, -4220393014, -3056833219, 4905501815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 3262808641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-977301, 2499535, -427400, 95903, -319014]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-977301, 2499535, -427400, 95903, -319014]] 
 ![![239, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![224, 0, 1, 0, 0], ![183, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![-977301, 2499535, -427400, 95903, -319014], ![-191806, 490561, -83882, 18822, -62610], ![-37644, 96278, -16463, 3694, -12288], ![-7388, 18896, -3232, 725, -2412], ![-245714, 628436, -107458, 24112, -80207]]]
  hmulB := by decide  
  f := ![![![911, -5749, 894, -155, 732]], ![![230, -1453, 226, -40, 186]], ![![856, -5398, 845, -146, 684]], ![![699, -4393, 654, -106, 552]], ![![644, -4076, 618, -112, 529]]]
  g := ![![![-77530, 2499535, -427400, 95903, -319014], ![-15216, 490561, -83882, 18822, -62610], ![-2986, 96278, -16463, 3694, -12288], ![-585, 18896, -3232, 725, -2412], ![-19492, 628436, -107458, 24112, -80207]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-911, 5749, -894, 155, -732]] ![![-977301, 2499535, -427400, 95903, -319014]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![-239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [9, 163, 49, 120, 31, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 73, 61, 131, 156], [96, 184, 58, 216, 5], [26, 65, 138, 39, 29], [8, 159, 225, 96, 51], [0, 1]]
 g := ![![[125, 138, 107, 163, 29], [158, 139, 110, 161], [192, 176, 193, 2], [117, 20, 187, 223], [230, 229, 191, 221, 169], [118, 210, 1], []], ![[71, 226, 192, 234, 19, 164, 126, 19], [202, 225, 26, 216], [225, 81, 194, 100], [38, 74, 109, 61], [49, 120, 72, 40, 43, 187, 32, 11], [103, 139, 30, 87, 58, 238, 61, 220], [9, 22, 46, 208, 185, 36, 43, 184]], ![[181, 48, 201, 98, 164, 30, 33, 12], [240, 179, 91, 150], [112, 143, 143, 15], [238, 203, 136, 121], [139, 71, 188, 125, 177, 212, 5, 72], [9, 54, 9, 171, 50, 105, 57, 180], [94, 219, 205, 229, 40, 81, 34, 125]], ![[219, 162, 205, 18, 88, 209, 161, 82], [7, 188, 223, 47], [5, 34, 218, 5], [169, 183, 99, 135], [35, 126, 78, 199, 200, 44, 212, 237], [6, 86, 127, 95, 12, 196, 238, 20], [239, 22, 192, 202, 136, 98, 27, 48]], ![[25, 207, 167, 229, 236, 105, 217, 171], [193, 146, 188, 5], [77, 132, 112, 133], [153, 232, 161, 6], [166, 138, 207, 65, 239, 80, 140, 22], [236, 68, 194, 163, 44, 109, 32, 215], [21, 105, 119, 86, 123, 124, 62, 101]]]
 h' := ![![[80, 73, 61, 131, 156], [0, 109, 5, 197, 92], [82, 133, 135, 156, 99], [72, 87, 66, 164, 219], [99, 178, 218, 231, 127], [143, 84, 226, 210, 13], [0, 0, 0, 1], [0, 1]], ![[96, 184, 58, 216, 5], [98, 227, 63, 174, 166], [62, 101, 45, 171, 162], [20, 64, 48, 4, 231], [11, 8, 140, 139, 28], [191, 39, 210, 63, 123], [35, 207, 51, 218, 208], [80, 73, 61, 131, 156]], ![[26, 65, 138, 39, 29], [70, 37, 9, 117, 90], [28, 5, 74, 144, 106], [109, 156, 166, 222, 225], [75, 116, 1, 100, 11], [78, 185, 76, 113, 20], [143, 22, 147, 121, 6], [96, 184, 58, 216, 5]], ![[8, 159, 225, 96, 51], [158, 195, 188, 74, 213], [71, 96, 33, 194, 218], [184, 76, 12, 10, 103], [66, 240, 186, 135, 48], [213, 26, 148, 159, 190], [1, 121, 11, 32, 3], [26, 65, 138, 39, 29]], ![[0, 1], [203, 155, 217, 161, 162], [112, 147, 195, 58, 138], [75, 99, 190, 82, 186], [27, 181, 178, 118, 27], [94, 148, 63, 178, 136], [82, 132, 32, 110, 24], [8, 159, 225, 96, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62, 185, 11, 176], [], [], []]
 b := ![[], [225, 45, 146, 103, 141], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [9, 163, 49, 120, 31, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-256714666967, 702388208454, -541273124816, -213592482260, 562112669074]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1065206087, 2914473894, -2245946576, -886275860, 2332417714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 812990017201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def PBC241 : ContainsPrimesAboveP 241 ![I241N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI241N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![241, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 241 (by decide) 𝕀

instance hp251 : Fact (Nat.Prime 251) := {out := by norm_num}

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4409, 42716, -98975, -5763, -35386]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![4409, 42716, -98975, -5763, -35386]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![179, 210, 34, 2, 1]] where
  M :=![![![4409, 42716, -98975, -5763, -35386], ![11526, 134427, -293047, -16677, -105350], ![33354, 399572, -863754, -48993, -310762], ![97986, 1178416, -2544265, -144244, -915482], ![61694, 741020, -1600463, -90749, -575863]]]
  hmulB := by decide  
  f := ![![![15, -48, 33, -5, -2]], ![![10, 13, -81, 47, -34]], ![![-94, 240, -152, -107, 214]], ![![214, -1164, 1845, -366, -214]], ![![9, -2, -50, 20, -5]]]
  g := ![![![25253, 29776, 4399, 259, -35386], ![75176, 88677, 13103, 773, -105350], ![221752, 261592, 38654, 2281, -310762], ![653264, 770636, 113873, 6720, -915482], ![410921, 484750, 71629, 4227, -575863]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 4 2 7 [244, 33, 83, 108, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [208, 232, 145, 222], [176, 175, 67, 112], [10, 94, 39, 168], [0, 1]]
 g := ![![[209, 105, 106, 217], [232, 157, 131, 131], [41, 120, 75], [125, 88, 162, 152], [205, 32, 47, 164], [131, 35, 143, 1], []], ![[9, 123, 215, 113, 3, 83], [130, 5, 211, 188, 154, 65], [70, 126, 79], [163, 108, 115, 85, 88, 94], [192, 125, 146, 96, 132, 7], [100, 87, 191, 244, 44, 86], [181, 97, 29, 134, 146, 209]], ![[157, 227, 161, 156, 244, 173], [120, 199, 236, 143, 80, 49], [22, 61, 73], [180, 13, 250, 72, 196, 152], [243, 41, 93, 151, 102, 105], [79, 160, 100, 154, 182, 3], [31, 146, 250, 211, 86, 81]], ![[52, 230, 245, 229, 165, 129], [86, 207, 222, 62, 16, 151], [145, 249, 197], [66, 174, 167, 55, 64, 107], [133, 140, 5, 213, 238, 170], [204, 26, 82, 237, 101, 248], [22, 75, 215, 81, 20, 242]]]
 h' := ![![[208, 232, 145, 222], [118, 242, 149, 79], [111, 58, 50, 70], [122, 26, 9, 122], [180, 24, 74, 34], [164, 189, 17, 72], [0, 0, 0, 1], [0, 1]], ![[176, 175, 67, 112], [21, 216, 9, 58], [3, 54, 155, 103], [212, 232, 1, 62], [158, 103, 157, 98], [174, 47, 120, 128], [72, 4, 28, 147], [208, 232, 145, 222]], ![[10, 94, 39, 168], [134, 131, 157, 204], [233, 194, 6, 136], [189, 245, 107, 233], [114, 21, 187, 200], [146, 115, 190, 53], [22, 109, 80, 114], [176, 175, 67, 112]], ![[0, 1], [243, 164, 187, 161], [230, 196, 40, 193], [138, 250, 134, 85], [161, 103, 84, 170], [26, 151, 175, 249], [150, 138, 143, 240], [10, 94, 39, 168]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 228, 184], []]
 b := ![[], [], [88, 29, 243, 88], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 4
  hpos := by decide
  P := [244, 33, 83, 108, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55367737900, 123297789553, -46518681109, -77502656404, 133429258983]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-95375319107, -111142815127, -18259416281, -1371956870, 133429258983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 3969126001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 48, -33, 5, 2]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-15, 48, -33, 5, 2]] 
 ![![251, 0, 0, 0, 0], ![237, 1, 0, 0, 0], ![55, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![-15, 48, -33, 5, 2], ![-10, -13, 81, -47, 34], ![94, -240, 152, 107, -214], ![-214, 1164, -1845, 366, 214], ![-242, 472, -31, -415, 605]]]
  hmulB := by decide  
  f := ![![![-4409, -42716, 98975, 5763, 35386]], ![![-4209, -40869, 94622, 5508, 33832]], ![![-1099, -10952, 25129, 1458, 8992]], ![![-689, -7588, 16840, 965, 6044]], ![![-1370, -13844, 31613, 1831, 11317]]]
  g := ![![![-39, 48, -33, 5, 2], ![-11, -13, 81, -47, 34], ![241, -240, 152, 107, -214], ![-775, 1164, -1845, 366, 214], ![-566, 472, -31, -415, 605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![4409, 42716, -98975, -5763, -35386]] ![![-15, 48, -33, 5, 2]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![-251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC251 : ContainsPrimesAboveP 251 ![I251N0, I251N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
    exact isPrimeI251N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 251 (by decide) (𝕀 ⊙ MulI251N0)


lemma PB984I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB984I5 : PrimesBelowBoundCertificateInterval O 197 251 984 where
  m := 9
  g := ![2, 2, 3, 3, 1, 2, 2, 1, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB984I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1, I227N2]
    · exact ![I229N0]
    · exact ![I233N0, I233N1]
    · exact ![I239N0, I239N1]
    · exact ![I241N0]
    · exact ![I251N0, I251N1]
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
    · exact ![1568239201, 199]
    · exact ![1982119441, 211]
    · exact ![49729, 49729, 223]
    · exact ![51529, 51529, 227]
    · exact ![629763392149]
    · exact ![12649337, 54289]
    · exact ![3262808641, 239]
    · exact ![812990017201]
    · exact ![3969126001, 251]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI199N0
      exact NI199N1
    · dsimp ; intro j
      fin_cases j
      exact NI211N0
      exact NI211N1
    · dsimp ; intro j
      fin_cases j
      exact NI223N0
      exact NI223N1
      exact NI223N2
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I199N1, I211N1, I223N2, I227N2, I239N1, I251N1]
  Il := ![[I199N1], [I211N1], [I223N2], [I227N2], [], [], [I239N1], [], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
