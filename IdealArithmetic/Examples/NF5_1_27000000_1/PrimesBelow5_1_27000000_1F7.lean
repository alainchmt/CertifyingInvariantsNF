
import IdealArithmetic.Examples.NF5_1_27000000_1.RI5_1_27000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp311 : Fact (Nat.Prime 311) := {out := by norm_num}

def I311N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![93, 57, 190, 227, -210]] i)))

def SI311N0: IdealEqSpanCertificate' Table ![![93, 57, 190, 227, -210]] 
 ![![311, 0, 0, 0, 0], ![0, 311, 0, 0, 0], ![0, 0, 311, 0, 0], ![201, 63, 49, 1, 0], ![48, 210, 18, 0, 1]] where
  M :=![![![93, 57, 190, 227, -210], ![1680, -114, -760, 573, 454], ![-2656, -113, 147, -1787, 346], ![-2224, 533, 2400, 408, -2014], ![5968, -14, -1302, 3200, 201]]]
  hmulB := by decide  
  f := ![![![-413, 205, -82, 69, -62]], ![![496, -428, 148, -109, 138]], ![![-800, 431, -255, 119, -178]], ![![-291, 113, -63, 41, -40]], ![![224, -232, 72, -56, 73]]]
  g := ![![![-114, 96, -23, 227, -210], ![-435, -423, -119, 573, 454], ![1093, 128, 262, -1787, 346], ![40, 1279, 60, 408, -2014], ![-2080, -784, -520, 3200, 201]]]
  hle1 := by decide   
  hle2 := by decide  


def P311P0 : CertificateIrreducibleZModOfList' 311 3 2 8 [262, 15, 251, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 166, 287], [302, 144, 24], [0, 1]]
 g := ![![[122, 179, 146], [59, 90, 42], [29, 172, 144], [36, 75], [169, 258, 140], [114, 131, 150], [60, 1], []], ![[265, 23, 81, 31], [84, 150, 142, 207], [72, 236, 82, 181], [46, 225], [30, 50, 175, 129], [228, 239, 293, 123], [66, 210], [157, 265]], ![[126, 126, 247, 253], [32, 41, 28, 189], [20, 297, 36, 137], [250, 282], [35, 284, 7, 192], [95, 279, 102, 40], [201, 188], [109, 265]]]
 h' := ![![[69, 166, 287], [92, 22, 222], [177, 268, 238], [292, 10, 12], [195, 299, 186], [299, 21, 206], [141, 82, 164], [0, 0, 1], [0, 1]], ![[302, 144, 24], [53, 16, 29], [231, 244, 161], [217, 127, 244], [105, 215, 15], [278, 28, 237], [9, 125, 189], [14, 261, 144], [69, 166, 287]], ![[0, 1], [8, 273, 60], [39, 110, 223], [267, 174, 55], [222, 108, 110], [241, 262, 179], [84, 104, 269], [135, 50, 166], [302, 144, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184, 140], []]
 b := ![[], [18, 93, 265], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI311N0 : CertifiedPrimeIdeal' SI311N0 311 where
  n := 3
  hpos := by decide
  P := [262, 15, 251, 1]
  hirr := P311P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1126156, -578234, -1487861, -477821, 955903]
  a := ![0, 8, 5, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![164903, -550531, 15174, -477821, 955903]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI311N0 : Ideal.IsPrime I311N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI311N0 B_one_repr
lemma NI311N0 : Nat.card (O ⧸ I311N0) = 30080231 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI311N0

def I311N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0, 1, 0]] i)))

def SI311N1: IdealEqSpanCertificate' Table ![![3, 1, 0, 1, 0]] 
 ![![311, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![260, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![3, 1, 0, 1, 0], ![0, 2, 0, -1, 2], ![-8, 1, 5, -1, -2], ![8, -1, 0, 8, -2], ![4, -2, -6, 0, 7]]]
  hmulB := by decide  
  f := ![![![389, -203, 72, -65, 60]], ![![66, -34, 12, -11, 10]], ![![90, -47, 17, -15, 14]], ![![324, -169, 60, -54, 50]], ![![96, -50, 18, -16, 15]]]
  g := ![![![-1, 1, 0, 1, 0], ![0, 2, 0, -1, 2], ![0, 1, 5, -1, -2], ![-6, -1, 0, 8, -2], ![0, -2, -6, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N1 : Nat.card (O ⧸ I311N1) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N1)

lemma isPrimeI311N1 : Ideal.IsPrime I311N1 := prime_ideal_of_norm_prime hp311.out _ NI311N1

def I311N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1175, -706, 302, -206, 238]] i)))

def SI311N2: IdealEqSpanCertificate' Table ![![1175, -706, 302, -206, 238]] 
 ![![311, 0, 0, 0, 0], ![160, 1, 0, 0, 0], ![182, 0, 1, 0, 0], ![288, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![1175, -706, 302, -206, 238], ![-1904, 1183, -524, 334, -412], ![2600, -1548, 699, -446, 540], ![-1208, 730, -300, 215, -240], ![1052, -604, 300, -172, 223]]]
  hmulB := by decide  
  f := ![![![265, -590, -2210, -1662, 2190]], ![![80, -301, -1116, -878, 1116]], ![![226, -340, -1289, -918, 1264]], ![![344, -562, -2124, -1533, 2088]], ![![-49, -286, -1034, -902, 1057]]]
  g := ![![![267, -706, 302, -206, 238], ![-420, 1183, -524, 334, -412], ![550, -1548, 699, -446, 540], ![-288, 730, -300, 215, -240], ![191, -604, 300, -172, 223]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI311N2 : Nat.card (O ⧸ I311N2) = 311 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI311N2)

lemma isPrimeI311N2 : Ideal.IsPrime I311N2 := prime_ideal_of_norm_prime hp311.out _ NI311N2
def MulI311N0 : IdealMulLeCertificate' Table 
  ![![93, 57, 190, 227, -210]] ![![3, 1, 0, 1, 0]]
  ![![-265, 590, 2210, 1662, -2190]] where
 M := ![![![-265, 590, 2210, 1662, -2190]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI311N1 : IdealMulLeCertificate' Table 
  ![![-265, 590, 2210, 1662, -2190]] ![![1175, -706, 302, -206, 238]]
  ![![311, 0, 0, 0, 0]] where
 M := ![![![-311, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC311 : ContainsPrimesAboveP 311 ![I311N0, I311N1, I311N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI311N0
    exact isPrimeI311N1
    exact isPrimeI311N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 311 (by decide) (𝕀 ⊙ MulI311N0 ⊙ MulI311N1)
instance hp313 : Fact (Nat.Prime 313) := {out := by norm_num}

def I313N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22426495, -13570286, 5981893, -3902285, 4677461]] i)))

def SI313N0: IdealEqSpanCertificate' Table ![![22426495, -13570286, 5981893, -3902285, 4677461]] 
 ![![313, 0, 0, 0, 0], ![0, 313, 0, 0, 0], ![0, 0, 313, 0, 0], ![226, 251, 236, 1, 0], ![300, 89, 73, 0, 1]] where
  M :=![![![22426495, -13570286, 5981893, -3902285, 4677461], ![-37419688, 22642672, -9981080, 6511149, -7804570], ![49928124, -30211533, 13317493, -8687659, 10413434], ![-22943892, 13883365, -6119900, 3992314, -4785374], ![20177986, -12209706, 5382140, -3511036, 4208491]]]
  hmulB := by decide  
  f := ![![![-263, 32, 143, -57, -67]], ![![536, 26, 44, 477, -114]], ![![188, -187, -587, -319, 534]], ![![374, -97, -302, 97, 262]], ![![-54, -5, 15, 10, 25]]]
  g := ![![![-1593915, 1755940, 1870500, -3902285, 4677461], ![2659526, -2929869, -3121018, 6511149, -7804570], ![-3548534, 3909250, 4164295, -8687659, 10413434], ![1630688, -1796451, -1913654, 3992314, -4785374], ![-1434106, 1579887, 1682961, -3511036, 4208491]]]
  hle1 := by decide   
  hle2 := by decide  


def P313P0 : CertificateIrreducibleZModOfList' 313 3 2 8 [201, 18, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 94, 182], [221, 218, 131], [0, 1]]
 g := ![![[210, 139, 225], [249, 79], [294, 304], [158, 170, 169], [60, 44, 275], [48], [266, 1], []], ![[231, 119, 289, 178], [241, 33], [107, 205], [177, 275, 207, 253], [100, 200, 205, 201], [223, 125, 211, 260], [276, 261], [133, 259]], ![[170, 43, 179, 266], [292, 58], [240, 25], [249, 15, 174, 188], [52, 305, 191, 221], [9, 297, 53, 53], [118, 72], [184, 259]]]
 h' := ![![[45, 94, 182], [261, 248, 298], [117, 274, 198], [168, 245, 238], [147, 300, 13], [55, 194, 223], [57, 19], [0, 0, 1], [0, 1]], ![[221, 218, 131], [181, 193, 237], [246, 211, 71], [65, 83, 70], [122, 264, 155], [189, 27, 38], [286, 221, 15], [19, 18, 218], [45, 94, 182]], ![[0, 1], [223, 185, 91], [135, 141, 44], [122, 298, 5], [236, 62, 145], [248, 92, 52], [187, 73, 298], [276, 295, 94], [221, 218, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 114], []]
 b := ![[], [238, 105, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI313N0 : CertifiedPrimeIdeal' SI313N0 313 where
  n := 3
  hpos := by decide
  P := [201, 18, 47, 1]
  hirr := P313P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14692121, -2513942, -9803316, 3394300, 7135864]
  a := ![3, -5, -3, -1, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9243383, -4759026, -4254876, 3394300, 7135864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI313N0 : Ideal.IsPrime I313N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI313N0 B_one_repr
lemma NI313N0 : Nat.card (O ⧸ I313N0) = 30664297 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI313N0

def I313N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -5, 2, -1, 2]] i)))

def SI313N1: IdealEqSpanCertificate' Table ![![9, -5, 2, -1, 2]] 
 ![![313, 0, 0, 0, 0], ![195, 1, 0, 0, 0], ![296, 0, 1, 0, 0], ![308, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![9, -5, 2, -1, 2], ![-16, 8, -4, 1, -2], ![16, -11, 7, -3, 2], ![0, 5, -4, 6, -2], ![8, -6, -2, -4, 5]]]
  hmulB := by decide  
  f := ![![![-111, -183, -98, -41, -6]], ![![-69, -115, -62, -26, -4]], ![![-104, -173, -93, -39, -6]], ![![-108, -179, -96, -40, -6]], ![![-11, -21, -12, -5, -1]]]
  g := ![![![2, -5, 2, -1, 2], ![-2, 8, -4, 1, -2], ![3, -11, 7, -3, 2], ![-5, 5, -4, 6, -2], ![9, -6, -2, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N1 : Nat.card (O ⧸ I313N1) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N1)

lemma isPrimeI313N1 : Ideal.IsPrime I313N1 := prime_ideal_of_norm_prime hp313.out _ NI313N1

def I313N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1597, -964, 422, -276, 334]] i)))

def SI313N2: IdealEqSpanCertificate' Table ![![1597, -964, 422, -276, 334]] 
 ![![313, 0, 0, 0, 0], ![273, 1, 0, 0, 0], ![159, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![302, 0, 0, 0, 1]] where
  M :=![![![1597, -964, 422, -276, 334], ![-2672, 1607, -708, 452, -552], ![3544, -2142, 957, -608, 728], ![-1576, 984, -452, 307, -332], ![1412, -872, 368, -276, 317]]]
  hmulB := by decide  
  f := ![![![21237, 4016, -5766, -2812, -5086]], ![![18653, 3583, -5018, -2448, -4454]], ![![10795, 2106, -2877, -1404, -2570]], ![![4630, 896, -1240, -605, -1104]], ![![20434, 3960, -5468, -2668, -4871]]]
  g := ![![![371, -964, 422, -276, 334], ![-619, 1607, -708, 452, -552], ![827, -2142, 957, -608, 728], ![-382, 984, -452, 307, -332], ![334, -872, 368, -276, 317]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI313N2 : Nat.card (O ⧸ I313N2) = 313 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI313N2)

lemma isPrimeI313N2 : Ideal.IsPrime I313N2 := prime_ideal_of_norm_prime hp313.out _ NI313N2
def MulI313N0 : IdealMulLeCertificate' Table 
  ![![22426495, -13570286, 5981893, -3902285, 4677461]] ![![9, -5, 2, -1, 2]]
  ![![552093007, -334071777, 147261603, -96066014, 115149223]] where
 M := ![![![552093007, -334071777, 147261603, -96066014, 115149223]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI313N1 : IdealMulLeCertificate' Table 
  ![![552093007, -334071777, 147261603, -96066014, 115149223]] ![![1597, -964, 422, -276, 334]]
  ![![313, 0, 0, 0, 0]] where
 M := ![![![2610218182295, -1579444438245, 696232173533, -454186619606, 544409352565]]]
 hmul := by decide  
 g := ![![![![8339355215, -5046148365, 2224383941, -1451075462, 1739327005]]]]
 hle2 := by decide  


def PBC313 : ContainsPrimesAboveP 313 ![I313N0, I313N1, I313N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI313N0
    exact isPrimeI313N1
    exact isPrimeI313N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 313 (by decide) (𝕀 ⊙ MulI313N0 ⊙ MulI313N1)
instance hp317 : Fact (Nat.Prime 317) := {out := by norm_num}

def I317N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14953, 3157, -3815, -1858, -3519]] i)))

def SI317N0: IdealEqSpanCertificate' Table ![![14953, 3157, -3815, -1858, -3519]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![0, 0, 317, 0, 0], ![66, 201, 236, 1, 0], ![307, 148, 97, 0, 1]] where
  M :=![![![14953, 3157, -3815, -1858, -3519], ![28152, 18011, 2992, 1266, -3716], ![788, 14306, 11533, 5442, 3124], ![-26572, -1134, 10492, 5055, 7300], ![-13546, 18088, 20882, 9900, 8113]]]
  hmulB := by decide  
  f := ![![![-2277, 149, 1015, -786, -603]], ![![4824, 459, 664, 4022, -1572]], ![![3876, -1278, -5467, -1786, 4808]], ![![5402, -629, -3422, 1021, 2454]], ![![1239, -25, -354, 596, 126]]]
  g := ![![![3842, 2831, 2448, -1858, -3519], ![3424, 989, 204, 1266, -3716], ![-4156, -4864, -4971, 5442, 3124], ![-8206, -6617, -5964, 5055, 7300], ![-9961, -10008, -9787, 9900, 8113]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P0 : CertificateIrreducibleZModOfList' 317 3 2 8 [130, 83, 237, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [294, 19, 309], [103, 297, 8], [0, 1]]
 g := ![![[27, 207, 24], [16, 145], [13, 269, 311], [194, 149, 7], [102, 266, 306], [268, 285, 212], [80, 1], []], ![[112, 25, 210, 187], [119, 149], [96, 211, 146, 177], [53, 132, 6, 155], [11, 238, 25, 265], [231, 244, 200, 133], [297, 83], [61, 64]], ![[288, 59, 30, 200], [314, 308], [295, 125, 220, 41], [244, 257, 313, 190], [109, 66, 302, 197], [145, 55, 199, 154], [46, 44], [45, 64]]]
 h' := ![![[294, 19, 309], [69, 51, 179], [212, 35, 70], [140, 95, 59], [54, 15, 18], [30, 219, 185], [61, 204, 294], [0, 0, 1], [0, 1]], ![[103, 297, 8], [128, 182, 133], [266, 274, 222], [24, 58, 279], [265, 112, 154], [3, 252, 254], [118, 205, 96], [207, 8, 297], [294, 19, 309]], ![[0, 1], [15, 84, 5], [293, 8, 25], [17, 164, 296], [86, 190, 145], [186, 163, 195], [59, 225, 244], [4, 309, 19], [103, 297, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [207, 181], []]
 b := ![[], [26, 40, 300], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N0 : CertifiedPrimeIdeal' SI317N0 317 where
  n := 3
  hpos := by decide
  P := [130, 83, 237, 1]
  hirr := P317P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27149, -138757, -268579, -244688, 184752]
  a := ![1, 3, 2, -1, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-128065, 68455, 124785, -244688, 184752]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N0 : Ideal.IsPrime I317N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N0 B_one_repr
lemma NI317N0 : Nat.card (O ⧸ I317N0) = 31855013 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N0

def I317N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2277, 149, 1015, -786, -603]] i)))

def SI317N1: IdealEqSpanCertificate' Table ![![-2277, 149, 1015, -786, -603]] 
 ![![317, 0, 0, 0, 0], ![0, 317, 0, 0, 0], ![125, 82, 1, 0, 0], ![211, 37, 0, 1, 0], ![202, 201, 0, 0, 1]] where
  M :=![![![-2277, 149, 1015, -786, -603], ![4824, 459, 664, 4022, -1572], ![3876, -1278, -5467, -1786, 4808], ![-21644, 122, 4984, -11393, -1000], ![1878, 2366, 8204, 8220, -8657]]]
  hmulB := by decide  
  f := ![![![14953, 3157, -3815, -1858, -3519]], ![![28152, 18011, 2992, 1266, -3716]], ![![13181, 5949, -694, -388, -2339]], ![![13155, 4200, -2157, -1073, -2753]], ![![27336, 13489, -468, -350, -4573]]]
  g := ![![![500, 212, 1015, -786, -603], ![-1922, 357, 664, 4022, -1572], ![293, -1430, -5467, -1786, 4808], ![6187, 675, 4984, -11393, -1000], ![-3184, 2415, 8204, 8220, -8657]]]
  hle1 := by decide   
  hle2 := by decide  


def P317P1 : CertificateIrreducibleZModOfList' 317 2 2 8 [177, 302, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 316], [0, 1]]
 g := ![![[102, 204], [172], [190, 240], [227, 294], [138, 141], [131, 138], [225], [1]], ![[309, 113], [172], [303, 77], [199, 23], [34, 176], [299, 179], [225], [1]]]
 h' := ![![[15, 316], [138, 134], [289, 55], [80, 157], [300, 151], [271, 211], [63, 284], [140, 15], [0, 1]], ![[0, 1], [246, 183], [163, 262], [216, 160], [29, 166], [266, 106], [202, 33], [48, 302], [15, 316]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [233]]
 b := ![[], [315, 275]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI317N1 : CertifiedPrimeIdeal' SI317N1 317 where
  n := 2
  hpos := by decide
  P := [177, 302, 1]
  hirr := P317P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26038, -8991, -6132, -22994, 19756]
  a := ![1, -11, -7, -1, 47]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5052, -8285, -6132, -22994, 19756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI317N1 : Ideal.IsPrime I317N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI317N1 B_one_repr
lemma NI317N1 : Nat.card (O ⧸ I317N1) = 100489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI317N1
def MulI317N0 : IdealMulLeCertificate' Table 
  ![![14953, 3157, -3815, -1858, -3519]] ![![-2277, 149, 1015, -786, -603]]
  ![![317, 0, 0, 0, 0]] where
 M := ![![![317, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC317 : ContainsPrimesAboveP 317 ![I317N0, I317N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI317N0
    exact isPrimeI317N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 317 (by decide) (𝕀 ⊙ MulI317N0)


lemma PB324I7_primes (p : ℕ) :
  p ∈ Set.range ![311, 313, 317] ↔ Nat.Prime p ∧ 307 < p ∧ p ≤ 323 := by
  rw [← List.mem_ofFn']
  convert primes_range 307 323 (by omega)

def PB324I7 : PrimesBelowBoundCertificateInterval O 307 323 324 where
  m := 3
  g := ![3, 3, 2]
  P := ![311, 313, 317]
  hP := PB324I7_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I311N0, I311N1, I311N2]
    · exact ![I313N0, I313N1, I313N2]
    · exact ![I317N0, I317N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC311
    · exact PBC313
    · exact PBC317
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![30080231, 311, 311]
    · exact ![30664297, 313, 313]
    · exact ![31855013, 100489]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI311N0
      exact NI311N1
      exact NI311N2
    · dsimp ; intro j
      fin_cases j
      exact NI313N0
      exact NI313N1
      exact NI313N2
    · dsimp ; intro j
      fin_cases j
      exact NI317N0
      exact NI317N1
  β := ![I311N1, I311N2, I313N1, I313N2]
  Il := ![[I311N1, I311N2], [I313N1, I313N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
