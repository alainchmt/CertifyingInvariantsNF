
import IdealArithmetic.Examples.NF5_3_2025000000_6.RI5_3_2025000000_6
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5881, 1386, -405, -1375, 5846]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-5881, 1386, -405, -1375, 5846]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![190, 10, 196, 1, 0], ![6, 32, 59, 0, 1]] where
  M :=![![![-5881, 1386, -405, -1375, 5846], ![-30996, 6957, -2065, -6997, 29810], ![-159324, 37582, -10972, -37265, 158438], ![-840068, 188650, -55951, -189648, 807990], ![-211240, 47656, -14112, -47844, 203799]]]
  hmulB := by decide  
  f := ![![![-311, -34, 27, 31, -130]], ![![652, -505, 33, 127, -474]], ![![1148, 2962, -582, -1139, 4502]], ![![782, 2828, -535, -1070, 4222]], ![![414, 790, -164, -313, 1241]]]
  g := ![![![1107, -864, -381, -1375, 5846], ![5626, -4407, -1957, -6997, 29810], ![30002, -23416, -10326, -37265, 158438], ![152488, -119450, -53047, -189648, 807990], ![38474, -30128, -13371, -47844, 203799]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [77, 106, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 11, 15], [62, 187, 184], [0, 1]]
 g := ![![[9, 87, 40], [78, 6, 144], [112, 113, 112], [184, 63], [84, 13], [142, 161], [1]], ![[74, 124, 110, 194], [143, 168, 148, 171], [80, 79, 66, 84], [82, 40], [99, 158], [66, 144], [135, 185, 135, 191]], ![[192, 64, 168, 63], [36, 29, 51, 65], [186, 127, 24, 91], [119, 49], [187, 187], [6, 86], [120, 173, 185, 8]]]
 h' := ![![[103, 11, 15], [163, 137, 144], [132, 55, 12], [176, 118, 149], [4, 99, 62], [169, 19, 150], [122, 93, 165], [0, 1]], ![[62, 187, 184], [138, 71, 128], [42, 21, 84], [58, 83, 181], [2, 128, 144], [137, 73, 77], [170, 157, 12], [103, 11, 15]], ![[0, 1], [126, 190, 126], [128, 123, 103], [26, 197, 68], [45, 171, 192], [64, 107, 171], [39, 148, 22], [62, 187, 184]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 185], []]
 b := ![[], [5, 154, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [77, 106, 34, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5700410585, -2341174029, 518919468, 1924080231, -8077366179]
  a := ![220, -541, 57, 274, -1115]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1564877569, 1190420811, 502330647, 1924080231, -8077366179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-311, -34, 27, 31, -130]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-311, -34, 27, 31, -130]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![163, 3, 1, 0, 0], ![108, 154, 0, 1, 0], ![62, 82, 0, 0, 1]] where
  M :=![![![-311, -34, 27, 31, -130], ![652, -505, 33, 127, -474], ![1148, 2962, -582, -1139, 4502], ![-16820, -6270, 2147, 3154, -12774], ![-4344, -1184, 484, 664, -2711]]]
  hmulB := by decide  
  f := ![![![-5881, 1386, -405, -1375, 5846]], ![![-30996, 6957, -2065, -6997, 29810]], ![![-6085, 1429, -418, -1419, 6034]], ![![-31400, 7084, -2099, -7114, 30302]], ![![-15666, 3538, -1048, -3552, 15129]]]
  g := ![![![0, 29, 27, 31, -130], ![55, 94, 33, 127, -474], ![-302, -950, -582, -1139, 4502], ![425, 2759, 2147, 3154, -12774], ![66, 590, 484, 664, -2711]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [147, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 198], [0, 1]]
 g := ![![[162, 103], [197, 50], [36, 63], [128], [23], [104], [66, 1]], ![[194, 96], [114, 149], [15, 136], [128], [23], [104], [132, 198]]]
 h' := ![![[66, 198], [95, 74], [81, 100], [47, 62], [117, 39], [48, 53], [49, 30], [0, 1]], ![[0, 1], [4, 125], [114, 99], [159, 137], [104, 160], [163, 146], [39, 169], [66, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [184]]
 b := ![[], [148, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [147, 133, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2544453, 2422614, -457871, -1817989, 7487398]
  a := ![-351, 800, -91, -439, 1779]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-983856, -1659297, -457871, -1817989, 7487398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-5881, 1386, -405, -1375, 5846]] ![![-311, -34, 27, 31, -130]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-876159, 269129, -87682, -272327, 1133598]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-876159, 269129, -87682, -272327, 1133598]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![0, 0, 0, 211, 0], ![37, 208, 188, 148, 1]] where
  M :=![![![-876159, 269129, -87682, -272327, 1133598], ![-5508772, 381903, -268938, -738858, 3237938], ![-19166884, 6508614, -2051991, -6418884, 26642512], ![-127843520, 6407308, -5712126, -15322575, 67854056], ![-30956618, 2139999, -1509984, -4147483, 18177497]]]
  hmulB := by decide  
  f := ![![![-873, -305, 166, 279, -1176]], ![![6024, -2937, 334, 1228, -4926]], ![![20012, 10194, -1625, -1744, 5828]], ![![1944, -47808, 15338, 32859, -136744]], ![![24979, -27448, 9686, 22790, -95937]]]
  g := ![![![-202935, -1116205, -1010446, -796421, 1133598], ![-593898, -3190091, -2886262, -2274662, 3237938], ![-4762748, -26232862, -23748077, -18718060, 26642512], ![-12504472, -66858940, -60484714, -47666933, 67854056], ![-3334237, -17908907, -16203220, -12769749, 18177497]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 4 2 7 [67, 83, 183, 87, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 62, 40, 110], [116, 76, 2, 77], [128, 72, 169, 24], [0, 1]]
 g := ![![[175, 152, 37, 179], [4, 183, 60, 6], [137, 155, 46], [77, 117, 96], [80, 16, 108, 201], [1, 124, 1], []], ![[70, 127, 0, 43, 24, 191], [79, 77, 149, 63, 79, 140], [121, 16, 121], [137, 156, 201], [87, 161, 198, 131, 7, 15], [92, 173, 188], [168, 73, 158, 176, 120, 12]], ![[71, 38, 205, 17, 134, 158], [117, 109, 37, 6, 149, 130], [16, 79, 14], [167, 203, 84], [44, 148, 182, 191, 9, 27], [123, 23, 70], [79, 36, 169, 165, 184, 140]], ![[53, 140, 189, 145, 51, 71], [67, 58, 85, 90, 181, 201], [151, 79, 136], [111, 81, 37], [58, 110, 37, 23, 75, 83], [210, 33, 134], [17, 163, 97, 169, 20, 109]]]
 h' := ![![[91, 62, 40, 110], [154, 186, 76, 161], [142, 95, 121, 46], [167, 61, 203, 149], [126, 153, 192, 27], [144, 49, 8, 137], [0, 0, 0, 1], [0, 1]], ![[116, 76, 2, 77], [169, 84, 55, 21], [198, 191, 103, 194], [169, 202, 86, 11], [8, 71, 152, 74], [33, 79, 162, 12], [17, 121, 105, 140], [91, 62, 40, 110]], ![[128, 72, 169, 24], [170, 39, 97, 64], [179, 65, 138, 114], [14, 73, 6, 196], [81, 28, 10, 154], [71, 41, 19, 164], [111, 132, 124, 131], [116, 76, 2, 77]], ![[0, 1], [97, 113, 194, 176], [63, 71, 60, 68], [120, 86, 127, 66], [52, 170, 68, 167], [201, 42, 22, 109], [150, 169, 193, 150], [128, 72, 169, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 23, 201], []]
 b := ![[], [], [194, 118, 0, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 4
  hpos := by decide
  P := [67, 83, 183, 87, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2190107871, 555157090, -145130239, -519097901, 2212672582]
  a := ![15, -39, 4, 18, -76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-398383855, -2178581706, -1972168605, -1554476967, 2212672582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 1982119441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![873, 305, -166, -279, 1176]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![873, 305, -166, -279, 1176]] 
 ![![211, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![72, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![873, 305, -166, -279, 1176], ![-6024, 2937, -334, -1228, 4926], ![-20012, -10194, 1625, 1744, -5828], ![-1944, 47808, -15338, -32859, 136744], ![90, 10235, -3608, -7683, 32139]]]
  hmulB := by decide  
  f := ![![![876159, -269129, 87682, 272327, -1133598]], ![![590836, -175277, 57790, 179030, -746006]], ![![389812, -122682, 39645, 123348, -513088]], ![![1124945, -189803, 79016, 233950, -993146]], ![![541193, -131314, 46634, 142268, -596537]]]
  g := ![![![-500, 305, -166, -279, 1176], ![-3298, 2937, -334, -1228, 4926], ![7512, -10194, 1625, 1744, -5828], ![-67691, 47808, -15338, -32859, 136744], ![-15284, 10235, -3608, -7683, 32139]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N1 : Nat.card (O ⧸ I211N1) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N1)

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := prime_ideal_of_norm_prime hp211.out _ NI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-876159, 269129, -87682, -272327, 1133598]] ![![873, 305, -166, -279, 1176]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187871, -33312, 13544, 40270, -170652]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![187871, -33312, 13544, 40270, -170652]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![58, 37, 1, 0, 0], ![84, 27, 0, 1, 0], ![161, 193, 0, 0, 1]] where
  M :=![![![187871, -33312, 13544, 40270, -170652], ![893192, -158365, 64390, 191448, -811300], ![4246376, -752940, 306131, 910210, -3857192], ![20188512, -3579440, 1455382, 4327215, -18337460], ![5017904, -889684, 361740, 1075544, -4557837]]]
  hmulB := by decide  
  f := ![![![1121, 384, -148, -218, 892]], ![![-4008, 1309, 46, -252, 892]], ![![-378, 267, -23, -82, 316]], ![![148, 473, -96, -193, 768]], ![![-2601, 1447, -78, -394, 1491]]]
  g := ![![![105357, 140422, 13544, 40270, -170652], ![500880, 667583, 64390, 191448, -811300], ![2381350, 3173913, 306131, 910210, -3857192], ![11321172, 15089087, 1455382, 4327215, -18337460], ![2813915, 3750443, 361740, 1075544, -4557837]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [127, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 222], [0, 1]]
 g := ![![[124, 72], [10, 175], [172, 50], [112, 124], [74, 175], [106], [85, 1]], ![[0, 151], [167, 48], [185, 173], [171, 99], [8, 48], [106], [170, 222]]]
 h' := ![![[85, 222], [68, 133], [10, 93], [48, 148], [191, 149], [171, 93], [132, 185], [0, 1]], ![[0, 1], [0, 90], [110, 130], [140, 75], [145, 74], [48, 130], [24, 38], [85, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132]]
 b := ![[], [94, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [127, 138, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4110556, 2648208, -482923, -2071628, 8625257]
  a := ![-381, 955, -99, -477, 1931]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5339689, -7122082, -482923, -2071628, 8625257]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2037, 383, -151, -452, 1912]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-2037, 383, -151, -452, 1912]] 
 ![![223, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![165, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![167, 0, 0, 0, 1]] where
  M :=![![![-2037, 383, -151, -452, 1912], ![-9936, 1667, -693, -2055, 8728], ![-46088, 8768, -3436, -10299, 43550], ![-225988, 37478, -15655, -46396, 197146], ![-56042, 9415, -3908, -11595, 49247]]]
  hmulB := by decide  
  f := ![![![16729, -219, -1155, -1028, 4526]], ![![8355, 44, -602, -567, 2470]], ![![11843, -881, -699, -475, 2216]], ![![10845, 1035, -942, -1078, 4544]], ![![13611, 12, -971, -903, 3943]]]
  g := ![![![-1347, 383, -151, -452, 1912], ![-6111, 1667, -693, -2055, 8728], ![-30703, 8768, -3436, -10299, 43550], ![-137959, 37478, -15655, -46396, 197146], ![-34487, 9415, -3908, -11595, 49247]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 307, -49, -106, 414]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-19, 307, -49, -106, 414]] 
 ![![223, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![165, 0, 1, 0, 0], ![87, 0, 0, 1, 0], ![63, 0, 0, 0, 1]] where
  M :=![![![-19, 307, -49, -106, 414], ![-1436, -973, 261, 433, -1736], ![7032, 84, -516, -497, 2158], ![-12372, 14054, -1433, -4112, 15718], ![-2102, 3851, -484, -1211, 4675]]]
  hmulB := by decide  
  f := ![![![-37401, 6065, -2565, -7582, 32240]], ![![-19719, 3224, -1358, -4017, 17076]], ![![-31491, 5095, -2157, -6375, 27110]], ![![-31909, 5839, -2330, -6960, 29470]], ![![-14891, 2564, -1053, -3129, 13277]]]
  g := ![![![-195, 307, -49, -106, 414], ![615, -973, 261, 433, -1736], ![-45, 84, -516, -497, 2158], ![-8953, 14054, -1433, -4112, 15718], ![-2451, 3851, -484, -1211, 4675]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2

def I223N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 122, -20, -42, 164]] i)))

def SI223N3: IdealEqSpanCertificate' Table ![![5, 122, -20, -42, 164]] 
 ![![223, 0, 0, 0, 0], ![183, 1, 0, 0, 0], ![184, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![5, 122, -20, -42, 164], ![-568, -375, 104, 172, -692], ![2856, -92, -179, -132, 592], ![-3776, 5720, -608, -1643, 6248], ![-548, 1550, -200, -478, 1837]]]
  hmulB := by decide  
  f := ![![![-2349997, 416666, -169412, -503706, 2134556]], ![![-1978573, 350811, -142636, -424094, 1797184]], ![![-2177200, 386028, -156955, -466668, 1977600]], ![![-1142931, 202654, -82396, -244985, 1038172]], ![![-934822, 165750, -67392, -200374, 849125]]]
  g := ![![![-129, 122, -20, -42, 164], ![411, -375, 104, 172, -692], ![72, -92, -179, -132, 592], ![-5939, 5720, -608, -1643, 6248], ![-1618, 1550, -200, -478, 1837]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N3 : Nat.card (O ⧸ I223N3) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N3)

lemma isPrimeI223N3 : Ideal.IsPrime I223N3 := prime_ideal_of_norm_prime hp223.out _ NI223N3
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![187871, -33312, 13544, 40270, -170652]] ![![-2037, 383, -151, -452, 1912]]
  ![![-212778443, 37727761, -15339323, -45608168, 193273792]] where
 M := ![![![-212778443, 37727761, -15339323, -45608168, 193273792]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-212778443, 37727761, -15339323, -45608168, 193273792]] ![![-19, 307, -49, -106, 414]]
  ![![2349997, -416666, 169412, 503706, -2134556]] where
 M := ![![![2349997, -416666, 169412, 503706, -2134556]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N2 : IdealMulLeCertificate' Table 
  ![![2349997, -416666, 169412, 503706, -2134556]] ![![5, 122, -20, -42, 164]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11119, -9539, 1679, 6168, -24070]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-11119, -9539, 1679, 6168, -24070]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![75, 94, 1, 0, 0], ![214, 92, 0, 1, 0], ![184, 173, 0, 0, 1]] where
  M :=![![![-11119, -9539, 1679, 6168, -24070], ![83036, 45459, -6983, -26911, 103228], ![-315760, -258656, 45044, 166071, -647226], ![2213628, 1252598, -194933, -747664, 2872806], ![467318, 255953, -39324, -151537, 581295]]]
  hmulB := by decide  
  f := ![![![8407, 1771, -905, -1208, 4996]], ![![-23592, 12267, -421, -2917, 10792]], ![![-7097, 5305, -409, -1479, 5618]], ![![138, 7608, -1319, -2798, 11014]], ![![-10694, 10982, -1123, -3308, 12705]]]
  g := ![![![13092, 15107, 1679, 6168, -24070], ![-55631, -64673, -6983, -26911, 103228], ![351790, 406162, 45044, 166071, -647226], ![-1549615, -1800150, -194933, -747664, 2872806], ![-313272, -364186, -39324, -151537, 581295]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [2, 197, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 226], [0, 1]]
 g := ![![[212, 57], [159, 214], [84], [160], [100], [114, 100], [30, 1]], ![[106, 170], [223, 13], [84], [160], [100], [163, 127], [60, 226]]]
 h' := ![![[30, 226], [136, 113], [159, 21], [10, 68], [28, 29], [226, 10], [167, 217], [0, 1]], ![[0, 1], [121, 114], [108, 206], [7, 159], [217, 198], [72, 217], [94, 10], [30, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [140, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [2, 197, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4907554, 3522922, -686246, -2840450, 11786288]
  a := ![469, -1152, 123, 588, -2377]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6670748, -7531614, -686246, -2840450, 11786288]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12443, 2206, -897, -2667, 11302]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-12443, 2206, -897, -2667, 11302]] 
 ![![227, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![220, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![199, 0, 0, 0, 1]] where
  M :=![![![-12443, 2206, -897, -2667, 11302], ![-59156, 10491, -4265, -12681, 53738], ![-281260, 49862, -20274, -60281, 255454], ![-1337076, 237106, -96399, -286622, 1214614], ![-332336, 58932, -23960, -71240, 301893]]]
  hmulB := by decide  
  f := ![![![-6705, 1562, -473, -1577, 6718]], ![![-1251, 293, -88, -294, 1252]], ![![-7328, 1694, -512, -1713, 7298]], ![![-5164, 1230, -363, -1220, 5190]], ![![-6941, 1622, -489, -1633, 6955]]]
  g := ![![![-9077, 2206, -897, -2667, 11302], ![-43159, 10491, -4265, -12681, 53738], ![-205164, 49862, -20274, -60281, 255454], ![-975500, 237106, -96399, -286622, 1214614], ![-242461, 58932, -23960, -71240, 301893]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -5, 1, 2, -8]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![-3, -5, 1, 2, -8]] 
 ![![227, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![68, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![116, 0, 0, 0, 1]] where
  M :=![![![-3, -5, 1, 2, -8], ![32, 5, -3, -3, 12], ![-48, 20, 2, 3, -18], ![204, -354, 59, 158, -642], ![38, -89, 16, 41, -167]]]
  hmulB := by decide  
  f := ![![![251, 213, -39, -138, 538]], ![![35, 32, -6, -21, 82]], ![![108, 88, -16, -57, 222]], ![![-124, -58, 7, 32, -122]], ![![86, 83, -16, -55, 215]]]
  g := ![![![4, -5, 1, 2, -8], ![-5, 5, -3, -3, 12], ![4, 20, 2, 3, -18], ![322, -354, 59, 158, -642], ![83, -89, 16, 41, -167]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2

def I227N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![647, 320, -5, 45, -258]] i)))

def SI227N3: IdealEqSpanCertificate' Table ![![647, 320, -5, 45, -258]] 
 ![![227, 0, 0, 0, 0], ![57, 1, 0, 0, 0], ![156, 0, 1, 0, 0], ![188, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![647, 320, -5, 45, -258], ![2748, -3307, 833, 2011, -8310], ![39092, -3306, 300, 3993, -17194], ![95660, -9702, 8019, 25308, -110462], ![25852, -1554, 1748, 5946, -26093]]]
  hmulB := by decide  
  f := ![![![50797149, -9004980, 3661595, 10886771, -46135218]], ![![13819019, -2449827, 996130, 2961734, -12551020]], ![![39967080, -7085058, 2880926, 8565657, -36298966]], ![![66114296, -11722394, 4766147, 14171074, -60052838]], ![![24549777, -4352490, 1769715, 5261821, -22298103]]]
  g := ![![![-17, 320, -5, 45, -258], ![1643, -3307, 833, 2011, -8310], ![3776, -3306, 300, 3993, -17194], ![16776, -9702, 8019, 25308, -110462], ![3919, -1554, 1748, 5946, -26093]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N3 : Nat.card (O ⧸ I227N3) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N3)

lemma isPrimeI227N3 : Ideal.IsPrime I227N3 := prime_ideal_of_norm_prime hp227.out _ NI227N3
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-11119, -9539, 1679, 6168, -24070]] ![![-12443, 2206, -897, -2667, 11302]]
  ![![-17349987, 3092703, -1254300, -3731063, 15808188]] where
 M := ![![![-17349987, 3092703, -1254300, -3731063, 15808188]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![-17349987, 3092703, -1254300, -3731063, 15808188]] ![![-3, -5, 1, 2, -8]]
  ![![50797149, -9004980, 3661595, 10886771, -46135218]] where
 M := ![![![50797149, -9004980, 3661595, 10886771, -46135218]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N2 : IdealMulLeCertificate' Table 
  ![![50797149, -9004980, 3661595, 10886771, -46135218]] ![![647, 320, -5, 45, -258]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC227 : ContainsPrimesAboveP 227 ![I227N0, I227N1, I227N2, I227N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI227N0
    exact isPrimeI227N1
    exact isPrimeI227N2
    exact isPrimeI227N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 227 (by decide) (𝕀 ⊙ MulI227N0 ⊙ MulI227N1 ⊙ MulI227N2)
instance hp229 : Fact (Nat.Prime 229) := {out := by norm_num}

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1917, 350, -140, -418, 1770]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-1917, 350, -140, -418, 1770]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![158, 135, 48, 1, 0], ![107, 111, 48, 0, 1]] where
  M :=![![![-1917, 350, -140, -418, 1770], ![-9236, 1605, -656, -1950, 8272], ![-43472, 7980, -3177, -9500, 40220], ![-209720, 36188, -14840, -44117, 187200], ![-52080, 9038, -3696, -10994, 46641]]]
  hmulB := by decide  
  f := ![![![31, 2, -4, -6, 26]], ![![-148, 113, -16, -46, 184]], ![![-736, -332, 67, 76, -276]], ![![-218, 3, 0, -19, 84]], ![![-211, -13, 4, -10, 47]]]
  g := ![![![-547, -610, -284, -418, 1770], ![-2560, -2853, -1328, -1950, 8272], ![-12428, -13860, -6453, -9500, 40220], ![-57946, -64573, -30056, -44117, 187200], ![-14435, -16087, -7488, -10994, 46641]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [19, 68, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 189, 194], [12, 39, 35], [0, 1]]
 g := ![![[7, 62, 204], [119, 11], [105, 58, 202], [118, 168], [111, 20], [141, 180, 214], [1]], ![[30, 39, 122, 89], [47, 187], [26, 186, 97, 98], [48, 76], [157, 215], [10, 139, 189, 8], [97, 74, 127, 177]], ![[108, 145, 32, 198], [81, 228], [186, 228, 81, 141], [9, 81], [0, 1], [197, 205, 104, 7], [210, 104, 91, 52]]]
 h' := ![![[96, 189, 194], [34, 104, 152], [66, 55, 34], [104, 146, 109], [133, 10, 175], [69, 177, 132], [210, 161, 108], [0, 1]], ![[12, 39, 35], [7, 146, 227], [199, 95, 88], [172, 29, 57], [175, 77, 63], [69, 227, 98], [98, 163, 180], [96, 189, 194]], ![[0, 1], [20, 208, 79], [52, 79, 107], [32, 54, 63], [165, 142, 220], [169, 54, 228], [28, 134, 170], [12, 39, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [227, 161], []]
 b := ![[], [165, 207, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [19, 68, 121, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6859894411, 5751143848, -927750000, -3526145008, 13696477140]
  a := ![-264, 648, -68, -340, 1338]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3936822045, -4535057828, -2135823984, -3526145008, 13696477140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22369, 21447, -3864, -14085, 55122]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![22369, 21447, -3864, -14085, 55122]] 
 ![![229, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![180, 0, 1, 0, 0], ![114, 0, 0, 1, 0], ![222, 0, 0, 0, 1]] where
  M :=![![![22369, 21447, -3864, -14085, 55122], ![-193692, -98525, 14670, 57192, -218490], ![647844, 579810, -103001, -377220, 1473732], ![-5121672, -2723880, 413478, 1600435, -6129600], ![-1090014, -554751, 82620, 322071, -1230443]]]
  hmulB := by decide  
  f := ![![![19657, 17343, -2436, -3501, 12324]], ![![547, 166, 30, 111, -522]], ![![19632, 13038, -1901, -2364, 8064]], ![![17850, 10578, -990, -575, 600]], ![![21396, 17379, -2340, -3147, 10747]]]
  g := ![![![-43946, 21447, -3864, -14085, 55122], ![173975, -98525, 14670, 57192, -218490], ![-1174830, 579810, -103001, -377220, 1473732], ![4881402, -2723880, 413478, 1600435, -6129600], ![979755, -554751, 82620, 322071, -1230443]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1721, 7049, -952, -2175, 8366]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-1721, 7049, -952, -2175, 8366]] 
 ![![229, 0, 0, 0, 0], ![174, 1, 0, 0, 0], ![181, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-1721, 7049, -952, -2175, 8366], ![-26116, -28123, 6878, 12416, -49790], ![201932, 16870, -14951, -14552, 60636], ![-295960, 272408, -12250, -51403, 179768], ![-50610, 78871, -6468, -18103, 66163]]]
  hmulB := by decide  
  f := ![![![10162383, -98479, 365524, 912785, -4174164]], ![![7844794, -135555, 294994, 748848, -3398954]], ![![9076963, -59737, 320401, 794325, -3644548]], ![![7358788, -1564528, 586474, 1770289, -7455288]], ![![3664635, -370346, 203968, 577908, -2499207]]]
  g := ![![![-6033, 7049, -952, -2175, 8366], ![24530, -28123, 6878, 12416, -49790], ![-10997, 16870, -14951, -14552, 60636], ![-226946, 272408, -12250, -51403, 179768], ![-65857, 78871, -6468, -18103, 66163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-1917, 350, -140, -418, 1770]] ![![22369, 21447, -3864, -14085, 55122]]
  ![![10162383, -98479, 365524, 912785, -4174164]] where
 M := ![![![10162383, -98479, 365524, 912785, -4174164]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![10162383, -98479, 365524, 912785, -4174164]] ![![-1721, 7049, -952, -2175, 8366]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9375, -1831, 545, 1966, -8396]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![9375, -1831, 545, 1966, -8396]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![157, 194, 20, 1, 0], ![160, 52, 216, 0, 1]] where
  M :=![![![9375, -1831, 545, 1966, -8396], ![45288, -10957, 3327, 10977, -46724], ![248848, -60052, 16916, 57405, -243898], ![1289708, -278266, 83021, 287612, -1226150], ![325570, -70307, 20884, 72447, -308821]]]
  hmulB := by decide  
  f := ![![![-24301, -16419, 2715, 10190, -39458]], ![![129188, 85465, -14041, -52819, 204360]], ![![-665288, -448636, 74142, 278329, -1077674]], ![![49219, 31617, -5146, -19422, 75056]], ![![-601482, -406039, 67124, 251955, -975595]]]
  g := ![![![4481, 229, 7617, 1966, -8396], ![24883, 1241, 42387, 10977, -46724], ![129871, 6378, 221248, 57405, -243898], ![653728, 32982, 1112357, 287612, -1226150], ![164647, 8299, 280160, 72447, -308821]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [40, 28, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 215, 38], [172, 17, 195], [0, 1]]
 g := ![![[186, 213, 117], [22, 29], [59, 91], [98, 67, 133], [145, 133], [5, 168, 161], [1]], ![[193, 212, 85, 210], [36, 159], [163, 208], [205, 103, 196, 215], [231, 128], [188, 110, 63, 183], [121, 123, 173, 117]], ![[121, 32, 152, 175], [222, 107], [19, 9], [134, 79, 145, 18], [50, 63], [0, 182, 153, 161], [104, 139, 155, 116]]]
 h' := ![![[16, 215, 38], [219, 185, 74], [20, 183, 31], [41, 206, 18], [182, 183, 42], [33, 99, 191], [193, 205, 188], [0, 1]], ![[172, 17, 195], [193, 119, 133], [85, 18, 25], [224, 34, 212], [118, 156, 212], [182, 127, 19], [188, 3, 35], [16, 215, 38]], ![[0, 1], [156, 162, 26], [101, 32, 177], [167, 226, 3], [149, 127, 212], [106, 7, 23], [228, 25, 10], [172, 17, 195]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 182], []]
 b := ![[], [67, 168, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [40, 28, 45, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164494476788, 62424752618, -13939718530, -51959300074, 218829091926]
  a := ![-641, 1583, -166, -797, 3249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-115963687010, -5307226666, -198462822202, -51959300074, 218829091926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-172915, 39958, -11708, -39792, 169364]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-172915, 39958, -11708, -39792, 169364]] 
 ![![233, 0, 0, 0, 0], ![56, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![167, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![-172915, 39958, -11708, -39792, 169364], ![-901768, 208305, -61010, -207416, 882808], ![-4700400, 1085200, -317975, -1081066, 4601344], ![-24501136, 5660576, -1658346, -5637003, 23992404], ![-6169092, 1425222, -417548, -1419322, 6040973]]]
  hmulB := by decide  
  f := ![![![-7056499, 1245530, -507488, -1508328, 6392860]], ![![-1839680, 324961, -132358, -393412, 1667384]], ![![-4500634, 794284, -323651, -961926, 4077024]], ![![-8304925, 1471966, -598582, -1779695, 7541920]], ![![-2624416, 464594, -189036, -561982, 2381645]]]
  g := ![![![-19107, 39958, -11708, -39792, 169364], ![-99612, 208305, -61010, -207416, 882808], ![-519096, 1085200, -317975, -1081066, 4601344], ![-2706895, 5660576, -1658346, -5637003, 23992404], ![-681554, 1425222, -417548, -1419322, 6040973]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2689, 599, -177, -608, 2590]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![-2689, 599, -177, -608, 2590]] 
 ![![233, 0, 0, 0, 0], ![157, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![229, 0, 0, 1, 0], ![178, 0, 0, 0, 1]] where
  M :=![![![-2689, 599, -177, -608, 2590], ![-13836, 3253, -957, -3227, 13732], ![-73056, 16928, -4918, -16751, 71278], ![-379140, 86462, -25467, -86814, 369634], ![-95526, 21771, -6408, -21855, 93053]]]
  hmulB := by decide  
  f := ![![![64315, -6469, 3573, 10120, -43772]], ![![44399, -4658, 2508, 7129, -30788]], ![![19883, -1909, 1085, 3061, -13262]], ![![86603, -13531, 5850, 17208, -73250]], ![![55100, -6623, 3294, 9473, -40709]]]
  g := ![![![-1759, 599, -177, -608, 2590], ![-9369, 3253, -957, -3227, 13732], ![-48675, 16928, -4918, -16751, 71278], ![-251589, 86462, -25467, -86814, 369634], ![-63340, 21771, -6408, -21855, 93053]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![9375, -1831, 545, 1966, -8396]] ![![-172915, 39958, -11708, -39792, 169364]]
  ![![1094804139, -252837701, 74075207, 251827340, -1071844512]] where
 M := ![![![1094804139, -252837701, 74075207, 251827340, -1071844512]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![1094804139, -252837701, 74075207, 251827340, -1071844512]] ![![-2689, 599, -177, -608, 2590]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![2053896944385, -474379657668, 138976244344, 472455667158, -2010892367152]]]
 hmul := by decide  
 g := ![![![![8815008345, -2035964196, 596464568, 2027706726, -8630439344]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-463, -16, -12, -26, 128]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-463, -16, -12, -26, 128]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![100, 93, 1, 0, 0], ![21, 55, 0, 1, 0], ![165, 143, 0, 0, 1]] where
  M :=![![![-463, -16, -12, -26, 128], ![-1040, 705, -186, -608, 2484], ![-11080, -716, -215, -374, 2072], ![-20960, 17952, -4546, -15019, 61116], ![-5928, 3988, -1052, -3440, 14057]]]
  hmulB := by decide  
  f := ![![![-609, 144, 16, -18, 56]], ![![128, -1529, 222, 484, -1868]], ![![-180, -511, 87, 170, -660]], ![![-203, -345, 64, 119, -464]], ![![-387, -813, 146, 278, -1083]]]
  g := ![![![-83, -66, -12, -26, 128], ![-1588, -1271, -186, -608, 2484], ![-1354, -1073, -215, -374, 2072], ![-39059, -31267, -4546, -15019, 61116], ![-8987, -7193, -1052, -3440, 14057]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 2 2 7 [60, 182, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 238], [0, 1]]
 g := ![![[11, 4], [22, 8], [212, 16], [128, 132], [116], [204, 32], [57, 1]], ![[0, 235], [0, 231], [168, 223], [4, 107], [116], [116, 207], [114, 238]]]
 h' := ![![[57, 238], [114, 237], [186, 198], [207, 235], [182, 111], [188, 127], [165, 82], [0, 1]], ![[0, 1], [0, 2], [0, 41], [218, 4], [56, 128], [18, 112], [59, 157], [57, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [161]]
 b := ![[], [36, 200]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 2
  hpos := by decide
  P := [60, 182, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16521, 89836, -15323, -60608, 243041]
  a := ![-59, 141, -15, -75, 299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-155984, -125132, -15323, -60608, 243041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-126741, 29270, -8581, -29165, 124136]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-126741, 29270, -8581, -29165, 124136]] 
 ![![239, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![78, 0, 0, 1, 0], ![187, 0, 0, 0, 1]] where
  M :=![![![-126741, 29270, -8581, -29165, 124136], ![-661016, 152827, -44751, -152103, 647370], ![-3446556, 795346, -233024, -792411, 3372762], ![-17959644, 4149054, -1215773, -4132388, 17588514], ![-4522100, 1044596, -306100, -1040456, 4428461]]]
  hmulB := by decide  
  f := ![![![-1429283, 299658, -113001, -340707, 1435508]], ![![-383551, 78409, -29892, -89940, 379270]], ![![-756036, 159458, -59978, -180927, 762150]], ![![-1166378, 194254, -81379, -240680, 1022186]], ![![-1290883, 259366, -99629, -299339, 1263033]]]
  g := ![![![-91631, 29270, -8581, -29165, 124136], ![-477899, 152827, -44751, -152103, 647370], ![-2489690, 795346, -233024, -792411, 3372762], ![-12983428, 4149054, -1215773, -4132388, 17588514], ![-3268977, 1044596, -306100, -1040456, 4428461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8220245, 1898600, -556222, -1890898, 8048146]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![-8220245, 1898600, -556222, -1890898, 8048146]] 
 ![![239, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![-8220245, 1898600, -556222, -1890898, 8048146], ![-42852772, 9897525, -2899622, -9857384, 41955552], ![-223394560, 51596540, -15115955, -51387286, 218717456], ![-1164572688, 268976832, -78800618, -267885807, 1140190604], ![-293227036, 67725512, -19841160, -67450804, 287087897]]]
  hmulB := by decide  
  f := ![![![279877, 76848, -7078, -33970, 121230]], ![![153896, 39797, -3362, -16852, 59360]], ![![56365, 16644, -1677, -7708, 27878]], ![![52269, -47336, 11972, 39483, -160478]], ![![109727, 16296, 206, -3042, 6467]]]
  g := ![![![-3734137, 1898600, -556222, -1890898, 8048146], ![-19466314, 9897525, -2899622, -9857384, 41955552], ![-101479359, 51596540, -15115955, -51387286, 218717456], ![-529019651, 268976832, -78800618, -267885807, 1140190604], ![-133201535, 67725512, -19841160, -67450804, 287087897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2

def I239N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1167, 7610, -1329, -2731, 10714]] i)))

def SI239N3: IdealEqSpanCertificate' Table ![![1167, 7610, -1329, -2731, 10714]] 
 ![![239, 0, 0, 0, 0], ![194, 1, 0, 0, 0], ![126, 0, 1, 0, 0], ![173, 0, 0, 1, 0], ![197, 0, 0, 0, 1]] where
  M :=![![![1167, 7610, -1329, -2731, 10714], ![-38236, -20887, 6139, 9803, -39486], ![163972, -13546, -9440, -6069, 28678], ![-211556, 373002, -46027, -116156, 447806], ![-28160, 99400, -14272, -32812, 127451]]]
  hmulB := by decide  
  f := ![![![-181271, -46994, 3967, 19907, -70158]], ![![-146838, -36471, 2869, 14939, -52090]], ![![-114538, -30462, 2672, 13149, -46610]], ![![-114577, 10280, -6122, -17141, 74420]], ![![-147661, -29318, 1297, 9553, -30527]]]
  g := ![![![-12326, 7610, -1329, -2731, 10714], ![39009, -20887, 6139, 9803, -39486], ![-2587, -13546, -9440, -6069, 28678], ![-564424, 373002, -46027, -116156, 447806], ![-154581, 99400, -14272, -32812, 127451]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N3 : Nat.card (O ⧸ I239N3) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N3)

lemma isPrimeI239N3 : Ideal.IsPrime I239N3 := prime_ideal_of_norm_prime hp239.out _ NI239N3
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-463, -16, -12, -26, 128]] ![![-126741, 29270, -8581, -29165, 124136]]
  ![![-1262045, 291490, -85395, -290305, 1235612]] where
 M := ![![![-1262045, 291490, -85395, -290305, 1235612]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![-1262045, 291490, -85395, -290305, 1235612]] ![![-8220245, 1898600, -556222, -1890898, 8048146]]
  ![![-7273627174247, 1679960511534, -492168626995, -1673146838693, 7121341572534]] where
 M := ![![![-7273627174247, 1679960511534, -492168626995, -1673146838693, 7121341572534]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N2 : IdealMulLeCertificate' Table 
  ![![-7273627174247, 1679960511534, -492168626995, -1673146838693, 7121341572534]] ![![1167, 7610, -1329, -2731, 10714]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![2106786994455, -486595442844, 142555031752, 484621907514, -2062675003216]]]
 hmul := by decide  
 g := ![![![![8815008345, -2035964196, 596464568, 2027706726, -8630439344]]]]
 hle2 := by decide  


def PBC239 : ContainsPrimesAboveP 239 ![I239N0, I239N1, I239N2, I239N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
    exact isPrimeI239N1
    exact isPrimeI239N2
    exact isPrimeI239N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 239 (by decide) (𝕀 ⊙ MulI239N0 ⊙ MulI239N1 ⊙ MulI239N2)
instance hp241 : Fact (Nat.Prime 241) := {out := by norm_num}

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![138669, 87308, -14117, -53405, 206210]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![138669, 87308, -14117, -53405, 206210]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![25, 73, 1, 0, 0], ![103, 239, 0, 1, 0], ![226, 134, 0, 0, 1]] where
  M :=![![![138669, 87308, -14117, -53405, 206210], ![-661820, -467681, 78363, 292763, -1135530], ![3760636, 2391898, -388050, -1466257, 5663998], ![-18233332, -12758982, 2131821, 7972274, -30910842], ![-3726220, -2632890, 441144, 1648126, -6392507]]]
  hmulB := by decide  
  f := ![![![-42963, -36656, 9065, 15631, -62426]], ![![247548, 24755, -21613, -24843, 104566]], ![![68317, 5453, -5736, -6369, 26950]], ![![222531, -989, -15611, -14200, 62186]], ![![95694, -22988, -3008, 1786, -4131]]]
  g := ![![![-168511, -57056, -14117, -53405, 206210], ![928856, 315363, 78363, 292763, -1135530], ![-4628951, -1567721, -388050, -1466257, 5663998], ![25282893, 8582147, 2131821, 7972274, -30910842], ![5229024, 1775342, 441144, 1648126, -6392507]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [162, 234, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 240], [0, 1]]
 g := ![![[55, 61], [91], [143], [225], [201, 18], [73, 237], [7, 1]], ![[0, 180], [91], [143], [225], [86, 223], [45, 4], [14, 240]]]
 h' := ![![[7, 240], [196, 213], [128, 36], [188, 216], [214, 226], [224, 175], [71, 128], [0, 1]], ![[0, 1], [0, 28], [139, 205], [13, 25], [109, 15], [3, 66], [3, 113], [7, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171]]
 b := ![[], [2, 206]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [162, 234, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5480793, 5243810, -970568, -4001988, 16514177]
  a := ![-527, 1296, -134, -662, 2671]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13697991, -4897632, -970568, -4001988, 16514177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1023, 109, -89, -102, 428]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![1023, 109, -89, -102, 428]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![21, 73, 1, 0, 0], ![154, 235, 0, 1, 0], ![84, 130, 0, 0, 1]] where
  M :=![![![1023, 109, -89, -102, 428], ![-2152, 1675, -113, -425, 1588], ![-3888, -9788, 1922, 3761, -14870], ![55652, 20378, -7071, -10298, 41706], ![14370, 3825, -1592, -2161, 8823]]]
  hmulB := by decide  
  f := ![![![-5125, -4655, 829, 3034, -11858]], ![![41316, 21745, -3289, -12745, 48784]], ![![11459, 5658, -832, -3258, 12424]], ![![41566, 20719, -3060, -11963, 45646]], ![![21466, 10615, -1562, -6115, 23321]]]
  g := ![![![-72, -104, -89, -102, 428], ![-281, -401, -113, -425, 1588], ![2596, 3731, 1922, 3761, -14870], ![-7109, -10229, -7071, -10298, 41706], ![-1496, -2154, -1592, -2161, 8823]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [84, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [128, 240], [0, 1]]
 g := ![![[228, 83], [32], [53], [98], [43, 77], [19, 32], [128, 1]], ![[7, 158], [32], [53], [98], [18, 164], [18, 209], [15, 240]]]
 h' := ![![[128, 240], [220, 18], [4, 153], [212, 52], [3, 87], [91, 199], [93, 153], [0, 1]], ![[0, 1], [114, 223], [67, 88], [120, 189], [53, 154], [17, 42], [156, 88], [128, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [224]]
 b := ![[], [62, 112]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N1 : CertifiedPrimeIdeal' SI241N1 241 where
  n := 2
  hpos := by decide
  P := [84, 113, 1]
  hirr := P241P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2164314, 1551263, -286118, -1203853, 4995620]
  a := ![-293, 721, -77, -367, 1485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-955994, -1427748, -286118, -1203853, 4995620]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N1 B_one_repr
lemma NI241N1 : Nat.card (O ⧸ I241N1) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 11, -4, -5, 20]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![41, 11, -4, -5, 20]] 
 ![![241, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![138, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![41, 11, -4, -5, 20], ![-80, 21, 6, 6, -30], ![252, -374, 63, 156, -624], ![2496, 876, -218, -249, 936], ![670, 185, -52, -53, 199]]]
  hmulB := by decide  
  f := ![![![-1107, 823, -216, -705, 2874]], ![![-489, 320, -86, -279, 1140]], ![![-699, 541, -141, -461, 1878]], ![![-1894, 318, -134, -395, 1676]], ![![-455, 94, -36, -108, 455]]]
  g := ![![![-2, 11, -4, -5, 20], ![-11, 21, 6, 6, -30], ![115, -374, 63, 156, -624], ![-208, 876, -218, -249, 936], ![-40, 185, -52, -53, 199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![138669, 87308, -14117, -53405, 206210]] ![![1023, 109, -89, -102, 428]]
  ![![1107, -823, 216, 705, -2874]] where
 M := ![![![1107, -823, 216, 705, -2874]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![1107, -823, 216, 705, -2874]] ![![41, 11, -4, -5, 20]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73607, -22856, 2433, 10901, -39744]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-73607, -22856, 2433, 10901, -39744]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![135, 114, 33, 133, 1]] where
  M :=![![![-73607, -22856, 2433, 10901, -39744], ![74056, 174577, -35115, -123589, 490006], ![-1864324, -650850, 77088, 329513, -1220034], ![2723740, 4648682, -909445, -3228424, 12759058], ![418440, 982690, -197576, -695450, 2757211]]]
  hmulB := by decide  
  f := ![![![224467, -51844, 15189, 51635, -219772]], ![![1170192, -270289, 79183, 269183, -1145710]], ![![6100356, -1408910, 412762, 1403223, -5972482]], ![![31800908, -7345022, 2151853, 7315246, -31135562]], ![![18336831, -4235232, 1240784, 4218062, -17953153]]]
  g := ![![![21083, 17960, 5235, 21103, -39744], ![-263254, -221857, -64563, -260137, 490006], ![648766, 551526, 160710, 647785, -1220034], ![-6851590, -5776430, -1681109, -6773638, 12759058], ![-1481295, -1248364, -363289, -1463763, 2757211]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 4 2 7 [1, 185, 15, 122, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [192, 245, 112, 36], [157, 140, 102, 52], [31, 116, 37, 163], [0, 1]]
 g := ![![[59, 219, 246, 108], [142, 77, 228, 105], [236, 65, 140], [216, 101, 132, 31], [165, 109, 194, 3], [98, 60, 129, 1], []], ![[44, 97, 44, 129, 39, 51], [87, 102, 105, 94, 102, 3], [201, 246, 233], [76, 199, 111, 239, 157, 190], [112, 244, 30, 188, 248, 89], [235, 175, 154, 112, 218, 195], [243, 177, 36, 101, 117, 221]], ![[204, 29, 192, 158, 191, 86], [101, 246, 250, 110, 56, 84], [12, 92, 115], [139, 225, 207, 6, 110, 15], [29, 149, 95, 232, 158, 66], [231, 180, 108, 74, 109, 218], [19, 150, 181, 28, 45, 48]], ![[36, 166, 219, 146, 14, 176], [63, 138, 173, 224, 88, 96], [2, 165, 201], [183, 64, 101, 127, 110, 159], [243, 183, 190, 27, 47, 139], [14, 219, 156, 40], [24, 248, 203, 89, 10, 244]]]
 h' := ![![[192, 245, 112, 36], [109, 233, 195, 46], [236, 9, 59, 119], [35, 216, 32, 162], [86, 54, 43, 28], [153, 133, 102, 175], [0, 0, 0, 1], [0, 1]], ![[157, 140, 102, 52], [107, 231, 143, 183], [81, 147, 45, 71], [223, 73, 147, 229], [125, 177, 128, 129], [196, 59, 185, 240], [198, 140, 79, 19], [192, 245, 112, 36]], ![[31, 116, 37, 163], [226, 57, 175, 182], [68, 244, 108, 163], [64, 169, 113, 158], [143, 26, 111, 208], [11, 190, 137, 188], [207, 185, 11, 231], [157, 140, 102, 52]], ![[0, 1], [54, 232, 240, 91], [21, 102, 39, 149], [147, 44, 210, 204], [56, 245, 220, 137], [226, 120, 78, 150], [149, 177, 161], [31, 116, 37, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [223, 55, 196], []]
 b := ![[], [], [232, 131, 60, 170], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 4
  hpos := by decide
  P := [1, 185, 15, 122, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31569993127159, 9614631428168, -2367334571499, -8581071411552, 36309495604883]
  a := ![-248, 612, -65, -308, 1257]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19654788445364, -16452860029994, -4783189998138, -19273880425741, 36309495604883]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 3969126001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![224467, -51844, 15189, 51635, -219772]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![224467, -51844, 15189, 51635, -219772]] 
 ![![251, 0, 0, 0, 0], ![59, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![61, 0, 0, 1, 0], ![169, 0, 0, 0, 1]] where
  M :=![![![224467, -51844, 15189, 51635, -219772], ![1170192, -270289, 79183, 269183, -1145710], ![6100356, -1408910, 412762, 1403223, -5972482], ![31800908, -7345022, 2151853, 7315246, -31135562], ![8007136, -1849390, 541812, 1841898, -7839591]]]
  hmulB := by decide  
  f := ![![![-73607, -22856, 2433, 10901, -39744]], ![![-17007, -4677, 432, 2070, -7390]], ![![-17105, -5598, 627, 2746, -10086]], ![![-7037, 12966, -3032, -10213, 41174]], ![![-47893, -11474, 851, 4569, -15775]]]
  g := ![![![146509, -51844, 15189, 51635, -219772], ![763781, -270289, 79183, 269183, -1145710], ![3981505, -1408910, 412762, 1403223, -5972482], ![20756279, -7345022, 2151853, 7315246, -31135562], ![5226201, -1849390, 541812, 1841898, -7839591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-73607, -22856, 2433, 10901, -39744]] ![![224467, -51844, 15189, 51635, -219772]]
  ![![251, 0, 0, 0, 0]] where
 M := ![![![251, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB2201I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB2201I5 : PrimesBelowBoundCertificateInterval O 197 251 2201 where
  m := 9
  g := ![2, 2, 4, 4, 3, 3, 4, 3, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB2201I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2, I223N3]
    · exact ![I227N0, I227N1, I227N2, I227N3]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1, I239N2, I239N3]
    · exact ![I241N0, I241N1, I241N2]
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
    · exact ![7880599, 39601]
    · exact ![1982119441, 211]
    · exact ![49729, 223, 223, 223]
    · exact ![51529, 227, 227, 227]
    · exact ![12008989, 229, 229]
    · exact ![12649337, 233, 233]
    · exact ![57121, 239, 239, 239]
    · exact ![58081, 58081, 241]
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
      exact NI223N3
    · dsimp ; intro j
      fin_cases j
      exact NI227N0
      exact NI227N1
      exact NI227N2
      exact NI227N3
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
      exact NI229N1
      exact NI229N2
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
      exact NI239N3
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I211N1, I223N1, I223N2, I223N3, I227N1, I227N2, I227N3, I229N1, I229N2, I233N1, I233N2, I239N1, I239N2, I239N3, I241N2, I251N1]
  Il := ![[], [I211N1], [I223N1, I223N2, I223N3], [I227N1, I227N2, I227N3], [I229N1, I229N2], [I233N1, I233N2], [I239N1, I239N2, I239N3], [I241N2], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
