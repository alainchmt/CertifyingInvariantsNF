
import IdealArithmetic.Examples.NF5_3_81000000_2.RI5_3_81000000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4103, -5377, -3812, -211, 564]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-4103, -5377, -3812, -211, 564]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![58, 175, 13, 127, 1]] where
  M :=![![![-4103, -5377, -3812, -211, 564], ![3384, 4357, 2872, 136, -422], ![-2532, -2946, -1837, -82, 272], ![1632, 1548, 1052, 67, -164], ![774, 1059, 496, -7, -69]]]
  hmulB := by decide  
  f := ![![![-5, -11, -8, -3, 2]], ![![12, 25, 16, 6, -6]], ![![-36, -78, -59, -26, 12]], ![![72, 144, 76, 25, -52]], ![![52, 104, 55, 18, -37]]]
  g := ![![![-185, -523, -56, -361, 564], ![140, 393, 42, 270, -422], ![-92, -254, -27, -174, 272], ![56, 152, 16, 105, -164], ![24, 66, 7, 44, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [99, 161, 134, 31, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [165, 106, 55, 198], [26, 128, 103, 123], [176, 163, 41, 77], [0, 1]]
 g := ![![[131, 144, 126, 25], [70, 152, 118, 51], [132, 71, 36, 132], [96, 197, 116], [89, 97, 20], [31, 168, 1], []], ![[74, 182, 132, 180, 70, 38], [158, 104, 64, 96, 50, 84], [143, 146, 103, 198, 128, 78], [178, 183, 125], [131, 48, 31], [138, 177, 140], [135, 132, 77, 27, 196, 198]], ![[64, 4, 70, 119, 97, 64], [19, 94, 164, 40, 36, 80], [96, 56, 172, 181, 159, 46], [77, 11, 80], [119, 58, 155], [107, 146, 64], [78, 113, 80, 147, 191, 18]], ![[28, 191, 126, 63, 102, 170], [172, 69, 158, 130, 131, 186], [85, 76, 2, 198, 55, 55], [19, 75, 98], [115, 95, 139], [63, 17, 50], [113, 4, 39, 72, 90, 27]]]
 h' := ![![[165, 106, 55, 198], [35, 127, 110, 5], [66, 189, 114, 38], [150, 41, 187, 27], [36, 66, 168, 64], [115, 68, 141, 47], [0, 0, 0, 1], [0, 1]], ![[26, 128, 103, 123], [124, 143, 172, 165], [44, 27, 196, 151], [86, 83, 33, 11], [185, 18, 31, 181], [47, 74, 159, 164], [66, 77, 66, 90], [165, 106, 55, 198]], ![[176, 163, 41, 77], [160, 161, 194, 103], [24, 68, 102, 133], [29, 121, 183, 183], [17, 90, 63, 94], [16, 128, 88, 126], [103, 24, 158, 8], [26, 128, 103, 123]], ![[0, 1], [168, 166, 121, 125], [183, 114, 185, 76], [160, 153, 194, 177], [161, 25, 136, 59], [197, 128, 10, 61], [128, 98, 174, 100], [176, 163, 41, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [178, 62, 139], []]
 b := ![[], [], [80, 16, 170, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 4
  hpos := by decide
  P := [99, 161, 134, 31, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7940240493, 21521335606, 27535800855, 15047504264, 6319482829]
  a := ![0, -1, -3, -1, -5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1801958611, -5449186731, -274459678, -3957421181, 6319482829]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 11, 8, 3, -2]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![5, 11, 8, 3, -2]] 
 ![![199, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![159, 0, 1, 0, 0], ![188, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![5, 11, 8, 3, -2], ![-12, -25, -16, -6, 6], ![36, 78, 59, 26, -12], ![-72, -144, -76, -25, 52], ![138, 315, 276, 131, -19]]]
  hmulB := by decide  
  f := ![![![4103, 5377, 3812, 211, -564]], ![![2952, 3869, 2744, 152, -406]], ![![3291, 4311, 3055, 169, -452]], ![![3868, 5072, 3596, 199, -532]], ![![326, 427, 304, 17, -45]]]
  g := ![![![-17, 11, 8, 3, -2], ![36, -25, -16, -6, 6], ![-127, 78, 59, 26, -12], ![184, -144, -76, -25, 52], ![-570, 315, 276, 131, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-4103, -5377, -3812, -211, 564]] ![![5, 11, 8, 3, -2]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![-199, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -47, -44, -17, -4]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-29, -47, -44, -17, -4]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![54, 192, 18, 1, 0], ![147, 198, 40, 0, 1]] where
  M :=![![![-29, -47, -44, -17, -4], ![-24, -89, -124, -72, -34], ![-204, -534, -671, -362, -144], ![-864, -2364, -3056, -1679, -724], ![-2070, -5595, -7116, -3881, -1607]]]
  hmulB := by decide  
  f := ![![![37, 95, 24, -5, -2]], ![![-12, 7, 60, 10, -10]], ![![-60, -162, -133, -10, 20]], ![![-6, 18, 50, 7, -8]], ![![3, 42, 48, 4, -7]]]
  g := ![![![7, 19, 2, -17, -4], ![42, 97, 12, -72, -34], ![192, 462, 55, -362, -144], ![930, 2196, 266, -1679, -724], ![2103, 5013, 602, -3881, -1607]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [56, 182, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 168, 10], [127, 42, 201], [0, 1]]
 g := ![![[154, 24, 172], [0, 133, 113], [9, 11], [57, 5], [168, 116, 58], [135, 84], [1]], ![[36, 57, 76, 89], [157, 62, 74, 195], [95, 64], [101, 46], [66, 95, 101, 40], [70, 36], [208, 139, 152, 156]], ![[26, 152, 68, 183], [87, 28, 67, 47], [168, 185], [116, 93], [104, 85, 74, 76], [181, 69], [67, 90, 181, 55]]]
 h' := ![![[27, 168, 10], [0, 200, 52], [91, 124, 18], [157, 146, 86], [87, 113, 65], [7, 183, 67], [155, 29, 154], [0, 1]], ![[127, 42, 201], [99, 23, 175], [54, 193, 97], [47, 168, 8], [46, 170, 62], [167, 48, 2], [17, 1, 6], [27, 168, 10]], ![[0, 1], [105, 199, 195], [47, 105, 96], [148, 108, 117], [174, 139, 84], [196, 191, 142], [41, 181, 51], [127, 42, 201]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193, 113], []]
 b := ![[], [53, 114, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [56, 182, 57, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-924292, -1990184, -879920, -678456, 668340]
  a := ![3, -64, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-296368, -19232, -72992, -678456, 668340]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -95, -24, 5, 2]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-37, -95, -24, 5, 2]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![117, 193, 1, 0, 0], ![207, 4, 0, 1, 0], ![24, 43, 0, 0, 1]] where
  M :=![![![-37, -95, -24, 5, 2], ![12, -7, -60, -10, 10], ![60, 162, 133, 10, -20], ![-120, -240, -128, -7, 20], ![30, 9, -40, 1, 3]]]
  hmulB := by decide  
  f := ![![![29, 47, 44, 17, 4]], ![![24, 89, 124, 72, 34]], ![![39, 110, 141, 77, 34]], ![![33, 59, 60, 26, 8]], ![![18, 50, 64, 35, 15]]]
  g := ![![![8, 21, -24, 5, 2], ![42, 53, -60, -10, 10], ![-81, -117, 133, 10, -20], ![75, 112, -128, -7, 20], ![21, 36, -40, 1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [198, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 210], [0, 1]]
 g := ![![[88, 24], [118, 36], [139], [49], [5, 9], [93], [89, 1]], ![[114, 187], [157, 175], [139], [49], [173, 202], [93], [178, 210]]]
 h' := ![![[89, 210], [57, 119], [200, 6], [9, 75], [65, 204], [8, 3], [102, 127], [0, 1]], ![[0, 1], [98, 92], [101, 205], [143, 136], [75, 7], [64, 208], [11, 84], [89, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [134, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [198, 122, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1113, 1800, 2705, 1418, 424]
  a := ![1, -3, -1, -1, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2934, -2579, 2705, 1418, 424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-29, -47, -44, -17, -4]] ![![-37, -95, -24, 5, 2]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-533, -653, -467, -28, 70]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-533, -653, -467, -28, 70]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![158, 174, 1, 0, 0], ![160, 210, 0, 1, 0], ![56, 9, 0, 0, 1]] where
  M :=![![![-533, -653, -467, -28, 70], ![420, 517, 369, 23, -56], ![-336, -420, -300, -23, 46], ![276, 354, 247, 22, -46], ![30, 3, -7, -26, -1]]]
  hmulB := by decide  
  f := ![![![-311, -607, -255, 10, 32]], ![![192, 169, -117, -31, 20]], ![![-70, -296, -270, -17, 38]], ![![-44, -280, -295, -22, 42]], ![![-70, -146, -70, 1, 9]]]
  g := ![![![331, 385, -467, -28, 70], ![-262, -305, 369, 23, -56], ![216, 252, -300, -23, 46], ![-178, -210, 247, 22, -46], ![24, 30, -7, -26, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [184, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [179, 222], [0, 1]]
 g := ![![[199, 124], [106, 138], [46, 82], [222, 33], [197, 15], [132], [179, 1]], ![[95, 99], [55, 85], [6, 141], [108, 190], [206, 208], [132], [135, 222]]]
 h' := ![![[179, 222], [120, 149], [10, 19], [184, 159], [101, 207], [183, 98], [68, 191], [0, 1]], ![[0, 1], [31, 74], [66, 204], [101, 64], [136, 16], [108, 125], [138, 32], [179, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [191, 181]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [184, 44, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4963, 14968, 20887, 11475, 6209]
  a := ![1, 19, 4, -1, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24569, -27287, 20887, 11475, 6209]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65, 75, 54, 3, -8]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![65, 75, 54, 3, -8]] 
 ![![223, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![174, 0, 1, 0, 0], ![120, 0, 0, 1, 0], ![162, 0, 0, 0, 1]] where
  M :=![![![65, 75, 54, 3, -8], ![-48, -55, -42, -2, 6], ![36, 42, 33, 0, -4], ![-24, -24, -18, 5, 0], ![-18, -33, -26, -9, 7]]]
  hmulB := by decide  
  f := ![![![-37, -135, -118, -21, 6]], ![![-1, -4, -4, -1, 0]], ![![-30, -108, -95, -18, 4]], ![![-24, -84, -78, -19, 0]], ![![-36, -123, -118, -33, -3]]]
  g := ![![![-40, 75, 54, 3, -8], ![31, -55, -42, -2, 6], ![-24, 42, 33, 0, -4], ![12, -24, -18, 5, 0], ![21, -33, -26, -9, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 103, 75, 6, -10]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![83, 103, 75, 6, -10]] 
 ![![223, 0, 0, 0, 0], ![129, 1, 0, 0, 0], ![84, 0, 1, 0, 0], ![91, 0, 0, 1, 0], ![221, 0, 0, 0, 1]] where
  M :=![![![83, 103, 75, 6, -10], ![-60, -67, -41, 5, 12], ![72, 120, 118, 43, 10], ![60, 222, 313, 188, 86], ![222, 615, 791, 436, 183]]]
  hmulB := by decide  
  f := ![![![1793, 5237, 3795, 160, -528]], ![![1023, 3002, 2184, 93, -304]], ![![684, 1980, 1424, 59, -198]], ![![737, 2159, 1568, 66, -218]], ![![1765, 5170, 3756, 160, -523]]]
  g := ![![![-80, 103, 75, 6, -10], ![40, -67, -41, 5, 12], ![-141, 120, 118, 43, 10], ![-408, 222, 313, 188, 86], ![-1012, 615, 791, 436, 183]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2

def I223N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 56, 42, 2, -6]] i)))

def SI223N3: IdealEqSpanCertificate' Table ![![43, 56, 42, 2, -6]] 
 ![![223, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![132, 0, 0, 0, 1]] where
  M :=![![![43, 56, 42, 2, -6], ![-36, -47, -32, 0, 4], ![24, 24, 13, -4, 0], ![0, 24, 20, 13, -8], ![-36, -72, -48, -16, 13]]]
  hmulB := by decide  
  f := ![![![85, 184, 142, 38, 6]], ![![52, 113, 88, 24, 4]], ![![7, 16, 15, 6, 2]], ![![16, 40, 44, 21, 8]], ![![72, 168, 160, 64, 21]]]
  g := ![![![-33, 56, 42, 2, -6], ![28, -47, -32, 0, 4], ![-15, 24, 13, -4, 0], ![-12, 24, 20, 13, -8], ![40, -72, -48, -16, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N3 : Nat.card (O ⧸ I223N3) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N3)

lemma isPrimeI223N3 : Ideal.IsPrime I223N3 := prime_ideal_of_norm_prime hp223.out _ NI223N3
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-533, -653, -467, -28, 70]] ![![65, 75, 54, 3, -8]]
  ![![-20701, -25312, -18083, -1063, 2704]] where
 M := ![![![-20701, -25312, -18083, -1063, 2704]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-20701, -25312, -18083, -1063, 2704]] ![![83, 103, 75, 6, -10]]
  ![![-964931, -1179285, -842432, -49235, 125850]] where
 M := ![![![-964931, -1179285, -842432, -49235, 125850]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N2 : IdealMulLeCertificate' Table 
  ![![-964931, -1179285, -842432, -49235, 125850]] ![![43, 56, 42, 2, -6]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-23786741, -29070949, -20767098, -1213789, 3102376]]]
 hmul := by decide  
 g := ![![![![-106667, -130363, -93126, -5443, 13912]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1181, 1445, 1031, 60, -154]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![1181, 1445, 1031, 60, -154]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![20, 56, 1, 0, 0], ![15, 62, 0, 1, 0], ![51, 173, 0, 0, 1]] where
  M :=![![![1181, 1445, 1031, 60, -154], ![-924, -1129, -805, -47, 120], ![720, 876, 624, 35, -94], ![-564, -690, -499, -34, 70], ![-150, -195, -149, -22, 13]]]
  hmulB := by decide  
  f := ![![![-29, 35, 95, 6, -12]], ![![-72, -209, -139, 11, 12]], ![![-20, -48, -26, 3, 2]], ![![-21, -53, -30, 4, 2]], ![![-63, -155, -87, 9, 7]]]
  g := ![![![-55, -147, 1031, 60, -154], ![43, 115, -805, -47, 120], ![-33, -88, 624, 35, -94], ![28, 76, -499, -34, 70], ![11, 32, -149, -22, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [86, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 226], [0, 1]]
 g := ![![[175, 59], [179, 225], [155], [175], [122], [171, 4], [159, 1]], ![[22, 168], [88, 2], [155], [175], [122], [126, 223], [91, 226]]]
 h' := ![![[159, 226], [42, 112], [218, 212], [137, 137], [81, 185], [49, 24], [173, 225], [0, 1]], ![[0, 1], [144, 115], [103, 15], [128, 90], [213, 42], [6, 203], [82, 2], [159, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [119, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [86, 68, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4093, 13824, 23419, 14025, 8639]
  a := ![-1, 0, -4, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4913, -16131, 23419, 14025, 8639]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-247, -301, -215, -12, 32]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-247, -301, -215, -12, 32]] 
 ![![227, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![191, 0, 1, 0, 0], ![216, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-247, -301, -215, -12, 32], ![192, 233, 167, 9, -24], ![-144, -168, -118, -1, 18], ![108, 126, 101, 8, -2], ![66, 123, 111, 44, -1]]]
  hmulB := by decide  
  f := ![![![-4073, -6931, -1959, 266, 214]], ![![-102, -187, -67, 5, 8]], ![![-3413, -5791, -1619, 225, 176]], ![![-3900, -6642, -1883, 254, 206]], ![![-915, -1572, -460, 58, 51]]]
  g := ![![![192, -301, -215, -12, 32], ![-149, 233, 167, 9, -24], ![100, -168, -118, -1, 18], ![-95, 126, 101, 8, -2], ![-138, 123, 111, 44, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![145, 174, 122, 4, -20]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![145, 174, 122, 4, -20]] 
 ![![227, 0, 0, 0, 0], ![31, 1, 0, 0, 0], ![174, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![211, 0, 0, 0, 1]] where
  M :=![![![145, 174, 122, 4, -20], ![-120, -155, -122, -18, 8], ![48, 0, -53, -66, -36], ![-216, -492, -606, -305, -132], ![-420, -1098, -1362, -732, -287]]]
  hmulB := by decide  
  f := ![![![9299, 6966, -7366, -1700, 1252]], ![![1303, 1075, -900, -226, 156]], ![![7038, 5148, -5741, -1302, 972]], ![![2286, 1752, -1758, -413, 300]], ![![8695, 6624, -6740, -1576, 1149]]]
  g := ![![![-99, 174, 122, 4, -20], ![111, -155, -122, -18, 8], ![90, 0, -53, -66, -36], ![726, -492, -606, -305, -132], ![1633, -1098, -1362, -732, -287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2

def I227N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 8, 5, 1, -2]] i)))

def SI227N3: IdealEqSpanCertificate' Table ![![5, 8, 5, 1, -2]] 
 ![![227, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![204, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![201, 0, 0, 0, 1]] where
  M :=![![![5, 8, 5, 1, -2], ![-12, -25, -21, -9, 2], ![12, 18, -4, -7, -18], ![-108, -258, -259, -130, -14], ![-48, -168, -297, -175, -121]]]
  hmulB := by decide  
  f := ![![![2383, 4100, 1469, -105, -178]], ![![1402, 2419, 873, -61, -106]], ![![2136, 3666, 1306, -95, -158]], ![![1387, 2390, 858, -61, -104]], ![![2109, 3636, 1310, -92, -159]]]
  g := ![![![-8, 8, 5, 1, -2], ![37, -25, -21, -9, 2], ![13, 18, -4, -7, -18], ![472, -258, -259, -130, -14], ![574, -168, -297, -175, -121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N3 : Nat.card (O ⧸ I227N3) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N3)

lemma isPrimeI227N3 : Ideal.IsPrime I227N3 := prime_ideal_of_norm_prime hp227.out _ NI227N3
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![1181, 1445, 1031, 60, -154]] ![![-247, -301, -215, -12, 32]]
  ![![-166415, -203386, -145292, -8494, 21704]] where
 M := ![![![-166415, -203386, -145292, -8494, 21704]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![-166415, -203386, -145292, -8494, 21704]] ![![145, 174, 122, 4, -20]]
  ![![-13978847, -17083324, -12202546, -712098, 1823884]] where
 M := ![![![-13978847, -17083324, -12202546, -712098, 1823884]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N2 : IdealMulLeCertificate' Table 
  ![![-13978847, -17083324, -12202546, -712098, 1823884]] ![![5, 8, 5, 1, -2]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-21964747, -27084732, -19594413, -1418069, 2716282]]]
 hmul := by decide  
 g := ![![![![-96761, -119316, -86319, -6247, 11966]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -60, 46, 12, -8]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-71, -60, 46, 12, -8]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![20, 13, 1, 0, 0], ![198, 80, 0, 1, 0], ![106, 145, 0, 0, 1]] where
  M :=![![![-71, -60, 46, 12, -8], ![-48, -191, -168, -10, 24], ![144, 312, 159, 0, -20], ![-120, -156, 12, 19, 0], ![-72, -216, -148, 6, 29]]]
  hmulB := by decide  
  f := ![![![-563, -660, -474, -12, 64]], ![![384, 397, 288, -26, -24]], ![![-28, -35, -25, -2, 4]], ![![-354, -436, -312, -21, 48]], ![![-14, -47, -32, -20, 13]]]
  g := ![![![-11, -2, 46, 12, -8], ![12, -3, -168, -10, 24], ![-4, 5, 159, 0, -20], ![-18, -8, 12, 19, 0], ![-6, -13, -148, 6, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [210, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [221, 228], [0, 1]]
 g := ![![[96, 12], [103], [216, 42], [146], [159], [35, 19], [221, 1]], ![[0, 217], [103], [109, 187], [146], [159], [112, 210], [213, 228]]]
 h' := ![![[221, 228], [220, 142], [211, 164], [117, 202], [70, 157], [207, 56], [77, 83], [0, 1]], ![[0, 1], [0, 87], [44, 65], [104, 27], [188, 72], [217, 173], [100, 146], [221, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157]]
 b := ![[], [85, 193]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [210, 8, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7590, -16608, -10872, -4292, 4220]
  a := ![0, 0, 4, -10, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2674, -628, -10872, -4292, 4220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, -1105, -1813, -188, 270]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![187, -1105, -1813, -188, 270]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![150, 107, 1, 0, 0], ![209, 151, 0, 1, 0], ![50, 102, 0, 0, 1]] where
  M :=![![![187, -1105, -1813, -188, 270], ![1620, 4237, 2757, 77, -376], ![-2256, -4020, -1326, 125, 154], ![924, 54, -1585, -248, 250], ![1878, 4347, 2441, 20, -325]]]
  hmulB := by decide  
  f := ![![![-749, -881, -619, -10, 96]], ![![576, 691, 549, 53, -20]], ![![-222, -253, -147, 20, 54]], ![![-301, -342, -193, 31, 78]], ![![104, 143, 141, 38, 17]]]
  g := ![![![1301, 846, -1813, -188, 270], ![-1787, -1153, 2757, 77, -376], ![711, 451, -1326, 125, 154], ![1214, 793, -1585, -248, 250], ![-1538, -990, 2441, 20, -325]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P1 : CertificateIrreducibleZModOfList' 229 2 2 7 [139, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [159, 228], [0, 1]]
 g := ![![[101, 135], [135], [186, 3], [82], [192], [176, 14], [159, 1]], ![[40, 94], [135], [205, 226], [82], [192], [112, 215], [89, 228]]]
 h' := ![![[159, 228], [84, 140], [23, 89], [123, 158], [23, 178], [39, 110], [112, 181], [0, 1]], ![[0, 1], [131, 89], [205, 140], [55, 71], [158, 51], [125, 119], [37, 48], [159, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [10, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N1 : CertifiedPrimeIdeal' SI229N1 229 where
  n := 2
  hpos := by decide
  P := [139, 70, 1]
  hirr := P229P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4464, 10194, 16056, 9527, 5077]
  a := ![13, -1, -3, 1, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20301, -16001, 16056, 9527, 5077]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N1 B_one_repr
lemma NI229N1 : Nat.card (O ⧸ I229N1) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-425, -523, -375, -22, 56]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-425, -523, -375, -22, 56]] 
 ![![229, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![-425, -523, -375, -22, 56], ![336, 415, 295, 17, -44], ![-264, -324, -228, -13, 34], ![204, 246, 173, 10, -26], ![54, 69, 47, 2, -7]]]
  hmulB := by decide  
  f := ![![![-113, -251, -157, -32, 30]], ![![-53, -118, -74, -15, 14]], ![![-15, -33, -21, -5, 4]], ![![-14, -32, -21, -4, 2]], ![![-46, -103, -69, -18, 11]]]
  g := ![![![275, -523, -375, -22, 56], ![-218, 415, 295, 17, -44], ![170, -324, -228, -13, 34], ![-129, 246, 173, 10, -26], ![-36, 69, 47, 2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-71, -60, 46, 12, -8]] ![![187, -1105, -1813, -188, 270]]
  ![![-218189, -394813, -136241, 11342, 16074]] where
 M := ![![![-218189, -394813, -136241, 11342, 16074]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-218189, -394813, -136241, 11342, 16074]] ![![-425, -523, -375, -22, 56]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-777455, -1693226, -868368, 5038, 113584]]]
 hmul := by decide  
 g := ![![![![-3395, -7394, -3792, 22, 496]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![233, 0, 0, 0, 0]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![233, 0, 0, 0, 0]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![0, 0, 0, 0, 233]] where
  M :=![![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![0, 0, 0, 233, 0], ![0, 0, 0, 0, 233]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 5 2 7 [31, 121, 100, 113, 157, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [201, 214, 86, 224, 178], [21, 208, 228, 52, 202], [37, 196, 177, 28, 195], [50, 80, 208, 162, 124], [0, 1]]
 g := ![![[219, 152, 177, 174, 226], [72, 230, 134, 144], [123, 1, 177, 121], [120, 97, 208, 144, 30], [158, 108, 189, 201], [71, 76, 1], []], ![[180, 111, 77, 100, 81, 225, 42, 26], [137, 43, 13, 102], [164, 44, 228, 169], [224, 124, 199, 231, 145, 228, 167, 9], [121, 85, 217, 167], [183, 118, 210, 36, 84, 108, 106, 89], [207, 56, 57, 196, 149, 111, 52, 220]], ![[197, 133, 49, 104, 185, 33, 49, 162], [126, 151, 113, 175], [18, 129, 127, 109], [69, 101, 62, 20, 114, 127, 54, 32], [65, 2, 1, 89], [47, 81, 230, 131, 45, 155, 31, 15], [119, 195, 189, 32, 211, 128, 42, 33]], ![[82, 203, 44, 81, 182, 78, 148, 201], [108, 143, 73, 210], [132, 0, 178, 51], [174, 202, 200, 73, 162, 96, 13, 33], [62, 231, 184, 175], [100, 48, 159, 57, 186, 193, 190, 217], [147, 35, 86, 37, 175, 222, 98, 116]], ![[13, 3, 109, 223, 22, 45, 94, 55], [158, 137, 120, 72], [95, 196, 50, 220], [7, 32, 193, 83, 197, 92, 173, 51], [35, 196, 164, 101], [60, 93, 188, 21, 68, 142, 37, 107], [112, 185, 101, 101, 117, 74, 218, 218]]]
 h' := ![![[201, 214, 86, 224, 178], [73, 137, 185, 86, 61], [212, 80, 86, 35, 12], [8, 209, 11, 124, 222], [93, 2, 47, 64, 27], [129, 4, 216, 100, 203], [0, 0, 0, 1], [0, 1]], ![[21, 208, 228, 52, 202], [70, 98, 126, 101, 63], [194, 32, 230, 133, 175], [102, 63, 44, 160, 13], [147, 18, 232, 221, 132], [183, 102, 230, 108, 213], [192, 127, 146, 63, 159], [201, 214, 86, 224, 178]], ![[37, 196, 177, 28, 195], [172, 21, 25, 9, 10], [159, 136, 61, 139, 116], [211, 116, 47, 67, 153], [194, 101, 184, 28, 125], [186, 217, 70, 36, 97], [213, 71, 27, 230, 218], [21, 208, 228, 52, 202]], ![[50, 80, 208, 162, 124], [14, 148, 52, 206, 71], [223, 201, 138, 77, 207], [11, 195, 156, 26, 135], [175, 16, 214, 222, 172], [0, 61, 0, 165, 117], [195, 191, 90, 101, 128], [37, 196, 177, 28, 195]], ![[0, 1], [41, 62, 78, 64, 28], [38, 17, 184, 82, 189], [120, 116, 208, 89, 176], [161, 96, 22, 164, 10], [224, 82, 183, 57, 69], [135, 77, 203, 71, 194], [50, 80, 208, 162, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [214, 201, 95, 54], [], [], []]
 b := ![[], [200, 27, 192, 199, 73], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 5
  hpos := by decide
  P := [31, 121, 100, 113, 157, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![316573634591, 859399807503, 1102480938351, 602929558830, 254890747032]
  a := ![-1, -3, 2, -1, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1358685127, 3688411191, 4731677847, 2587680510, 1093951704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 686719856393 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def PBC233 : ContainsPrimesAboveP 233 ![I233N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![233, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 233 (by decide) 𝕀

instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11425, 13950, 9966, 576, -1486]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![11425, 13950, 9966, 576, -1486]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![171, 117, 114, 1, 0], ![52, 228, 14, 0, 1]] where
  M :=![![![11425, 13950, 9966, 576, -1486], ![-8916, -10865, -7764, -436, 1152], ![6912, 8364, 5979, 300, -872], ![-5232, -6168, -4416, -125, 600], ![-1656, -2298, -1636, -258, 311]]]
  hmulB := by decide  
  f := ![![![-73, -258, -214, -12, 30]], ![![180, 377, 180, -4, -24]], ![![-144, -180, 13, 12, -8]], ![![-33, -87, -60, -5, 6]], ![![148, 294, 126, -6, -17]]]
  g := ![![![-41, 1194, -146, 576, -1486], ![24, -931, 108, -436, 1152], ![4, 720, -67, 300, -872], ![-63, -537, 6, -125, 600], ![110, -180, 98, -258, 311]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [195, 56, 196, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [122, 236, 109], [160, 2, 130], [0, 1]]
 g := ![![[144, 62, 96], [175, 188, 213], [204, 165, 110], [10, 173, 32], [60, 71], [202, 123, 176], [1]], ![[34, 96, 92, 54], [178, 162, 98, 201], [94, 155, 168, 201], [57, 64, 122, 182], [0, 142], [18, 238, 86, 64], [189, 34, 107, 127]], ![[78, 131, 103, 238], [30, 11, 13, 118], [150, 88, 57, 94], [63, 163, 11, 229], [95, 17], [84, 233], [148, 167, 100, 112]]]
 h' := ![![[122, 236, 109], [52, 148, 88], [133, 148, 90], [201, 201, 189], [124, 70, 157], [45, 99, 73], [44, 183, 43], [0, 1]], ![[160, 2, 130], [200, 13, 56], [113, 94, 60], [4, 1, 60], [17, 54, 57], [16, 150, 182], [116, 117, 196], [122, 236, 109]], ![[0, 1], [189, 78, 95], [88, 236, 89], [105, 37, 229], [144, 115, 25], [160, 229, 223], [77, 178], [160, 2, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 218], []]
 b := ![[], [103, 160, 237], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [195, 56, 196, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4436478, 13523934, 20607057, 11776306, 6860851]
  a := ![3, 0, 7, -4, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9899900, -12253464, -5932819, 11776306, 6860851]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73, -258, -214, -12, 30]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![-73, -258, -214, -12, 30]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![197, 125, 1, 0, 0], ![231, 107, 0, 1, 0], ![117, 177, 0, 0, 1]] where
  M :=![![![-73, -258, -214, -12, 30], ![180, 377, 180, -4, -24], ![-144, -180, 13, 12, -8], ![-48, -264, -288, -43, 24], ![144, 246, 20, -66, -39]]]
  hmulB := by decide  
  f := ![![![11425, 13950, 9966, 576, -1486]], ![![-8916, -10865, -7764, -436, 1152]], ![![4783, 5851, 4179, 248, -626]], ![![7029, 8593, 6138, 361, -918]], ![![-1017, -1227, -878, -42, 127]]]
  g := ![![![173, 94, -214, -12, 30], ![-132, -73, 180, -4, -24], ![-19, -7, 13, 12, -8], ![267, 151, -288, -43, 24], ![67, 49, 20, -66, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P1 : CertificateIrreducibleZModOfList' 239 2 2 7 [211, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [211, 238], [0, 1]]
 g := ![![[238, 128], [75, 204], [19, 22], [185, 116], [62], [99, 182], [211, 1]], ![[0, 111], [99, 35], [120, 217], [44, 123], [62], [22, 57], [183, 238]]]
 h' := ![![[211, 238], [188, 75], [54, 193], [161, 71], [197, 127], [143, 121], [172, 95], [0, 1]], ![[0, 1], [0, 164], [147, 46], [85, 168], [226, 112], [101, 118], [141, 144], [211, 238]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [112, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N1 : CertifiedPrimeIdeal' SI239N1 239 where
  n := 2
  hpos := by decide
  P := [211, 28, 1]
  hirr := P239P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1662, 4692, 7743, 4439, 2989]
  a := ![1, 1, 2, -1, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12129, -8231, 7743, 4439, 2989]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N1 B_one_repr
lemma NI239N1 : Nat.card (O ⧸ I239N1) = 57121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N1
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![11425, 13950, 9966, 576, -1486]] ![![-73, -258, -214, -12, 30]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [178, 76, 186, 172, 190, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [131, 39, 186, 180, 15], [131, 165, 239, 174, 70], [231, 190, 186, 141, 239], [40, 87, 112, 228, 158], [0, 1]]
 g := ![![[201, 147, 37, 62, 232], [43, 231, 240, 108], [63, 173, 113, 100], [230, 1, 138, 4], [5, 6, 22, 69, 91], [19, 51, 1], []], ![[228, 168, 87, 126, 46, 40, 98, 61], [63, 172, 233, 80], [165, 228, 120, 123], [34, 132, 73, 12], [217, 169, 216, 54, 166, 7, 132, 120], [148, 185, 71, 233, 96, 42, 218, 48], [184, 125, 29, 88, 21, 107, 87, 1]], ![[60, 137, 205, 95, 186, 156, 212, 52], [36, 89, 219, 187], [24, 92, 126, 2], [70, 35, 179, 121], [236, 87, 135, 234, 122, 69, 207, 155], [129, 181, 172, 61, 35, 49, 107, 228], [43, 49, 82, 147, 113, 62, 82, 57]], ![[62, 184, 120, 227, 10, 192, 197, 174], [114, 213, 62, 87], [220, 86, 194, 177], [166, 100, 129, 61], [18, 133, 94, 170, 199, 162, 39, 183], [3, 108, 111, 83, 165, 211, 204, 12], [126, 189, 77, 234, 12, 175, 79, 233]], ![[179, 140, 65, 58, 160, 180, 149, 123], [117, 67, 26, 5], [9, 227, 67, 177], [8, 210, 107, 50], [234, 189, 175, 38, 51, 89, 230, 134], [52, 163, 29, 146, 80, 148, 108, 174], [229, 55, 49, 116, 97, 154, 148, 106]]]
 h' := ![![[131, 39, 186, 180, 15], [149, 142, 171, 175, 49], [36, 190, 71, 81, 146], [204, 194, 118, 165, 231], [74, 62, 134, 137, 239], [233, 82, 124, 184, 205], [0, 0, 0, 1], [0, 1]], ![[131, 165, 239, 174, 70], [140, 140, 104, 9, 62], [73, 118, 105, 222, 171], [139, 6, 216, 108, 169], [86, 76, 1, 25, 129], [185, 9, 142, 36, 44], [67, 223, 54, 123, 14], [131, 39, 186, 180, 15]], ![[231, 190, 186, 141, 239], [12, 182, 26, 97, 155], [201, 127, 85, 32, 118], [193, 148, 158, 132, 22], [11, 225, 119, 122, 11], [160, 75, 84, 13, 181], [101, 228, 122, 149, 101], [131, 165, 239, 174, 70]], ![[40, 87, 112, 228, 158], [1, 72, 75, 158, 201], [7, 27, 4, 126, 150], [208, 73, 69, 146, 30], [178, 131, 153, 234, 213], [207, 78, 164, 73, 149], [190, 45, 10, 206, 41], [231, 190, 186, 141, 239]], ![[0, 1], [69, 187, 106, 43, 15], [13, 20, 217, 21, 138], [13, 61, 162, 172, 30], [192, 229, 75, 205, 131], [96, 238, 209, 176, 144], [102, 227, 55, 3, 85], [40, 87, 112, 228, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150, 191, 106, 157], [], [], []]
 b := ![[], [223, 91, 155, 90, 102], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [178, 76, 186, 172, 190, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2687632, 16611648, 73166877, 48280735, 50211145]
  a := ![4, 0, -1, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11152, 68928, 303597, 200335, 208345]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10501, 13082, 9334, 690, -1460]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![10501, 13082, 9334, 690, -1460]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![201, 208, 192, 15, 1]] where
  M :=![![![10501, 13082, 9334, 690, -1460], ![-8760, -11399, -8128, -886, 1380], ![8280, 11940, 8415, 1532, -1772], ![-10632, -18300, -13108, -3989, 3064], ![5052, 11694, 7628, 3404, -3103]]]
  hmulB := by decide  
  f := ![![![-385, -1102, -782, -30, 108]], ![![648, 1235, 488, -26, -60]], ![![-360, -252, 309, 68, -52]], ![![-312, -1140, -964, -55, 136]], ![![-63, -116, -42, 3, 5]]]
  g := ![![![1211, 1262, 1154, 90, -1460], ![-1140, -1189, -1088, -86, 1380], ![1452, 1516, 1389, 112, -1772], ![-2496, -2612, -2396, -199, 3064], ![2505, 2618, 2404, 199, -3103]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 4 2 7 [36, 96, 112, 91, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 203, 12, 18], [99, 60, 80, 243], [2, 238, 159, 241], [0, 1]]
 g := ![![[89, 118, 151, 39], [138, 180, 221, 121], [6, 135, 135], [209, 112, 100, 245], [134, 231, 175, 152], [139, 137, 160, 1], []], ![[15, 5, 143, 1, 156, 29], [166, 117, 212, 130, 60, 215], [55, 92, 198], [242, 142, 96, 74, 2, 10], [57, 83, 229, 232, 53, 19], [148, 239, 141, 235, 135, 130], [119, 49, 135, 131, 20, 59]], ![[221, 197, 5, 138, 67, 68], [187, 166, 153, 187, 9, 63], [66, 4, 181], [156, 74, 153, 94, 24, 154], [246, 19, 117, 191, 71, 164], [184, 133, 101, 20, 95, 66], [201, 152, 232, 181, 206, 241]], ![[95, 249, 129, 68, 70, 121], [67, 206, 38, 82, 104, 3], [53, 226, 154], [95, 224, 121, 145, 201, 92], [2, 182, 26, 108, 17, 103], [133, 240, 14, 3, 127, 124], [5, 124, 104, 97, 148, 4]]]
 h' := ![![[59, 203, 12, 18], [52, 122, 198, 164], [71, 242, 77, 11], [6, 13, 111, 117], [196, 160, 188, 139], [16, 47, 158, 34], [0, 0, 0, 1], [0, 1]], ![[99, 60, 80, 243], [92, 57, 246, 197], [235, 139, 102, 91], [61, 123, 89, 82], [63, 127, 247, 89], [213, 10, 60, 212], [44, 98, 200, 125], [59, 203, 12, 18]], ![[2, 238, 159, 241], [45, 168, 63, 86], [0, 55, 115, 20], [165, 16, 141, 159], [153, 197, 58, 238], [200, 5, 190, 132], [227, 233, 34, 96], [99, 60, 80, 243]], ![[0, 1], [63, 155, 246, 55], [46, 66, 208, 129], [166, 99, 161, 144], [6, 18, 9, 36], [164, 189, 94, 124], [79, 171, 17, 29], [2, 238, 159, 241]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [176, 132, 185], []]
 b := ![[], [], [7, 160, 250, 180], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 4
  hpos := by decide
  P := [36, 96, 112, 91, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2944925173752, 7988341246620, 10234502528010, 5595003575558, 2357635065064]
  a := ![7, 2, -24, 0, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1876253876112, -1921911363692, -1762675019778, -118603674902, 2357635065064]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 3969126001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-385, -1102, -782, -30, 108]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![-385, -1102, -782, -30, 108]] 
 ![![251, 0, 0, 0, 0], ![221, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![108, 0, 0, 1, 0], ![62, 0, 0, 0, 1]] where
  M :=![![![-385, -1102, -782, -30, 108], ![648, 1235, 488, -26, -60], ![-360, -252, 309, 68, -52], ![-312, -1140, -964, -55, 136], ![588, 990, 268, -40, -29]]]
  hmulB := by decide  
  f := ![![![10501, 13082, 9334, 690, -1460]], ![![9211, 11473, 8186, 604, -1280]], ![![4384, 5468, 3901, 292, -612]], ![![4476, 5556, 3964, 281, -616]], ![![2614, 3278, 2336, 184, -373]]]
  g := ![![![1279, -1102, -782, -30, 108], ![-1261, 1235, 488, -26, -60], ![76, -252, 309, 68, -52], ![1392, -1140, -964, -55, 136], ![-956, 990, 268, -40, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![10501, 13082, 9334, 690, -1460]] ![![-385, -1102, -782, -30, 108]]
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


lemma PB441I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB441I5 : PrimesBelowBoundCertificateInterval O 197 251 441 where
  m := 9
  g := ![2, 2, 4, 4, 3, 1, 2, 1, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB441I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2, I223N3]
    · exact ![I227N0, I227N1, I227N2, I227N3]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0]
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
    · exact ![9393931, 44521]
    · exact ![49729, 223, 223, 223]
    · exact ![51529, 227, 227, 227]
    · exact ![52441, 52441, 229]
    · exact ![686719856393]
    · exact ![13651919, 57121]
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
  β := ![I199N1, I223N1, I223N2, I223N3, I227N1, I227N2, I227N3, I229N2, I251N1]
  Il := ![[I199N1], [], [I223N1, I223N2, I223N3], [I227N1, I227N2, I227N3], [I229N2], [], [], [], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
