
import IdealArithmetic.Examples.NF5_1_15000000_1.RI5_1_15000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, -381, 237, 476, -346]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![95, -381, 237, 476, -346]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![0, 0, 0, 199, 0], ![197, 96, 39, 101, 1]] where
  M :=![![![95, -381, 237, 476, -346], ![3114, 1370, -1421, -1042, 1428], ![-12852, -2591, 3854, 684, -3126], ![12681, 1048, -2808, 1086, 1719], ![-987, 1407, -753, -1797, 1190]]]
  hmulB := by decide  
  f := ![![![-67, -35, 13, 24, 22]], ![![-198, -120, 33, 70, 72]], ![![-648, -381, 92, 208, 210]], ![![-99, -76, 2, 24, 33]], ![![-341, -207, 48, 111, 115]]]
  g := ![![![343, 165, 69, 178, -346], ![-1398, -682, -287, -730, 1428], ![3030, 1495, 632, 1590, -3126], ![-1638, -824, -351, -867, 1719], ![-1183, -567, -237, -613, 1190]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 4 2 7 [127, 144, 51, 182, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [181, 20, 56, 121], [95, 29, 193, 41], [139, 149, 149, 37], [0, 1]]
 g := ![![[149, 149, 60, 91], [55, 183, 40, 4], [118, 182, 23, 100], [163, 56, 16], [163, 20, 112], [39, 17, 1], []], ![[4, 21, 80, 69, 98, 43], [82, 190, 103, 57, 183, 86], [131, 197, 111, 17, 60, 25], [114, 41, 1], [132, 174, 29], [149, 52, 40], [147, 152, 132, 52, 124, 63]], ![[117, 48, 110, 94, 108, 174], [141, 43, 168, 114, 191, 147], [13, 127, 131, 44, 7, 152], [155, 36, 188], [97, 55, 80], [105, 177, 66], [168, 6, 177, 87, 134, 67]], ![[154, 121, 114, 23, 84, 136], [32, 82, 68, 102, 37, 55], [45, 36, 34, 163, 140, 37], [101, 176, 18], [87, 198, 144], [144, 9, 26], [63, 198, 98, 14, 46, 107]]]
 h' := ![![[181, 20, 56, 121], [179, 22, 74, 115], [138, 14, 192, 2], [188, 49, 145, 10], [81, 38, 27, 195], [22, 185, 13, 50], [0, 0, 0, 1], [0, 1]], ![[95, 29, 193, 41], [128, 59, 35, 20], [187, 20, 154, 197], [81, 116, 43, 109], [80, 60, 12, 1], [160, 8, 23, 32], [175, 62, 16, 55], [181, 20, 56, 121]], ![[139, 149, 149, 37], [25, 161, 168, 155], [157, 167, 130, 53], [56, 37, 196, 81], [55, 44, 76, 63], [6, 108, 8, 105], [40, 41, 151, 128], [95, 29, 193, 41]], ![[0, 1], [155, 156, 121, 108], [172, 197, 121, 146], [12, 196, 14, 198], [74, 57, 84, 139], [175, 97, 155, 12], [73, 96, 32, 15], [139, 149, 149, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [186, 56, 127], []]
 b := ![[], [], [53, 57, 162, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 4
  hpos := by decide
  P := [127, 144, 51, 182, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-453600863, -485373450, -100605590, 15748908, -59552310]
  a := ![0, -8, -7, -7, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![56674393, 26289690, 11165500, 30304182, -59552310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 1568239201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, -35, 13, 24, 22]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-67, -35, 13, 24, 22]] 
 ![![199, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![129, 0, 1, 0, 0], ![32, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-67, -35, 13, 24, 22], ![-198, -120, 33, 70, 72], ![-648, -381, 92, 208, 210], ![-99, -76, 2, 24, 33], ![-381, -243, 33, 105, 116]]]
  hmulB := by decide  
  f := ![![![95, -381, 237, 476, -346]], ![![61, -175, 106, 222, -158]], ![![-3, -260, 173, 312, -240]], ![![79, -56, 24, 82, -47]], ![![17, -81, 51, 101, -74]]]
  g := ![![![-1, -35, 13, 24, 22], ![7, -120, 33, 70, 72], ![37, -381, 92, 208, 210], ![23, -76, 2, 24, 33], ![49, -243, 33, 105, 116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![95, -381, 237, 476, -346]] ![![-67, -35, 13, 24, 22]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4679, -688, -712, -524, 1036]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![4679, -688, -712, -524, 1036]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![120, 197, 104, 1, 0], ![109, 178, 201, 0, 1]] where
  M :=![![![4679, -688, -712, -524, 1036], ![-9324, 859, 1520, 1308, -1572], ![14148, -3088, -2125, -1252, 3924], ![-13572, 1392, 2104, 1743, -2508], ![3192, -1416, -528, -120, 1379]]]
  hmulB := by decide  
  f := ![![![197, 304, -232, -316, 284]], ![![-2556, -887, 1008, 556, -948]], ![![8532, 1296, -2271, 76, 1668]], ![![1896, -17, -304, 371, 96]], ![![6071, 638, -1429, 384, 931]]]
  g := ![![![-215, -388, -732, -524, 1036], ![24, 109, 860, 1308, -1572], ![-1248, -2156, -3131, -1252, 3924], ![240, 495, 1540, 1743, -2508], ![-629, -1058, -1257, -120, 1379]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [132, 88, 139, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 143, 209], [71, 67, 2], [0, 1]]
 g := ![![[203, 172, 14], [169, 170, 150], [52, 83], [45, 79], [81, 2, 105], [188, 120], [1]], ![[139, 3, 67, 119], [64, 185, 88, 180], [166, 204], [124, 182], [96, 97, 176, 193], [187, 87], [156, 192, 85, 203]], ![[38, 157, 60, 42], [137, 59, 18, 128], [166, 47], [150, 189], [112, 14, 190, 153], [188, 64], [104, 53, 114, 8]]]
 h' := ![![[1, 143, 209], [58, 155, 15], [72, 9, 19], [87, 59, 100], [69, 42, 76], [204, 132, 152], [79, 123, 72], [0, 1]], ![[71, 67, 2], [22, 111, 62], [36, 163, 200], [209, 178, 41], [142, 33, 155], [187, 178, 3], [87, 181, 147], [1, 143, 209]], ![[0, 1], [75, 156, 134], [114, 39, 203], [90, 185, 70], [30, 136, 191], [158, 112, 56], [42, 118, 203], [71, 67, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [199, 84], []]
 b := ![[], [108, 163, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [132, 88, 139, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3582887388, 2218639834, -353904778, -1036360546, -1248595900]
  a := ![3, -61, -63, -66, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1251389128, 2031430036, 1698556246, -1036360546, -1248595900]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![197, 304, -232, -316, 284]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![197, 304, -232, -316, 284]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![111, 8, 1, 0, 0], ![39, 8, 0, 1, 0], ![189, 70, 0, 0, 1]] where
  M :=![![![197, 304, -232, -316, 284], ![-2556, -887, 1008, 556, -948], ![8532, 1296, -2271, 76, 1668], ![-7380, -112, 1304, -1235, -540], ![-456, -1128, 816, 1224, -1039]]]
  hmulB := by decide  
  f := ![![![4679, -688, -712, -524, 1036]], ![![-9324, 859, 1520, 1308, -1572]], ![![2175, -344, -327, -232, 504]], ![![447, -88, -64, -39, 120]], ![![1113, -338, -136, -36, 413]]]
  g := ![![![-73, -72, -232, -316, 284], ![204, 251, 1008, 556, -948], ![-273, -464, -2271, 76, 1668], ![-9, 176, 1304, -1235, -540], ![273, 262, 816, 1224, -1039]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [155, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 210], [0, 1]]
 g := ![![[32, 100], [45, 62], [64], [99], [195, 95], [83], [104, 1]], ![[93, 111], [163, 149], [64], [99], [158, 116], [83], [208, 210]]]
 h' := ![![[104, 210], [199, 10], [147, 22], [19, 203], [159, 164], [99, 112], [127, 111], [0, 1]], ![[0, 1], [184, 201], [114, 189], [31, 8], [124, 47], [142, 99], [66, 100], [104, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [76, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [155, 107, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16234, -9889, 3393, 5965, 2325]
  a := ![1, -6, -6, -7, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5047, -1173, 3393, 5965, 2325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![4679, -688, -712, -524, 1036]] ![![197, 304, -232, -316, 284]]
  ![![211, 0, 0, 0, 0]] where
 M := ![![![211, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37556, 4848, 5908, 4619, -7603]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-37556, 4848, 5908, 4619, -7603]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![88, 192, 48, 1, 0], ![76, 76, 29, 0, 1]] where
  M :=![![![-37556, 4848, 5908, 4619, -7603], ![68427, -8839, -10764, -8415, 13857], ![-124713, 16092, 19619, 15345, -25245], ![102051, -13176, -16056, -12556, 20667], ![-35538, 4578, 5592, 4374, -7193]]]
  hmulB := by decide  
  f := ![![![40, 30, -8, -19, -11]], ![![99, 65, 0, -27, -57]], ![![513, 270, -79, -117, -81]], ![![211, 126, -20, -56, -71]], ![![115, 68, -13, -31, -34]]]
  g := ![![![600, -1364, 21, 4619, -7603], ![-1095, 2483, -39, -8415, 13857], ![1989, -4536, 68, 15345, -25245], ![-1631, 3708, -57, -12556, 20667], ![566, -1294, 19, 4374, -7193]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [66, 26, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 147, 21], [143, 75, 202], [0, 1]]
 g := ![![[131, 47, 152], [12, 118, 197], [56, 147, 152], [219, 36, 68], [0, 41, 29], [88, 172], [1]], ![[142, 169, 104, 77], [119, 130, 143, 160], [109, 119, 210, 80], [56, 24, 90, 77], [117, 186, 127, 52], [211, 18], [46, 80, 171, 118]], ![[211, 78, 129, 32], [180, 138, 8, 164], [19, 191, 108, 83], [174, 201, 21, 164], [107, 7, 204, 38], [50, 124], [78, 67, 67, 105]]]
 h' := ![![[51, 147, 21], [100, 33, 179], [95, 112, 33], [41, 181, 44], [0, 32, 115], [109, 50, 156], [157, 197, 194], [0, 1]], ![[143, 75, 202], [106, 209, 69], [96, 210, 144], [22, 29, 188], [212, 0, 154], [151, 170, 39], [52, 143, 178], [51, 147, 21]], ![[0, 1], [101, 204, 198], [137, 124, 46], [91, 13, 214], [172, 191, 177], [166, 3, 28], [212, 106, 74], [143, 75, 202]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 1], []]
 b := ![[], [185, 68, 138], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [66, 26, 29, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-367374430, -220523378, 36053148, 100394276, 126591510]
  a := ![1, 26, 22, 17, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-84408186, -130570310, -37910430, 100394276, 126591510]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-673, 11, 99, 98, -86]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-673, 11, 99, 98, -86]] 
 ![![223, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![180, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![-673, 11, 99, 98, -86], ![774, -316, -147, -58, 294], ![-2646, -255, 330, 410, -174], ![1521, -242, -260, -196, 321], ![-831, -147, 69, 111, -40]]]
  hmulB := by decide  
  f := ![![![-30067, -4439, 7923, -414, -5770]], ![![-16486, -2490, 4381, -162, -3214]], ![![-1433, 6, 235, -272, -80]], ![![-24813, -3870, 6674, -102, -4947]], ![![-15252, -2244, 4014, -219, -2920]]]
  g := ![![![-48, 11, 99, 98, -86], ![79, -316, -147, -58, 294], ![-126, -255, 330, 410, -174], ![144, -242, -260, -196, 321], ![6, -147, 69, 111, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, 11, 11, 8, -16]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-71, 11, 11, 8, -16]] 
 ![![223, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![193, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-71, 11, 11, 8, -16], ![144, -12, -23, -20, 24], ![-216, 49, 34, 20, -60], ![207, -22, -32, -26, 39], ![-51, 21, 9, 3, -20]]]
  hmulB := by decide  
  f := ![![![-149, -127, 99, 116, -104]], ![![-84, -74, 57, 68, -60]], ![![-143, -112, 89, 100, -92]], ![![-43, -46, 34, 44, -37]], ![![-10, -8, 6, 7, -6]]]
  g := ![![![-18, 11, 11, 8, -16], ![33, -12, -23, -20, 24], ![-62, 49, 34, 20, -60], ![48, -22, -32, -26, 39], ![-20, 21, 9, 3, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-37556, 4848, 5908, 4619, -7603]] ![![-673, 11, 99, 98, -86]]
  ![![26738564, -3451781, -4206607, -3288649, 5413955]] where
 M := ![![![26738564, -3451781, -4206607, -3288649, 5413955]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![26738564, -3451781, -4206607, -3288649, 5413955]] ![![-71, 11, 11, 8, -16]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-2443729444, 315465166, 384452892, 300558731, -494799759]]]
 hmul := by decide  
 g := ![![![![-10958428, 1414642, 1724004, 1347797, -2218833]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-513449, 66283, 80777, 63150, -103962]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-513449, 66283, 80777, 63150, -103962]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![54, 201, 93, 1, 0], ![150, 2, 160, 0, 1]] where
  M :=![![![-513449, 66283, 80777, 63150, -103962], ![935658, -120786, -147199, -115078, 189450], ![-1705050, 220109, 268244, 209710, -345234], ![1395387, -180134, -219526, -171622, 282537], ![-485703, 62697, 76413, 59739, -98342]]]
  hmulB := by decide  
  f := ![![![-7, 29, 5, -18, -6]], ![![54, 16, 39, 38, -54]], ![![486, 255, -106, -82, 114]], ![![243, 125, -7, -4, -3]], ![![339, 199, -71, -69, 76]]]
  g := ![![![51413, -54709, 47761, 63150, -103962], ![-93690, 99696, -87035, -115078, 189450], ![170730, -181679, 158602, 209710, -345234], ![-139725, 148682, -129800, -171622, 282537], ![48633, -51754, 45178, 59739, -98342]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 3 2 7 [1, 124, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 121, 171], [205, 105, 56], [0, 1]]
 g := ![![[115, 112, 84], [54, 218, 29], [144, 76], [144, 43], [175, 121], [175, 29, 155], [1]], ![[26, 2, 66, 101], [2, 77, 206, 64], [194, 188], [214, 28], [196, 103], [118, 0, 123, 59], [42, 166, 79, 82]], ![[186, 55, 189, 216], [64, 105, 69, 154], [16, 79], [144, 64], [220, 62], [223, 101, 13, 55], [14, 25, 47, 145]]]
 h' := ![![[112, 121, 171], [173, 215, 159], [186, 209, 16], [199, 126, 168], [32, 44, 66], [52, 64, 216], [226, 103, 90], [0, 1]], ![[205, 105, 56], [46, 30, 115], [167, 224, 191], [208, 61, 142], [60, 80, 153], [16, 219, 28], [210, 153, 50], [112, 121, 171]], ![[0, 1], [96, 209, 180], [48, 21, 20], [219, 40, 144], [96, 103, 8], [61, 171, 210], [7, 198, 87], [205, 105, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [176, 133], []]
 b := ![[], [41, 212, 201], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 3
  hpos := by decide
  P := [1, 124, 137, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9505660, 1648545, -48343, 1600701, -1806975]
  a := ![-1, -6, 1, 10, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![855128, -1394178, 617632, 1600701, -1806975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 11697083 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -29, -5, 18, 6]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![7, -29, -5, 18, 6]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![114, 84, 1, 0, 0], ![46, 209, 0, 1, 0], ![223, 157, 0, 0, 1]] where
  M :=![![![7, -29, -5, 18, 6], ![-54, -16, -39, -38, 54], ![-486, -255, 106, 82, -114], ![513, 122, -160, -52, 105], ![-135, 9, -15, -81, -20]]]
  hmulB := by decide  
  f := ![![![513449, -66283, -80777, -63150, 103962]], ![![-935658, 120786, 147199, 115078, -189450]], ![![-80868, 10439, 12722, 9946, -16374]], ![![-763565, 98570, 120125, 93912, -154605]], ![![-140588, 18148, 22117, 17291, -28466]]]
  g := ![![![-7, -19, -5, 18, 6], ![-26, 12, -39, -38, 54], ![40, -37, 106, 82, -114], ![-10, 35, -160, -52, 105], ![43, 94, -15, -81, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P1 : CertificateIrreducibleZModOfList' 227 2 2 7 [22, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [127, 226], [0, 1]]
 g := ![![[149, 19], [220, 23], [79], [71], [12], [26, 100], [127, 1]], ![[65, 208], [190, 204], [79], [71], [12], [14, 127], [27, 226]]]
 h' := ![![[127, 226], [154, 143], [160, 93], [38, 144], [40, 170], [109, 100], [157, 217], [0, 1]], ![[0, 1], [155, 84], [167, 134], [166, 83], [65, 57], [97, 127], [22, 10], [127, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [73, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N1 : CertifiedPrimeIdeal' SI227N1 227 where
  n := 2
  hpos := by decide
  P := [22, 100, 1]
  hirr := P227P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42574, -2596, -8108, 3248, 7308]
  a := ![0, -2, -14, -36, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3578, -5056, -8108, 3248, 7308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N1 B_one_repr
lemma NI227N1 : Nat.card (O ⧸ I227N1) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-513449, 66283, 80777, 63150, -103962]] ![![7, -29, -5, 18, 6]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-155, -125, 19, 50, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-155, -125, 19, 50, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![203, 112, 179, 1, 0], ![5, 188, 72, 0, 1]] where
  M :=![![![-155, -125, 19, 50, 0], ![0, -136, -137, -24, 150], ![-1350, -587, 64, -50, -72], ![837, 60, -154, 66, -39], ![225, 111, -225, -261, 16]]]
  hmulB := by decide  
  f := ![![![-118235, 15263, 18601, 14542, -23940]], ![![215460, -27814, -33897, -26500, 43626]], ![![-392634, 50685, 61770, 48290, -79500]], ![![-304936, 39364, 47973, 37504, -61743]], ![![50366, -6502, -7924, -6195, 10198]]]
  g := ![![![-45, -25, -39, 50, 0], ![18, -112, -29, -24, 150], ![40, 81, 62, -50, -72], ![-54, 0, -40, 66, -39], ![232, 115, 198, -261, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 3 2 7 [219, 92, 198, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 27, 122], [143, 201, 107], [0, 1]]
 g := ![![[172, 45, 171], [54, 172], [225, 71, 48], [25, 224], [44, 94], [63, 42, 45], [1]], ![[191, 161, 74, 208], [100, 95], [192, 38, 46, 140], [49, 204], [170, 78], [219, 86, 122, 188], [11, 153, 30, 107]], ![[130, 211, 217, 152], [167, 56], [90, 56, 42, 152], [35, 226], [73, 176], [2, 60, 135, 190], [90, 98, 202, 122]]]
 h' := ![![[117, 27, 122], [79, 223, 209], [189, 11, 114], [188, 35, 55], [25, 208, 192], [172, 220, 134], [10, 137, 31], [0, 1]], ![[143, 201, 107], [22, 101, 57], [204, 149, 211], [162, 50, 211], [78, 160, 77], [179, 33, 188], [97, 51, 45], [117, 27, 122]], ![[0, 1], [211, 134, 192], [12, 69, 133], [66, 144, 192], [113, 90, 189], [38, 205, 136], [90, 41, 153], [143, 201, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 44], []]
 b := ![[], [175, 203, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 3
  hpos := by decide
  P := [219, 92, 198, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3717174, -368888, 785863, 2138765, -1060709]
  a := ![13, -6, -1, 5, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1856544, -176844, -1334856, 2138765, -1060709]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 12008989 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, 53, 39, 27, 9]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![32, 53, 39, 27, 9]] 
 ![![229, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![84, 0, 0, 1, 0], ![189, 0, 0, 0, 1]] where
  M :=![![![32, 53, 39, 27, 9], ![-81, 44, 131, 129, 81], ![-729, -193, 420, 509, 387], ![-486, -282, 82, 169, 168], ![-1071, -555, 267, 447, 410]]]
  hmulB := by decide  
  f := ![![![3788, -109, -775, -481, 867]], ![![793, -22, -163, -103, 183]], ![![371, -18, -71, -38, 78]], ![![1356, -28, -284, -181, 318]], ![![3123, -96, -636, -396, 713]]]
  g := ![![![-32, 53, 39, 27, 9], ![-135, 44, 131, 129, 81], ![-502, -193, 420, 509, 387], ![-148, -282, 82, 169, 168], ![-408, -555, 267, 447, 410]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![320, -37, -47, -37, 65]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![320, -37, -47, -37, 65]] 
 ![![229, 0, 0, 0, 0], ![152, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![320, -37, -47, -37, 65], ![-585, 78, 101, 81, -111], ![999, -151, -134, -91, 243], ![-900, 90, 142, 119, -162], ![219, -81, -27, -3, 92]]]
  hmulB := by decide  
  f := ![![![56, -1359, 883, 1587, -1217]], ![![85, -882, 565, 1039, -787]], ![![-181, -184, 151, 180, -176]], ![![186, -166, 78, 227, -138]], ![![1, -186, 122, 216, -167]]]
  g := ![![![26, -37, -47, -37, 65], ![-59, 78, 101, 81, -111], ![94, -151, -134, -91, 243], ![-70, 90, 142, 119, -162], ![44, -81, -27, -3, 92]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-155, -125, 19, 50, 0]] ![![32, 53, 39, 27, 9]]
  ![![-32986, -31482, -10340, -2189, 4233]] where
 M := ![![![-32986, -31482, -10340, -2189, 4233]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-32986, -31482, -10340, -2189, 4233]] ![![320, -37, -47, -37, 65]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![428917, -213657, -668909, -661810, -418154]]]
 hmul := by decide  
 g := ![![![![1873, -933, -2921, -2890, -1826]]]]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29035, 3751, 4567, 3574, -5880]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-29035, 3751, 4567, 3574, -5880]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![0, 0, 233, 0, 0], ![211, 82, 71, 1, 0], ![204, 75, 2, 0, 1]] where
  M :=![![![-29035, 3751, 4567, 3574, -5880], ![52920, -6828, -8329, -6520, 10722], ![-96498, 12425, 15200, 11890, -19560], ![79029, -10160, -12454, -9730, 16017], ![-27531, 3543, 4335, 3375, -5572]]]
  hmulB := by decide  
  f := ![![![-215, -145, 9, 50, 60]], ![![-540, -386, 3, 116, 150]], ![![-1350, -987, -46, 230, 348]], ![![-796, -568, -5, 156, 213]], ![![-375, -261, 8, 83, 104]]]
  g := ![![![1787, 651, -1019, 3574, -5880], ![-3256, -1186, 1859, -6520, 10722], ![5944, 2165, -3390, 11890, -19560], ![-4873, -1775, 2774, -9730, 16017], ![1704, 621, -962, 3375, -5572]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 3 2 7 [152, 12, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [194, 145, 214], [142, 87, 19], [0, 1]]
 g := ![![[198, 139, 30], [203, 217], [127, 23], [45, 102, 162], [140, 91], [15, 48, 124], [1]], ![[194, 213, 42, 23], [58, 4], [], [219, 64, 156, 26], [226, 159], [45, 232, 216, 141], [15, 34, 205, 131]], ![[197, 117, 79, 38], [37, 14], [203, 23], [19, 129, 92, 50], [165, 218], [137, 187, 90, 217], [199, 10, 110, 102]]]
 h' := ![![[194, 145, 214], [62, 128, 206], [167, 232, 123], [150, 61, 16], [93, 168, 167], [50, 17, 215], [81, 221, 103], [0, 1]], ![[142, 87, 19], [89, 223, 112], [98, 28, 2], [104, 148], [140, 92, 153], [170, 104, 208], [146, 159, 102], [194, 145, 214]], ![[0, 1], [34, 115, 148], [84, 206, 108], [157, 24, 217], [32, 206, 146], [114, 112, 43], [226, 86, 28], [142, 87, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 108], []]
 b := ![[], [178, 172, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 3
  hpos := by decide
  P := [152, 12, 130, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29294, -44924, 4568, 35882, 1818]
  a := ![-1, 0, -2, -5, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-33960, -13406, -10930, 35882, 1818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 12649337 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1661, -215, -261, -204, 336]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![1661, -215, -261, -204, 336]] 
 ![![233, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![146, 0, 0, 0, 1]] where
  M :=![![![1661, -215, -261, -204, 336], ![-3024, 392, 475, 372, -612], ![5508, -713, -866, -680, 1116], ![-4509, 582, 710, 558, -915], ![1575, -201, -249, -195, 320]]]
  hmulB := by decide  
  f := ![![![-1343, -923, 57, 328, 384]], ![![-84, -58, 3, 20, 24]], ![![-551, -380, 21, 132, 156]], ![![-200, -139, 7, 48, 57]], ![![-851, -587, 33, 205, 242]]]
  g := ![![![-62, -215, -261, -204, 336], ![113, 392, 475, 372, -612], ![-206, -713, -866, -680, 1116], ![169, 582, 710, 558, -915], ![-59, -201, -249, -195, 320]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-437, -49, 105, -24, -70]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![-437, -49, 105, -24, -70]] 
 ![![233, 0, 0, 0, 0], ![172, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![122, 0, 0, 0, 1]] where
  M :=![![![-437, -49, 105, -24, -70], ![630, -122, -25, 258, -72], ![648, 821, -646, -832, 774], ![-2223, -960, 1000, 702, -993], ![1713, 219, -429, 63, 298]]]
  hmulB := by decide  
  f := ![![![-11569, 623, 1791, 1652, -1714]], ![![-8474, 440, 1311, 1214, -1244]], ![![-539, 10, 81, 80, -68]], ![![17, -14, -4, 0, 11]], ![![-6121, 317, 945, 875, -900]]]
  g := ![![![68, -49, 105, -24, -70], ![129, -122, -25, 258, -72], ![-982, 821, -646, -832, 774], ![1183, -960, 1000, 702, -993], ![-298, 219, -429, 63, 298]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-29035, 3751, 4567, 3574, -5880]] ![![1661, -215, -261, -204, 336]]
  ![![-59791289, 7718594, 9406498, 7353844, -12106410]] where
 M := ![![![-59791289, 7718594, 9406498, 7353844, -12106410]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![-59791289, 7718594, 9406498, 7353844, -12106410]] ![![-437, -49, 105, -24, -70]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![1042675, -154479, -154013, -123490, 203642]]]
 hmul := by decide  
 g := ![![![![4475, -663, -661, -530, 874]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 0, 0, 0, 0]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![239, 0, 0, 0, 0]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![0, 0, 0, 0, 239]] where
  M :=![![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![0, 0, 0, 239, 0], ![0, 0, 0, 0, 239]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 5 2 7 [66, 142, 225, 136, 114, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [233, 54, 13, 12, 136], [206, 73, 152, 61, 127], [216, 213, 229, 43, 18], [187, 137, 84, 123, 197], [0, 1]]
 g := ![![[87, 13, 49, 177, 68], [40, 148, 167, 8, 64], [189, 198, 53, 176, 220], [5, 92, 223, 24, 120], [128, 204, 139, 5], [193, 125, 1], []], ![[18, 110, 9, 77, 36, 4, 221, 161], [9, 96, 88, 36, 180, 221, 224, 24], [70, 136, 85, 106, 43, 162, 220, 45], [134, 78, 216, 238, 93, 122, 234, 186], [1, 92, 186, 226], [86, 142, 177, 91, 16, 85, 194, 155], [46, 224, 25, 219, 231, 168, 17, 220]], ![[48, 41, 11, 238, 153, 21, 229, 226], [157, 44, 231, 4, 129, 140, 50, 49], [182, 42, 30, 218, 236, 55, 218, 132], [74, 148, 216, 37, 23, 147, 228, 3], [210, 219, 33, 10], [165, 63, 105, 79, 173, 209, 220, 22], [114, 149, 104, 152, 215, 45, 201, 153]], ![[23, 53, 217, 174, 16, 26, 117, 5], [79, 177, 120, 108, 90, 70, 151, 100], [2, 53, 238, 107, 88, 117, 186, 225], [9, 202, 201, 172, 140, 229, 172, 40], [218, 186, 164, 133], [41, 66, 8, 63, 13, 229, 128, 88], [148, 37, 134, 60, 185, 108, 21, 96]], ![[12, 98, 182, 158, 111, 141, 47, 220], [139, 30, 153, 52, 123, 235, 108, 81], [103, 187, 209, 98, 133, 237, 27, 193], [29, 5, 99, 37, 158, 159, 230, 174], [151, 59, 135, 116], [224, 147, 8, 163, 40, 156, 100, 48], [147, 40, 206, 97, 82, 202, 130, 2]]]
 h' := ![![[233, 54, 13, 12, 136], [228, 52, 223, 201, 207], [193, 162, 183, 141, 231], [148, 46, 41, 198, 170], [178, 84, 59, 66, 169], [168, 194, 182, 216, 208], [0, 0, 0, 1], [0, 1]], ![[206, 73, 152, 61, 127], [40, 135, 29, 181, 16], [149, 122, 36, 25, 156], [139, 155, 82, 153, 170], [61, 190, 79, 12, 64], [102, 97, 219, 52, 153], [94, 51, 230, 34, 25], [233, 54, 13, 12, 136]], ![[216, 213, 229, 43, 18], [103, 112, 103, 91, 118], [146, 97, 137, 55, 96], [95, 19, 23, 185, 219], [46, 66, 126, 92, 151], [98, 36, 161, 6, 38], [37, 237, 186, 27, 86], [206, 73, 152, 61, 127]], ![[187, 137, 84, 123, 197], [236, 95, 146, 104, 86], [173, 30, 157, 129, 165], [191, 57, 40, 145, 111], [7, 165, 180, 84, 59], [85, 237, 174, 43, 206], [53, 49, 28, 150, 192], [216, 213, 229, 43, 18]], ![[0, 1], [172, 84, 216, 140, 51], [182, 67, 204, 128, 69], [32, 201, 53, 36, 47], [37, 212, 34, 224, 35], [46, 153, 220, 161, 112], [21, 141, 34, 27, 175], [187, 137, 84, 123, 197]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [185, 76, 19, 110], [], [], []]
 b := ![[], [83, 92, 59, 149, 73], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 5
  hpos := by decide
  P := [66, 142, 225, 136, 114, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2262730360233, -1721023241774, -362056416556, -13697296257, 312898201305]
  a := ![3, 10, 6, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9467491047, -7200934066, -1514880404, -57310863, 1309197495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 779811265199 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def PBC239 : ContainsPrimesAboveP 239 ![I239N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI239N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![239, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 239 (by decide) 𝕀

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


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [56, 80, 119, 144, 20, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 137, 8, 54, 35], [105, 228, 223, 32, 230], [2, 165, 97, 200, 125], [7, 192, 154, 196, 92], [0, 1]]
 g := ![![[11, 128, 117, 37, 237], [162, 123, 73, 188], [14, 239, 45, 231], [84, 137, 4, 141], [27, 193, 37, 97, 191], [15, 221, 1], []], ![[57, 240, 130, 84, 41, 96, 193, 35], [35, 220, 68, 177], [146, 179, 239, 16], [69, 149, 155, 32], [62, 136, 32, 131, 213, 104, 191, 117], [195, 8, 97, 47, 188, 49, 168, 195], [49, 95, 193, 75, 180, 33, 85, 218]], ![[2, 208, 39, 132, 146, 53, 60, 198], [21, 229, 234, 188], [133, 211, 101, 169], [187, 214, 127, 113], [30, 146, 157, 11, 172, 18, 12, 71], [210, 124, 131, 202, 125, 152, 74, 124], [117, 199, 143, 5, 2, 204, 158, 115]], ![[44, 68, 67, 91, 223, 68, 159, 214], [164, 19, 96, 181], [14, 135, 197, 47], [105, 42, 95, 98], [165, 122, 99, 238, 185, 66, 172, 147], [122, 120, 183, 20, 195, 196, 63, 45], [192, 85, 43, 42, 33, 208, 85, 61]], ![[235, 211, 235, 75, 148, 32, 216, 203], [29, 196, 200, 4], [217, 80, 66, 123], [57, 141, 10, 120], [12, 85, 77, 44, 203, 157, 37, 111], [21, 198, 29, 235, 211, 155, 70, 66], [188, 159, 235, 22, 157, 153, 83, 17]]]
 h' := ![![[107, 137, 8, 54, 35], [192, 39, 162, 206, 128], [61, 3, 228, 181, 195], [134, 91, 74, 88, 58], [175, 239, 164, 73, 158], [124, 161, 0, 140, 51], [0, 0, 0, 1], [0, 1]], ![[105, 228, 223, 32, 230], [115, 92, 201, 222, 1], [151, 119, 60, 213, 211], [186, 93, 170, 100, 4], [215, 107, 219, 99, 88], [202, 111, 11, 197, 187], [188, 173, 228, 115, 47], [107, 137, 8, 54, 35]], ![[2, 165, 97, 200, 125], [123, 122, 26, 140, 114], [217, 107, 194, 119, 195], [26, 179, 218, 172, 228], [193, 207, 236, 193, 63], [179, 197, 134, 108, 208], [57, 191, 121, 117, 37], [105, 228, 223, 32, 230]], ![[7, 192, 154, 196, 92], [174, 73, 56, 61, 41], [220, 45, 32, 140, 120], [47, 80, 213, 9, 23], [25, 207, 154, 117, 154], [74, 179, 149, 79, 178], [101, 176, 149, 165, 97], [2, 165, 97, 200, 125]], ![[0, 1], [117, 156, 37, 94, 198], [81, 208, 209, 70, 2], [122, 39, 48, 113, 169], [121, 204, 191, 0, 19], [97, 75, 188, 199, 99], [178, 183, 225, 84, 60], [7, 192, 154, 196, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [187, 140, 196, 34], [], [], []]
 b := ![[], [8, 20, 34, 53, 61], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [56, 80, 119, 144, 20, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27591444120, -8762919542, -1562277680, -7587161036, -3910970654]
  a := ![1, 4, 0, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-114487320, -36360662, -6482480, -31481996, -16228094]
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



lemma PB242I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 241 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 241 (by omega)

def PB242I5 : PrimesBelowBoundCertificateInterval O 197 241 242 where
  m := 8
  g := ![2, 2, 3, 2, 3, 3, 1, 1]
  P := ![199, 211, 223, 227, 229, 233, 239, 241]
  hP := PB242I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0]
    · exact ![I241N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1568239201, 199]
    · exact ![9393931, 44521]
    · exact ![11089567, 223, 223]
    · exact ![11697083, 51529]
    · exact ![12008989, 229, 229]
    · exact ![12649337, 233, 233]
    · exact ![779811265199]
    · exact ![812990017201]
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
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
  β := ![I199N1, I223N1, I223N2, I229N1, I229N2, I233N1, I233N2]
  Il := ![[I199N1], [], [I223N1, I223N2], [], [I229N1, I229N2], [I233N1, I233N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
