
import IdealArithmetic.Examples.NF5_1_40500000_1.RI5_1_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1730008, 495869, -232528, 698712, 1006563]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![1730008, 495869, -232528, 698712, 1006563]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![93, 69, 1, 0, 0], ![15, 71, 0, 1, 0], ![25, 160, 0, 0, 1]] where
  M :=![![![1730008, 495869, -232528, 698712, 1006563], ![4417113, 1266080, -593704, 1783982, 2570007], ![11277985, 3232575, -1515859, 4554920, 6561835], ![670978, 192321, -90183, 270993, 390382], ![3207128, 919250, -431068, 1295286, 1866003]]]
  hmulB := by decide  
  f := ![![![-9586, 1335, 2184, -396, -4265]], ![![-13587, 938, -1742, 12122, 9627]], ![![-8924, 898, 287, 4210, 1687]], ![![-5395, 414, -481, 4261, 3140]], ![![-12072, 911, -1154, 9738, 7278]]]
  g := ![![![-61757, -975469, -232528, 698712, 1006563], ![-157680, -2490614, -593704, 1783982, 2570007], ![-402597, -6359126, -1515859, 4554920, 6561835], ![-23952, -378325, -90183, 270993, 390382], ![-114487, -1808356, -431068, 1295286, 1866003]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 2 2 7 [179, 128, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 198], [0, 1]]
 g := ![![[113, 50], [57, 175], [82, 49], [8], [86], [33], [71, 1]], ![[81, 149], [144, 24], [178, 150], [8], [86], [33], [142, 198]]]
 h' := ![![[71, 198], [145, 100], [48, 37], [1, 192], [144, 159], [195, 22], [27, 86], [0, 1]], ![[0, 1], [81, 99], [88, 162], [101, 7], [90, 40], [165, 177], [163, 113], [71, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139]]
 b := ![[], [70, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 2
  hpos := by decide
  P := [179, 128, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1474, -546, 2230, -2387, -7392]
  a := ![-11, -7, 13, -19, -44]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![59, 6019, 2230, -2387, -7392]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 3, 2, 2, -11]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![2, 3, 2, 2, -11]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![1, 191, 1, 0, 0], ![160, 34, 0, 1, 0], ![11, 113, 0, 0, 1]] where
  M :=![![![2, 3, 2, 2, -11], ![-29, 14, -14, 4, 49], ![155, -95, 51, -30, -115], ![-26, 31, -5, 17, -14], ![70, -54, 18, -22, -19]]]
  hmulB := by decide  
  f := ![![![80, 1, -18, 22, 49]], ![![191, 12, -16, -16, 29]], ![![184, 12, -15, -16, 27]], ![![96, 3, -17, 15, 44]], ![![113, 7, -10, -8, 19]]]
  g := ![![![-1, 4, 2, 2, -11], ![-6, -15, -14, 4, 49], ![31, 21, 51, -30, -115], ![-13, 10, -5, 17, -14], ![19, -3, 18, -22, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P1 : CertificateIrreducibleZModOfList' 199 2 2 7 [101, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [109, 198], [0, 1]]
 g := ![![[60, 70], [51, 62], [146, 50], [28], [25], [128], [109, 1]], ![[128, 129], [43, 137], [24, 149], [28], [25], [128], [19, 198]]]
 h' := ![![[109, 198], [23, 95], [179, 103], [69, 100], [67, 174], [123, 5], [135, 39], [0, 1]], ![[0, 1], [30, 104], [63, 96], [24, 99], [128, 25], [71, 194], [8, 160], [109, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [196]]
 b := ![[], [32, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N1 : CertifiedPrimeIdeal' SI199N1 199 where
  n := 2
  hpos := by decide
  P := [101, 90, 1]
  hirr := P199P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42047, 10526, 7429, -3440, -31482]
  a := ![-49, -56, 48, -106, -199]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4680, 11387, 7429, -3440, -31482]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N1 B_one_repr
lemma NI199N1 : Nat.card (O ⧸ I199N1) = 39601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2105, 460, 1312, -2274, -3636]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![-2105, 460, 1312, -2274, -3636]] 
 ![![199, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![119, 0, 0, 0, 1]] where
  M :=![![![-2105, 460, 1312, -2274, -3636], ![-15456, 2181, 3646, -974, -7284], ![-23800, 1800, -2181, 18970, 14060], ![15740, -2664, -5928, 6809, 14600], ![-5192, 400, -440, 4044, 2951]]]
  hmulB := by decide  
  f := ![![![5330873, 1528020, -716504, 2153050, 3101548]], ![![3765182, 1079237, -506066, 1520694, 2190620]], ![![1781940, 510760, -239501, 719690, 1036740]], ![![2635642, 755472, -354248, 1064493, 1533440]], ![![3237473, 927972, -435136, 1307558, 1883587]]]
  g := ![![![2569, 460, 1312, -2274, -3636], ![2146, 2181, 3646, -974, -7284], ![-18460, 1800, -2181, 18970, 14060], ![-8370, -2664, -5928, 6809, 14600], ![-3927, 400, -440, 4044, 2951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![1730008, 495869, -232528, 698712, 1006563]] ![![2, 3, 2, 2, -11]]
  ![![5330873, 1528020, -716504, 2153050, 3101548]] where
 M := ![![![5330873, 1528020, -716504, 2153050, 3101548]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![5330873, 1528020, -716504, 2153050, 3101548]] ![![-2105, 460, 1312, -2274, -3636]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![136855, 39225, -18395, 55272, 79626]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![136855, 39225, -18395, 55272, 79626]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![0, 0, 211, 0, 0], ![80, 200, 182, 1, 0], ![180, 204, 92, 0, 1]] where
  M :=![![![136855, 39225, -18395, 55272, 79626], ![349422, 100152, -46965, 141118, 203298], ![892130, 255715, -119904, 360300, 519050], ![53064, 15215, -7131, 21437, 30876], ![253696, 72718, -34098, 102460, 147605]]]
  hmulB := by decide  
  f := ![![![21, -5, 19, -6, -70]], ![![-222, 110, -57, 32, 162]], ![![550, -475, 176, -150, -230]], ![![272, -307, 105, -101, -72]], ![![44, -106, 38, -40, -3]]]
  g := ![![![-88235, -129189, -82481, 55272, 79626], ![-225278, -329840, -210587, 141118, 203298], ![-575170, -842135, -537664, 360300, 519050], ![-34216, -50099, -31987, 21437, 30876], ![-163564, -239482, -152898, 102460, 147605]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 3 2 7 [184, 210, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 133, 143], [93, 77, 68], [0, 1]]
 g := ![![[150, 79, 125], [68, 176, 201], [180, 69], [98, 143], [135, 169, 136], [128, 21], [1]], ![[135, 11, 192, 114], [127, 70, 90, 109], [152, 173], [200, 76], [2, 178, 32, 81], [32, 114], [89, 187, 61, 169]], ![[113, 84, 176, 77], [103, 94, 209, 60], [69, 53], [3, 54], [31, 140, 190, 197], [144, 126], [34, 54, 204, 42]]]
 h' := ![![[41, 133, 143], [148, 87, 97], [72, 130, 74], [102, 2, 160], [58, 15, 96], [176, 116, 145], [27, 1, 134], [0, 1]], ![[93, 77, 68], [165, 191, 76], [140, 164, 23], [195, 139, 157], [131, 62, 42], [56, 22, 112], [6, 24, 122], [41, 133, 143]], ![[0, 1], [94, 144, 38], [136, 128, 114], [159, 70, 105], [194, 134, 73], [185, 73, 165], [99, 186, 166], [93, 77, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 23], []]
 b := ![[], [156, 133, 171], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 3
  hpos := by decide
  P := [184, 210, 77, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1287, 562, 10935, -5946, -30073]
  a := ![-4, -4, 5, -9, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![27903, 34714, 18293, -5946, -30073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 9393931 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, 5, -19, 6, 70]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![-21, 5, -19, 6, 70]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![26, 79, 1, 0, 0], ![90, 12, 0, 1, 0], ![201, 129, 0, 0, 1]] where
  M :=![![![-21, 5, -19, 6, 70], ![222, -110, 57, -32, -162], ![-550, 475, -176, 150, 230], ![-12, -73, -3, -69, 132], ![-192, 206, -34, 88, -79]]]
  hmulB := by decide  
  f := ![![![-136855, -39225, 18395, -55272, -79626]], ![![-349422, -100152, 46965, -141118, -203298]], ![![-151918, -43543, 20419, -61354, -88388]], ![![-78498, -22499, 10551, -31703, -45672]], ![![-345199, -98941, 46398, -139414, -200843]]]
  g := ![![![-67, -36, -19, 6, 70], ![162, 79, 57, -32, -162], ![-264, -81, -176, 150, 230], ![-96, -76, -3, -69, 132], ![41, 57, -34, 88, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [8, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 210], [0, 1]]
 g := ![![[179, 150], [129, 136], [171], [182], [136, 78], [209], [45, 1]], ![[177, 61], [130, 75], [171], [182], [59, 133], [209], [90, 210]]]
 h' := ![![[45, 210], [23, 192], [180, 66], [55, 63], [178, 56], [62, 194], [62, 118], [0, 1]], ![[0, 1], [12, 19], [196, 145], [147, 148], [166, 155], [141, 17], [97, 93], [45, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [193]]
 b := ![[], [97, 202]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [8, 166, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10175, 10728, -2173, 12254, 7888]
  a := ![36, 27, -39, 62, 143]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12425, -4655, -2173, 12254, 7888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![136855, 39225, -18395, 55272, 79626]] ![![-21, 5, -19, 6, 70]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1499, -416, 198, -596, -868]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-1499, -416, 198, -596, -868]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![0, 0, 223, 0, 0], ![112, 99, 43, 1, 0], ![15, 174, 54, 0, 1]] where
  M :=![![![-1499, -416, 198, -596, -868], ![-3796, -1105, 504, -1544, -2164], ![-9580, -2820, 1363, -3920, -5860], ![-644, -116, 56, -213, -296], ![-2666, -844, 406, -1132, -1701]]]
  hmulB := by decide  
  f := ![![![19, -8, -30, 68, 92]], ![![412, -63, -120, 88, 268]], ![![980, -100, -59, -400, -100]], ![![380, -51, -79, -5, 144]], ![![561, -74, -110, -24, 191]]]
  g := ![![![351, 940, 326, -596, -868], ![904, 2369, 824, -1544, -2164], ![2320, 6300, 2181, -3920, -5860], ![124, 325, 113, -213, -296], ![671, 1826, 632, -1132, -1701]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 3 2 7 [103, 206, 201, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [180, 167, 140], [65, 55, 83], [0, 1]]
 g := ![![[113, 160, 72], [56, 9, 202], [57, 208, 49], [78, 169, 130], [34, 149, 69], [23, 38], [1]], ![[21, 119, 34, 48], [152, 123, 50, 214], [202, 181, 178, 107], [101, 88, 87, 134], [57, 100, 146, 189], [15, 38], [72, 73, 134, 208]], ![[163, 15, 156, 29], [169, 28, 113, 31], [149, 37, 69, 60], [168, 218, 140, 132], [193, 173, 36, 106], [76, 152], [30, 163, 161, 15]]]
 h' := ![![[180, 167, 140], [30, 2, 90], [150, 97, 176], [217, 94, 216], [66, 70, 199], [212, 111, 31], [120, 17, 22], [0, 1]], ![[65, 55, 83], [122, 217, 101], [128, 48, 68], [81, 164, 64], [190, 36, 6], [218, 10, 74], [47, 179, 22], [180, 167, 140]], ![[0, 1], [218, 4, 32], [37, 78, 202], [133, 188, 166], [200, 117, 18], [197, 102, 118], [144, 27, 179], [65, 55, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 88], []]
 b := ![[], [177, 185, 216], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 3
  hpos := by decide
  P := [103, 206, 201, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-424071, 507276, 385492, 620212, -1825378]
  a := ![-21, -9, 26, -28, -83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-190615, 1151220, 324156, 620212, -1825378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 11089567 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -1, -10, 28, 35]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![-8, -1, -10, 28, 35]] 
 ![![223, 0, 0, 0, 0], ![82, 1, 0, 0, 0], ![189, 0, 1, 0, 0], ![104, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-8, -1, -10, 28, 35], ![161, -30, -50, 54, 119], ![465, -35, -73, -100, 75], ![-78, 15, 59, -115, -162], ![96, -2, -16, -18, 11]]]
  hmulB := by decide  
  f := ![![![-1205122, -345419, 161978, -486720, -701169]], ![![-456937, -130970, 61416, -184546, -265857]], ![![-1056611, -302852, 142017, -426740, -614762]], ![![-564126, -161693, 75823, -227837, -328222]], ![![-242396, -69477, 32580, -97898, -141032]]]
  g := ![![![-11, -1, -10, 28, 35], ![6, -30, -50, 54, 119], ![109, -35, -73, -100, 75], ![29, 15, 59, -115, -162], ![21, -2, -16, -18, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-388, -111, 52, -156, -225]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![-388, -111, 52, -156, -225]] 
 ![![223, 0, 0, 0, 0], ![157, 1, 0, 0, 0], ![104, 0, 1, 0, 0], ![95, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-388, -111, 52, -156, -225], ![-987, -284, 132, -398, -573], ![-2515, -725, 337, -1020, -1465], ![-150, -43, 21, -63, -90], ![-716, -206, 96, -290, -417]]]
  hmulB := by decide  
  f := ![![![-246, 155, -60, 72, 115]], ![![-171, 107, -42, 50, 82]], ![![-113, 75, -27, 36, 45]], ![![-108, 68, -27, 31, 53]], ![![-44, 29, -10, 14, 16]]]
  g := ![![![162, -111, 52, -156, -225], ![414, -284, 132, -398, -573], ![1059, -725, 337, -1020, -1465], ![64, -43, 21, -63, -90], ![301, -206, 96, -290, -417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-1499, -416, 198, -596, -868]] ![![-8, -1, -10, 28, 35]]
  ![![246, -155, 60, -72, -115]] where
 M := ![![![246, -155, 60, -72, -115]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![246, -155, 60, -72, -115]] ![![-388, -111, 52, -156, -225]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![-223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![705, -98, -154, 16, 296]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![705, -98, -154, 16, 296]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![0, 0, 227, 0, 0], ![0, 0, 0, 227, 0], ![178, 219, 182, 43, 1]] where
  M :=![![![705, -98, -154, 16, 296], ![920, -49, 150, -900, -760], ![-4080, 770, 1891, -2720, -4920], ![-2480, 290, 326, 541, -320], ![-876, 172, 400, -584, -1043]]]
  hmulB := by decide  
  f := ![![![19, 6, -2, 8, 8]], ![![40, 17, -10, 20, 40]], ![![160, 10, -3, 40, 40]], ![![0, 10, -2, 7, 0]], ![![182, 31, -14, 59, 77]]]
  g := ![![![-229, -286, -238, -56, 296], ![600, 733, 610, 140, -760], ![3840, 4750, 3953, 920, -4920], ![240, 310, 258, 63, -320], ![814, 1007, 838, 195, -1043]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 4 2 7 [111, 82, 67, 41, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 163, 110, 194], [72, 26, 131, 24], [84, 37, 213, 9], [0, 1]]
 g := ![![[12, 134, 120, 34], [65, 67, 15, 36], [131, 202, 177], [185, 51, 172], [183, 51, 89], [51, 25, 186, 1], []], ![[6, 107, 146, 223, 39, 211], [203, 138, 70, 138, 55, 158], [167, 226, 43], [221, 99, 10], [225, 189, 133], [83, 156, 106, 39, 155, 17], [137, 95, 146, 172, 216, 156]], ![[158, 188, 134, 23, 130, 20], [113, 188, 56, 117, 29, 130], [92, 20, 219], [171, 206, 47], [221, 49, 29], [186, 109, 118, 183, 173, 105], [125, 130, 20, 153, 84, 204]], ![[52, 195, 74, 95, 46, 176], [22, 42, 18, 129, 180, 144], [225, 106, 185], [111, 198, 11], [16, 61, 49], [31, 212, 174, 32, 56, 92], [89, 179, 221, 151, 78, 48]]]
 h' := ![![[30, 163, 110, 194], [49, 35, 93, 179], [35, 195, 181, 6], [27, 210, 24, 75], [86, 187, 57, 132], [14, 80, 219, 166], [0, 0, 0, 1], [0, 1]], ![[72, 26, 131, 24], [129, 117, 51, 74], [16, 203, 59, 8], [180, 90, 175, 66], [60, 162, 176, 64], [92, 209, 63, 70], [216, 187, 43, 150], [30, 163, 110, 194]], ![[84, 37, 213, 9], [85, 219, 38, 72], [142, 141, 62, 217], [65, 50, 10, 30], [146, 13, 39, 71], [191, 32, 89, 211], [32, 128, 125, 138], [72, 26, 131, 24]], ![[0, 1], [47, 83, 45, 129], [154, 142, 152, 223], [39, 104, 18, 56], [130, 92, 182, 187], [35, 133, 83, 7], [116, 139, 59, 165], [84, 37, 213, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [57, 7, 108], []]
 b := ![[], [], [95, 112, 185, 109], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 4
  hpos := by decide
  P := [111, 82, 67, 41, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-132211345, 66745752, -55725528, 22179136, 170710976]
  a := ![12, -4, -14, -2, 48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-134443899, -164400696, -137115080, -32239616, 170710976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 2655237841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 6, -2, 8, 8]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![19, 6, -2, 8, 8]] 
 ![![227, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![170, 0, 1, 0, 0], ![179, 0, 0, 1, 0], ![150, 0, 0, 0, 1]] where
  M :=![![![19, 6, -2, 8, 8], ![40, 17, -10, 20, 40], ![160, 10, -3, 40, 40], ![0, 10, -2, 7, 0], ![52, -4, 0, 8, 15]]]
  hmulB := by decide  
  f := ![![![705, -98, -154, 16, 296]], ![![355, -49, -76, 4, 144]], ![![510, -70, -107, 0, 200]], ![![545, -76, -120, 15, 232]], ![![462, -64, -100, 8, 191]]]
  g := ![![![-13, 6, -2, 8, 8], ![-43, 17, -10, 20, 40], ![-60, 10, -3, 40, 40], ![-9, 10, -2, 7, 0], ![-14, -4, 0, 8, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![705, -98, -154, 16, 296]] ![![19, 6, -2, 8, 8]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7109314, -2037737, 955558, -2871300, -4136397]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![-7109314, -2037737, 955558, -2871300, -4136397]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![198, 175, 1, 0, 0], ![199, 118, 0, 1, 0], ![85, 70, 0, 0, 1]] where
  M :=![![![-7109314, -2037737, 955558, -2871300, -4136397], ![-18151791, -5202824, 2439766, -7331114, -10561209], ![-46345855, -13284075, 6229309, -18718100, -26965285], ![-2757310, -790329, 370611, -1113621, -1604290], ![-13179416, -3777602, 1771432, -5322882, -7668135]]]
  hmulB := by decide  
  f := ![![![-1796, -297, -2322, 7104, 8057]], ![![38379, -6302, -13552, 14206, 32661]], ![![28328, -5139, -12435, 16878, 31994]], ![![18128, -3484, -8935, 13369, 23643]], ![![11184, -2051, -5020, 6954, 12990]]]
  g := ![![![3173243, 2004807, 955558, -2871300, -4136397], ![8102048, 5118752, 2439766, -7331114, -10561209], ![20686472, 13069400, 6229309, -18718100, -26965285], ![1230729, 777556, 370611, -1113621, -1604290], ![5882629, 3716556, 1771432, -5322882, -7668135]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 2 2 7 [181, 193, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 228], [0, 1]]
 g := ![![[58, 62], [214], [212, 224], [49], [5], [168, 213], [36, 1]], ![[0, 167], [214], [32, 5], [49], [5], [50, 16], [72, 228]]]
 h' := ![![[36, 228], [120, 73], [100, 121], [61, 37], [122, 7], [49, 66], [125, 199], [0, 1]], ![[0, 1], [0, 156], [105, 108], [19, 192], [145, 222], [135, 163], [190, 30], [36, 228]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [157, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 2
  hpos := by decide
  P := [181, 193, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10110, 6841, -3236, 9068, 13371]
  a := ![24, 19, -20, 44, 83]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10001, -6257, -3236, 9068, 13371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI229N0 : Ideal.IsPrime I229N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI229N0 B_one_repr
lemma NI229N0 : Nat.card (O ⧸ I229N0) = 52441 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI229N0

def I229N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2023, 303, 565, -358, -1238]] i)))

def SI229N1: IdealEqSpanCertificate' Table ![![-2023, 303, 565, -358, -1238]] 
 ![![229, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![161, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![171, 0, 0, 0, 1]] where
  M :=![![![-2023, 303, 565, -358, -1238], ![-4430, 444, 139, 2100, 850], ![6750, -1635, -5006, 9390, 14250], ![8368, -1111, -1625, -389, 2812], ![1410, -346, -1068, 2020, 3049]]]
  hmulB := by decide  
  f := ![![![32469, 8643, -3979, 12652, 17702]], ![![12536, 3356, -1545, 4898, 6858]], ![![23751, 6312, -2917, 9248, 12988]], ![![5450, 1447, -663, 2121, 2952]], ![![24501, 6523, -3009, 9548, 13387]]]
  g := ![![![464, 303, 565, -358, -1238], ![-1267, 444, 139, 2100, 850], ![-8036, -1635, -5006, 9390, 14250], ![-439, -1111, -1625, -389, 2812], ![-1725, -346, -1068, 2020, 3049]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N1 : Nat.card (O ⧸ I229N1) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N1)

lemma isPrimeI229N1 : Ideal.IsPrime I229N1 := prime_ideal_of_norm_prime hp229.out _ NI229N1

def I229N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 10, -3, 10, -1]] i)))

def SI229N2: IdealEqSpanCertificate' Table ![![-8, 10, -3, 10, -1]] 
 ![![229, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![42, 0, 1, 0, 0], ![136, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![-8, 10, -3, 10, -1], ![17, -13, -21, -2, 83], ![245, -90, 76, -50, -265], ![-98, 64, -10, 9, -2], ![130, -76, 40, -34, -99]]]
  hmulB := by decide  
  f := ![![![-1555670, -445898, 209097, -628300, -905131]], ![![-615157, -176321, 82683, -248448, -357915]], ![![-329605, -94474, 44302, -133120, -191773]], ![![-926526, -265568, 124534, -374203, -539078]], ![![-426986, -122386, 57391, -172450, -248432]]]
  g := ![![![-9, 10, -3, 10, -1], ![-12, -13, -21, -2, 83], ![122, -90, 76, -50, -265], ![-28, 64, -10, 9, -2], ![69, -76, 40, -34, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N2 : Nat.card (O ⧸ I229N2) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N2)

lemma isPrimeI229N2 : Ideal.IsPrime I229N2 := prime_ideal_of_norm_prime hp229.out _ NI229N2

def I229N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -8, 4, -12, -18]] i)))

def SI229N3: IdealEqSpanCertificate' Table ![![-31, -8, 4, -12, -18]] 
 ![![229, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![27, 0, 1, 0, 0], ![155, 0, 0, 1, 0], ![174, 0, 0, 0, 1]] where
  M :=![![![-31, -8, 4, -12, -18], ![-78, -23, 10, -32, -42], ![-190, -60, 31, -80, -130], ![-16, 0, 0, -3, -4], ![-50, -20, 10, -24, -39]]]
  hmulB := by decide  
  f := ![![![313, -48, -72, 12, 146]], ![![151, -23, -34, 4, 68]], ![![29, -4, -5, -4, 8]], ![![207, -32, -48, 9, 98]], ![![236, -36, -54, 8, 109]]]
  g := ![![![25, -8, 4, -12, -18], ![63, -23, 10, -32, -42], ![177, -60, 31, -80, -130], ![5, 0, 0, -3, -4], ![54, -20, 10, -24, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI229N3 : Nat.card (O ⧸ I229N3) = 229 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI229N3)

lemma isPrimeI229N3 : Ideal.IsPrime I229N3 := prime_ideal_of_norm_prime hp229.out _ NI229N3
def MulI229N0 : IdealMulLeCertificate' Table 
  ![![-7109314, -2037737, 955558, -2871300, -4136397]] ![![-2023, 303, 565, -358, -1238]]
  ![![-24538, -7038, 3295, -9908, -14271]] where
 M := ![![![-24538, -7038, 3295, -9908, -14271]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N1 : IdealMulLeCertificate' Table 
  ![![-24538, -7038, 3295, -9908, -14271]] ![![-8, 10, -3, 10, -1]]
  ![![-313, 48, 72, -12, -146]] where
 M := ![![![-313, 48, 72, -12, -146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI229N2 : IdealMulLeCertificate' Table 
  ![![-313, 48, 72, -12, -146]] ![![-31, -8, 4, -12, -18]]
  ![![229, 0, 0, 0, 0]] where
 M := ![![![-229, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC229 : ContainsPrimesAboveP 229 ![I229N0, I229N1, I229N2, I229N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI229N0
    exact isPrimeI229N1
    exact isPrimeI229N2
    exact isPrimeI229N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 229 (by decide) (𝕀 ⊙ MulI229N0 ⊙ MulI229N1 ⊙ MulI229N2)
instance hp233 : Fact (Nat.Prime 233) := {out := by norm_num}

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23351742, 6693286, -3138689, 9431266, 13586687]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![23351742, 6693286, -3138689, 9431266, 13586687]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![19, 159, 1, 0, 0], ![94, 14, 0, 1, 0], ![201, 21, 0, 0, 1]] where
  M :=![![![23351742, 6693286, -3138689, 9431266, 13586687], ![59622593, 17089563, -8013825, 24080282, 34690067], ![152230765, 43633750, -20461216, 61482730, 88572055], ![9056866, 2595960, -1217326, 3657873, 5269534], ![43289996, 12408168, -5818574, 17483898, 25187313]]]
  hmulB := by decide  
  f := ![![![-1504, 282, 343, -116, -759]], ![![-2509, 95, -129, 1564, 1349]], ![![-1804, 81, -74, 1084, 895]], ![![-736, 118, 126, 45, -218]], ![![-1515, 249, 282, 46, -527]]]
  g := ![![![-15169426, 379342, -3138689, 9431266, 13586687], ![-38731179, 968551, -8013825, 24080282, 34690067], ![-98889982, 2472943, -20461216, 61482730, 88572055], ![-5883392, 147126, -1217326, 3657873, 5269534], ![-28121431, 703233, -5818574, 17483898, 25187313]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [139, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 232], [0, 1]]
 g := ![![[95, 62], [74], [170], [143, 162], [226], [0, 161], [76, 1]], ![[147, 171], [74], [170], [106, 71], [226], [120, 72], [152, 232]]]
 h' := ![![[76, 232], [89, 67], [194, 128], [161, 50], [41, 167], [0, 172], [154, 45], [0, 1]], ![[0, 1], [55, 166], [136, 105], [0, 183], [151, 66], [24, 61], [79, 188], [76, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [228]]
 b := ![[], [95, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [139, 157, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![338, -437, -204, -566, 259]
  a := ![0, -3, -1, -4, 1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![23, 148, -204, -566, 259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 3, 2, 8, 1]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![-22, 3, 2, 8, 1]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![15, 26, 1, 0, 0], ![194, 214, 0, 1, 0], ![27, 103, 0, 0, 1]] where
  M :=![![![-22, 3, 2, 8, 1], ![19, -4, -20, 46, 61], ![275, -35, -81, 60, 185], ![58, -5, 7, -49, -38], ![58, -6, -18, 14, 41]]]
  hmulB := by decide  
  f := ![![![16, 23, -6, 20, 11]], ![![73, 6, -26, 22, 127]], ![![11, 2, -3, 4, 14]], ![![80, 25, -29, 37, 126]], ![![35, 5, -12, 12, 57]]]
  g := ![![![-7, -8, 2, 8, 1], ![-44, -67, -20, 46, 61], ![-65, -128, -81, 60, 185], ![45, 61, 7, -49, -38], ![-15, -29, -18, 14, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P1 : CertificateIrreducibleZModOfList' 233 2 2 7 [176, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [171, 232], [0, 1]]
 g := ![![[3, 178], [219], [152], [55, 100], [123], [34, 105], [171, 1]], ![[151, 55], [219], [152], [146, 133], [123], [48, 128], [109, 232]]]
 h' := ![![[171, 232], [72, 143], [95, 174], [106, 131], [138, 10], [74, 39], [194, 173], [0, 1]], ![[0, 1], [60, 90], [25, 59], [139, 102], [217, 223], [219, 194], [186, 60], [171, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [96, 191]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N1 : CertifiedPrimeIdeal' SI233N1 233 where
  n := 2
  hpos := by decide
  P := [176, 62, 1]
  hirr := P233P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-946, 5794, -887, 4334, 30]
  a := ![23, 9, -23, 28, 89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3559, -3870, -887, 4334, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N1 B_one_repr
lemma NI233N1 : Nat.card (O ⧸ I233N1) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62448, -10887, -25112, 31196, 63089]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![62448, -10887, -25112, 31196, 63089]] 
 ![![233, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![224, 0, 0, 1, 0], ![207, 0, 0, 0, 1]] where
  M :=![![![62448, -10887, -25112, 31196, 63089], ![251659, -31916, -41386, -31354, 60301], ![118195, 13375, 122447, -387320, -431735], ![-332814, 50269, 95053, -64419, -210486], ![27022, 2630, 25854, -82930, -91765]]]
  hmulB := by decide  
  f := ![![![-21476990, -6155955, 2887032, -8674120, -12497401]], ![![-4659811, -1335630, 626380, -1881994, -2711485]], ![![-2997415, -859215, 402947, -1210640, -1744227]], ![![-20683166, -5928407, 2780321, -8353501, -12035482]], ![![-19251270, -5518027, 2587848, -7775218, -11202266]]]
  g := ![![![-80727, -10887, -25112, 31196, 63089], ![-11156, -31916, -41386, -31354, 60301], ![740006, 13375, 122447, -387320, -431735], ![226538, 50269, 95053, -64419, -210486], ![157941, 2630, 25854, -82930, -91765]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![23351742, 6693286, -3138689, 9431266, 13586687]] ![![-22, 3, 2, 8, 1]]
  ![![85335909, 24459745, -11469931, 34465336, 49650782]] where
 M := ![![![85335909, 24459745, -11469931, 34465336, 49650782]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![85335909, 24459745, -11469931, 34465336, 49650782]] ![![62448, -10887, -25112, 31196, 63089]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![413342, -57784, -93899, 16310, 182905]]]
 hmul := by decide  
 g := ![![![![1774, -248, -403, 70, 785]]]]
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

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7270, -2002, 961, -2880, -4229]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![-7270, -2002, 961, -2880, -4229]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![14, 70, 44, 1, 0], ![181, 7, 171, 0, 1]] where
  M :=![![![-7270, -2002, 961, -2880, -4229], ![-18447, -5345, 2409, -7488, -10353], ![-46035, -13890, 6766, -19080, -28845], ![-3246, -456, 246, -983, -1434], ![-12706, -4244, 2036, -5550, -8373]]]
  hmulB := by decide  
  f := ![![![-1872, 230, 271, 330, -329]], ![![-327, -187, -1089, 3042, 3627]], ![![16965, -2730, -5686, 5490, 13455]], ![![2940, -546, -1350, 1909, 3514]], ![![10726, -1787, -3900, 4272, 9496]]]
  g := ![![![3341, 959, 3560, -2880, -4229], ![8202, 2474, 8796, -7488, -10353], ![22770, 6375, 24179, -19080, -28845], ![1130, 328, 1208, -983, -1434], ![6613, 1853, 7021, -5550, -8373]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [171, 1, 153, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [147, 97, 54], [178, 141, 185], [0, 1]]
 g := ![![[83, 7, 18], [26, 146, 200], [132, 183, 36], [61, 58, 9], [185, 225], [194, 144, 226], [1]], ![[200, 48, 81, 109], [194, 38, 58, 48], [101, 229, 237, 22], [53, 213, 109, 22], [189, 66], [29, 111, 1, 218], [141, 126, 31, 202]], ![[193, 218, 139, 21], [84, 175, 137, 140], [77, 202, 7, 13], [43, 138, 136, 56], [65, 127], [28, 38, 92, 208], [167, 71, 64, 37]]]
 h' := ![![[147, 97, 54], [95, 106, 181], [133, 178, 34], [85, 183, 233], [210, 199, 236], [47, 121, 224], [68, 238, 86], [0, 1]], ![[178, 141, 185], [4, 72, 175], [230, 233, 66], [179, 6, 193], [166, 34, 46], [170, 237, 117], [2, 191, 122], [147, 97, 54]], ![[0, 1], [134, 61, 122], [16, 67, 139], [45, 50, 52], [205, 6, 196], [39, 120, 137], [192, 49, 31], [178, 141, 185]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 182], []]
 b := ![[], [108, 12, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [171, 1, 153, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29313, -7239, 112849, -25380, -271805]
  a := ![14, 7, -17, 20, 55]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![207208, 15364, 199616, -25380, -271805]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18421, 5280, -2476, 7440, 10718]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![18421, 5280, -2476, 7440, 10718]] 
 ![![239, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![236, 0, 1, 0, 0], ![69, 0, 0, 1, 0], ![124, 0, 0, 0, 1]] where
  M :=![![![18421, 5280, -2476, 7440, 10718], ![47034, 13481, -6322, 18996, 27366], ![120090, 34420, -16141, 48500, 69870], ![7144, 2048, -960, 2885, 4156], ![34150, 9788, -4590, 13792, 19869]]]
  hmulB := by decide  
  f := ![![![95, -232, 104, -112, -74]], ![![51, -127, 58, -60, -44]], ![![90, -228, 95, -108, -46]], ![![37, -72, 32, -35, -26]], ![![42, -116, 50, -56, -27]]]
  g := ![![![-8125, 5280, -2476, 7440, 10718], ![-20745, 13481, -6322, 18996, 27366], ![-52966, 34420, -16141, 48500, 69870], ![-3151, 2048, -960, 2885, 4156], ![-15062, 9788, -4590, 13792, 19869]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3352, 498, 917, -542, -1989]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![-3352, 498, 917, -542, -1989]] 
 ![![239, 0, 0, 0, 0], ![144, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![111, 0, 0, 1, 0], ![115, 0, 0, 0, 1]] where
  M :=![![![-3352, 498, 917, -542, -1989], ![-7051, 691, 135, 3566, 1631], ![12025, -2810, -8376, 15310, 23635], ![13678, -1800, -2578, -839, 4342], ![2518, -596, -1788, 3294, 5061]]]
  hmulB := by decide  
  f := ![![![277671318, 79588634, -37321573, 112145460, 161556803]], ![![170266239, 48803231, -22885345, 68766864, 99065577]], ![![73796709, 21152272, -9918955, 29804900, 42936954]], ![![129410920, 37092914, -17394015, 52266281, 75294829]], ![![135761318, 38913122, -18247567, 54831070, 78989666]]]
  g := ![![![676, 498, 917, -542, -1989], ![-2919, 691, 135, 3566, 1631], ![-14742, -2810, -8376, 15310, 23635], ![57, -1800, -2578, -839, 4342], ![-3169, -596, -1788, 3294, 5061]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![-7270, -2002, 961, -2880, -4229]] ![![18421, 5280, -2476, 7440, 10718]]
  ![![-277671318, -79588634, 37321573, -112145460, -161556803]] where
 M := ![![![-277671318, -79588634, 37321573, -112145460, -161556803]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![-277671318, -79588634, 37321573, -112145460, -161556803]] ![![-3352, 498, 917, -542, -1989]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-40, 7, 12, -6, -29]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![-40, 7, 12, -6, -29]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![177, 147, 1, 0, 0], ![25, 195, 0, 1, 0], ![111, 228, 0, 0, 1]] where
  M :=![![![-40, 7, 12, -6, -29], ![-99, 14, -4, 44, 39], ![205, -75, -79, 170, 235], ![154, -9, -33, -3, 46], ![58, -30, -14, 30, 53]]]
  hmulB := by decide  
  f := ![![![8782, 2515, -1180, 3546, 5109]], ![![22419, 6428, -3014, 9056, 13041]], ![![20362, 5836, -2737, 8224, 11845]], ![![19065, 5466, -2563, 7701, 11090]], ![![25322, 7259, -3404, 10228, 14730]]]
  g := ![![![5, 25, 12, -6, -29], ![-20, -70, -4, 44, 39], ![-67, -312, -79, 170, 235], ![4, -21, -33, -3, 46], ![-17, -66, -14, 30, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 2 2 7 [71, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [141, 240], [0, 1]]
 g := ![![[127, 91], [1], [229], [27], [165, 180], [48, 135], [141, 1]], ![[185, 150], [1], [229], [27], [240, 61], [44, 106], [41, 240]]]
 h' := ![![[141, 240], [230, 205], [209, 240], [171, 179], [94, 73], [207, 105], [111, 48], [0, 1]], ![[0, 1], [215, 36], [68, 1], [105, 62], [24, 168], [70, 136], [131, 193], [141, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [227, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 2
  hpos := by decide
  P := [71, 100, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1449, 1090, -658, 1809, 2648]
  a := ![10, 8, -10, 19, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-918, -3563, -658, 1809, 2648]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N0 : Ideal.IsPrime I241N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N0 B_one_repr
lemma NI241N0 : Nat.card (O ⧸ I241N0) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N0

def I241N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112303785, -32189520, 15094662, -45357082, -65341436]] i)))

def SI241N1: IdealEqSpanCertificate' Table ![![-112303785, -32189520, 15094662, -45357082, -65341436]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![40, 92, 1, 0, 0], ![114, 98, 0, 1, 0], ![85, 60, 0, 0, 1]] where
  M :=![![![-112303785, -32189520, 15094662, -45357082, -65341436], ![-286738472, -82187557, 38540290, -115807498, -166832348], ![-732112040, -209844520, 98402589, -295684290, -425962940], ![-43556504, -12484560, 5854396, -17591537, -25342376], ![-208191346, -59673668, 27982830, -84084000, -121131455]]]
  hmulB := by decide  
  f := ![![![32639, -4720, -8306, 3646, 17340]], ![![59312, -5245, 1682, -37442, -22852]], ![![27464, -2660, -387, -14274, -6804]], ![![39030, -4298, -3156, -13441, -1224]], ![![26153, -2944, -2436, -8162, 221]]]
  g := ![![![41529623, 28815692, 15094662, -45357082, -65341436], ![106035080, 73573367, 38540290, -115807498, -166832348], ![270732960, 187850432, 98402589, -295684290, -425962940], ![16107074, 11176034, 5854396, -17591537, -25342376], ![76988569, 53419192, 27982830, -84084000, -121131455]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P1 : CertificateIrreducibleZModOfList' 241 2 2 7 [35, 201, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 240], [0, 1]]
 g := ![![[171, 200], [48], [164], [64], [227, 116], [193, 183], [40, 1]], ![[218, 41], [48], [164], [64], [47, 125], [42, 58], [80, 240]]]
 h' := ![![[40, 240], [221, 21], [93, 17], [234, 37], [8, 8], [234, 57], [46, 119], [0, 1]], ![[0, 1], [97, 220], [50, 224], [27, 204], [87, 233], [104, 184], [227, 122], [40, 240]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [175, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N1 : CertifiedPrimeIdeal' SI241N1 241 where
  n := 2
  hpos := by decide
  P := [35, 201, 1]
  hirr := P241P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10486, 9121, 3086, -1514, -22837]
  a := ![-23, -7, 22, -30, -99]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![8215, 5161, 3086, -1514, -22837]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI241N1 : Ideal.IsPrime I241N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI241N1 B_one_repr
lemma NI241N1 : Nat.card (O ⧸ I241N1) = 58081 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI241N1

def I241N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-232, 21, -4, 140, 81]] i)))

def SI241N2: IdealEqSpanCertificate' Table ![![-232, 21, -4, 140, 81]] 
 ![![241, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![237, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![-232, 21, -4, 140, 81], ![523, -112, -318, 542, 877], ![3715, -525, -861, 200, 1705], ![290, 17, 217, -731, -790], ![798, -114, -186, 46, 371]]]
  hmulB := by decide  
  f := ![![![-1474326, -422607, 198172, -595464, -857825]], ![![-27855, -7984, 3744, -11250, -16207]], ![![-1489737, -427024, 200243, -601688, -866790]], ![![-296014, -84851, 39789, -119557, -172234]], ![![-555802, -159317, 74708, -224482, -323388]]]
  g := ![![![-55, 21, -4, 140, 81], ![-116, -112, -318, 542, 877], ![197, -525, -861, 200, 1705], ![225, 17, 217, -731, -790], ![41, -114, -186, 46, 371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI241N2 : Nat.card (O ⧸ I241N2) = 241 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI241N2)

lemma isPrimeI241N2 : Ideal.IsPrime I241N2 := prime_ideal_of_norm_prime hp241.out _ NI241N2
def MulI241N0 : IdealMulLeCertificate' Table 
  ![![-40, 7, 12, -6, -29]] ![![-112303785, -32189520, 15094662, -45357082, -65341436]]
  ![![-1474326, -422607, 198172, -595464, -857825]] where
 M := ![![![-1474326, -422607, 198172, -595464, -857825]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI241N1 : IdealMulLeCertificate' Table 
  ![![-1474326, -422607, 198172, -595464, -857825]] ![![-232, 21, -4, 140, 81]]
  ![![241, 0, 0, 0, 0]] where
 M := ![![![241, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-408821, 98467, 300427, -561446, -854088]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![-408821, 98467, 300427, -561446, -854088]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![221, 117, 19, 74, 1]] where
  M :=![![![-408821, 98467, 300427, -561446, -854088], ![-3685156, 531868, 928717, -388244, -1929304], ![-6564400, 570185, -232704, 4263830, 2681960], ![3499932, -612343, -1418293, 1776959, 3571128], ![-1427862, 125526, -43112, 907744, 559033]]]
  hmulB := by decide  
  f := ![![![2925581, 838569, -393231, 1181588, 1702200]], ![![7469776, 2141014, -1003995, 3016854, 4346104]], ![![19072020, 5466655, -2563444, 7702820, 11096520]], ![![1134632, 325255, -152531, 458279, 660248]], ![![7857657, 2252240, -1056148, 3173544, 4571825]]]
  g := ![![![750377, 398513, 65849, 249566, -854088], ![1684028, 901436, 149743, 567252, -1929304], ![-2387560, -1247885, -203944, -773710, 2681960], ![-3130356, -1667069, -275975, -1045763, 3571128], ![-497905, -260085, -42489, -161198, 559033]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 4 2 7 [176, 45, 173, 120, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [246, 101, 145, 118], [190, 235, 112, 45], [197, 165, 245, 88], [0, 1]]
 g := ![![[184, 14, 42, 196], [219, 111, 77, 106], [200, 210, 153], [192, 87, 11, 92], [164, 28, 70, 243], [195, 171, 131, 1], []], ![[34, 121, 117, 20, 56, 35], [194, 110, 119, 244, 104, 80], [191, 118, 208], [189, 131, 195, 88, 86, 89], [223, 137, 64, 112], [53, 5, 97, 233, 88, 3], [141, 68, 115, 175, 233, 237]], ![[233, 1, 79, 7, 3, 5], [203, 41, 224, 51, 42, 113], [184, 100, 114], [66, 56, 11, 124, 8, 3], [167, 28, 38, 133, 109, 16], [218, 157, 103, 195, 114, 66], [61, 192, 104, 216, 5, 12]], ![[163, 3, 148, 54, 208, 94], [116, 86, 206, 22, 157, 113], [96, 111, 222], [44, 75, 25, 148, 235, 110], [198, 152, 31, 55, 231, 195], [206, 90, 137, 68, 237, 198], [234, 245, 17, 65, 77, 7]]]
 h' := ![![[246, 101, 145, 118], [110, 240, 214, 14], [55, 86, 155, 68], [93, 145, 13, 135], [1, 213, 3, 43], [67, 34, 21, 182], [0, 0, 0, 1], [0, 1]], ![[190, 235, 112, 45], [216, 81, 216, 189], [174, 184, 165, 233], [174, 139, 138, 220], [156, 243, 130, 97], [58, 105, 110], [159, 55, 174, 10], [246, 101, 145, 118]], ![[197, 165, 245, 88], [181, 62, 108, 84], [203, 28, 48, 92], [220, 157, 58, 214], [40, 73, 154, 103], [233, 233, 144, 21], [231, 213, 16, 113], [190, 235, 112, 45]], ![[0, 1], [18, 119, 215, 215], [119, 204, 134, 109], [82, 61, 42, 184], [215, 224, 215, 8], [106, 130, 227, 48], [144, 234, 61, 127], [197, 165, 245, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [249, 194, 93], []]
 b := ![[], [], [130, 234, 176, 182], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 4
  hpos := by decide
  P := [176, 45, 173, 120, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29158804, 18581400, -5908087, 8583309, 7853259]
  a := ![-10, -4, 11, -15, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7030793, -3586653, -618008, -2281107, 7853259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 3969126001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def I251N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2925581, 838569, -393231, 1181588, 1702200]] i)))

def SI251N1: IdealEqSpanCertificate' Table ![![2925581, 838569, -393231, 1181588, 1702200]] 
 ![![251, 0, 0, 0, 0], ![164, 1, 0, 0, 0], ![212, 0, 1, 0, 0], ![156, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![2925581, 838569, -393231, 1181588, 1702200], ![7469776, 2141014, -1003995, 3016854, 4346104], ![19072020, 5466655, -2563444, 7702820, 11096520], ![1134632, 325255, -152531, 458279, 660248], ![5423566, 1554538, -728952, 2190452, 3155475]]]
  hmulB := by decide  
  f := ![![![-408821, 98467, 300427, -561446, -854088]], ![![-281800, 66456, 199995, -368388, -565736]], ![![-371452, 85439, 252820, -457222, -710696]], ![![-240144, 58759, 181069, -341867, -516600]], ![![-10575, 1677, 3419, -3094, -7981]]]
  g := ![![![-958841, 838569, -393231, 1181588, 1702200], ![-2448116, 2141014, -1003995, 3016854, 4346104], ![-6250752, 5466655, -2563444, 7702820, 11096520], ![-371884, 325255, -152531, 458279, 660248], ![-1777529, 1554538, -728952, 2190452, 3155475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI251N1 : Nat.card (O ⧸ I251N1) = 251 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI251N1)

lemma isPrimeI251N1 : Ideal.IsPrime I251N1 := prime_ideal_of_norm_prime hp251.out _ NI251N1
def MulI251N0 : IdealMulLeCertificate' Table 
  ![![-408821, 98467, 300427, -561446, -854088]] ![![2925581, 838569, -393231, 1181588, 1702200]]
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


lemma PB397I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB397I5 : PrimesBelowBoundCertificateInterval O 197 251 397 where
  m := 9
  g := ![3, 2, 3, 2, 4, 3, 3, 3, 2]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB397I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1]
    · exact ![I223N0, I223N1, I223N2]
    · exact ![I227N0, I227N1]
    · exact ![I229N0, I229N1, I229N2, I229N3]
    · exact ![I233N0, I233N1, I233N2]
    · exact ![I239N0, I239N1, I239N2]
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
    · exact ![39601, 39601, 199]
    · exact ![9393931, 44521]
    · exact ![11089567, 223, 223]
    · exact ![2655237841, 227]
    · exact ![52441, 229, 229, 229]
    · exact ![54289, 54289, 233]
    · exact ![13651919, 239, 239]
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
      exact NI199N2
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
      exact NI229N3
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
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
      exact NI241N1
      exact NI241N2
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
      exact NI251N1
  β := ![I199N2, I223N1, I223N2, I227N1, I229N1, I229N2, I229N3, I233N2, I239N1, I239N2, I241N2, I251N1]
  Il := ![[I199N2], [], [I223N1, I223N2], [I227N1], [I229N1, I229N2, I229N3], [I233N2], [I239N1, I239N2], [I241N2], [I251N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
