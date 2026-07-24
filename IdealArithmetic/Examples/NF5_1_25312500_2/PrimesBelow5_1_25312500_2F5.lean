
import IdealArithmetic.Examples.NF5_1_25312500_2.RI5_1_25312500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp199 : Fact (Nat.Prime 199) := {out := by norm_num}

def I199N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1052535, 569708, -27896, 23712, -141272]] i)))

def SI199N0: IdealEqSpanCertificate' Table ![![-1052535, 569708, -27896, 23712, -141272]] 
 ![![199, 0, 0, 0, 0], ![0, 199, 0, 0, 0], ![0, 0, 199, 0, 0], ![166, 154, 16, 1, 0], ![155, 98, 81, 0, 1]] where
  M :=![![![-1052535, 569708, -27896, 23712, -141272], ![1408536, -761187, 37136, -32080, 188696], ![-1645220, 890436, -43539, 37136, -220776], ![1508604, -815196, 39848, -34299, 202120], ![-531592, 288200, -14048, 11952, -71435]]]
  hmulB := by decide  
  f := ![![![5263, -2628, -3864, 2016, 296]], ![![-4808, 5075, 976, -5712, 3736]], ![![-18644, 3700, 19043, 976, -9448]], ![![-614, 1926, -1096, -2579, 2392]], ![![-6097, 2138, 5341, -1024, -1699]]]
  g := ![![![84967, 54084, 55456, 23712, -141272], ![-113136, -71925, -74040, -32080, 188696], ![132716, 84460, 86659, 37136, -220776], ![-121238, -77090, -79312, -34299, 202120], ![42999, 27378, 28045, 11952, -71435]]]
  hle1 := by decide   
  hle2 := by decide  


def P199P0 : CertificateIrreducibleZModOfList' 199 3 2 7 [117, 76, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [65, 0, 1], [122, 198, 198], [0, 1]]
 g := ![![[110, 192, 28], [10, 160, 80], [170, 103, 72], [120, 18], [30, 124], [96, 144], [1]], ![[150, 75, 50, 56], [159, 76, 101, 94], [186, 106, 67, 158], [23, 56], [163, 63], [57, 116], [27, 64, 187, 1]], ![[144, 19, 159, 41], [173, 111, 182, 60], [188, 22, 96, 141], [103, 175], [31, 64], [116, 5], [172, 132, 9, 198]]]
 h' := ![![[65, 0, 1], [24, 122, 25], [10, 138, 105], [154, 156, 79], [57, 37, 139], [69, 8, 70], [82, 123, 187], [0, 1]], ![[122, 198, 198], [26, 174, 97], [40, 94, 33], [71, 120, 77], [37, 60, 97], [2, 129, 137], [30, 12, 135], [65, 0, 1]], ![[0, 1], [149, 102, 77], [71, 166, 61], [121, 122, 43], [113, 102, 162], [77, 62, 191], [147, 64, 76], [122, 198, 198]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160, 114], []]
 b := ![[], [159, 149, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI199N0 : CertifiedPrimeIdeal' SI199N0 199 where
  n := 3
  hpos := by decide
  P := [117, 76, 12, 1]
  hirr := P199P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4695569, 5260117, 2357371, -4932793, 1938453]
  a := ![-16, 11, 7, -17, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2581346, 2889155, -380566, -4932793, 1938453]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI199N0 : Ideal.IsPrime I199N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI199N0 B_one_repr
lemma NI199N0 : Nat.card (O ⧸ I199N0) = 7880599 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI199N0

def I199N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-195, 124, 13, 19, -22]] i)))

def SI199N1: IdealEqSpanCertificate' Table ![![-195, 124, 13, 19, -22]] 
 ![![199, 0, 0, 0, 0], ![179, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-195, 124, 13, 19, -22], ![252, -147, 59, 45, 60], ![-374, 134, 34, 59, -15], ![158, -250, 97, 106, 100], ![-254, -58, 76, 110, 47]]]
  hmulB := by decide  
  f := ![![![-119, 914, -727, -1281, 1271]], ![![-181, 849, -590, -1166, 1124]], ![![153, -40, -147, 6, 63]], ![![-61, 430, -336, -601, 594]], ![![-328, 106, 296, -42, -105]]]
  g := ![![![-121, 124, 13, 19, -22], ![111, -147, 59, 45, 60], ![-149, 134, 34, 59, -15], ![175, -250, 97, 106, 100], ![0, -58, 76, 110, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N1 : Nat.card (O ⧸ I199N1) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N1)

lemma isPrimeI199N1 : Ideal.IsPrime I199N1 := prime_ideal_of_norm_prime hp199.out _ NI199N1

def I199N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 36, -9, -19, -12]] i)))

def SI199N2: IdealEqSpanCertificate' Table ![![47, 36, -9, -19, -12]] 
 ![![199, 0, 0, 0, 0], ![187, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![142, 0, 0, 0, 1]] where
  M :=![![![47, 36, -9, -19, -12], ![92, 87, -15, -37, -26], ![58, 46, -2, -15, -11], ![98, 98, -1, -26, -22], ![70, 66, 8, -10, -11]]]
  hmulB := by decide  
  f := ![![![-325, 150, 263, -115, -33]], ![![-303, 139, 246, -106, -32]], ![![-213, 100, 171, -78, -19]], ![![-117, 54, 94, -41, -12]], ![![-212, 94, 176, -70, -27]]]
  g := ![![![-13, 36, -9, -19, -12], ![-41, 87, -15, -37, -26], ![-29, 46, -2, -15, -11], ![-67, 98, -1, -26, -22], ![-56, 66, 8, -10, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI199N2 : Nat.card (O ⧸ I199N2) = 199 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI199N2)

lemma isPrimeI199N2 : Ideal.IsPrime I199N2 := prime_ideal_of_norm_prime hp199.out _ NI199N2
def MulI199N0 : IdealMulLeCertificate' Table 
  ![![-1052535, 569708, -27896, 23712, -141272]] ![![-195, 124, 13, 19, -22]]
  ![![398873429, -215733704, 10544745, -9033617, 53488106]] where
 M := ![![![398873429, -215733704, 10544745, -9033617, 53488106]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI199N1 : IdealMulLeCertificate' Table 
  ![![398873429, -215733704, 10544745, -9033617, 53488106]] ![![47, 36, -9, -19, -12]]
  ![![199, 0, 0, 0, 0]] where
 M := ![![![2370018559, -1279410004, 61993674, -54626296, 316973369]]]
 hmul := by decide  
 g := ![![![![11909641, -6429196, 311526, -274504, 1592831]]]]
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

def I211N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-969, 538, 3, 47, -120]] i)))

def SI211N0: IdealEqSpanCertificate' Table ![![-969, 538, 3, 47, -120]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![48, 40, 1, 0, 0], ![109, 46, 0, 1, 0], ![59, 113, 0, 0, 1]] where
  M :=![![![-969, 538, 3, 47, -120], ![1250, -721, 113, 53, 214], ![-1612, 756, 22, 113, -161], ![1176, -908, 167, 138, 280], ![-726, 86, 100, 170, 25]]]
  hmulB := by decide  
  f := ![![![-1097, 560, 795, -437, -45]], ![![808, -985, -35, 1153, -829]], ![![-76, -64, 154, 119, -158]], ![![-433, 96, 434, 9, -206]], ![![169, -405, 184, 530, -473]]]
  g := ![![![4, 56, 3, 47, -120], ![-107, -151, 113, 53, 214], ![-26, 61, 22, 113, -161], ![-182, -216, 167, 138, 280], ![-121, -69, 100, 170, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P0 : CertificateIrreducibleZModOfList' 211 2 2 7 [59, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 210], [0, 1]]
 g := ![![[17, 93], [162, 5], [163], [20], [85, 69], [109], [52, 1]], ![[0, 118], [0, 206], [163], [20], [86, 142], [109], [104, 210]]]
 h' := ![![[52, 210], [148, 127], [4, 146], [166, 116], [49, 81], [24, 160], [97, 113], [0, 1]], ![[0, 1], [0, 84], [0, 65], [79, 95], [41, 130], [115, 51], [65, 98], [52, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [197, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N0 : CertifiedPrimeIdeal' SI211N0 211 where
  n := 2
  hpos := by decide
  P := [59, 159, 1]
  hirr := P211P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2525559, 571070, 1812302, -367024, -147831]
  a := ![-121, 61, 62, -122, -243]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-193310, -181673, 1812302, -367024, -147831]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N0 : Ideal.IsPrime I211N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N0 B_one_repr
lemma NI211N0 : Nat.card (O ⧸ I211N0) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N0

def I211N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5889, -3032, -4236, 2388, 194]] i)))

def SI211N1: IdealEqSpanCertificate' Table ![![5889, -3032, -4236, 2388, 194]] 
 ![![211, 0, 0, 0, 0], ![0, 211, 0, 0, 0], ![119, 203, 1, 0, 0], ![168, 198, 0, 1, 0], ![92, 85, 0, 0, 1]] where
  M :=![![![5889, -3032, -4236, 2388, 194], ![-3788, 5093, -276, -6084, 4582], ![-24196, 5868, 23697, -276, -10666], ![48104, -24544, -34816, 19185, 1918], ![-46296, 37848, 19924, -39052, 19461]]]
  hmulB := by decide  
  f := ![![![7027, 7144, 2652, 684, -366]], ![![6996, 10103, 8708, 5988, 1734]], ![![10671, 13739, 9913, 6188, 1482]], ![![12088, 15134, 10368, 6257, 1382]], ![![5776, 7113, 4744, 2808, 591]]]
  g := ![![![431, 1742, -4236, 2388, 194], ![2984, 4153, -276, -6084, 4582], ![-8609, -18215, 23697, -276, -10666], ![3752, 14604, -34816, 19185, 1918], ![11152, 9817, 19924, -39052, 19461]]]
  hle1 := by decide   
  hle2 := by decide  


def P211P1 : CertificateIrreducibleZModOfList' 211 2 2 7 [53, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 210], [0, 1]]
 g := ![![[182, 4], [58, 203], [176], [117], [49, 188], [123], [60, 1]], ![[0, 207], [0, 8], [176], [117], [146, 23], [123], [120, 210]]]
 h' := ![![[60, 210], [91, 2], [188, 25], [134, 78], [146, 180], [36, 140], [196, 171], [0, 1]], ![[0, 1], [0, 209], [0, 186], [172, 133], [185, 31], [207, 71], [117, 40], [60, 210]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [5, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI211N1 : CertifiedPrimeIdeal' SI211N1 211 where
  n := 2
  hpos := by decide
  P := [53, 151, 1]
  hirr := P211P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23227, 5784, 15970, -4982, -3952]
  a := ![-12, 8, 6, -13, -23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3427, -9070, 15970, -4982, -3952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI211N1 : Ideal.IsPrime I211N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI211N1 B_one_repr
lemma NI211N1 : Nat.card (O ⧸ I211N1) = 44521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI211N1

def I211N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -76, 5, 25, 19]] i)))

def SI211N2: IdealEqSpanCertificate' Table ![![-83, -76, 5, 25, 19]] 
 ![![211, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![116, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![-83, -76, 5, 25, 19], ![-160, -151, -5, 35, 31], ![-60, -64, -22, -5, 4], ![-102, -114, -53, -22, 1], ![-30, -50, -62, -48, -17]]]
  hmulB := by decide  
  f := ![![![565, -318, -55, 57, 42]], ![![397, -223, -40, 40, 30]], ![![20, -12, 2, 1, 1]], ![![312, -176, -33, 34, 22]], ![![72, -38, -10, 4, 9]]]
  g := ![![![37, -76, 5, 25, 19], ![83, -151, -5, 35, 31], ![48, -64, -22, -5, 4], ![94, -114, -53, -22, 1], ![66, -50, -62, -48, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI211N2 : Nat.card (O ⧸ I211N2) = 211 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI211N2)

lemma isPrimeI211N2 : Ideal.IsPrime I211N2 := prime_ideal_of_norm_prime hp211.out _ NI211N2
def MulI211N0 : IdealMulLeCertificate' Table 
  ![![-969, 538, 3, 47, -120]] ![![5889, -3032, -4236, 2388, 194]]
  ![![-565, 318, 55, -57, -42]] where
 M := ![![![-565, 318, 55, -57, -42]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI211N1 : IdealMulLeCertificate' Table 
  ![![-565, 318, 55, -57, -42]] ![![-83, -76, 5, 25, 19]]
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

def I223N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 10, 2, -10, 6]] i)))

def SI223N0: IdealEqSpanCertificate' Table ![![-7, 10, 2, -10, 6]] 
 ![![223, 0, 0, 0, 0], ![0, 223, 0, 0, 0], ![122, 161, 1, 0, 0], ![155, 57, 0, 1, 0], ![105, 43, 0, 0, 1]] where
  M :=![![![-7, 10, 2, -10, 6], ![-68, 23, 66, -6, -26], ![194, -90, -147, 66, 20], ![-74, 74, 22, -79, 50], ![-272, 48, 284, 24, -145]]]
  hmulB := by decide  
  f := ![![![1127, -578, 34, -26, 146]], ![![-1452, 833, -22, 42, -198]], ![![-424, 281, 3, 16, -62]], ![![405, -185, 18, -7, 50]], ![![253, -113, 12, -4, 31]]]
  g := ![![![3, 0, 2, -10, 6], ![-20, -41, 66, -6, -26], ![26, 85, -147, 66, 20], ![19, -5, 22, -79, 50], ![-105, -183, 284, 24, -145]]]
  hle1 := by decide   
  hle2 := by decide  


def P223P0 : CertificateIrreducibleZModOfList' 223 2 2 7 [40, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [139, 222], [0, 1]]
 g := ![![[69, 210], [187, 101], [214, 217], [190, 212], [77, 156], [128], [139, 1]], ![[46, 13], [177, 122], [49, 6], [222, 11], [130, 67], [128], [55, 222]]]
 h' := ![![[139, 222], [102, 136], [137, 205], [205, 70], [42, 124], [11, 143], [15, 103], [0, 1]], ![[0, 1], [51, 87], [88, 18], [123, 153], [107, 99], [41, 80], [60, 120], [139, 222]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [197]]
 b := ![[], [123, 210]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI223N0 : CertifiedPrimeIdeal' SI223N0 223 where
  n := 2
  hpos := by decide
  P := [40, 84, 1]
  hirr := P223P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-439455, 96812, 318480, -56843, -13564]
  a := ![51, -28, -25, 50, 103]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-130310, -212355, 318480, -56843, -13564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI223N0 : Ideal.IsPrime I223N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI223N0 B_one_repr
lemma NI223N0 : Nat.card (O ⧸ I223N0) = 49729 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI223N0

def I223N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![327, -156, -247, 115, 30]] i)))

def SI223N1: IdealEqSpanCertificate' Table ![![327, -156, -247, 115, 30]] 
 ![![223, 0, 0, 0, 0], ![58, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![179, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![327, -156, -247, 115, 30], ![-432, 363, 175, -379, 200], ![-886, 86, 988, 175, -579], ![2654, -1258, -2019, 916, 260], ![-3558, 2398, 2012, -2266, 741]]]
  hmulB := by decide  
  f := ![![![21926751, -11861262, 579833, -496161, 2940857]], ![![5571420, -3013855, 147331, -126071, 747249]], ![![7331503, -3965972, 193875, -165898, 983315]], ![![17459555, -9444734, 461702, -395077, 2341708]], ![![9980639, -5399020, 263929, -225843, 1338622]]]
  g := ![![![17, -156, -247, 115, 30], ![60, 363, 175, -379, 200], ![-228, 86, 988, 175, -579], ![147, -1258, -2019, 916, 260], ![185, 2398, 2012, -2266, 741]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N1 : Nat.card (O ⧸ I223N1) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N1)

lemma isPrimeI223N1 : Ideal.IsPrime I223N1 := prime_ideal_of_norm_prime hp223.out _ NI223N1

def I223N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -2, -1, -3, 0]] i)))

def SI223N2: IdealEqSpanCertificate' Table ![![19, -2, -1, -3, 0]] 
 ![![223, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![119, 0, 1, 0, 0], ![200, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![19, -2, -1, -3, 0], ![-4, 21, -3, -5, -6], ![28, -4, 0, -3, 1], ![-4, 24, -1, -4, -6], ![18, 6, 0, -2, -1]]]
  hmulB := by decide  
  f := ![![![71, -28, -61, 13, 29]], ![![23, -9, -20, 4, 10]], ![![39, -16, -33, 8, 15]], ![![66, -26, -57, 12, 27]], ![![6, -2, -6, 0, 5]]]
  g := ![![![4, -2, -1, -3, 0], ![0, 21, -3, -5, -6], ![4, -4, 0, -3, 1], ![-3, 24, -1, -4, -6], ![0, 6, 0, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N2 : Nat.card (O ⧸ I223N2) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N2)

lemma isPrimeI223N2 : Ideal.IsPrime I223N2 := prime_ideal_of_norm_prime hp223.out _ NI223N2

def I223N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8315119, -4498084, 219890, -188148, 1115247]] i)))

def SI223N3: IdealEqSpanCertificate' Table ![![8315119, -4498084, 219890, -188148, 1115247]] 
 ![![223, 0, 0, 0, 0], ![213, 1, 0, 0, 0], ![178, 0, 1, 0, 0], ![194, 0, 0, 1, 0], ![88, 0, 0, 0, 1]] where
  M :=![![![8315119, -4498084, 219890, -188148, 1115247], ![-11120728, 6015787, -294082, 251632, -1491543], ![12996854, -7030682, 343697, -294082, 1743175], ![-11910564, 6443048, -314968, 269505, -1597477], ![4202012, -2273092, 111122, -95078, 563587]]]
  hmulB := by decide  
  f := ![![![12125, -2384, -12316, -606, 6073]], ![![11251, -2121, -11512, -692, 5768]], ![![10076, -2170, -10057, -232, 4767]], ![![10970, -2152, -11150, -557, 5505]], ![![3040, -192, -3462, -730, 2115]]]
  g := ![![![3881729, -4498084, 219890, -188148, 1115247], ![-5191469, 6015787, -294082, 251632, -1491543], ![6067294, -7030682, 343697, -294082, 1743175], ![-5560186, 6443048, -314968, 269505, -1597477], ![1961616, -2273092, 111122, -95078, 563587]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI223N3 : Nat.card (O ⧸ I223N3) = 223 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI223N3)

lemma isPrimeI223N3 : Ideal.IsPrime I223N3 := prime_ideal_of_norm_prime hp223.out _ NI223N3
def MulI223N0 : IdealMulLeCertificate' Table 
  ![![-7, 10, 2, -10, 6]] ![![327, -156, -247, 115, 30]]
  ![![-56269, 31862, 37717, -27001, 2478]] where
 M := ![![![-56269, 31862, 37717, -27001, 2478]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N1 : IdealMulLeCertificate' Table 
  ![![-56269, 31862, 37717, -27001, 2478]] ![![19, -2, -1, -3, 0]]
  ![![12125, -2384, -12316, -606, 6073]] where
 M := ![![![12125, -2384, -12316, -606, 6073]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI223N2 : IdealMulLeCertificate' Table 
  ![![12125, -2384, -12316, -606, 6073]] ![![8315119, -4498084, 219890, -188148, 1115247]]
  ![![223, 0, 0, 0, 0]] where
 M := ![![![223, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I227N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 10, -8, 4, -3]] i)))

def SI227N0: IdealEqSpanCertificate' Table ![![-17, 10, -8, 4, -3]] 
 ![![227, 0, 0, 0, 0], ![0, 227, 0, 0, 0], ![102, 86, 1, 0, 0], ![19, 118, 0, 1, 0], ![213, 76, 0, 0, 1]] where
  M :=![![![-17, 10, -8, 4, -3], ![26, -9, 4, -12, 11], ![-72, 28, 31, 4, -23], ![118, -58, -58, 27, 11], ![-108, 76, 50, -66, 23]]]
  hmulB := by decide  
  f := ![![![-287, -230, 98, 158, 95]], ![![-694, -583, 202, 354, 221]], ![![-394, -326, 121, 206, 127]], ![![-389, -326, 114, 199, 124]], ![![-505, -414, 160, 268, 164]]]
  g := ![![![6, 2, -8, 4, -3], ![-11, 1, 4, -12, 11], ![7, -6, 31, 4, -23], ![14, 4, -58, 27, 11], ![-39, 8, 50, -66, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P227P0 : CertificateIrreducibleZModOfList' 227 2 2 7 [210, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [222, 226], [0, 1]]
 g := ![![[200, 40], [51, 101], [69], [71], [87], [157, 175], [222, 1]], ![[0, 187], [0, 126], [69], [71], [87], [190, 52], [217, 226]]]
 h' := ![![[222, 226], [186, 128], [74, 151], [6, 117], [191, 170], [172, 108], [142, 42], [0, 1]], ![[0, 1], [0, 99], [0, 76], [102, 110], [22, 57], [86, 119], [159, 185], [222, 226]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122]]
 b := ![[], [39, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI227N0 : CertifiedPrimeIdeal' SI227N0 227 where
  n := 2
  hpos := by decide
  P := [210, 5, 1]
  hirr := P227P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-29712, 7524, 22321, -4649, -2911]
  a := ![-12, 9, 7, -10, -27]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7040, -5032, 22321, -4649, -2911]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI227N0 : Ideal.IsPrime I227N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI227N0 B_one_repr
lemma NI227N0 : Nat.card (O ⧸ I227N0) = 51529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI227N0

def I227N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, -6, 20, 12, -18]] i)))

def SI227N1: IdealEqSpanCertificate' Table ![![-13, -6, 20, 12, -18]] 
 ![![227, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![152, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![144, 0, 0, 0, 1]] where
  M :=![![![-13, -6, 20, 12, -18], ![212, -87, -176, 52, 42], ![-378, 210, 257, -176, 10], ![-86, -50, 152, 101, -146], ![1012, -356, -884, 172, 277]]]
  hmulB := by decide  
  f := ![![![527745, -285554, 13956, -11932, 70798]], ![![138707, -75053, 3668, -3136, 18608]], ![![357014, -193174, 9441, -8072, 47894]], ![![22243, -12036, 588, -503, 2984]], ![![335956, -181780, 8884, -7596, 45069]]]
  g := ![![![-1, -6, 20, 12, -18], ![113, -87, -176, 52, 42], ![-228, 210, 257, -176, 10], ![-1, -50, 152, 101, -146], ![508, -356, -884, 172, 277]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N1 : Nat.card (O ⧸ I227N1) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N1)

lemma isPrimeI227N1 : Ideal.IsPrime I227N1 := prime_ideal_of_norm_prime hp227.out _ NI227N1

def I227N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 5, 5, 2]] i)))

def SI227N2: IdealEqSpanCertificate' Table ![![1, 2, 5, 5, 2]] 
 ![![227, 0, 0, 0, 0], ![109, 1, 0, 0, 0], ![134, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![1, 2, 5, 5, 2], ![-10, -3, 15, 15, 8], ![-20, -12, 14, 15, 7], ![-36, -32, 21, 34, 18], ![-50, -30, 24, 26, 19]]]
  hmulB := by decide  
  f := ![![![-11135, 6028, -295, 253, -1497]], ![![-5281, 2859, -140, 120, -710]], ![![-6650, 3600, -176, 151, -894]], ![![-4001, 2166, -106, 91, -538]], ![![-1496, 810, -40, 34, -201]]]
  g := ![![![-6, 2, 5, 5, 2], ![-14, -3, 15, 15, 8], ![-9, -12, 14, 15, 7], ![-12, -32, 21, 34, 18], ![-12, -30, 24, 26, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N2 : Nat.card (O ⧸ I227N2) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N2)

lemma isPrimeI227N2 : Ideal.IsPrime I227N2 := prime_ideal_of_norm_prime hp227.out _ NI227N2

def I227N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-963767, 521350, -25485, 21809, -129262]] i)))

def SI227N3: IdealEqSpanCertificate' Table ![![-963767, 521350, -25485, 21809, -129262]] 
 ![![227, 0, 0, 0, 0], ![113, 1, 0, 0, 0], ![142, 0, 1, 0, 0], ![50, 0, 0, 1, 0], ![158, 0, 0, 0, 1]] where
  M :=![![![-963767, 521350, -25485, 21809, -129262], ![1288944, -697265, 34089, -29161, 172880], ![-1506408, 814888, -39834, 34089, -202041], ![1380484, -746792, 36511, -31230, 185160], ![-487046, 263454, -12876, 11026, -65319]]]
  hmulB := by decide  
  f := ![![![-16123, 9052, 10923, -7599, 537]], ![![-8035, 4465, 5488, -3720, 198]], ![![-9678, 5532, 6464, -4703, 468]], ![![-4136, 2318, 2805, -1944, 133]], ![![-10908, 5918, 7588, -4842, 53]]]
  g := ![![![-162663, 521350, -25485, 21809, -129262], ![217543, -697265, 34089, -29161, 172880], ![-254248, 814888, -39834, 34089, -202041], ![232994, -746792, 36511, -31230, 185160], ![-82202, 263454, -12876, 11026, -65319]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI227N3 : Nat.card (O ⧸ I227N3) = 227 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI227N3)

lemma isPrimeI227N3 : Ideal.IsPrime I227N3 := prime_ideal_of_norm_prime hp227.out _ NI227N3
def MulI227N0 : IdealMulLeCertificate' Table 
  ![![-17, 10, -8, 4, -3]] ![![-13, -6, 20, 12, -18]]
  ![![1985, -1580, -896, 1612, -769]] where
 M := ![![![1985, -1580, -896, 1612, -769]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N1 : IdealMulLeCertificate' Table 
  ![![1985, -1580, -896, 1612, -769]] ![![1, 2, 5, 5, 2]]
  ![![16123, -9052, -10923, 7599, -537]] where
 M := ![![![16123, -9052, -10923, 7599, -537]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI227N2 : IdealMulLeCertificate' Table 
  ![![16123, -9052, -10923, 7599, -537]] ![![-963767, 521350, -25485, 21809, -129262]]
  ![![227, 0, 0, 0, 0]] where
 M := ![![![-227, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I229N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0, 0, 0]] i)))

def SI229N0: IdealEqSpanCertificate' Table ![![229, 0, 0, 0, 0]] 
 ![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]] where
  M :=![![![229, 0, 0, 0, 0], ![0, 229, 0, 0, 0], ![0, 0, 229, 0, 0], ![0, 0, 0, 229, 0], ![0, 0, 0, 0, 229]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P229P0 : CertificateIrreducibleZModOfList' 229 5 2 7 [182, 203, 159, 210, 131, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 193, 124, 28, 149], [149, 37, 114, 21, 93], [41, 40, 92, 218, 83], [79, 187, 128, 191, 133], [0, 1]]
 g := ![![[201, 59, 3, 158, 212], [204, 31, 148, 62], [113, 109, 138, 17, 151], [151, 127, 13, 172], [141, 212, 120, 20], [5, 98, 1], []], ![[116, 68, 92, 129, 98, 161, 65, 42], [169, 164, 77, 180], [87, 34, 4, 131, 28, 116, 125, 174], [12, 75, 188, 180], [147, 106, 186, 144], [87, 57, 201, 158, 146, 209, 201, 185], [60, 227, 79, 77, 78, 100, 98, 44]], ![[195, 153, 227, 207, 207, 221, 104, 102], [188, 52, 75, 5], [195, 153, 181, 89, 193, 124, 139, 102], [49, 115, 176, 149], [126, 207, 110, 104], [167, 20, 55, 68, 58, 187, 101, 22], [121, 77, 114, 99, 82, 137, 15, 109]], ![[175, 171, 39, 117, 115, 164, 219, 118], [191, 177, 102, 1], [207, 53, 58, 107, 165, 101, 102, 217], [12, 8, 221, 97], [4, 112, 55, 134], [111, 110, 221, 84, 60, 182, 148, 183], [216, 106, 66, 184, 112, 132, 31, 203]], ![[80, 5, 220, 206, 219, 158, 9, 59], [89, 214, 13, 42], [193, 35, 31, 195, 201, 30, 209, 133], [36, 137, 200, 1], [28, 154, 125, 80], [176, 209, 95, 124, 5, 45, 213, 179], [125, 68, 117, 119, 196, 108, 109, 120]]]
 h' := ![![[58, 193, 124, 28, 149], [74, 125, 78, 22, 208], [44, 164, 163, 210, 156], [24, 174, 214, 205, 36], [22, 159, 90, 103, 115], [6, 156, 197, 111, 132], [0, 0, 0, 1], [0, 1]], ![[149, 37, 114, 21, 93], [160, 31, 73, 170, 153], [71, 94, 122, 77, 167], [131, 149, 75, 45, 106], [224, 94, 138, 7, 62], [177, 141, 14, 164, 12], [76, 203, 166, 146, 87], [58, 193, 124, 28, 149]], ![[41, 40, 92, 218, 83], [34, 118, 58, 115, 20], [154, 100, 185, 220, 163], [1, 102, 6, 87, 20], [149, 137, 159, 41, 81], [160, 226, 53, 151, 185], [6, 166, 102, 116, 21], [149, 37, 114, 21, 93]], ![[79, 187, 128, 191, 133], [103, 53, 38, 197, 117], [61, 83, 112, 227, 228], [12, 23, 193, 122, 68], [89, 31, 136, 129, 201], [151, 21, 130, 224, 94], [68, 35, 1, 1, 225], [41, 40, 92, 218, 83]], ![[0, 1], [45, 131, 211, 183, 189], [199, 17, 105, 182, 202], [32, 10, 199, 228, 228], [114, 37, 164, 178, 228], [114, 143, 64, 37, 35], [152, 54, 189, 194, 125], [79, 187, 128, 191, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [179, 56, 57, 163], [], [], []]
 b := ![[], [74, 7, 102, 164, 211], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI229N0 : CertifiedPrimeIdeal' SI229N0 229 where
  n := 5
  hpos := by decide
  P := [182, 203, 159, 210, 131, 1]
  hirr := P229P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8227917330, 1582667090, -730793044, -4966968322, 8653237656]
  a := ![-16, 10, 4, -26, -12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-35929770, 6911210, -3191236, -21689818, 37787064]
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

def I233N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3393, -1242, -394, 206, 90]] i)))

def SI233N0: IdealEqSpanCertificate' Table ![![-3393, -1242, -394, 206, 90]] 
 ![![233, 0, 0, 0, 0], ![0, 233, 0, 0, 0], ![114, 214, 1, 0, 0], ![10, 26, 0, 1, 0], ![177, 149, 0, 0, 1]] where
  M :=![![![-3393, -1242, -394, 206, 90], ![-1088, -4267, -1370, -582, 322], ![-2042, 754, -1609, -1370, -904], ![3162, -1194, -3350, -3373, -1254], ![2480, 2176, -3348, -3744, -2003]]]
  hmulB := by decide  
  f := ![![![-5497, 10078, -2966, -12718, 10674]], ![![-122424, 41613, 108514, -18650, -36110]], ![![-113900, 42540, 97307, -22886, -27868]], ![![-14128, 5444, 11910, -3081, -3206]], ![![-84689, 34847, 69280, -21672, -15903]]]
  g := ![![![101, 276, -394, 206, 90], ![446, 1099, -1370, -582, 322], ![1524, 2212, -1609, -1370, -904], ![2750, 4250, -3350, -3373, -1254], ![3331, 4783, -3348, -3744, -2003]]]
  hle1 := by decide   
  hle2 := by decide  


def P233P0 : CertificateIrreducibleZModOfList' 233 2 2 7 [222, 228, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 232], [0, 1]]
 g := ![![[64, 19], [171], [60], [89, 101], [112], [188, 131], [5, 1]], ![[159, 214], [171], [60], [128, 132], [112], [144, 102], [10, 232]]]
 h' := ![![[5, 232], [220, 46], [73, 95], [47, 35], [209, 164], [204, 47], [55, 36], [0, 1]], ![[0, 1], [217, 187], [82, 138], [222, 198], [97, 69], [206, 186], [2, 197], [5, 232]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [98, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI233N0 : CertifiedPrimeIdeal' SI233N0 233 where
  n := 2
  hpos := by decide
  P := [222, 228, 1]
  hirr := P233P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6411, 4717, 7632, -963, -4846]
  a := ![1, 9, 7, 2, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-39, -3783, 7632, -963, -4846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI233N0 : Ideal.IsPrime I233N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI233N0 B_one_repr
lemma NI233N0 : Nat.card (O ⧸ I233N0) = 54289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI233N0

def I233N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![231, 218, -22, -78, -58]] i)))

def SI233N1: IdealEqSpanCertificate' Table ![![231, 218, -22, -78, -58]] 
 ![![233, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![174, 0, 0, 1, 0], ![61, 0, 0, 0, 1]] where
  M :=![![![231, 218, -22, -78, -58], ![480, 433, -6, -122, -98], ![186, 206, 47, -6, -24], ![358, 362, 118, 19, -26], ![144, 192, 148, 96, 25]]]
  hmulB := by decide  
  f := ![![![-2721, 1594, 1766, -1378, 198]], ![![-1198, 693, 786, -594, 74]], ![![-1160, 698, 735, -614, 112]], ![![-2128, 1246, 1382, -1077, 154]], ![![-685, 362, 482, -290, -9]]]
  g := ![![![-11, 218, -22, -78, -58], ![-68, 433, -6, -122, -98], ![-100, 206, 47, -6, -24], ![-218, 362, 118, 19, -26], ![-229, 192, 148, 96, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N1 : Nat.card (O ⧸ I233N1) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N1)

lemma isPrimeI233N1 : Ideal.IsPrime I233N1 := prime_ideal_of_norm_prime hp233.out _ NI233N1

def I233N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21489, -11646, 575, -477, 2890]] i)))

def SI233N2: IdealEqSpanCertificate' Table ![![21489, -11646, 575, -477, 2890]] 
 ![![233, 0, 0, 0, 0], ![196, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![143, 0, 0, 1, 0], ![226, 0, 0, 0, 1]] where
  M :=![![![21489, -11646, 575, -477, 2890], ![-28802, 15525, -747, 673, -3844], ![33584, -18208, 896, -747, 4517], ![-30864, 16612, -801, 724, -4114], ![10818, -5922, 296, -226, 1471]]]
  hmulB := by decide  
  f := ![![![-9857, 3144, 8941, -1199, -3227]], ![![-8120, 2555, 7399, -937, -2711]], ![![-1525, 560, 1313, -292, -389]], ![![-6385, 2034, 5794, -773, -2094]], ![![-8584, 2582, 7936, -818, -3045]]]
  g := ![![![7297, -11646, 575, -477, 2890], ![-9762, 15525, -747, 673, -3844], ![11411, -18208, 896, -747, 4517], ![-10447, 16612, -801, 724, -4114], ![3698, -5922, 296, -226, 1471]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N2 : Nat.card (O ⧸ I233N2) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N2)

lemma isPrimeI233N2 : Ideal.IsPrime I233N2 := prime_ideal_of_norm_prime hp233.out _ NI233N2

def I233N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -10, -15, 9, 0]] i)))

def SI233N3: IdealEqSpanCertificate' Table ![![19, -10, -15, 9, 0]] 
 ![![233, 0, 0, 0, 0], ![207, 1, 0, 0, 0], ![141, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![19, -10, -15, 9, 0], ![-6, 15, -5, -21, 18], ![-100, 28, 92, -5, -39], ![176, -92, -123, 72, 4], ![-146, 130, 52, -138, 77]]]
  hmulB := by decide  
  f := ![![![-2899, -2512, 423, 1087, 745]], ![![-2601, -2255, 378, 974, 668]], ![![-1767, -1532, 255, 660, 453]], ![![-359, -314, 46, 129, 90]], ![![-1158, -1006, 162, 428, 295]]]
  g := ![![![17, -10, -15, 9, 0], ![-15, 15, -5, -21, 18], ![-65, 28, 92, -5, -39], ![147, -92, -123, 72, 4], ![-162, 130, 52, -138, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI233N3 : Nat.card (O ⧸ I233N3) = 233 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI233N3)

lemma isPrimeI233N3 : Ideal.IsPrime I233N3 := prime_ideal_of_norm_prime hp233.out _ NI233N3
def MulI233N0 : IdealMulLeCertificate' Table 
  ![![-3393, -1242, -394, 206, 90]] ![![231, 218, -22, -78, -58]]
  ![![-1366519, -1266772, 101208, 431096, 324860]] where
 M := ![![![-1366519, -1266772, 101208, 431096, 324860]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N1 : IdealMulLeCertificate' Table 
  ![![-1366519, -1266772, 101208, 431096, 324860]] ![![21489, -11646, 575, -477, 2890]]
  ![![728398361, -357404458, 2063291, -37615225, 81728310]] where
 M := ![![![728398361, -357404458, 2063291, -37615225, 81728310]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI233N2 : IdealMulLeCertificate' Table 
  ![![728398361, -357404458, 2063291, -37615225, 81728310]] ![![19, -10, -15, 9, 0]]
  ![![233, 0, 0, 0, 0]] where
 M := ![![![-2774946353, 1498002668, -72585558, 63959432, -371129623]]]
 hmul := by decide  
 g := ![![![![-11909641, 6429196, -311526, 274504, -1592831]]]]
 hle2 := by decide  


def PBC233 : ContainsPrimesAboveP 233 ![I233N0, I233N1, I233N2, I233N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI233N0
    exact isPrimeI233N1
    exact isPrimeI233N2
    exact isPrimeI233N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 233 (by decide) (𝕀 ⊙ MulI233N0 ⊙ MulI233N1 ⊙ MulI233N2)
instance hp239 : Fact (Nat.Prime 239) := {out := by norm_num}

def I239N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![215, -96, 10, -4, 26]] i)))

def SI239N0: IdealEqSpanCertificate' Table ![![215, -96, 10, -4, 26]] 
 ![![239, 0, 0, 0, 0], ![0, 239, 0, 0, 0], ![0, 0, 239, 0, 0], ![93, 60, 152, 1, 0], ![234, 171, 226, 0, 1]] where
  M :=![![![215, -96, 10, -4, 26], ![-254, 165, 6, 16, -34], ![308, -172, 23, 6, 50], ![-316, 148, 26, 39, -24], ![76, -84, 24, 36, 33]]]
  hmulB := by decide  
  f := ![![![9, 0, -6, 0, 2]], ![![-26, 19, 22, -12, -2]], ![![28, -20, -11, 22, -10]], ![![15, -8, -4, 11, -6]], ![![16, -5, 0, 12, -9]]]
  g := ![![![-23, -18, -22, -4, 26], ![26, 21, 22, 16, -34], ![-50, -38, -51, 6, 50], ![7, 8, -2, 39, -24], ![-46, -33, -54, 36, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P239P0 : CertificateIrreducibleZModOfList' 239 3 2 7 [186, 238, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 213, 223], [57, 25, 16], [0, 1]]
 g := ![![[191, 132, 183], [126, 154, 150], [41, 120, 36], [55, 147, 58], [138, 169], [117, 113, 88], [1]], ![[52, 208, 113, 89], [135, 104, 141, 38], [111, 163, 81, 233], [41, 236, 104, 39], [31, 176], [127, 231, 219, 209], [80, 60, 202, 206]], ![[164, 116, 180, 100], [185, 119, 70, 20], [124, 94, 55, 4], [139, 98, 170, 55], [147, 29], [179, 47, 59, 90], [218, 121, 225, 33]]]
 h' := ![![[85, 213, 223], [225, 168, 209], [22, 6, 110], [47, 177, 233], [74, 53, 192], [226, 72, 226], [53, 1, 142], [0, 1]], ![[57, 25, 16], [14, 237, 147], [50, 167, 25], [196, 143, 125], [144, 220, 128], [202, 4, 196], [72, 165, 188], [85, 213, 223]], ![[0, 1], [82, 73, 122], [230, 66, 104], [114, 158, 120], [193, 205, 158], [222, 163, 56], [50, 73, 148], [57, 25, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 237], []]
 b := ![[], [162, 46, 209], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI239N0 : CertifiedPrimeIdeal' SI239N0 239 where
  n := 3
  hpos := by decide
  P := [186, 238, 97, 1]
  hirr := P239P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20572, 606, 10032, -916, 11885]
  a := ![-3, 0, 1, -4, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11366, -8271, -10614, -916, 11885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI239N0 : Ideal.IsPrime I239N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI239N0 B_one_repr
lemma NI239N0 : Nat.card (O ⧸ I239N0) = 13651919 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI239N0

def I239N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -18, -18, 16, -4]] i)))

def SI239N1: IdealEqSpanCertificate' Table ![![29, -18, -18, 16, -4]] 
 ![![239, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![159, 0, 1, 0, 0], ![193, 0, 0, 1, 0], ![123, 0, 0, 0, 1]] where
  M :=![![![29, -18, -18, 16, -4], ![38, 5, -50, -20, 36], ![-234, 90, 199, -50, -56], ![242, -146, -150, 131, -30], ![24, 112, -132, -168, 181]]]
  hmulB := by decide  
  f := ![![![-119949, 64762, -3154, 2748, -16052]], ![![-24424, 13185, -642, 560, -3268]], ![![-80583, 43508, -2119, 1846, -10784]], ![![-96145, 51908, -2528, 2203, -12866]], ![![-61985, 33466, -1630, 1420, -8295]]]
  g := ![![![5, -18, -18, 16, -4], ![30, 5, -50, -20, 36], ![-83, 90, 199, -50, -56], ![41, -146, -150, 131, -30], ![107, 112, -132, -168, 181]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N1 : Nat.card (O ⧸ I239N1) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N1)

lemma isPrimeI239N1 : Ideal.IsPrime I239N1 := prime_ideal_of_norm_prime hp239.out _ NI239N1

def I239N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-319, 170, -8, 8, -42]] i)))

def SI239N2: IdealEqSpanCertificate' Table ![![-319, 170, -8, 8, -42]] 
 ![![239, 0, 0, 0, 0], ![124, 1, 0, 0, 0], ![137, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-319, 170, -8, 8, -42], ![420, -233, 12, -8, 58], ![-498, 266, -13, 12, -66], ![450, -250, 12, -9, 62], ![-164, 84, -4, 4, -21]]]
  hmulB := by decide  
  f := ![![![-97, 46, 88, -32, -50]], ![![-48, 23, 44, -16, -26]], ![![-57, 28, 51, -20, -28]], ![![-4, 2, 4, -1, -2]], ![![-11, 6, 12, -4, -11]]]
  g := ![![![-75, 170, -8, 8, -42], ![102, -233, 12, -8, 58], ![-117, 266, -13, 12, -66], ![110, -250, 12, -9, 62], ![-37, 84, -4, 4, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI239N2 : Nat.card (O ⧸ I239N2) = 239 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI239N2)

lemma isPrimeI239N2 : Ideal.IsPrime I239N2 := prime_ideal_of_norm_prime hp239.out _ NI239N2
def MulI239N0 : IdealMulLeCertificate' Table 
  ![![215, -96, 10, -4, 26]] ![![29, -18, -18, 16, -4]]
  ![![-97, 46, 88, -32, -50]] where
 M := ![![![-97, 46, 88, -32, -50]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI239N1 : IdealMulLeCertificate' Table 
  ![![-97, 46, 88, -32, -50]] ![![-319, 170, -8, 8, -42]]
  ![![239, 0, 0, 0, 0]] where
 M := ![![![239, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I241N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![241, 0, 0, 0, 0]] i)))

def SI241N0: IdealEqSpanCertificate' Table ![![241, 0, 0, 0, 0]] 
 ![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]] where
  M :=![![![241, 0, 0, 0, 0], ![0, 241, 0, 0, 0], ![0, 0, 241, 0, 0], ![0, 0, 0, 241, 0], ![0, 0, 0, 0, 241]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P241P0 : CertificateIrreducibleZModOfList' 241 5 2 7 [207, 221, 86, 233, 119, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 10, 185, 196, 180], [107, 87, 233, 85, 8], [52, 233, 215, 38, 16], [121, 151, 90, 163, 37], [0, 1]]
 g := ![![[208, 111, 60, 103, 125], [213, 112, 48, 188], [73, 166, 129, 91], [143, 180, 28, 80], [10, 52, 226, 16, 29], [191, 122, 1], []], ![[194, 97, 22, 148, 193, 119, 116, 45], [52, 104, 199, 10], [73, 133, 99, 174], [97, 174, 74, 183], [83, 29, 9, 228, 44, 79, 73, 80], [168, 183, 236, 62, 17, 82, 104, 187], [69, 54, 201, 24, 178, 212, 91, 41]], ![[74, 46, 59, 68, 195, 164, 6, 4], [224, 183, 122, 181], [203, 207, 233, 2], [74, 179, 23, 162], [85, 129, 26, 160, 207, 210, 157, 239], [6, 207, 54, 60, 49, 94, 25, 183], [96, 203, 23, 18, 88, 116, 218, 30]], ![[152, 212, 68, 98, 209, 100, 55, 15], [102, 143, 213, 113], [153, 107, 19, 196], [122, 221, 124, 5], [51, 71, 211, 37, 128, 138, 208, 194], [46, 213, 0, 229, 228, 160, 128, 58], [19, 177, 51, 198, 144, 144, 142, 240]], ![[19, 100, 75, 197, 7, 214, 117, 136], [188, 71, 162, 166], [41, 94, 21, 4], [11, 213, 101, 72], [234, 184, 12, 175, 201, 64, 192, 222], [5, 35, 25, 197, 236, 118, 40, 70], [76, 238, 52, 220, 173, 32, 128, 43]]]
 h' := ![![[83, 10, 185, 196, 180], [92, 79, 101, 132, 33], [70, 165, 147, 144, 195], [203, 234, 138, 216, 205], [99, 209, 3, 221, 171], [228, 15, 26, 214, 92], [0, 0, 0, 1], [0, 1]], ![[107, 87, 233, 85, 8], [84, 207, 39, 81, 121], [56, 32, 191, 168, 144], [226, 118, 120, 165, 74], [28, 77, 106, 107, 119], [196, 76, 119, 27, 81], [71, 216, 59, 18, 132], [83, 10, 185, 196, 180]], ![[52, 233, 215, 38, 16], [2, 179, 102, 194, 230], [154, 12, 120, 29, 120], [0, 93, 6, 181, 219], [48, 5, 224, 53, 198], [88, 200, 167, 4, 209], [171, 176, 52, 141, 52], [107, 87, 233, 85, 8]], ![[121, 151, 90, 163, 37], [192, 22, 169, 100, 4], [87, 207, 13, 14, 178], [118, 45, 15, 225, 227], [157, 201, 215, 7, 103], [157, 57, 5, 11, 127], [28, 65, 91, 207, 217], [52, 233, 215, 38, 16]], ![[0, 1], [201, 236, 71, 216, 94], [39, 66, 11, 127, 86], [36, 233, 203, 177, 239], [12, 231, 175, 94, 132], [175, 134, 165, 226, 214], [144, 25, 39, 115, 81], [121, 151, 90, 163, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [238, 89, 43, 59], [], [], []]
 b := ![[], [173, 197, 33, 200, 159], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI241N0 : CertifiedPrimeIdeal' SI241N0 241 where
  n := 5
  hpos := by decide
  P := [207, 221, 86, 233, 119, 1]
  hirr := P241P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2415534152167, 946981539180, 2011230702251, -557774757039, -515552603461]
  a := ![12, -6, -3, 8, 29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10022963287, 3929383980, 8345355611, -2314418079, -2139222421]
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

def I251N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![251, 0, 0, 0, 0]] i)))

def SI251N0: IdealEqSpanCertificate' Table ![![251, 0, 0, 0, 0]] 
 ![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]] where
  M :=![![![251, 0, 0, 0, 0], ![0, 251, 0, 0, 0], ![0, 0, 251, 0, 0], ![0, 0, 0, 251, 0], ![0, 0, 0, 0, 251]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P251P0 : CertificateIrreducibleZModOfList' 251 5 2 7 [147, 5, 36, 235, 175, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [216, 103, 156, 129, 66], [21, 166, 103, 98, 239], [137, 64, 143, 195, 56], [204, 168, 100, 80, 141], [0, 1]]
 g := ![![[60, 80, 126, 91, 74], [16, 243, 76, 175, 28], [167, 194, 89, 214], [233, 47, 126, 96, 69], [244, 160, 145, 89, 195], [19, 76, 1], []], ![[26, 51, 171, 134, 91, 72, 160, 74], [133, 227, 194, 241, 118, 88, 183, 110], [122, 243, 184, 237], [6, 86, 150, 243, 103, 185, 146, 69], [53, 98, 37, 144, 68, 28, 155, 142], [123, 168, 171, 76, 72, 54, 31, 194], [17, 234, 41, 31, 205, 178, 202, 101]], ![[175, 242, 170, 57, 114, 211, 179, 30], [29, 67, 87, 124, 95, 57, 119, 30], [214, 140, 52, 197], [146, 197, 244, 85, 90, 79, 83, 231], [157, 80, 98, 231, 61, 227, 159, 148], [15, 105, 16, 179, 201, 187, 133, 212], [150, 93, 220, 45, 85, 219, 113, 29]], ![[111, 218, 104, 4, 172, 109, 47, 137], [181, 86, 163, 224, 221, 84, 52, 87], [25, 71, 88, 152], [196, 80, 230, 12, 229, 10, 15, 42], [61, 97, 4, 49, 225, 30, 129, 228], [115, 56, 77, 142, 234, 123, 51, 184], [61, 14, 53, 102, 23, 220, 143, 167]], ![[122, 233, 88, 64, 247, 152, 135, 183], [55, 191, 4, 81, 155, 13, 202, 188], [2, 104, 155, 161], [216, 22, 221, 115, 81, 146, 57, 234], [165, 219, 145, 28, 37, 139, 177, 168], [72, 150, 187, 89, 182, 215, 6, 43], [144, 8, 196, 65, 160, 157, 193, 53]]]
 h' := ![![[216, 103, 156, 129, 66], [158, 180, 15, 246, 227], [222, 209, 187, 208, 84], [136, 81, 138, 132, 88], [25, 129, 190, 125, 128], [219, 28, 44, 73, 114], [0, 0, 0, 1], [0, 1]], ![[21, 166, 103, 98, 239], [51, 82, 246, 177, 10], [84, 189, 171, 70, 13], [166, 110, 197, 174, 194], [117, 50, 64, 32, 114], [230, 58, 62, 96, 126], [57, 172, 232, 111, 189], [216, 103, 156, 129, 66]], ![[137, 64, 143, 195, 56], [205, 195, 129, 147, 25], [135, 38, 71, 129, 226], [192, 114, 65, 178, 85], [125, 35, 14, 237, 13], [66, 120, 32, 210, 197], [12, 130, 35, 96, 153], [21, 166, 103, 98, 239]], ![[204, 168, 100, 80, 141], [209, 157, 16, 89, 156], [94, 221, 44, 79, 212], [2, 123, 153, 171, 34], [106, 121, 120, 34, 38], [77, 31, 194, 197, 111], [178, 188, 54, 215, 122], [137, 64, 143, 195, 56]], ![[0, 1], [94, 139, 96, 94, 84], [131, 96, 29, 16, 218], [26, 74, 200, 98, 101], [115, 167, 114, 74, 209], [165, 14, 170, 177, 205], [7, 12, 181, 79, 38], [204, 168, 100, 80, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141, 122, 202, 210], [], [], []]
 b := ![[], [83, 129, 136, 69, 225], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI251N0 : CertifiedPrimeIdeal' SI251N0 251 where
  n := 5
  hpos := by decide
  P := [147, 5, 36, 235, 175, 1]
  hirr := P251P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-237889539339, 135157813344, 156690219071, -116606457309, 13281675040]
  a := ![9, -6, -5, 8, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-947767089, 538477344, 624263821, -464567559, 52915040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI251N0 : Ideal.IsPrime I251N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI251N0 B_one_repr
lemma NI251N0 : Nat.card (O ⧸ I251N0) = 996250626251 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI251N0

def PBC251 : ContainsPrimesAboveP 251 ![I251N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI251N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![251, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 251 (by decide) 𝕀



lemma PB314I5_primes (p : ℕ) :
  p ∈ Set.range ![199, 211, 223, 227, 229, 233, 239, 241, 251] ↔ Nat.Prime p ∧ 197 < p ∧ p ≤ 251 := by
  rw [← List.mem_ofFn']
  convert primes_range 197 251 (by omega)

def PB314I5 : PrimesBelowBoundCertificateInterval O 197 251 314 where
  m := 9
  g := ![3, 3, 4, 4, 1, 4, 3, 1, 1]
  P := ![199, 211, 223, 227, 229, 233, 239, 241, 251]
  hP := PB314I5_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I199N0, I199N1, I199N2]
    · exact ![I211N0, I211N1, I211N2]
    · exact ![I223N0, I223N1, I223N2, I223N3]
    · exact ![I227N0, I227N1, I227N2, I227N3]
    · exact ![I229N0]
    · exact ![I233N0, I233N1, I233N2, I233N3]
    · exact ![I239N0, I239N1, I239N2]
    · exact ![I241N0]
    · exact ![I251N0]
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
    · exact ![7880599, 199, 199]
    · exact ![44521, 44521, 211]
    · exact ![49729, 223, 223, 223]
    · exact ![51529, 227, 227, 227]
    · exact ![629763392149]
    · exact ![54289, 233, 233, 233]
    · exact ![13651919, 239, 239]
    · exact ![812990017201]
    · exact ![996250626251]
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
      exact NI227N2
      exact NI227N3
    · dsimp ; intro j
      fin_cases j
      exact NI229N0
    · dsimp ; intro j
      fin_cases j
      exact NI233N0
      exact NI233N1
      exact NI233N2
      exact NI233N3
    · dsimp ; intro j
      fin_cases j
      exact NI239N0
      exact NI239N1
      exact NI239N2
    · dsimp ; intro j
      fin_cases j
      exact NI241N0
    · dsimp ; intro j
      fin_cases j
      exact NI251N0
  β := ![I199N1, I199N2, I211N2, I223N1, I223N2, I223N3, I227N1, I227N2, I227N3, I233N1, I233N2, I233N3, I239N1, I239N2]
  Il := ![[I199N1, I199N2], [I211N2], [I223N1, I223N2, I223N3], [I227N1, I227N2, I227N3], [], [I233N1, I233N2, I233N3], [I239N1, I239N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
