
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![164, 47, -14, -6, -7]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![164, 47, -14, -6, -7]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![6, 83, 38, 1, 0], ![2, 75, 0, 0, 1]] where
  M :=![![![164, 47, -14, -6, -7], ![-196, 109, 52, -100, -12], ![-92, -228, 149, 232, -100], ![-407, -73, -96, -87, 111], ![927, 173, -180, -16, 30]]]
  hmulB := by decide  
  f := ![![![-1274, 37, -76, -184, 145]], ![![3328, -77, 212, 492, -368]], ![![-4204, 148, -233, -592, 492]], ![![1057, -6, 80, 167, -107]], ![![2283, -52, 146, 338, -252]]]
  g := ![![![2, 10, 2, -6, -7], ![4, 87, 36, -100, -12], ![-12, -112, -81, 232, -100], ![-1, -11, 30, -87, 111], ![9, -7, 4, -16, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [31, 25, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 106, 42], [56, 0, 65], [0, 1]]
 g := ![![[5, 63, 14], [70, 11, 25], [65, 10], [53, 61, 102], [5, 64], [1]], ![[65, 89, 29, 14], [30, 26, 68, 61], [10, 25], [41, 94, 49, 92], [106, 79], [6, 61, 89, 44]], ![[7, 2, 56, 20], [4, 41, 2, 50], [95, 47], [52, 72, 75, 2], [91, 35], [91, 65, 76, 63]]]
 h' := ![![[59, 106, 42], [77, 61, 11], [71, 51, 102], [69, 33, 63], [57, 83, 67], [76, 82, 8], [0, 1]], ![[56, 0, 65], [17, 33, 101], [6, 23, 2], [67, 19, 102], [50, 81, 62], [74, 35, 20], [59, 106, 42]], ![[0, 1], [30, 13, 102], [46, 33, 3], [40, 55, 49], [61, 50, 85], [97, 97, 79], [56, 0, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 28], []]
 b := ![[], [10, 10, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [31, 25, 99, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12312700, -6301828, -5480911, -5806514, -2163917]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![250974, 5961987, 2010903, -5806514, -2163917]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 2, 18, 4, -11]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-10, 2, 18, 4, -11]] 
 ![![107, 0, 0, 0, 0], ![24, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![51, 0, 0, 0, 1]] where
  M :=![![![-10, 2, 18, 4, -11], ![-228, -123, 18, 56, 8], ![114, -59, -97, 14, 56], ![119, 120, -4, -61, -9], ![121, 172, 94, -58, -74]]]
  hmulB := by decide  
  f := ![![![-1388, 362, 258, -134, 457]], ![![-204, 103, 78, 4, 100]], ![![-438, 161, 119, -20, 175]], ![![123, 46, 40, 49, 11]], ![![-583, 266, 200, -2, 267]]]
  g := ![![![-1, 2, 18, 4, -11], ![14, -123, 18, 56, 8], ![17, -59, -97, 14, 56], ![-18, 120, -4, -61, -9], ![-29, 172, 94, -58, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12, -2, 6, 2, -3]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![-12, -2, 6, 2, -3]] 
 ![![107, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![101, 0, 1, 0, 0], ![103, 0, 0, 1, 0], ![49, 0, 0, 0, 1]] where
  M :=![![![-12, -2, 6, 2, -3], ![-60, -43, 2, 20, 4], ![50, -3, -37, -6, 20], ![45, 38, 4, -17, -7], ![-5, 40, 38, -12, -26]]]
  hmulB := by decide  
  f := ![![![14, 46, -18, 84, -31]], ![![2, 29, -12, 52, -19]], ![![32, 45, -17, 86, -33]], ![![-9, 42, -18, 73, -26]], ![![33, 22, -8, 46, -19]]]
  g := ![![![-5, -2, 6, 2, -3], ![5, -43, 2, 20, 4], ![34, -3, -37, -6, 20], ![-9, 38, 4, -17, -7], ![-39, 40, 38, -12, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![164, 47, -14, -6, -7]] ![![-10, 2, 18, 4, -11]]
  ![![-15513, -6551, 4522, 3864, -1640]] where
 M := ![![![-15513, -6551, 4522, 3864, -1640]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-15513, -6551, 4522, 3864, -1640]] ![![-12, -2, 6, 2, -3]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![987396, 380385, -320358, -235186, 126367]]]
 hmul := by decide  
 g := ![![![![9228, 3555, -2994, -2198, 1181]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1728, -21, 96, 294, -209]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![1728, -21, 96, 294, -209]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![83, 34, 47, 69, 1]] where
  M :=![![![1728, -21, 96, 294, -209], ![-4824, 45, -268, -848, 588], ![6788, -56, 365, 1220, -848], ![-6913, 35, -378, -1253, 857], ![5405, -25, 270, 1004, -690]]]
  hmulB := by decide  
  f := ![![![2, -1, -2, 0, 1]], ![![20, 13, -4, -8, 0]], ![![-4, 8, 9, -4, -8]], ![![-25, -15, 0, 5, 1]], ![![-10, -3, 1, -1, -2]]]
  g := ![![![175, 65, 91, 135, -209], ![-492, -183, -256, -380, 588], ![708, 264, 369, 548, -848], ![-716, -267, -373, -554, 857], ![575, 215, 300, 446, -690]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [84, 7, 107, 71, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 77, 25, 82], [42, 20, 13, 87], [1, 11, 71, 49], [0, 1]]
 g := ![![[87, 37, 75, 94], [18, 40, 15], [5, 0, 62, 12], [89, 81, 37, 21], [29, 38, 1], []], ![[59, 101, 90, 86, 40, 25], [103, 84, 48], [40, 35, 23, 107, 33, 74], [102, 90, 12, 5, 108, 1], [80, 65, 84], [19, 24, 64, 81, 70, 46]], ![[103, 17, 9, 73, 71, 49], [74, 74, 93], [19, 33, 88, 3, 54, 83], [67, 1, 8, 102, 14, 74], [49, 38, 71], [93, 6, 64, 83, 3, 34]], ![[105, 88, 60, 62, 82, 12], [39, 86, 3], [83, 30, 82, 19, 33, 74], [61, 25, 26, 5, 42, 38], [94, 82, 74], [70, 72, 73, 22, 12, 38]]]
 h' := ![![[104, 77, 25, 82], [52, 26, 48, 51], [16, 28, 24, 48], [45, 12, 8, 98], [71, 93, 35, 81], [0, 0, 0, 1], [0, 1]], ![[42, 20, 13, 87], [104, 57, 28, 99], [103, 92, 99, 87], [21, 107, 48, 80], [22, 1, 79, 2], [23, 29, 84, 56], [104, 77, 25, 82]], ![[1, 11, 71, 49], [1, 67, 103, 54], [2, 38, 48, 23], [8, 50, 20, 81], [42, 95, 71, 75], [4, 45, 59, 92], [42, 20, 13, 87]], ![[0, 1], [10, 68, 39, 14], [4, 60, 47, 60], [0, 49, 33, 68], [1, 29, 33, 60], [7, 35, 75, 69], [1, 11, 71, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [71, 104, 52], []]
 b := ![[], [], [89, 15, 19, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [84, 7, 107, 71, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15881539694390, 8130092011548, 6937006477492, 7386944817108, 2855581334324]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2028731294078, -816143792252, -1167663451704, -1739891442672, 2855581334324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, -2, 0, 1]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![2, -1, -2, 0, 1]] 
 ![![109, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![2, -1, -2, 0, 1], ![20, 13, -4, -8, 0], ![-4, 8, 9, -4, -8], ![-25, -15, 0, 5, 1], ![-23, -27, -12, 6, 6]]]
  hmulB := by decide  
  f := ![![![1728, -21, 96, 294, -209]], ![![1224, -15, 68, 208, -148]], ![![1172, -14, 65, 200, -142]], ![![539, -7, 30, 91, -65]], ![![113, -1, 6, 20, -14]]]
  g := ![![![2, -1, -2, 0, 1], ![-4, 13, -4, -8, 0], ![-10, 8, 9, -4, -8], ![9, -15, 0, 5, 1], ![25, -27, -12, 6, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![1728, -21, 96, 294, -209]] ![![2, -1, -2, 0, 1]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 47, -16, 76, -24]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-13, 47, -16, 76, -24]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![32, 84, 80, 1, 0], ![3, 71, 28, 0, 1]] where
  M :=![![![-13, 47, -16, 76, -24], ![-608, -137, 14, -344, 152], ![1838, 201, 29, 690, -344], ![-2076, -205, -40, -743, 378], ![2724, 175, 86, 808, -441]]]
  hmulB := by decide  
  f := ![![![-17, -9, 6, 8, 0]], ![![12, -15, -6, 20, 16]], ![![186, 91, -5, -6, 20]], ![![136, 51, -6, 13, 26]], ![![53, 13, -4, 12, 15]]]
  g := ![![![-21, -41, -48, 76, -24], ![88, 159, 206, -344, 152], ![-170, -295, -403, 690, -344], ![182, 313, 432, -743, 378], ![-193, -322, -462, 808, -441]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [111, 51, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 11, 6], [35, 101, 107], [0, 1]]
 g := ![![[73, 45, 41], [30, 97], [63, 111], [41, 81], [37, 23, 104], [1]], ![[0, 16, 76, 42], [101, 61], [43, 14], [102, 62], [21, 22, 16, 45], [88, 3, 56, 103]], ![[96, 99, 106, 65], [44, 18], [96, 11], [9, 88], [15, 60, 44, 35], [87, 35, 62, 10]]]
 h' := ![![[33, 11, 6], [64, 43, 43], [2, 34, 53], [21, 107, 87], [74, 84, 104], [2, 62, 68], [0, 1]], ![[35, 101, 107], [7, 66, 81], [101, 9, 20], [69, 96, 50], [54, 50, 47], [66, 41, 8], [33, 11, 6]], ![[0, 1], [80, 4, 102], [61, 70, 40], [78, 23, 89], [25, 92, 75], [109, 10, 37], [35, 101, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 75], []]
 b := ![[], [2, 65, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [111, 51, 45, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1207798, -619678, -530284, -559396, -210762]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![153320, 542776, 443564, -559396, -210762]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 3, 0, -2, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![1, 3, 0, -2, 0]] 
 ![![113, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![1, 3, 0, -2, 0], ![0, -1, 6, 4, -4], ![-42, -19, 1, 6, 4], ![30, 5, -4, 1, 0], ![26, 23, -6, -14, 3]]]
  hmulB := by decide  
  f := ![![![-1783, 47, -106, -262, 204]], ![![-69, 2, -4, -10, 8]], ![![-558, 15, -33, -82, 64]], ![![-104, 3, -6, -15, 12]], ![![-478, 13, -28, -70, 55]]]
  g := ![![![0, 3, 0, -2, 0], ![-1, -1, 6, 4, -4], ![-1, -19, 1, 6, 4], ![1, 5, -4, 1, 0], ![1, 23, -6, -14, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 2, 2, 2, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![7, 2, 2, 2, 0]] 
 ![![113, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![77, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![7, 2, 2, 2, 0], ![4, 7, 8, 8, 4], ![56, 20, 19, 24, 8], ![18, 16, 10, 9, 6], ![98, 48, 38, 38, 13]]]
  hmulB := by decide  
  f := ![![![2315, 46, 106, 530, -324]], ![![1572, 31, 72, 360, -220]], ![![1687, 34, 77, 386, -236]], ![![214, 4, 10, 49, -30]], ![![392, 8, 18, 90, -55]]]
  g := ![![![-3, 2, 2, 2, 0], ![-12, 7, 8, 8, 4], ![-31, 20, 19, 24, 8], ![-20, 16, 10, 9, 6], ![-66, 48, 38, 38, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-13, 47, -16, 76, -24]] ![![1, 3, 0, -2, 0]]
  ![![2315, 46, 106, 530, -324]] where
 M := ![![![2315, 46, 106, 530, -324]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![2315, 46, 106, 530, -324]] ![![7, 2, 2, 2, 0]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-304, -579, -312, 208, 239]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-304, -579, -312, 208, 239]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![0, 0, 0, 127, 0], ![88, 64, 97, 20, 1]] where
  M :=![![![-304, -579, -312, 208, 239], ![5112, 2367, -1304, -1332, 416], ![3688, 4414, 1479, -1748, -1332], ![-5111, -2805, 914, 1465, -149], ![-8541, -6939, -474, 3110, 1108]]]
  hmulB := by decide  
  f := ![![![50, -9, 6, -6, -1]], ![![-12, 29, -8, 44, -12]], ![![-152, -34, 9, -92, 44]], ![![211, 43, 0, 109, -47]], ![![-57, -11, 7, -36, 20]]]
  g := ![![![-168, -125, -185, -36, 239], ![-248, -191, -328, -76, 416], ![952, 706, 1029, 196, -1332], ![63, 53, 121, 35, -149], ![-835, -613, -850, -150, 1108]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 4 2 6 [57, 20, 21, 77, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 39, 1, 80], [9, 19, 1, 73], [118, 68, 125, 101], [0, 1]]
 g := ![![[37, 21, 119, 64], [52, 59, 28, 1], [109, 8, 24, 44], [126, 75, 79, 26], [71, 66, 50, 1], []], ![[119, 72, 108, 93, 78, 119], [15, 109, 23, 70, 37, 6], [46, 125, 71, 33, 122, 27], [118, 112, 71, 76, 31, 86], [55, 120, 88, 89, 114, 125], [34, 43, 35, 95, 125, 63]], ![[46, 90, 97, 112, 115, 64], [94, 88, 109, 62, 85, 120], [58, 28, 82, 60, 112, 69], [17, 58, 61, 126, 7, 74], [10, 103, 80, 95, 8, 13], [7, 51, 81, 113, 23, 16]], ![[122, 27, 55, 100, 46, 90], [122, 2, 95, 77, 78, 3], [63, 55, 73, 57, 15, 46], [114, 20, 73, 113, 104, 77], [114, 33, 65, 92, 116, 102], [22, 39, 71, 72, 48, 77]]]
 h' := ![![[50, 39, 1, 80], [84, 15, 10, 119], [10, 105, 116, 1], [57, 98, 75, 60], [17, 25, 54, 91], [0, 0, 0, 1], [0, 1]], ![[9, 19, 1, 73], [20, 66, 37, 61], [118, 47, 107, 17], [2, 60, 26, 100], [90, 23, 61, 6], [126, 63, 52, 94], [50, 39, 1, 80]], ![[118, 68, 125, 101], [116, 75, 58, 19], [31, 13, 55, 36], [79, 92, 125, 62], [106, 104, 35, 56], [76, 46, 15, 78], [9, 19, 1, 73]], ![[0, 1], [70, 98, 22, 55], [61, 89, 103, 73], [57, 4, 28, 32], [87, 102, 104, 101], [49, 18, 60, 81], [118, 68, 125, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8, 84, 115], []]
 b := ![[], [], [20, 17, 32, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 4
  hpos := by decide
  P := [57, 20, 21, 77, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1478347344329, 758975604156, 650524030704, 692883775881, 269042867424]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-174782873929, -129604471740, -200367197712, -36913177737, 269042867424]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 260144641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, 9, -6, 6, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-50, 9, -6, 6, 1]] 
 ![![127, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-50, 9, -6, 6, 1], ![12, -29, 8, -44, 12], ![152, 34, -9, 92, -44], ![-211, -43, 0, -109, 47], ![347, 23, 0, 116, -68]]]
  hmulB := by decide  
  f := ![![![304, 579, 312, -208, -239]], ![![168, 378, 224, -132, -167]], ![![184, 371, 207, -132, -157]], ![![57, 54, 10, -23, -12]], ![![163, 237, 102, -90, -84]]]
  g := ![![![-3, 9, -6, 6, 1], ![13, -29, 8, -44, 12], ![-7, 34, -9, 92, -44], ![19, -43, 0, -109, 47], ![2, 23, 0, 116, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-304, -579, -312, 208, 239]] ![![-50, 9, -6, 6, 1]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [95, 119, 106, 52, 44, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 19, 31, 128, 120], [90, 27, 117, 107, 42], [101, 25, 18, 112, 55], [94, 59, 96, 46, 45], [0, 1]]
 g := ![![[60, 101, 126, 71, 33], [1, 7, 125, 54, 84], [130, 41, 14, 64], [46, 38, 12, 65], [113, 50, 87, 1], [], []], ![[7, 16, 35, 11, 42, 101, 48, 22], [87, 79, 17, 126, 106, 129, 14, 30], [125, 62, 118, 27], [9, 97, 27, 129], [117, 10, 13, 113], [84, 116, 130, 59], [0, 115, 113, 121]], ![[70, 34, 127, 57, 84, 74, 45, 71], [4, 30, 12, 73, 27, 71, 101, 31], [60, 94, 30, 64], [10, 69, 96, 107], [83, 99, 36, 64], [100, 91, 99, 109], [16, 109, 16, 61]], ![[63, 30, 44, 54, 21, 31, 111, 34], [99, 105, 44, 107, 16, 64, 52, 61], [74, 101, 96, 74], [44, 70, 41, 114], [33, 30, 36, 46], [32, 121, 129, 35], [16, 57, 2, 12]], ![[23, 50, 10, 52, 29, 67, 35, 77], [34, 123, 46, 62, 88, 90, 70, 20], [42, 105, 118, 100], [122, 70, 79, 13], [106, 14, 89, 99], [128, 26, 24, 63], [21, 62, 59, 60]]]
 h' := ![![[64, 19, 31, 128, 120], [36, 109, 76, 82, 66], [99, 122, 68, 94, 52], [2, 123, 53, 36, 123], [7, 12, 7, 122, 117], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[90, 27, 117, 107, 42], [97, 70, 84, 83, 28], [87, 8, 109, 96, 66], [98, 112, 101, 108, 114], [125, 116, 87, 34, 28], [57, 43, 56, 71, 84], [35, 22, 83, 80, 94], [64, 19, 31, 128, 120]], ![[101, 25, 18, 112, 55], [37, 17, 11, 51, 125], [128, 101, 67, 15, 86], [123, 111, 97, 96, 8], [126, 79, 46, 15, 99], [46, 41, 95, 51, 123], [30, 68, 100, 122, 41], [90, 27, 117, 107, 42]], ![[94, 59, 96, 46, 45], [102, 106, 84, 36, 38], [71, 112, 108, 105, 15], [17, 86, 64, 130, 27], [108, 53, 114, 69, 30], [19, 97, 90, 123, 35], [35, 89, 46, 76, 67], [101, 25, 18, 112, 55]], ![[0, 1], [66, 91, 7, 10, 5], [124, 50, 41, 83, 43], [61, 92, 78, 23, 121], [75, 2, 8, 22, 119], [78, 81, 21, 17, 19], [29, 83, 32, 115, 60], [94, 59, 96, 46, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 18, 19, 113], [], [], []]
 b := ![[], [114, 130, 43, 72, 46], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [95, 119, 106, 52, 44, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18986733719089, -9777408489799, -8333090564112, -8877888541478, -3489885677080]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-144936898619, -74636706029, -63611378352, -67770141538, -26640348680]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 38579489651 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165, -31, -14, -4, 22]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-165, -31, -14, -4, 22]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![3, 10, 1, 0, 0], ![35, 55, 0, 1, 0], ![7, 71, 0, 0, 1]] where
  M :=![![![-165, -31, -14, -4, 22], ![500, 43, -46, 12, -8], ![-142, 243, -11, -166, 12], ![230, -95, 82, 111, -68], ![-754, -293, 24, 104, 47]]]
  hmulB := by decide  
  f := ![![![-3109, -43, -112, -704, 458]], ![![10768, 421, 606, 2568, -1408]], ![![599, 30, 39, 146, -74]], ![![3663, 163, 222, 883, -466]], ![![5311, 219, 308, 1272, -687]]]
  g := ![![![-1, -9, -14, -4, 22], ![2, 3, -46, 12, -8], ![41, 63, -11, -166, 12], ![-25, -16, 82, 111, -68], ![-35, -70, 24, 104, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [109, 121, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 136], [0, 1]]
 g := ![![[118, 44], [60], [34], [77, 120], [38], [119], [1]], ![[0, 93], [60], [34], [79, 17], [38], [119], [1]]]
 h' := ![![[16, 136], [21, 110], [56, 34], [101, 87], [4, 95], [6, 60], [28, 16], [0, 1]], ![[0, 1], [0, 27], [52, 103], [123, 50], [17, 42], [7, 77], [10, 121], [16, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [6, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [109, 121, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37815, 8058, -3178, -23202, 8574]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5283, 5162, -3178, -23202, 8574]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, -45, 28, 26, -10]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-101, -45, 28, 26, -10]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![108, 90, 1, 0, 0], ![58, 5, 0, 1, 0], ![66, 64, 0, 0, 1]] where
  M :=![![![-101, -45, 28, 26, -10], ![-184, -193, -54, 76, 52], ![570, 207, -195, -134, 76], ![52, 133, 76, -51, -58], ![-476, -69, 254, 74, -135]]]
  hmulB := by decide  
  f := ![![![-19737, 539, -1206, -2866, 2222]], ![![50916, -1399, 3110, 7384, -5732]], ![![17410, -481, 1063, 2522, -1960]], ![![-6022, 164, -368, -875, 678]], ![![13954, -385, 852, 2022, -1571]]]
  g := ![![![-29, -15, 28, 26, -10], ![-16, 7, -54, 76, 52], ![178, 99, -195, -134, 76], ![-10, -20, 76, -51, -58], ![-170, -107, 254, 74, -135]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [74, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 136], [0, 1]]
 g := ![![[3, 50], [2], [59], [90, 4], [73], [101], [1]], ![[0, 87], [2], [59], [24, 133], [73], [101], [1]]]
 h' := ![![[52, 136], [23, 18], [87, 31], [53, 14], [39, 2], [57, 22], [63, 52], [0, 1]], ![[0, 1], [0, 119], [55, 106], [96, 123], [6, 135], [105, 115], [27, 85], [52, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104]]
 b := ![[], [18, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [74, 85, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![159967, 80163, 87696, 100708, 40167]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129951, -79465, 87696, 100708, 40167]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -11, 2, 8, -1]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![-6, -11, 2, 8, -1]] 
 ![![137, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![33, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-6, -11, 2, 8, -1], ![-20, -9, -20, -8, 16], ![172, 68, -13, -20, -8], ![-95, -5, 16, -9, -1], ![-81, -65, 36, 50, -18]]]
  hmulB := by decide  
  f := ![![![1492, 325, 344, 434, 29]], ![![816, 189, 196, 244, 22]], ![![108, 38, 35, 40, 10]], ![![377, 98, 98, 119, 16]], ![![223, 81, 74, 84, 22]]]
  g := ![![![4, -11, 2, 8, -1], ![6, -9, -20, -8, 16], ![-30, 68, -13, -20, -8], ![4, -5, 16, -9, -1], ![23, -65, 36, 50, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-165, -31, -14, -4, 22]] ![![-101, -45, 28, 26, -10]]
  ![![3709, 8460, 5068, -2938, -3764]] where
 M := ![![![3709, 8460, 5068, -2938, -3764]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![3709, 8460, 5068, -2938, -3764]] ![![-6, -11, 2, 8, -1]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![1264236, 487035, -410178, -301126, 161797]]]
 hmul := by decide  
 g := ![![![![9228, 3555, -2994, -2198, 1181]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)
instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0, 0, 0]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]] where
  M :=![![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![0, 0, 0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [54, 119, 5, 57, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 123, 2, 25, 127], [103, 111, 118, 19, 34], [12, 42, 7, 21, 90], [83, 1, 12, 74, 27], [0, 1]]
 g := ![![[130, 97, 132, 20, 16], [88, 63, 18, 91, 100], [84, 127, 36, 24], [83, 41, 59, 87, 66], [57, 64, 128, 1], [], []], ![[83, 106, 36, 132, 70, 103, 136, 66], [103, 76, 50, 113, 72, 137, 113, 120], [138, 81, 109, 11], [32, 38, 83, 20, 20, 14, 87, 83], [136, 52, 111, 127], [75, 92, 25, 106], [85, 130, 40, 5]], ![[127, 136, 122, 103, 81, 115, 78, 25], [93, 95, 123, 32, 27, 76, 10, 51], [130, 37, 65, 45], [136, 90, 14, 46, 15, 26, 102, 16], [92, 75, 108, 45], [57, 133, 40, 51], [128, 47, 113, 44]], ![[80, 24, 138, 46, 96, 74, 52, 75], [82, 110, 12, 13, 6, 127, 23, 60], [58, 48, 65, 78], [137, 98, 80, 64, 55, 110, 99, 75], [137, 56, 85, 36], [113, 0, 82, 86], [126, 83, 26, 38]], ![[124, 96, 126, 61, 127, 83, 77, 123], [49, 109, 9, 27, 40, 123, 41, 40], [104, 74, 70, 99], [111, 122, 49, 20, 113, 97, 75, 32], [36, 96, 8, 41], [120, 87, 88, 41], [50, 67, 8, 34]]]
 h' := ![![[69, 123, 2, 25, 127], [113, 16, 43, 45, 135], [95, 12, 12, 3, 129], [105, 124, 65, 112, 118], [119, 47, 60, 49, 109], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[103, 111, 118, 19, 34], [2, 35, 102, 69, 8], [100, 132, 84, 32, 95], [121, 21, 46, 64, 17], [74, 42, 129, 120, 107], [32, 128, 23, 25, 108], [32, 117, 130, 89, 84], [69, 123, 2, 25, 127]], ![[12, 42, 7, 21, 90], [131, 40, 11, 48, 41], [100, 1, 54, 38, 99], [46, 137, 77, 85, 36], [64, 116, 68, 122, 134], [58, 56, 58, 9, 103], [83, 92, 108, 84, 107], [103, 111, 118, 19, 34]], ![[83, 1, 12, 74, 27], [93, 60, 64, 84, 118], [131, 55, 116, 83, 66], [30, 41, 56, 7, 56], [52, 64, 76, 108, 118], [19, 75, 95, 41, 133], [12, 19, 29, 25, 15], [12, 42, 7, 21, 90]], ![[0, 1], [94, 127, 58, 32, 115], [129, 78, 12, 122, 28], [18, 94, 34, 10, 51], [11, 9, 84, 18, 88], [136, 19, 102, 64, 72], [19, 50, 10, 80, 72], [83, 1, 12, 74, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 14, 81, 4], [], [], []]
 b := ![[], [31, 106, 70, 42, 93], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [54, 119, 5, 57, 11, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8931155880, -4560380666, -3891308336, -4151685221, -1603302728]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-64252920, -32808494, -27995024, -29868239, -11534552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 51888844699 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2548, -272, 222, 34, -177]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![2548, -272, 222, 34, -177]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![58, 31, 24, 52, 1]] where
  M :=![![![2548, -272, 222, 34, -177], ![-3804, 767, -454, 556, 68], ![362, -1091, 381, -1782, 556], ![747, 1116, -328, 2021, -709], ![-6187, -910, -22, -2680, 1278]]]
  hmulB := by decide  
  f := ![![![-10, -4, -6, -8, -3]], ![![-84, -39, -26, -32, -16]], ![![-218, -117, -81, -78, -32]], ![![-93, -50, -52, -53, -17]], ![![-91, -47, -40, -42, -16]]]
  g := ![![![86, 35, 30, 62, -177], ![-52, -9, -14, -20, 68], ![-214, -123, -87, -206, 556], ![281, 155, 112, 261, -709], ![-539, -272, -206, -464, 1278]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [90, 41, 7, 101, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 73, 128, 50], [101, 16, 145, 94], [108, 59, 25, 5], [0, 1]]
 g := ![![[20, 69, 53, 53], [144], [6, 100, 65, 148], [97, 49, 110], [92, 21, 107, 69], [1], []], ![[17, 66, 4, 93, 47, 126], [78, 43, 33], [31, 140, 63, 87, 108, 79], [21, 69, 45], [57, 115, 43, 105, 119, 8], [17, 35, 17], [106, 41, 116]], ![[122, 26, 76, 143, 16, 146], [25, 6, 85], [18, 110, 89, 146, 28, 23], [24, 111, 142], [143, 22, 76, 147, 87, 40], [5, 74, 113], [114, 67, 45]], ![[53, 120, 96, 69, 86, 143], [5, 147, 24], [35, 69, 31, 61, 74, 114], [9, 24, 76], [142, 110, 12, 142, 57, 143], [88, 114, 35], [14, 109, 25]]]
 h' := ![![[137, 73, 128, 50], [10, 73, 37, 65], [56, 68, 137], [134, 15, 47, 44], [64, 54, 119, 40], [59, 108, 142, 48], [0, 0, 1], [0, 1]], ![[101, 16, 145, 94], [139, 24, 0, 123], [93, 91, 88, 114], [86, 123, 91, 104], [28, 38, 88, 55], [41, 93, 114, 60], [140, 46, 122, 100], [137, 73, 128, 50]], ![[108, 59, 25, 5], [31, 55, 3, 38], [33, 11, 46, 95], [51, 136, 84, 81], [107, 148, 0, 69], [51, 52, 57, 118], [90, 127, 48, 115], [101, 16, 145, 94]], ![[0, 1], [101, 146, 109, 72], [113, 128, 27, 89], [2, 24, 76, 69], [31, 58, 91, 134], [57, 45, 134, 72], [123, 125, 127, 83], [108, 59, 25, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [93, 89, 101], []]
 b := ![[], [], [134, 74, 55, 140], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [90, 41, 7, 101, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125783637192, 64972905524, 55783359688, 59329880496, 23276006568]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8216273448, -4406599316, -3374770456, -7724982960, 23276006568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, -4, -6, -8, -3]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-10, -4, -6, -8, -3]] 
 ![![149, 0, 0, 0, 0], ![45, 1, 0, 0, 0], ![105, 0, 1, 0, 0], ![129, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![-10, -4, -6, -8, -3], ![-84, -39, -26, -32, -16], ![-218, -117, -81, -78, -32], ![-93, -50, -52, -53, -17], ![-307, -154, -158, -174, -62]]]
  hmulB := by decide  
  f := ![![![2548, -272, 222, 34, -177]], ![![744, -77, 64, 14, -53]], ![![1798, -199, 159, 12, -121]], ![![2211, -228, 190, 43, -158]], ![![557, -70, 52, -10, -33]]]
  g := ![![![13, -4, -6, -8, -3], ![61, -39, -26, -32, -16], ![166, -117, -81, -78, -32], ![101, -50, -52, -53, -17], ![321, -154, -158, -174, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![2548, -272, 222, 34, -177]] ![![-10, -4, -6, -8, -3]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1354, -71, 58, 178, -171]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![1354, -71, 58, 178, -171]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![38, 147, 133, 127, 1]] where
  M :=![![![1354, -71, 58, 178, -171], ![-3988, -65, -368, -692, 356], ![3904, -554, -77, 300, -692], ![-5211, -127, -496, -913, 447], ![1651, -897, -488, -248, -644]]]
  hmulB := by decide  
  f := ![![![28, 3, 0, 4, -3]], ![![-72, 5, 0, -20, 8]], ![![96, -10, 13, 36, -20]], ![![-129, -7, -10, -29, 21]], ![![-86, -9, 3, -11, 7]]]
  g := ![![![52, 166, 151, 145, -171], ![-116, -347, -316, -304, 356], ![200, 670, 609, 584, -692], ![-147, -436, -397, -382, 447], ![173, 621, 564, 540, -644]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [109, 102, 75, 57, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 26, 103, 110], [19, 121, 119, 150], [54, 3, 80, 42], [0, 1]]
 g := ![![[76, 92, 46, 91], [75, 134, 7, 17], [126, 118, 123, 37], [133, 2, 21], [3, 49, 27, 78], [1], []], ![[129, 144, 144, 40, 140, 59], [82, 113, 34, 99, 45, 84], [37, 67, 97, 43, 56, 88], [102, 112, 11], [120, 53, 28, 54, 126, 10], [139, 127, 97], [115, 78, 20]], ![[27, 121, 86, 121, 5, 131], [101, 41, 64, 145, 112, 23], [35, 35, 0, 53, 47, 133], [73, 6, 76], [108, 30, 117, 71, 81, 3], [94, 27, 49], [6, 7, 1]], ![[9, 56, 146, 12, 21, 19], [127, 54, 131, 98, 68, 47], [92, 118, 63, 38, 46, 36], [47, 49, 10], [132, 94, 134, 149, 21, 21], [73, 8, 94], [62, 94, 103]]]
 h' := ![![[21, 26, 103, 110], [130, 141, 28, 53], [7, 54, 150, 116], [20, 72, 111, 108], [126, 43, 27, 25], [42, 49, 76, 94], [0, 0, 1], [0, 1]], ![[19, 121, 119, 150], [107, 111, 55, 131], [143, 148, 32, 3], [98, 111, 86, 129], [58, 54, 97, 112], [145, 86, 84, 120], [137, 37, 133, 61], [21, 26, 103, 110]], ![[54, 3, 80, 42], [119, 18, 111, 41], [38, 37, 91, 85], [110, 116, 60, 138], [143, 15, 37, 128], [103, 32, 29, 65], [9, 52, 72, 7], [19, 121, 119, 150]], ![[0, 1], [12, 32, 108, 77], [122, 63, 29, 98], [148, 3, 45, 78], [99, 39, 141, 37], [5, 135, 113, 23], [84, 62, 96, 83], [54, 3, 80, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [54, 96, 135], []]
 b := ![[], [], [32, 54, 149, 135], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [109, 102, 75, 57, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7771860989, 4091551694, 3500270714, 3723483633, 1535029200]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-334829461, -1467269806, -1328864986, -1266392217, 1535029200]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, 3, 0, 4, -3]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![28, 3, 0, 4, -3]] 
 ![![151, 0, 0, 0, 0], ![48, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![45, 0, 0, 1, 0], ![149, 0, 0, 0, 1]] where
  M :=![![![28, 3, 0, 4, -3], ![-72, 5, 0, -20, 8], ![96, -10, 13, 36, -20], ![-129, -7, -10, -29, 21], ![149, 11, -6, 22, -12]]]
  hmulB := by decide  
  f := ![![![1354, -71, 58, 178, -171]], ![![404, -23, 16, 52, -52]], ![![528, -30, 21, 68, -68]], ![![369, -22, 14, 47, -48]], ![![1347, -76, 54, 174, -173]]]
  g := ![![![1, 3, 0, 4, -3], ![-4, 5, 0, -20, 8], ![8, -10, 13, 36, -20], ![-7, -7, -10, -29, 21], ![5, 11, -6, 22, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![1354, -71, 58, 178, -171]] ![![28, 3, 0, 4, -3]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)


lemma PB519I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB519I3 : PrimesBelowBoundCertificateInterval O 103 151 519 where
  m := 9
  g := ![3, 2, 3, 2, 1, 3, 1, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB519I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
    · exact PBC139
    · exact PBC149
    · exact PBC151
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![1225043, 107, 107]
    · exact ![141158161, 109]
    · exact ![1442897, 113, 113]
    · exact ![260144641, 127]
    · exact ![38579489651]
    · exact ![18769, 18769, 137]
    · exact ![51888844699]
    · exact ![492884401, 149]
    · exact ![519885601, 151]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I107N2, I109N1, I113N1, I113N2, I127N1, I137N2, I149N1, I151N1]
  Il := ![[I107N1, I107N2], [I109N1], [I113N1, I113N2], [I127N1], [], [I137N2], [], [I149N1], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
