
import IdealArithmetic.Examples.NF5_1_48600000_3.RI5_1_48600000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4395, 4641, -3760, 772, -1433]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![4395, 4641, -3760, 772, -1433]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![62, 82, 40, 1, 0], ![100, 100, 35, 0, 1]] where
  M :=![![![4395, 4641, -3760, 772, -1433], ![-2866, -2770, 2314, -466, 883], ![1766, 1549, -1339, 262, -515], ![-1398, -1179, 1032, -187, 393], ![-670, -597, 508, -98, 206]]]
  hmulB := by decide  
  f := ![![![1729, 5319, 5190, 368, 1501]], ![![3002, 9234, 9008, 638, 2605]], ![![5210, 16027, 15637, 1110, 4519]], ![![5268, 16205, 15810, 1121, 4571]], ![![6148, 18912, 18451, 1308, 5335]]]
  g := ![![![933, 791, 145, 772, -1433], ![-582, -494, -93, -466, 883], ![346, 295, 58, 262, -515], ![-272, -235, -49, -187, 393], ![-142, -123, -26, -98, 206]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [85, 47, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 57, 56], [46, 49, 51], [0, 1]]
 g := ![![[41, 6, 69], [22, 11, 44], [13, 37], [61, 41, 37], [68, 11], [1]], ![[63, 75, 86, 83], [78, 15, 71, 64], [45, 101], [70, 33, 28, 27], [37, 39], [26, 103, 72, 29]], ![[98, 61, 30, 7], [94, 4, 16, 73], [37, 48], [5, 35, 15, 91], [61, 52], [58, 51, 43, 78]]]
 h' := ![![[46, 57, 56], [56, 101, 47], [12, 95, 30], [58, 95, 12], [54, 7, 12], [22, 60, 92], [0, 1]], ![[46, 49, 51], [6, 60, 41], [96, 78, 49], [60, 6, 23], [74, 19, 17], [3, 43, 57], [46, 57, 56]], ![[0, 1], [40, 53, 19], [79, 41, 28], [96, 6, 72], [3, 81, 78], [65, 4, 65], [46, 49, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 53], []]
 b := ![[], [56, 98, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [85, 47, 15, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1719165, -2694674, 3952521, 11448947, -13205447]
  a := ![0, -1, -4, 5, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5691503, 3542396, 76498, 11448947, -13205447]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1729, 5319, 5190, 368, 1501]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1729, 5319, 5190, 368, 1501]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![100, 28, 1, 0, 0], ![48, 72, 0, 1, 0], ![93, 34, 0, 0, 1]] where
  M :=![![![1729, 5319, 5190, 368, 1501], ![3002, 9234, 9008, 638, 2605], ![5210, 16027, 15637, 1110, 4519], ![1914, 5889, 5754, 415, 1665], ![2386, 7339, 7162, 506, 2080]]]
  hmulB := by decide  
  f := ![![![4395, 4641, -3760, 772, -1433]], ![![-2866, -2770, 2314, -466, 883]], ![![3374, 3627, -2921, 602, -1113]], ![![30, 207, -120, 31, -45]], ![![2903, 3148, -2528, 522, -963]]]
  g := ![![![-6304, -2033, 5190, 368, 1501], ![-10941, -3528, 9008, 638, 2605], ![-18991, -6125, 15637, 1110, 4519], ![-6993, -2259, 5754, 415, 1665], ![-8706, -2807, 7162, 506, 2080]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P1 : CertificateIrreducibleZModOfList' 107 2 2 6 [96, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 106], [0, 1]]
 g := ![![[15, 41], [14, 101], [33], [43, 11], [47], [58, 1]], ![[39, 66], [94, 6], [33], [39, 96], [47], [9, 106]]]
 h' := ![![[58, 106], [47, 83], [34, 84], [45, 51], [105, 15], [103, 58], [0, 1]], ![[0, 1], [46, 24], [91, 23], [7, 56], [12, 92], [43, 49], [58, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [90, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N1 : CertifiedPrimeIdeal' SI107N1 107 where
  n := 2
  hpos := by decide
  P := [96, 49, 1]
  hirr := P107P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1238, -7484, 4312, 2356, 2632]
  a := ![3, -64, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7386, -3620, 4312, 2356, 2632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N1 B_one_repr
lemma NI107N1 : Nat.card (O ⧸ I107N1) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![4395, 4641, -3760, 772, -1433]] ![![1729, 5319, 5190, 368, 1501]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2161, -6647, -6484, -460, -1875]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-2161, -6647, -6484, -460, -1875]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![44, 97, 1, 0, 0], ![24, 65, 0, 1, 0], ![80, 57, 0, 0, 1]] where
  M :=![![![-2161, -6647, -6484, -460, -1875], ![-3750, -11536, -11256, -798, -3255], ![-6510, -20025, -19537, -1386, -5649], ![-2394, -7365, -7188, -511, -2079], ![-2982, -9173, -8950, -634, -2590]]]
  hmulB := by decide  
  f := ![![![875, 653, -602, 112, -231]], ![![-462, -280, 282, -42, 105]], ![![-56, 15, 7, 8, 0]], ![![-84, -23, 36, -1, 12]], ![![400, 333, -294, 60, -115]]]
  g := ![![![4075, 6964, -6484, -460, -1875], ![7074, 12089, -11256, -798, -3255], ![12278, 20983, -19537, -1386, -5649], ![4518, 7721, -7188, -511, -2079], ![5626, 9613, -8950, -634, -2590]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [15, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 108], [0, 1]]
 g := ![![[57, 80], [88], [80, 20], [69, 81], [84], [17, 1]], ![[0, 29], [88], [93, 89], [29, 28], [84], [34, 108]]]
 h' := ![![[17, 108], [98, 84], [108, 52], [55, 67], [0, 9], [72, 56], [0, 1]], ![[0, 1], [0, 25], [11, 57], [104, 42], [44, 100], [43, 53], [17, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [61, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [15, 92, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![216, -414, -886, -1784, 2682]
  a := ![1, -3, -2, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1216, 446, -886, -1784, 2682]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![530577, 1632120, 1592401, 112936, 460483]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![530577, 1632120, 1592401, 112936, 460483]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![5, 18, 1, 0, 0], ![7, 104, 0, 1, 0], ![13, 29, 0, 0, 1]] where
  M :=![![![530577, 1632120, 1592401, 112936, 460483], ![920966, 2832992, 2764038, 196032, 799291], ![1598582, 4917421, 4797739, 340266, 1387387], ![588096, 1809048, 1765017, 125179, 510399], ![732330, 2252729, 2197900, 155880, 635578]]]
  hmulB := by decide  
  f := ![![![377, 468, -337, 46, -163]], ![![-326, -438, 294, 212, -25]], ![![-37, -55, 32, 40, -6]], ![![-281, -372, 254, 183, -30]], ![![-35, -41, 37, 50, -44]]]
  g := ![![![-130351, -478261, 1592401, 112936, 460483], ![-226259, -830151, 2764038, 196032, 799291], ![-392734, -1440952, 4797739, 340266, 1387387], ![-144481, -530105, 1765017, 125179, 510399], ![-179916, -660117, 2197900, 155880, 635578]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [64, 37, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 108], [0, 1]]
 g := ![![[67, 46], [100], [10, 73], [27, 83], [9], [72, 1]], ![[0, 63], [100], [34, 36], [8, 26], [9], [35, 108]]]
 h' := ![![[72, 108], [9, 68], [14, 10], [16, 20], [106, 65], [79, 106], [0, 1]], ![[0, 1], [0, 41], [80, 99], [39, 89], [99, 44], [81, 3], [72, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [60, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [64, 37, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3128, 6515, -4209, -15708, 15776]
  a := ![1, 19, 3, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-651, 11545, -4209, -15708, 15776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-439, -845, 595, -162, 212]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-439, -845, 595, -162, 212]] 
 ![![109, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![87, 0, 0, 0, 1]] where
  M :=![![![-439, -845, 595, -162, 212], ![424, 621, -462, 242, -274], ![-548, -946, 433, 236, 452], ![726, 1329, -699, -1277, 354], ![720, 1718, -374, -1174, -923]]]
  hmulB := by decide  
  f := ![![![19277086497, 59298495863, 57855249143, 4103221484, 16730300638]], ![![18522940463, 56978657464, 55591872533, 3942697838, 16075788356]], ![![13443185729, 41352758025, 40346286756, 2861447372, 11667143726]], ![![3556251357, 10939430936, 10673179700, 756965373, 3086418394]], ![![15630400215, 48080876881, 46910652125, 3327006598, 13565395099]]]
  g := ![![![255, -845, 595, -162, 212], ![-97, 621, -462, 242, -274], ![197, -946, 433, 236, 452], ![-841, 1329, -699, -1277, 354], ![-425, 1718, -374, -1174, -923]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-2161, -6647, -6484, -460, -1875]] ![![530577, 1632120, 1592401, 112936, 460483]]
  ![![-19277086497, -59298495863, -57855249143, -4103221484, -16730300638]] where
 M := ![![![-19277086497, -59298495863, -57855249143, -4103221484, -16730300638]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-19277086497, -59298495863, -57855249143, -4103221484, -16730300638]] ![![-439, -845, 595, -162, 212]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![-109, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39333, 120990, 118046, 8372, 34136]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![39333, 120990, 118046, 8372, 34136]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![64, 27, 43, 1, 0], ![16, 94, 100, 0, 1]] where
  M :=![![![39333, 120990, 118046, 8372, 34136], ![68272, 210013, 204900, 14532, 59252], ![118504, 364532, 355661, 25224, 102848], ![43596, 134106, 130842, 9281, 37836], ![54288, 166996, 162932, 11556, 47117]]]
  hmulB := by decide  
  f := ![![![125, 18, -46, 4, -16]], ![![-32, 45, -12, -4, -4]], ![![-8, -52, 37, 8, -16]], ![![60, 1, -15, 5, -16]], ![![-16, -6, 16, 4, -19]]]
  g := ![![![-9227, -29326, -32350, 8372, 34136], ![-16016, -50903, -56152, 14532, 59252], ![-27800, -88356, -97467, 25224, 102848], ![-10228, -32505, -35857, 9281, 37836], ![-12736, -40478, -44652, 11556, 47117]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [3, 3, 80, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 36, 43], [8, 76, 70], [0, 1]]
 g := ![![[67, 13, 50], [46, 22], [69, 41], [73, 8], [53, 31, 72], [1]], ![[110, 64, 47, 35], [107, 85], [1, 51], [86, 112], [86, 92, 110, 79], [9, 42, 5, 68]], ![[65, 49, 2, 66], [17, 88], [101, 41], [32, 16], [7, 37, 80, 24], [46, 33, 98, 45]]]
 h' := ![![[25, 36, 43], [84, 1, 29], [30, 107, 19], [89, 78, 70], [67, 96, 102], [110, 110, 33], [0, 1]], ![[8, 76, 70], [3, 41, 100], [95, 99, 56], [18, 73, 86], [29, 68, 15], [4, 112, 6], [25, 36, 43]], ![[0, 1], [78, 71, 97], [4, 20, 38], [9, 75, 70], [61, 62, 109], [35, 4, 74], [8, 76, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 7], []]
 b := ![[], [45, 67, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [3, 3, 80, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4823265, -10515972, 5909367, 19594906, -11891517]
  a := ![-1, 0, -2, 9, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9456929, 5117028, 3119293, 19594906, -11891517]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 18, -7, -60, 43]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-3, 18, -7, -60, 43]] 
 ![![113, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![-3, 18, -7, -60, 43], ![86, 212, -32, -152, -137], ![-274, -599, 317, 1062, -593], ![-456, -1320, -3, 503, 1593], ![758, 1623, -974, -3188, 2096]]]
  hmulB := by decide  
  f := ![![![20075689, 61755078, 60251991, 4273210, 17423377]], ![![2084988, 6413658, 6257554, 443800, 1809529]], ![![2844867, 8751131, 8538134, 605544, 2469016]], ![![17607694, 54163248, 52844943, 3747885, 15281443]], ![![7351654, 22614515, 22064090, 1564836, 6380386]]]
  g := ![![![36, 18, -7, -60, 43], ![166, 212, -32, -152, -137], ![-697, -599, 317, 1062, -593], ![-887, -1320, -3, 503, 1593], ![1998, 1623, -974, -3188, 2096]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -116, -77, -10, -21]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-37, -116, -77, -10, -21]] 
 ![![113, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![82, 0, 0, 0, 1]] where
  M :=![![![-37, -116, -77, -10, -21], ![-42, -142, -172, -8, -51], ![-102, -297, -263, -22, -75], ![-24, -90, -111, -5, -33], ![-38, -123, -130, -8, -38]]]
  hmulB := by decide  
  f := ![![![7, -8, 9, 60, -63]], ![![0, -4, 2, 12, -9]], ![![3, 3, -2, -2, 0]], ![![9, 18, 0, 1, -30]], ![![0, -15, 16, 72, -74]]]
  g := ![![![46, -116, -77, -10, -21], ![84, -142, -172, -8, -51], ![141, -297, -263, -22, -75], ![54, -90, -111, -5, -33], ![66, -123, -130, -8, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![39333, 120990, 118046, 8372, 34136]] ![![-3, 18, -7, -60, 43]]
  ![![-7, 8, -9, -60, 63]] where
 M := ![![![-7, 8, -9, -60, 63]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-7, 8, -9, -60, 63]] ![![-37, -116, -77, -10, -21]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![865, 1780, -1215, 284, -461]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![865, 1780, -1215, 284, -461]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![0, 0, 127, 0, 0], ![6, 23, 21, 1, 0], ![47, 34, 31, 0, 1]] where
  M :=![![![865, 1780, -1215, 284, -461], ![-922, -1440, 1026, -232, 391], ![782, 1033, -805, 170, -305], ![-696, -888, 669, -145, 255], ![-294, -399, 288, -64, 110]]]
  hmulB := by decide  
  f := ![![![3, 8, -3, -10, -1]], ![![-2, -2, 6, 20, -31]], ![![-62, -157, 35, 158, 29]], ![![-10, -25, 6, 27, 1]], ![![-13, -32, 8, 36, -2]]]
  g := ![![![164, 86, 56, 284, -461], ![-141, -74, -49, -232, 391], ![111, 59, 40, 170, -305], ![-93, -49, -33, -145, 255], ![-40, -21, -14, -64, 110]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [125, 57, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 43, 84], [44, 83, 43], [0, 1]]
 g := ![![[87, 52, 11], [79, 59, 37], [12, 13, 31], [23, 98, 73], [97, 120, 26], [1]], ![[61, 51, 43, 52], [54, 55, 94, 94], [16, 87, 54, 115], [121, 15, 51, 121], [28, 126, 93, 32], [52, 86, 68, 122]], ![[33, 123, 9, 14], [85, 18, 39, 91], [69, 15, 3, 97], [2, 56, 10, 92], [76, 65, 11, 65], [68, 88, 100, 5]]]
 h' := ![![[47, 43, 84], [31, 1, 97], [24, 61, 52], [46, 72, 44], [67, 49, 33], [2, 70, 91], [0, 1]], ![[44, 83, 43], [57, 75, 7], [108, 36, 42], [108, 18, 48], [69, 116, 124], [41, 102, 98], [47, 43, 84]], ![[0, 1], [69, 51, 23], [26, 30, 33], [124, 37, 35], [96, 89, 97], [103, 82, 65], [44, 83, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 85], []]
 b := ![[], [16, 73, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [125, 57, 36, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1576141, 3958464, -1012526, -4191406, -548130]
  a := ![0, 0, -6, -6, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![413281, 936986, 818890, -4191406, -548130]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-496782247, -1528158315, -1490964969, -105742514, -431150026]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-496782247, -1528158315, -1490964969, -105742514, -431150026]] 
 ![![127, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![110, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![55, 0, 0, 0, 1]] where
  M :=![![![-496782247, -1528158315, -1490964969, -105742514, -431150026], ![-862300052, -2652532377, -2587973258, -183544754, -748377568], ![-1496755136, -4604187892, -4492128067, -318591600, -1299011830], ![-550634262, -1693813197, -1652588031, -117205177, -477887400], ![-685681108, -2109232552, -2057896630, -145950554, -595092577]]]
  hmulB := by decide  
  f := ![![![-151701, -97593, 96065, -17132, 36700]], ![![-13756, -8971, 8776, -1570, 3352]], ![![-131626, -84530, 83271, -14844, 31818]], ![![-55995, -36156, 35536, -6359, 13574]], ![![-65605, -42255, 41577, -7414, 15867]]]
  g := ![![![1657719793, -1528158315, -1490964969, -105742514, -431150026], ![2877421390, -2652532377, -2587973258, -183544754, -748377568], ![4994543644, -4604187892, -4492128067, -318591600, -1299011830], ![1837419353, -1693813197, -1652588031, -117205177, -477887400], ![2288059107, -2109232552, -2057896630, -145950554, -595092577]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-179, -79, 152, -184, 45]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-179, -79, 152, -184, 45]] 
 ![![127, 0, 0, 0, 0], ![74, 1, 0, 0, 0], ![112, 0, 1, 0, 0], ![118, 0, 0, 1, 0], ![89, 0, 0, 0, 1]] where
  M :=![![![-179, -79, 152, -184, 45], ![90, 46, 28, 402, -507], ![-1014, -2445, 581, 2294, 699], ![1206, 2463, -1572, -4957, 3441], ![3098, 7779, -1898, -7930, -1516]]]
  hmulB := by decide  
  f := ![![![-13665614405, -42036973769, -41013849606, -2908792396, -11860186317]], ![![-8149416052, -25068524448, -24458389826, -1734642786, -7072758669]], ![![-12375763310, -38069246081, -37142691145, -2634241326, -10740743469]], ![![-12816452672, -39424856345, -38465307654, -2728044197, -11123211303]], ![![-9725209253, -29915842358, -29187730450, -2070058022, -8440366477]]]
  g := ![![![50, -79, 152, -184, 45], ![-69, 46, 28, 402, -507], ![-1717, -2445, 581, 2294, 699], ![2155, 2463, -1572, -4957, 3441], ![5596, 7779, -1898, -7930, -1516]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![865, 1780, -1215, 284, -461]] ![![-496782247, -1528158315, -1490964969, -105742514, -431150026]]
  ![![13665614405, 42036973769, 41013849606, 2908792396, 11860186317]] where
 M := ![![![13665614405, 42036973769, 41013849606, 2908792396, 11860186317]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![13665614405, 42036973769, 41013849606, 2908792396, 11860186317]] ![![-179, -79, 152, -184, 45]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![-127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
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


def P131P0 : CertificateIrreducibleZModOfList' 131 5 2 7 [116, 104, 46, 10, 94, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 120, 2, 21, 39], [87, 101, 122, 49, 92], [52, 89, 78, 32, 73], [100, 82, 60, 29, 58], [0, 1]]
 g := ![![[4, 112, 99, 96, 91], [118, 77, 130, 70, 65], [46, 124, 57, 62], [2, 124, 116, 36], [87, 49, 37, 1], [], []], ![[55, 71, 116, 89, 74, 115, 111, 11], [33, 71, 10, 107, 100, 72, 46, 123], [106, 105, 36, 129], [80, 124, 17, 12], [93, 48, 87, 49], [76, 48, 57, 12], [69, 16, 13, 80]], ![[45, 111, 115, 117, 120, 89, 86, 31], [52, 20, 36, 63, 50, 21, 50, 87], [38, 128, 46, 41], [26, 111, 13, 102], [0, 33, 41, 20], [125, 90, 66, 114], [10, 15, 55, 80]], ![[59, 22, 39, 78, 67, 43, 120, 8], [97, 51, 51, 104, 111, 53, 112, 130], [76, 83, 50, 74], [83, 130, 52, 125], [20, 94, 9, 107], [90, 35, 82, 58], [82, 80, 105, 89]], ![[86, 94, 108, 42, 100, 100, 7, 11], [84, 124, 54, 53, 32, 103, 29, 112], [125, 97, 6, 53], [13, 126, 96, 91], [48, 75, 100, 7], [4, 90, 52, 49], [119, 128, 107, 89]]]
 h' := ![![[60, 120, 2, 21, 39], [67, 0, 61, 12, 22], [47, 88, 109, 60, 117], [55, 25, 99, 7, 18], [126, 71, 103, 117, 6], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[87, 101, 122, 49, 92], [17, 1, 25, 105, 111], [59, 30, 85, 17, 101], [98, 37, 90, 115, 103], [83, 122, 111, 67, 76], [103, 114, 13, 11, 124], [50, 128, 41, 112, 55], [60, 120, 2, 21, 39]], ![[52, 89, 78, 32, 73], [64, 93, 114, 81, 127], [24, 126, 50, 111, 40], [41, 103, 96, 60, 98], [100, 83, 34, 74, 87], [10, 58, 125, 103, 85], [121, 122, 104, 88, 30], [87, 101, 122, 49, 92]], ![[100, 82, 60, 29, 58], [60, 46, 116, 26, 6], [4, 129, 2, 127, 89], [49, 96, 121, 108, 104], [30, 30, 25, 16, 115], [56, 39, 40, 57, 32], [4, 94, 14, 114, 53], [52, 89, 78, 32, 73]], ![[0, 1], [57, 122, 77, 38, 127], [23, 20, 16, 78, 46], [84, 1, 118, 103, 70], [85, 87, 120, 119, 109], [85, 51, 84, 91, 20], [126, 49, 102, 79, 124], [100, 82, 60, 29, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 89, 103, 102], [], [], []]
 b := ![[], [77, 95, 100, 79, 78], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 5
  hpos := by decide
  P := [116, 104, 46, 10, 94, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2728926070975, -6557687138164, 2272331597761, 8511537591269, -1571418137693]
  a := ![13, -1, -2, 7, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20831496725, -50058680444, 17346042731, 64973569399, -11995558303]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12009, -36936, -36034, -2556, -10420]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-12009, -36936, -36034, -2556, -10420]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![129, 103, 1, 0, 0], ![5, 120, 0, 1, 0], ![95, 26, 0, 0, 1]] where
  M :=![![![-12009, -36936, -36034, -2556, -10420], ![-20840, -64109, -62550, -4436, -18088], ![-36176, -111280, -108571, -7700, -31396], ![-13308, -40938, -39942, -2833, -11550], ![-16572, -50978, -49738, -3528, -14383]]]
  hmulB := by decide  
  f := ![![![191, 360, -250, 68, -100]], ![![-200, -309, 210, -36, 104]], ![![31, 109, -79, 36, -16]], ![![-169, -258, 176, -29, 86]], ![![93, 188, -132, 44, -51]]]
  g := ![![![41161, 31038, -36034, -2556, -10420], ![71450, 53877, -62550, -4436, -18088], ![124019, 93517, -108571, -7700, -31396], ![45625, 34404, -39942, -2833, -11550], ![56815, 42842, -49738, -3528, -14383]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [88, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 136], [0, 1]]
 g := ![![[102, 123], [120], [115], [57, 77], [74], [109], [1]], ![[0, 14], [120], [115], [70, 60], [74], [109], [1]]]
 h' := ![![[66, 136], [23, 64], [87, 95], [53, 65], [32, 112], [70, 99], [49, 66], [0, 1]], ![[0, 1], [0, 73], [55, 42], [96, 72], [26, 25], [28, 38], [21, 71], [66, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [64, 106]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [88, 71, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![236, 99, -493, -1834, 2486]
  a := ![-1, -3, 1, -3, 7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1191, 1506, -493, -1834, 2486]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1213, 3731, 3640, 258, 1053]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![1213, 3731, 3640, 258, 1053]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![64, 80, 1, 0, 0], ![11, 80, 0, 1, 0], ![36, 70, 0, 0, 1]] where
  M :=![![![1213, 3731, 3640, 258, 1053], ![2106, 6478, 6318, 446, 1827], ![3654, 11241, 10969, 782, 3165], ![1338, 4119, 4038, 301, 1173], ![1674, 5147, 5020, 346, 1474]]]
  hmulB := by decide  
  f := ![![![-3331, -6421, 4414, -1026, 1677]], ![![3354, 5054, -3684, 818, -1401]], ![![382, -75, -69, -6, -27]], ![![1709, 2458, -1814, 399, -690]], ![![846, 905, -730, 150, -278]]]
  g := ![![![-1989, -2787, 3640, 258, 1053], ![-3452, -4836, 6318, 446, 1827], ![-5992, -8397, 10969, 782, 3165], ![-2209, -3103, 4038, 301, 1173], ![-2748, -3849, 5020, 346, 1474]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [97, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 136], [0, 1]]
 g := ![![[86, 18], [16], [17], [135, 115], [39], [88], [1]], ![[82, 119], [16], [17], [79, 22], [39], [88], [1]]]
 h' := ![![[15, 136], [110, 44], [93, 133], [57, 47], [51, 65], [51, 54], [40, 15], [0, 1]], ![[0, 1], [85, 93], [33, 4], [77, 90], [67, 72], [39, 83], [128, 122], [15, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [89, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [97, 122, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2102, 2878, -2720, -10395, 12047]
  a := ![3, 0, 3, -7, 16]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1045, 1524, -2720, -10395, 12047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2959, 7273, -2164, -8492, 253]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![2959, 7273, -2164, -8492, 253]] 
 ![![137, 0, 0, 0, 0], ![91, 1, 0, 0, 0], ![76, 0, 1, 0, 0], ![66, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![2959, 7273, -2164, -8492, 253], ![506, 4224, 4856, 11138, -25223], ![-50446, -125609, 34303, 138774, 8191], ![33414, 58059, -66900, -198431, 208161], ![161050, 396779, -116934, -460922, 9730]]]
  hmulB := by decide  
  f := ![![![-20054306577, -61689312503, -60187876178, -4268656560, -17404838411]], ![![-13574829017, -41757707565, -40741380164, -2889468290, -11781394916]], ![![-11566050482, -35578477865, -34712544747, -2461890022, -10038005501]], ![![-9823448616, -30218037669, -29482570578, -2090968751, -8525626911]], ![![-14401077299, -44299340618, -43221153226, -3065339250, -12498483675]]]
  g := ![![![303, 7273, -2164, -8492, 253], ![6997, 4224, 4856, 11138, -25223], ![-8618, -125609, 34303, 138774, 8191], ![-52998, 58059, -66900, -198431, 208161], ![17651, 396779, -116934, -460922, 9730]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-12009, -36936, -36034, -2556, -10420]] ![![1213, 3731, 3640, 258, 1053]]
  ![![-244885377, -753295085, -734960882, -52125042, -212532427]] where
 M := ![![![-244885377, -753295085, -734960882, -52125042, -212532427]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-244885377, -753295085, -734960882, -52125042, -212532427]] ![![2959, 7273, -2164, -8492, 253]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-11919, -24934, 16440, 52882, -38360]]]
 hmul := by decide  
 g := ![![![![-87, -182, 120, 386, -280]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1082097, -3328654, -3247641, -230330, -939137]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-1082097, -3328654, -3247641, -230330, -939137]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![0, 0, 0, 139, 0], ![39, 24, 111, 8, 1]] where
  M :=![![![-1082097, -3328654, -3247641, -230330, -939137], ![-1878274, -5777782, -5637158, -399800, -1630127], ![-3260254, -10028909, -9784813, -693954, -2829527], ![-1199400, -3689490, -3599691, -255301, -1040931], ![-1493554, -4594345, -4482544, -317932, -1296232]]]
  hmulB := by decide  
  f := ![![![-1351, -1262, 1067, -212, 407]], ![![814, 684, -602, 116, -229]], ![![-458, -331, 311, -62, 119]], ![![348, 234, -225, 47, -93]], ![![-583, -486, 430, -86, 164]]]
  g := ![![![255714, 138206, 726594, 52394, -939137], ![443861, 239894, 1261201, 90944, -1630127], ![770441, 416401, 2189156, 157858, -2829527], ![283431, 153186, 805350, 58073, -1040931], ![352946, 190757, 1002872, 72316, -1296232]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 4 2 7 [67, 122, 47, 25, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 62, 37, 76], [122, 37, 98, 84], [7, 39, 4, 118], [0, 1]]
 g := ![![[133, 56, 126, 35], [64, 34, 2, 54], [6, 83, 69], [87, 132, 108, 120], [5, 69, 69], [1], []], ![[19, 104, 1, 120, 46, 130], [34, 24, 75, 0, 95, 60], [106, 111, 71], [51, 101, 42, 86, 127, 110], [32, 23, 69], [103, 80, 120], [45, 85, 77]], ![[17, 47, 60, 115, 65, 130], [107, 110, 124, 99, 6, 85], [56, 74, 63], [104, 61, 28, 48, 56, 111], [43, 128, 129], [37, 132, 96], [61, 53, 106]], ![[47, 72, 72, 93, 136, 44], [60, 60, 68, 93, 117, 6], [48, 107, 41], [78, 34, 20, 2, 43, 6], [61, 136, 129], [42, 105, 117], [48, 66, 24]]]
 h' := ![![[124, 62, 37, 76], [21, 103, 111, 69], [96, 19, 70, 101], [9, 119, 114, 25], [123, 134, 122, 113], [72, 17, 92, 114], [0, 0, 1], [0, 1]], ![[122, 37, 98, 84], [121, 56, 67, 24], [130, 75, 125, 82], [2, 107, 105, 99], [41, 16, 138, 132], [10, 2, 85, 25], [129, 21, 102, 26], [124, 62, 37, 76]], ![[7, 39, 4, 118], [89, 132, 100, 92], [48, 10, 56, 7], [73, 117, 63, 87], [17, 91, 12, 121], [102, 28, 46, 44], [94, 120, 89, 97], [122, 37, 98, 84]], ![[0, 1], [41, 126, 0, 93], [105, 35, 27, 88], [92, 74, 135, 67], [134, 37, 6, 51], [32, 92, 55, 95], [30, 137, 86, 16], [7, 39, 4, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [115, 98, 93], []]
 b := ![[], [], [28, 28, 104, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 4
  hpos := by decide
  P := [67, 122, 47, 25, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![670026396, 1559248520, -647234104, -2305200267, 817808071]
  a := ![1, 1, 1, -5, 11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-224636607, -129986656, -657726115, -63652265, 817808071]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 373301041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1351, -1262, 1067, -212, 407]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-1351, -1262, 1067, -212, 407]] 
 ![![139, 0, 0, 0, 0], ![114, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![54, 0, 0, 0, 1]] where
  M :=![![![-1351, -1262, 1067, -212, 407], ![814, 684, -602, 116, -229], ![-458, -331, 311, -62, 119], ![348, 234, -225, 47, -93], ![170, 117, -116, 36, -46]]]
  hmulB := by decide  
  f := ![![![-1082097, -3328654, -3247641, -230330, -939137]], ![![-900988, -2771542, -2704088, -191780, -781955]], ![![-568396, -1748451, -1705897, -120986, -493303]], ![![-55338, -170226, -166083, -11779, -48027]], ![![-431128, -1326199, -1293922, -91768, -374170]]]
  g := ![![![339, -1262, 1067, -212, 407], ![-168, 684, -602, 116, -229], ![68, -331, 311, -62, 119], ![-42, 234, -225, 47, -93], ![-20, 117, -116, 36, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-1082097, -3328654, -3247641, -230330, -939137]] ![![-1351, -1262, 1067, -212, 407]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![139, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2597, 2020, -1832, 346, -700]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![2597, 2020, -1832, 346, -700]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![114, 78, 52, 11, 1]] where
  M :=![![![2597, 2020, -1832, 346, -700], ![-1400, -903, 888, -156, 338], ![676, 290, -353, 60, -130], ![-468, -132, 210, -53, 90], ![-252, -94, 136, -40, 37]]]
  hmulB := by decide  
  f := ![![![9, 28, 28, 2, 8]], ![![16, 49, 48, 4, 14]], ![![28, 86, 83, 4, 26]], ![![12, 36, 30, -1, 6]], ![![26, 80, 78, 5, 23]]]
  g := ![![![553, 380, 232, 54, -700], ![-268, -183, -112, -26, 338], ![104, 70, 43, 10, -130], ![-72, -48, -30, -7, 90], ![-30, -20, -12, -3, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [122, 61, 15, 42, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 124, 3, 46], [115, 37, 86, 141], [8, 136, 60, 111], [0, 1]]
 g := ![![[27, 112, 75, 120], [80, 88, 132], [118, 15, 139, 7], [145, 100, 124], [0, 2, 33, 125], [1], []], ![[128, 78, 26, 45, 68, 54], [146, 71, 88], [5, 54, 5, 109, 108, 24], [9, 4, 22], [20, 60, 137, 69, 144, 107], [128, 130, 9], [145, 59, 30]], ![[26, 87, 58, 83, 75, 108], [93, 111, 133], [118, 148, 146, 68, 27, 147], [103, 67, 29], [112, 35, 51, 137, 126, 135], [78, 78, 145], [116, 108, 64]], ![[116, 9, 22, 88, 86, 98], [33, 24, 4], [133, 124, 77, 64, 84, 65], [97, 82, 36], [98, 81, 68, 85, 13, 139], [3, 148, 86], [30, 54, 103]]]
 h' := ![![[133, 124, 3, 46], [45, 0, 88, 57], [57, 103, 53, 70], [41, 113, 93, 56], [0, 38, 8, 71], [27, 88, 134, 107], [0, 0, 1], [0, 1]], ![[115, 37, 86, 141], [42, 75, 137, 84], [102, 58, 79, 104], [103, 44, 138, 93], [146, 93, 14, 97], [30, 113, 96, 144], [148, 104, 35, 3], [133, 124, 3, 46]], ![[8, 136, 60, 111], [85, 8, 134, 106], [16, 28, 118, 122], [129, 89, 74, 74], [46, 116, 19, 124], [66, 53, 91, 28], [116, 29, 96, 88], [115, 37, 86, 141]], ![[0, 1], [117, 66, 88, 51], [92, 109, 48, 2], [17, 52, 142, 75], [123, 51, 108, 6], [34, 44, 126, 19], [129, 16, 17, 58], [8, 136, 60, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [54, 60, 35], []]
 b := ![[], [], [128, 27, 66, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [122, 61, 15, 42, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16202, -41560, 26728, 88647, -63407]
  a := ![4, 0, 0, 1, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![48404, 32914, 22308, 5276, -63407]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 28, 28, 2, 8]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![9, 28, 28, 2, 8]] 
 ![![149, 0, 0, 0, 0], ![115, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![147, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![9, 28, 28, 2, 8], ![16, 49, 48, 4, 14], ![28, 86, 83, 4, 26], ![12, 36, 30, -1, 6], ![12, 38, 40, 8, 5]]]
  hmulB := by decide  
  f := ![![![2597, 2020, -1832, 346, -700]], ![![1995, 1553, -1408, 266, -538]], ![![632, 490, -445, 84, -170]], ![![2559, 1992, -1806, 341, -690]], ![![2177, 1694, -1536, 290, -587]]]
  g := ![![![-37, 28, 28, 2, 8], ![-65, 49, 48, 4, 14], ![-112, 86, 83, 4, 26], ![-39, 36, 30, -1, 6], ![-51, 38, 40, 8, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![2597, 2020, -1832, 346, -700]] ![![9, 28, 28, 2, 8]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1153, 5105, 5851, 306, 1732]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![1153, 5105, 5851, 306, 1732]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![0, 0, 0, 151, 0], ![29, 40, 42, 83, 1]] where
  M :=![![![1153, 5105, 5851, 306, 1732], ![3464, 9813, 9224, 698, 2650], ![5300, 16714, 16387, 1152, 4744], ![2094, 6153, 5985, 427, 1728], ![2548, 7680, 7460, 534, 2155]]]
  hmulB := by decide  
  f := ![![![3, 7, -3, -8, 2]], ![![4, 13, 2, -2, -22]], ![![-44, -106, 37, 140, -28]], ![![-6, -39, -39, -89, 210]], ![![-13, -44, -12, -15, 103]]]
  g := ![![![-325, -425, -443, -950, 1732], ![-486, -637, -676, -1452, 2650], ![-876, -1146, -1211, -2600, 4744], ![-318, -417, -441, -947, 1728], ![-397, -520, -550, -1181, 2155]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 4 2 7 [146, 40, 72, 135, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 9, 73, 100], [128, 56, 35, 92], [15, 85, 43, 110], [0, 1]]
 g := ![![[35, 106, 18, 1], [112, 78, 62, 78], [93, 147, 38, 34], [49, 22, 40], [95, 101, 131, 105], [1], []], ![[97, 17, 139, 64, 33, 44], [9, 82, 22, 118, 145, 55], [53, 120, 150, 115, 91, 78], [110, 26, 144], [0, 143, 41, 50, 23, 118], [105, 111, 74], [100, 44, 34]], ![[57, 134, 20, 73, 24, 13], [118, 32, 61, 18, 121, 147], [135, 73, 74, 45, 135, 46], [144, 77, 20], [85, 123, 114, 95, 46, 114], [36, 0, 118], [73, 75, 8]], ![[145, 132, 80, 17, 69, 121], [67, 92, 47, 79, 12, 37], [102, 69, 74, 47, 54, 64], [100, 147, 39], [142, 112, 50, 34, 27, 44], [16, 112, 138], [127, 116, 20]]]
 h' := ![![[24, 9, 73, 100], [107, 131, 150, 150], [12, 107, 21, 94], [125, 136, 2, 100], [22, 52, 96, 77], [5, 111, 79, 16], [0, 0, 1], [0, 1]], ![[128, 56, 35, 92], [2, 13, 92, 38], [69, 121, 137, 139], [116, 25, 2, 100], [87, 62, 119, 12], [131, 48, 89, 124], [19, 125, 80, 15], [24, 9, 73, 100]], ![[15, 85, 43, 110], [76, 137, 49, 15], [36, 135, 117, 135], [10, 83, 53, 23], [14, 141, 49, 110], [22, 60, 26, 109], [139, 13, 105, 119], [128, 56, 35, 92]], ![[0, 1], [46, 21, 11, 99], [25, 90, 27, 85], [138, 58, 94, 79], [98, 47, 38, 103], [82, 83, 108, 53], [105, 13, 116, 17], [15, 85, 43, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [77, 23, 31], []]
 b := ![[], [], [62, 8, 7, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 4
  hpos := by decide
  P := [146, 40, 72, 135, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1262641230834, 2370030265400, -2218383013470, -6751779546268, 6369249549662]
  a := ![7, 2, -24, 23, -94]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1214871494764, -1671522859080, -1786270623174, -3545692001114, 6369249549662]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 519885601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 7, -3, -8, 2]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![3, 7, -3, -8, 2]] 
 ![![151, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![82, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![3, 7, -3, -8, 2], ![4, 13, 2, -2, -22], ![-44, -106, 37, 140, -28], ![-6, -39, -39, -89, 210], ![136, 322, -122, -446, 121]]]
  hmulB := by decide  
  f := ![![![1153, 5105, 5851, 306, 1732]], ![![420, 1823, 2076, 110, 614]], ![![142, 584, 651, 36, 192]], ![![640, 2813, 3217, 169, 952]], ![![727, 3195, 3653, 192, 1081]]]
  g := ![![![1, 7, -3, -8, 2], ![10, 13, 2, -2, -22], ![-26, -106, 37, 140, -28], ![-64, -39, -39, -89, 210], ![69, 322, -122, -446, 121]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![1153, 5105, 5851, 306, 1732]] ![![3, 7, -3, -8, 2]]
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


lemma PB434I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB434I3 : PrimesBelowBoundCertificateInterval O 103 151 434 where
  m := 9
  g := ![2, 3, 3, 3, 1, 3, 2, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB434I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1, I137N2]
    · exact ![I139N0, I139N1]
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
    · exact ![1225043, 11449]
    · exact ![11881, 11881, 109]
    · exact ![1442897, 113, 113]
    · exact ![2048383, 127, 127]
    · exact ![38579489651]
    · exact ![18769, 18769, 137]
    · exact ![373301041, 139]
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
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I109N2, I113N1, I113N2, I127N1, I127N2, I137N2, I139N1, I149N1, I151N1]
  Il := ![[], [I109N2], [I113N1, I113N2], [I127N1, I127N2], [], [I137N2], [I139N1], [I149N1], [I151N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
