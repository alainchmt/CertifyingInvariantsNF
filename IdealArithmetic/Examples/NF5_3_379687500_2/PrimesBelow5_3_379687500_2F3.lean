
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11583, -6539, -722, 2539, 14696]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-11583, -6539, -722, 2539, 14696]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![60, 98, 47, 5, 1]] where
  M :=![![![-11583, -6539, -722, 2539, 14696], ![-20142, -11413, -1258, 4474, 25890], ![-35660, -20010, -2111, 7978, 46022], ![-15992, -9735, -807, 4053, 22874], ![-11960, -6659, -773, 2570, 14959]]]
  hmulB := by decide  
  f := ![![![1107, 1774, 105, -563, -3620]], ![![-5650, -9047, -536, 2872, 18466]], ![![28808, 46134, 2735, -14646, -94166]], ![![-87818, -140661, -8337, 44653, 287090]], ![![4136, 6624, 393, -2103, -13521]]]
  g := ![![![-8349, -13521, -6462, -663, 14696], ![-14706, -23819, -11384, -1168, 25890], ![-26140, -42338, -20235, -2076, 46022], ![-12976, -21041, -10055, -1031, 22874], ![-8500, -13763, -6578, -675, 14959]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [89, 44, 101, 98, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 91, 96, 79], [31, 74, 14, 102], [42, 48, 104, 33], [0, 1]]
 g := ![![[44, 43, 48, 48], [75, 32, 32, 36], [81, 36, 47], [104, 82, 29, 10], [87, 9, 1], []], ![[43, 36, 59, 86, 98, 14], [71, 11, 63, 31, 64, 3], [94, 41, 76], [21, 81, 15, 83, 85, 23], [75, 36, 37], [33, 29, 10, 36, 83, 90]], ![[97, 9, 99, 1, 27, 75], [27, 5, 0, 76, 23, 10], [77, 4, 48], [100, 57, 0, 66, 12, 90], [59, 6, 25], [37, 59, 83, 8, 32, 89]], ![[69, 25, 53, 80, 38, 9], [7, 64, 67, 63, 39, 53], [41, 104, 30], [12, 12, 26, 55, 27, 49], [63, 73, 42], [62, 66, 56, 34, 15, 92]]]
 h' := ![![[43, 91, 96, 79], [66, 13, 33, 72], [94, 54, 60, 101], [53, 26, 43, 49], [68, 79, 37, 44], [0, 0, 0, 1], [0, 1]], ![[31, 74, 14, 102], [64, 102, 34, 69], [55, 42, 69, 33], [17, 76, 77, 66], [11, 83, 86, 89], [65, 91, 106, 95], [43, 91, 96, 79]], ![[42, 48, 104, 33], [82, 77, 48, 29], [22, 106, 84, 31], [54, 105, 0, 35], [45, 14, 36, 14], [69, 60, 54, 102], [31, 74, 14, 102]], ![[0, 1], [106, 22, 99, 44], [5, 12, 1, 49], [103, 7, 94, 64], [32, 38, 55, 67], [90, 63, 54, 16], [42, 48, 104, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [50, 22, 56], []]
 b := ![[], [], [105, 19, 12, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [89, 44, 101, 98, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2900399205299, -3102213115388, -177572514688, 1170157472444, 7050287767852]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3980538927817, -6486265554812, -3098514930876, -318516648288, 7050287767852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1107, 1774, 105, -563, -3620]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![1107, 1774, 105, -563, -3620]] 
 ![![107, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![98, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![1107, 1774, 105, -563, -3620], ![-5650, -9047, -536, 2872, 18466], ![28808, 46134, 2735, -14646, -94166], ![-87818, -140661, -8337, 44653, 287090], ![14946, 23941, 1419, -7600, -48863]]]
  hmulB := by decide  
  f := ![![![-11583, -6539, -722, 2539, 14696]], ![![-513, -290, -32, 113, 654]], ![![-10942, -6176, -681, 2400, 13890]], ![![-2098, -1191, -129, 465, 2686]], ![![-10504, -5929, -655, 2302, 13325]]]
  g := ![![![3207, 1774, 105, -563, -3620], ![-16359, -9047, -536, 2872, 18466], ![83420, 46134, 2735, -14646, -94166], ![-254329, -140661, -8337, 44653, 287090], ![43287, 23941, 1419, -7600, -48863]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-11583, -6539, -722, 2539, 14696]] ![![1107, 1774, 105, -563, -3620]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![439, 163, 47, -108, -696]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![439, 163, 47, -108, -696]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![75, 12, 1, 0, 0], ![3, 14, 0, 1, 0], ![45, 54, 0, 0, 1]] where
  M :=![![![439, 163, 47, -108, -696], ![-1128, -1553, -258, 622, 3648], ![-3596, 252, -197, 408, 3140], ![11078, 8988, 1776, -4207, -25568], ![-2246, -2102, -394, 938, 5643]]]
  hmulB := by decide  
  f := ![![![-2469, -1675, -89, 814, 4516]], ![![-11932, -7889, -426, 3870, 21400]], ![![-3551, -2385, -128, 1162, 6440]], ![![-2605, -1717, -93, 843, 4660]], ![![-6851, -4549, -245, 2228, 12327]]]
  g := ![![![262, 355, 47, -108, -696], ![-1356, -1873, -258, 622, 3648], ![-1205, -1584, -197, 408, 3140], ![9551, 13094, 1776, -4207, -25568], ![-2105, -2892, -394, 938, 5643]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [106, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 108], [0, 1]]
 g := ![![[83, 36], [31], [65, 4], [95, 73], [71], [31, 1]], ![[0, 73], [31], [80, 105], [69, 36], [71], [62, 108]]]
 h' := ![![[31, 108], [77, 103], [86, 85], [67, 2], [33, 20], [93, 92], [0, 1]], ![[0, 1], [0, 6], [105, 24], [20, 107], [108, 89], [2, 17], [31, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [37, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [106, 78, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2331151, -2561328, -166238, 960830, 5818496]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2335579, -3011164, -166238, 960830, 5818496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![585, 961, 57, -304, -1952]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![585, 961, 57, -304, -1952]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![89, 11, 1, 0, 0], ![11, 33, 0, 1, 0], ![60, 12, 0, 0, 1]] where
  M :=![![![585, 961, 57, -304, -1952], ![-2976, -4823, -278, 1522, 9792], ![15436, 24636, 1445, -7816, -50308], ![-47670, -75816, -4524, 24119, 155088], ![8134, 12922, 774, -4114, -26451]]]
  hmulB := by decide  
  f := ![![![64277, 42911, 2345, -20866, -115660]], ![![308740, 206089, 11266, -100206, -555448]], ![![97241, 64914, 3548, -31564, -174960]], ![![125809, 83980, 4591, -40833, -226340]], ![![67314, 44936, 2456, -21850, -121115]]]
  g := ![![![1064, 310, 57, -304, -1952], ![-5344, -1555, -278, 1522, 9792], ![27443, 7985, 1445, -7816, -50308], ![-84547, -24615, -4524, 24119, 155088], ![14418, 4198, 774, -4114, -26451]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P1 : CertificateIrreducibleZModOfList' 109 2 2 6 [94, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 108], [0, 1]]
 g := ![![[56, 29], [105], [69, 74], [70, 45], [94], [77, 1]], ![[0, 80], [105], [99, 35], [47, 64], [94], [45, 108]]]
 h' := ![![[77, 108], [22, 62], [54, 66], [69, 69], [76, 63], [65, 58], [0, 1]], ![[0, 1], [0, 47], [13, 43], [41, 40], [22, 46], [62, 51], [77, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [78, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N1 : CertifiedPrimeIdeal' SI109N1 109 where
  n := 2
  hpos := by decide
  P := [94, 32, 1]
  hirr := P109P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20879, -17883, -1035, 7442, 43848]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-24234, -7140, -1035, 7442, 43848]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N1 B_one_repr
lemma NI109N1 : Nat.card (O ⧸ I109N1) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![329, 245, 20, -115, -646]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![329, 245, 20, -115, -646]] 
 ![![109, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![67, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![329, 245, 20, -115, -646], ![1462, 871, 52, -444, -2488], ![5816, 3726, 119, -1832, -10016], ![12588, 9213, 579, -4333, -24024], ![-972, -823, -55, 368, 2029]]]
  hmulB := by decide  
  f := ![![![-1158603, -650282, -72399, 252005, 1460158]], ![![-932076, -523149, -58244, 202736, 1174688]], ![![-200324, -112406, -12517, 43564, 252408]], ![![-722679, -405713, -45162, 157216, 910966]], ![![-223874, -125637, -13989, 48690, 282113]]]
  g := ![![![-4, 245, 20, -115, -646], ![48, 871, 52, -444, -2488], ![60, 3726, 119, -1832, -10016], ![-167, 9213, 579, -4333, -24024], ![50, -823, -55, 368, 2029]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![439, 163, 47, -108, -696]] ![![585, 961, 57, -304, -1952]]
  ![![-15685, -11962, -2488, 5770, 35084]] where
 M := ![![![-15685, -11962, -2488, 5770, 35084]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![-15685, -11962, -2488, 5770, 35084]] ![![329, 245, 20, -115, -646]]
  ![![109, 0, 0, 0, 0]] where
 M := ![![![1412095, 752863, 179414, -417579, -2619270]]]
 hmul := by decide  
 g := ![![![![12955, 6907, 1646, -3831, -24030]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1339, 1212, 219, -539, -3272]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![1339, 1212, 219, -539, -3272]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![0, 0, 113, 0, 0], ![0, 0, 0, 113, 0], ![87, 39, 89, 73, 1]] where
  M :=![![![1339, 1212, 219, -539, -3272], ![14, -2959, -300, 856, 4702], ![-13864, -7002, -1993, 4174, 25654], ![11298, 17631, 3675, -7435, -41610], ![-1570, -3747, -693, 1444, 7953]]]
  hmulB := by decide  
  f := ![![![-741, -507, -24, 253, 1396]], ![![-3922, -2639, -138, 1294, 7162]], ![![-19444, -13014, -701, 6346, 35158]], ![![-37476, -25029, -1365, 12175, 67482]], ![![-41421, -27702, -1499, 13496, 74783]]]
  g := ![![![2531, 1140, 2579, 2109, -3272], ![-3620, -1649, -3706, -3030, 4702], ![-19874, -8916, -20223, -16536, 25654], ![32136, 14517, 32805, 26815, -41610], ![-6137, -2778, -6270, -5125, 7953]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 4 2 6 [77, 8, 4, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 22, 52, 1], [63, 70, 28, 12], [108, 20, 33, 100], [0, 1]]
 g := ![![[89, 101, 24, 14], [47, 28, 81], [36, 106, 1], [59, 15, 26], [14, 108, 98, 1], []], ![[105, 70, 57, 69, 62, 26], [81, 72, 4], [66, 79, 85], [98, 49, 106], [84, 98, 102, 79, 76, 14], [40, 105, 87, 70, 28, 1]], ![[65, 97, 102, 79, 55, 34], [30, 64, 41], [58, 82, 44], [31, 23, 53], [67, 41, 54, 62, 39, 27], [111, 38, 14, 29, 75, 33]], ![[86, 22, 84, 109, 26, 31], [81, 48, 91], [50, 11, 81], [59, 112, 111], [21, 104, 69, 36, 21, 97], [45, 33, 27, 19, 79, 63]]]
 h' := ![![[40, 22, 52, 1], [6, 67, 18, 63], [110, 0, 0, 9], [82, 97, 109, 112], [52, 47, 9, 79], [0, 0, 0, 1], [0, 1]], ![[63, 70, 28, 12], [92, 67, 20, 34], [1, 22, 33, 2], [87, 5, 111, 57], [66, 26, 1, 85], [13, 15, 79, 63], [40, 22, 52, 1]], ![[108, 20, 33, 100], [37, 11, 43, 60], [55, 44, 46, 43], [1, 21, 76, 48], [69, 59, 71, 36], [19, 30, 93, 55], [63, 70, 28, 12]], ![[0, 1], [3, 81, 32, 69], [5, 47, 34, 59], [37, 103, 43, 9], [88, 94, 32, 26], [26, 68, 54, 107], [108, 20, 33, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [12, 77, 94], []]
 b := ![[], [], [84, 85, 67, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 4
  hpos := by decide
  P := [77, 8, 4, 15, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15778823825313, -16466264053864, -936101516328, 6283897951902, 37698926529444]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29164472848557, -13156853085860, -29700358961388, -24298564059270, 37698926529444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 163047361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![741, 507, 24, -253, -1396]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![741, 507, 24, -253, -1396]] 
 ![![113, 0, 0, 0, 0], ![54, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![73, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![741, 507, 24, -253, -1396], ![3922, 2639, 138, -1294, -7162], ![19444, 13014, 701, -6346, -35158], ![37476, 25029, 1365, -12175, -67482], ![-3116, -2067, -117, 998, 5539]]]
  hmulB := by decide  
  f := ![![![-1339, -1212, -219, 539, 3272]], ![![-640, -553, -102, 250, 1522]], ![![-138, -174, -25, 68, 410]], ![![-965, -939, -174, 414, 2482]], ![![-152, -117, -21, 54, 335]]]
  g := ![![![96, 507, 24, -253, -1396], ![470, 2639, 138, -1294, -7162], ![2272, 13014, 701, -6346, -35158], ![4331, 25029, 1365, -12175, -67482], ![-348, -2067, -117, 998, 5539]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![1339, 1212, 219, -539, -3272]] ![![741, 507, 24, -253, -1396]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![-113, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2723, -1528, -170, 592, 3430]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-2723, -1528, -170, 592, 3430]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![115, 89, 1, 0, 0], ![32, 53, 0, 1, 0], ![42, 6, 0, 0, 1]] where
  M :=![![![-2723, -1528, -170, 592, 3430], ![-4600, -2587, -288, 1002, 5806], ![-7772, -4356, -487, 1690, 9794], ![-2648, -1482, -162, 571, 3314], ![-2900, -1630, -182, 632, 3661]]]
  hmulB := by decide  
  f := ![![![43, 52, 2, -20, -110]], ![![320, 203, 24, -106, -590]], ![![275, 197, 19, -96, -534]], ![![152, 99, 10, -51, -280]], ![![30, 28, 2, -12, -67]]]
  g := ![![![-1151, -302, -170, 592, 3430], ![-1948, -511, -288, 1002, 5806], ![-3285, -861, -487, 1690, 9794], ![-1114, -293, -162, 571, 3314], ![-1228, -322, -182, 632, 3661]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [3, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 126], [0, 1]]
 g := ![![[111, 1], [74, 47], [4, 1], [92, 17], [3, 98], [48, 1]], ![[32, 126], [44, 80], [52, 126], [19, 110], [8, 29], [96, 126]]]
 h' := ![![[48, 126], [32, 126], [115, 38], [105, 1], [118, 12], [110, 15], [0, 1]], ![[0, 1], [111, 1], [34, 89], [26, 126], [59, 115], [68, 112], [48, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [8, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [3, 79, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3681909, -3547101, -224166, 1402171, 8401194]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2957657, -852902, -224166, 1402171, 8401194]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 237, 14, -79, -498]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![167, 237, 14, -79, -498]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![113, 26, 1, 0, 0], ![62, 23, 0, 1, 0], ![107, 42, 0, 0, 1]] where
  M :=![![![167, 237, 14, -79, -498], ![-514, -979, -58, 292, 1924], ![4232, 6054, 355, -2008, -12692], ![-9124, -15951, -951, 4901, 31936], ![1688, 2805, 167, -878, -5679]]]
  hmulB := by decide  
  f := ![![![7597, 4284, 479, -1661, -9626]], ![![12842, 7151, 800, -2782, -16136]], ![![9555, 5368, 600, -2083, -12074]], ![![6094, 3424, 383, -1329, -7704]], ![![10711, 6009, 672, -2333, -13525]]]
  g := ![![![447, 178, 14, -79, -498], ![-1716, -685, -58, 292, 1924], ![11391, 4536, 355, -2008, -12692], ![-28525, -11380, -951, 4901, 31936], ![5078, 2025, 167, -878, -5679]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [61, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 126], [0, 1]]
 g := ![![[113, 25], [70, 2], [30, 19], [26, 8], [67, 60], [92, 1]], ![[0, 102], [0, 125], [0, 108], [0, 119], [126, 67], [57, 126]]]
 h' := ![![[92, 126], [48, 5], [75, 111], [65, 20], [104, 32], [103, 21], [0, 1]], ![[0, 1], [0, 122], [0, 16], [0, 107], [0, 95], [3, 106], [92, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [1, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [61, 35, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54549, -85806, -4132, 26678, 173926]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-156313, -62180, -4132, 26678, 173926]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -10, -1, 3, 16]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-3, -10, -1, 3, 16]] 
 ![![127, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![110, 0, 1, 0, 0], ![47, 0, 0, 1, 0], ![53, 0, 0, 0, 1]] where
  M :=![![![-3, -10, -1, 3, 16], ![-62, -41, -8, 20, 122], ![16, 114, 17, -38, -214], ![226, 33, 21, -41, -286], ![-66, -25, -7, 16, 103]]]
  hmulB := by decide  
  f := ![![![-357, -461, -30, 153, 964]], ![![-26, -29, -2, 10, 62]], ![![-366, -484, -31, 160, 1010]], ![![11, 68, 3, -18, -126]], ![![-175, -234, -15, 77, 487]]]
  g := ![![![-6, -10, -1, 3, 16], ![-48, -41, -8, 20, 122], ![78, 114, 17, -38, -214], ![115, 33, 21, -41, -286], ![-41, -25, -7, 16, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-2723, -1528, -170, 592, 3430]] ![![167, 237, 14, -79, -498]]
  ![![-357, -461, -30, 153, 964]] where
 M := ![![![-357, -461, -30, 153, 964]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-357, -461, -30, 153, 964]] ![![-3, -10, -1, 3, 16]]
  ![![127, 0, 0, 0, 0]] where
 M := ![![![127, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![260711, 146355, 16292, -56715, -328626]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![260711, 146355, 16292, -56715, -328626]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![35, 3, 80, 57, 1]] where
  M :=![![![260711, 146355, 16292, -56715, -328626], ![440022, 247013, 27494, -95720, -554628], ![742816, 417078, 46423, -161624, -936484], ![255856, 143637, 15993, -55695, -322720], ![277116, 155565, 17315, -60278, -349267]]]
  hmulB := by decide  
  f := ![![![17, 30, 1, -9, -58]], ![![-94, -149, -8, 46, 304]], ![![692, 966, 65, -324, -2060]], ![![-1646, -2733, -177, 865, 5564]], ![![-289, -591, -37, 176, 1147]]]
  g := ![![![89791, 8643, 200812, 142557, -328626], ![151542, 14587, 338914, 240596, -554628], ![255876, 24630, 572253, 406244, -936484], ![88176, 8487, 197203, 139995, -322720], ![95431, 9186, 213425, 151511, -349267]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 4 2 7 [64, 73, 9, 90, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 15, 100, 28], [80, 22, 5, 64], [80, 93, 26, 39], [0, 1]]
 g := ![![[8, 53, 8, 44], [28, 9, 119, 105], [77, 27, 100], [69, 16, 48], [20, 63, 109], [1], []], ![[7, 5, 71, 20, 90, 38], [18, 18, 24, 49, 11, 89], [58, 121, 48], [119, 12, 38], [39, 100, 13], [69, 72, 102], [117, 16, 129]], ![[122, 18, 83, 33, 30, 77], [113, 22, 78, 51, 58, 125], [35, 73, 44], [96, 111, 39], [4, 37, 45], [75, 120, 65], [93, 110, 35]], ![[4, 67, 24, 45, 28, 13], [68, 97, 12, 5, 45, 55], [74], [107, 5, 12], [115, 98, 28], [10, 15, 89], [42, 68, 80]]]
 h' := ![![[12, 15, 100, 28], [42, 62, 67, 100], [113, 67, 62, 74], [71, 43, 78, 10], [65, 53, 97, 21], [67, 58, 122, 41], [0, 0, 1], [0, 1]], ![[80, 22, 5, 64], [31, 11, 18, 56], [31, 16, 92, 123], [59, 75, 34, 21], [48, 102, 130, 118], [102, 85, 89, 119], [123, 96, 8, 87], [12, 15, 100, 28]], ![[80, 93, 26, 39], [85, 103, 60, 6], [39, 8, 91, 129], [24, 17, 123, 100], [81, 67, 43, 68], [59, 22, 15, 62], [55, 40, 2, 117], [80, 22, 5, 64]], ![[0, 1], [34, 86, 117, 100], [69, 40, 17, 67], [73, 127, 27], [41, 40, 123, 55], [117, 97, 36, 40], [44, 126, 120, 58], [80, 93, 26, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [92, 81, 67], []]
 b := ![[], [], [118, 79, 60, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 4
  hpos := by decide
  P := [64, 73, 9, 90, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-241319748309667, -239906412469502, -13681121797918, 93765480604314, 558082347958426]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-150948106311867, -14611858445380, -340918083652458, -242113956893328, 558082347958426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 294499921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 30, 1, -9, -58]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![17, 30, 1, -9, -58]] 
 ![![131, 0, 0, 0, 0], ![44, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![68, 0, 0, 1, 0], ![35, 0, 0, 0, 1]] where
  M :=![![![17, 30, 1, -9, -58], ![-94, -149, -8, 46, 304], ![692, 966, 65, -324, -2060], ![-1646, -2733, -177, 865, 5564], ![290, 477, 31, -152, -973]]]
  hmulB := by decide  
  f := ![![![260711, 146355, 16292, -56715, -328626]], ![![90926, 51043, 5682, -19780, -114612]], ![![63385, 35583, 3961, -13789, -79898]], ![![137284, 77067, 8579, -29865, -173048]], ![![71771, 40290, 4485, -15613, -90467]]]
  g := ![![![10, 30, 1, -9, -58], ![-54, -149, -8, 46, 304], ![385, 966, 65, -324, -2060], ![-991, -2733, -177, 865, 5564], ![174, 477, 31, -152, -973]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![260711, 146355, 16292, -56715, -328626]] ![![17, 30, 1, -9, -58]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35451, -19971, -2223, 7730, 44780]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-35451, -19971, -2223, 7730, 44780]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![0, 0, 0, 137, 0], ![56, 20, 117, 33, 1]] where
  M :=![![![-35451, -19971, -2223, 7730, 44780], ![-60260, -33871, -3804, 13154, 76280], ![-100340, -55368, -6145, 21476, 124532], ![-31842, -18594, -1956, 6899, 39636], ![-38330, -21420, -2418, 8360, 48523]]]
  hmulB := by decide  
  f := ![![![1613, 2583, 153, -820, -5272]], ![![-8216, -13163, -780, 4178, 26864]], ![![41932, 67140, 3979, -21316, -137044]], ![![-127722, -204624, -12126, 64951, 417612]], ![![4664, 7438, 441, -2365, -15197]]]
  g := ![![![-18563, -6683, -38259, -10730, 44780], ![-31620, -11383, -65172, -18278, 76280], ![-51636, -18584, -106397, -29840, 124532], ![-16434, -5922, -33864, -9497, 39636], ![-20114, -7240, -41457, -11627, 48523]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 4 2 7 [25, 52, 69, 17, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 128, 136, 126], [120, 96, 113, 55], [123, 49, 25, 93], [0, 1]]
 g := ![![[120, 126, 39, 17], [114, 29, 19], [51, 91, 121], [9, 92, 122, 25], [87, 36, 15], [1], []], ![[119, 89, 47, 99, 18, 98], [123, 18, 78], [73, 24, 135], [39, 10, 64, 103, 9, 59], [72, 3, 11], [80, 98, 69], [4, 20, 121]], ![[118, 43, 22, 109, 126, 26], [26, 118, 68], [45, 105, 15], [30, 125, 116, 74, 28, 21], [34, 97, 76], [21, 17, 28], [74, 50, 11]], ![[98, 82, 100, 108, 53, 121], [53, 90, 120], [14, 79, 76], [109, 118, 36, 15, 101, 59], [67, 129, 126], [31, 113, 38], [135, 97, 18]]]
 h' := ![![[14, 128, 136, 126], [105, 57, 14, 90], [30, 89, 110, 29], [49, 40, 2, 126], [94, 53, 96, 132], [112, 85, 68, 120], [0, 0, 1], [0, 1]], ![[120, 96, 113, 55], [74, 31, 99, 4], [86, 36, 5, 107], [33, 63, 78, 86], [88, 81, 50, 13], [92, 48, 64, 55], [96, 136, 96, 53], [14, 128, 136, 126]], ![[123, 49, 25, 93], [91, 3, 22, 33], [59, 33, 18, 43], [122, 80, 70, 120], [117, 14, 136, 67], [62, 119, 27, 79], [83, 132, 133, 24], [120, 96, 113, 55]], ![[0, 1], [28, 46, 2, 10], [95, 116, 4, 95], [87, 91, 124, 79], [50, 126, 129, 62], [9, 22, 115, 20], [109, 6, 44, 60], [123, 49, 25, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [41, 12, 43], []]
 b := ![[], [], [28, 90, 77, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 4
  hpos := by decide
  P := [25, 52, 69, 17, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1814033874, -2725536654, -160432051, 886733032, 5645775164]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2321003234, -844095182, -4822745447, -1353458740, 5645775164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 352275361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1613, -2583, -153, 820, 5272]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-1613, -2583, -153, 820, 5272]] 
 ![![137, 0, 0, 0, 0], ![85, 1, 0, 0, 0], ![36, 0, 1, 0, 0], ![96, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![-1613, -2583, -153, 820, 5272], ![8216, 13163, 780, -4178, -26864], ![-41932, -67140, -3979, 21316, 137044], ![127722, 204624, 12126, -64951, -417612], ![-21742, -34830, -2064, 11056, 71085]]]
  hmulB := by decide  
  f := ![![![35451, 19971, 2223, -7730, -44780]], ![![22435, 12638, 1407, -4892, -28340]], ![![10048, 5652, 629, -2188, -12676]], ![![25074, 14130, 1572, -5467, -31668]], ![![15547, 8757, 975, -3390, -19639]]]
  g := ![![![-1214, -2583, -153, 820, 5272], ![6185, 13163, 780, -4178, -26864], ![-31560, -67140, -3979, 21316, 137044], ![96150, 204624, 12126, -64951, -417612], ![-16367, -34830, -2064, 11056, 71085]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-35451, -19971, -2223, 7730, 44780]] ![![-1613, -2583, -153, 820, 5272]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![-137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)
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


def P139P0 : CertificateIrreducibleZModOfList' 139 5 2 7 [43, 11, 33, 132, 62, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 81, 131, 111, 86], [16, 29, 112, 74, 109], [19, 55, 123, 38, 69], [38, 112, 51, 55, 14], [0, 1]]
 g := ![![[29, 3, 78, 58, 7], [132, 138, 3, 134, 6], [103, 66, 25, 34], [107, 53, 112, 17, 25], [129, 98, 77, 1], [], []], ![[39, 5, 60, 69, 118, 40, 8, 121], [94, 135, 43, 81, 103, 43, 0, 13], [125, 14, 36, 131], [59, 78, 56, 47, 114, 18, 129, 42], [34, 64, 127, 96], [111, 69, 90, 120], [135, 46, 58, 29]], ![[17, 25, 101, 108, 28, 95, 5, 94], [37, 110, 109, 69, 71, 23, 111, 43], [80, 11, 100, 45], [87, 69, 38, 133, 35, 81, 2, 84], [33, 42, 93, 24], [104, 33, 124, 77], [70, 2, 86, 66]], ![[24, 125, 115, 30, 36, 81, 23, 44], [60, 80, 101, 84, 35, 117, 112, 49], [92, 29, 122, 122], [117, 63, 5, 8, 25, 69, 38, 4], [33, 91, 1, 96], [85, 19, 63, 36], [45, 18, 16, 35]], ![[76, 137, 118, 93, 95, 5, 41, 8], [3, 13, 74, 31, 23, 34, 88, 12], [51, 97, 129, 52], [61, 18, 9, 43, 135, 128, 56, 39], [13, 87, 78, 122], [117, 69, 33, 42], [48, 44, 91, 57]]]
 h' := ![![[4, 81, 131, 111, 86], [23, 58, 15, 73, 110], [76, 78, 6, 130, 80], [125, 49, 14, 109, 27], [13, 66, 111, 115, 5], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[16, 29, 112, 74, 109], [67, 49, 83, 86, 10], [28, 60, 125, 41, 12], [11, 61, 133, 44, 39], [9, 2, 85, 57, 77], [130, 27, 102, 108, 97], [49, 104, 15, 53, 113], [4, 81, 131, 111, 86]], ![[19, 55, 123, 38, 69], [88, 119, 80, 72, 99], [100, 115, 17, 94, 93], [75, 45, 55, 44, 36], [13, 98, 0, 39, 134], [96, 69, 28, 12, 118], [26, 72, 63, 83, 63], [16, 29, 112, 74, 109]], ![[38, 112, 51, 55, 14], [7, 116, 20, 134, 107], [52, 76, 89, 53, 67], [33, 8, 97, 65, 119], [25, 3, 28, 131, 39], [38, 113, 36, 99, 42], [94, 126, 46, 87, 6], [19, 55, 123, 38, 69]], ![[0, 1], [15, 75, 80, 52, 91], [65, 88, 41, 99, 26], [27, 115, 118, 16, 57], [51, 109, 54, 75, 23], [38, 69, 112, 59, 20], [75, 115, 14, 55, 96], [38, 112, 51, 55, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 36, 6, 50], [], [], []]
 b := ![[], [67, 30, 124, 73, 77], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 5
  hpos := by decide
  P := [43, 11, 33, 132, 62, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-128910991291762401, -154907630350823625, -8998189805666170, 55390762503897238, 340233623137140577]
  a := ![-1738, -1656, -145, 684, 4069]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-927417203537859, -1114443383818875, -64735178458030, 398494694272642, 2447723907461443]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7655, 4483, 449, -1810, -10408]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![7655, 4483, 449, -1810, -10408]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![138, 48, 122, 148, 1]] where
  M :=![![![7655, 4483, 449, -1810, -10408], ![16276, 9451, 858, -4074, -23044], ![47348, 31032, 2287, -13684, -77504], ![54410, 31506, 1890, -16171, -87980], ![3374, 2236, 344, -506, -3517]]]
  hmulB := by decide  
  f := ![![![-341, -179, -43, 100, 628]], ![![584, 1043, 162, -394, -2276]], ![![3252, 684, 287, -644, -4320]], ![![-7366, -7032, -1308, 3117, 18724]], ![![-4772, -6244, -1050, 2530, 14883]]]
  g := ![![![9691, 3383, 8525, 10326, -10408], ![21452, 7487, 18874, 22862, -23044], ![72100, 25176, 63475, 76892, -77504], ![81850, 28554, 72050, 87281, -87980], ![3280, 1148, 2882, 3490, -3517]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [143, 145, 146, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 38, 24, 113], [135, 64, 49, 78], [59, 46, 76, 107], [0, 1]]
 g := ![![[15, 29, 133, 73], [129, 64, 143], [127, 112, 74, 68], [132], [109, 145, 3, 47], [1], []], ![[31, 127, 77, 43, 103, 39], [37, 18, 24], [23, 82, 146, 136, 40, 116], [115, 117, 9], [62, 27, 70, 114, 131, 61], [36, 55, 42], [114, 94, 104]], ![[90, 51, 87, 47, 69, 87], [91, 8, 140], [64, 51, 7, 77, 140, 78], [43, 86, 5], [79, 47, 65, 64, 111, 108], [130, 38, 17], [75, 97, 124]], ![[98, 78, 124, 29, 123, 130], [70, 57, 73], [87, 57, 39, 4, 111, 17], [8, 43, 53], [105, 28, 104, 49, 45, 100], [22, 33, 54], [92, 61, 125]]]
 h' := ![![[90, 38, 24, 113], [20, 107, 94, 64], [17, 95, 35, 21], [133, 48, 25, 98], [58, 1, 79], [6, 4, 3, 135], [0, 0, 1], [0, 1]], ![[135, 64, 49, 78], [141, 72, 34, 43], [98, 69, 70, 60], [70, 53, 33, 19], [42, 95, 115, 3], [116, 98, 60, 82], [142, 112, 103, 108], [90, 38, 24, 113]], ![[59, 46, 76, 107], [94, 79, 21, 40], [137, 107, 21, 132], [56, 109, 20, 1], [120, 141, 12, 81], [2, 42, 144, 99], [50, 133, 58, 100], [135, 64, 49, 78]], ![[0, 1], [91, 40, 0, 2], [72, 27, 23, 85], [68, 88, 71, 31], [13, 61, 92, 65], [83, 5, 91, 131], [10, 53, 136, 90], [59, 46, 76, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [97, 83, 40], []]
 b := ![[], [], [118, 42, 104, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [143, 145, 146, 14, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4839464765493, -5374880856942, -308274901098, 1991041950668, 12075746087720]
  a := ![-1061, -1010, -91, 418, 2484]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11216727683697, -3926246262198, -9889592601362, -11981338114308, 12075746087720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-341, -179, -43, 100, 628]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-341, -179, -43, 100, 628]] 
 ![![149, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![123, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![126, 0, 0, 0, 1]] where
  M :=![![![-341, -179, -43, 100, 628], ![584, 1043, 162, -394, -2276], ![3252, 684, 287, -644, -4320], ![-7366, -7032, -1308, 3117, 18724], ![1422, 1570, 278, -666, -3961]]]
  hmulB := by decide  
  f := ![![![7655, 4483, 449, -1810, -10408]], ![![1034, 605, 60, -246, -1412]], ![![6637, 3909, 386, -1586, -9112]], ![![5400, 3160, 308, -1299, -7436]], ![![6496, 3806, 382, -1534, -8825]]]
  g := ![![![-542, -179, -43, 100, 628], ![1928, 1043, 162, -394, -2276], ![3779, 684, 287, -644, -4320], ![-16004, -7032, -1308, 3117, 18724], ![3378, 1570, 278, -666, -3961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![7655, 4483, 449, -1810, -10408]] ![![-341, -179, -43, 100, 628]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3875, -2268, -245, 869, 5064]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-3875, -2268, -245, 869, 5064]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![64, 150, 65, 1, 0], ![28, 130, 77, 0, 1]] where
  M :=![![![-3875, -2268, -245, 869, 5064], ![-5938, -2861, -356, 1160, 6574], ![-13128, -9786, -895, 3534, 21222], ![3282, 9183, 435, -2761, -18282], ![-5218, -4179, -365, 1484, 8987]]]
  hmulB := by decide  
  f := ![![![127, 105, 22, -49, -300]], ![![-70, -335, -38, 110, 598]], ![![-1956, -1146, -229, 606, 3714]], ![![-848, -765, -124, 343, 2028]], ![![-1036, -857, -146, 396, 2361]]]
  g := ![![![-1333, -5238, -2958, 869, 5064], ![-1750, -6831, -3854, 1160, 6574], ![-5520, -21846, -12349, 3534, 21222], ![4582, 18543, 10514, -2761, -18282], ![-2330, -9239, -5224, 1484, 8987]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [13, 97, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 72, 115], [50, 78, 36], [0, 1]]
 g := ![![[45, 124, 34], [128, 91, 81], [55, 27, 74], [109, 95], [23, 3, 138], [69, 1], []], ![[6, 112, 61, 51], [68, 106, 58, 26], [7, 48, 117, 53], [105, 123], [55, 122], [96, 44], [133, 88]], ![[79, 103, 49, 36], [6, 45, 81, 125], [95, 78, 48, 68], [1, 58], [77, 80, 125, 136], [89, 50], [61, 88]]]
 h' := ![![[19, 72, 115], [148, 81, 100], [40, 37, 142], [102, 124, 136], [3, 76, 47], [9, 89, 134], [0, 0, 1], [0, 1]], ![[50, 78, 36], [32, 33, 52], [69, 104, 80], [26, 81, 104], [118, 33, 24], [41, 96], [142, 16, 78], [19, 72, 115]], ![[0, 1], [40, 37, 150], [117, 10, 80], [25, 97, 62], [76, 42, 80], [53, 117, 17], [46, 135, 72], [50, 78, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 84], []]
 b := ![[], [73, 115, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [13, 97, 82, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3265215891, -3136414824, -181675302, 1245076498, 7389771724]
  a := ![-1099, -1047, -93, 435, 2573]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1919627285, -7619657044, -4305457420, 1245076498, 7389771724]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-389, -332, -28, 116, 708]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-389, -332, -28, 116, 708]] 
 ![![151, 0, 0, 0, 0], ![53, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![41, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![-389, -332, -28, 116, 708], ![104, 643, 24, -188, -1268], ![-3544, -4944, -317, 1588, 10132], ![8640, 13920, 816, -4433, -28476], ![-1800, -2552, -160, 824, 5251]]]
  hmulB := by decide  
  f := ![![![12085, 10484, 2020, -4796, -29004]], ![![4263, 3527, 692, -1640, -9952]], ![![3820, 3552, 667, -1588, -9556]], ![![4331, 4492, 812, -1941, -11592]], ![![9207, 7796, 1516, -3596, -21785]]]
  g := ![![![-455, -332, -28, 116, 708], ![799, 643, 24, -188, -1268], ![-6444, -4944, -317, 1588, 10132], ![18115, 13920, 816, -4433, -28476], ![-3345, -2552, -160, 824, 5251]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6289, -10075, -597, 3198, 20562]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-6289, -10075, -597, 3198, 20562]] 
 ![![151, 0, 0, 0, 0], ![120, 1, 0, 0, 0], ![96, 0, 1, 0, 0], ![81, 0, 0, 1, 0], ![128, 0, 0, 0, 1]] where
  M :=![![![-6289, -10075, -597, 3198, 20562], ![32076, 51371, 3044, -16308, -104850], ![-163440, -261828, -15515, 83110, 534366], ![498494, 798408, 47310, -253453, -1629554], ![-84838, -135886, -8052, 43136, 277341]]]
  hmulB := by decide  
  f := ![![![-5543, -2567, -275, 1032, 6034]], ![![-4448, -2065, -220, 828, 4838]], ![![-3664, -1752, -191, 702, 4102]], ![![-3083, -1383, -153, 567, 3332]], ![![-4718, -2196, -234, 880, 5141]]]
  g := ![![![-10801, -10075, -597, 3198, 20562], ![55080, 51371, 3044, -16308, -104850], ![-280698, -261828, -15515, 83110, 534366], ![856029, 798408, 47310, -253453, -1629554], ![-145690, -135886, -8052, 43136, 277341]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-3875, -2268, -245, 869, 5064]] ![![-389, -332, -28, 116, 708]]
  ![![532743, 212608, 30597, -91717, -504596]] where
 M := ![![![532743, 212608, 30597, -91717, -504596]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![532743, 212608, 30597, -91717, -504596]] ![![-6289, -10075, -597, 3198, 20562]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-4443038949, -7116705953, -421705552, 2259113265, 14524954250]]]
 hmul := by decide  
 g := ![![![![-29424099, -47130503, -2792752, 14961015, 96191750]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)


lemma PB953I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB953I3 : PrimesBelowBoundCertificateInterval O 103 151 953 where
  m := 9
  g := ![2, 3, 2, 3, 2, 2, 1, 2, 3]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB953I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1]
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
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
    · exact ![131079601, 107]
    · exact ![11881, 11881, 109]
    · exact ![163047361, 113]
    · exact ![16129, 16129, 127]
    · exact ![294499921, 131]
    · exact ![352275361, 137]
    · exact ![51888844699]
    · exact ![492884401, 149]
    · exact ![3442951, 151, 151]
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
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
      exact NI151N2
  β := ![I107N1, I109N2, I113N1, I127N2, I131N1, I137N1, I149N1, I151N1, I151N2]
  Il := ![[I107N1], [I109N2], [I113N1], [I127N2], [I131N1], [I137N1], [], [I149N1], [I151N1, I151N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
