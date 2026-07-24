
import IdealArithmetic.Examples.NF5_1_48600000_5.RI5_1_48600000_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -290, 60, 32, -300]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-39, -290, 60, 32, -300]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![129, 143, 10, 1, 0], ![50, 101, 116, 0, 1]] where
  M :=![![![-39, -290, 60, 32, -300], ![536, 1585, -1116, 184, 792], ![-976, -2086, 2561, -932, -240], ![904, -332, -2700, 1537, -2952], ![304, 2854, -144, -640, 3221]]]
  hmulB := by decide  
  f := ![![![899445, -198326, -52884, 42848, 167868]], ![![-421432, 92917, 24780, -20072, -78648]], ![![98720, -21778, -5803, 4708, 18432]], ![![362665, -79975, -21322, 17281, 67692]], ![![90378, -19941, -5312, 4312, 16877]]]
  g := ![![![69, 162, 220, 32, -300], ![-400, -667, -604, 184, 792], ![836, 990, 253, -932, -240], ![-317, 497, 2066, 1537, -2952], ![-498, -1471, -2340, -640, 3221]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [135, 28, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 132, 127], [139, 24, 30], [0, 1]]
 g := ![![[65, 31, 11], [6, 75], [119, 30, 46], [151, 86, 109], [50, 25, 101], [156, 1], []], ![[57, 31, 75, 33], [98, 10], [63, 83, 67, 49], [18, 60, 141, 153], [19, 60, 100, 46], [103, 105], [129, 115]], ![[127, 155, 142, 3], [12, 156], [23, 15, 84, 113], [155, 36, 82, 120], [118, 10, 95, 13], [115, 154], [69, 115]]]
 h' := ![![[17, 132, 127], [64, 53, 110], [106, 151, 111], [25, 20, 49], [1, 105, 57], [135, 50, 130], [0, 0, 1], [0, 1]], ![[139, 24, 30], [6, 146, 108], [131, 3, 18], [42, 131, 105], [103, 134, 102], [80, 46, 50], [144, 109, 24], [17, 132, 127]], ![[0, 1], [142, 115, 96], [105, 3, 28], [119, 6, 3], [113, 75, 155], [55, 61, 134], [115, 48, 132], [139, 24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136, 17], []]
 b := ![[], [56, 133, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [135, 28, 1, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![175727, 115894, -29216, -137022, -243792]
  a := ![5, -7, -8, -8, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![191345, 282376, 188668, -137022, -243792]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-899445, 198326, 52884, -42848, -167868]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-899445, 198326, 52884, -42848, -167868]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![67, 147, 1, 0, 0], ![42, 91, 0, 1, 0], ![129, 22, 0, 0, 1]] where
  M :=![![![-899445, 198326, 52884, -42848, -167868], ![421432, -92917, -24780, 20072, 78648], ![-98720, 21778, 5803, -4708, -18432], ![-187576, 41372, 11028, -8941, -35016], ![-330208, 72806, 19416, -15728, -61625]]]
  hmulB := by decide  
  f := ![![![39, 290, -60, -32, 300]], ![![-536, -1585, 1116, -184, -792]], ![![-479, -1347, 1003, -180, -612]], ![![-306, -839, 648, -125, -360]], ![![-45, -2, 108, -48, 115]]]
  g := ![![![121095, 106, 52884, -42848, -167868], ![-56732, -45, -24780, 20072, 78648], ![13299, 17, 5803, -4708, -18432], ![25262, 27, 11028, -8941, -35016], ![44453, 36, 19416, -15728, -61625]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [97, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 156], [0, 1]]
 g := ![![[61, 146], [141], [37, 46], [13, 145], [50, 115], [46], [1]], ![[150, 11], [141], [93, 111], [53, 12], [33, 42], [46], [1]]]
 h' := ![![[49, 156], [152, 97], [22, 45], [152, 49], [17, 50], [80, 127], [60, 49], [0, 1]], ![[0, 1], [38, 60], [29, 112], [41, 108], [112, 107], [23, 30], [106, 108], [49, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [116, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [97, 108, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11, 55188, -52543, 56071, 60417]
  a := ![-6, -56, 11, -57, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-42219, 8582, -52543, 56071, 60417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-39, -290, 60, 32, -300]] ![![-899445, 198326, 52884, -42848, -167868]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![-157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![503, 85, -58, -76, -48]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![503, 85, -58, -76, -48]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![106, 16, 1, 0, 0], ![97, 42, 0, 1, 0], ![78, 72, 0, 0, 1]] where
  M :=![![![503, 85, -58, -76, -48], ![248, 533, -78, -268, -360], ![628, 717, -95, -346, -444], ![666, 764, -34, -307, -414], ![-106, -295, 64, 168, 221]]]
  hmulB := by decide  
  f := ![![![-211, -697, 452, -72, -408]], ![![960, 2137, -2354, 760, 384]], ![![-50, -249, 83, 18, -216]], ![![117, 97, -334, 161, -186]], ![![336, 657, -850, 304, 5]]]
  g := ![![![109, 47, -58, -76, -48], ![384, 239, -78, -268, -360], ![484, 299, -95, -346, -444], ![407, 270, -34, -307, -414], ![-248, -149, 64, 168, 221]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [107, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 162], [0, 1]]
 g := ![![[97, 144], [158, 62], [62], [1], [56], [126, 38], [1]], ![[68, 19], [21, 101], [62], [1], [56], [21, 125], [1]]]
 h' := ![![[53, 162], [46, 12], [37, 15], [71, 148], [129, 1], [47, 43], [56, 53], [0, 1]], ![[0, 1], [30, 151], [17, 148], [91, 15], [19, 162], [44, 120], [94, 110], [53, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [17, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [107, 110, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99, -524, 9, -181, 291]
  a := ![1, -4, -1, -5, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-38, -86, 9, -181, 291]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-555, -1742, 1210, -224, -946]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-555, -1742, 1210, -224, -946]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![71, 7, 1, 0, 0], ![155, 150, 0, 1, 0], ![69, 140, 0, 0, 1]] where
  M :=![![![-555, -1742, 1210, -224, -946], ![2340, 4937, -5824, 1972, 548], ![-2520, -1140, 7457, -3852, 5368], ![-2686, -17272, 3288, 2619, -17198], ![5630, 19216, -11854, 1648, 11797]]]
  hmulB := by decide  
  f := ![![![-23140805, 5102466, 1360598, -1102368, -4318858]], ![![10842452, -2390653, -637520, 516460, 2023508]], ![![-9629693, 2123317, 566191, -458736, -1797230]], ![![-12056951, 2658580, 708886, -574405, -2250292]], ![![-535385, 118110, 31460, -25544, -99973]]]
  g := ![![![83, 956, 1210, -224, -946], ![444, -2005, -5824, 1972, 548], ![-1873, -1393, 7457, -3852, 5368], ![3341, 12114, 3288, 2619, -17198], ![-1363, -11022, -11854, 1648, 11797]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [144, 156, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 162], [0, 1]]
 g := ![![[69, 60], [35, 158], [85], [100], [6], [120, 49], [1]], ![[0, 103], [0, 5], [85], [100], [6], [137, 114], [1]]]
 h' := ![![[7, 162], [13, 68], [154, 141], [13, 133], [118, 153], [161, 13], [19, 7], [0, 1]], ![[0, 1], [0, 95], [0, 22], [129, 30], [48, 10], [89, 150], [68, 156], [7, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [47, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [144, 156, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16297, -8356, 13893, 15732, 19122]
  a := ![-8, 27, 13, 26, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29206, -31549, 13893, 15732, 19122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54663, 12053, 3214, -2604, -10202]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![-54663, 12053, 3214, -2604, -10202]] 
 ![![163, 0, 0, 0, 0], ![117, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![139, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![-54663, 12053, 3214, -2604, -10202], ![25612, -5647, -1506, 1220, 4780], ![-6000, 1323, 353, -286, -1120], ![-11400, 2514, 670, -543, -2128], ![-20068, 4425, 1180, -956, -3745]]]
  hmulB := by decide  
  f := ![![![-209, -157, 188, 216, 190]], ![![-155, -116, 138, 160, 142]], ![![-117, -90, 103, 118, 106]], ![![-193, -149, 166, 197, 174]], ![![-105, -78, 94, 108, 97]]]
  g := ![![![-3208, 12053, 3214, -2604, -10202], ![1503, -5647, -1506, 1220, 4780], ![-352, 1323, 353, -286, -1120], ![-669, 2514, 670, -543, -2128], ![-1178, 4425, 1180, -956, -3745]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![503, 85, -58, -76, -48]] ![![-555, -1742, 1210, -224, -946]]
  ![![-209, -157, 188, 216, 190]] where
 M := ![![![-209, -157, 188, 216, 190]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![-209, -157, 188, 216, 190]] ![![-54663, 12053, 3214, -2604, -10202]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1841, -162, -5750, 3242, -5344]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![1841, -162, -5750, 3242, -5344]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![155, 99, 1, 0, 0], ![19, 130, 0, 1, 0], ![72, 7, 0, 0, 1]] where
  M :=![![![1841, -162, -5750, 3242, -5344], ![4204, 29295, -4528, -5016, 30140], ![-25124, -80528, 54419, -9544, -45188], ![52630, 103426, -132996, 47383, 1486], ![-26246, -16290, 76550, -38398, 49627]]]
  hmulB := by decide  
  f := ![![![2575222971, -567825650, -151414778, 122675558, 480622036]], ![![-1206595188, 266049129, 70943888, -57478440, -225190724]], ![![1676582671, -369679277, -98577639, 79867134, 312905924]], ![![-643060247, 141792074, 37809858, -30633395, -120016402]], ![![1065361106, -234907565, -62639786, 50750466, 198831723]]]
  g := ![![![7283, 1108, -5750, 3242, -5344], ![-8196, 5501, -4528, -5016, 30140], ![-30091, -23419, 54419, -9544, -45188], ![117723, 42514, -132996, 47383, 1486], ![-88234, -17667, 76550, -38398, 49627]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [106, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 166], [0, 1]]
 g := ![![[3, 48], [60, 99], [20, 93], [21], [97], [36, 89], [1]], ![[103, 119], [141, 68], [5, 74], [21], [97], [124, 78], [1]]]
 h' := ![![[16, 166], [153, 81], [51, 44], [118, 107], [29, 45], [25, 40], [61, 16], [0, 1]], ![[0, 1], [113, 86], [87, 123], [160, 60], [81, 122], [164, 127], [150, 151], [16, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [151, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [106, 151, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-410, -6387, -3710, 3134, -7528]
  a := ![10, -9, -15, -7, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6330, 37, -3710, 3134, -7528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3670, 281, -5876, -5430, -4965]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![3670, 281, -5876, -5430, -4965]] 
 ![![167, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![106, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![3670, 281, -5876, -5430, -4965], ![20790, 11759, -20228, -22612, -22650], ![45262, 34294, -33503, -42840, -45186], ![77631, 70125, -43618, -65037, -72009], ![-989, 5365, 8184, 5468, 3926]]]
  hmulB := by decide  
  f := ![![![140860, 447951, -306236, 55088, 248271]], ![![10706, 37836, -22176, 2600, 24279]], ![![93410, 286488, -206143, 40956, 149556]], ![![11447, 50204, -20882, -1303, 39876]], ![![96899, 305776, -211352, 38890, 167399]]]
  g := ![![![7732, 281, -5876, -5430, -4965], ![29939, 11759, -20228, -22612, -22650], ![54176, 34294, -33503, -42840, -45186], ![78416, 70125, -43618, -65037, -72009], ![-8980, 5365, 8184, 5468, 3926]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0, -2, -3]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![2, 1, 0, -2, -3]] 
 ![![167, 0, 0, 0, 0], ![132, 1, 0, 0, 0], ![139, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![2, 1, 0, -2, -3], ![10, 13, -8, -4, -6], ![10, 12, 3, -12, -6], ![13, 3, -2, -7, -27], ![1, 13, -8, 4, 14]]]
  hmulB := by decide  
  f := ![![![10932, -2421, -640, 528, 2049]], ![![8610, -1907, -504, 416, 1614]], ![![9106, -2017, -533, 440, 1707]], ![![7345, -1627, -430, 355, 1377]], ![![5261, -1165, -308, 254, 986]]]
  g := ![![![2, 1, 0, -2, -3], ![2, 13, -8, -4, -6], ![-1, 12, 3, -12, -6], ![17, 3, -2, -7, -27], ![-13, 13, -8, 4, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2

def I167N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![14, 2, -6, -6, -5]] i)))

def SI167N3: IdealEqSpanCertificate' Table ![![14, 2, -6, -6, -5]] 
 ![![167, 0, 0, 0, 0], ![154, 1, 0, 0, 0], ![166, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![60, 0, 0, 0, 1]] where
  M :=![![![14, 2, -6, -6, -5], ![22, 21, -18, -24, -26], ![50, 43, -29, -42, -46], ![77, 73, -36, -59, -67], ![-3, -2, 8, 8, 8]]]
  hmulB := by decide  
  f := ![![![-12, -126, 44, 8, -97]], ![![-10, -113, 38, 8, -88]], ![![-14, -129, 49, 6, -96]], ![![1, -3, -4, 3, -7]], ![![-3, -38, 14, 2, -28]]]
  g := ![![![6, 2, -6, -6, -5], ![8, 21, -18, -24, -26], ![6, 43, -29, -42, -46], ![-7, 73, -36, -59, -67], ![-9, -2, 8, 8, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N3 : Nat.card (O ⧸ I167N3) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N3)

lemma isPrimeI167N3 : Ideal.IsPrime I167N3 := prime_ideal_of_norm_prime hp167.out _ NI167N3
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![1841, -162, -5750, 3242, -5344]] ![![3670, 281, -5876, -5430, -4965]]
  ![![96908, 96553, -43382, -74432, -85487]] where
 M := ![![![96908, 96553, -43382, -74432, -85487]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![96908, 96553, -43382, -74432, -85487]] ![![2, 1, 0, -2, -3]]
  ![![-327577, -503114, -69810, 119632, 203096]] where
 M := ![![![-327577, -503114, -69810, 119632, 203096]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI167N2 : IdealMulLeCertificate' Table 
  ![![-327577, -503114, -69810, 119632, 203096]] ![![14, 2, -6, -6, -5]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![-10542710, -5895434, 10364020, 11538698, 11539533]]]
 hmul := by decide  
 g := ![![![![-63130, -35302, 62060, 69094, 69099]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2, I167N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
    exact isPrimeI167N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1 ⊙ MulI167N2)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -4, 16, 16, 15]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-14, -4, 16, 16, 15]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![29, 13, 1, 0, 0], ![142, 19, 0, 1, 0], ![105, 104, 0, 0, 1]] where
  M :=![![![-14, -4, 16, 16, 15], ![-62, -41, 54, 64, 66], ![-130, -105, 89, 118, 126], ![-213, -197, 112, 175, 195], ![7, -8, -22, -18, -14]]]
  hmulB := by decide  
  f := ![![![-100, 8, 14, -6, -27]], ![![66, 37, -50, 16, 18]], ![![-12, 4, -1, 0, -3]], ![![-75, 10, 6, -3, -21]], ![![-21, 28, -22, 6, -5]]]
  g := ![![![-25, -12, 16, 16, 15], ![-102, -51, 54, 64, 66], ![-189, -96, 89, 118, 126], ![-282, -146, 112, 175, 195], ![27, 12, -22, -18, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [98, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 172], [0, 1]]
 g := ![![[72, 38], [122], [26, 15], [156, 158], [41], [151, 158], [1]], ![[94, 135], [122], [62, 158], [120, 15], [41], [115, 15], [1]]]
 h' := ![![[37, 172], [114, 111], [47, 128], [109, 19], [133, 136], [80, 53], [75, 37], [0, 1]], ![[0, 1], [69, 62], [112, 45], [120, 154], [148, 37], [138, 120], [60, 136], [37, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [110, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [98, 136, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3390, 7008, -10452, 3844, 1164]
  a := ![-6, -4, 10, -14, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2090, -296, -10452, 3844, 1164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46, -133, 118, -40, -57]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-46, -133, 118, -40, -57]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![163, 61, 1, 0, 0], ![91, 167, 0, 1, 0], ![68, 148, 0, 0, 1]] where
  M :=![![![-46, -133, 118, -40, -57], ![194, 277, -460, 156, -126], ![-30, 338, 307, -304, 594], ![-387, -1789, 858, -75, -1443], ![565, 1603, -1298, 322, 712]]]
  hmulB := by decide  
  f := ![![![18823252, -4150449, -1106746, 896682, 3513045]], ![![-8819454, 1944645, 518556, -420128, -1645998]], ![![14637396, -3227488, -860631, 697282, 2731827]], ![![1410363, -310987, -82924, 67189, 263226]], ![![-106287, 23429, 6250, -5060, -19832]]]
  g := ![![![-68, 45, 118, -40, -57], ![402, 121, -460, 156, -126], ![-363, -321, 307, -304, 594], ![-204, 994, 858, -75, -1443], ![777, -453, -1298, 322, 712]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P1 : CertificateIrreducibleZModOfList' 173 2 2 7 [112, 157, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 172], [0, 1]]
 g := ![![[74, 35], [138], [39, 38], [35, 92], [138], [166, 83], [1]], ![[115, 138], [138], [128, 135], [123, 81], [138], [110, 90], [1]]]
 h' := ![![[16, 172], [60, 143], [130, 22], [59, 111], [101, 28], [92, 22], [61, 16], [0, 1]], ![[0, 1], [99, 30], [136, 151], [105, 62], [30, 145], [98, 151], [144, 157], [16, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [72, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N1 : CertifiedPrimeIdeal' SI173N1 173 where
  n := 2
  hpos := by decide
  P := [112, 157, 1]
  hirr := P173P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12277, -9819, 11140, 11614, 12331]
  a := ![-6, 19, 16, 20, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-21523, -25745, 11140, 11614, 12331]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N1 B_one_repr
lemma NI173N1 : Nat.card (O ⧸ I173N1) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5964, -7095, 1258, 3720, 4701]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![-5964, -7095, 1258, 3720, 4701]] 
 ![![173, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![120, 0, 1, 0, 0], ![131, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  M :=![![![-5964, -7095, 1258, 3720, 4701], ![-16842, -20771, 2652, 9956, 12918], ![-22874, -29434, 2103, 12608, 16950], ![-21137, -29767, -1202, 9733, 14415], ![10247, 11801, -2638, -6682, -8266]]]
  hmulB := by decide  
  f := ![![![5422, 1877, -3510, 1298, 1083]], ![![756, 266, -458, 162, 189]], ![![3754, 1206, -2433, 924, 642]], ![![4205, 1718, -2864, 1021, 984]], ![![705, 68, -296, 122, 113]]]
  g := ![![![-3378, -7095, 1258, 3720, 4701], ![-8341, -20771, 2652, 9956, 12918], ![-9334, -29434, 2103, 12608, 16950], ![-4440, -29767, -1202, 9733, 14415], ![6438, 11801, -2638, -6682, -8266]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-14, -4, 16, 16, 15]] ![![-46, -133, 118, -40, -57]]
  ![![1671, 1583, -642, -1298, -1602]] where
 M := ![![![1671, 1583, -642, -1298, -1602]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![1671, 1583, -642, -1298, -1602]] ![![-5964, -7095, 1258, 3720, 4701]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-10921490, -6107246, 10736380, 11953262, 11954127]]]
 hmul := by decide  
 g := ![![![![-63130, -35302, 62060, 69094, 69099]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5617, 7550, -616, -3516, -5646]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-5617, 7550, -616, -3516, -5646]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![85, 114, 99, 1, 0], ![90, 169, 20, 0, 1]] where
  M :=![![![-5617, 7550, -616, -3516, -5646], ![18324, 14965, -3224, -8264, -9804], ![18068, 23796, -3103, -11488, -14988], ![17314, 25982, -1068, -10459, -14574], ![-11430, -7698, 2576, 5056, 5639]]]
  hmulB := by decide  
  f := ![![![-3263, -8218, 7720, -2180, -2670]], ![![9700, 13447, -26136, 11080, -7740]], ![![-3340, 22212, 16787, -15056, 40980]], ![![2609, 16290, -3353, -2327, 16008]], ![![7344, 11587, -19380, 7800, -3853]]]
  g := ![![![4477, 7612, 2572, -3516, -5646], ![8956, 14603, 5648, -8264, -9804], ![13092, 21600, 8011, -11488, -14988], ![12391, 20566, 7407, -10459, -14574], ![-5300, -8587, -3412, 5056, 5639]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [49, 125, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 88, 19], [28, 90, 160], [0, 1]]
 g := ![![[138, 107, 22], [45, 108, 156], [149, 117], [134, 47], [72, 20, 158], [24, 68, 1], []], ![[60, 0, 65, 75], [67, 173, 18, 70], [1, 75], [19, 56], [49, 145, 31, 51], [104, 112, 30, 139], [147, 3]], ![[21, 121, 8, 34], [55, 170, 97, 84], [53, 9], [136, 147], [52, 41, 52, 162], [122, 108, 120, 2], [6, 3]]]
 h' := ![![[40, 88, 19], [122, 59, 102], [86, 87, 131], [76, 162, 98], [52, 66, 88], [77, 112, 64], [0, 0, 1], [0, 1]], ![[28, 90, 160], [17, 34, 98], [72, 133, 18], [11, 73, 84], [88, 119, 45], [27, 137, 12], [125, 153, 90], [40, 88, 19]], ![[0, 1], [23, 86, 158], [124, 138, 30], [6, 123, 176], [91, 173, 46], [26, 109, 103], [132, 26, 88], [28, 90, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 81], []]
 b := ![[], [8, 164, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [49, 125, 111, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7024, -53056, 2929, 21650, -61206]
  a := ![-2, -3, 3, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![20454, 43702, -5119, 21650, -61206]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3402, -750, -200, 162, 635]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![3402, -750, -200, 162, 635]] 
 ![![179, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![121, 0, 1, 0, 0], ![70, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![3402, -750, -200, 162, 635], ![-1594, 351, 94, -76, -298], ![374, -81, -23, 18, 70], ![709, -157, -40, 33, 133], ![1249, -276, -74, 60, 232]]]
  hmulB := by decide  
  f := ![![![-144, -30, 194, 192, 187]], ![![-34, -9, 44, 44, 43]], ![![-106, -27, 137, 138, 135]], ![![-71, -25, 84, 87, 87]], ![![-23, -6, 30, 30, 29]]]
  g := ![![![143, -750, -200, 162, 635], ![-67, 351, 94, -76, -298], ![16, -81, -23, 18, 70], ![29, -157, -40, 33, 133], ![53, -276, -74, 60, 232]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1714, -3632, 4254, -1432, -425]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-1714, -3632, 4254, -1432, -425]] 
 ![![179, 0, 0, 0, 0], ![123, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![158, 0, 0, 1, 0], ![173, 0, 0, 0, 1]] where
  M :=![![![-1714, -3632, 4254, -1432, -425], ![3714, 1801, -10978, 5644, -7742], ![2098, 21367, -297, -5334, 24674], ![-21197, -67019, 46196, -8453, -36805], ![19643, 45426, -47648, 14818, 10298]]]
  hmulB := by decide  
  f := ![![![40918816, -9023004, -2405712, 1949630, 7637315]], ![![28010282, -6176557, -1646786, 1334594, 5228005]], ![![9854738, -2173085, -579379, 469552, 1839357]], ![![36165943, -7974971, -2126276, 1723185, 6750229]], ![![39631163, -8739058, -2330010, 1888274, 7396975]]]
  g := ![![![3139, -3632, 4254, -1432, -425], ![3921, 1801, -10978, 5644, -7742], ![-33738, 21367, -297, -5334, 24674], ![77869, -67019, 46196, -8453, -36805], ![-42691, 45426, -47648, 14818, 10298]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-5617, 7550, -616, -3516, -5646]] ![![3402, -750, -200, 162, 635]]
  ![![-40918816, 9023004, 2405712, -1949630, -7637315]] where
 M := ![![![-40918816, 9023004, 2405712, -1949630, -7637315]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-40918816, 9023004, 2405712, -1949630, -7637315]] ![![-1714, -3632, 4254, -1432, -425]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-179, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0, 0, 0]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]] where
  M :=![![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![0, 0, 0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 5 2 7 [57, 130, 123, 43, 163, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 71, 163, 76, 21], [162, 38, 0, 142, 161], [34, 15, 22, 112, 35], [12, 56, 177, 32, 145], [0, 1]]
 g := ![![[124, 66, 89, 123, 108], [65, 31, 133, 4], [15, 158, 9, 66, 3], [68, 153, 11, 1], [42, 51, 147, 121, 143], [1], []], ![[23, 174, 60, 133, 60, 175, 74, 68], [50, 73, 66, 27], [44, 45, 63, 66, 58, 177, 137, 124], [66, 10, 68, 143], [49, 129, 56, 139, 68, 95, 151, 97], [90, 102, 4, 55, 31, 177, 17, 26], [45, 148, 89, 79]], ![[126, 60, 151, 98, 106, 135, 46, 142], [95, 159, 59, 154], [139, 112, 180, 87, 102, 107, 152, 145], [13, 149, 75, 121], [151, 75, 126, 87, 56, 19, 167, 108], [138, 50, 96, 37, 114, 157, 132, 65], [58, 97, 72, 38]], ![[50, 6, 140, 75, 31, 44, 27, 151], [58, 26, 152, 121], [40, 47, 5, 128, 108, 91, 93, 107], [49, 168, 90, 56], [133, 66, 141, 100, 26, 159, 66, 32], [55, 156, 148, 47, 91, 131, 145, 30], [109, 50, 25, 139]], ![[28, 90, 116, 147, 38, 26, 108, 106], [6, 99, 15, 4], [55, 46, 178, 177, 157, 75, 18, 27], [1, 152, 112, 1], [21, 11, 98, 39, 139, 49, 168, 166], [88, 15, 120, 108, 72, 117, 167, 82], [97, 26, 28, 29]]]
 h' := ![![[172, 71, 163, 76, 21], [62, 141, 84, 5, 17], [50, 71, 94, 30, 179], [158, 114, 49, 115, 148], [140, 131, 75, 94, 180], [124, 51, 58, 138, 18], [0, 0, 1], [0, 1]], ![[162, 38, 0, 142, 161], [92, 51, 164, 52, 23], [74, 180, 175, 46, 82], [112, 71, 90, 146, 174], [39, 37, 161, 140, 163], [63, 173, 114, 83, 38], [50, 2, 133, 46, 76], [172, 71, 163, 76, 21]], ![[34, 15, 22, 112, 35], [102, 55, 45, 54, 83], [102, 52, 131, 130, 110], [39, 170, 127, 70, 20], [31, 94, 147, 38, 170], [91, 133, 39, 54, 130], [132, 148, 40, 147, 59], [162, 38, 0, 142, 161]], ![[12, 56, 177, 32, 145], [162, 71, 180, 10, 176], [36, 164, 21, 125, 170], [48, 15, 90, 135, 159], [137, 158, 136, 137, 31], [74, 154, 153, 175, 53], [11, 109, 118, 22, 95], [34, 15, 22, 112, 35]], ![[0, 1], [155, 44, 70, 60, 63], [139, 76, 122, 31, 2], [22, 173, 6, 77, 42], [21, 123, 24, 134, 180], [98, 32, 179, 93, 123], [45, 103, 70, 147, 132], [12, 56, 177, 32, 145]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 71, 78, 95], [], [], []]
 b := ![[], [64, 56, 111, 12, 142], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 5
  hpos := by decide
  P := [57, 130, 123, 43, 163, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-127103158495, -342660069636, 279991163224, -67148007708, -136674331524]
  a := ![-10, 9, 20, 5, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-702227395, -1893149556, 1546912504, -370983468, -755106804]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 194264244901 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![72677, -21171, -19998, -9026, 2740]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![72677, -21171, -19998, -9026, 2740]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![44, 84, 15, 1, 0], ![147, 167, 12, 0, 1]] where
  M :=![![![72677, -21171, -19998, -9026, 2740], ![12572, 20927, -54914, -58048, -59636], ![117684, 69871, -96757, -112962, -114508], ![221184, 173308, -130142, -180695, -194560], ![32164, 21983, 19956, 10614, 7973]]]
  hmulB := by decide  
  f := ![![![-37745, -209089, 56220, 22534, -193648]], ![![342228, 1031783, -760406, 157508, 522500]], ![![-680008, -1357831, 1711791, -602898, -49976]], ![![90932, 296463, -195571, 32507, 170680]], ![![228863, 666551, -515320, 115152, 315949]]]
  g := ![![![351, 1463, 432, -9026, 2740], ![59336, 77781, 8018, -58048, -59636], ![114768, 150165, 15559, -112962, -114508], ![192524, 250488, 25733, -180695, -194560], ![-8413, -11524, -1230, 10614, 7973]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [88, 68, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 173, 96], [110, 17, 95], [0, 1]]
 g := ![![[15, 103, 16], [119, 37, 96], [20, 1, 20], [148, 26, 136], [36, 31, 75], [17, 127, 1], []], ![[73, 139, 0, 3], [115, 46, 72, 102], [112, 175, 150, 2], [1, 24, 145, 149], [138, 139, 151, 23], [128, 2, 133, 49], [157, 48]], ![[1, 114, 152, 56], [41, 190, 4, 63], [104, 91, 73, 44], [102, 138, 57, 159], [175, 61, 28, 83], [40, 190, 188, 29], [158, 48]]]
 h' := ![![[17, 173, 96], [33, 74, 187], [150, 39, 67], [155, 1, 163], [79, 50, 30], [32, 83, 120], [0, 0, 1], [0, 1]], ![[110, 17, 95], [9, 169, 160], [35, 180, 108], [175, 175, 2], [39, 162, 153], [175, 80, 76], [34, 150, 17], [17, 173, 96]], ![[0, 1], [109, 139, 35], [82, 163, 16], [162, 15, 26], [164, 170, 8], [108, 28, 186], [106, 41, 173], [110, 17, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 176], []]
 b := ![[], [3, 118, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [88, 68, 64, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234360, -137341, 171693, 85896, 363189]
  a := ![-6, 7, 9, 6, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-300537, -356048, -28665, 85896, 363189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![87, 179, 74, 2, -32]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![87, 179, 74, 2, -32]] 
 ![![191, 0, 0, 0, 0], ![39, 1, 0, 0, 0], ![99, 0, 1, 0, 0], ![151, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![87, 179, 74, 2, -32], ![60, 325, 298, 152, 76], ![-228, 141, 553, 450, 380], ![-860, -500, 822, 927, 932], ![-248, -403, -80, 74, 143]]]
  hmulB := by decide  
  f := ![![![-2147, 225, 152, -54, -652]], ![![-431, 52, 26, -10, -128]], ![![-1119, 106, 91, -32, -340]], ![![-1695, 179, 106, -35, -528]], ![![-408, 55, 30, -14, -109]]]
  g := ![![![-70, 179, 74, 2, -32], ![-355, 325, 298, 152, 76], ![-744, 141, 553, 450, 380], ![-1237, -500, 822, 927, 932], ![37, -403, -80, 74, 143]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-460171, 101457, 27052, -21922, -85882]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-460171, 101457, 27052, -21922, -85882]] 
 ![![191, 0, 0, 0, 0], ![122, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![85, 0, 0, 1, 0], ![110, 0, 0, 0, 1]] where
  M :=![![![-460171, 101457, 27052, -21922, -85882], ![215608, -47553, -12694, 10260, 40232], ![-50492, 11137, 2939, -2434, -9452], ![-95918, 21196, 5598, -4625, -17966], ![-168926, 37269, 9938, -8050, -31535]]]
  hmulB := by decide  
  f := ![![![16659, 50623, -36902, 7502, 26002]], ![![10290, 31627, -22690, 4484, 16572]], ![![955, 1904, -2405, 848, 66]], ![![7903, 25319, -17128, 3013, 14196]], ![![8696, 26201, -19328, 4010, 13253]]]
  g := ![![![-8989, 101457, 27052, -21922, -85882], ![4232, -47553, -12694, 10260, 40232], ![-959, 11137, 2939, -2434, -9452], ![-1841, 21196, 5598, -4625, -17966], ![-3310, 37269, 9938, -8050, -31535]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![72677, -21171, -19998, -9026, 2740]] ![![87, 179, 74, 2, -32]]
  ![![16695023, 6717670, -19628326, -20236080, -19554312]] where
 M := ![![![16695023, 6717670, -19628326, -20236080, -19554312]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![16695023, 6717670, -19628326, -20236080, -19554312]] ![![-460171, 101457, 27052, -21922, -85882]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![1127431171, -1912685269, 1059680606, 1714427078, 2196913706]]]
 hmul := by decide  
 g := ![![![![5902781, -10014059, 5548066, 8976058, 11502166]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![862, 683, -582, -776, -829]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![862, 683, -582, -776, -829]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![100, 137, 61, 17, 1]] where
  M :=![![![862, 683, -582, -776, -829], ![3210, 2873, -1844, -2716, -2998], ![5714, 5462, -2841, -4560, -5150], ![8105, 8315, -3326, -6043, -7031], ![-1031, -681, 890, 1058, 1084]]]
  hmulB := by decide  
  f := ![![![16, 3, -6, 2, 5]], ![![-14, -11, 20, -8, 2]], ![![6, -10, -17, 12, -26]], ![![21, 77, -34, -1, 61]], ![![2, -3, 3, -1, 1]]]
  g := ![![![434, 592, 259, 69, -829], ![1570, 2143, 938, 250, -2998], ![2698, 3684, 1613, 430, -5150], ![3685, 5034, 2205, 588, -7031], ![-567, -773, -338, -90, 1084]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [151, 49, 71, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 179, 139, 106], [80, 69, 154, 155], [123, 137, 93, 125], [0, 1]]
 g := ![![[133, 106, 24, 12], [189, 104, 185], [153, 158, 147], [188, 97, 170], [145, 27, 165], [123, 192, 1], []], ![[26, 110, 127, 191, 151, 156], [152, 152, 124], [163, 67, 118], [129, 130, 121], [60, 78, 92], [108, 28, 75], [141, 125, 140, 0, 131, 13]], ![[67, 139, 54, 117, 113, 90], [75, 151, 134], [140, 6, 129], [94, 85, 54], [70, 55, 43], [155, 128, 98], [78, 166, 163, 91, 180, 133]], ![[127, 8, 76, 184, 4, 122], [36, 169, 131], [107, 52, 151], [65, 186, 162], [122, 91, 3], [13, 180, 157], [64, 96, 164, 53, 119, 158]]]
 h' := ![![[182, 179, 139, 106], [182, 76, 151, 165], [100, 186, 171, 68], [64, 70, 27, 95], [9, 32, 189, 39], [148, 107, 43, 92], [0, 0, 0, 1], [0, 1]], ![[80, 69, 154, 155], [51, 186, 45, 120], [6, 72, 127, 33], [109, 94, 148, 73], [148, 43, 143, 11], [41, 140, 66, 51], [152, 14, 151, 70], [182, 179, 139, 106]], ![[123, 137, 93, 125], [163, 129, 107, 27], [115, 187, 32, 110], [5, 4, 20, 124], [66, 119, 66, 61], [139, 144, 46, 64], [159, 110, 49, 22], [80, 69, 154, 155]], ![[0, 1], [112, 188, 83, 74], [181, 134, 56, 175], [60, 25, 191, 94], [178, 192, 181, 82], [74, 188, 38, 179], [140, 69, 186, 100], [123, 137, 93, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [189, 108, 151], []]
 b := ![[], [], [92, 145, 1, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [151, 49, 71, 1, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19818851, -23649920, 7849962, 10039314, 15751538]
  a := ![-3, 8, 6, 9, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8264107, -11303682, -4937792, -1335424, 15751538]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, -3, 6, -2, -5]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-16, -3, 6, -2, -5]] 
 ![![193, 0, 0, 0, 0], ![93, 1, 0, 0, 0], ![18, 0, 1, 0, 0], ![178, 0, 0, 1, 0], ![168, 0, 0, 0, 1]] where
  M :=![![![-16, -3, 6, -2, -5], ![14, 11, -20, 8, -2], ![-6, 10, 17, -12, 26], ![-21, -77, 34, 1, -61], ![19, 71, -54, 12, 32]]]
  hmulB := by decide  
  f := ![![![-862, -683, 582, 776, 829]], ![![-432, -344, 290, 388, 415]], ![![-110, -92, 69, 96, 104]], ![![-837, -673, 554, 747, 801]], ![![-745, -591, 502, 670, 716]]]
  g := ![![![7, -3, 6, -2, -5], ![-9, 11, -20, 8, -2], ![-18, 10, 17, -12, 26], ![86, -77, 34, 1, -61], ![-68, 71, -54, 12, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![862, 683, -582, -776, -829]] ![![-16, -3, 6, -2, -5]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 21, -4, -12, -18]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![-17, 21, -4, -12, -18]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![130, 54, 1, 0, 0], ![72, 6, 0, 1, 0], ![132, 147, 0, 0, 1]] where
  M :=![![![-17, 21, -4, -12, -18], ![60, 45, -18, -32, -36], ![68, 79, -23, -50, -60], ![80, 100, -22, -57, -72], ![-32, -17, 10, 16, 17]]]
  hmulB := by decide  
  f := ![![![-1, 5, -14, 8, -6]], ![![-4, 31, 14, -12, 60]], ![![-2, 11, -5, 2, 12]], ![![0, 4, -6, 3, 0]], ![![-4, 26, 2, -4, 41]]]
  g := ![![![19, 15, -4, -12, -18], ![48, 33, -18, -32, -36], ![74, 53, -23, -50, -60], ![84, 62, -22, -57, -72], ![-24, -16, 10, 16, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [142, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 196], [0, 1]]
 g := ![![[9, 154], [150], [59, 190], [107], [191], [144], [101, 1]], ![[0, 43], [150], [140, 7], [107], [191], [144], [5, 196]]]
 h' := ![![[101, 196], [154, 96], [93, 97], [165, 105], [92, 111], [182, 114], [39, 12], [0, 1]], ![[0, 1], [0, 101], [40, 100], [132, 92], [74, 86], [73, 83], [69, 185], [101, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [123, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [142, 96, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60, -1656, -13097, 10791, -3999]
  a := ![16, -7, -33, -7, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![7378, 6237, -13097, 10791, -3999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1029, -1091, 2870, -1316, 1300]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-1029, -1091, 2870, -1316, 1300]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![123, 95, 1, 0, 0], ![135, 99, 0, 1, 0], ![123, 8, 0, 0, 1]] where
  M :=![![![-1029, -1091, 2870, -1316, 1300], ![32, -7291, -2214, 3108, -10496], ![7388, 28257, -14679, 894, 19820], ![-20730, -48656, 50078, -15339, -11890], ![13170, 18553, -35400, 14920, -10087]]]
  hmulB := by decide  
  f := ![![![654775, -144751, -38452, 31376, 122468]], ![![-307688, 66735, 18186, -14152, -56680]], ![![260801, -58283, -15259, 12786, 49204]], ![![294767, -65818, -17252, 14425, 55574]], ![![397547, -87934, -23342, 19072, 74389]]]
  g := ![![![-1707, -781, 2870, -1316, 1300], ![5806, -105, -2214, 3108, -10496], ![-3785, 5968, -14679, 894, 19820], ![-13437, -16205, 50078, -15339, -11890], ![18243, 10077, -35400, 14920, -10087]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [20, 168, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 196], [0, 1]]
 g := ![![[166, 171], [100], [18, 19], [49], [1], [104], [29, 1]], ![[3, 26], [100], [175, 178], [49], [1], [104], [58, 196]]]
 h' := ![![[29, 196], [141, 34], [34, 10], [159, 77], [101, 7], [11, 196], [11, 33], [0, 1]], ![[0, 1], [142, 163], [127, 187], [28, 120], [107, 190], [179, 1], [180, 164], [29, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [50, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [20, 168, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![232, -2196, -3217, 1401, -3641]
  a := ![7, -4, -13, -5, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3323, 984, -3217, 1401, -3641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17999, -3970, -1056, 860, 3362]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![17999, -3970, -1056, 860, 3362]] 
 ![![197, 0, 0, 0, 0], ![96, 1, 0, 0, 0], ![120, 0, 1, 0, 0], ![102, 0, 0, 1, 0], ![166, 0, 0, 0, 1]] where
  M :=![![![17999, -3970, -1056, 860, 3362], ![-8444, 1853, 504, -392, -1564], ![1956, -452, -103, 112, 388], ![3722, -858, -204, 205, 730], ![6610, -1458, -392, 312, 1231]]]
  hmulB := by decide  
  f := ![![![-313, -2326, 304, 428, -2450]], ![![-132, -1067, 104, 216, -1156]], ![![-236, -1516, 297, 224, -1508]], ![![-120, -1202, 28, 293, -1382]], ![![-256, -1850, 264, 328, -1929]]]
  g := ![![![-609, -3970, -1056, 860, 3362], ![268, 1853, 504, -392, -1564], ![-92, -452, -103, 112, 388], ![-160, -858, -204, 205, 730], ![-216, -1458, -392, 312, 1231]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![-17, 21, -4, -12, -18]] ![![-1029, -1091, 2870, -1316, 1300]]
  ![![313, 2326, -304, -428, 2450]] where
 M := ![![![313, 2326, -304, -428, 2450]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![313, 2326, -304, -428, 2450]] ![![17999, -3970, -1056, 860, 3362]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB434I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB434I4 : PrimesBelowBoundCertificateInterval O 151 197 434 where
  m := 9
  g := ![2, 3, 4, 3, 3, 1, 3, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB434I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2, I167N3]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1, I197N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 24649]
    · exact ![26569, 26569, 163]
    · exact ![27889, 167, 167, 167]
    · exact ![29929, 29929, 173]
    · exact ![5735339, 179, 179]
    · exact ![194264244901]
    · exact ![6967871, 191, 191]
    · exact ![1387488001, 193]
    · exact ![38809, 38809, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
      exact NI167N3
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I163N2, I167N1, I167N2, I167N3, I173N2, I179N1, I179N2, I191N1, I191N2, I193N1, I197N2]
  Il := ![[], [I163N2], [I167N1, I167N2, I167N3], [I173N2], [I179N1, I179N2], [], [I191N1, I191N2], [I193N1], [I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
