
import IdealArithmetic.Examples.NF5_3_40500000_1.RI5_3_40500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10684, -2341, -3455, -610, 10841]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-10684, -2341, -3455, -610, 10841]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![156, 41, 98, 120, 1]] where
  M :=![![![-10684, -2341, -3455, -610, 10841], ![-45665, -10008, -14873, -2640, 46607], ![-196075, -42971, -63622, -11266, 199529], ![-397128, -87043, -129083, -22871, 404664], ![-147321, -32285, -47833, -8472, 149990]]]
  hmulB := by decide  
  f := ![![![-22, -9, 3, 2, -5]], ![![-3, -2, -29, -8, 61]], ![![-193, -59, -4, -2, 43]], ![![-92, -87, -43, 7, 72]], ![![-214, -113, -40, 4, 93]]]
  g := ![![![-10840, -2846, -6789, -8290, 10841], ![-46601, -12235, -29187, -35640, 46607], ![-199507, -52380, -124952, -152578, 199529], ![-404616, -106231, -253415, -309443, 404664], ![-149973, -39375, -93929, -114696, 149990]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [44, 36, 38, 76, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 129, 130, 20], [34, 23, 94, 138], [16, 4, 90, 156], [0, 1]]
 g := ![![[10, 78, 106, 113], [153, 77, 39], [142, 77, 11, 99], [70, 56, 0, 122], [66, 149, 120, 124], [1], []], ![[62, 154, 142, 10, 51, 66], [42, 7, 57], [140, 108, 117, 131, 29, 22], [106, 17, 3, 117, 73, 87], [39, 102, 82, 64, 19, 69], [20, 144, 126], [66, 77, 86]], ![[9, 17, 81, 23, 121, 49], [8, 74, 156], [6, 65, 21, 151, 65, 39], [2, 96, 70, 39, 74, 110], [140, 68, 145, 37, 87, 143], [64, 33, 76], [91, 78, 47]], ![[13, 81, 46, 16, 152, 3], [117, 16, 64], [109, 21, 71, 21, 66, 110], [143, 44, 138, 108, 136, 100], [106, 144, 120, 116, 15, 71], [2, 68, 101], [35, 58, 1]]]
 h' := ![![[31, 129, 130, 20], [101, 139, 48, 120], [32, 124, 103, 14], [60, 1, 103, 16], [79, 69, 64, 43], [113, 121, 119, 81], [0, 0, 1], [0, 1]], ![[34, 23, 94, 138], [72, 44, 83, 31], [151, 54, 17, 123], [156, 18, 103, 41], [14, 127, 148, 111], [89, 0, 68, 59], [98, 36, 94, 35], [31, 129, 130, 20]], ![[16, 4, 90, 156], [20, 97, 39, 138], [134, 13, 28, 28], [112, 2, 105, 119], [51, 15, 108, 126], [23, 111, 57, 154], [135, 37, 0, 95], [34, 23, 94, 138]], ![[0, 1], [46, 34, 144, 25], [135, 123, 9, 149], [155, 136, 3, 138], [83, 103, 151, 34], [68, 82, 70, 20], [129, 84, 62, 27], [16, 4, 90, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [148, 75, 55], []]
 b := ![[], [], [44, 41, 53, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [44, 36, 38, 76, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-265029327801, -55550474518, -90310192913, -16539932374, 280477291776]
  a := ![77, -62, 79, 36, -264]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-280378897101, -73599486862, -175650221573, -214482897742, 280477291776]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 9, -3, -2, 5]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![22, 9, -3, -2, 5]] 
 ![![157, 0, 0, 0, 0], ![42, 1, 0, 0, 0], ![120, 0, 1, 0, 0], ![128, 0, 0, 1, 0], ![52, 0, 0, 0, 1]] where
  M :=![![![22, 9, -3, -2, 5], ![3, 2, 29, 8, -61], ![193, 59, 4, 2, -43], ![92, 87, 43, -7, -72], ![89, 33, 7, 0, -26]]]
  hmulB := by decide  
  f := ![![![10684, 2341, 3455, 610, -10841]], ![![3149, 690, 1019, 180, -3197]], ![![9415, 2063, 3046, 538, -9557]], ![![11240, 2463, 3639, 643, -11416]], ![![4477, 981, 1449, 256, -4546]]]
  g := ![![![0, 9, -3, -2, 5], ![-9, 2, 29, 8, -61], ![-5, 59, 4, 2, -43], ![-26, 87, 43, -7, -72], ![-5, 33, 7, 0, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-10684, -2341, -3455, -610, 10841]] ![![22, 9, -3, -2, 5]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2311, -506, -748, -132, 2348]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-2311, -506, -748, -132, 2348]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![121, 61, 129, 1, 0], ![2, 60, 138, 0, 1]] where
  M :=![![![-2311, -506, -748, -132, 2348], ![-9892, -2163, -3222, -572, 10100], ![-42492, -9306, -13783, -2440, 43244], ![-86084, -18854, -27986, -4957, 87744], ![-31934, -6994, -10368, -1836, 32519]]]
  hmulB := by decide  
  f := ![![![-53, -10, 32, 12, -68]], ![![172, 43, -54, -20, 100]], ![![-220, -2, 143, 32, -260]], ![![-147, 7, 117, 27, -220]], ![![-124, 14, 102, 20, -185]]]
  g := ![![![55, -818, -1888, -132, 2348], ![240, -3517, -8118, -572, 10100], ![1020, -15062, -34765, -2440, 43244], ![2075, -30559, -70535, -4957, 87744], ![768, -11326, -26142, -1836, 32519]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [56, 83, 149, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 145, 35], [58, 17, 128], [0, 1]]
 g := ![![[59, 105, 145], [131, 49, 41], [57, 25], [92, 151], [73, 140], [113, 14, 1], []], ![[150, 20, 132, 111], [63, 41, 118, 95], [149, 143], [67, 6], [52, 69], [1, 44, 134, 9], [79, 84]], ![[131, 71, 153, 101], [4, 82, 160, 137], [72, 54], [48, 47], [132, 49], [94, 26, 99, 70], [149, 84]]]
 h' := ![![[119, 145, 35], [162, 128, 109], [78, 36, 81], [70, 150, 5], [13, 73, 71], [29, 106, 38], [0, 0, 1], [0, 1]], ![[58, 17, 128], [112, 121, 139], [64, 34, 29], [101, 97, 119], [105, 131, 13], [88, 50, 118], [120, 103, 17], [119, 145, 35]], ![[0, 1], [58, 77, 78], [92, 93, 53], [7, 79, 39], [139, 122, 79], [149, 7, 7], [73, 60, 145], [58, 17, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 147], []]
 b := ![[], [65, 109, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [56, 83, 149, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51296118601, 10593183944, 16034001200, 2852031318, -51766489929]
  a := ![379, -328, 378, 160, -1299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1167280313, 18052813922, 41668083260, 2852031318, -51766489929]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, -9, 45, 18, -96]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-133, -9, 45, 18, -96]] 
 ![![163, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-133, -9, 45, 18, -96], ![228, 14, -87, -36, 192], ![-456, -63, 170, 78, -384], ![300, 87, -189, -85, 432], ![-210, -21, 69, 30, -151]]]
  hmulB := by decide  
  f := ![![![63797, 13977, 20727, 3672, -64992]], ![![35338, 7742, 11481, 2034, -36000]], ![![47118, 10323, 15308, 2712, -48000]], ![![67425, 14772, 21906, 3881, -68688]], ![![14802, 3243, 4809, 852, -15079]]]
  g := ![![![-25, -9, 45, 18, -96], ![50, 14, -87, -36, 192], ![-84, -63, 170, 78, -384], ![81, 87, -189, -85, 432], ![-36, -21, 69, 30, -151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 1, 0, -4]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![5, 1, 1, 0, -4]] 
 ![![163, 0, 0, 0, 0], ![145, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![117, 0, 0, 0, 1]] where
  M :=![![![5, 1, 1, 0, -4], ![20, 2, 9, 2, -28], ![112, 23, 28, 4, -100], ![212, 41, 77, 13, -240], ![84, 17, 25, 4, -83]]]
  hmulB := by decide  
  f := ![![![403, 47, -173, -66, 364]], ![![353, 41, -152, -58, 320]], ![![14, 1, -6, -2, 12]], ![![59, 8, -28, -11, 60]], ![![293, 34, -126, -48, 265]]]
  g := ![![![2, 1, 1, 0, -4], ![18, 2, 9, 2, -28], ![51, 23, 28, 4, -100], ![134, 41, 77, 13, -240], ![44, 17, 25, 4, -83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-2311, -506, -748, -132, 2348]] ![![-133, -9, 45, 18, -96]]
  ![![403, 47, -173, -66, 364]] where
 M := ![![![403, 47, -173, -66, 364]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![403, 47, -173, -66, 364]] ![![5, 1, 1, 0, -4]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-381, -46, 144, 52, -290]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-381, -46, 144, 52, -290]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![164, 46, 13, 1, 0], ![67, 104, 79, 0, 1]] where
  M :=![![![-381, -46, 144, 52, -290], ![722, 45, -246, -76, 466], ![-1266, 106, 253, 40, -386], ![324, -502, 262, 151, -624], ![-604, -30, 184, 56, -343]]]
  hmulB := by decide  
  f := ![![![209, 42, 68, 12, -218]], ![![922, 191, 298, 52, -950]], ![![4022, 842, 1311, 232, -4154]], ![![822, 170, 267, 47, -850]], ![![2579, 538, 839, 148, -2663]]]
  g := ![![![63, 166, 134, 52, -290], ![-108, -269, -216, -76, 466], ![108, 230, 181, 40, -386], ![104, 344, 285, 151, -624], ![79, 198, 159, 56, -343]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [39, 113, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 133, 162], [69, 33, 5], [0, 1]]
 g := ![![[24, 143, 147], [165, 45, 7], [47, 32, 63], [47, 16], [55, 75], [76, 135, 1], []], ![[65, 34, 126, 1], [26, 82, 73, 18], [78, 126, 103, 144], [39, 77], [6, 9], [125, 133, 137, 66], [41, 25]], ![[3, 86, 163, 46], [48, 37, 48, 111], [7, 131, 2, 155], [9, 24], [27, 107], [101, 121, 26, 102], [31, 25]]]
 h' := ![![[66, 133, 162], [78, 157, 100], [4, 48, 95], [42, 147, 49], [120, 49, 4], [42, 8, 143], [0, 0, 1], [0, 1]], ![[69, 33, 5], [69, 88, 10], [58, 166, 56], [48, 129, 47], [20, 34, 54], [33, 49, 3], [85, 91, 33], [66, 133, 162]], ![[0, 1], [47, 89, 57], [76, 120, 16], [32, 58, 71], [7, 84, 109], [15, 110, 21], [45, 76, 133], [69, 33, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 75], []]
 b := ![[], [134, 89, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [39, 113, 32, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42570625, 8966298, 12780224, 2289432, -41690512]
  a := ![40, -33, 41, 18, -137]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![14732743, 25386022, 19620168, 2289432, -41690512]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![209, 42, 68, 12, -218]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![209, 42, 68, 12, -218]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![64, 141, 1, 0, 0], ![164, 112, 0, 1, 0], ![110, 76, 0, 0, 1]] where
  M :=![![![209, 42, 68, 12, -218], ![922, 191, 298, 52, -950], ![4022, 842, 1311, 232, -4154], ![8300, 1770, 2686, 473, -8496], ![3064, 650, 996, 176, -3149]]]
  hmulB := by decide  
  f := ![![![-381, -46, 144, 52, -290]], ![![722, 45, -246, -76, 466]], ![![456, 21, -151, -44, 280]], ![![112, -18, -22, 1, 24]], ![![74, -10, -16, 0, 19]]]
  g := ![![![107, 34, 68, 12, -218], ![466, 147, 298, 52, -950], ![2030, 633, 1311, 232, -4154], ![4152, 1292, 2686, 473, -8496], ![1538, 478, 996, 176, -3149]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [157, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 166], [0, 1]]
 g := ![![[65, 50], [50, 77], [3, 28], [8], [147], [154, 157], [1]], ![[0, 117], [0, 90], [0, 139], [8], [147], [0, 10], [1]]]
 h' := ![![[149, 166], [166, 102], [30, 113], [80, 23], [0, 141], [37, 67], [10, 149], [0, 1]], ![[0, 1], [0, 65], [0, 54], [0, 144], [134, 26], [0, 100], [0, 18], [149, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [133, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [157, 18, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2015886, -396688, -780019, -102449, 2412708]
  a := ![-240, 198, -243, -111, 823]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1201742, -373087, -780019, -102449, 2412708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-381, -46, 144, 52, -290]] ![![209, 42, 68, 12, -218]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![428, 339, 147, 36, -143]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![428, 339, 147, 36, -143]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![95, 167, 126, 105, 1]] where
  M :=![![![428, 339, 147, 36, -143], ![211, 828, 85, 42, 727], ![-4223, 1485, -1256, -124, 7105], ![-17000, -283, -5475, -843, 21528], ![-5719, 119, -1807, -266, 7448]]]
  hmulB := by decide  
  f := ![![![198, 15, -71, -28, 151]], ![![-363, -30, 133, 54, -287]], ![![679, 77, -266, -112, 583]], ![![-492, -103, 229, 99, -504]], ![![-44, -27, 34, 15, -74]]]
  g := ![![![81, 140, 105, 87, -143], ![-398, -697, -529, -441, 727], ![-3926, -6850, -5182, -4313, 7105], ![-11920, -20783, -15711, -13071, 21528], ![-4123, -7189, -5435, -4522, 7448]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [96, 52, 48, 19, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 65, 26, 164], [171, 79, 16, 38], [87, 28, 131, 144], [0, 1]]
 g := ![![[102, 53, 131, 15], [54, 126, 13], [135, 24, 161, 78], [161, 104, 82, 49], [151, 53, 51], [154, 1], []], ![[111, 41, 22, 3, 78, 60], [52, 154, 6], [14, 43, 63, 151, 158, 148], [66, 117, 99, 154, 148, 64], [143, 163, 60], [166, 127, 154, 55, 38, 38], [16, 69, 81]], ![[12, 98, 8, 172, 3, 10], [105, 147, 89], [24, 67, 58, 75, 35, 56], [54, 138, 59, 164, 169, 64], [131, 135, 85], [71, 97, 118, 131, 51, 152], [33, 76, 60]], ![[28, 153, 72, 156, 155, 150], [103, 163, 159], [55, 75, 109, 109, 17, 34], [110, 103, 9, 155, 45, 138], [25, 151, 31], [160, 36, 162, 115, 128, 96], [147, 124, 149]]]
 h' := ![![[69, 65, 26, 164], [58, 106, 71, 154], [15, 39, 102, 79], [114, 134, 141, 123], [49, 94, 113, 166], [94, 27, 168, 140], [0, 0, 1], [0, 1]], ![[171, 79, 16, 38], [138, 78, 126, 33], [99, 66, 101, 51], [140, 30, 103, 56], [161, 30, 84, 75], [7, 94, 17, 135], [111, 130, 6, 19], [69, 65, 26, 164]], ![[87, 28, 131, 144], [141, 144, 152, 8], [138, 94, 63, 75], [110, 23, 98, 77], [162, 101, 99, 78], [121, 110, 67, 137], [123, 14, 71, 171], [171, 79, 16, 38]], ![[0, 1], [79, 18, 170, 151], [148, 147, 80, 141], [87, 159, 4, 90], [154, 121, 50, 27], [85, 115, 94, 107], [31, 29, 95, 156], [87, 28, 131, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [114, 145, 139], []]
 b := ![[], [], [22, 56, 141, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [96, 52, 48, 19, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1292513270995, -243865465289, -477353758309, -97151229608, 1458169983213]
  a := ![135, -105, 140, 70, -463]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-808200356510, -1409007240820, -1064779026839, -885578031601, 1458169983213]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![198, 15, -71, -28, 151]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![198, 15, -71, -28, 151]] 
 ![![173, 0, 0, 0, 0], ![143, 1, 0, 0, 0], ![138, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![198, 15, -71, -28, 151], ![-363, -30, 133, 54, -287], ![679, 77, -266, -112, 583], ![-492, -103, 229, 99, -504], ![305, 27, -113, -46, 244]]]
  hmulB := by decide  
  f := ![![![428, 339, 147, 36, -143]], ![![355, 285, 122, 30, -114]], ![![317, 279, 110, 28, -73]], ![![-76, 16, -24, -3, 117]], ![![9, 34, 4, 2, 29]]]
  g := ![![![32, 15, -71, -28, 151], ![-58, -30, 133, 54, -287], ![101, 77, -266, -112, 583], ![-56, -103, 229, 99, -504], ![48, 27, -113, -46, 244]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![428, 339, 147, 36, -143]] ![![198, 15, -71, -28, 151]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-609, -130, -204, -38, 634]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-609, -130, -204, -38, 634]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![4, 93, 72, 1, 0], ![130, 72, 87, 0, 1]] where
  M :=![![![-609, -130, -204, -38, 634], ![-2638, -597, -828, -142, 2614], ![-11082, -2414, -3695, -662, 11482], ![-22752, -4990, -7310, -1307, 22992], ![-8368, -1830, -2744, -490, 8573]]]
  hmulB := by decide  
  f := ![![![617, 54, -232, -90, 490]], ![![-1190, -115, 424, 166, -890]], ![![2126, 170, -825, -314, 1738]], ![![242, 9, -114, -41, 242]], ![![1008, 76, -401, -152, 847]]]
  g := ![![![-463, -236, -294, -38, 634], ![-1910, -981, -1218, -142, 2614], ![-8386, -4288, -5335, -662, 11482], ![-16796, -8597, -10690, -1307, 22992], ![-6262, -3204, -3985, -490, 8573]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [4, 160, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [177, 152, 144], [163, 26, 35], [0, 1]]
 g := ![![[90, 125, 168], [1, 3, 22], [126, 68], [39, 29], [143, 8, 48], [164, 161, 1], []], ![[80, 72, 79, 42], [159, 23, 0, 88], [74, 29], [16, 168], [135, 82, 9, 161], [21, 137, 5, 147], [67, 151]], ![[69, 57, 144, 63], [177, 16, 169, 163], [82, 59], [61, 149], [81, 13, 129, 167], [107, 111, 38, 97], [176, 151]]]
 h' := ![![[177, 152, 144], [175, 149, 40], [58, 27, 77], [174, 120, 28], [144, 20, 108], [60, 145, 103], [0, 0, 1], [0, 1]], ![[163, 26, 35], [57, 28, 121], [82, 30, 162], [60, 79, 108], [53, 141, 139], [144, 41, 109], [94, 61, 26], [177, 152, 144]], ![[0, 1], [98, 2, 18], [35, 122, 119], [30, 159, 43], [128, 18, 111], [105, 172, 146], [89, 118, 152], [163, 26, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [169, 129], []]
 b := ![[], [69, 103, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [4, 160, 18, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-73867068, -93271104, 90658240, 43178400, -201652992]
  a := ![-84, 56, -86, -62, 288]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![145074348, 58157280, 81148736, 43178400, -201652992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, 9, 9, 2, -22]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![25, 9, 9, 2, -22]] 
 ![![179, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![102, 0, 1, 0, 0], ![71, 0, 0, 1, 0], ![78, 0, 0, 0, 1]] where
  M :=![![![25, 9, 9, 2, -22], ![82, 34, 23, 4, -58], ![234, 91, 90, 18, -214], ![368, 137, 113, 25, -288], ![138, 53, 49, 10, -119]]]
  hmulB := by decide  
  f := ![![![379, 39, -53, -28, 74]], ![![34, 4, -3, -2, 2]], ![![232, 25, -28, -16, 34]], ![![171, 20, -12, -9, 2]], ![![176, 19, -21, -12, 25]]]
  g := ![![![3, 9, 9, 2, -22], ![8, 34, 23, 4, -58], ![28, 91, 90, 18, -214], ![41, 137, 113, 25, -288], ![16, 53, 49, 10, -119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32, 15, 11, 2, -27]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![32, 15, 11, 2, -27]] 
 ![![179, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![176, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![109, 0, 0, 0, 1]] where
  M :=![![![32, 15, 11, 2, -27], ![107, 38, 39, 8, -93], ![353, 141, 104, 22, -267], ![460, 197, 153, 23, -360], ![193, 79, 61, 12, -152]]]
  hmulB := by decide  
  f := ![![![-4074, -883, -1305, -230, 4101]], ![![-529, -115, -170, -30, 534]], ![![-4421, -959, -1418, -250, 4455]], ![![-1274, -278, -412, -73, 1293]], ![![-2793, -606, -896, -158, 2815]]]
  g := ![![![4, 15, 11, 2, -27], ![14, 38, 39, 8, -93], ![45, 141, 104, 22, -267], ![48, 197, 153, 23, -360], ![24, 79, 61, 12, -152]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-609, -130, -204, -38, 634]] ![![25, 9, 9, 2, -22]]
  ![![-113, -69, -59, -20, 92]] where
 M := ![![![-113, -69, -59, -20, 92]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-113, -69, -59, -20, 92]] ![![32, 15, 11, 2, -27]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-23270, -9308, -7518, -1432, 18437]]]
 hmul := by decide  
 g := ![![![![-130, -52, -42, -8, 103]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-735, -76, 308, 142, -716]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-735, -76, 308, 142, -716]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![157, 81, 129, 63, 1]] where
  M :=![![![-735, -76, 308, 142, -716], ![1592, 419, -774, -378, 1804], ![-3728, -1536, 2481, 1098, -5516], ![5308, 2448, -3100, -1173, 6144], ![-1268, -336, 752, 342, -1727]]]
  hmulB := by decide  
  f := ![![![381, 84, 124, 22, -388]], ![![1632, 359, 530, 94, -1660]], ![![6984, 1536, 2269, 402, -7108]], ![![14140, 3104, 4596, 815, -14400]], ![![10989, 2415, 3571, 633, -11187]]]
  g := ![![![617, 320, 512, 250, -716], ![-1556, -805, -1290, -630, 1804], ![4764, 2460, 3945, 1926, -5516], ![-5300, -2736, -4396, -2145, 6144], ![1491, 771, 1235, 603, -1727]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 4 2 7 [23, 86, 53, 89, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 57, 57, 118], [143, 146, 87, 103], [76, 158, 37, 141], [0, 1]]
 g := ![![[37, 119, 148, 56], [9, 2, 52], [89, 50, 78, 167], [0, 32, 59], [21, 110, 169, 166], [92, 1], []], ![[54, 5, 46, 115, 56, 151], [50, 31, 25], [129, 46, 173, 31, 141, 78], [47, 24, 60], [105, 177, 116, 142, 61, 92], [151, 0, 34, 129, 33, 173], [117, 129, 168]], ![[106, 41, 178, 34, 22, 127], [29, 38, 136], [90, 61, 64, 104, 97, 17], [158, 52, 56], [132, 35, 0, 146, 176, 86], [21, 159, 103, 146, 129, 159], [115, 79, 111]], ![[135, 108, 11, 112, 121, 174], [93, 9, 126], [130, 45, 173, 16, 10, 72], [120, 11, 94], [105, 126, 94, 45, 95, 31], [117, 24, 50, 57, 107, 128], [105, 164, 152]]]
 h' := ![![[54, 57, 57, 118], [33, 133, 34, 150], [125, 103, 23, 140], [161, 64, 132, 23], [60, 67, 10, 56], [56, 29, 106, 85], [0, 0, 1], [0, 1]], ![[143, 146, 87, 103], [36, 131, 40, 131], [171, 141, 64, 176], [161, 135, 19, 4], [95, 83, 57, 28], [73, 37, 174, 150], [44, 5, 11, 33], [54, 57, 57, 118]], ![[76, 158, 37, 141], [57, 71, 168, 137], [0, 104, 166, 90], [152, 21, 103, 172], [96, 46, 164, 150], [147, 65, 90, 120], [66, 3, 167, 124], [143, 146, 87, 103]], ![[0, 1], [132, 27, 120, 125], [113, 14, 109, 137], [94, 142, 108, 163], [35, 166, 131, 128], [134, 50, 173, 7], [103, 173, 2, 24], [76, 158, 37, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [66, 159, 91], []]
 b := ![[], [], [159, 14, 48, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 4
  hpos := by decide
  P := [23, 86, 53, 89, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-360022286545, -75821686540, -113701972410, -19892485629, 364352281983]
  a := ![-12, 22, -8, 15, 43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-318029450596, -163471583023, -260304675957, -126928653318, 364352281983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 1073283121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![381, 84, 124, 22, -388]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![381, 84, 124, 22, -388]] 
 ![![181, 0, 0, 0, 0], ![46, 1, 0, 0, 0], ![56, 0, 1, 0, 0], ![137, 0, 0, 1, 0], ![148, 0, 0, 0, 1]] where
  M :=![![![381, 84, 124, 22, -388], ![1632, 359, 530, 94, -1660], ![6984, 1536, 2269, 402, -7108], ![14140, 3104, 4596, 815, -14400], ![5244, 1152, 1704, 302, -5339]]]
  hmulB := by decide  
  f := ![![![-735, -76, 308, 142, -716]], ![![-178, -17, 74, 34, -172]], ![![-248, -32, 109, 50, -252]], ![![-527, -44, 216, 101, -508]], ![![-608, -64, 256, 118, -595]]]
  g := ![![![243, 84, 124, 22, -388], ![1040, 359, 530, 94, -1660], ![4454, 1536, 2269, 402, -7108], ![9025, 3104, 4596, 815, -14400], ![3346, 1152, 1704, 302, -5339]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-735, -76, 308, 142, -716]] ![![381, 84, 124, 22, -388]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![669, 61, -255, -112, 574]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![669, 61, -255, -112, 574]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![139, 70, 67, 1, 0], ![2, 70, 182, 0, 1]] where
  M :=![![![669, 61, -255, -112, 574], ![-1302, -244, 593, 274, -1358], ![2954, 947, -1638, -732, 3646], ![-3340, -1423, 2021, 787, -4128], ![1130, 229, -531, -240, 1201]]]
  hmulB := by decide  
  f := ![![![-789, -185, -257, -46, 790]], ![![-3306, -762, -1075, -192, 3322]], ![![-13922, -3171, -4526, -806, 14038]], ![![-6815, -1559, -2216, -395, 6864]], ![![-14540, -3315, -4727, -842, 14657]]]
  g := ![![![79, -169, -509, -112, 574], ![-192, 396, 1201, 274, -1358], ![510, -1063, -3226, -732, 3646], ![-547, 1217, 3668, 787, -4128], ![168, -351, -1063, -240, 1201]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [26, 100, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [173, 180, 155], [59, 10, 36], [0, 1]]
 g := ![![[177, 104, 144], [124, 156, 150], [145, 25, 17], [51, 6, 34], [65, 52, 130], [53, 41, 1], []], ![[122, 89, 138, 22], [138, 112, 38, 71], [181, 33, 0, 62], [82, 167, 11, 178], [183, 130, 51, 174], [6, 68, 161, 29], [66, 150]], ![[75, 79, 10, 158], [26, 74, 151, 129], [162, 143, 141, 136], [18, 117, 94, 133], [18, 166, 92, 128], [112, 153, 34, 154], [185, 150]]]
 h' := ![![[173, 180, 155], [23, 178, 179], [50, 60, 36], [11, 169, 50], [29, 132, 15], [150, 128, 148], [0, 0, 1], [0, 1]], ![[59, 10, 36], [153, 106, 157], [46, 24, 110], [140, 46, 146], [75, 170, 173], [20, 67, 119], [136, 19, 10], [173, 180, 155]], ![[0, 1], [115, 98, 46], [58, 107, 45], [68, 167, 186], [106, 80, 3], [100, 187, 115], [8, 172, 180], [59, 10, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78, 25], []]
 b := ![[], [102, 168, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [26, 100, 150, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![746805, -71344, -67241, 107281, -204526]
  a := ![-12, 6, -13, -11, 41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-72022, 35266, 156904, 107281, -204526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![789, 185, 257, 46, -790]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![789, 185, 257, 46, -790]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![34, 57, 1, 0, 0], ![177, 112, 0, 1, 0], ![112, 108, 0, 0, 1]] where
  M :=![![![789, 185, 257, 46, -790], ![3306, 762, 1075, 192, -3322], ![13922, 3171, 4526, 806, -14038], ![27800, 6257, 9041, 1609, -28128], ![10338, 2333, 3361, 598, -10451]]]
  hmulB := by decide  
  f := ![![![-669, -61, 255, 112, -574]], ![![1302, 244, -593, -274, 1358]], ![![254, 57, -123, -58, 284]], ![![161, 94, -122, -61, 286]], ![![338, 101, -183, -88, 425]]]
  g := ![![![379, 344, 257, 46, -790], ![1596, 1449, 1075, 192, -3322], ![6752, 6131, 4526, 806, -14038], ![13539, 12296, 9041, 1609, -28128], ![5030, 4568, 3361, 598, -10451]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P1 : CertificateIrreducibleZModOfList' 191 2 2 7 [53, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [187, 190], [0, 1]]
 g := ![![[119, 134], [186, 162], [106, 77], [168, 136], [92, 30], [169, 16], [1]], ![[156, 57], [111, 29], [180, 114], [6, 55], [163, 161], [105, 175], [1]]]
 h' := ![![[187, 190], [74, 158], [112, 60], [73, 29], [90, 161], [20, 139], [138, 187], [0, 1]], ![[0, 1], [15, 33], [63, 131], [148, 162], [19, 30], [37, 52], [154, 4], [187, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [39, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N1 : CertifiedPrimeIdeal' SI191N1 191 where
  n := 2
  hpos := by decide
  P := [53, 4, 1]
  hirr := P191P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-292797, -43800, -198598, -30904, 537258]
  a := ![-125, 97, -125, -66, 429]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-252583, -226630, -198598, -30904, 537258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N1 B_one_repr
lemma NI191N1 : Nat.card (O ⧸ I191N1) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![669, 61, -255, -112, 574]] ![![789, 185, 257, 46, -790]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0, 0, 0]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]] where
  M :=![![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![0, 0, 0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 5 2 7 [170, 75, 153, 150, 160, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 47, 166, 75, 48], [83, 109, 118, 148, 126], [162, 112, 142, 141, 8], [107, 117, 153, 22, 11], [0, 1]]
 g := ![![[112, 136, 140, 52, 86], [153, 137, 55, 93], [57, 42, 166, 128], [182, 9, 24, 187], [88, 131, 94, 97], [33, 1], []], ![[35, 156, 133, 163, 80, 75, 178, 48], [50, 177, 125, 184], [89, 39, 62, 31], [56, 88, 83, 192], [130, 57, 64, 161], [95, 107, 65, 23], [57, 141, 129, 149, 6, 167, 101, 3]], ![[0, 74, 5, 1, 9, 129, 3, 3], [64, 152, 123, 54], [180, 185, 49, 172], [167, 142, 173, 168], [154, 51, 2, 128], [88, 18, 132, 100], [13, 23, 166, 47, 137, 178, 44, 124]], ![[150, 125, 157, 87, 6, 31, 134, 96], [110, 95, 117, 42], [61, 25, 37, 16], [19, 167, 149, 139], [157, 82, 112, 7], [41, 66, 136, 46], [81, 187, 64, 142, 141, 83, 157, 126]], ![[126, 38, 120, 21, 175, 111, 103, 47], [88, 127, 126, 65], [66, 153, 52, 137], [164, 107, 164, 31], [133, 1, 82, 21], [141, 15, 60, 42], [41, 163, 39, 36, 87, 135, 185, 173]]]
 h' := ![![[67, 47, 166, 75, 48], [109, 14, 42, 5, 146], [185, 82, 44, 67, 38], [15, 68, 45, 16, 30], [70, 142, 125, 121, 103], [180, 57, 87, 108, 167], [0, 0, 0, 1], [0, 1]], ![[83, 109, 118, 148, 126], [158, 79, 151, 126, 192], [121, 192, 13, 93, 50], [2, 45, 188, 111, 80], [79, 113, 124, 66, 112], [131, 68, 135, 129, 136], [29, 35, 188, 112, 71], [67, 47, 166, 75, 48]], ![[162, 112, 142, 141, 8], [145, 149, 105, 14, 71], [105, 6, 176, 31, 132], [37, 185, 113, 119, 128], [40, 147, 81, 55, 174], [92, 53, 53, 154, 163], [34, 140, 127, 189, 10], [83, 109, 118, 148, 126]], ![[107, 117, 153, 22, 11], [52, 13, 158, 123, 28], [80, 79, 2, 16, 87], [118, 41, 130, 182, 189], [158, 158, 175, 94, 77], [139, 41, 39, 174, 59], [57, 163, 77, 65, 25], [162, 112, 142, 141, 8]], ![[0, 1], [66, 131, 123, 118, 142], [92, 27, 151, 179, 79], [73, 47, 103, 151, 152], [57, 19, 74, 50, 113], [146, 167, 72, 14, 54], [50, 48, 187, 19, 87], [107, 117, 153, 22, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 108, 77, 105], [], [], []]
 b := ![[], [191, 100, 118, 122, 34], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 5
  hpos := by decide
  P := [170, 75, 153, 150, 160, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-351411764354558, -77577448869818, -114036628353199, -19789348199893, 357638559833295]
  a := ![-86, 68, -89, -43, 295]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1820786343806, -401955693626, -590863359343, -102535482901, 1853049532815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 267785184193 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀

instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1716, 414, -694, -98, 935]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![1716, 414, -694, -98, 935]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![0, 0, 0, 197, 0], ![76, 39, 6, 65, 1]] where
  M :=![![![1716, 414, -694, -98, 935], ![-3303, 879, 14, -702, 1841], ![623, -9170, 7727, 4942, -20809], ![19080, 20512, -20848, -9219, 44856], ![2251, -1170, 608, 808, -2788]]]
  hmulB := by decide  
  f := ![![![-5834, -1278, -1896, -336, 5945]], ![![-25021, -5481, -8128, -1440, 25487]], ![![-107275, -23502, -34855, -6176, 109289]], ![![-217480, -47648, -70656, -12519, 221544]], ![![-82638, -18105, -26848, -4757, 84183]]]
  g := ![![![-352, -183, -32, -309, 935], ![-727, -360, -56, -611, 1841], ![8031, 4073, 673, 6891, -20809], ![-17208, -8776, -1472, -14847, 44856], ![1087, 546, 88, 924, -2788]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 4 2 7 [119, 195, 196, 159, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 53, 173, 31], [154, 193, 55, 96], [53, 147, 166, 70], [0, 1]]
 g := ![![[162, 74, 8, 136], [88, 9, 63], [183, 188, 62, 168], [28, 164, 90], [68, 111, 169], [66, 38, 1], []], ![[23, 36, 169, 195, 47, 12], [153, 168, 64], [113, 14, 174, 44, 12, 140], [152, 5, 64], [117, 19, 51], [29, 112, 109], [42, 193, 93, 120, 51, 44]], ![[91, 163, 192, 19, 126, 187], [184, 73, 33], [97, 126, 183, 20, 161, 96], [128, 5, 34], [172, 176, 178], [106, 193, 93], [185, 7, 23, 77, 142, 9]], ![[130, 139, 86, 81, 63, 55], [167, 63, 1], [118, 156, 44, 187, 83, 4], [1, 167, 25], [110, 84, 156], [70, 192, 36], [171, 34, 148, 125, 47, 23]]]
 h' := ![![[28, 53, 173, 31], [189, 183, 91, 147], [90, 122, 53, 76], [189, 63, 2, 94], [70, 169, 74, 175], [26, 141, 23, 184], [0, 0, 0, 1], [0, 1]], ![[154, 193, 55, 96], [60, 71, 50, 87], [145, 115, 43, 189], [106, 91, 123, 190], [55, 136, 164, 189], [42, 75, 125, 53], [12, 121, 40, 122], [28, 53, 173, 31]], ![[53, 147, 166, 70], [31, 188, 68, 195], [81, 44, 187, 128], [158, 88, 119, 196], [157, 71, 57, 25], [149, 152, 187, 93], [130, 4, 58, 68], [154, 193, 55, 96]], ![[0, 1], [60, 149, 185, 162], [191, 113, 111, 1], [41, 152, 150, 111], [102, 18, 99, 5], [105, 26, 59, 64], [84, 72, 99, 6], [53, 147, 166, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [22, 69, 109], []]
 b := ![[], [], [125, 125, 118, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 4
  hpos := by decide
  P := [119, 195, 196, 159, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40517271431, -8555395914, -13137487770, -2309758235, 41634705972]
  a := ![-22, 22, -22, -3, 76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16267791499, -8285832126, -1334749866, -13749064195, 41634705972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 1506138481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5834, -1278, -1896, -336, 5945]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-5834, -1278, -1896, -336, 5945]] 
 ![![197, 0, 0, 0, 0], ![25, 1, 0, 0, 0], ![163, 0, 1, 0, 0], ![117, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![-5834, -1278, -1896, -336, 5945], ![-25021, -5481, -8128, -1440, 25487], ![-107275, -23502, -34855, -6176, 109289], ![-217480, -47648, -70656, -12519, 221544], ![-80633, -17666, -26198, -4642, 82144]]]
  hmulB := by decide  
  f := ![![![1716, 414, -694, -98, 935]], ![![201, 57, -88, -16, 128]], ![![1423, 296, -535, -56, 668]], ![![1116, 350, -518, -105, 783]], ![![1379, 324, -550, -74, 731]]]
  g := ![![![-2837, -1278, -1896, -336, 5945], ![-12163, -5481, -8128, -1440, 25487], ![-52153, -23502, -34855, -6176, 109289], ![-105721, -47648, -70656, -12519, 221544], ![-39199, -17666, -26198, -4642, 82144]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![1716, 414, -694, -98, 935]] ![![-5834, -1278, -1896, -336, 5945]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB312I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB312I4 : PrimesBelowBoundCertificateInterval O 151 197 312 where
  m := 9
  g := ![2, 3, 2, 2, 3, 2, 2, 1, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB312I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
    · exact ![I197N0, I197N1]
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
    · exact ![607573201, 157]
    · exact ![4330747, 163, 163]
    · exact ![4657463, 27889]
    · exact ![895745041, 173]
    · exact ![5735339, 179, 179]
    · exact ![1073283121, 181]
    · exact ![6967871, 36481]
    · exact ![267785184193]
    · exact ![1506138481, 197]
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I163N1, I163N2, I173N1, I179N1, I179N2, I181N1, I197N1]
  Il := ![[I157N1], [I163N1, I163N2], [], [I173N1], [I179N1, I179N2], [I181N1], [], [], [I197N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
