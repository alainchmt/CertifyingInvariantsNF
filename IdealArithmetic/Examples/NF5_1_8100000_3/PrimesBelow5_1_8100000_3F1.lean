
import IdealArithmetic.Examples.NF5_1_8100000_3.RI5_1_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42, 4, -32, -47, -26]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![42, 4, -32, -47, -26]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![14, 11, 28, 23, 1]] where
  M :=![![![42, 4, -32, -47, -26], ![5, 93, -48, -85, -68], ![51, 212, -43, -113, -102], ![43, 156, 28, -6, -28], ![-20, -24, 76, 108, 69]]]
  hmulB := by decide  
  f := ![![![2, 4, -4, 3, 0]], ![![3, 1, 4, -5, 6]], ![![-17, -28, 13, -3, -16]], ![![13, 36, -32, 22, 2]], ![![-4, 3, -12, 13, -11]]]
  g := ![![![14, 10, 24, 19, -26], ![33, 29, 64, 51, -68], ![51, 46, 97, 77, -102], ![15, 16, 28, 22, -28], ![-34, -27, -64, -51, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 4 2 4 [8, 4, 18, 5, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12, 19, 7], [12, 28], [12, 17, 10, 22], [0, 1]]
 g := ![![[0, 15, 2, 6], [0, 3, 6], [22, 7, 24, 1], []], ![[13, 6, 13, 0, 1, 4], [4, 25, 20], [22, 20, 9, 20, 2, 13], [27, 27, 26, 14, 5, 24]], ![[19, 13, 15, 23], [1, 27, 6], [12, 0, 2, 28], []], ![[5, 0, 20, 21, 9, 25], [23, 17, 20], [26, 0, 27, 14, 28, 16], [15, 4, 27, 15, 24, 5]]]
 h' := ![![[0, 12, 19, 7], [4, 1, 27, 21], [27, 1, 22, 8], [0, 0, 0, 1], [0, 1]], ![[12, 28], [1, 1, 7, 19], [27, 11, 18, 22], [16, 24, 10, 21], [0, 12, 19, 7]], ![[12, 17, 10, 22], [27, 23, 0, 8], [8, 17, 20, 21], [17, 3, 7, 28], [12, 28]], ![[0, 1], [10, 4, 24, 10], [22, 0, 27, 7], [13, 2, 12, 8], [12, 17, 10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [8], []]
 b := ![[], [], [2, 17, 15, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 4
  hpos := by decide
  P := [8, 4, 18, 5, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1683984, 1724917, 759331, -1370686, 2306810]
  a := ![-5, -7, -3, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1055564, -815517, -2201081, -1876804, 2306810]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 707281 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 4, -4, 3, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![2, 4, -4, 3, 0]] 
 ![![29, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![2, 4, -4, 3, 0], ![3, 1, 4, -5, 6], ![-17, -28, 13, -3, -16], ![13, 36, -32, 22, 2], ![0, -24, 36, -32, 17]]]
  hmulB := by decide  
  f := ![![![42, 4, -32, -47, -26]], ![![19, 5, -16, -24, -14]], ![![9, 8, -7, -12, -8]], ![![29, 8, -20, -31, -18]], ![![8, 0, -4, -6, -3]]]
  g := ![![![-3, 4, -4, 3, 0], ![1, 1, 4, -5, 6], ![15, -28, 13, -3, -16], ![-25, 36, -32, 22, 2], ![22, -24, 36, -32, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![42, 4, -32, -47, -26]] ![![2, 4, -4, 3, 0]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, 59, -33, 14, 28]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![33, 59, -33, 14, 28]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![23, 7, 16, 1, 0], ![24, 13, 3, 0, 1]] where
  M :=![![![33, 59, -33, 14, 28], ![-42, -126, 115, -80, 0], ![-80, -7, -126, 150, -160], ![256, 435, -221, 69, 230], ![-319, -707, 517, -303, -175]]]
  hmulB := by decide  
  f := ![![![1765, -731, 95, 116, 348]], ![![-580, 236, -35, -42, -116]], ![![190, -77, 4, 4, 32]], ![![1285, -532, 65, 79, 250]], ![![1117, -464, 58, 71, 219]]]
  g := ![![![-31, -13, -11, 14, 28], ![58, 14, 45, -80, 0], ![10, 33, -66, 150, -160], ![-221, -98, -65, 69, 230], ![350, 119, 190, -303, -175]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [18, 15, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 21, 10], [0, 9, 21], [0, 1]]
 g := ![![[26, 19, 8], [5, 13, 25], [9, 1, 9], [1]], ![[19, 0, 0, 18], [14, 0, 10, 4], [3, 5, 30, 4], [26, 16, 14, 8]], ![[0, 13, 27, 21], [28, 28, 28, 24], [22, 21, 1, 12], [15, 27, 27, 23]]]
 h' := ![![[28, 21, 10], [3, 19, 15], [24, 16, 26], [13, 16, 28], [0, 1]], ![[0, 9, 21], [14, 30, 15], [5, 25, 22], [1, 13, 9], [28, 21, 10]], ![[0, 1], [23, 13, 1], [7, 21, 14], [9, 2, 25], [0, 9, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 2], []]
 b := ![[], [7, 20, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [18, 15, 3, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2067498, -9067080, 12455241, -10375392, 1674279]
  a := ![9, -56, 5, -57, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6334962, 1348227, 5594796, -10375392, 1674279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-420, -553, 121, 97, -488]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-420, -553, 121, 97, -488]] 
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![-420, -553, 121, 97, -488], ![1073, 2238, -1529, 827, 682], ![-537, -3039, 3602, -2913, 972], ![-2965, -3473, 217, 1246, -3740], ![5519, 9493, -4881, 1625, 4889]]]
  hmulB := by decide  
  f := ![![![-192850, 79521, -10615, -12897, -38098]], ![![-16621, 6861, -920, -1120, -3290]], ![![-137527, 56727, -7574, -9207, -27178]], ![![-75559, 31171, -4157, -5054, -14930]], ![![-34631, 14279, -1901, -2309, -6837]]]
  g := ![![![11, -553, 121, 97, -488], ![451, 2238, -1529, 827, 682], ![-1340, -3039, 3602, -2913, 972], ![328, -3473, 217, 1246, -3740], ![1148, 9493, -4881, 1625, 4889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -3, 3, -3, 2]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![0, -3, 3, -3, 2]] 
 ![![31, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![15, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![0, -3, 3, -3, 2], ![-7, -10, 1, 1, -8], ![17, 35, -26, 11, 10], ![-1, -19, 27, -26, 10], ![-19, -9, -15, 23, -33]]]
  hmulB := by decide  
  f := ![![![20850, -8597, 1139, 1383, 4112]], ![![17939, -7397, 980, 1190, 3538]], ![![10161, -4190, 555, 674, 2004]], ![![771, -318, 42, 51, 152]], ![![2399, -989, 131, 159, 473]]]
  g := ![![![1, -3, 3, -3, 2], ![9, -10, 1, 1, -8], ![-19, 35, -26, 11, 10], ![3, -19, 27, -26, 10], ![18, -9, -15, 23, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![33, 59, -33, 14, 28]] ![![-420, -553, 121, 97, -488]]
  ![![180190, 431262, -338714, 211067, 76590]] where
 M := ![![![180190, 431262, -338714, 211067, 76590]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![180190, 431262, -338714, 211067, 76590]] ![![0, -3, 3, -3, 2]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-10443249, -21407763, 14328355, -7561334, -6893656]]]
 hmul := by decide  
 g := ![![![![-336879, -690573, 462205, -243914, -222376]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)
instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-457, -606, 138, 100, -528]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-457, -606, 138, 100, -528]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![31, 29, 18, 1, 0], ![19, 25, 33, 0, 1]] where
  M :=![![![-457, -606, 138, 100, -528], ![1156, 2421, -1662, 904, 728], ![-552, -3242, 3877, -3148, 1080], ![-3232, -3822, 290, 1311, -4052], ![5974, 10318, -5346, 1814, 5263]]]
  hmulB := by decide  
  f := ![![![-1749, 678, -122, -140, -352]], ![![564, -251, -26, -32, 72]], ![![-176, 146, -107, -156, -136]], ![![-1115, 449, -176, -221, -308]], ![![-653, 303, -173, -230, -249]]]
  g := ![![![175, 262, 426, 100, -528], ![-1100, -1135, -1134, 904, 728], ![2068, 1650, 673, -3148, 1080], ![895, 1607, 2984, 1311, -4052], ![-4061, -4699, -5721, 1814, 5263]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [33, 17, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 11, 29], [22, 25, 8], [0, 1]]
 g := ![![[31, 21, 9], [28, 26], [25, 6, 21], [35, 1], []], ![[5, 11, 31, 23], [25, 16], [21, 2], [16, 33], [29, 27]], ![[13, 36, 6, 6], [20, 36], [10, 18, 23, 20], [12, 10], [13, 27]]]
 h' := ![![[13, 11, 29], [11, 12, 34], [26, 33, 27], [29, 1, 24], [0, 0, 1], [0, 1]], ![[22, 25, 8], [15, 22, 14], [10, 21, 4], [0, 3], [26, 12, 25], [13, 11, 29]], ![[0, 1], [36, 3, 26], [17, 20, 6], [2, 33, 13], [18, 25, 11], [22, 25, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 28], []]
 b := ![[], [6, 8, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [33, 17, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1379, -2084, 1742, 100, -1262]
  a := ![0, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![527, 718, 1124, 100, -1262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, -1, -3, -2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![0, 1, -1, -3, -2]] 
 ![![37, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![28, 0, 0, 0, 1]] where
  M :=![![![0, 1, -1, -3, -2], ![1, 6, -3, -3, -4], ![5, 15, -2, -5, -2], ![-1, 1, 7, -2, -2], ![1, 3, -3, 11, 3]]]
  hmulB := by decide  
  f := ![![![-4162, 1717, -227, -275, -820]], ![![-863, 356, -47, -57, -170]], ![![-1137, 469, -62, -75, -224]], ![![-3391, 1399, -185, -224, -668]], ![![-3101, 1279, -169, -205, -611]]]
  g := ![![![4, 1, -1, -3, -2], ![5, 6, -3, -3, -4], ![3, 15, -2, -5, -2], ![1, 1, 7, -2, -2], ![-11, 3, -3, 11, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1

def I37N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![150, 420, -372, 255, 22]] i)))

def SI37N2: IdealEqSpanCertificate' Table ![![150, 420, -372, 255, 22]] 
 ![![37, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![18, 0, 0, 0, 1]] where
  M :=![![![150, 420, -372, 255, 22], ![211, -77, 464, -511, 488], ![-1487, -2276, 899, -71, -1510], ![1369, 3484, -2880, 1874, 440], ![-368, -2832, 3576, -2972, 1179]]]
  hmulB := by decide  
  f := ![![![-1397466, 576020, -76280, -92571, -275492]], ![![-1120691, 461939, -61172, -74237, -220930]], ![![-948297, 390880, -51761, -62816, -186944]], ![![-647607, 266936, -35348, -42897, -127666]], ![![-663488, 273480, -36216, -43950, -130797]]]
  g := ![![![-213, 420, -372, 255, 22], ![-248, -77, 464, -511, 488], ![1965, -2276, 899, -71, -1510], ![-1917, 3484, -2880, 1874, 440], ![662, -2832, 3576, -2972, 1179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N2 : Nat.card (O ⧸ I37N2) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N2)

lemma isPrimeI37N2 : Ideal.IsPrime I37N2 := prime_ideal_of_norm_prime hp37.out _ NI37N2
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-457, -606, 138, 100, -528]] ![![0, 1, -1, -3, -2]]
  ![![-544, -3507, 4283, -3509, 1278]] where
 M := ![![![-544, -3507, 4283, -3509, 1278]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-544, -3507, 4283, -3509, 1278]] ![![150, 420, -372, 255, 22]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-12464523, -25551201, 17101585, -9024818, -8227912]]]
 hmul := by decide  
 g := ![![![![-336879, -690573, 462205, -243914, -222376]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -8, 2, 5, 4]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-6, -8, 2, 5, 4]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![4, 20, 1, 0, 0], ![1, 28, 0, 1, 0], ![26, 35, 0, 0, 1]] where
  M :=![![![-6, -8, 2, 5, 4], ![-3, -19, 0, 5, 6], ![-7, -28, -7, -1, 4], ![-3, -8, -10, -12, -6], ![6, 20, -6, -12, -11]]]
  hmulB := by decide  
  f := ![![![-6, 8, -2, -1, 2]], ![![-5, -19, 12, -7, -4]], ![![-3, -8, 5, -3, -2]], ![![-3, -12, 8, -5, -2]], ![![-9, -13, 10, -7, -3]]]
  g := ![![![-3, -8, 2, 5, 4], ![-4, -9, 0, 5, 6], ![-2, 0, -7, -1, 4], ![5, 18, -10, -12, -6], ![8, 21, -6, -12, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [8, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 40], [0, 1]]
 g := ![![[2, 36], [8], [36], [14, 10], [1]], ![[0, 5], [8], [36], [18, 31], [1]]]
 h' := ![![[25, 40], [27, 35], [38, 7], [11, 6], [33, 25], [0, 1]], ![[0, 1], [0, 6], [8, 34], [38, 35], [2, 16], [25, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [38, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [8, 16, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-211, -3280, 1900, 970, 2865]
  a := ![9, 27, 5, 26, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2031, -4115, 1900, 970, 2865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![258, 351, -91, -45, 292]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![258, 351, -91, -45, 292]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![29, 16, 1, 0, 0], ![14, 10, 0, 1, 0], ![33, 25, 0, 0, 1]] where
  M :=![![![258, 351, -91, -45, 292], ![-629, -1338, 935, -519, -382], ![245, 1697, -2102, 1733, -656], ![1837, 2247, -275, -648, 2252], ![-3309, -5803, 3091, -1119, -2855]]]
  hmulB := by decide  
  f := ![![![41036, -16881, 2259, 2735, 8094]], ![![-13453, 5560, -693, -841, -2624]], ![![23883, -9816, 1335, 1616, 4724]], ![![10877, -4471, 611, 740, 2154]], ![![24392, -10020, 1371, 1659, 4829]]]
  g := ![![![-149, -123, -91, -45, 292], ![-192, -38, 935, -519, -382], ![1429, 839, -2102, 1733, -656], ![-1352, -1053, -275, -648, 2252], ![413, 666, 3091, -1119, -2855]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P1 : CertificateIrreducibleZModOfList' 41 2 2 5 [36, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40], [0, 1]]
 g := ![![[10, 8], [25], [39], [40, 40], [1]], ![[0, 33], [25], [39], [31, 1], [1]]]
 h' := ![![[9, 40], [22, 34], [15, 36], [36, 11], [5, 9], [0, 1]], ![[0, 1], [0, 7], [11, 5], [12, 30], [4, 32], [9, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [35, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N1 : CertifiedPrimeIdeal' SI41N1 41 where
  n := 2
  hpos := by decide
  P := [36, 32, 1]
  hirr := P41P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3176, -5550, 2142, -1184, -3043]
  a := ![-11, -9, -5, -7, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1261, 1173, 2142, -1184, -3043]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N1 B_one_repr
lemma NI41N1 : Nat.card (O ⧸ I41N1) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9859, 4063, -539, -654, -1944]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-9859, 4063, -539, -654, -1944]] 
 ![![41, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![-9859, 4063, -539, -654, -1944], ![3234, -1332, 175, 212, 636], ![-1060, 441, -60, -74, -212], ![-1442, 599, -79, -97, -286], ![4271, -1759, 235, 285, 843]]]
  hmulB := by decide  
  f := ![![![-77, 15, -149, 172, -168]], ![![3, 21, -26, 22, -8]], ![![-54, -51, -14, 40, -76]], ![![-45, 20, -104, 115, -106]], ![![2, 58, -82, 73, -35]]]
  g := ![![![868, 4063, -539, -654, -1944], ![-282, -1332, 175, 212, 636], ![97, 441, -60, -74, -212], ![128, 599, -79, -97, -286], ![-378, -1759, 235, 285, 843]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-6, -8, 2, 5, 4]] ![![258, 351, -91, -45, 292]]
  ![![-77, 15, -149, 172, -168]] where
 M := ![![![-77, 15, -149, 172, -168]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-77, 15, -149, 172, -168]] ![![-9859, 4063, -539, -654, -1944]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 311, -435, 376, -182]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![15, 311, -435, 376, -182]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![19, 40, 1, 0, 0], ![7, 27, 0, 1, 0], ![20, 31, 0, 0, 1]] where
  M :=![![![15, 311, -435, 376, -182], ![740, 866, -53, -312, 934], ![-2180, -4295, 2734, -1352, -1558], ![512, 3063, -3679, 2993, -1040], ![1903, 393, 2575, -3191, 3657]]]
  hmulB := by decide  
  f := ![![![643, -803, -19, 102, 258]], ![![-414, -564, -287, -194, -54]], ![![-103, -894, -291, -152, 56]], ![![-151, -476, -195, -123, -4]], ![![-1, -751, -214, -97, 73]]]
  g := ![![![216, 307, -435, 376, -182], ![-343, -408, -53, -312, 934], ![-314, -671, 2734, -1352, -1558], ![1634, 2364, -3679, 2993, -1040], ![-2275, -3019, 2575, -3191, 3657]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [32, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[20, 16], [13, 36], [13], [20, 25], [1]], ![[14, 27], [21, 7], [13], [16, 18], [1]]]
 h' := ![![[5, 42], [14, 4], [39, 37], [5, 23], [11, 5], [0, 1]], ![[0, 1], [34, 39], [9, 6], [34, 20], [36, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [25, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [32, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1628, -1400, -1112, 1812, -2480]
  a := ![6, -4, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1312, 1652, -1112, 1812, -2480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63, 21, -15, -18, -20]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-63, 21, -15, -18, -20]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![21, 24, 1, 0, 0], ![6, 24, 0, 1, 0], ![25, 26, 0, 0, 1]] where
  M :=![![![-63, 21, -15, -18, -20], ![22, 4, -19, -28, -16], ![4, 55, -28, -50, -40], ![4, 61, -3, -19, -22], ![31, 3, 27, 31, 21]]]
  hmulB := by decide  
  f := ![![![-15, -49, 49, -36, 4]], ![![-44, -22, -41, 58, -76]], ![![-27, -28, -3, 16, -36]], ![![-30, -29, -7, 21, -42]], ![![-36, -36, -6, 23, -49]]]
  g := ![![![20, 31, -15, -18, -20], ![23, 36, -19, -28, -16], ![44, 69, -28, -50, -40], ![17, 27, -3, -19, -22], ![-29, -45, 27, 31, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [1, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 42], [0, 1]]
 g := ![![[21, 1], [21, 1], [9], [26, 11], [1]], ![[0, 42], [0, 42], [9], [10, 32], [1]]]
 h' := ![![[22, 42], [22, 42], [22, 42], [17, 3], [42, 22], [0, 1]], ![[0, 1], [0, 1], [0, 1], [40, 40], [10, 21], [22, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [40, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [1, 21, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2279, -6989, 3601, -100, 520]
  a := ![19, 19, 10, 20, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2100, -2431, 3601, -100, 520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1

def I43N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -8, 4, 6, 6]] i)))

def SI43N2: IdealEqSpanCertificate' Table ![![11, -8, 4, 6, 6]] 
 ![![43, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![32, 0, 1, 0, 0], ![24, 0, 0, 1, 0], ![36, 0, 0, 0, 1]] where
  M :=![![![11, -8, 4, 6, 6], ![-6, -9, 4, 8, 6], ![-4, -24, 3, 10, 10], ![-2, -16, -4, -1, 2], ![-4, 8, -8, -12, -9]]]
  hmulB := by decide  
  f := ![![![-19, -24, -4, 14, -30]], ![![-8, -9, -4, 8, -14]], ![![-16, -24, 3, 6, -22]], ![![-14, -16, -4, 11, -22]], ![![-8, -8, -8, 12, -17]]]
  g := ![![![-7, -8, 4, 6, 6], ![-8, -9, 4, 8, 6], ![-4, -24, 3, 10, 10], ![10, -16, -4, -1, 2], ![16, 8, -8, -12, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N2 : Nat.card (O ⧸ I43N2) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N2)

lemma isPrimeI43N2 : Ideal.IsPrime I43N2 := prime_ideal_of_norm_prime hp43.out _ NI43N2
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![15, 311, -435, 376, -182]] ![![-63, 21, -15, -18, -20]]
  ![![19, 24, 4, -14, 30]] where
 M := ![![![19, 24, 4, -14, 30]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![19, 24, 4, -14, 30]] ![![11, -8, 4, 6, 6]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![-43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4549, -2990, 2, 250, 1062]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![4549, -2990, 2, 250, 1062]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![3, 4, 37, 19, 1]] where
  M :=![![![4549, -2990, 2, 250, 1062], ![-1874, -509, -866, -808, -562], ![316, -738, -1633, -1978, -1054], ![1002, 1242, -990, -1691, -1170], ![-1514, 3214, 378, -126, -771]]]
  hmulB := by decide  
  f := ![![![287, 418, -142, -14, 306]], ![![-626, -1399, 1030, -604, -334]], ![![64, 1470, -2067, 1790, -874]], ![![2082, 2778, -654, -433, 2394]], ![![783, 2052, -1735, 1149, 211]]]
  g := ![![![29, -154, -836, -424, 1062], ![-4, 37, 424, 210, -562], ![74, 74, 795, 384, -1054], ![96, 126, 900, 437, -1170], ![17, 134, 615, 309, -771]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [40, 27, 44, 35, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 4, 44, 27], [1, 18, 2, 27], [39, 24, 1, 40], [0, 1]]
 g := ![![[43, 43, 18, 6], [44, 5, 23, 16], [15, 45, 23, 36], [12, 1], []], ![[44, 32, 0, 46, 34, 24], [23, 35, 42, 42, 3, 14], [9, 14, 3, 46, 20, 36], [6, 19, 36, 13, 18, 16], [23, 32, 24]], ![[12, 29, 17, 40, 40, 6], [4, 23, 7, 10, 46, 16], [33, 15, 35, 18], [8, 28, 45, 27, 41, 27], [19, 20, 24]], ![[12, 25, 24, 34, 14, 22], [9, 43, 3, 25, 3, 10], [2, 10, 32, 7, 15, 19], [44, 19, 46, 1, 28, 43], [26, 10, 2]]]
 h' := ![![[19, 4, 44, 27], [26, 2, 2, 10], [11, 10, 20, 4], [37, 12, 9, 6], [0, 0, 1], [0, 1]], ![[1, 18, 2, 27], [43, 2, 24, 11], [16, 43, 21, 45], [0, 4, 14, 39], [5, 37, 27, 21], [19, 4, 44, 27]], ![[39, 24, 1, 40], [40, 9, 14, 18], [23, 25, 1, 21], [11, 34, 28], [40, 39, 13, 1], [1, 18, 2, 27]], ![[0, 1], [9, 34, 7, 8], [29, 16, 5, 24], [45, 44, 43, 2], [11, 18, 6, 25], [39, 24, 1, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [46, 30, 26], []]
 b := ![[], [], [41, 10, 10, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [40, 27, 44, 35, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-126084, -13999, -183435, 209759, -255267]
  a := ![1, -3, 1, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![13611, 21427, 197052, 107656, -255267]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![287, 418, -142, -14, 306]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![287, 418, -142, -14, 306]] 
 ![![47, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![25, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![287, 418, -142, -14, 306], ![-626, -1399, 1030, -604, -334], ![64, 1470, -2067, 1790, -874], ![2082, 2778, -654, -433, 2394], ![-3482, -6386, 3666, -1542, -2813]]]
  hmulB := by decide  
  f := ![![![4549, -2990, 2, 250, 1062]], ![![928, -647, -18, 36, 214]], ![![3975, -2624, -33, 176, 904]], ![![2441, -1564, -20, 97, 540]], ![![4420, -2858, 10, 242, 1023]]]
  g := ![![![-251, 418, -142, -14, 306], ![34, -1399, 1030, -604, -334], ![1395, 1470, -2067, 1790, -874], ![-2089, 2778, -654, -433, 2394], ![1660, -6386, 3666, -1542, -2813]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![4549, -2990, 2, 250, 1062]] ![![287, 418, -142, -14, 306]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0, 0, 0]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]] where
  M :=![![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![0, 0, 0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [27, 7, 20, 21, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 13, 50, 31, 1], [23, 10, 16, 14, 33], [2, 7, 25, 35, 41], [6, 22, 15, 26, 31], [0, 1]]
 g := ![![[31, 20, 45, 40, 9], [17, 18, 31, 36], [21, 38, 12, 40, 36], [42, 1], []], ![[52, 48, 50, 37, 15, 8, 36, 38], [46, 10, 43, 13], [30, 2, 13, 6, 51, 50, 43, 1], [20, 41, 11, 28], [10, 28, 28, 45, 27, 43, 29, 1]], ![[43, 50, 32, 26, 1, 14, 37, 32], [41, 47, 37, 52], [13, 42, 3, 15, 38, 8, 52, 3], [12, 4, 2, 25], [0, 32, 15, 26, 35, 13, 19, 3]], ![[3, 46, 47, 50, 23, 38, 8, 21], [12, 6, 46, 15], [0, 52, 17, 13, 37, 4, 39, 48], [6, 39, 12, 38], [45, 12, 11, 49, 38, 11, 49, 21]], ![[21, 21, 46, 33, 5, 20], [36, 27, 23, 17], [30, 33, 40, 49, 5, 24, 49, 51], [33, 6, 29, 11], [6, 16, 49, 37, 47, 13, 14, 5]]]
 h' := ![![[11, 13, 50, 31, 1], [9, 33, 30, 32, 3], [16, 10, 17, 40, 6], [32, 50, 1, 52, 47], [0, 0, 0, 1], [0, 1]], ![[23, 10, 16, 14, 33], [19, 18, 34, 39, 41], [28, 9, 30, 15, 38], [44, 20, 10, 15, 52], [1, 24, 50, 3, 9], [11, 13, 50, 31, 1]], ![[2, 7, 25, 35, 41], [49, 27, 6, 15, 50], [34, 49, 33, 34, 30], [46, 16, 40, 10, 33], [30, 7, 22, 20, 48], [23, 10, 16, 14, 33]], ![[6, 22, 15, 26, 31], [32, 0, 1, 29, 12], [12, 50, 19, 12, 11], [35, 1, 9, 51, 7], [12, 28, 2, 13, 41], [2, 7, 25, 35, 41]], ![[0, 1], [42, 28, 35, 44], [22, 41, 7, 5, 21], [11, 19, 46, 31, 20], [1, 47, 32, 16, 8], [6, 22, 15, 26, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 29, 49, 2], [], [], []]
 b := ![[], [28, 24, 34, 44, 51], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [27, 7, 20, 21, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27202215232, 71246390295, -60214621343, 39953375681, 7389722690]
  a := ![13, 9, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![513249344, 1344271515, -1136124931, 753837277, 139428730]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 418195493 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2610, 6804, -5730, 3783, 728]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![2610, 6804, -5730, 3783, 728]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![4, 30, 47, 1, 0], ![17, 17, 54, 0, 1]] where
  M :=![![![2610, 6804, -5730, 3783, 728], ![2327, -2977, 8260, -8405, 6838], ![-22081, -32008, 10699, 1277, -23648], ![23123, 55556, -43782, 27364, 9682], ![-10030, -50544, 58086, -46312, 13899]]]
  hmulB := by decide  
  f := ![![![-4650, 2084, -122, -177, -866]], ![![1555, -619, 352, 445, 512]], ![![-579, -208, 405, 637, 378]], ![![0, -346, 495, 727, 506]], ![![-1389, 211, 434, 658, 249]]]
  g := ![![![-422, -2018, -3777, 3783, 728], ![-1361, 2253, 577, -8405, 6838], ![6353, 5622, 20808, 1277, -23648], ![-4253, -15762, -31402, 27364, 9682], ![-1035, 18687, 25156, -46312, 13899]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [11, 18, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 9, 50], [2, 49, 9], [0, 1]]
 g := ![![[57, 24, 41], [16, 4, 27], [3, 29], [40, 39, 45], [1]], ![[10, 46, 1, 10], [47, 15, 25, 52], [24, 5], [5, 58, 2, 55], [1, 33, 31, 38]], ![[20, 20, 53, 57], [10, 3], [43, 27], [37, 30, 52, 48], [40, 8, 21, 21]]]
 h' := ![![[22, 9, 50], [1, 48, 49], [47, 33, 26], [32, 34, 41], [48, 41, 24], [0, 1]], ![[2, 49, 9], [15, 49, 22], [13, 42, 33], [49, 6, 51], [17, 2, 40], [22, 9, 50]], ![[0, 1], [46, 21, 47], [45, 43], [20, 19, 26], [40, 16, 54], [2, 49, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 46], []]
 b := ![[], [45, 42, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [11, 18, 35, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42312, 128800, -130730, 82745, -4410]
  a := ![7, 7, 3, 6, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3622, -38620, -64095, 82745, -4410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4650, -2084, 122, 177, 866]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![4650, -2084, 122, 177, 866]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![45, 24, 1, 0, 0], ![50, 30, 0, 1, 0], ![38, 34, 0, 0, 1]] where
  M :=![![![4650, -2084, 122, 177, 866], ![-1555, 619, -352, -445, -512], ![579, 208, -405, -637, -378], ![837, 404, -98, -312, -192], ![-1930, 1224, 174, 132, -297]]]
  hmulB := by decide  
  f := ![![![-2610, -6804, 5730, -3783, -728]], ![![-2327, 2977, -8260, 8405, -6838]], ![![-2563, -3436, 829, 512, -2936]], ![![-3787, -5194, 1398, 604, -4258]], ![![-2852, -1810, -2054, 3192, -4645]]]
  g := ![![![-722, -674, 122, 177, 866], ![949, 675, -352, -445, -512], ![1102, 710, -405, -637, -378], ![477, 316, -98, -312, -192], ![-86, 54, 174, 132, -297]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [38, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 58], [0, 1]]
 g := ![![[16, 25], [32, 3], [57], [36, 22], [41, 1]], ![[38, 34], [37, 56], [57], [53, 37], [23, 58]]]
 h' := ![![[41, 58], [23, 5], [20, 11], [48, 36], [35, 50], [0, 1]], ![[0, 1], [51, 54], [58, 48], [49, 23], [20, 9], [41, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [39, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [38, 18, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-208, -1006, 615, -24, 262]
  a := ![7, 8, 3, 9, 10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-621, -406, 615, -24, 262]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![2610, 6804, -5730, 3783, 728]] ![![4650, -2084, 122, 177, 866]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![-59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 5, -11, 10, -18]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-25, 5, -11, 10, -18]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![59, 37, 4, 13, 1]] where
  M :=![![![-25, 5, -11, 10, -18], ![46, 64, -31, 6, 38], ![-70, -169, 140, -94, -26], ![-44, 21, -95, 103, -100], ![163, 187, -21, -53, 193]]]
  hmulB := by decide  
  f := ![![![-3, 1, 3, 4, 2]], ![![0, -6, 5, 8, 6]], ![![-4, -17, 6, 12, 10]], ![![-4, -15, -1, 3, 4]], ![![-4, -7, 6, 10, 7]]]
  g := ![![![17, 11, 1, 4, -18], ![-36, -22, -3, -8, 38], ![24, 13, 4, 4, -26], ![96, 61, 5, 23, -100], ![-184, -114, -13, -42, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 4 2 5 [35, 36, 40, 37, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 29, 1, 11], [9, 39, 50, 28], [33, 53, 10, 22], [0, 1]]
 g := ![![[4, 11, 33, 52], [30, 60, 52], [28, 9, 29, 39], [34, 48, 24, 1], []], ![[17, 2, 17, 59, 21, 32], [45, 46, 49], [55, 41, 54, 21, 41, 32], [1, 18, 57, 35, 16, 8], [34, 39, 33, 17, 38, 50]], ![[21, 29, 3, 42, 33, 33], [58, 12, 25], [55, 30, 52, 26, 54, 35], [43, 6, 59, 16, 34, 17], [7, 60, 36, 56, 44, 53]], ![[14, 4, 14, 21, 53, 22], [31, 50, 46], [30, 41, 55, 21, 34, 27], [40, 32, 59, 0, 24, 25], [11, 34, 49, 19, 25, 34]]]
 h' := ![![[43, 29, 1, 11], [3, 21, 60, 28], [57, 4, 18, 28], [30, 24, 37, 10], [0, 0, 0, 1], [0, 1]], ![[9, 39, 50, 28], [23, 43, 41, 21], [16, 47, 50, 7], [59, 38, 2, 40], [54, 40, 12, 20], [43, 29, 1, 11]], ![[33, 53, 10, 22], [2, 26, 14, 11], [43, 55, 10, 56], [42, 35, 52, 13], [57, 49, 46, 15], [9, 39, 50, 28]], ![[0, 1], [47, 32, 7, 1], [41, 16, 44, 31], [31, 25, 31, 59], [50, 33, 3, 25], [33, 53, 10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [15, 36, 12], []]
 b := ![[], [], [57, 27, 44, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 4
  hpos := by decide
  P := [35, 36, 40, 37, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-248730850, -394932667, 181334507, -33807727, -241527032]
  a := ![-9, -7, -17, -7, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![229530558, 140025697, 18810535, 50918749, -241527032]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 13845841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 3, 4, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-3, 1, 3, 4, 2]] 
 ![![61, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![46, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![48, 0, 0, 0, 1]] where
  M :=![![![-3, 1, 3, 4, 2], ![0, -6, 5, 8, 6], ![-4, -17, 6, 12, 10], ![-4, -15, -1, 3, 4], ![1, -1, -7, -9, -5]]]
  hmulB := by decide  
  f := ![![![-25, 5, -11, 10, -18]], ![![-14, 4, -7, 6, -10]], ![![-20, 1, -6, 6, -14]], ![![-4, 1, -3, 3, -4]], ![![-17, 7, -9, 7, -11]]]
  g := ![![![-5, 1, 3, 4, 2], ![-6, -6, 5, 8, 6], ![-4, -17, 6, 12, 10], ![6, -15, -1, 3, 4], ![11, -1, -7, -9, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-25, 5, -11, 10, -18]] ![![-3, 1, 3, 4, 2]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![61, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)


lemma PB178I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB178I1 : PrimesBelowBoundCertificateInterval O 23 61 178 where
  m := 9
  g := ![2, 3, 3, 3, 3, 2, 1, 2, 2]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB178I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1, I37N2]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N2]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC29
    · exact PBC31
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![707281, 29]
    · exact ![29791, 31, 31]
    · exact ![50653, 37, 37]
    · exact ![1681, 1681, 41]
    · exact ![1849, 1849, 43]
    · exact ![4879681, 47]
    · exact ![418195493]
    · exact ![205379, 3481]
    · exact ![13845841, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
      exact NI37N2
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N2
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
  β := ![I29N1, I31N1, I31N2, I37N1, I37N2, I41N2, I43N2, I47N1, I61N1]
  Il := ![[I29N1], [I31N1, I31N2], [I37N1, I37N2], [I41N2], [I43N2], [I47N1], [], [], [I61N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
