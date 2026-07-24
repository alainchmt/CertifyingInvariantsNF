
import IdealArithmetic.Examples.NF5_3_2025000000_6.RI5_3_2025000000_6
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![302, -51, 22, 64, -271]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![302, -51, 22, 64, -271]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![302, -51, 22, 64, -271], ![1414, -237, 103, 299, -1266], ![6604, -1100, 482, 1395, -5906], ![30796, -5094, 2251, 6494, -27490], ![7632, -1261, 558, 1609, -6811]]]
  hmulB := by decide  
  f := ![![![-15, -8, 1, 6, -23]], ![![35, 31, -4, -19, 73]], ![![-226, -200, 30, 115, -444]], ![![1424, 1082, -181, -632, 2450]], ![![303, 229, -39, -133, 516]]]
  g := ![![![151, -51, 22, 64, -271], ![707, -237, 103, 299, -1266], ![3302, -1100, 482, 1395, -5906], ![15398, -5094, 2251, 6494, -27490], ![3816, -1261, 558, 1609, -6811]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1053, -1287, 263, 470, -1845]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-1053, -1287, 263, 470, -1845]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1053, -1287, 263, 470, -1845], ![6610, 2682, -1027, -1622, 6670], ![-30684, 9768, -32, -2697, 10288], ![-30152, -67972, 10071, 18862, -71182], ![-12000, -17205, 2864, 5071, -19314]]]
  hmulB := by decide  
  f := ![![![1283204, -226741, 92338, 274467, -1163250]], ![![3045702, -542087, 220009, 654359, -2772609]], ![![14504242, -2561031, 1043310, 3100962, -13142876]], ![![68830120, -12260394, 4974099, 14795142, -62687308]], ![![17752359, -3158840, 1282185, 3813441, -16158217]]]
  g := ![![![396, -1287, 263, 470, -1845], ![-30, 2682, -1027, -1622, 6670], ![-20486, 9768, -32, -2697, 10288], ![20515, -67972, 10071, 18862, -71182], ![3657, -17205, 2864, 5071, -19314]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![862509, 577053, -95134, -357436, 1383550]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![862509, 577053, -95134, -357436, 1383550]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![862509, 577053, -95134, -357436, 1383550], ![-4517932, -3015517, 496781, 1866976, -7225956], ![23580968, 15773216, -2600229, -9769767, 37816136], ![-123480040, -82433496, 13581041, 51038469, -197541122], ![-25434942, -16976723, 2796774, 10510685, -40680627]]]
  hmulB := by decide  
  f := ![![![-6746, -1016, 635, 775, -3222]], ![![4413, -5564, 563, 1577, -5996]], ![![5961, 31805, -5787, -11817, 46556]], ![![-181719, -74495, 24332, 36269, -146448]], ![![-46578, -14467, 5484, 7693, -31273]]]
  g := ![![![369013, 577053, -95134, -357436, 1383550], ![-1933086, -3015517, 496781, 1866976, -7225956], ![10088874, 15773216, -2600229, -9769767, 37816136], ![-52833027, -82433496, 13581041, 51038469, -197541122], ![-10882839, -16976723, 2796774, 10510685, -40680627]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![302, -51, 22, 64, -271]] ![![-1053, -1287, 263, 470, -1845]]
  ![![-7892, 1787, -501, -1745, 7422]] where
 M := ![![![-7892, 1787, -501, -1745, 7422]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-7892, 1787, -501, -1745, 7422]] ![![-1053, -1287, 263, 470, -1845]]
  ![![-953730, 971600, -212100, -533785, 2189824]] where
 M := ![![![-953730, 971600, -212100, -533785, 2189824]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-953730, 971600, -212100, -533785, 2189824]] ![![862509, 577053, -95134, -357436, 1383550]]
  ![![-31378, 7118, -2089, -7145, 30422]] where
 M := ![![![-31378, 7118, -2089, -7145, 30422]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-31378, 7118, -2089, -7145, 30422]] ![![862509, 577053, -95134, -357436, 1383550]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-9254, -5450, 874, 3304, -12716]]]
 hmul := by decide  
 g := ![![![![-4627, -2725, 437, 1652, -6358]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12065, -8667, 1459, 5442, -21120]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-12065, -8667, 1459, 5442, -21120]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![-12065, -8667, 1459, 5442, -21120], ![70224, 44047, -7113, -26921, 103932], ![-333184, -236316, 39638, 148033, -574246], ![1903492, 1206906, -195599, -739350, 2855658], ![395306, 247985, -40048, -151569, 585155]]]
  hmulB := by decide  
  f := ![![![1014913, -234413, 68675, 233462, -993674]], ![![5290868, -1222017, 358005, 1217053, -5180088]], ![![9532179, -2201587, 644989, 2192671, -9332572]], ![![49691824, -11477201, 3362412, 11430623, -48651654]], ![![13831434, -3194610, 935907, 3181646, -13541899]]]
  g := ![![![-4508, 2337, 1459, 5442, -21120], ![25779, -10988, -7113, -26921, 103932], ![-124274, 63299, 39638, 148033, -574246], ![699697, -303134, -195599, -739350, 2855658], ![145118, -61867, -40048, -151569, 585155]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28143, 9432, -1575, -7144, 30592]
  a := ![15, -39, 4, 18, -76]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8856, -4672, -1575, -7144, 30592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-667, 132, -47, -147, 624]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-667, 132, -47, -147, 624]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-667, 132, -47, -147, 624], ![-3288, 653, -231, -725, 3078], ![-16228, 3246, -1140, -3587, 15230], ![-80324, 16170, -5633, -17780, 75498], ![-20080, 4046, -1408, -4446, 18879]]]
  hmulB := by decide  
  f := ![![![-1497, -1000, 165, 619, -2396]], ![![1610, 1073, -177, -665, 2574]], ![![-14618, -9754, 1608, 6043, -23390]], ![![70142, 46854, -7719, -29024, 112338]], ![![14648, 9786, -1612, -6062, 23463]]]
  g := ![![![-181, 132, -47, -147, 624], ![-894, 653, -231, -725, 3078], ![-4422, 3246, -1140, -3587, 15230], ![-21946, 16170, -5633, -17780, 75498], ![-5488, 4046, -1408, -4446, 18879]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-12065, -8667, 1459, 5442, -21120]] ![![-667, 132, -47, -147, 624]]
  ![![-165809, 29403, -11954, -35543, 150620]] where
 M := ![![![-165809, 29403, -11954, -35543, 150620]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-165809, 29403, -11954, -35543, 150620]] ![![-667, 132, -47, -147, 624]]
  ![![38413383, -6811103, 2769249, 8233766, -34892236]] where
 M := ![![![38413383, -6811103, 2769249, 8233766, -34892236]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![38413383, -6811103, 2769249, 8233766, -34892236]] ![![-667, 132, -47, -147, 624]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-8899113873, 1577907915, -641543658, -1907492013, 8083380252]]]
 hmul := by decide  
 g := ![![![![-2966371291, 525969305, -213847886, -635830671, 2694460084]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -54, 8, 18, -70]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![11, -54, 8, 18, -70]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![11, -54, 8, 18, -70], ![236, 189, -48, -82, 328], ![-1312, -92, 107, 116, -492], ![2584, -2332, 192, 631, -2384], ![472, -654, 72, 194, -743]]]
  hmulB := by decide  
  f := ![![![1047, -250, 72, 246, -1046]], ![![1319, -301, 88, 300, -1278]], ![![6556, -1564, 451, 1540, -6548]], ![![30499, -6894, 2024, 6893, -29374]], ![![8038, -1830, 536, 1826, -7779]]]
  g := ![![![31, -54, 8, 18, -70], ![-67, 189, -48, -82, 328], ![-156, -92, 107, 116, -492], ![1657, -2332, 192, 631, -2384], ![426, -654, 72, 194, -743]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![11, -54, 8, 18, -70]] ![![11, -54, 8, 18, -70]]
  ![![-9647, -7732, 1952, 3332, -13320]] where
 M := ![![![-9647, -7732, 1952, 3332, -13320]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-9647, -7732, 1952, 3332, -13320]] ![![11, -54, 8, 18, -70]]
  ![![-2169045, -178938, 183528, 205222, -867918]] where
 M := ![![![-2169045, -178938, 183528, 205222, -867918]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-2169045, -178938, 183528, 205222, -867918]] ![![11, -54, 8, 18, -70]]
  ![![-186241247, 155465240, -12213312, -41961656, 158459536]] where
 M := ![![![-186241247, 155465240, -12213312, -41961656, 158459536]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-186241247, 155465240, -12213312, -41961656, 158459536]] ![![11, -54, 8, 18, -70]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![17028990155, 34785627650, -6906637240, -13253891270, 52339588170]]]
 hmul := by decide  
 g := ![![![![3405798031, 6957125530, -1381327448, -2650778254, 10467917634]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-32445, 3507, -1855, -5286, 22804]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-32445, 3507, -1855, -5286, 22804]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 4, 1]] where
  M :=![![![-32445, 3507, -1855, -5286, 22804], ![-127736, 34391, -11739, -36103, 150884], ![-745920, 70868, -40544, -114277, 495302], ![-2821476, 821254, -272573, -843228, 3515678], ![-717458, 193319, -65968, -202895, 847931]]]
  hmulB := by decide  
  f := ![![![-6055, 1361, -399, -1370, 5834]], ![![-31124, 7227, -2133, -7217, 30720]], ![![-163624, 38164, -11102, -37703, 160418]], ![![-853004, 194682, -57175, -195058, 830442]], ![![-518126, 118255, -34728, -118479, 504413]]]
  g := ![![![-4635, 501, -265, -13786, 22804], ![-18248, 4913, -1677, -91377, 150884], ![-106560, 10124, -5792, -299355, 495302], ![-403068, 117322, -38939, -2129420, 3515678], ![-102494, 27617, -9424, -513517, 847931]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 6, 6, 4, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 2, 5, 4], [1, 3, 3, 5], [3, 1, 6, 5], [0, 1]]
 g := ![![[6, 3, 3, 1], []], ![[2, 1, 5, 2, 6, 2], [2, 0, 5, 6, 5, 1]], ![[6, 6, 5, 5, 2, 3], [4, 5, 0, 3, 5, 6]], ![[2, 5, 5, 6, 5, 3], [6, 4, 2, 2, 6, 6]]]
 h' := ![![[6, 2, 5, 4], [0, 0, 0, 1], [0, 1]], ![[1, 3, 3, 5], [1, 1, 3, 5], [6, 2, 5, 4]], ![[3, 1, 6, 5], [5, 4, 3, 4], [1, 3, 3, 5]], ![[0, 1], [5, 2, 1, 4], [3, 1, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [1, 3], []]
 b := ![[], [], [2, 0, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 6, 6, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-89999907366327, 38292617284880, -8838099797989, -32271588088688, 134813689718553]
  a := ![-381, 955, -99, -477, 1931]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12857129623761, 5470373897840, -1262585685427, -81646620994700, 134813689718553]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6055, -1361, 399, 1370, -5834]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![6055, -1361, 399, 1370, -5834]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![6055, -1361, 399, 1370, -5834], ![31124, -7227, 2133, 7217, -30720], ![163624, -38164, 11102, 37703, -160418], ![853004, -194682, 57175, 195058, -830442], ![214866, -49057, 14396, 49121, -209123]]]
  hmulB := by decide  
  f := ![![![32445, -3507, 1855, 5286, -22804]], ![![32153, -6416, 2472, 7423, -31328]], ![![129735, -12629, 7117, 20101, -87046]], ![![430878, -120328, 40529, 124992, -521786]], ![![102494, -27617, 9424, 28985, -121133]]]
  g := ![![![-11, -1361, 399, 1370, -5834], ![-166, -7227, 2133, 7217, -30720], ![-516, -38164, 11102, 37703, -160418], ![-2739, -194682, 57175, 195058, -830442], ![-667, -49057, 14396, 49121, -209123]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-32445, 3507, -1855, -5286, 22804]] ![![6055, -1361, 399, 1370, -5834]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 0, -6, -10, 44]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![35, 0, -6, -10, 44]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![2, 0, 5, 1, 0], ![2, 7, 3, 0, 1]] where
  M :=![![![35, 0, -6, -10, 44], ![-264, 207, -34, -94, 380], ![-1608, -428, 89, 46, -124], ![-824, 1756, -742, -1623, 6876], ![-232, 340, -168, -372, 1587]]]
  hmulB := by decide  
  f := ![![![33209, -5888, 2394, 7118, -30164]], ![![157880, -27995, 11382, 33842, -143412]], ![![750616, -133084, 54111, 160886, -681788]], ![![671638, -119088, 48419, 143963, -610072]], ![![391854, -69479, 28249, 83992, -355933]]]
  g := ![![![-3, -28, -8, -10, 44], ![-76, -223, -64, -94, 380], ![-132, 40, 21, 46, -124], ![-1030, -4216, -1205, -1623, 6876], ![-242, -979, -279, -372, 1587]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [9, 10, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 1, 7], [8, 9, 4], [0, 1]]
 g := ![![[0, 4, 4], [10, 8, 1], []], ![[4, 1, 8, 6], [8, 5, 9, 6], [10, 5]], ![[7, 8, 3, 9], [1, 8, 2, 4], [2, 5]]]
 h' := ![![[0, 1, 7], [9, 4, 2], [0, 0, 1], [0, 1]], ![[8, 9, 4], [5, 0, 2], [9, 9, 9], [0, 1, 7]], ![[0, 1], [1, 7, 7], [2, 2, 1], [8, 9, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 3], []]
 b := ![[], [3, 9, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [9, 10, 3, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![30396557245, -19695176036, 4129269836, 15191371132, -62851387212]
  a := ![469, -1152, 123, 588, -2377]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![11428780855, 38205866768, 10611506892, 15191371132, -62851387212]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33209, -5888, 2394, 7118, -30164]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![33209, -5888, 2394, 7118, -30164]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![1, 6, 1, 0, 0], ![5, 9, 0, 1, 0], ![6, 5, 0, 0, 1]] where
  M :=![![![33209, -5888, 2394, 7118, -30164], ![157880, -27995, 11382, 33842, -143412], ![750616, -133084, 54111, 160886, -681788], ![3568520, -632772, 257266, 764927, -3241524], ![886968, -157276, 63944, 190124, -805687]]]
  hmulB := by decide  
  f := ![![![35, 0, -6, -10, 44]], ![![-264, 207, -34, -94, 380]], ![![-287, 74, -11, -48, 200]], ![![-275, 329, -98, -229, 956]], ![![-122, 125, -34, -82, 341]]]
  g := ![![![16019, 6046, 2394, 7118, -30164], ![76160, 28745, 11382, 33842, -143412], ![362073, 136656, 54111, 160886, -681788], ![1721433, 649719, 257266, 764927, -3241524], ![427866, 161489, 63944, 190124, -805687]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[2, 4], [7, 3], [1]], ![[0, 7], [0, 8], [1]]]
 h' := ![![[5, 10], [1, 2], [8, 5], [0, 1]], ![[0, 1], [0, 9], [0, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [8, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [3, 6, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16898084, 8014052, -1470776, -6352474, 26691107]
  a := ![-641, 1583, -166, -797, 3249]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13073780, -5404051, -1470776, -6352474, 26691107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![35, 0, -6, -10, 44]] ![![33209, -5888, 2394, 7118, -30164]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, -49, 20, 59, -250]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![271, -49, 20, 59, -250]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![4, 1, 1, 0, 0], ![9, 3, 0, 1, 0], ![5, 4, 0, 0, 1]] where
  M :=![![![271, -49, 20, 59, -250], ![1308, -235, 94, 280, -1186], ![6196, -1070, 441, 1316, -5580], ![29272, -5288, 2142, 6341, -26864], ![7274, -1311, 532, 1575, -6673]]]
  hmulB := by decide  
  f := ![![![135, -25, 8, 27, -116]], ![![640, -181, 50, 170, -718]], ![![376, -75, 23, 78, -334]], ![![1579, -428, 120, 410, -1734]], ![![589, -156, 44, 150, -635]]]
  g := ![![![70, 58, 20, 59, -250], ![334, 275, 94, 280, -1186], ![1576, 1297, 441, 1316, -5580], ![7535, 6231, 2142, 6341, -26864], ![1872, 1548, 532, 1575, -6673]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[9, 12], [3], [9, 1]], ![[0, 1], [3], [5, 12]]]
 h' := ![![[9, 12], [6, 8], [9, 4], [0, 1]], ![[0, 1], [0, 5], [6, 9], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [5, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26975, 64738, -12653, -47258, 189819]
  a := ![-59, 141, -15, -75, 299]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-34322, -41547, -12653, -47258, 189819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-103819, -69370, 11432, 42958, -166272]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-103819, -69370, 11432, 42958, -166272]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![4, 6, 1, 0, 0], ![2, 7, 0, 1, 0], ![10, 11, 0, 0, 1]] where
  M :=![![![-103819, -69370, 11432, 42958, -166272], ![542768, 362693, -59772, -224604, 869348], ![-2837896, -1896252, 312497, 1174272, -4545104], ![14836768, 9914344, -1633884, -6139615, 23763872], ![3055660, 2041890, -336504, -1264474, 4894249]]]
  hmulB := by decide  
  f := ![![![-79815, 18434, -5400, -18358, 78136]], ![![-416032, 96065, -28148, -95692, 407292]], ![![-383396, 88546, -25943, -88192, 375368]], ![![-1106022, 255423, -74832, -254399, 1082788]], ![![-632410, 146041, -42788, -145462, 619125]]]
  g := ![![![109789, 106948, 11432, 42958, -166272], ![-574032, -559175, -59772, -224604, 869348], ![3001124, 2923462, 312497, 1174272, -4545104], ![-15691322, -15285203, -1633884, -6139615, 23763872], ![-3231682, -3148039, -336504, -1264474, 4894249]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[4, 12], [3], [4, 1]], ![[0, 1], [3], [8, 12]]]
 h' := ![![[4, 12], [6, 5], [4, 4], [0, 1]], ![[0, 1], [0, 8], [7, 9], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [12, 9, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5362368, 4952210, -940418, -3853038, 15913202]
  a := ![-527, 1296, -134, -662, 2671]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11771280, -10575326, -940418, -3853038, 15913202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![556507, -128535, 37656, 128013, -544856]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![556507, -128535, 37656, 128013, -544856]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![556507, -128535, 37656, 128013, -544856], ![2901112, -670053, 196302, 667338, -2840362], ![15123668, -3493066, 1023345, 3478896, -14807072], ![78841024, -18209612, 5334758, 18135729, -77190304], ![19851330, -4584989, 1343236, 4566385, -19435703]]]
  hmulB := by decide  
  f := ![![![-34189, -22471, 3684, 13869, -53646]], ![![-2370, -1273, 194, 750, -2874]], ![![-79623, -52467, 8609, 32399, -125334]], ![![346304, 234736, -38854, -145775, 564544]], ![![59720, 40849, -6780, -25413, 98451]]]
  g := ![![![266137, -128535, 37656, 128013, -544856], ![1387384, -670053, 196302, 667338, -2840362], ![7232561, -3493066, 1023345, 3478896, -14807072], ![37703878, -18209612, 5334758, 18135729, -77190304], ![9493438, -4584989, 1343236, 4566385, -19435703]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![271, -49, 20, 59, -250]] ![![-103819, -69370, 11432, 42958, -166272]]
  ![![-34189, -22471, 3684, 13869, -53646]] where
 M := ![![![-34189, -22471, 3684, 13869, -53646]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-34189, -22471, 3684, 13869, -53646]] ![![556507, -128535, 37656, 128013, -544856]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4317, -755, 309, 918, -3892]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![4317, -755, 309, 918, -3892]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![5, 4, 15, 1, 0], ![16, 10, 3, 0, 1]] where
  M :=![![![4317, -755, 309, 918, -3892], ![20408, -3671, 1483, 4413, -18692], ![97648, -17060, 6982, 20737, -87922], ![461116, -83026, 33521, 99806, -422718], ![114682, -20591, 8324, 24779, -104959]]]
  hmulB := by decide  
  f := ![![![8785, -2031, 595, 2022, -8606]], ![![45820, -10581, 3099, 10537, -44848]], ![![238792, -55132, 16156, 54925, -233778]], ![![297289, -68653, 20116, 68385, -291066]], ![![95798, -22125, 6482, 22036, -93791]]]
  g := ![![![3647, 2029, -105, 918, -3892], ![17495, 9741, -508, 4413, -18692], ![82395, 45836, -2371, 20737, -87922], ![395622, 220290, -11495, 99806, -422718], ![98243, 54699, -2852, 24779, -104959]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 9, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 4, 16], [16, 12, 1], [0, 1]]
 g := ![![[16, 1, 2], [16, 1], [12, 1], []], ![[12, 6, 14, 1], [12, 15], [5, 8], [4, 1]], ![[0, 13, 12, 4], [9, 2], [7, 16], [2, 1]]]
 h' := ![![[13, 4, 16], [5, 8, 6], [14, 15, 16], [0, 0, 1], [0, 1]], ![[16, 12, 1], [12, 5, 13], [7, 5, 7], [15, 4, 12], [13, 4, 16]], ![[0, 1], [0, 4, 15], [7, 14, 11], [9, 13, 4], [16, 12, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6], []]
 b := ![[], [4, 14, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 9, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8243734716, 4858058163, -1029266105, -3789553901, 15721119967]
  a := ![-293, 721, -77, -367, 1485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14166699099, -8070289759, 508863677, -3789553901, 15721119967]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -22, 3, 13, -50]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-25, -22, 3, 13, -50]] 
 ![![17, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-25, -22, 3, 13, -50], ![156, 133, -21, -77, 298], ![-972, -682, 116, 403, -1562], ![5148, 3290, -579, -2040, 7918], ![1080, 672, -120, -420, 1631]]]
  hmulB := by decide  
  f := ![![![-20609, 4754, -1395, -4739, 20170]], ![![-14803, 3415, -1002, -3404, 14488]], ![![-35342, 8154, -2392, -8127, 34590]], ![![-175167, 40420, -11856, -40283, 171452]], ![![-62584, 14440, -4236, -14392, 61255]]]
  g := ![![![52, -22, 3, 13, -50], ![-310, 133, -21, -77, 298], ![1609, -682, 116, 403, -1562], ![-8076, 3290, -579, -2040, 7918], ![-1660, 672, -120, -420, 1631]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24651, -2516, -1342, -748, 3670]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![24651, -2516, -1342, -748, 3670]] 
 ![![17, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![11, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![24651, -2516, -1342, -748, 3670], ![-29596, 57593, -7332, -18152, 70092], ![-225016, -235552, 54537, 96904, -385672], ![1499920, 265632, -150312, -191759, 795264], ![369004, 29976, -31188, -34840, 147413]]]
  hmulB := by decide  
  f := ![![![-1376325, -969236, 162242, 606340, -2351498]], ![![-513816, -392183, 67108, 248904, -967948]], ![![-2958037, -2068724, 345595, 1292476, -5011202]], ![![11543433, 7368068, -1196738, -4520067, 17463122]], ![![2252760, 1415784, -228780, -865672, 3342317]]]
  g := ![![![3557, -2516, -1342, -748, 3670], ![-43260, 57593, -7332, -18152, 70092], ![152207, -235552, 54537, 96904, -385672], ![-82739, 265632, -150312, -191759, 795264], ![4916, 29976, -31188, -34840, 147413]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![4317, -755, 309, 918, -3892]] ![![-25, -22, 3, 13, -50]]
  ![![-3549, -1331, 168, 703, -2626]] where
 M := ![![![-3549, -1331, 168, 703, -2626]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-3549, -1331, 168, 703, -2626]] ![![24651, -2516, -1342, -748, 3670]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-457555, 722585, -85782, -221901, 853876]]]
 hmul := by decide  
 g := ![![![![-26915, 42505, -5046, -13053, 50228]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-688265, -451557, 73992, 278599, -1077562]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-688265, -451557, 73992, 278599, -1077562]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![12, 4, 11, 10, 1]] where
  M :=![![![-688265, -451557, 73992, 278599, -1077562], ![3499900, 2378333, -393962, -1477724, 5723334], ![-18766972, -12351782, 2025981, 7625660, -29498164], ![95894184, 64972896, -10752978, -40346191, 156246320], ![19704562, 13389333, -2217860, -8319077, 32220327]]]
  hmulB := by decide  
  f := ![![![4593, -16627, 2396, 5497, -21356]], ![![71520, 60077, -14922, -25662, 102502]], ![![-406796, -38866, 35291, 40344, -170032]], ![![870560, -704188, 53414, 188315, -710096]], ![![249278, -401469, 48019, 123629, -475903]]]
  g := ![![![644341, 203089, 627746, 581801, -1077562], ![-3430532, -1079737, -3334244, -3090056, 5723334], ![17642684, 5560046, 17184515, 15926700, -29498164], ![-93634824, -29474336, -91024342, -84358389, 156246320], ![-19312598, -6078525, -18770603, -17395913, 32220327]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [16, 5, 14, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 7, 5, 8], [3, 18, 4, 12], [15, 12, 10, 18], [0, 1]]
 g := ![![[12, 17, 1, 9], [5, 5, 0, 9], [1], []], ![[8, 12, 6, 13], [5, 9, 1, 12, 16, 13], [14, 8, 5], [14, 2, 7]], ![[1, 3, 13, 15, 7, 3], [9, 5, 12, 5, 17, 3], [4, 2, 5], [10, 6, 11]], ![[18, 9, 8, 14, 12, 2], [15, 2, 1, 14, 9, 13], [3, 18, 1], [17, 15, 1]]]
 h' := ![![[17, 7, 5, 8], [15, 18, 8, 16], [3, 14, 5, 16], [0, 0, 1], [0, 1]], ![[3, 18, 4, 12], [1, 1, 17], [11, 2, 9, 17], [8, 3, 15, 9], [17, 7, 5, 8]], ![[15, 12, 10, 18], [2, 1, 13, 9], [13, 5, 10, 10], [1, 0, 2, 9], [3, 18, 4, 12]], ![[0, 1], [2, 18, 0, 13], [14, 17, 14, 14], [10, 16, 1, 1], [15, 12, 10, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 8, 13], []]
 b := ![[], [], [4, 13, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [16, 5, 14, 3, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30386685587016, 9184711931610, -2270449372899, -8220099895430, 34786738780471]
  a := ![-248, 612, -65, -308, 1257]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23569871102772, -6840118062646, -20259188208320, -18741446721060, 34786738780471]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4593, 16627, -2396, -5497, 21356]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-4593, 16627, -2396, -5497, 21356]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-4593, 16627, -2396, -5497, 21356], ![-71520, -60077, 14922, 25662, -102502], ![406796, 38866, -35291, -40344, 170032], ![-870560, 704188, -53414, -188315, 710096], ![-164242, 199289, -20956, -58701, 224581]]]
  hmulB := by decide  
  f := ![![![688265, 451557, -73992, -278599, 1077562]], ![![141815, 88720, -14314, -54193, 209196]], ![![1494878, 982820, -161151, -606634, 2346528]], ![![-4793491, -3253263, 538686, 2020842, -7826494]], ![![-638613, -443274, 73892, 276552, -1071955]]]
  g := ![![![-16691, 16627, -2396, -5497, 21356], ![63587, -60077, 14922, 25662, -102502], ![-54572, 38866, -35291, -40344, 170032], ![-681753, 704188, -53414, -188315, 710096], ![-195997, 199289, -20956, -58701, 224581]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-688265, -451557, 73992, 278599, -1077562]] ![![-4593, 16627, -2396, -5497, 21356]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![-19, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9641, 591, -140, 529, -2476]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![9641, 591, -140, 529, -2476]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![15, 4, 8, 1, 0], ![12, 2, 17, 0, 1]] where
  M :=![![![9641, 591, -140, 529, -2476], ![17824, -7323, 3280, 8522, -36426], ![197140, -72002, 15227, 49362, -206048], ![1013392, -61212, 28960, 148703, -649828], ![261918, -18079, 7248, 37927, -165313]]]
  hmulB := by decide  
  f := ![![![-8411205, 1491109, -606308, -1802697, 7639342]], ![![-39985556, 7091369, -2882912, -8571872, 36324758]], ![![-190118972, 33702266, -13704123, -40745458, 172668468]], ![![-117862693, 20897441, -8496620, -25262782, 107056266]], ![![-158155102, 28037129, -11400341, -33895903, 143641673]]]
  g := ![![![1366, 149, 1640, 529, -2476], ![14222, 1367, 24102, 8522, -36426], ![83882, 6202, 135789, 49362, -206048], ![286121, 27984, 429844, 148703, -649828], ![72903, 6993, 109311, 37927, -165313]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [10, 4, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 19, 22], [10, 3, 1], [0, 1]]
 g := ![![[19, 17, 8], [6, 19, 1], [12, 4, 1], []], ![[7, 19, 11, 19], [13, 6, 7, 20], [9, 3, 11, 14], [12, 1]], ![[2, 2, 19, 6], [17, 20, 20, 18], [8, 15, 9, 16], [10, 1]]]
 h' := ![![[17, 19, 22], [9, 18, 13], [18, 4, 22], [0, 0, 1], [0, 1]], ![[10, 3, 1], [5, 5, 21], [9, 17, 16], [8, 13, 3], [17, 19, 22]], ![[0, 1], [5, 0, 12], [12, 2, 8], [0, 10, 19], [10, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 18], []]
 b := ![[], [4, 13, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [10, 4, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44715686336, -29399125108, 6065395958, 22621063980, -93539517170]
  a := ![501, -1222, 119, 628, -2539]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![35994518812, 2921550144, 61533420696, 22621063980, -93539517170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8411205, -1491109, 606308, 1802697, -7639342]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![8411205, -1491109, 606308, 1802697, -7639342]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![2, 15, 1, 0, 0], ![16, 7, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![8411205, -1491109, 606308, 1802697, -7639342], ![39985556, -7091369, 2882912, 8571872, -36324758], ![190118972, -33702266, 13704123, 40745458, -172668468], ![903779864, -160290904, 65163008, 193752379, -821057212], ![224639250, -39839399, 16196232, 48156875, -204072903]]]
  hmulB := by decide  
  f := ![![![-9641, -591, 140, -529, 2476]], ![![-17824, 7323, -3280, -8522, 36426]], ![![-21034, 7855, -2789, -7750, 32930]], ![![-56192, 4479, -2160, -9427, 41062]], ![![-16837, 452, -236, -1948, 8587]]]
  g := ![![![3376821, -1008896, 606308, 1802697, -7639342], ![16056158, -4797311, 2882912, 8571872, -36324758], ![76324934, -22803579, 13704123, 40745458, -172668468], ![362919980, -108434899, 65163008, 193752379, -821057212], ![90203675, -26951348, 16196232, 48156875, -204072903]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [12, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22], [0, 1]]
 g := ![![[2, 2], [10, 13], [0, 1], [1]], ![[0, 21], [20, 10], [22, 22], [1]]]
 h' := ![![[22, 22], [18, 18], [0, 17], [11, 22], [0, 1]], ![[0, 1], [0, 5], [6, 6], [12, 1], [22, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [12, 1, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2612252, 1530237, -285073, -1196548, 4995002]
  a := ![279, -681, 70, 348, -1414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2079668, 616616, -285073, -1196548, 4995002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![9641, 591, -140, 529, -2476]] ![![8411205, -1491109, 606308, 1802697, -7639342]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0)


lemma PB2201I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB2201I0 : PrimesBelowBoundCertificateInterval O 1 23 2201 where
  m := 9
  g := ![5, 4, 5, 2, 2, 3, 3, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB2201I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC2
    · exact PBC3
    · exact PBC5
    · exact PBC7
    · exact PBC11
    · exact PBC13
    · exact PBC17
    · exact PBC19
    · exact PBC23
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![1331, 121]
    · exact ![169, 169, 13]
    · exact ![4913, 17, 17]
    · exact ![130321, 19]
    · exact ![12167, 529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N1
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N0, I11N1, I13N0, I13N1, I13N2, I17N1, I17N2, I19N1, I23N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N0, I11N1], [I13N0, I13N1, I13N2], [I17N1, I17N2], [I19N1], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
