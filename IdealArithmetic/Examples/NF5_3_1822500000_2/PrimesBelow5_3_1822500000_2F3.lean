
import IdealArithmetic.Examples.NF5_3_1822500000_2.RI5_3_1822500000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-641197, -64047, -74422, -129699, -417042]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-641197, -64047, -74422, -129699, -417042]] 
 ![![107, 0, 0, 0, 0], ![0, 107, 0, 0, 0], ![0, 0, 107, 0, 0], ![0, 0, 0, 107, 0], ![45, 74, 6, 41, 1]] where
  M :=![![![-641197, -64047, -74422, -129699, -417042], ![670680, -595, 59892, 113300, 359658], ![-474192, 152958, -1829, -29636, -81500], ![-177792, -451956, -135970, -179629, -607488], ![476088, 107823, 71268, 116243, 377925]]]
  hmulB := by decide  
  f := ![![![-239, -933, 276, 473, 1444]], ![![-600, -1883, 384, 822, 2534]], ![![-1632, -3678, -159, 940, 3176]], ![![-8544, -7656, -8106, -3975, -10280]], ![![-3849, -4790, -2714, -701, -1401]]]
  g := ![![![169399, 287823, 22690, 158589, -417042], ![-144990, -248741, -19608, -136754, 359658], ![29844, 57794, 4553, 30952, -81500], ![253824, 415908, 32794, 231097, -607488], ![-154491, -260361, -20526, -143726, 377925]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 4 2 6 [74, 82, 37, 31, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 6, 96, 18], [22, 38, 35, 4], [88, 62, 83, 85], [0, 1]]
 g := ![![[93, 44, 87, 64], [97, 33, 82, 3], [86, 86, 34], [75, 47, 61, 87], [68, 76, 1], []], ![[2, 12, 94, 79, 70, 66], [52, 101, 87, 0, 66, 38], [73, 35, 92], [63, 104, 59, 51, 92, 28], [93, 56, 4], [22, 60, 13, 61, 46, 54]], ![[67, 12, 97, 50, 97, 89], [39, 24, 104, 24, 51, 79], [29, 40, 79], [90, 89, 12, 59, 76, 39], [55, 16, 92], [30, 9, 40, 40, 17, 64]], ![[41, 1, 77, 0, 12, 41], [86, 45, 93, 101, 91, 62], [59, 57, 101], [70, 60, 80, 22, 96, 102], [19, 93, 44], [14, 28, 67, 27, 27, 52]]]
 h' := ![![[73, 6, 96, 18], [98, 36, 11, 99], [38, 53, 10, 89], [14, 11, 96, 26], [104, 35, 59, 27], [0, 0, 0, 1], [0, 1]], ![[22, 38, 35, 4], [67, 13, 16, 90], [40, 102, 70, 11], [78, 57, 48, 78], [13, 106, 31, 75], [49, 12, 62, 105], [73, 6, 96, 18]], ![[88, 62, 83, 85], [8, 88, 7, 7], [77, 102, 66, 97], [46, 101, 10, 87], [86, 38, 12, 82], [82, 48, 76, 78], [22, 38, 35, 4]], ![[0, 1], [31, 77, 73, 18], [65, 64, 68, 17], [30, 45, 60, 23], [86, 35, 5, 30], [23, 47, 76, 30], [88, 62, 83, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [61, 61, 13], []]
 b := ![[], [], [4, 86, 93, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 4
  hpos := by decide
  P := [74, 82, 37, 31, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![15569219128334, 884796043913, 22806910716831, 17164939670382, 48848467648159]
  a := ![-180, -61, -183, -126, -395]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20398241355503, -33774783270279, -2526017711889, -18557217139291, 48848467648159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 131079601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![239, 933, -276, -473, -1444]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![239, 933, -276, -473, -1444]] 
 ![![107, 0, 0, 0, 0], ![99, 1, 0, 0, 0], ![43, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![239, 933, -276, -473, -1444], ![600, 1883, -384, -822, -2534], ![1632, 3678, 159, -940, -3176], ![8544, 7656, 8106, 3975, 10280], ![-3408, -4761, -2066, -215, -21]]]
  hmulB := by decide  
  f := ![![![641197, 64047, 74422, 129699, 417042]], ![![586989, 59264, 68298, 118943, 382500]], ![![262109, 24309, 29925, 52399, 168358]], ![![139489, 17991, 17268, 29558, 95322]], ![![97423, 9168, 11158, 19520, 62727]]]
  g := ![![![-419, 933, -276, -473, -1444], ![-1003, 1883, -384, -822, -2534], ![-2745, 3678, 159, -940, -3176], ![-12749, 7656, 8106, 3975, 10280], ![5253, -4761, -2066, -215, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-641197, -64047, -74422, -129699, -417042]] ![![239, 933, -276, -473, -1444]]
  ![![107, 0, 0, 0, 0]] where
 M := ![![![-107, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3689, -14832, 5108, 8246, 25110]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-3689, -14832, 5108, 8246, 25110]] 
 ![![109, 0, 0, 0, 0], ![0, 109, 0, 0, 0], ![0, 0, 109, 0, 0], ![0, 0, 0, 109, 0], ![74, 87, 95, 59, 1]] where
  M :=![![![-3689, -14832, 5108, 8246, 25110], ![-8928, -31775, 9596, 15648, 47368], ![-10176, -59688, 21065, 34108, 103984], ![-39840, -127440, 38564, 62721, 189864], ![20088, 77952, -25188, -40876, -124127]]]
  hmulB := by decide  
  f := ![![![-149, -48, -124, -90, -290]], ![![480, 301, 52, 16, 280]], ![![-5568, -1656, -4971, -3628, -11472]], ![![14112, 10608, -2644, -2819, 376]], ![![3038, 4479, -5789, -4721, -9747]]]
  g := ![![![-17081, -20178, -21838, -13516, 25110], ![-32240, -38099, -41196, -25496, 47368], ![-70688, -83544, -90435, -55972, 103984], ![-129264, -152712, -165124, -102195, 189864], ![84454, 99789, 107953, 66813, -124127]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 4 2 6 [50, 26, 79, 86, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 96, 65, 81], [101, 74, 34, 38], [34, 47, 10, 99], [0, 1]]
 g := ![![[72, 20, 81, 102], [8, 2, 22], [42, 83, 67, 5], [33, 14, 39, 25], [14, 23, 1], []], ![[16, 59, 56, 102, 104, 15], [52, 10, 5], [47, 105, 58, 89, 35, 105], [52, 70, 75, 81, 86, 26], [56, 9, 48], [32, 80, 18, 9, 54, 66]], ![[105, 55, 98, 106, 85, 12], [76, 104, 102], [69, 32, 82, 35, 4, 9], [47, 42, 18, 86, 8, 3], [56, 39, 45], [17, 39, 74, 100, 83, 45]], ![[65, 56, 33, 61, 76, 40], [68, 105, 35], [98, 86, 31, 80, 74, 101], [44, 86, 1, 33, 68, 18], [49, 47, 80], [42, 7, 75, 46, 56, 90]]]
 h' := ![![[106, 96, 65, 81], [5, 84, 70, 50], [80, 106, 49, 26], [94, 13, 79, 88], [63, 12, 99, 5], [0, 0, 0, 1], [0, 1]], ![[101, 74, 34, 38], [45, 25, 72, 78], [47, 42, 52, 21], [89, 74, 53, 80], [98, 77, 12, 93], [8, 49, 67, 87], [106, 96, 65, 81]], ![[34, 47, 10, 99], [22, 30, 34, 47], [15, 44, 19, 50], [92, 35, 91, 102], [7, 17, 90, 78], [55, 44, 65, 46], [101, 74, 34, 38]], ![[0, 1], [50, 79, 42, 43], [17, 26, 98, 12], [74, 96, 104, 57], [83, 3, 17, 42], [35, 16, 86, 84], [34, 47, 10, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [35, 91, 33], []]
 b := ![[], [], [96, 87, 33, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 4
  hpos := by decide
  P := [50, 26, 79, 86, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![124645536979106, 17357384803918, 158162010038338, 118167235558300, 345082608543162]
  a := ![309, 41, 314, 215, 678]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-233132729313898, -275273665673864, -299309044051028, -185703730903562, 345082608543162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 141158161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149, -48, -124, -90, -290]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-149, -48, -124, -90, -290]] 
 ![![109, 0, 0, 0, 0], ![102, 1, 0, 0, 0], ![60, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![43, 0, 0, 0, 1]] where
  M :=![![![-149, -48, -124, -90, -290], ![480, 301, 52, 16, 280], ![-5568, -1656, -4971, -3628, -11472], ![14112, 10608, -2644, -2819, 376], ![-3240, -2976, 1892, 1660, 2333]]]
  hmulB := by decide  
  f := ![![![-3689, -14832, 5108, 8246, 25110]], ![![-3534, -14171, 4868, 7860, 23932]], ![![-2124, -8712, 3005, 4852, 14776]], ![![-3513, -13824, 4712, 7611, 23166]], ![![-1271, -5136, 1784, 2878, 8767]]]
  g := ![![![303, -48, -124, -90, -290], ![-430, 301, 52, 16, 280], ![11856, -1656, -4971, -3628, -11472], ![-6085, 10608, -2644, -2819, 376], ![-623, -2976, 1892, 1660, 2333]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-3689, -14832, 5108, 8246, 25110]] ![![-149, -48, -124, -90, -290]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 164, -67, -97, -292]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![31, 164, -67, -97, -292]] 
 ![![113, 0, 0, 0, 0], ![0, 113, 0, 0, 0], ![74, 16, 1, 0, 0], ![59, 44, 0, 1, 0], ![50, 57, 0, 0, 1]] where
  M :=![![![31, 164, -67, -97, -292], ![24, 331, -201, -245, -726], ![-216, 678, -856, -835, -2410], ![-2280, 1434, -4847, -4046, -11430], ![696, -870, 1794, 1594, 4545]]]
  hmulB := by decide  
  f := ![![![1487, 716, 325, 489, 1612]], ![![-3480, -1285, -663, -1017, -3338]], ![![542, 306, 130, 193, 638]], ![![-691, -158, -110, -171, -558]], ![![-1090, -331, -189, -295, -965]]]
  g := ![![![224, 196, -67, -97, -292], ![581, 493, -201, -245, -726], ![2061, 1668, -856, -835, -2410], ![10324, 8040, -4847, -4046, -11430], ![-4012, -3175, 1794, 1594, 4545]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [60, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 112], [0, 1]]
 g := ![![[19, 81], [62], [88], [44], [21, 18], [103, 1]], ![[0, 32], [62], [88], [44], [67, 95], [93, 112]]]
 h' := ![![[103, 112], [23, 104], [63, 47], [22, 75], [96, 48], [35, 40], [0, 1]], ![[0, 1], [0, 9], [45, 66], [63, 38], [68, 65], [87, 73], [103, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [105, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [60, 10, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1175, -60, 1916, 1433, 3999]
  a := ![-5, -4, -5, -4, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3762, -2847, 1916, 1433, 3999]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![509, 86, 69, 115, 372]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![509, 86, 69, 115, 372]] 
 ![![113, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![87, 0, 1, 0, 0], ![93, 0, 0, 1, 0], ![68, 0, 0, 0, 1]] where
  M :=![![![509, 86, 69, 115, 372], ![-648, -79, -75, -133, -430], ![744, 30, 102, 155, 486], ![-504, 90, 167, 76, 190], ![-312, -72, -112, -122, -373]]]
  hmulB := by decide  
  f := ![![![-1115, -3502, 917, 1657, 4964]], ![![-334, -1107, 305, 537, 1614]], ![![-981, -2856, 689, 1300, 3874]], ![![-423, -2892, 1166, 1725, 5310]], ![![-788, -2020, 410, 852, 2511]]]
  g := ![![![-393, 86, 69, 115, 372], ![444, -79, -75, -133, -430], ![-501, 30, 102, 155, 486], ![-337, 90, 167, 76, 190], ![430, -72, -112, -122, -373]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-20921, 831, -35608, -26951, -74878]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-20921, 831, -35608, -26951, -74878]] 
 ![![113, 0, 0, 0, 0], ![76, 1, 0, 0, 0], ![100, 0, 1, 0, 0], ![84, 0, 0, 1, 0], ![96, 0, 0, 0, 1]] where
  M :=![![![-20921, 831, -35608, -26951, -74878], ![-143400, 6157, -244398, -185110, -514358], ![-983328, 43182, -1676639, -1270170, -3529480], ![-6744720, 297912, -11501188, -8713459, -24212860], ![2327256, -102579, 3968320, 3006393, 8354097]]]
  hmulB := by decide  
  f := ![![![718847, -379521, -36442, -3925, -43696]], ![![490252, -246245, -21510, 1488, -15542]], ![![601036, -354630, -40379, -15626, -78796]], ![![622428, -247752, -10076, 23357, 53764]], ![![594000, -324831, -33094, -6957, -48821]]]
  g := ![![![114415, 831, -35608, -26951, -74878], ![785452, 6157, -244398, -185110, -514358], ![5388700, 43182, -1676639, -1270170, -3529480], ![36965468, 297912, -11501188, -8713459, -24212860], ![-12754328, -102579, 3968320, 3006393, 8354097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2

def I113N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3907, -1567, -2380, -1695, -6058]] i)))

def SI113N3: IdealEqSpanCertificate' Table ![![-3907, -1567, -2380, -1695, -6058]] 
 ![![113, 0, 0, 0, 0], ![100, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-3907, -1567, -2380, -1695, -6058], ![23352, 9935, 14032, 9798, 35090], ![-136704, -57306, -81881, -57508, -206416], ![813408, 340848, 492178, 345375, 1234536], ![-226152, -94893, -136950, -96047, -343177]]]
  hmulB := by decide  
  f := ![![![1901773, 1213217, 492522, 723251, 2396040]], ![![1634924, 1053249, 426140, 625164, 2071466]], ![![1062021, 647079, 266961, 393823, 1303572]], ![![869283, 620499, 242644, 352412, 1169912]], ![![519558, 322293, 132124, 194561, 644221]]]
  g := ![![![5106, -1567, -2380, -1695, -6058], ![-30442, 9935, 14032, 9798, 35090], ![177669, -57306, -81881, -57508, -206416], ![-1063011, 340848, 492178, 345375, 1234536], ![295713, -94893, -136950, -96047, -343177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N3 : Nat.card (O ⧸ I113N3) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N3)

lemma isPrimeI113N3 : Ideal.IsPrime I113N3 := prime_ideal_of_norm_prime hp113.out _ NI113N3
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![31, 164, -67, -97, -292]] ![![509, 86, 69, 115, 372]]
  ![![-349, -6, -490, -380, -1064]] where
 M := ![![![-349, -6, -490, -380, -1064]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-349, -6, -490, -380, -1064]] ![![-20921, 831, -35608, -26951, -74878]]
  ![![576785765, -25548645, 983605650, 745212127, 2070791362]] where
 M := ![![![576785765, -25548645, 983605650, 745212127, 2070791362]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI113N2 : IdealMulLeCertificate' Table 
  ![![576785765, -25548645, 983605650, 745212127, 2070791362]] ![![-3907, -1567, -2380, -1695, -6058]]
  ![![113, 0, 0, 0, 0]] where
 M := ![![![534956980297, -23696111300, 912274281716, 691169201026, 1920617213178]]]
 hmul := by decide  
 g := ![![![![4734132569, -209700100, 8073223732, 6116541602, 16996612506]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2, I113N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
    exact isPrimeI113N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1 ⊙ MulI113N2)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-41, -19, -22, -15, -56]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-41, -19, -22, -15, -56]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![29, 19, 1, 0, 0], ![84, 49, 0, 1, 0], ![19, 75, 0, 0, 1]] where
  M :=![![![-41, -19, -22, -15, -56], ![264, 103, 174, 124, 430], ![-1392, -630, -735, -506, -1908], ![9360, 3636, 6316, 4493, 15452], ![-2640, -1005, -1826, -1303, -4445]]]
  hmulB := by decide  
  f := ![![![2401, 307, 300, 513, 1654]], ![![-2760, -173, -286, -514, -1646]], ![![155, 42, 27, 43, 140]], ![![516, 145, 90, 143, 466]], ![![-1283, -59, -126, -230, -735]]]
  g := ![![![23, 42, -22, -15, -56], ![-184, -327, 174, 124, 430], ![777, 1427, -735, -506, -1908], ![-6652, -11775, 6316, 4493, 15452], ![1923, 3393, -1826, -1303, -4445]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [108, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [102, 126], [0, 1]]
 g := ![![[119, 47], [114, 68], [112, 124], [111, 115], [93, 81], [102, 1]], ![[87, 80], [65, 59], [60, 3], [30, 12], [100, 46], [77, 126]]]
 h' := ![![[102, 126], [7, 38], [96, 24], [77, 39], [116, 49], [33, 9], [0, 1]], ![[0, 1], [73, 89], [4, 103], [118, 88], [34, 78], [62, 118], [102, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [117, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [108, 25, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2516444, 603978, 2595707, 1914021, 5838754]
  a := ![319, 126, 324, 221, 700]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2712387, -4570142, 2595707, 1914021, 5838754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![990155, 344312, 180108, 281484, 921998]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![990155, 344312, 180108, 281484, 921998]] 
 ![![127, 0, 0, 0, 0], ![0, 127, 0, 0, 0], ![26, 5, 1, 0, 0], ![124, 1, 0, 1, 0], ![68, 24, 0, 0, 1]] where
  M :=![![![990155, 344312, 180108, 281484, 921998], ![-1861104, -552211, -313310, -497660, -1625428], ![3178752, 823908, 503453, 810538, 2641120], ![-5028144, -1138416, -752578, -1227567, -3990996], ![840, -84384, -22338, -27778, -95135]]]
  hmulB := by decide  
  f := ![![![-30163, -12824, -17576, -12312, -44662]], ![![185424, 76307, 115626, 81416, 287804]], ![![-7106, -3171, -3769, -2610, -9832]], ![![23252, 8949, 16128, 11469, 39056]], ![![4564, 1760, 3286, 2326, 7809]]]
  g := ![![![-797579, -180832, 180108, 281484, 921998], ![1405700, 319073, -313310, -497660, -1625428], ![-2283574, -518825, 503453, 810538, 2641120], ![3449960, 784535, -752578, -1227567, -3990996], ![82640, 18412, -22338, -27778, -95135]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P1 : CertificateIrreducibleZModOfList' 127 2 2 6 [108, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [114, 126], [0, 1]]
 g := ![![[6, 76], [69, 113], [39, 47], [103, 22], [106, 38], [114, 1]], ![[34, 51], [124, 14], [63, 80], [71, 105], [120, 89], [101, 126]]]
 h' := ![![[114, 126], [41, 40], [106, 42], [52, 38], [109, 28], [7, 61], [0, 1]], ![[0, 1], [29, 87], [68, 85], [66, 89], [126, 99], [103, 66], [114, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [72, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N1 : CertifiedPrimeIdeal' SI127N1 127 where
  n := 2
  hpos := by decide
  P := [108, 13, 1]
  hirr := P127P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3835602, 985799, 3797821, 2792850, 8604582]
  a := ![-391, -131, -396, -270, -858]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8081360, -1789812, 3797821, 2792850, 8604582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N1 B_one_repr
lemma NI127N1 : Nat.card (O ⧸ I127N1) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 9, -36, -33, -108]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-35, 9, -36, -33, -108]] 
 ![![127, 0, 0, 0, 0], ![103, 1, 0, 0, 0], ![59, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![34, 0, 0, 0, 1]] where
  M :=![![![-35, 9, -36, -33, -108], ![216, 145, 84, 42, 186], ![-1440, -450, -1067, -792, -2664], ![6912, 3528, 3006, 1957, 8064], ![-1872, -1053, -702, -423, -1895]]]
  hmulB := by decide  
  f := ![![![-207197, -50985, -32094, -51933, -169074]], ![![-165533, -40814, -25662, -41517, -135168]], ![![-99841, -24327, -15401, -24945, -81198]], ![![-26297, -6993, -4212, -6764, -22050]], ![![-54974, -13455, -8496, -13755, -44777]]]
  g := ![![![43, 9, -36, -33, -108], ![-211, 145, 84, 42, 186], ![1681, -450, -1067, -792, -2664], ![-6655, 3528, 3006, 1957, 8064], ![1736, -1053, -702, -423, -1895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-41, -19, -22, -15, -56]] ![![990155, 344312, 180108, 281484, 921998]]
  ![![207197, 50985, 32094, 51933, 169074]] where
 M := ![![![207197, 50985, 32094, 51933, 169074]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![207197, 50985, 32094, 51933, 169074]] ![![-35, 9, -36, -33, -108]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2441, -405, -326, -547, -1770]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-2441, -405, -326, -547, -1770]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![122, 113, 1, 0, 0], ![100, 60, 0, 1, 0], ![85, 118, 0, 0, 1]] where
  M :=![![![-2441, -405, -326, -547, -1770], ![3096, 361, 374, 644, 2074], ![-3408, -114, -329, -610, -1948], ![2832, -516, 160, 339, 1020], ![1320, 357, 198, 331, 1085]]]
  hmulB := by decide  
  f := ![![![221, 561, -112, -235, -692]], ![![-312, 809, -678, -790, -2530]], ![![-34, 1247, -679, -898, -2814]], ![![-116, 768, -496, -621, -1964]], ![![-101, 1090, -652, -836, -2633]]]
  g := ![![![1851, 2123, -326, -547, -1770], ![-2162, -2483, 374, 644, 2074], ![2010, 2317, -329, -610, -1948], ![-1048, -1216, 160, 339, 1020], ![-1131, -1297, 198, 331, 1085]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [3, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 130], [0, 1]]
 g := ![![[36, 44], [63, 77], [64], [4], [5], [5], [1]], ![[0, 87], [0, 54], [64], [4], [5], [5], [1]]]
 h' := ![![[23, 130], [73, 31], [56, 83], [36, 8], [21, 129], [125, 108], [128, 23], [0, 1]], ![[0, 1], [0, 100], [0, 48], [89, 123], [106, 2], [120, 23], [2, 108], [23, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [109, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [3, 108, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1862163, 725568, 1269188, 898932, 3092060]
  a := ![216, 72, 220, 140, 474]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3860283, -4286196, 1269188, 898932, 3092060]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-67, 4, -2, -8, -26]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-67, 4, -2, -8, -26]] 
 ![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![29, 88, 1, 0, 0], ![68, 14, 0, 1, 0], ![55, 19, 0, 0, 1]] where
  M :=![![![-67, 4, -2, -8, -26], ![48, -25, 18, 14, 36], ![144, 60, 169, 142, 412], ![336, -156, 950, 677, 1836], ![-120, 24, -336, -244, -669]]]
  hmulB := by decide  
  f := ![![![79, 100, 14, -12, -22]], ![![-336, -11, -270, -234, -796]], ![![-191, 24, -169, -154, -518]], ![![-92, 14, -82, -75, -252]], ![![11, 49, -16, -26, -79]]]
  g := ![![![15, 6, -2, -8, -26], ![-26, -19, 18, 14, 36], ![-283, -188, 169, 142, 412], ![-1330, -978, 950, 677, 1836], ![481, 349, -336, -244, -669]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P1 : CertificateIrreducibleZModOfList' 131 2 2 7 [124, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 130], [0, 1]]
 g := ![![[69, 13], [80, 7], [99], [27], [33], [109], [1]], ![[60, 118], [55, 124], [99], [27], [33], [109], [1]]]
 h' := ![![[90, 130], [36, 12], [112, 111], [27, 19], [121, 114], [26, 66], [7, 90], [0, 1]], ![[0, 1], [68, 119], [15, 20], [34, 112], [32, 17], [71, 65], [116, 41], [90, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [15, 87]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N1 : CertifiedPrimeIdeal' SI131N1 131 where
  n := 2
  hpos := by decide
  P := [124, 41, 1]
  hirr := P131P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8949304, 1579822, 10585615, 7873553, 23312938]
  a := ![619, 214, 629, 437, 1358]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16149975, -11321602, 10585615, 7873553, 23312938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N1 B_one_repr
lemma NI131N1 : Nat.card (O ⧸ I131N1) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1201, 1759, 66, -373, -934]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![1201, 1759, 66, -373, -934]] 
 ![![131, 0, 0, 0, 0], ![61, 1, 0, 0, 0], ![78, 0, 1, 0, 0], ![89, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![1201, 1759, 66, -373, -934], ![-4440, 655, -3988, -3640, -12234], ![31536, 18306, 16317, 9756, 36580], ![-175488, -63540, -110846, -81163, -287552], ![47784, 13689, 32072, 24633, 86215]]]
  hmulB := by decide  
  f := ![![![125771, 23653, 17568, 29127, 94412]], ![![57277, 10824, 8016, 13283, 43058]], ![![76446, 14220, 10645, 17658, 57224]], ![![83921, 16111, 11870, 19586, 63484]], ![![108978, 20451, 15190, 25209, 81717]]]
  g := ![![![217, 1759, 66, -373, -934], ![15155, 655, -3988, -3640, -12234], ![-56460, 18306, 16317, 9756, 36580], ![399625, -63540, -110846, -81163, -287552], ![-116868, 13689, 32072, 24633, 86215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-2441, -405, -326, -547, -1770]] ![![-67, 4, -2, -8, -26]]
  ![![125771, 23653, 17568, 29127, 94412]] where
 M := ![![![125771, 23653, 17568, 29127, 94412]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![125771, 23653, 17568, 29127, 94412]] ![![1201, 1759, 66, -373, -934]]
  ![![131, 0, 0, 0, 0]] where
 M := ![![![131, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -2, 28, 20, 56]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![11, -2, 28, 20, 56]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![0, 0, 137, 0, 0], ![93, 97, 77, 1, 0], ![126, 117, 110, 0, 1]] where
  M :=![![![11, -2, 28, 20, 56], ![96, -13, 170, 132, 360], ![864, 24, 1343, 1010, 2856], ![4176, -600, 8066, 6147, 16780], ![-1488, 186, -2818, -2144, -5873]]]
  hmulB := by decide  
  f := ![![![187, 34, 32, 52, 168]], ![![-288, -77, -34, -56, -184]], ![![384, 24, 67, 110, 352]], ![![135, -19, 35, 57, 180]], ![![234, -15, 54, 88, 279]]]
  g := ![![![-65, -62, -56, 20, 56], ![-420, -401, -362, 132, 360], ![-3306, -3154, -2851, 1010, 2856], ![-19575, -18687, -16869, 6147, 16780], ![6846, 6535, 5900, -2144, -5873]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [120, 73, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 110, 38], [28, 26, 99], [0, 1]]
 g := ![![[53, 117, 15], [37, 36], [19, 112], [84, 65, 109], [85, 25], [107, 1], []], ![[102, 16, 10, 130], [129, 15], [1, 109], [103, 56, 19, 32], [108, 88], [130, 128], [112, 74]], ![[98, 73, 40, 38], [84, 118], [85, 50], [50, 44], [73, 126], [10, 44], [51, 74]]]
 h' := ![![[79, 110, 38], [88, 61, 17], [125, 36, 6], [58, 49, 89], [12, 18, 66], [38, 15, 5], [0, 0, 1], [0, 1]], ![[28, 26, 99], [70, 25, 20], [53, 13, 17], [131, 113, 66], [46, 74, 71], [26, 119, 15], [62, 50, 26], [79, 110, 38]], ![[0, 1], [134, 51, 100], [79, 88, 114], [135, 112, 119], [19, 45], [82, 3, 117], [7, 87, 110], [28, 26, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114, 44], []]
 b := ![[], [2, 106, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [120, 73, 30, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![64483768, 24778114, 44282787, 31538089, 107836938]
  a := ![41, 10, 42, 27, 90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-120116881, -114243345, -103986958, 31538089, 107836938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, 34, 32, 52, 168]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![187, 34, 32, 52, 168]] 
 ![![137, 0, 0, 0, 0], ![0, 137, 0, 0, 0], ![33, 60, 1, 0, 0], ![75, 132, 0, 1, 0], ![129, 5, 0, 0, 1]] where
  M :=![![![187, 34, 32, 52, 168], ![-288, -77, -34, -56, -184], ![384, 24, 67, 110, 352], ![-528, -144, -42, -65, -220], ![-48, 30, -26, -44, -137]]]
  hmulB := by decide  
  f := ![![![11, -2, 28, 20, 56]], ![![96, -13, 170, 132, 360]], ![![51, -6, 91, 70, 192]], ![![129, -18, 238, 183, 500]], ![![3, -1, 12, 8, 23]]]
  g := ![![![-193, -70, 32, 52, 168], ![210, 75, -34, -56, -184], ![-405, -148, 67, 110, 352], ![249, 88, -42, -65, -220], ![159, 59, -26, -44, -137]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P1 : CertificateIrreducibleZModOfList' 137 2 2 7 [73, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 136], [0, 1]]
 g := ![![[49, 122], [78], [37], [35, 38], [112], [88], [1]], ![[0, 15], [78], [37], [13, 99], [112], [88], [1]]]
 h' := ![![[122, 136], [119, 81], [14, 30], [48, 96], [45, 60], [1, 48], [64, 122], [0, 1]], ![[0, 1], [0, 56], [112, 107], [115, 41], [104, 77], [103, 89], [15, 15], [122, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [127, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N1 : CertifiedPrimeIdeal' SI137N1 137 where
  n := 2
  hpos := by decide
  P := [73, 15, 1]
  hirr := P137P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5404357, 1437021, 5243589, 3848808, 11919036]
  a := ![453, 153, 463, 312, 994]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14553652, -6429315, 5243589, 3848808, 11919036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N1 B_one_repr
lemma NI137N1 : Nat.card (O ⧸ I137N1) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![11, -2, 28, 20, 56]] ![![187, 34, 32, 52, 168]]
  ![![137, 0, 0, 0, 0]] where
 M := ![![![137, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35525, 455354, 124128, 156676, 534894]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![35525, 455354, 124128, 156676, 534894]] 
 ![![139, 0, 0, 0, 0], ![0, 139, 0, 0, 0], ![0, 0, 139, 0, 0], ![43, 6, 132, 1, 0], ![104, 107, 20, 0, 1]] where
  M :=![![![35525, 455354, 124128, 156676, 534894], ![-1556784, -1018297, -409860, -600376, -1989892], ![4530336, 1943220, 921771, 1409612, 4635192], ![-9752544, -3355704, -1764520, -2760701, -9040904], ![1328664, 145206, 157532, 272890, 878327]]]
  hmulB := by decide  
  f := ![![![-961, -1070, -656, -208, -518]], ![![-2544, -1291, -4340, -2768, -6964]], ![![-32160, -6300, -43183, -31316, -89144]], ![![-31777, -6236, -43140, -31237, -88646]], ![![-6992, -2721, -9436, -6338, -17349]]]
  g := ![![![-448421, -415240, -224856, 156676, 534894], ![1663368, 1550377, 853508, -600376, -1989892], ![-3871532, -3614964, -1998927, 1409612, 4635192], ![7548285, 7054570, 3909828, -2760701, -9040904], ![-732026, -686857, -384392, 272890, 878327]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [57, 63, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 79, 132], [59, 59, 7], [0, 1]]
 g := ![![[26, 32, 29], [81, 114, 31], [50, 116], [0, 66, 55], [10, 29], [106, 1], []], ![[106, 68, 50, 103], [138, 128, 108, 104], [80, 34], [134, 48, 134, 15], [43, 31], [21, 6], [57, 49]], ![[10, 16, 49, 57], [105, 59, 57, 30], [91, 36], [100, 4, 122, 57], [10, 49], [124, 125], [43, 49]]]
 h' := ![![[47, 79, 132], [109, 110, 86], [69, 107, 93], [0, 4, 33], [41, 69, 65], [74, 76, 53], [0, 0, 1], [0, 1]], ![[59, 59, 7], [73, 29, 134], [118, 136, 12], [62, 91, 112], [41, 67, 16], [95, 70, 93], [72, 69, 59], [47, 79, 132]], ![[0, 1], [103, 0, 58], [7, 35, 34], [32, 44, 133], [33, 3, 58], [73, 132, 132], [57, 70, 79], [59, 59, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 83], []]
 b := ![[], [84, 132, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [57, 63, 33, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8238750058, 1520207742, 9567450558, 7111707809, 21139623036]
  a := ![247, 84, 250, 171, 542]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-17957449507, -16568990676, -9726406050, 7111707809, 21139623036]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -156, -57, -81, -270]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-173, -156, -57, -81, -270]] 
 ![![139, 0, 0, 0, 0], ![66, 1, 0, 0, 0], ![92, 0, 1, 0, 0], ![44, 0, 0, 1, 0], ![125, 0, 0, 0, 1]] where
  M :=![![![-173, -156, -57, -81, -270], ![648, 313, 141, 213, 702], ![-1512, -558, -284, -441, -1446], ![2952, 918, 507, 802, 2622], ![-288, -18, -30, -54, -173]]]
  hmulB := by decide  
  f := ![![![-263, -60, -195, -153, -522]], ![![-114, -23, -87, -69, -234]], ![![-244, -66, -176, -135, -462]], ![![284, 150, 129, 82, 330]], ![![-337, -102, -225, -171, -599]]]
  g := ![![![379, -156, -57, -81, -270], ![-936, 313, 141, 213, 702], ![1882, -558, -284, -441, -1446], ![-3362, 918, 507, 802, 2622], ![199, -18, -30, -54, -173]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1099, 14, -89, -173, -548]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-1099, 14, -89, -173, -548]] 
 ![![139, 0, 0, 0, 0], ![80, 1, 0, 0, 0], ![133, 0, 1, 0, 0], ![63, 0, 0, 1, 0], ![80, 0, 0, 0, 1]] where
  M :=![![![-1099, 14, -89, -173, -548], ![696, -319, -11, 29, 66], ![504, 798, 280, 383, 1282], ![-3192, -1842, -729, -1082, -3586], ![1224, 276, 154, 256, 835]]]
  hmulB := by decide  
  f := ![![![-2497, -458, -2907, -2161, -6420]], ![![-1448, -239, -1749, -1303, -3842]], ![![-3127, -548, -3701, -2754, -8154]], ![![-2277, 684, -5270, -4035, -10786]], ![![-920, -520, -236, -138, -793]]]
  g := ![![![463, 14, -89, -173, -548], ![148, -319, -11, 29, 66], ![-1635, 798, 280, 383, 1282], ![4289, -1842, -729, -1082, -3586], ![-894, 276, 154, 256, 835]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![35525, 455354, 124128, 156676, 534894]] ![![-173, -156, -57, -81, -270]]
  ![![409700111, 201920954, 90315549, 136142305, 448845480]] where
 M := ![![![409700111, 201920954, 90315549, 136142305, 448845480]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![409700111, 201920954, 90315549, 136142305, 448845480]] ![![-1099, 14, -89, -173, -548]]
  ![![139, 0, 0, 0, 0]] where
 M := ![![![-149383771349, -113497948000, -43521623078, -62833087400, -208824673976]]]
 hmul := by decide  
 g := ![![![![-1074703391, -816532000, -313105202, -452036600, -1502335784]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21583, -13765, -5582, -8205, -27180]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-21583, -13765, -5582, -8205, -27180]] 
 ![![149, 0, 0, 0, 0], ![0, 149, 0, 0, 0], ![0, 0, 149, 0, 0], ![0, 0, 0, 149, 0], ![115, 61, 66, 29, 1]] where
  M :=![![![-21583, -13765, -5582, -8205, -27180], ![61560, 26117, 12410, 19048, 62610], ![-131184, -44778, -23409, -36950, -120916], ![241584, 70260, 38940, 63747, 207700], ![-17856, 141, -1186, -2869, -8967]]]
  hmulB := by decide  
  f := ![![![-1427, -5953, 1944, 3153, 9578]], ![![-2856, -11957, 3922, 6346, 19274]], ![![-5664, -24018, 7999, 12838, 38968]], ![![-10896, -48264, 16892, 26411, 80004]], ![![-6853, -29319, 9868, 15749, 47783]]]
  g := ![![![20833, 11035, 12002, 5235, -27180], ![-47910, -25457, -27650, -12058, 62610], ![92444, 49202, 53403, 23286, -120916], ![-158684, -84560, -91740, -39997, 207700], ![6801, 3672, 3964, 1726, -8967]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 4 2 7 [58, 18, 49, 92, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 82, 13, 28], [44, 125, 22, 130], [108, 90, 114, 140], [0, 1]]
 g := ![![[71, 61, 54, 73], [59, 138, 124], [140, 3, 76, 31], [66, 76, 73], [93, 89, 62, 120], [1], []], ![[32, 142, 35, 133, 130, 113], [92, 64, 4], [97, 58, 74, 111, 69, 145], [47, 107, 4], [145, 5, 78, 43, 80, 113], [25, 43, 68], [5, 120, 39]], ![[24, 102, 146, 19, 121, 125], [37, 104, 73], [6, 46, 119, 97, 72, 129], [89, 1, 145], [140, 50, 15, 73, 86, 127], [85, 36, 16], [86, 73, 63]], ![[127, 84, 33, 22, 84, 47], [134, 10, 107], [111, 129, 144, 45, 23, 64], [63, 45, 37], [125, 43, 105, 106, 93, 17], [138, 32, 123], [142, 32, 81]]]
 h' := ![![[54, 82, 13, 28], [117, 33, 145, 85], [75, 10, 96, 71], [52, 84, 100, 110], [119, 104, 81, 64], [91, 131, 100, 57], [0, 0, 1], [0, 1]], ![[44, 125, 22, 130], [24, 53, 71, 13], [61, 31, 41, 147], [58, 54, 59, 95], [20, 51, 7, 2], [47, 106, 109, 13], [93, 18, 34, 51], [54, 82, 13, 28]], ![[108, 90, 114, 140], [93, 9, 61, 8], [2, 75, 30, 64], [120, 11, 146, 111], [31, 63, 135, 61], [105, 122, 105, 3], [77, 3, 35, 145], [44, 125, 22, 130]], ![[0, 1], [126, 54, 21, 43], [1, 33, 131, 16], [106, 0, 142, 131], [83, 80, 75, 22], [43, 88, 133, 76], [1, 128, 79, 102], [108, 90, 114, 140]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [125, 116, 95], []]
 b := ![[], [], [96, 74, 119, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 4
  hpos := by decide
  P := [58, 18, 49, 92, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50373637803554, 704525345868, 78922607753796, 59581186903638, 167709432680184]
  a := ![232, 80, 235, 164, 509]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-129102088056494, -68654838041244, -73757717779452, -32241559468602, 167709432680184]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 492884401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1427, 5953, -1944, -3153, -9578]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![1427, 5953, -1944, -3153, -9578]] 
 ![![149, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![1427, 5953, -1944, -3153, -9578], ![2856, 11957, -3922, -6346, -19274], ![5664, 24018, -7999, -12838, -38968], ![10896, 48264, -16892, -26411, -80004], ![-7032, -30285, 10272, 16327, 49521]]]
  hmulB := by decide  
  f := ![![![21583, 13765, 5582, 8205, 27180]], ![![12189, 7862, 3176, 4663, 15450]], ![![5226, 3072, 1281, 1900, 6284]], ![![8808, 6180, 2436, 3537, 11740]], ![![3886, 2401, 982, 1451, 4803]]]
  g := ![![![120, 5953, -1944, -3153, -9578], ![257, 11957, -3922, -6346, -19274], ![628, 24018, -7999, -12838, -38968], ![2016, 48264, -16892, -26411, -80004], ![-963, -30285, 10272, 16327, 49521]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-21583, -13765, -5582, -8205, -27180]] ![![1427, 5953, -1944, -3153, -9578]]
  ![![149, 0, 0, 0, 0]] where
 M := ![![![-149, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-167, 598, -273, -443, -1364]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-167, 598, -273, -443, -1364]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![0, 0, 151, 0, 0], ![106, 104, 51, 1, 0], ![34, 28, 66, 0, 1]] where
  M :=![![![-167, 598, -273, -443, -1364], ![840, 1477, -369, -599, -1794], ![-72, 2610, -988, -1615, -4942], ![2328, 5646, -1619, -2666, -8070], ![-744, -3420, 1128, 1846, 5619]]]
  hmulB := by decide  
  f := ![![![-593, -250, -359, -251, -900]], ![![3528, 1483, 2127, 1491, 5342]], ![![-20856, -8766, -12540, -8795, -31522]], ![![-4214, -1772, -2531, -1775, -6364]], ![![-8822, -3708, -5304, -3720, -13333]]]
  g := ![![![617, 562, 744, -443, -1364], ![830, 755, 984, -599, -1794], ![2246, 2046, 2699, -1615, -4942], ![3704, 3370, 4417, -2666, -8070], ![-2566, -2336, -3072, 1846, 5619]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [28, 64, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 100, 144], [69, 50, 7], [0, 1]]
 g := ![![[3, 22, 25], [34, 76, 58], [58, 91, 144], [56, 5], [11, 77, 100], [136, 1], []], ![[101, 114, 13, 43], [3, 112, 13, 11], [69, 84, 48, 1], [137, 95], [130, 15, 76, 20], [43, 84], [130, 49]], ![[104, 0, 123, 142], [108, 29, 91, 77], [83, 114, 37, 115], [82, 136], [101, 21, 136, 51], [55, 34], [116, 49]]]
 h' := ![![[67, 100, 144], [105, 85, 5], [37, 113, 71], [129, 12, 12], [145, 41, 55], [118, 26, 10], [0, 0, 1], [0, 1]], ![[69, 50, 7], [79, 11, 108], [88, 50, 41], [98, 94, 63], [59, 113, 47], [82, 118, 16], [94, 84, 50], [67, 100, 144]], ![[0, 1], [96, 55, 38], [44, 139, 39], [87, 45, 76], [119, 148, 49], [130, 7, 125], [3, 67, 100], [69, 50, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 16], []]
 b := ![[], [148, 100, 67], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [28, 64, 15, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31281427836, -7717531493, -31701373282, -23356777177, -71556352820]
  a := ![-359, -113, -376, -246, -788]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![32301012906, 29304405125, 38955056615, -23356777177, -71556352820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![593, 250, 359, 251, 900]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![593, 250, 359, 251, 900]] 
 ![![151, 0, 0, 0, 0], ![0, 151, 0, 0, 0], ![36, 100, 1, 0, 0], ![24, 2, 0, 1, 0], ![14, 86, 0, 0, 1]] where
  M :=![![![593, 250, 359, 251, 900], ![-3528, -1483, -2127, -1491, -5342], ![20856, 8766, 12540, 8795, 31522], ![-123288, -51762, -74205, -52062, -186490], ![34248, 14376, 20614, 14464, 51807]]]
  hmulB := by decide  
  f := ![![![167, -598, 273, 443, 1364]], ![![-840, -1477, 369, 599, 1794]], ![![-516, -1138, 316, 513, 1546]], ![![0, -152, 59, 96, 294]], ![![-458, -874, 228, 370, 1111]]]
  g := ![![![-205, -752, 359, 251, 900], ![1216, 4461, -2127, -1491, -5342], ![-7172, -26316, 12540, 8795, 31522], ![42440, 155702, -74205, -52062, -186490], ![-11790, -43254, 20614, 14464, 51807]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P1 : CertificateIrreducibleZModOfList' 151 2 2 7 [27, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 150], [0, 1]]
 g := ![![[45, 74], [2, 19], [79, 4], [95], [128, 17], [49], [1]], ![[131, 77], [20, 132], [51, 147], [95], [9, 134], [49], [1]]]
 h' := ![![[144, 150], [97, 136], [132, 64], [140, 2], [17, 104], [10, 35], [124, 144], [0, 1]], ![[0, 1], [51, 15], [137, 87], [126, 149], [44, 47], [67, 116], [22, 7], [144, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [146, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N1 : CertifiedPrimeIdeal' SI151N1 151 where
  n := 2
  hpos := by decide
  P := [27, 7, 1]
  hirr := P151P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1242797, 286314, 1310597, 967715, 2938182]
  a := ![-221, -70, -227, -154, -485]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-730453, -2552268, 1310597, 967715, 2938182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N1 B_one_repr
lemma NI151N1 : Nat.card (O ⧸ I151N1) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-167, 598, -273, -443, -1364]] ![![593, 250, 359, 251, 900]]
  ![![151, 0, 0, 0, 0]] where
 M := ![![![-151, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB2088I3_primes (p : ℕ) :
  p ∈ Set.range ![107, 109, 113, 127, 131, 137, 139, 149, 151] ↔ Nat.Prime p ∧ 103 < p ∧ p ≤ 151 := by
  rw [← List.mem_ofFn']
  convert primes_range 103 151 (by omega)

def PB2088I3 : PrimesBelowBoundCertificateInterval O 103 151 2088 where
  m := 9
  g := ![2, 2, 4, 3, 3, 2, 3, 2, 2]
  P := ![107, 109, 113, 127, 131, 137, 139, 149, 151]
  hP := PB2088I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2, I113N3]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
    · exact ![I139N0, I139N1, I139N2]
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
    · exact ![131079601, 107]
    · exact ![141158161, 109]
    · exact ![12769, 113, 113, 113]
    · exact ![16129, 16129, 127]
    · exact ![17161, 17161, 131]
    · exact ![2571353, 18769]
    · exact ![2685619, 139, 139]
    · exact ![492884401, 149]
    · exact ![3442951, 22801]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
      exact NI113N3
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
  β := ![I107N1, I109N1, I113N1, I113N2, I113N3, I127N2, I131N2, I139N1, I139N2, I149N1]
  Il := ![[I107N1], [I109N1], [I113N1, I113N2, I113N3], [I127N2], [I131N2], [], [I139N1, I139N2], [I149N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
