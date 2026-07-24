
import IdealArithmetic.Examples.NF5_3_405000000_1.RI5_3_405000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp829 : Fact (Nat.Prime 829) := {out := by norm_num}

def I829N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13947, -35671, 6101, -1370, 4554]] i)))

def SI829N0: IdealEqSpanCertificate' Table ![![13947, -35671, 6101, -1370, 4554]] 
 ![![829, 0, 0, 0, 0], ![0, 829, 0, 0, 0], ![690, 41, 1, 0, 0], ![725, 667, 0, 1, 0], ![12, 601, 0, 0, 1]] where
  M :=![![![13947, -35671, 6101, -1370, 4554], ![2740, -7009, 1205, -267, 888], ![534, -1346, 182, -37, 174], ![74, -236, 109, -92, 126], ![3524, -9062, 1681, -373, 1127]]]
  hmulB := by decide  
  f := ![![![-2299, 15731, -4179, 430, -2508]], ![![-860, 8593, -5551, -23, -2436]], ![![-1956, 13529, -3769, 356, -2214]], ![![-2701, 20694, -8167, 355, -4170]], ![![-656, 6473, -4114, -12, -1813]]]
  g := ![![![-3929, -2544, 6101, -1370, 4554], ![-779, -497, 1205, -267, 888], ![-121, -107, 182, -37, 174], ![-12, -23, 109, -92, 126], ![-1085, -611, 1681, -373, 1127]]]
  hle1 := by decide   
  hle2 := by decide  


def P829P0 : CertificateIrreducibleZModOfList' 829 2 2 9 [437, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [777, 828], [0, 1]]
 g := ![![[76, 240], [769], [293, 291], [51, 522], [175, 60], [9, 813], [322], [318], [777, 1]], ![[31, 589], [769], [83, 538], [264, 307], [371, 769], [12, 16], [322], [318], [725, 828]]]
 h' := ![![[777, 828], [216, 528], [454, 282], [96, 266], [622, 505], [212, 565], [230, 155], [527, 53], [341, 609], [0, 1]], ![[0, 1], [117, 301], [712, 547], [357, 563], [61, 324], [676, 264], [460, 674], [258, 776], [175, 220], [777, 828]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [718]]
 b := ![[], [215, 359]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI829N0 : CertifiedPrimeIdeal' SI829N0 829 where
  n := 2
  hpos := by decide
  P := [437, 52, 1]
  hirr := P829P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1464, -8821, 15723, -3178, 441]
  a := ![5, -6, -8, 4, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10312, 1449, 15723, -3178, 441]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI829N0 : Ideal.IsPrime I829N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI829N0 B_one_repr
lemma NI829N0 : Nat.card (O ⧸ I829N0) = 687241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI829N0

def I829N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -27, -79, 34, -8]] i)))

def SI829N1: IdealEqSpanCertificate' Table ![![25, -27, -79, 34, -8]] 
 ![![829, 0, 0, 0, 0], ![0, 829, 0, 0, 0], ![739, 777, 1, 0, 0], ![294, 522, 0, 1, 0], ![788, 352, 0, 0, 1]] where
  M :=![![![25, -27, -79, 34, -8], ![-68, 125, 3, -131, 188], ![262, -1082, 1424, -111, -410], ![222, 1680, -5105, 2466, -1486], ![-848, 2900, -3157, -245, 1615]]]
  hmulB := by decide  
  f := ![![![26663, -170013, 30637, -5798, 22366]], ![![11596, -74397, 13887, -2499, 9944]], ![![34643, -221326, 40336, -7512, 29264]], ![![16760, -107160, 19619, -3630, 14198]], ![![30272, -193222, 35027, -6573, 25487]]]
  g := ![![![66, 56, -79, 34, -8], ![-135, 0, 3, -131, 188], ![-840, -1092, 1424, -111, -410], ![5089, 3865, -5105, 2466, -1486], ![1365, 2431, -3157, -245, 1615]]]
  hle1 := by decide   
  hle2 := by decide  


def P829P1 : CertificateIrreducibleZModOfList' 829 2 2 9 [642, 518, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [311, 828], [0, 1]]
 g := ![![[742, 696], [768], [697, 361], [779, 663], [498, 232], [580, 55], [767], [593], [311, 1]], ![[0, 133], [768], [224, 468], [551, 166], [527, 597], [276, 774], [767], [593], [622, 828]]]
 h' := ![![[311, 828], [806, 184], [186, 232], [598, 19], [278, 385], [690, 216], [341, 682], [183, 349], [127, 744], [0, 1]], ![[0, 1], [0, 645], [215, 597], [704, 810], [637, 444], [717, 613], [219, 147], [123, 480], [220, 85], [311, 828]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [620]]
 b := ![[], [706, 310]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI829N1 : CertifiedPrimeIdeal' SI829N1 829 where
  n := 2
  hpos := by decide
  P := [642, 518, 1]
  hirr := P829P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1608, -34343, 19986, -7276, 10449]
  a := ![-6, -55, 11, -7, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25170, -18629, 19986, -7276, 10449]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI829N1 : Ideal.IsPrime I829N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI829N1 B_one_repr
lemma NI829N1 : Nat.card (O ⧸ I829N1) = 687241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI829N1

def I829N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112109, 711882, -122518, 24730, -91772]] i)))

def SI829N2: IdealEqSpanCertificate' Table ![![-112109, 711882, -122518, 24730, -91772]] 
 ![![829, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![708, 0, 1, 0, 0], ![502, 0, 0, 1, 0], ![547, 0, 0, 0, 1]] where
  M :=![![![-112109, 711882, -122518, 24730, -91772], ![-49460, 304439, -39876, 11566, -35164], ![-23132, 114328, 22661, 7320, -932], ![-14640, -4764, 127900, 9885, 42056], ![-17492, 49880, 70988, 8026, 19519]]]
  hmulB := by decide  
  f := ![![![-206833, 531726, -95870, 24262, -71396]], ![![-2803, 7209, -1318, 320, -944]], ![![-176640, 454040, -81699, 20672, -60980]], ![![-125150, 321912, -58320, 14977, -43536]], ![![-136603, 351338, -63782, 16100, -47053]]]
  g := ![![![140633, 711882, -122518, 24730, -91772], ![46155, 304439, -39876, 11566, -35164], ![-24716, 114328, 22661, 7320, -932], ![-142922, -4764, 127900, 9885, 42056], ![-79049, 49880, 70988, 8026, 19519]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI829N2 : Nat.card (O ⧸ I829N2) = 829 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI829N2)

lemma isPrimeI829N2 : Ideal.IsPrime I829N2 := prime_ideal_of_norm_prime hp829.out _ NI829N2
def MulI829N0 : IdealMulLeCertificate' Table 
  ![![13947, -35671, 6101, -1370, 4554]] ![![25, -27, -79, 34, -8]]
  ![![206833, -531726, 95870, -24262, 71396]] where
 M := ![![![206833, -531726, 95870, -24262, 71396]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI829N1 : IdealMulLeCertificate' Table 
  ![![206833, -531726, 95870, -24262, 71396]] ![![-112109, 711882, -122518, 24730, -91772]]
  ![![829, 0, 0, 0, 0]] where
 M := ![![![-829, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC829 : ContainsPrimesAboveP 829 ![I829N0, I829N1, I829N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI829N0
    exact isPrimeI829N1
    exact isPrimeI829N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 829 (by decide) (𝕀 ⊙ MulI829N0 ⊙ MulI829N1)
instance hp839 : Fact (Nat.Prime 839) := {out := by norm_num}

def I839N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3701, -9459, 1602, -357, 1206]] i)))

def SI839N0: IdealEqSpanCertificate' Table ![![3701, -9459, 1602, -357, 1206]] 
 ![![839, 0, 0, 0, 0], ![0, 839, 0, 0, 0], ![820, 143, 1, 0, 0], ![200, 507, 0, 1, 0], ![283, 353, 0, 0, 1]] where
  M :=![![![3701, -9459, 1602, -357, 1206], ![714, -1837, 324, -96, 270], ![192, -558, 305, -24, -36], ![48, 288, -954, 425, -216], ![774, -1872, -108, -162, 611]]]
  hmulB := by decide  
  f := ![![![131905, -842247, 151020, -28779, 110556]], ![![57558, -367877, 66420, -12534, 48438]], ![![138758, -886067, 158957, -30270, 116334]], ![![66238, -423165, 76158, -14437, 55638]], ![![68729, -439004, 78912, -14985, 57689]]]
  g := ![![![-1883, -576, 1602, -357, 1206], ![-384, -113, 324, -96, 270], ![-280, -23, 305, -24, -36], ![904, -3, -954, 425, -216], ![-61, -143, -108, -162, 611]]]
  hle1 := by decide   
  hle2 := by decide  


def P839P0 : CertificateIrreducibleZModOfList' 839 2 2 9 [8, 744, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 838], [0, 1]]
 g := ![![[93, 105], [45, 43], [375, 370], [243], [64], [828], [330, 295], [477], [95, 1]], ![[0, 734], [774, 796], [287, 469], [243], [64], [828], [668, 544], [477], [190, 838]]]
 h' := ![![[95, 838], [479, 622], [356, 230], [177, 89], [128, 369], [115, 8], [716, 538], [747, 73], [79, 627], [0, 1]], ![[0, 1], [0, 217], [392, 609], [242, 750], [784, 470], [36, 831], [647, 301], [131, 766], [75, 212], [95, 838]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [316, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI839N0 : CertifiedPrimeIdeal' SI839N0 839 where
  n := 2
  hpos := by decide
  P := [8, 744, 1]
  hirr := P839P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![727, -2336, -422, -88, -1354]
  a := ![1, -3, -1, 0, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![891, 692, -422, -88, -1354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI839N0 : Ideal.IsPrime I839N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI839N0 B_one_repr
lemma NI839N0 : Nat.card (O ⧸ I839N0) = 703921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI839N0

def I839N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, -269, 47, -10, 34]] i)))

def SI839N1: IdealEqSpanCertificate' Table ![![105, -269, 47, -10, 34]] 
 ![![839, 0, 0, 0, 0], ![130, 1, 0, 0, 0], ![719, 0, 1, 0, 0], ![498, 0, 0, 1, 0], ![579, 0, 0, 0, 1]] where
  M :=![![![105, -269, 47, -10, 34], ![20, -51, 7, -1, 8], ![2, -14, 18, -7, 10], ![14, -52, 55, 12, -22], ![28, -62, -13, 17, 1]]]
  hmulB := by decide  
  f := ![![![450013, -2872893, 514509, -98214, 376904]], ![![69962, -446639, 79989, -15269, 58596]], ![![385751, -2462643, 441037, -84189, 323082]], ![![267156, -1705530, 305445, -58306, 223754]], ![![310625, -1983037, 355144, -67793, 260161]]]
  g := ![![![-16, -269, 47, -10, 34], ![-3, -51, 7, -1, 8], ![-16, -14, 18, -7, 10], ![-31, -52, 55, 12, -22], ![10, -62, -13, 17, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI839N1 : Nat.card (O ⧸ I839N1) = 839 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI839N1)

lemma isPrimeI839N1 : Ideal.IsPrime I839N1 := prime_ideal_of_norm_prime hp839.out _ NI839N1

def I839N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1031, 6583, -1180, 225, -864]] i)))

def SI839N2: IdealEqSpanCertificate' Table ![![-1031, 6583, -1180, 225, -864]] 
 ![![839, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![801, 0, 1, 0, 0], ![134, 0, 0, 1, 0], ![57, 0, 0, 0, 1]] where
  M :=![![![-1031, 6583, -1180, 225, -864], ![-450, 2875, -518, 98, -378], ![-196, 1258, -233, 42, -168], ![-84, 560, -128, 19, -84], ![-130, 842, -170, 28, -115]]]
  hmulB := by decide  
  f := ![![![190117, -486233, 83126, -18653, 62058]], ![![30862, -78931, 13494, -3028, 10074]], ![![181515, -464233, 79365, -17809, 59250]], ![![30366, -77662, 13276, -2979, 9912]], ![![12973, -33179, 5672, -1273, 4235]]]
  g := ![![![81, 6583, -1180, 225, -864], ![38, 2875, -518, 98, -378], ![23, 1258, -233, 42, -168], ![34, 560, -128, 19, -84], ![29, 842, -170, 28, -115]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI839N2 : Nat.card (O ⧸ I839N2) = 839 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI839N2)

lemma isPrimeI839N2 : Ideal.IsPrime I839N2 := prime_ideal_of_norm_prime hp839.out _ NI839N2

def I839N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5251, -13230, 1936, -534, 1582]] i)))

def SI839N3: IdealEqSpanCertificate' Table ![![5251, -13230, 1936, -534, 1582]] 
 ![![839, 0, 0, 0, 0], ![430, 1, 0, 0, 0], ![519, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![570, 0, 0, 0, 1]] where
  M :=![![![5251, -13230, 1936, -534, 1582], ![1068, -2145, -594, -160, -40], ![320, 908, -2985, -194, -1040], ![388, 4092, -9034, -517, -3244], ![1536, -730, -5118, -452, -1619]]]
  hmulB := by decide  
  f := ![![![-1347, 8814, 580, -150, -1606]], ![![-690, 4523, 290, -72, -828]], ![![-843, 5482, 335, -100, -974]], ![![8, -60, 186, -49, -12]], ![![-890, 5930, 422, -68, -1151]]]
  g := ![![![4517, -13230, 1936, -534, 1582], ![1496, -2145, -594, -160, -40], ![2089, 908, -2985, -194, -1040], ![5698, 4092, -9034, -517, -3244], ![4644, -730, -5118, -452, -1619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI839N3 : Nat.card (O ⧸ I839N3) = 839 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI839N3)

lemma isPrimeI839N3 : Ideal.IsPrime I839N3 := prime_ideal_of_norm_prime hp839.out _ NI839N3
def MulI839N0 : IdealMulLeCertificate' Table 
  ![![3701, -9459, 1602, -357, 1206]] ![![105, -269, 47, -10, 34]]
  ![![231399, -591796, 101257, -22547, 75242]] where
 M := ![![![231399, -591796, 101257, -22547, 75242]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI839N1 : IdealMulLeCertificate' Table 
  ![![231399, -591796, 101257, -22547, 75242]] ![![-1031, 6583, -1180, 225, -864]]
  ![![1947, -5133, 1503, -56, 94]] where
 M := ![![![1947, -5133, 1503, -56, 94]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI839N2 : IdealMulLeCertificate' Table 
  ![![1947, -5133, 1503, -56, 94]] ![![5251, -13230, 1936, -534, 1582]]
  ![![839, 0, 0, 0, 0]] where
 M := ![![![5345269, -13681573, 2356751, -523536, 1751832]]]
 hmul := by decide  
 g := ![![![![6371, -16307, 2809, -624, 2088]]]]
 hle2 := by decide  


def PBC839 : ContainsPrimesAboveP 839 ![I839N0, I839N1, I839N2, I839N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI839N0
    exact isPrimeI839N1
    exact isPrimeI839N2
    exact isPrimeI839N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 839 (by decide) (𝕀 ⊙ MulI839N0 ⊙ MulI839N1 ⊙ MulI839N2)
instance hp853 : Fact (Nat.Prime 853) := {out := by norm_num}

def I853N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![329595, 3961895, -8553608, -484931, -3077788]] i)))

def SI853N0: IdealEqSpanCertificate' Table ![![329595, 3961895, -8553608, -484931, -3077788]] 
 ![![853, 0, 0, 0, 0], ![0, 853, 0, 0, 0], ![0, 0, 853, 0, 0], ![498, 175, 161, 1, 0], ![735, 706, 739, 0, 1]] where
  M :=![![![329595, 3961895, -8553608, -484931, -3077788], ![969862, 11670885, -25192990, -1428170, -9065162], ![2856340, 34374170, -74200083, -4206326, -26699344], ![8412652, 101241064, -218538904, -12388743, -78636644], ![5292206, 63687230, -137475626, -7793360, -49467709]]]
  hmulB := by decide  
  f := ![![![-107, 9, 642, -435, 350]], ![![870, -2377, 1854, 812, -1910]], ![![-1624, 10134, -17131, 4050, 1052]], ![![-200, 1433, -2441, 645, 42]], ![![-771, 6783, -12701, 3799, -379]]]
  g := ![![![2935521, 2651516, 2747955, -484931, -3077788], ![8646064, 7809619, 8093666, -1428170, -9065162], ![25464976, 23001428, 23838023, -4206326, -26699344], ![75001102, 67745301, 70209295, -12388743, -78636644], ![47180717, 42616328, 44166345, -7793360, -49467709]]]
  hle1 := by decide   
  hle2 := by decide  


def P853P0 : CertificateIrreducibleZModOfList' 853 3 2 9 [225, 275, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [235, 73, 115], [502, 779, 738], [0, 1]]
 g := ![![[833, 221, 377], [784, 101], [688, 143, 231], [605, 347], [237, 657, 775], [650, 804], [478, 70, 819], [772, 661], [1]], ![[560, 644, 116, 99], [833, 419], [390, 247, 486, 381], [818, 476], [401, 164, 287, 612], [584, 219], [844, 839, 151, 767], [115, 100], [321, 542, 565, 829]], ![[755, 342, 358, 454], [759, 268], [320, 332, 785, 463], [597, 25], [145, 268, 629, 329], [527, 22], [599, 685, 845, 149], [258, 522], [425, 776, 704, 24]]]
 h' := ![![[235, 73, 115], [338, 279, 331], [446, 497, 131], [298, 117, 250], [414, 78, 672], [532, 567, 726], [781, 561, 625], [610, 712, 655], [628, 578, 737], [0, 1]], ![[502, 779, 738], [94, 484, 767], [435, 835, 546], [55, 59, 73], [182, 357, 186], [838, 20, 392], [149, 129, 352], [164, 137, 143], [613, 54, 843], [235, 73, 115]], ![[0, 1], [694, 90, 608], [849, 374, 176], [218, 677, 530], [509, 418, 848], [539, 266, 588], [594, 163, 729], [552, 4, 55], [48, 221, 126], [502, 779, 738]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [345, 68], []]
 b := ![[], [98, 434, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI853N0 : CertifiedPrimeIdeal' SI853N0 853 where
  n := 3
  hpos := by decide
  P := [225, 275, 116, 1]
  hirr := P853P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6644037, -6730515, -15397010, 20356325, -19411270]
  a := ![-8, 28, 13, -9, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4849329, 11881910, 12956815, 20356325, -19411270]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI853N0 : Ideal.IsPrime I853N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI853N0 B_one_repr
lemma NI853N0 : Nat.card (O ⧸ I853N0) = 620650477 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI853N0

def I853N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, -9, -642, 435, -350]] i)))

def SI853N1: IdealEqSpanCertificate' Table ![![107, -9, -642, 435, -350]] 
 ![![853, 0, 0, 0, 0], ![0, 853, 0, 0, 0], ![161, 692, 1, 0, 0], ![331, 683, 0, 1, 0], ![184, 67, 0, 0, 1]] where
  M :=![![![107, -9, -642, 435, -350], ![-870, 2377, -1854, -812, 1910], ![1624, -10134, 17131, -4050, -1052], ![8100, -2268, -31752, 27335, -26404], ![-6898, 31580, -45062, 5950, 9505]]]
  hmulB := by decide  
  f := ![![![-329595, -3961895, 8553608, 484931, 3077788]], ![![-969862, -11670885, 25192990, 1428170, 9065162]], ![![-852363, -10256145, 22139367, 1255069, 7966372]], ![![-914331, -11000988, 23747474, 1346238, 8545006]], ![![-153480, -1845985, 3985076, 225918, 1433935]]]
  g := ![![![28, 200, -642, 435, -350], ![252, 2007, -1854, -812, 1910], ![-1433, -10584, 17131, -4050, -1052], ![1091, 5943, -31752, 27335, -26404], ![4138, 31083, -45062, 5950, 9505]]]
  hle1 := by decide   
  hle2 := by decide  


def P853P1 : CertificateIrreducibleZModOfList' 853 2 2 9 [776, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [781, 852], [0, 1]]
 g := ![![[132, 144], [837], [329, 453], [733], [234, 557], [168], [287, 119], [830], [781, 1]], ![[0, 709], [837], [127, 400], [733], [221, 296], [168], [249, 734], [830], [709, 852]]]
 h' := ![![[781, 852], [842, 841], [596, 374], [79, 689], [105, 478], [411, 790], [774, 102], [575, 93], [427, 143], [0, 1]], ![[0, 1], [0, 12], [111, 479], [798, 164], [662, 375], [682, 63], [254, 751], [703, 760], [367, 710], [781, 852]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [520]]
 b := ![[], [830, 260]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI853N1 : CertifiedPrimeIdeal' SI853N1 853 where
  n := 2
  hpos := by decide
  P := [776, 72, 1]
  hirr := P853P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9176, -46179, 71453, -10492, -8119]
  a := ![10, -11, -15, 12, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7653, -48982, 71453, -10492, -8119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI853N1 : Ideal.IsPrime I853N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI853N1 B_one_repr
lemma NI853N1 : Nat.card (O ⧸ I853N1) = 727609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI853N1
def MulI853N0 : IdealMulLeCertificate' Table 
  ![![329595, 3961895, -8553608, -484931, -3077788]] ![![107, -9, -642, 435, -350]]
  ![![853, 0, 0, 0, 0]] where
 M := ![![![-853, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC853 : ContainsPrimesAboveP 853 ![I853N0, I853N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI853N0
    exact isPrimeI853N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 853 (by decide) (𝕀 ⊙ MulI853N0)
instance hp857 : Fact (Nat.Prime 857) := {out := by norm_num}

def I857N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1087, -2979, 794, -89, 472]] i)))

def SI857N0: IdealEqSpanCertificate' Table ![![1087, -2979, 794, -89, 472]] 
 ![![857, 0, 0, 0, 0], ![0, 857, 0, 0, 0], ![0, 0, 857, 0, 0], ![0, 0, 0, 857, 0], ![222, 493, 826, 786, 1]] where
  M :=![![![1087, -2979, 794, -89, 472], ![178, -979, 1002, 28, 410], ![-56, -1406, 2795, 126, 988], ![-252, -3756, 7864, 567, 2732], ![58, -2890, 4910, 298, 1915]]]
  hmulB := by decide  
  f := ![![![61, -381, 68, -13, 50]], ![![26, -165, 30, -6, 22]], ![![12, -74, 15, -2, 8]], ![![4, -24, -8, 3, 4]], ![![46, -287, 42, -6, 37]]]
  g := ![![![-121, -275, -454, -433, 472], ![-106, -237, -394, -376, 410], ![-256, -570, -949, -906, 988], ![-708, -1576, -2624, -2505, 2732], ![-496, -1105, -1840, -1756, 1915]]]
  hle1 := by decide   
  hle2 := by decide  


def P857P0 : CertificateIrreducibleZModOfList' 857 4 2 9 [18, 412, 365, 613, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 545, 373, 646], [2, 614, 276, 106], [146, 554, 208, 105], [0, 1]]
 g := ![![[566, 675, 368, 834], [754, 126, 64], [483, 832, 655], [95, 308, 23, 424], [603, 105, 526, 411], [246, 187, 802], [712, 60, 574, 471], [38, 244, 1], []], ![[550, 413, 201, 75, 381, 119], [65, 809, 743], [86, 443, 467], [219, 780, 522, 473, 508, 172], [247, 765, 26, 19, 551, 471], [170, 368, 8], [589, 786, 128, 392, 296, 477], [434, 218, 775], [318, 465, 524, 672, 56, 503]], ![[68, 597, 163, 476, 310, 465], [725, 590, 471], [435, 439, 184], [478, 16, 654, 592, 547, 114], [655, 700, 628, 579, 157, 743], [280, 158, 378], [583, 710, 219, 705, 167, 601], [16, 161, 816], [22, 215, 816, 274, 734, 643]], ![[436, 24, 585, 344, 51, 178], [710, 548, 8], [411, 846, 467], [588, 275, 170, 402, 6, 274], [686, 95, 346, 336, 171, 652], [466, 435, 613], [659, 128, 410, 47, 191, 585], [656, 355, 98], [625, 736, 180, 336, 617, 675]]]
 h' := ![![[96, 545, 373, 646], [663, 153, 216, 117], [749, 94, 4, 849], [4, 834, 304, 432], [287, 547, 577, 477], [521, 644, 552, 467], [39, 318, 683, 185], [173, 520, 422, 358], [0, 0, 0, 1], [0, 1]], ![[2, 614, 276, 106], [11, 538, 813, 629], [839, 265, 90, 40], [423, 237, 236, 139], [420, 661, 732, 535], [160, 438, 663, 93], [426, 177, 565, 531], [813, 321, 105, 350], [587, 691, 462, 417], [96, 545, 373, 646]], ![[146, 554, 208, 105], [435, 432, 590, 590], [682, 305, 660, 499], [416, 593, 767, 147], [15, 266, 486, 633], [678, 371, 656, 767], [24, 60, 352, 641], [281, 730, 348, 596], [469, 433, 349, 723], [2, 614, 276, 106]], ![[0, 1], [521, 591, 95, 378], [685, 193, 103, 326], [742, 50, 407, 139], [471, 240, 776, 69], [599, 261, 700, 387], [537, 302, 114, 357], [87, 143, 839, 410], [260, 590, 46, 573], [146, 554, 208, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [576, 712, 699], []]
 b := ![[], [], [387, 137, 33, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI857N0 : CertifiedPrimeIdeal' SI857N0 857 where
  n := 4
  hpos := by decide
  P := [18, 412, 365, 613, 1]
  hirr := P857P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5018859002, -1794538676, 27442814764, -20088307536, 17762499084]
  a := ![-6, 6, 10, -16, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4607110450, -10220194384, -17087959660, -16314367080, 17762499084]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI857N0 : Ideal.IsPrime I857N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI857N0 B_one_repr
lemma NI857N0 : Nat.card (O ⧸ I857N0) = 539415333601 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI857N0

def I857N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, -381, 68, -13, 50]] i)))

def SI857N1: IdealEqSpanCertificate' Table ![![61, -381, 68, -13, 50]] 
 ![![857, 0, 0, 0, 0], ![424, 1, 0, 0, 0], ![194, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![350, 0, 0, 0, 1]] where
  M :=![![![61, -381, 68, -13, 50], ![26, -165, 30, -6, 22], ![12, -74, 15, -2, 8], ![4, -24, -8, 3, 4], ![6, -44, 6, -4, 11]]]
  hmulB := by decide  
  f := ![![![1087, -2979, 794, -89, 472]], ![![538, -1475, 394, -44, 234]], ![![246, -676, 183, -20, 108]], ![![20, -60, 24, -1, 12]], ![![444, -1220, 330, -36, 195]]]
  g := ![![![153, -381, 68, -13, 50], ![66, -165, 30, -6, 22], ![30, -74, 15, -2, 8], ![12, -24, -8, 3, 4], ![16, -44, 6, -4, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI857N1 : Nat.card (O ⧸ I857N1) = 857 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI857N1)

lemma isPrimeI857N1 : Ideal.IsPrime I857N1 := prime_ideal_of_norm_prime hp857.out _ NI857N1
def MulI857N0 : IdealMulLeCertificate' Table 
  ![![1087, -2979, 794, -89, 472]] ![![61, -381, 68, -13, 50]]
  ![![857, 0, 0, 0, 0]] where
 M := ![![![857, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC857 : ContainsPrimesAboveP 857 ![I857N0, I857N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI857N0
    exact isPrimeI857N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 857 (by decide) (𝕀 ⊙ MulI857N0)
instance hp859 : Fact (Nat.Prime 859) := {out := by norm_num}

def I859N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![845, -3660, 646, -130, 476]] i)))

def SI859N0: IdealEqSpanCertificate' Table ![![845, -3660, 646, -130, 476]] 
 ![![859, 0, 0, 0, 0], ![0, 859, 0, 0, 0], ![641, 164, 1, 0, 0], ![533, 374, 0, 1, 0], ![131, 74, 0, 0, 1]] where
  M :=![![![845, -3660, 646, -130, 476], ![260, -1319, 234, -46, 172], ![92, -520, 91, -18, 68], ![36, -216, 38, -9, 28], ![164, -608, 106, -22, 77]]]
  hmulB := by decide  
  f := ![![![7, -12, -10, -10, -4]], ![![20, 3, -78, 18, -68]], ![![9, -8, -23, -4, -16]], ![![13, -6, -40, 1, -32]], ![![3, -2, -8, 0, -7]]]
  g := ![![![-473, -112, 646, -130, 476], ![-172, -41, 234, -46, 172], ![-67, -16, 91, -18, 68], ![-27, -6, 38, -9, 28], ![-77, -18, 106, -22, 77]]]
  hle1 := by decide   
  hle2 := by decide  


def P859P0 : CertificateIrreducibleZModOfList' 859 2 2 9 [64, 564, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [295, 858], [0, 1]]
 g := ![![[492, 604], [368, 354], [421], [51, 723], [417, 279], [714], [419, 487], [431], [295, 1]], ![[0, 255], [0, 505], [421], [304, 136], [258, 580], [714], [631, 372], [431], [590, 858]]]
 h' := ![![[295, 858], [500, 537], [63, 224], [172, 601], [800, 686], [440, 641], [672, 109], [228, 413], [18, 202], [0, 1]], ![[0, 1], [0, 322], [0, 635], [513, 258], [446, 173], [555, 218], [185, 750], [85, 446], [337, 657], [295, 858]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [515]]
 b := ![[], [459, 687]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI859N0 : CertifiedPrimeIdeal' SI859N0 859 where
  n := 2
  hpos := by decide
  P := [64, 564, 1]
  hirr := P859P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3888, -19331, 77232, -20186, 32969]
  a := ![-6, 18, 16, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50139, -8819, 77232, -20186, 32969]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI859N0 : Ideal.IsPrime I859N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI859N0 B_one_repr
lemma NI859N0 : Nat.card (O ⧸ I859N0) = 737881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI859N0

def I859N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![355833, -910073, 155615, -34918, 116152]] i)))

def SI859N1: IdealEqSpanCertificate' Table ![![355833, -910073, 155615, -34918, 116152]] 
 ![![859, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![834, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![807, 0, 0, 0, 1]] where
  M :=![![![355833, -910073, 155615, -34918, 116152], ![69836, -178611, 30541, -6853, 22796], ![13706, -35054, 5994, -1345, 4474], ![2690, -6880, 1177, -264, 878], ![89464, -228812, 39125, -8779, 29203]]]
  hmulB := by decide  
  f := ![![![-799, 4611, -339, 150, -374]], ![![-5, 28, 0, 1, -2]], ![![-776, 4476, -326, 147, -362]], ![![-119, 669, -36, 20, -44]], ![![-751, 4325, -302, 139, -347]]]
  g := ![![![-249414, -910073, 155615, -34918, 116152], ![-48950, -178611, 30541, -6853, 22796], ![-9607, -35054, 5994, -1345, 4474], ![-1886, -6880, 1177, -264, 878], ![-62708, -228812, 39125, -8779, 29203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI859N1 : Nat.card (O ⧸ I859N1) = 859 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI859N1)

lemma isPrimeI859N1 : Ideal.IsPrime I859N1 := prime_ideal_of_norm_prime hp859.out _ NI859N1

def I859N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![867, -7376, 1331, -247, 972]] i)))

def SI859N2: IdealEqSpanCertificate' Table ![![867, -7376, 1331, -247, 972]] 
 ![![859, 0, 0, 0, 0], ![16, 1, 0, 0, 0], ![603, 0, 1, 0, 0], ![660, 0, 0, 1, 0], ![14, 0, 0, 0, 1]] where
  M :=![![![867, -7376, 1331, -247, 972], ![494, -3515, 631, -119, 462], ![238, -1592, 286, -55, 210], ![110, -712, 133, -24, 90], ![50, -778, 139, -23, 101]]]
  hmulB := by decide  
  f := ![![![20221, 243440, -525461, -29789, -189072]], ![![446, 5369, -11589, -657, -4170]], ![![14399, 173348, -374169, -21212, -134634]], ![![16138, 194284, -419359, -23774, -150894]], ![![708, 8522, -18395, -1043, -6619]]]
  g := ![![![-622, -7376, 1331, -247, 972], ![-293, -3515, 631, -119, 462], ![-132, -1592, 286, -55, 210], ![-63, -712, 133, -24, 90], ![-67, -778, 139, -23, 101]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI859N2 : Nat.card (O ⧸ I859N2) = 859 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI859N2)

lemma isPrimeI859N2 : Ideal.IsPrime I859N2 := prime_ideal_of_norm_prime hp859.out _ NI859N2

def I859N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -36, 37, 5, -22]] i)))

def SI859N3: IdealEqSpanCertificate' Table ![![11, -36, 37, 5, -22]] 
 ![![859, 0, 0, 0, 0], ![674, 1, 0, 0, 0], ![135, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![700, 0, 0, 0, 1]] where
  M :=![![![11, -36, 37, 5, -22], ![-10, 109, -219, 71, -14], ![-142, 188, 196, -333, 398], ![666, -2400, 2771, 66, -1202], ![278, -8, -1259, 1007, -937]]]
  hmulB := by decide  
  f := ![![![9997, -105528, 19721, -3445, 14138]], ![![7852, -82863, 15487, -2705, 11102]], ![![1575, -16616, 3111, -542, 2228]], ![![746, -7884, 1491, -256, 1062]], ![![8146, -86012, 16085, -2807, 11527]]]
  g := ![![![40, -36, 37, 5, -22], ![-45, 109, -219, 71, -14], ![-478, 188, 196, -333, 398], ![2423, -2400, 2771, 66, -1202], ![893, -8, -1259, 1007, -937]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI859N3 : Nat.card (O ⧸ I859N3) = 859 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI859N3)

lemma isPrimeI859N3 : Ideal.IsPrime I859N3 := prime_ideal_of_norm_prime hp859.out _ NI859N3
def MulI859N0 : IdealMulLeCertificate' Table 
  ![![845, -3660, 646, -130, 476]] ![![355833, -910073, 155615, -34918, 116152]]
  ![![96168365, -245960421, 42057229, -9437084, 31391772]] where
 M := ![![![96168365, -245960421, 42057229, -9437084, 31391772]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI859N1 : IdealMulLeCertificate' Table 
  ![![96168365, -245960421, 42057229, -9437084, 31391772]] ![![867, -7376, 1331, -247, 972]]
  ![![-27585345657, 70554316199, -12064240206, 2707035609, -9004814220]] where
 M := ![![![-27585345657, 70554316199, -12064240206, 2707035609, -9004814220]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI859N2 : IdealMulLeCertificate' Table 
  ![![-27585345657, 70554316199, -12064240206, 2707035609, -9004814220]] ![![11, -36, 37, 5, -22]]
  ![![859, 0, 0, 0, 0]] where
 M := ![![![3687507469, -9431197225, 1612658253, -361858904, 1203697802]]]
 hmul := by decide  
 g := ![![![![4292791, -10979275, 1877367, -421256, 1401278]]]]
 hle2 := by decide  


def PBC859 : ContainsPrimesAboveP 859 ![I859N0, I859N1, I859N2, I859N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI859N0
    exact isPrimeI859N1
    exact isPrimeI859N2
    exact isPrimeI859N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 859 (by decide) (𝕀 ⊙ MulI859N0 ⊙ MulI859N1 ⊙ MulI859N2)
instance hp863 : Fact (Nat.Prime 863) := {out := by norm_num}

def I863N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3783, 9677, -1659, 372, -1234]] i)))

def SI863N0: IdealEqSpanCertificate' Table ![![-3783, 9677, -1659, 372, -1234]] 
 ![![863, 0, 0, 0, 0], ![0, 863, 0, 0, 0], ![327, 576, 1, 0, 0], ![645, 806, 0, 1, 0], ![281, 814, 0, 0, 1]] where
  M :=![![![-3783, 9677, -1659, 372, -1234], ![-744, 1897, -313, 65, -236], ![-130, 330, -32, 29, -82], ![-58, 256, -321, 74, 10], ![-992, 2522, -445, 31, -211]]]
  hmulB := by decide  
  f := ![![![-47715, 304649, -54597, 10412, -39980]], ![![-20824, 133029, -23935, 4539, -17488]], ![![-31989, 204291, -36675, 6977, -26830]], ![![-55115, 351965, -63166, 12022, -46218]], ![![-35185, 224717, -40362, 7673, -29519]]]
  g := ![![![748, 1935, -1659, 372, -1234], ![146, 373, -313, 65, -236], ![17, 72, -32, 29, -82], ![63, 136, -321, 74, 10], ![213, 470, -445, 31, -211]]]
  hle1 := by decide   
  hle2 := by decide  


def P863P0 : CertificateIrreducibleZModOfList' 863 2 2 9 [815, 665, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [198, 862], [0, 1]]
 g := ![![[112, 62], [143, 837], [360, 508], [674, 253], [290, 229], [140], [619, 153], [426], [198, 1]], ![[306, 801], [173, 26], [836, 355], [714, 610], [756, 634], [140], [708, 710], [426], [396, 862]]]
 h' := ![![[198, 862], [823, 713], [20, 197], [421, 211], [112, 103], [362, 529], [370, 193], [720, 318], [11, 417], [0, 1]], ![[0, 1], [465, 150], [191, 666], [775, 652], [657, 760], [681, 334], [612, 670], [685, 545], [592, 446], [198, 862]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [783]]
 b := ![[], [508, 823]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI863N0 : CertifiedPrimeIdeal' SI863N0 863 where
  n := 2
  hpos := by decide
  P := [815, 665, 1]
  hirr := P863P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-125, -2719, 3590, -1927, 2616]
  a := ![-2, -2, 3, -3, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-772, -3067, 3590, -1927, 2616]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI863N0 : Ideal.IsPrime I863N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI863N0 B_one_repr
lemma NI863N0 : Nat.card (O ⧸ I863N0) = 744769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI863N0

def I863N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, -66, 19, 43, -68]] i)))

def SI863N1: IdealEqSpanCertificate' Table ![![29, -66, 19, 43, -68]] 
 ![![863, 0, 0, 0, 0], ![0, 863, 0, 0, 0], ![551, 505, 1, 0, 0], ![494, 111, 0, 1, 0], ![339, 593, 0, 0, 1]] where
  M :=![![![29, -66, 19, 43, -68], ![-86, 387, -549, 69, 122], ![-138, -436, 1692, -931, 658], ![1862, -4632, 2693, 2238, -4270], ![-18, 2426, -5817, 2329, -1001]]]
  hmulB := by decide  
  f := ![![![205415, -527226, 90187, -20215, 67304]], ![![40430, -104231, 17865, -3991, 13318]], ![![154819, -397635, 68040, -15243, 50768]], ![![122786, -315207, 53924, -12085, 40240]], ![![108531, -278877, 47729, -10689, 35609]]]
  g := ![![![-10, 30, 19, 43, -68], ![263, 229, -549, 69, 122], ![-806, -1323, 1692, -931, 658], ![-1321, 1065, 2693, 2238, -4270], ![2774, 3795, -5817, 2329, -1001]]]
  hle1 := by decide   
  hle2 := by decide  


def P863P1 : CertificateIrreducibleZModOfList' 863 2 2 9 [285, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [804, 862], [0, 1]]
 g := ![![[733, 191], [92, 830], [392, 623], [529, 520], [581, 475], [16], [18, 707], [811], [804, 1]], ![[683, 672], [313, 33], [744, 240], [54, 343], [172, 388], [16], [592, 156], [811], [745, 862]]]
 h' := ![![[804, 862], [533, 497], [470, 682], [260, 332], [111, 782], [333, 398], [48, 859], [547, 487], [418, 607], [0, 1]], ![[0, 1], [552, 366], [793, 181], [521, 531], [575, 81], [152, 465], [284, 4], [293, 376], [851, 256], [804, 862]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [348]]
 b := ![[], [818, 174]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI863N1 : CertifiedPrimeIdeal' SI863N1 863 where
  n := 2
  hpos := by decide
  P := [285, 59, 1]
  hirr := P863P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10465, -54054, 82014, -9232, -10218]
  a := ![-10, 13, 20, -14, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-43053, -39846, 82014, -9232, -10218]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI863N1 : Ideal.IsPrime I863N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI863N1 B_one_repr
lemma NI863N1 : Nat.card (O ⧸ I863N1) = 744769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI863N1

def I863N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -10, 11, 1, -6]] i)))

def SI863N2: IdealEqSpanCertificate' Table ![![3, -10, 11, 1, -6]] 
 ![![863, 0, 0, 0, 0], ![645, 1, 0, 0, 0], ![804, 0, 1, 0, 0], ![83, 0, 0, 1, 0], ![700, 0, 0, 0, 1]] where
  M :=![![![3, -10, 11, 1, -6], ![-2, 29, -61, 21, -6], ![-42, 64, 38, -91, 114], ![182, -680, 817, -8, -318], ![86, -32, -317, 281, -277]]]
  hmulB := by decide  
  f := ![![![-46703, 159274, -27801, 5831, -20574]], ![![-34919, 119095, -20788, 4360, -15384]], ![![-43514, 148404, -25904, 5433, -19170]], ![![-4493, 15326, -2676, 561, -1980]], ![![-37894, 129228, -22557, 4731, -16693]]]
  g := ![![![2, -10, 11, 1, -6], ![38, 29, -61, 21, -6], ![-167, 64, 38, -91, 114], ![6, -680, 817, -8, -318], ![517, -32, -317, 281, -277]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI863N2 : Nat.card (O ⧸ I863N2) = 863 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI863N2)

lemma isPrimeI863N2 : Ideal.IsPrime I863N2 := prime_ideal_of_norm_prime hp863.out _ NI863N2
def MulI863N0 : IdealMulLeCertificate' Table 
  ![![-3783, 9677, -1659, 372, -1234]] ![![29, -66, 19, 43, -68]]
  ![![1889, 1213, -11604, 8123, -6990]] where
 M := ![![![1889, 1213, -11604, 8123, -6990]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI863N1 : IdealMulLeCertificate' Table 
  ![![1889, 1213, -11604, 8123, -6990]] ![![3, -10, 11, 1, -6]]
  ![![863, 0, 0, 0, 0]] where
 M := ![![![1367855, -6026329, 8358155, -945848, -1988352]]]
 hmul := by decide  
 g := ![![![![1585, -6983, 9685, -1096, -2304]]]]
 hle2 := by decide  


def PBC863 : ContainsPrimesAboveP 863 ![I863N0, I863N1, I863N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI863N0
    exact isPrimeI863N1
    exact isPrimeI863N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 863 (by decide) (𝕀 ⊙ MulI863N0 ⊙ MulI863N1)
instance hp877 : Fact (Nat.Prime 877) := {out := by norm_num}

def I877N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21007, -137596, 24633, -4715, 18108]] i)))

def SI877N0: IdealEqSpanCertificate' Table ![![21007, -137596, 24633, -4715, 18108]] 
 ![![877, 0, 0, 0, 0], ![0, 877, 0, 0, 0], ![0, 0, 877, 0, 0], ![0, 0, 0, 877, 0], ![20, 468, 48, 546, 1]] where
  M :=![![![21007, -137596, 24633, -4715, 18108], ![9430, -60855, 11231, -2153, 7926], ![4306, -26580, 4020, -315, 2934], ![630, -8060, -1119, -1218, 3978], ![2322, -17930, 6099, -2209, 3361]]]
  hmulB := by decide  
  f := ![![![-465, -5556, 12007, 681, 4320]], ![![-1362, -16383, 35367, 2005, 12726]], ![![-4010, -48256, 104166, 5905, 37482]], ![![-11810, -142128, 306797, 17392, 110394]], ![![-8318, -100098, 216073, 12249, 77749]]]
  g := ![![![-389, -9820, -963, -11279, 18108], ![-170, -4299, -421, -4937, 7926], ![-62, -1596, -156, -1827, 2934], ![-90, -2132, -219, -2478, 3978], ![-74, -1814, -177, -2095, 3361]]]
  hle1 := by decide   
  hle2 := by decide  


def P877P0 : CertificateIrreducibleZModOfList' 877 4 2 9 [779, 33, 340, 705, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [573, 760, 339, 510], [325, 207, 364, 478], [151, 786, 174, 766], [0, 1]]
 g := ![![[856, 558, 120, 477], [685, 493, 761], [394, 243, 811, 70], [477, 310, 540, 227], [231, 195, 755], [461, 101, 405, 250], [494, 764, 426, 789], [303, 172, 1], []], ![[333, 794, 270, 81, 490, 478], [366, 115, 625], [624, 488, 231, 779, 518, 832], [66, 852, 678, 480, 732, 776], [866, 361, 385], [834, 662, 373, 289, 596, 13], [639, 406, 584, 672, 616, 190], [536, 677, 284], [183, 693, 274, 337, 596, 365]], ![[410, 605, 689, 765, 633, 128], [55, 723, 196], [535, 278, 517, 595, 590, 54], [751, 833, 602, 645, 67, 288], [598, 517, 195], [261, 155, 695, 411, 794, 826], [427, 620, 839, 822, 822, 726], [94, 403, 415], [35, 91, 582, 768, 260, 788]], ![[769, 864, 546, 116, 58, 237], [838, 216, 609], [830, 431, 788, 627, 298, 441], [85, 68, 537, 192, 546, 847], [380, 622, 505], [672, 669, 175, 487, 291, 289], [551, 643, 291, 710, 303, 705], [668, 692, 259], [598, 140, 757, 735, 437, 489]]]
 h' := ![![[573, 760, 339, 510], [177, 557, 296, 389], [24, 353, 207, 132], [265, 393, 16, 115], [650, 579, 59, 298], [451, 581, 831, 561], [177, 278, 264, 210], [753, 718, 150, 619], [0, 0, 0, 1], [0, 1]], ![[325, 207, 364, 478], [624, 760, 749, 267], [340, 642, 306, 852], [138, 1, 617, 294], [773, 391, 288, 396], [484, 556, 753, 552], [528, 158, 619, 621], [268, 354, 586, 775], [625, 68, 108, 520], [573, 760, 339, 510]], ![[151, 786, 174, 766], [461, 173, 543, 361], [415, 327, 106, 14], [225, 49, 319, 243], [752, 700, 206, 103], [192, 780, 16, 585], [293, 574, 350, 365], [511, 284, 288, 14], [513, 411, 500, 193], [325, 207, 364, 478]], ![[0, 1], [141, 264, 166, 737], [830, 432, 258, 756], [871, 434, 802, 225], [228, 84, 324, 80], [767, 714, 154, 56], [244, 744, 521, 558], [363, 398, 730, 346], [571, 398, 269, 163], [151, 786, 174, 766]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [661, 478, 854], []]
 b := ![[], [], [59, 779, 404, 156], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI877N0 : CertifiedPrimeIdeal' SI877N0 877 where
  n := 4
  hpos := by decide
  P := [779, 33, 340, 705, 1]
  hirr := P877P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1501861095, 9846460046, -17240554625, 4680284353, 787854555]
  a := ![-6, 8, 9, -7, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-19679535, -409201222, -62779445, -485163401, 787854555]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI877N0 : Ideal.IsPrime I877N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI877N0 B_one_repr
lemma NI877N0 : Nat.card (O ⧸ I877N0) = 591559418641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI877N0

def I877N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-465, -5556, 12007, 681, 4320]] i)))

def SI877N1: IdealEqSpanCertificate' Table ![![-465, -5556, 12007, 681, 4320]] 
 ![![877, 0, 0, 0, 0], ![230, 1, 0, 0, 0], ![597, 0, 1, 0, 0], ![379, 0, 0, 1, 0], ![570, 0, 0, 0, 1]] where
  M :=![![![-465, -5556, 12007, 681, 4320], ![-1362, -16383, 35367, 2005, 12726], ![-4010, -48256, 104166, 5905, 37482], ![-11810, -142128, 306797, 17392, 110394], ![-7430, -89406, 192995, 10941, 69445]]]
  hmulB := by decide  
  f := ![![![21007, -137596, 24633, -4715, 18108]], ![![5520, -36155, 6473, -1239, 4758]], ![![14305, -93696, 16773, -3210, 12330]], ![![9079, -59472, 10644, -2039, 7830]], ![![13656, -89450, 16017, -3067, 11773]]]
  g := ![![![-9819, -5556, 12007, 681, 4320], ![-28918, -16383, 35367, 2005, 12726], ![-85171, -48256, 104166, 5905, 37482], ![-250851, -142128, 306797, 17392, 110394], ![-157802, -89406, 192995, 10941, 69445]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI877N1 : Nat.card (O ⧸ I877N1) = 877 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI877N1)

lemma isPrimeI877N1 : Ideal.IsPrime I877N1 := prime_ideal_of_norm_prime hp877.out _ NI877N1
def MulI877N0 : IdealMulLeCertificate' Table 
  ![![21007, -137596, 24633, -4715, 18108]] ![![-465, -5556, 12007, 681, 4320]]
  ![![877, 0, 0, 0, 0]] where
 M := ![![![877, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC877 : ContainsPrimesAboveP 877 ![I877N0, I877N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI877N0
    exact isPrimeI877N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 877 (by decide) (𝕀 ⊙ MulI877N0)
instance hp881 : Fact (Nat.Prime 881) := {out := by norm_num}

def I881N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![917, 11052, -23852, -1348, -8580]] i)))

def SI881N0: IdealEqSpanCertificate' Table ![![917, 11052, -23852, -1348, -8580]] 
 ![![881, 0, 0, 0, 0], ![0, 881, 0, 0, 0], ![0, 0, 881, 0, 0], ![153, 864, 273, 1, 0], ![284, 500, 148, 0, 1]] where
  M :=![![![917, 11052, -23852, -1348, -8580], ![2696, 32541, -70212, -3996, -25248], ![7992, 95696, -206679, -11724, -74472], ![23448, 282432, -609724, -34287, -219288], ![14656, 177804, -383452, -21780, -137687]]]
  hmulB := by decide  
  f := ![![![-33075, 89380, -15348, 3396, -11436]], ![![-6792, 19461, -3356, 732, -2496]], ![![-1464, 4656, -807, 172, -600]], ![![-12859, 36052, -6207, 1361, -4620]], ![![-14772, 40664, -6992, 1540, -5207]]]
  g := ![![![3001, 6204, 1832, -1348, -8580], ![8836, 18285, 5400, -3996, -25248], ![26052, 53872, 15909, -11724, -74472], ![76671, 158400, 46771, -34287, -219288], ![48184, 99704, 29444, -21780, -137687]]]
  hle1 := by decide   
  hle2 := by decide  


def P881P0 : CertificateIrreducibleZModOfList' 881 3 2 9 [342, 840, 465, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [339, 799, 63], [77, 81, 818], [0, 1]]
 g := ![![[795, 78, 204], [286, 861], [121, 26], [743, 5], [644, 72, 578], [337, 510, 93], [623, 653, 110], [134, 380], [1]], ![[863, 880, 767, 736], [258, 593], [651, 332], [235, 406], [601, 587, 602, 28], [348, 462, 333, 395], [198, 9, 242, 586], [337, 296], [164, 394, 537, 724]], ![[508, 201, 267, 351], [637, 339], [120, 345], [449, 685], [845, 625, 742, 492], [93, 415, 641, 479], [469, 740, 273, 58], [696, 863], [758, 459, 771, 157]]]
 h' := ![![[339, 799, 63], [828, 372, 561], [703, 551, 609], [507, 557, 94], [2, 880, 228], [157, 615, 167], [136, 850, 360], [656, 784, 782], [539, 41, 416], [0, 1]], ![[77, 81, 818], [817, 791, 159], [252, 140, 347], [880, 113, 417], [729, 415, 785], [819, 483, 293], [352, 703, 777], [394, 773, 847], [695, 445, 158], [339, 799, 63]], ![[0, 1], [703, 599, 161], [748, 190, 806], [402, 211, 370], [237, 467, 749], [352, 664, 421], [50, 209, 625], [285, 205, 133], [834, 395, 307], [77, 81, 818]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100, 197], []]
 b := ![[], [159, 29, 766], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI881N0 : CertifiedPrimeIdeal' SI881N0 881 where
  n := 3
  hpos := by decide
  P := [342, 840, 465, 1]
  hirr := P881P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![849590, -5386582, 8465572, -599880, -439280]
  a := ![-3, 7, 6, -2, 13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![246750, 831498, 269292, -599880, -439280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI881N0 : Ideal.IsPrime I881N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI881N0 B_one_repr
lemma NI881N0 : Nat.card (O ⧸ I881N0) = 683797841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI881N0

def I881N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2479, -15315, 2740, -525, 2008]] i)))

def SI881N1: IdealEqSpanCertificate' Table ![![2479, -15315, 2740, -525, 2008]] 
 ![![881, 0, 0, 0, 0], ![138, 1, 0, 0, 0], ![338, 0, 1, 0, 0], ![49, 0, 0, 1, 0], ![436, 0, 0, 0, 1]] where
  M :=![![![2479, -15315, 2740, -525, 2008], ![1050, -6603, 1182, -226, 866], ![452, -2866, 513, -98, 376], ![196, -1248, 224, -43, 164], ![330, -1978, 354, -68, 259]]]
  hmulB := by decide  
  f := ![![![-75, -1245, 2590, 111, 914]], ![![-12, -199, 414, 18, 146]], ![![-30, -488, 1017, 44, 360]], ![![-7, -105, 222, 8, 78]], ![![-38, -640, 1330, 58, 467]]]
  g := ![![![386, -15315, 2740, -525, 2008], ![166, -6603, 1182, -226, 866], ![72, -2866, 513, -98, 376], ![31, -1248, 224, -43, 164], ![50, -1978, 354, -68, 259]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI881N1 : Nat.card (O ⧸ I881N1) = 881 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI881N1)

lemma isPrimeI881N1 : Ideal.IsPrime I881N1 := prime_ideal_of_norm_prime hp881.out _ NI881N1

def I881N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-399, 1019, -174, 39, -130]] i)))

def SI881N2: IdealEqSpanCertificate' Table ![![-399, 1019, -174, 39, -130]] 
 ![![881, 0, 0, 0, 0], ![470, 1, 0, 0, 0], ![231, 0, 1, 0, 0], ![674, 0, 0, 1, 0], ![456, 0, 0, 0, 1]] where
  M :=![![![-399, 1019, -174, 39, -130], ![-78, 199, -34, 8, -26], ![-16, 42, -11, 2, -4], ![-4, 4, 12, -7, 4], ![-98, 248, -34, 10, -37]]]
  hmulB := by decide  
  f := ![![![1131, -6835, 696, -277, 724]], ![![604, -3649, 370, -148, 386]], ![![297, -1791, 177, -73, 188]], ![![866, -5222, 516, -213, 548]], ![![586, -3534, 350, -144, 371]]]
  g := ![![![-461, 1019, -174, 39, -130], ![-90, 199, -34, 8, -26], ![-19, 42, -11, 2, -4], ![-2, 4, 12, -7, 4], ![-112, 248, -34, 10, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI881N2 : Nat.card (O ⧸ I881N2) = 881 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI881N2)

lemma isPrimeI881N2 : Ideal.IsPrime I881N2 := prime_ideal_of_norm_prime hp881.out _ NI881N2
def MulI881N0 : IdealMulLeCertificate' Table 
  ![![917, 11052, -23852, -1348, -8580]] ![![2479, -15315, 2740, -525, 2008]]
  ![![1131, -6835, 696, -277, 724]] where
 M := ![![![1131, -6835, 696, -277, 724]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI881N1 : IdealMulLeCertificate' Table 
  ![![1131, -6835, 696, -277, 724]] ![![-399, 1019, -174, 39, -130]]
  ![![881, 0, 0, 0, 0]] where
 M := ![![![881, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC881 : ContainsPrimesAboveP 881 ![I881N0, I881N1, I881N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI881N0
    exact isPrimeI881N1
    exact isPrimeI881N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 881 (by decide) (𝕀 ⊙ MulI881N0 ⊙ MulI881N1)
instance hp883 : Fact (Nat.Prime 883) := {out := by norm_num}

def I883N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, 271, 204, -1, -156]] i)))

def SI883N0: IdealEqSpanCertificate' Table ![![-35, 271, 204, -1, -156]] 
 ![![883, 0, 0, 0, 0], ![0, 883, 0, 0, 0], ![687, 349, 1, 0, 0], ![413, 740, 0, 1, 0], ![862, 365, 0, 0, 1]] where
  M :=![![![-35, 271, 204, -1, -156], ![2, 587, -1136, 518, -318], ![-1036, 2310, -721, -1536, 2472], ![3072, -13996, 19950, -2593, -4272], ![2394, -3430, -2580, 5344, -6623]]]
  hmulB := by decide  
  f := ![![![358461, 4315603, -9315014, -528043, -3351834]], ![![1056086, 12709711, -27435032, -1555260, -9871926]], ![![699827, 8423490, -18182383, -1030727, -6542568]], ![![1063091, 12794769, -27618360, -1565646, -9937902]], ![![793010, 9545243, -20603668, -1167984, -7413821]]]
  g := ![![![-6, -15, 204, -1, -156], ![952, 147, -1136, 518, -318], ![-1135, 553, -721, -1536, 2472], ![-10135, -3962, 19950, -2593, -4272], ![5976, -725, -2580, 5344, -6623]]]
  hle1 := by decide   
  hle2 := by decide  


def P883P0 : CertificateIrreducibleZModOfList' 883 2 2 9 [714, 812, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 882], [0, 1]]
 g := ![![[711, 301], [359, 703], [170], [813], [469, 16], [345, 286], [813, 729], [680], [71, 1]], ![[7, 582], [824, 180], [170], [813], [722, 867], [342, 597], [475, 154], [680], [142, 882]]]
 h' := ![![[71, 882], [627, 268], [28, 345], [63, 839], [674, 529], [27, 4], [532, 641], [332, 27], [520, 795], [0, 1]], ![[0, 1], [229, 615], [682, 538], [471, 44], [264, 354], [311, 879], [127, 242], [483, 856], [453, 88], [71, 882]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [373]]
 b := ![[], [664, 628]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI883N0 : CertifiedPrimeIdeal' SI883N0 883 where
  n := 2
  hpos := by decide
  P := [714, 812, 1]
  hirr := P883P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28198, -81331, 84353, 4504, -48615]
  a := ![16, -7, -33, 16, -41]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-20245, -17111, 84353, 4504, -48615]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI883N0 : Ideal.IsPrime I883N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI883N0 B_one_repr
lemma NI883N0 : Nat.card (O ⧸ I883N0) = 779689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI883N0

def I883N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 33, -4, 9, -18]] i)))

def SI883N1: IdealEqSpanCertificate' Table ![![-3, 33, -4, 9, -18]] 
 ![![883, 0, 0, 0, 0], ![0, 883, 0, 0, 0], ![766, 398, 1, 0, 0], ![650, 419, 0, 1, 0], ![204, 806, 0, 0, 1]] where
  M :=![![![-3, 33, -4, 9, -18], ![-18, 87, -102, 14, 18], ![-28, -62, 291, -166, 120], ![332, -840, 520, 383, -756], ![2, 420, -1022, 420, -193]]]
  hmulB := by decide  
  f := ![![![-1387, 3553, -210, 167, -324]], ![![-334, 243, 1138, 104, 354]], ![![-1354, 3190, 335, 192, -120]], ![![-1180, 2725, 398, 173, -66]], ![![-626, 1040, 998, 134, 251]]]
  g := ![![![1, 14, -4, 9, -18], ![74, 23, -102, 14, 18], ![-158, -162, 291, -166, 120], ![-558, 273, 520, 383, -756], ![622, 438, -1022, 420, -193]]]
  hle1 := by decide   
  hle2 := by decide  


def P883P1 : CertificateIrreducibleZModOfList' 883 2 2 9 [12, 436, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [447, 882], [0, 1]]
 g := ![![[625, 716], [692, 529], [634], [94], [112, 710], [93, 485], [6, 878], [609], [447, 1]], ![[148, 167], [511, 354], [634], [94], [485, 173], [553, 398], [420, 5], [609], [11, 882]]]
 h' := ![![[447, 882], [526, 738], [806, 23], [356, 769], [422, 469], [650, 317], [811, 70], [580, 499], [817, 239], [0, 1]], ![[0, 1], [170, 145], [491, 860], [612, 114], [794, 414], [186, 566], [313, 813], [234, 384], [807, 644], [447, 882]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [535]]
 b := ![[], [37, 709]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI883N1 : CertifiedPrimeIdeal' SI883N1 883 where
  n := 2
  hpos := by decide
  P := [12, 436, 1]
  hirr := P883P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4983, -16700, 21258, -1948, -8322]
  a := ![7, -3, -13, 6, -20]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15079, -1080, 21258, -1948, -8322]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI883N1 : Ideal.IsPrime I883N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI883N1 B_one_repr
lemma NI883N1 : Nat.card (O ⧸ I883N1) = 779689 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI883N1

def I883N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-45, 97, -21, 4, -10]] i)))

def SI883N2: IdealEqSpanCertificate' Table ![![-45, 97, -21, 4, -10]] 
 ![![883, 0, 0, 0, 0], ![136, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![672, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-45, 97, -21, 4, -10], ![-8, 3, 19, -9, 4], ![18, -42, 12, 29, -46], ![-58, 260, -369, 46, 82], ![-56, 90, 47, -99, 119]]]
  hmulB := by decide  
  f := ![![![-17997, -217291, 468309, 26532, 168536]], ![![-2832, -34191, 73691, 4175, 26520]], ![![-1135, -13697, 29527, 1673, 10626]], ![![-14218, -171644, 369951, 20960, 133138]], ![![-1979, -23881, 51482, 2917, 18527]]]
  g := ![![![-16, 97, -21, 4, -10], ![5, 3, 19, -9, 4], ![-12, -42, 12, 29, -46], ![-63, 260, -369, 46, 82], ![48, 90, 47, -99, 119]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI883N2 : Nat.card (O ⧸ I883N2) = 883 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI883N2)

lemma isPrimeI883N2 : Ideal.IsPrime I883N2 := prime_ideal_of_norm_prime hp883.out _ NI883N2
def MulI883N0 : IdealMulLeCertificate' Table 
  ![![-35, 271, 204, -1, -156]] ![![-3, 33, -4, 9, -18]]
  ![![-11129, -54906, 190774, -96288, 60852]] where
 M := ![![![-11129, -54906, 190774, -96288, 60852]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI883N1 : IdealMulLeCertificate' Table 
  ![![-11129, -54906, 190774, -96288, 60852]] ![![-45, 97, -21, 4, -10]]
  ![![883, 0, 0, 0, 0]] where
 M := ![![![6550977, -28814939, 39870099, -4471512, -9538166]]]
 hmul := by decide  
 g := ![![![![7419, -32633, 45153, -5064, -10802]]]]
 hle2 := by decide  


def PBC883 : ContainsPrimesAboveP 883 ![I883N0, I883N1, I883N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI883N0
    exact isPrimeI883N1
    exact isPrimeI883N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 883 (by decide) (𝕀 ⊙ MulI883N0 ⊙ MulI883N1)


lemma PB984I16_primes (p : ℕ) :
  p ∈ Set.range ![829, 839, 853, 857, 859, 863, 877, 881, 883] ↔ Nat.Prime p ∧ 827 < p ∧ p ≤ 883 := by
  rw [← List.mem_ofFn']
  convert primes_range 827 883 (by omega)

def PB984I16 : PrimesBelowBoundCertificateInterval O 827 883 984 where
  m := 9
  g := ![3, 4, 2, 2, 4, 3, 2, 3, 3]
  P := ![829, 839, 853, 857, 859, 863, 877, 881, 883]
  hP := PB984I16_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I829N0, I829N1, I829N2]
    · exact ![I839N0, I839N1, I839N2, I839N3]
    · exact ![I853N0, I853N1]
    · exact ![I857N0, I857N1]
    · exact ![I859N0, I859N1, I859N2, I859N3]
    · exact ![I863N0, I863N1, I863N2]
    · exact ![I877N0, I877N1]
    · exact ![I881N0, I881N1, I881N2]
    · exact ![I883N0, I883N1, I883N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC829
    · exact PBC839
    · exact PBC853
    · exact PBC857
    · exact PBC859
    · exact PBC863
    · exact PBC877
    · exact PBC881
    · exact PBC883
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![687241, 687241, 829]
    · exact ![703921, 839, 839, 839]
    · exact ![620650477, 727609]
    · exact ![539415333601, 857]
    · exact ![737881, 859, 859, 859]
    · exact ![744769, 744769, 863]
    · exact ![591559418641, 877]
    · exact ![683797841, 881, 881]
    · exact ![779689, 779689, 883]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI829N0
      exact NI829N1
      exact NI829N2
    · dsimp ; intro j
      fin_cases j
      exact NI839N0
      exact NI839N1
      exact NI839N2
      exact NI839N3
    · dsimp ; intro j
      fin_cases j
      exact NI853N0
      exact NI853N1
    · dsimp ; intro j
      fin_cases j
      exact NI857N0
      exact NI857N1
    · dsimp ; intro j
      fin_cases j
      exact NI859N0
      exact NI859N1
      exact NI859N2
      exact NI859N3
    · dsimp ; intro j
      fin_cases j
      exact NI863N0
      exact NI863N1
      exact NI863N2
    · dsimp ; intro j
      fin_cases j
      exact NI877N0
      exact NI877N1
    · dsimp ; intro j
      fin_cases j
      exact NI881N0
      exact NI881N1
      exact NI881N2
    · dsimp ; intro j
      fin_cases j
      exact NI883N0
      exact NI883N1
      exact NI883N2
  β := ![I829N2, I839N1, I839N2, I839N3, I857N1, I859N1, I859N2, I859N3, I863N2, I877N1, I881N1, I881N2, I883N2]
  Il := ![[I829N2], [I839N1, I839N2, I839N3], [], [I857N1], [I859N1, I859N2, I859N3], [I863N2], [I877N1], [I881N1, I881N2], [I883N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
