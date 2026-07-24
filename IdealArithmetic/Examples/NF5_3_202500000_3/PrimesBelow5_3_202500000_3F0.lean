
import IdealArithmetic.Examples.NF5_3_202500000_3.RI5_3_202500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1297, 915, 1087, -741, -2003]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1297, 915, 1087, -741, -2003]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1297, 915, 1087, -741, -2003], ![2640, 1863, 2212, -1508, -4076], ![5376, 3792, 4507, -3072, -8304], ![4152, 2930, 3478, -2371, -6410], ![1842, 1299, 1545, -1053, -2846]]]
  hmulB := by decide  
  f := ![![![-196, 135, 253, -153, -449]], ![![60, -43, -82, 50, 146]], ![![-48, 24, 43, -24, -72]], ![![-30, 7, 17, -6, -25]], ![![-149, 102, 188, -114, -333]]]
  g := ![![![1650, 915, 1087, -741, -2003], ![3358, 1863, 2212, -1508, -4076], ![6840, 3792, 4507, -3072, -8304], ![5281, 2930, 3478, -2371, -6410], ![2344, 1299, 1545, -1053, -2846]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![26, 20, 20, -14, -37]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![26, 20, 20, -14, -37]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![26, 20, 20, -14, -37], ![60, 37, 58, -38, -104], ![120, 90, 83, -60, -168], ![42, 59, 22, -18, -20], ![60, 33, 48, -33, -103]]]
  hmulB := by decide  
  f := ![![![-164, 119, 224, -137, -400]], ![![66, -33, -58, 32, 98]], ![![24, 42, 95, -72, -192]], ![![111, 52, 134, -113, -289]], ![![-51, 27, 48, -27, -82]]]
  g := ![![![13, 20, 20, -14, -37], ![30, 37, 58, -38, -104], ![60, 90, 83, -60, -168], ![21, 59, 22, -18, -20], ![30, 33, 48, -33, -103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, 10, 18, -11, -32]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-11, 10, 18, -11, -32]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-11, 10, 18, -11, -32], ![12, -3, -7, 4, 12], ![0, 9, 9, -6, -16], ![6, 4, 15, -9, -26], ![-6, 7, 6, -4, -11]]]
  hmulB := by decide  
  f := ![![![-10, -3, -9, 8, 20]], ![![-29, -9, -26, 23, 58]], ![![-113, -37, -99, 89, 222]], ![![-251, -78, -228, 200, 504]], ![![13, 3, 14, -11, -29]]]
  g := ![![![2, 10, 18, -11, -32], ![3, -3, -7, 4, 12], ![2, 9, 9, -6, -16], ![11, 4, 15, -9, -26], ![-2, 7, 6, -4, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1297, 915, 1087, -741, -2003]] ![![26, 20, 20, -14, -37]]
  ![![67760, 47807, 56785, -38711, -104636]] where
 M := ![![![67760, 47807, 56785, -38711, -104636]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![67760, 47807, 56785, -38711, -104636]] ![![26, 20, 20, -14, -37]]
  ![![3540358, 2497772, 2966991, -2022620, -5467200]] where
 M := ![![![3540358, 2497772, 2966991, -2022620, -5467200]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![3540358, 2497772, 2966991, -2022620, -5467200]] ![![-11, 10, 18, -11, -32]]
  ![![11696806, 8252303, 9802459, -6682416, -18062728]] where
 M := ![![![11696806, 8252303, 9802459, -6682416, -18062728]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![11696806, 8252303, 9802459, -6682416, -18062728]] ![![-11, 10, 18, -11, -32]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![38644642, 27264522, 32385910, -22077752, -59676676]]]
 hmul := by decide  
 g := ![![![![19322321, 13632261, 16192955, -11038876, -29838338]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![21, 4, 18, -12, -46]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![21, 4, 18, -12, -46]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![21, 4, 18, -12, -46], ![-120, 17, -192, 112, 368], ![384, -168, 865, -480, -1472], ![-132, 360, -964, 489, 1288], ![216, -214, 750, -398, -1137]]]
  hmulB := by decide  
  f := ![![![711, 488, 574, -392, -1058]], ![![472, 337, 400, -272, -736]], ![![960, 680, 801, -544, -1472]], ![![724, 520, 604, -407, -1104]], ![![336, 234, 278, -190, -513]]]
  g := ![![![7, 4, 18, -12, -46], ![-40, 17, -192, 112, 368], ![128, -168, 865, -480, -1472], ![-44, 360, -964, 489, 1288], ![72, -214, 750, -398, -1137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![21, 4, 18, -12, -46]] ![![21, 4, 18, -12, -46]]
  ![![-1479, 2652, -7752, 3996, 10856]] where
 M := ![![![-1479, 2652, -7752, 3996, 10856]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-1479, 2652, -7752, 3996, 10856]] ![![21, 4, 18, -12, -46]]
  ![![-1508643, 456880, -2951430, 1669088, 5258490]] where
 M := ![![![-1508643, 456880, -2951430, 1669088, 5258490]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-1508643, 456880, -2951430, 1669088, 5258490]] ![![21, 4, 18, -12, -46]]
  ![![-304341999, -26872552, -332996816, 209265688, 752916592]] where
 M := ![![![-304341999, -26872552, -332996816, 209265688, 752916592]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N3 : IdealMulLeCertificate' Table 
  ![![-304341999, -26872552, -332996816, 209265688, 752916592]] ![![21, 4, 18, -12, -46]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3969659973, -31519239300, 74594448930, -36849032340, -92250012990]]]
 hmul := by decide  
 g := ![![![![1323219991, -10506413100, 24864816310, -12283010780, -30750004330]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 12, 13, -9, -24]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![17, 12, 13, -9, -24]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![17, 12, 13, -9, -24], ![36, 24, 33, -22, -60], ![72, 53, 54, -38, -104], ![42, 37, 33, -23, -54], ![30, 19, 23, -16, -47]]]
  hmulB := by decide  
  f := ![![![-41, -16, -43, 37, 94]], ![![-49, -16, -44, 39, 98]], ![![-220, -73, -202, 178, 448]], ![![-414, -133, -369, 327, 822]], ![![3, -1, -2, 1, 3]]]
  g := ![![![5, 12, 13, -9, -24], ![12, 24, 33, -22, -60], ![23, 53, 54, -38, -104], ![7, 37, 33, -23, -54], ![12, 19, 23, -16, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![17, 12, 13, -9, -24]] ![![17, 12, 13, -9, -24]]
  ![![559, 392, 470, -320, -866]] where
 M := ![![![559, 392, 470, -320, -866]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![559, 392, 470, -320, -866]] ![![17, 12, 13, -9, -24]]
  ![![18035, 12732, 15105, -10299, -27834]] where
 M := ![![![18035, 12732, 15105, -10299, -27834]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![18035, 12732, 15105, -10299, -27834]] ![![17, 12, 13, -9, -24]]
  ![![584929, 412644, 490232, -334188, -903336]] where
 M := ![![![584929, 412644, 490232, -334188, -903336]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![584929, 412644, 490232, -334188, -903336]] ![![17, 12, 13, -9, -24]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![18959705, 13376560, 15888925, -10831645, -29278120]]]
 hmul := by decide  
 g := ![![![![3791941, 2675312, 3177785, -2166329, -5855624]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 9, 10, -7, -20]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![13, 9, 10, -7, -20]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 6, 0, 1, 0], ![1, 2, 0, 0, 1]] where
  M :=![![![13, 9, 10, -7, -20], ![12, 17, 4, -4, -4], ![96, 20, 133, -80, -240], ![-6, 66, -112, 55, 162], ![54, -10, 110, -62, -183]]]
  hmulB := by decide  
  f := ![![![1, 25, 54, -39, -106]], ![![132, 27, 84, -80, -196]], ![![76, 40, 101, -84, -216]], ![![282, 78, 224, -203, -506]], ![![25, 9, 24, -21, -53]]]
  g := ![![![-1, 13, 10, -7, -20], ![0, 7, 4, -4, -4], ![-28, 140, 133, -80, -240], ![40, -84, -112, 55, 162], ![-29, 104, 110, -62, -183]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[5, 2], [3, 1]], ![[4, 5], [6, 6]]]
 h' := ![![[3, 6], [6, 4], [0, 1]], ![[0, 1], [4, 3], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113782, -50359, -78485, 84701, 192395]
  a := ![153, 6, 189, -140, -391]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1109, -134765, -78485, 84701, 192395]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 23, 29, -20, -54]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![31, 23, 29, -20, -54]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![3, 6, 1, 0, 0], ![5, 5, 0, 1, 0], ![1, 6, 0, 0, 1]] where
  M :=![![![31, 23, 29, -20, -54], ![72, 46, 59, -42, -112], ![168, 103, 144, -106, -280], ![192, 99, 167, -131, -340], ![36, 29, 31, -20, -55]]]
  hmulB := by decide  
  f := ![![![1, 3, -1, 0, -2]], ![![-24, -2, -29, 18, 64]], ![![-3, -4, 5, -2, -2]], ![![-37, 14, -77, 43, 134]], ![![-5, -8, 10, -4, -5]]]
  g := ![![![14, 39, 29, -20, -54], ![31, 82, 59, -42, -112], ![78, 207, 144, -106, -280], ![98, 256, 167, -131, -340], ![14, 39, 31, -20, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[1, 1], [2, 1]], ![[3, 6], [4, 6]]]
 h' := ![![[2, 6], [4, 6], [0, 1]], ![[0, 1], [2, 1], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [6, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-298039, 172022, -843017, 533847, 1271282]
  a := ![-183, -72, -226, 103, 468]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-244215, -723829, -843017, 533847, 1271282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 6, 11, -7, -20]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![-7, 6, 11, -7, -20]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![-7, 6, 11, -7, -20], ![12, -2, 1, -2, -4], ![24, 13, 24, -22, -56], ![54, 19, 53, -47, -114], ![-6, 3, 1, 0, -3]]]
  hmulB := by decide  
  f := ![![![-667, -470, -559, 381, 1030]], ![![-289, -204, -242, 165, 446]], ![![-966, -681, -810, 552, 1492]], ![![-306, -215, -257, 175, 474]], ![![-611, -431, -512, 349, 943]]]
  g := ![![![3, 6, 11, -7, -20], ![4, -2, 1, -2, -4], ![21, 13, 24, -22, -56], ![41, 19, 53, -47, -114], ![0, 3, 1, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![13, 9, 10, -7, -20]] ![![31, 23, 29, -20, -54]]
  ![![667, 470, 559, -381, -1030]] where
 M := ![![![667, 470, 559, -381, -1030]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![667, 470, 559, -381, -1030]] ![![-7, 6, 11, -7, -20]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3277, -2312, -2746, 1872, 5060]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-3277, -2312, -2746, 1872, 5060]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![7, 7, 1, 0, 0], ![3, 7, 0, 1, 0], ![6, 8, 0, 0, 1]] where
  M :=![![![-3277, -2312, -2746, 1872, 5060], ![-6672, -4707, -5592, 3812, 10304], ![-13584, -9584, -11383, 7760, 20976], ![-10488, -7402, -8788, 5991, 16192], ![-4656, -3284, -3902, 2660, 7191]]]
  hmulB := by decide  
  f := ![![![-23, 24, 50, -32, -92]], ![![48, -1, -8, -4, 0]], ![![29, 19, 43, -36, -92]], ![![57, 17, 38, -37, -92]], ![![18, 12, 22, -20, -49]]]
  g := ![![![-1821, -3334, -2746, 1872, 5060], ![-3708, -6789, -5592, 3812, 10304], ![-7549, -13821, -11383, 7760, 20976], ![-5827, -10669, -8788, 5991, 16192], ![-2588, -4738, -3902, 2660, 7191]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 6, 1] where
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
 g := ![![[6, 1], [5, 3], [1]], ![[0, 10], [9, 8], [1]]]
 h' := ![![[5, 10], [6, 1], [10, 5], [0, 1]], ![[0, 1], [0, 10], [2, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [6, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16621, -5779, -13701, 12677, 31745]
  a := ![38, -1, 47, -37, -97]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13565, -22961, -13701, 12677, 31745]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 4, 13, -11, -28]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![13, 4, 13, -11, -28]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 0, 1, 0, 0], ![0, 3, 0, 1, 0], ![5, 3, 0, 0, 1]] where
  M :=![![![13, 4, 13, -11, -28], ![60, 20, 51, -46, -116], ![264, 87, 234, -210, -520], ![630, 189, 583, -503, -1282], ![-54, -11, -57, 44, 121]]]
  hmulB := by decide  
  f := ![![![125, 100, 123, -83, -226]], ![![276, 188, 219, -150, -404]], ![![107, 81, 99, -67, -182]], ![![114, 79, 92, -63, -170]], ![![149, 109, 131, -89, -241]]]
  g := ![![![8, 11, 13, -11, -28], ![35, 46, 51, -46, -116], ![154, 207, 234, -210, -520], ![375, 504, 583, -503, -1282], ![-34, -46, -57, 44, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 10], [0, 1]]
 g := ![![[0, 1], [], [1]], ![[0, 10], [], [1]]]
 h' := ![![[0, 10], [0, 1], [10], [0, 1]], ![[0, 1], [0, 10], [10], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-708814, -250502, -576007, 539768, 1341720]
  a := ![-259, 5, -320, 250, 662]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-412489, -535906, -576007, 539768, 1341720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, -38, -71, 43, 126]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![55, -38, -71, 43, 126]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![55, -38, -71, 43, 126], ![-36, 24, 43, -26, -76], ![24, -17, -22, 14, 40], ![6, -5, -25, 15, 42], ![30, -21, -29, 18, 53]]]
  hmulB := by decide  
  f := ![![![-145, -102, -121, 83, 224]], ![![-80, -56, -67, 46, 124]], ![![-138, -95, -116, 80, 216]], ![![-154, -107, -127, 89, 238]], ![![-85, -59, -72, 49, 133]]]
  g := ![![![-31, -38, -71, 43, 126], ![18, 24, 43, -26, -76], ![-8, -17, -22, 14, 40], ![-14, -5, -25, 15, 42], ![-11, -21, -29, 18, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-3277, -2312, -2746, 1872, 5060]] ![![13, 4, 13, -11, -28]]
  ![![-145, -102, -121, 83, 224]] where
 M := ![![![-145, -102, -121, 83, 224]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-145, -102, -121, 83, 224]] ![![55, -38, -71, 43, 126]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [9, 11, 4, 12, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 1, 3, 4], [1, 12, 4, 7, 11], [2, 2, 3, 0, 1], [6, 11, 5, 3, 10], [0, 1]]
 g := ![![[1, 6, 8, 5, 1], [0, 1], []], ![[0, 3, 11, 5, 3, 10], [4, 8, 7, 3], [4, 2, 0, 3, 0, 12, 1, 12]], ![[8, 0, 4, 10, 1, 8, 6, 8], [0, 12], [2, 5, 12, 8, 7, 6, 6, 5]], ![[2, 9, 11, 1, 7, 7, 3, 1], [12, 6, 3, 1], [9, 2, 2, 6, 2, 10, 0, 1]], ![[8, 5, 1, 1, 12, 5, 10, 10], [10, 8, 8, 9], [4, 1, 8, 11, 9, 1, 3, 12]]]
 h' := ![![[4, 0, 1, 3, 4], [0, 4, 2, 9, 1], [0, 0, 0, 1], [0, 1]], ![[1, 12, 4, 7, 11], [7, 0, 12, 3], [2, 3, 10, 9, 4], [4, 0, 1, 3, 4]], ![[2, 2, 3, 0, 1], [3, 10, 10, 5, 10], [9, 8, 0, 8], [1, 12, 4, 7, 11]], ![[6, 11, 5, 3, 10], [8, 2, 2, 8, 1], [5, 11, 10, 5, 12], [2, 2, 3, 0, 1]], ![[0, 1], [5, 10, 0, 1, 1], [11, 4, 6, 3, 10], [6, 11, 5, 3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 5, 10, 10], [], [], []]
 b := ![[], [1, 4, 6, 1, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [9, 11, 4, 12, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6733596054034525, 2352909975288548, 5505326668218936, -5030437982713988, -12841298230244432]
  a := ![385, 23, 476, -339, -984]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![517968927233425, 180993075022196, 423486666786072, -386956767901076, -987792171557264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, -141, -339, 270, 706]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-173, -141, -339, 270, 706]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![11, 7, 2, 13, 1]] where
  M :=![![![-173, -141, -339, 270, 706], ![-1248, -346, -995, 902, 2248], ![-5496, -1799, -4968, 4394, 11048], ![-12180, -3929, -10883, 9645, 24232], ![840, 227, 655, -596, -1483]]]
  hmulB := by decide  
  f := ![![![11, 1, 17, -10, -30]], ![![0, 18, -29, 14, 40]], ![![-24, -17, 28, -10, 8]], ![![228, 7, 295, -179, -608]], ![![173, 11, 222, -135, -453]]]
  g := ![![![-467, -299, -103, -524, 706], ![-1528, -946, -323, -1666, 2248], ![-7472, -4655, -1592, -8190, 11048], ![-16396, -10209, -3491, -17963, 24232], ![1009, 624, 213, 1099, -1483]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [13, 8, 10, 14, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 14, 14, 13], [0, 9, 12, 14], [6, 10, 8, 7], [0, 1]]
 g := ![![[12, 0, 14, 9], [16, 1, 9], [1], []], ![[14, 0, 10, 11, 7, 2], [6, 0, 1], [8, 10, 8], [4, 4, 16]], ![[10, 16, 0, 11, 1, 14], [11, 8, 1], [16, 10, 4], [1, 6, 9]], ![[6, 10, 12, 12, 12, 6], [6, 8, 9], [4, 12, 15], [15, 4, 15]]]
 h' := ![![[14, 14, 14, 13], [12, 16, 5, 14], [4, 9, 7, 3], [0, 0, 1], [0, 1]], ![[0, 9, 12, 14], [9, 9, 7, 12], [11, 8, 10, 16], [8, 2, 2, 5], [14, 14, 14, 13]], ![[6, 10, 8, 7], [1, 3, 11, 16], [12, 6, 11, 1], [4, 16, 8, 2], [0, 9, 12, 14]], ![[0, 1], [8, 6, 11, 9], [1, 11, 6, 14], [11, 16, 6, 10], [6, 10, 8, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [4, 10, 13], []]
 b := ![[], [], [1, 7, 2, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [13, 8, 10, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-119392000907, 69764304056, -307668519072, 168086474584, 503078964856]
  a := ![-162, -18, -200, 126, 414]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-332544742019, -203046379408, -77283908752, -374820004032, 503078964856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 1, 17, -10, -30]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![11, 1, 17, -10, -30]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![11, 1, 17, -10, -30], ![0, 18, -29, 14, 40], ![-24, -17, 28, -10, 8], ![228, 7, 295, -179, -608], ![-96, -7, -101, 64, 237]]]
  hmulB := by decide  
  f := ![![![-173, -141, -339, 270, 706]], ![![-165, -95, -238, 196, 506]], ![![-364, -139, -372, 322, 816]], ![![-747, -256, -700, 615, 1550]], ![![-32, -53, -121, 92, 245]]]
  g := ![![![12, 1, 17, -10, -30], ![-24, 18, -29, 14, 40], ![-1, -17, 28, -10, 8], ![258, 7, 295, -179, -608], ![-101, -7, -101, 64, 237]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-173, -141, -339, 270, 706]] ![![11, 1, 17, -10, -30]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![17, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-383, -117, -328, 293, 734]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-383, -117, -328, 293, 734]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![18, 0, 18, 1, 0], ![2, 14, 5, 0, 1]] where
  M :=![![![-383, -117, -328, 293, 734], ![-1740, -563, -1558, 1380, 3468], ![-8064, -2590, -7175, 6364, 15984], ![-17778, -5710, -15834, 14039, 35266], ![1158, 374, 1040, -920, -2313]]]
  hmulB := by decide  
  f := ![![![-47, -33, -36, 25, 68]], ![![-84, -65, -70, 48, 124]], ![![-240, -126, -241, 156, 448]], ![![-276, -158, -260, 171, 486]], ![![-136, -86, -127, 84, 231]]]
  g := ![![![-375, -547, -488, 293, 734], ![-1764, -2585, -2302, 1380, 3468], ![-8136, -11914, -10613, 6364, 15984], ![-17948, -26286, -23414, 14039, 35266], ![1176, 1724, 1535, -920, -2313]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [17, 14, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 2, 16], [14, 16, 3], [0, 1]]
 g := ![![[18, 10, 5], [7, 2, 9], [12, 1], []], ![[16, 12, 16, 6], [8, 3, 5, 6], [18, 9], [1, 9]], ![[2, 10, 12, 8], [6, 2, 18, 15], [7, 4], [14, 9]]]
 h' := ![![[17, 2, 16], [14, 7, 10], [5, 5, 16], [0, 0, 1], [0, 1]], ![[14, 16, 3], [3, 12, 6], [15, 3, 13], [6, 15, 16], [17, 2, 16]], ![[0, 1], [15, 0, 3], [11, 11, 9], [15, 4, 2], [14, 16, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 2], []]
 b := ![[], [17, 17, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [17, 14, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1231511445, -404289053, -1079082605, 965963810, 2420794158]
  a := ![-163, 3, -201, 170, 418]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1234760439, -1805021435, -1608968525, 965963810, 2420794158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![125, -139, -242, 149, 432]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![125, -139, -242, 149, 432]] 
 ![![19, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![125, -139, -242, 149, 432], ![-180, 17, 68, -36, -116], ![-96, -156, -219, 144, 400], ![-102, -110, -152, 103, 282], ![30, -94, -150, 94, 269]]]
  hmulB := by decide  
  f := ![![![-139, 41, -270, 153, 482]], ![![-44, 5, -68, 40, 132]], ![![-60, 64, -219, 116, 328]], ![![-251, -1, -322, 196, 676]], ![![89, 23, 64, -45, -181]]]
  g := ![![![156, -139, -242, 149, 432], ![-44, 17, 68, -36, -116], ![140, -156, -219, 144, 400], ![95, -110, -152, 103, 282], ![97, -94, -150, 94, 269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, 91, 170, -103, -302]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-131, 91, 170, -103, -302]] 
 ![![19, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-131, 91, 170, -103, -302], ![84, -57, -106, 64, 188], ![-48, 38, 71, -44, -128], ![-18, 20, 38, -25, -70], ![-66, 46, 86, -52, -153]]]
  hmulB := by decide  
  f := ![![![37, 31, 26, -19, -48]], ![![31, 24, 24, -17, -44]], ![![14, 12, 7, -6, -16]], ![![21, 19, 16, -12, -26]], ![![19, 15, 12, -9, -25]]]
  g := ![![![73, 91, 170, -103, -302], ![-45, -57, -106, 64, 188], ![32, 38, 71, -44, -128], ![19, 20, 38, -25, -70], ![37, 46, 86, -52, -153]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-383, -117, -328, 293, 734]] ![![125, -139, -242, 149, 432]]
  ![![-3193, 1190, 1926, -912, -3012]] where
 M := ![![![-3193, 1190, 1926, -912, -3012]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![-3193, 1190, 1926, -912, -3012]] ![![-131, 91, 170, -103, -302]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![641003, -441997, -825892, 499719, 1466154]]]
 hmul := by decide  
 g := ![![![![33737, -23263, -43468, 26301, 77166]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -18, -31, 17, 52]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![37, -18, -31, 17, 52]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![4, 11, 14, 1, 0], ![14, 8, 5, 0, 1]] where
  M :=![![![37, -18, -31, 17, 52], ![12, 24, 49, -38, -100], ![168, 37, 134, -118, -296], ![342, 109, 281, -255, -642], ![-6, -21, -29, 24, 65]]]
  hmulB := by decide  
  f := ![![![89, 62, 75, -51, -138]], ![![180, 128, 149, -102, -276]], ![![360, 257, 302, -206, -552]], ![![334, 237, 280, -191, -514]], ![![200, 142, 167, -114, -307]]]
  g := ![![![-33, -27, -23, 17, 52], ![68, 54, 47, -38, -100], ![208, 161, 142, -118, -296], ![450, 350, 307, -255, -642], ![-44, -35, -30, 24, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [12, 1, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 9, 19], [17, 13, 4], [0, 1]]
 g := ![![[5, 20, 18], [21, 3, 12], [8, 3, 1], []], ![[14, 5, 13, 21], [16, 12, 4, 17], [18, 22, 2, 14], [22, 16]], ![[14, 22, 15, 6], [7, 2, 7, 13], [21, 8, 19, 2], [14, 16]]]
 h' := ![![[9, 9, 19], [1, 5, 15], [19, 2, 9], [0, 0, 1], [0, 1]], ![[17, 13, 4], [15, 1, 14], [0, 10, 17], [1, 17, 13], [9, 9, 19]], ![[0, 1], [15, 17, 17], [15, 11, 20], [6, 6, 9], [17, 13, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 8], []]
 b := ![[], [6, 6, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [12, 1, 20, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![991666, -1721575, 5073329, -2618854, -7132624]
  a := ![-47, -7, -58, 36, 120]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4840166, 3658557, 3365235, -2618854, -7132624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-295, 597, 981, -612, -1758]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-295, 597, 981, -612, -1758]] 
 ![![23, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-295, 597, 981, -612, -1758], ![936, 152, 9, -42, -48], ![936, 981, 1274, -846, -2328], ![792, 711, 897, -601, -1644], ![108, 483, 711, -456, -1285]]]
  hmulB := by decide  
  f := ![![![295, -51, 495, -288, -930]], ![![81, -1, 108, -66, -222]], ![![163, -96, 425, -234, -690]], ![![471, 36, 534, -337, -1182]], ![![4, -75, 171, -84, -205]]]
  g := ![![![295, 597, 981, -612, -1758], ![21, 152, 9, -42, -48], ![409, 981, 1274, -846, -2328], ![291, 711, 897, -601, -1644], ![220, 483, 711, -456, -1285]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -36, -94, 80, 204]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-83, -36, -94, 80, 204]] 
 ![![23, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![15, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-83, -36, -94, 80, 204], ![-432, -133, -372, 332, 832], ![-1968, -636, -1761, 1560, 3920], ![-4344, -1398, -3872, 3433, 8624], ![288, 88, 246, -220, -551]]]
  hmulB := by decide  
  f := ![![![-205, -132, -194, 128, 348]], ![![-99, -65, -90, 60, 164]], ![![-121, -88, -107, 72, 188]], ![![-189, -98, -202, 129, 364]], ![![-183, -132, -160, 108, 285]]]
  g := ![![![-183, -36, -94, 80, 204], ![-765, -133, -372, 332, 832], ![-3591, -636, -1761, 1560, 3920], ![-7903, -1398, -3872, 3433, 8624], ![507, 88, 246, -220, -551]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![37, -18, -31, 17, 52]] ![![-295, 597, 981, -612, -1758]]
  ![![-37699, 26145, 48862, -29591, -86782]] where
 M := ![![![-37699, 26145, 48862, -29591, -86782]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-37699, 26145, 48862, -29591, -86782]] ![![-83, -36, -94, 80, 204]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-775951, 535049, 999764, -604923, -1774818]]]
 hmul := by decide  
 g := ![![![![-33737, 23263, 43468, -26301, -77166]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB696I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB696I0 : PrimesBelowBoundCertificateInterval O 1 23 696 where
  m := 9
  g := ![5, 5, 5, 3, 3, 1, 2, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB696I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 49, 7]
    · exact ![121, 121, 11]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![6859, 19, 19]
    · exact ![12167, 23, 23]
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
      exact NI3N0
      exact NI3N0
      exact NI3N0
      exact NI3N0
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
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I17N1, I19N1, I19N2, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2], [], [I17N1], [I19N1, I19N2], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
