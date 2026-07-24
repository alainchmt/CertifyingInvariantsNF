
import IdealArithmetic.Examples.NF5_3_1215000000_3.RI5_3_1215000000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 30, 10, -12, 4]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-17, 30, 10, -12, 4]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![6, 14, 1, 0, 0], ![16, 7, 0, 1, 0], ![7, 8, 0, 0, 1]] where
  M :=![![![-17, 30, 10, -12, 4], ![-48, 9, 70, 28, -48], ![576, -54, -239, 44, 112], ![-648, 198, 118, -141, 112], ![-60, -94, 130, 144, -97]]]
  hmulB := by decide  
  f := ![![![-5296093, 3222330, 463494, 388972, -828660]], ![![9943920, -6050231, -870254, -730332, 1555888]], ![![3060954, -1862392, -267883, -224812, 478936]], ![![-88760, 54005, 7768, 6519, -13888]], ![![1025365, -623868, -89736, -75308, 160435]]]
  g := ![![![3, -2, 10, -12, 4], ![-20, -27, 70, 28, -48], ![18, 72, -239, 44, 112], ![4, -47, 118, -141, 112], ![-85, -74, 130, 144, -97]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [28, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 28], [0, 1]]
 g := ![![[17, 28], [1], [], [17, 1]], ![[0, 1], [1], [], [5, 28]]]
 h' := ![![[17, 28], [1, 17], [0, 28], [17], [0, 1]], ![[0, 1], [0, 12], [12, 1], [17], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [25, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [28, 12, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34391, -4042, 7708, 4973, 4916]
  a := ![0, 4, 9, -4, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6711, -6417, 7708, 4973, 4916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-92147, 56066, 8064, 6768, -14418]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-92147, 56066, 8064, 6768, -14418]] 
 ![![29, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![-92147, 56066, 8064, 6768, -14418], ![173016, -105269, -15142, -12708, 27072], ![-324864, 197654, 28435, 23860, -50832], ![218484, -132926, -19126, -16043, 34184], ![-221730, 134906, 19406, 16282, -34691]]]
  hmulB := by decide  
  f := ![![![8837, 4558, 368, -892, -1534]], ![![3682, 1867, 134, -388, -652]], ![![6352, 3114, 167, -724, -1168]], ![![2222, 842, -90, -379, -508]], ![![8198, 3870, 126, -1010, -1567]]]
  g := ![![![-17483, 56066, 8064, 6768, -14418], ![32826, -105269, -15142, -12708, 27072], ![-61636, 197654, 28435, 23860, -50832], ![41454, -132926, -19126, -16043, 34184], ![-42070, 134906, 19406, 16282, -34691]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-65, -26, -4, 4, 6]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![-65, -26, -4, 4, 6]] 
 ![![29, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-65, -26, -4, 4, 6], ![-72, -67, -10, 4, 16], ![-192, -70, -11, 12, 16], ![-60, -66, -10, 3, 16], ![-162, -66, -10, 10, 15]]]
  hmulB := by decide  
  f := ![![![-1, 10, 4, -8, -6]], ![![2, 5, 2, -4, -4]], ![![13, 4, -3, -4, -2]], ![![2, 6, 2, -5, -4]], ![![18, 2, -2, -2, -5]]]
  g := ![![![11, -26, -4, 4, 6], ![32, -67, -10, 4, 16], ![29, -70, -11, 12, 16], ![32, -66, -10, 3, 16], ![28, -66, -10, 10, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![187, 46, -22, -44, -52]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![187, 46, -22, -44, -52]] 
 ![![29, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![187, 46, -22, -44, -52], ![624, 157, -74, -148, -176], ![2112, 522, -251, -500, -592], ![3240, 806, -386, -769, -912], ![3948, 978, -470, -936, -1109]]]
  hmulB := by decide  
  f := ![![![-73, 26, 22, -20, 4]], ![![-52, 17, 18, -12, 0]], ![![18, 2, -11, -4, 8]], ![![-85, 28, 24, -21, 4]], ![![-14, 2, 10, 0, -5]]]
  g := ![![![23, 46, -22, -44, -52], ![76, 157, -74, -148, -176], ![262, 522, -251, -500, -592], ![401, 806, -386, -769, -912], ![490, 978, -470, -936, -1109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N3 : Nat.card (O ⧸ I29N3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N3)

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := prime_ideal_of_norm_prime hp29.out _ NI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-17, 30, 10, -12, 4]] ![![-92147, 56066, 8064, 6768, -14418]]
  ![![-389, 84, 138, -52, -26]] where
 M := ![![![-389, 84, 138, -52, -26]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-389, 84, 138, -52, -26]] ![![-65, -26, -4, 4, 6]]
  ![![73, -26, -22, 20, -4]] where
 M := ![![![73, -26, -22, 20, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![73, -26, -22, 20, -4]] ![![187, 46, -22, -44, -52]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-29, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2, I29N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
    exact isPrimeI29N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1 ⊙ MulI29N2)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3712342, 2258721, 324890, 272653, -580857]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![-3712342, 2258721, 324890, 272653, -580857]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![30, 26, 23, 1, 0], ![27, 24, 5, 0, 1]] where
  M :=![![![-3712342, 2258721, 324890, 272653, -580857], ![6970284, -4240962, -610013, -511934, 1090612], ![-13087344, 7962817, 1145354, 961198, -2047736], ![8801274, -5354981, -770255, -646415, 1377090], ![-8932371, 5434799, 781726, 656033, -1397630]]]
  hmulB := by decide  
  f := ![![![128, -89, -84, 29, 29]], ![![-348, 44, -31, -110, 116]], ![![-1392, -153, 728, 170, -440]], ![![-1110, -184, 397, 73, -192]], ![![-435, -57, 30, -44, 49]]]
  g := ![![![122297, 293881, -98124, 272653, -580857], ![-229620, -551786, 184239, -511934, 1090612], ![431148, 1036043, -345920, 961198, -2047736], ![-289926, -696721, 232640, -646415, 1377090], ![294279, 707131, -236093, 656033, -1397630]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [26, 29, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 29, 1], [21, 1, 30], [0, 1]]
 g := ![![[29, 5, 2], [3, 16, 16], [12, 11, 28], [1]], ![[5, 15, 14, 25], [18, 26, 13, 8], [2, 27, 1, 14], [29, 8, 5, 1]], ![[1, 14, 3, 17], [11, 26, 23, 11], [15, 1, 12, 13], [20, 1, 23, 30]]]
 h' := ![![[21, 29, 1], [15, 28, 8], [29, 11, 4], [5, 2, 11], [0, 1]], ![[21, 1, 30], [9, 13, 5], [25, 28, 15], [13, 25, 13], [21, 29, 1]], ![[0, 1], [27, 21, 18], [3, 23, 12], [30, 4, 7], [21, 1, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 26], []]
 b := ![[], [20, 25, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [26, 29, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8195148248, 2046051496, -1165615014, -2009481190, -2081542748]
  a := ![3, -4, 59, -65, -178]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4021975424, 3362889948, 1789037616, -2009481190, -2081542748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, 43, 6, 5, -11]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-70, 43, 6, 5, -11]] 
 ![![31, 0, 0, 0, 0], ![17, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![30, 0, 0, 1, 0], ![19, 0, 0, 0, 1]] where
  M :=![![![-70, 43, 6, 5, -11], ![132, -80, -11, -10, 20], ![-240, 151, 20, 18, -40], ![174, -99, -17, -15, 26], ![-165, 105, 16, 11, -30]]]
  hmulB := by decide  
  f := ![![![-2044, -1219, -184, 121, 287]], ![![-1232, -735, -111, 73, 173]], ![![-1572, -938, -142, 93, 221]], ![![-2082, -1241, -187, 123, 292]], ![![-1417, -846, -128, 84, 199]]]
  g := ![![![-28, 43, 6, 5, -11], ![53, -80, -11, -10, 20], ![-97, 151, 20, 18, -40], ![70, -99, -17, -15, 26], ![-66, 105, 16, 11, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12854, 7818, 1127, 943, -2011]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-12854, 7818, 1127, 943, -2011]] 
 ![![31, 0, 0, 0, 0], ![30, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-12854, 7818, 1127, 943, -2011], ![24132, -14681, -2112, -1768, 3772], ![-45264, 27560, 3943, 3320, -7072], ![30366, -18516, -2628, -2245, 4754], ![-30861, 18794, 2691, 2281, -4838]]]
  hmulB := by decide  
  f := ![![![17188, 5578, -1259, -3409, -4305]], ![![18300, 5883, -1374, -3658, -4606]], ![![21912, 6828, -1775, -4490, -5602]], ![![7782, 1996, -888, -1813, -2162]], ![![13423, 3732, -1358, -2980, -3613]]]
  g := ![![![-8617, 7818, 1127, 943, -2011], ![16178, -14681, -2112, -1768, 3772], ![-30350, 27560, 3943, 3320, -7072], ![20368, -18516, -2628, -2245, 4754], ![-20695, 18794, 2691, 2281, -4838]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![-3712342, 2258721, 324890, 272653, -580857]] ![![-70, 43, 6, 5, -11]]
  ![![623324539, -379252628, -54550996, -45780122, 97529270]] where
 M := ![![![623324539, -379252628, -54550996, -45780122, 97529270]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![623324539, -379252628, -54550996, -45780122, 97529270]] ![![-12854, 7818, 1127, 943, -2011]]
  ![![31, 0, 0, 0, 0]] where
 M := ![![![-19095151746380, 11618163467142, 1671135154747, 1402445018621, -2987747225281]]]
 hmul := by decide  
 g := ![![![![-615972636980, 374779466682, 53907585637, 45240161891, -96378942751]]]]
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

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27995, -17032, -2450, -2056, 4380]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![27995, -17032, -2450, -2056, 4380]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![10, 32, 12, 1, 0], ![14, 26, 28, 0, 1]] where
  M :=![![![27995, -17032, -2450, -2056, 4380], ![-52560, 31981, 4600, 3860, -8224], ![98688, -60044, -8635, -7248, 15440], ![-66360, 40380, 5806, 4875, -10384], ![67356, -40980, -5894, -4948, 10539]]]
  hmulB := by decide  
  f := ![![![47, 16, -2, -8, -12]], ![![144, 41, -16, -28, -32]], ![![384, 124, -31, -96, -112]], ![![278, 84, -26, -61, -72]], ![![430, 134, -38, -100, -117]]]
  g := ![![![-345, -1760, -2714, -2056, 4380], ![648, 3305, 5096, 3860, -8224], ![-1216, -6204, -9567, -7248, 15440], ![818, 4172, 6434, 4875, -10384], ![-830, -4234, -6530, -4948, 10539]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [12, 0, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 2, 36], [30, 34, 1], [0, 1]]
 g := ![![[5, 17, 9], [23, 25], [23, 17, 33], [7, 1], []], ![[18, 15, 35, 27], [11, 3], [8, 32, 0, 16], [21, 9], [3, 1]], ![[7, 19, 25, 11], [8, 30], [24, 17, 16, 33], [0, 4], [1, 1]]]
 h' := ![![[14, 2, 36], [13, 17, 3], [20, 7, 5], [27, 25, 12], [0, 0, 1], [0, 1]], ![[30, 34, 1], [28, 18, 11], [30, 12, 15], [3, 23, 13], [12, 7, 34], [14, 2, 36]], ![[0, 1], [5, 2, 23], [8, 18, 17], [0, 26, 12], [0, 30, 2], [30, 34, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 24], []]
 b := ![[], [2, 11, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [12, 0, 30, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4978858, 1397262, -680352, -1346914, -1308530]
  a := ![1, 1, 6, -5, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![993714, 2122170, 1408688, -1346914, -1308530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, -16, 2, 8, 12]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-47, -16, 2, 8, 12]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![27, 13, 1, 0, 0], ![28, 22, 0, 1, 0], ![13, 25, 0, 0, 1]] where
  M :=![![![-47, -16, 2, 8, 12], ![-144, -41, 16, 28, 32], ![-384, -124, 31, 96, 112], ![-600, -148, 58, 129, 176], ![-756, -196, 94, 172, 193]]]
  hmulB := by decide  
  f := ![![![-27995, 17032, 2450, 2056, -4380]], ![![52560, -31981, -4600, -3860, 8224]], ![![-4629, 2815, 405, 340, -724]], ![![11860, -7218, -1038, -871, 1856]], ![![23857, -14517, -2088, -1752, 3733]]]
  g := ![![![-13, -14, 2, 8, 12], ![-48, -45, 16, 28, 32], ![-145, -147, 31, 96, 112], ![-218, -220, 58, 129, 176], ![-287, -271, 94, 172, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P1 : CertificateIrreducibleZModOfList' 37 2 2 5 [33, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 36], [0, 1]]
 g := ![![[33, 9], [36], [5, 36], [34], [1]], ![[0, 28], [36], [21, 1], [34], [1]]]
 h' := ![![[21, 36], [26, 34], [20, 6], [4, 31], [4, 21], [0, 1]], ![[0, 1], [0, 3], [35, 31], [26, 6], [1, 16], [21, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [13, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N1 : CertifiedPrimeIdeal' SI37N1 37 where
  n := 2
  hpos := by decide
  P := [33, 16, 1]
  hirr := P37P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-448969, -55452, 92173, 68205, 78462]
  a := ![1, -8, -30, 18, 87]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-158578, -127453, 92173, 68205, 78462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N1 B_one_repr
lemma NI37N1 : Nat.card (O ⧸ I37N1) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![27995, -17032, -2450, -2056, 4380]] ![![-47, -16, 2, 8, 12]]
  ![![37, 0, 0, 0, 0]] where
 M := ![![![-37, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149, 464, -396, -264, 362]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-149, 464, -396, -264, 362]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![33, 4, 39, 26, 1]] where
  M :=![![![-149, 464, -396, -264, 362], ![-4344, 81, 2440, -68, -1056], ![12672, -2892, -4007, 2768, -272], ![3804, 2772, -5978, -4245, 6064], ![-12942, 608, 7486, 1410, -4645]]]
  hmulB := by decide  
  f := ![![![129911, 77600, 11768, -7724, -18290]], ![![219480, 131113, 19888, -13044, -30896]], ![![370752, 221516, 33617, -22016, -52176]], ![![203316, 121548, 18478, -12037, -28584]], ![![615525, 367792, 55829, -36536, -86611]]]
  g := ![![![-295, -24, -354, -236, 362], ![744, 105, 1064, 668, -1056], ![528, -44, 161, 240, -272], ![-4788, -524, -5914, -3949, 6064], ![3423, 468, 4601, 2980, -4645]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 4 2 5 [31, 38, 39, 13, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 29, 21, 9], [4, 1, 24, 36], [17, 10, 37, 37], [0, 1]]
 g := ![![[13, 7, 9, 36], [5, 29, 9], [19, 25, 8], [28, 1], []], ![[31, 17, 28, 6, 24, 32], [39, 11, 16], [18, 22, 21], [25, 22, 12, 16, 10, 39], [19, 22, 40]], ![[13, 29, 28, 35, 38, 21], [34, 6, 32], [33, 34, 4], [17, 17, 0, 30, 24, 33], [7, 9, 25]], ![[38, 18, 3, 6, 17, 23], [30, 22, 8], [29, 3, 2], [20, 37, 34, 31], [1, 29, 16]]]
 h' := ![![[7, 29, 21, 9], [17, 40, 32, 35], [34, 16, 3, 38], [34, 12, 18, 7], [0, 0, 1], [0, 1]], ![[4, 1, 24, 36], [3, 10, 36, 9], [8, 30, 29, 37], [19, 13, 14, 12], [34, 27, 40, 31], [7, 29, 21, 9]], ![[17, 10, 37, 37], [8, 19, 20, 2], [23, 37, 18, 14], [29, 27, 40, 39], [4, 37, 33, 10], [4, 1, 24, 36]], ![[0, 1], [38, 13, 35, 36], [5, 40, 32, 34], [24, 30, 10, 24], [12, 18, 8], [17, 10, 37, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [20, 0, 12], []]
 b := ![[], [], [40, 15, 5, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 4
  hpos := by decide
  P := [31, 38, 39, 13, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7658215756, -14097150, 1343341444, 198751517, 1407367282]
  a := ![-1, 11, 13, 5, -34]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1319544782, -137647958, -1305950794, -887629215, 1407367282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 2825761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129911, -77600, -11768, 7724, 18290]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-129911, -77600, -11768, 7724, 18290]] 
 ![![41, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![-129911, -77600, -11768, 7724, 18290], ![-219480, -131113, -19888, 13044, 30896], ![-370752, -221516, -33617, 22016, 52176], ![-203316, -121548, -18478, 12037, 28584], ![-325998, -194848, -29602, 19322, 45849]]]
  hmulB := by decide  
  f := ![![![149, -464, 396, 264, -362]], ![![175, -217, 124, 124, -142]], ![![-280, -20, 175, -16, -64]], ![![-31, -260, 310, 213, -298]], ![![352, -128, -86, 30, 25]]]
  g := ![![![27425, -77600, -11768, 7724, 18290], ![46343, -131113, -19888, 13044, 30896], ![78316, -221516, -33617, 22016, 52176], ![43011, -121548, -18478, 12037, 28584], ![68926, -194848, -29602, 19322, 45849]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-149, 464, -396, -264, 362]] ![![-129911, -77600, -11768, 7724, 18290]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![-41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 12, 3, -7, 3]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-16, 12, 3, -7, 3]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![11, 38, 38, 1, 0], ![6, 21, 18, 0, 1]] where
  M :=![![![-16, 12, 3, -7, 3], ![-36, -3, 38, 12, -28], ![336, -38, -139, 20, 48], ![-270, 114, 38, -97, 54], ![-3, -40, 71, 59, -80]]]
  hmulB := by decide  
  f := ![![![62, 20, -7, -15, -19]], ![![228, 51, -26, -52, -60]], ![![720, 194, -85, -172, -208]], ![![880, 228, -103, -208, -249]], ![![453, 117, -53, -107, -128]]]
  g := ![![![1, 5, 5, -7, 3], ![0, 3, 2, 12, -28], ![-4, -42, -41, 20, 48], ![11, 62, 64, -97, 54], ![-4, -14, -17, 59, -80]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [8, 13, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 35, 42], [35, 7, 1], [0, 1]]
 g := ![![[15, 33, 38], [1, 34, 1], [7, 14], [31, 1, 1], []], ![[13, 41, 25, 7], [28, 36, 31, 28], [1, 21], [20, 6, 8, 37], [17, 1]], ![[2, 40, 37, 9], [10, 2, 3, 40], [17, 23], [37, 31, 5, 21], [15, 1]]]
 h' := ![![[9, 35, 42], [35, 17, 34], [1, 5, 42], [10, 19, 10], [0, 0, 1], [0, 1]], ![[35, 7, 1], [38, 39, 6], [15, 32, 31], [18, 31, 8], [31, 14, 7], [9, 35, 42]], ![[0, 1], [16, 30, 3], [17, 6, 13], [29, 36, 25], [30, 29, 35], [35, 7, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40, 12], []]
 b := ![[], [41, 6, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [8, 13, 42, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11666888, -149392, -7370482, -1658970, 4870156]
  a := ![0, -16, -10, -18, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16154, -915856, -744010, -1658970, 4870156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62, 20, -7, -15, -19]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![62, 20, -7, -15, -19]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![20, 10, 1, 0, 0], ![29, 25, 0, 1, 0], ![14, 14, 0, 0, 1]] where
  M :=![![![62, 20, -7, -15, -19], ![228, 51, -26, -52, -60], ![720, 194, -85, -172, -208], ![1134, 274, -134, -267, -314], ![1359, 348, -161, -323, -386]]]
  hmulB := by decide  
  f := ![![![-16, 12, 3, -7, 3]], ![![-36, -3, 38, 12, -28]], ![![-8, 4, 7, 0, -4]], ![![-38, 9, 25, 0, -13]], ![![-17, 2, 15, 3, -10]]]
  g := ![![![21, 17, -7, -15, -19], ![72, 57, -26, -52, -60], ![240, 192, -85, -172, -208], ![371, 295, -134, -267, -314], ![450, 359, -161, -323, -386]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P1 : CertificateIrreducibleZModOfList' 43 2 2 5 [41, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 42], [0, 1]]
 g := ![![[32, 21], [2, 4], [17], [14, 11], [1]], ![[0, 22], [0, 39], [17], [30, 32], [1]]]
 h' := ![![[21, 42], [4, 8], [1, 2], [28, 19], [2, 21], [0, 1]], ![[0, 1], [0, 35], [0, 41], [40, 24], [13, 22], [21, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [26, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N1 : CertifiedPrimeIdeal' SI43N1 43 where
  n := 2
  hpos := by decide
  P := [41, 22, 1]
  hirr := P43P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34067, -3642, 11692, 5121, -504]
  a := ![13, 8, 11, 2, -29]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-9520, -5617, 11692, 5121, -504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N1 B_one_repr
lemma NI43N1 : Nat.card (O ⧸ I43N1) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-16, 12, 3, -7, 3]] ![![62, 20, -7, -15, -19]]
  ![![43, 0, 0, 0, 0]] where
 M := ![![![43, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75472, -45920, -6605, -5543, 11809]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![75472, -45920, -6605, -5543, 11809]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![3, 43, 35, 1, 0], ![18, 44, 44, 0, 1]] where
  M :=![![![75472, -45920, -6605, -5543, 11809], ![-141708, 86219, 12402, 10408, -22172], ![266064, -161886, -23285, -19540, 41632], ![-178938, 108866, 15660, 13143, -27994], ![181587, -110492, -15891, -13335, 28416]]]
  hmulB := by decide  
  f := ![![![74, 56, 13, -7, -13]], ![![156, 81, 18, 0, -28]], ![![336, 146, -31, -20, 0]], ![![396, 189, -4, -16, -27]], ![![495, 236, -7, -21, -32]]]
  g := ![![![-2563, -6961, -7068, -5543, 11809], ![4812, 13069, 13270, 10408, -22172], ![-9036, -24542, -24919, -19540, 41632], ![6075, 16499, 16753, 13143, -27994], ![-6168, -16753, -17010, -13335, 28416]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [6, 4, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 31, 33], [44, 15, 14], [0, 1]]
 g := ![![[46, 46, 6], [34, 17, 2], [3, 20, 9], [5, 3, 1], []], ![[27, 43, 26, 40], [18, 20], [16, 44, 36, 43], [20, 14, 24, 46], [2, 8]], ![[33, 4, 40, 37], [13, 39, 37, 28], [14, 12, 1, 18], [39, 5, 26, 12], [21, 8]]]
 h' := ![![[6, 31, 33], [31, 39, 10], [29, 16, 40], [17, 9, 44], [0, 0, 1], [0, 1]], ![[44, 15, 14], [35, 45, 27], [4, 23], [46, 36, 17], [24, 34, 15], [6, 31, 33]], ![[0, 1], [13, 10, 10], [1, 8, 7], [12, 2, 33], [24, 13, 31], [44, 15, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 23], []]
 b := ![[], [0, 3, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [6, 4, 44, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72840, -7212, -37449, -7283, 23708]
  a := ![-1, -4, -2, -4, 5]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7065, -15685, -17568, -7283, 23708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227, -137, -21, 14, 32]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-227, -137, -21, 14, 32]] 
 ![![47, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![38, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![-227, -137, -21, 14, 32], ![-384, -230, -37, 22, 56], ![-672, -387, -50, 38, 88], ![-336, -221, -37, 27, 48], ![-576, -339, -55, 30, 85]]]
  hmulB := by decide  
  f := ![![![6587, -3995, -577, -486, 1024]], ![![159, -95, -14, -12, 24]], ![![5822, -3529, -510, -430, 904]], ![![1356, -817, -119, -101, 208]], ![![6790, -4113, -595, -502, 1053]]]
  g := ![![![-14, -137, -21, 14, 32], ![-24, -230, -37, 22, 56], ![-45, -387, -50, 38, 88], ![-17, -221, -37, 27, 48], ![-37, -339, -55, 30, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1

def I47N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0, -1, -1]] i)))

def SI47N2: IdealEqSpanCertificate' Table ![![2, 1, 0, -1, -1]] 
 ![![47, 0, 0, 0, 0], ![21, 1, 0, 0, 0], ![29, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![2, 1, 0, -1, -1], ![12, 2, -1, -2, -4], ![48, 9, -10, -10, -8], ![42, 19, -1, -17, -18], ![81, 15, -10, -15, -22]]]
  hmulB := by decide  
  f := ![![![160, -177, -26, -13, 45]], ![![60, -75, -11, -5, 19]], ![![112, -122, -18, -9, 31]], ![![34, -47, -7, -3, 12]], ![![25, -28, -4, -2, 7]]]
  g := ![![![0, 1, 0, -1, -1], ![1, 2, -1, -2, -4], ![7, 9, -10, -10, -8], ![0, 19, -1, -17, -18], ![8, 15, -10, -15, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N2 : Nat.card (O ⧸ I47N2) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N2)

lemma isPrimeI47N2 : Ideal.IsPrime I47N2 := prime_ideal_of_norm_prime hp47.out _ NI47N2
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![75472, -45920, -6605, -5543, 11809]] ![![-227, -137, -21, 14, 32]]
  ![![160, -177, -26, -13, 45]] where
 M := ![![![160, -177, -26, -13, 45]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI47N1 : IdealMulLeCertificate' Table 
  ![![160, -177, -26, -13, 45]] ![![2, 1, 0, -1, -1]]
  ![![47, 0, 0, 0, 0]] where
 M := ![![![47, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1, I47N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
    exact isPrimeI47N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
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


def P53P0 : CertificateIrreducibleZModOfList' 53 5 2 5 [46, 21, 19, 13, 15, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 8, 34, 20, 35], [48, 14, 24, 36, 46], [31, 26, 34, 21, 32], [13, 4, 14, 29, 46], [0, 1]]
 g := ![![[15, 15, 31, 42, 47], [6, 9, 16, 7], [11, 30, 24], [38, 1], []], ![[5, 6, 36, 15, 30, 42, 17, 22], [44, 25, 35, 38], [33, 46, 31, 46, 27, 16, 37, 45], [14, 43, 38, 49], [27, 38, 20, 40, 19, 6, 19, 51]], ![[17, 12, 10, 51, 7, 50, 13, 49], [5, 49, 8, 24], [39, 38, 17, 26, 21, 29, 12, 16], [0, 46, 9, 42], [5, 37, 4, 27, 31, 17, 49, 28]], ![[52, 14, 47, 41, 45, 33, 46, 2], [23, 24, 8, 17], [1, 31, 28, 11, 35, 50, 50, 22], [17, 16, 1, 4], [35, 8, 26, 26, 9, 21, 13, 14]], ![[7, 46, 20, 12, 9, 29, 46, 37], [35, 50, 20, 25], [43, 3, 7, 50, 33, 35, 30, 13], [13, 30, 14, 29], [2, 42, 19, 7, 24, 5, 27, 28]]]
 h' := ![![[52, 8, 34, 20, 35], [35, 37, 26, 40, 10], [24, 33, 26, 16, 22], [1, 4, 52, 17], [0, 0, 0, 1], [0, 1]], ![[48, 14, 24, 36, 46], [26, 22, 35, 34, 27], [6, 51, 47, 30, 41], [38, 0, 38, 8, 36], [29, 41, 11, 6, 7], [52, 8, 34, 20, 35]], ![[31, 26, 34, 21, 32], [22, 8, 46, 21, 24], [27, 35, 48, 42, 17], [44, 1, 17, 6, 9], [16, 38, 30, 1, 28], [48, 14, 24, 36, 46]], ![[13, 4, 14, 29, 46], [44, 32, 21, 38, 40], [28, 45, 51, 5, 21], [26, 35, 7, 52, 2], [38, 26, 20, 51, 51], [31, 26, 34, 21, 32]], ![[0, 1], [39, 7, 31, 26, 5], [35, 48, 40, 13, 5], [51, 13, 45, 23, 6], [38, 1, 45, 47, 20], [13, 4, 14, 29, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 8, 47, 15], [], [], []]
 b := ![[], [7, 22, 20, 18, 45], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 5
  hpos := by decide
  P := [46, 21, 19, 13, 15, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17027669023007, -4126225866031, 2811348167226, 4113508777003, 3792379102146]
  a := ![3, -11, -14, -1, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-321276774019, -77853318227, 53044305042, 77613373151, 71554322682]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![257, 195, -309, 22, 104]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![257, 195, -309, 22, 104]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![27, 38, 26, 1, 0], ![3, 50, 25, 0, 1]] where
  M :=![![![257, 195, -309, 22, 104], ![-1248, 30, 567, -410, 88], ![-1056, -183, 1202, 1310, -1640], ![10464, -1417, -4965, -233, 2576], ![-8568, 1993, 3081, -642, -1031]]]
  hmulB := by decide  
  f := ![![![49915, 29725, 4467, -3014, -7064]], ![![84768, 50332, 7497, -5194, -12056]], ![![144672, 85403, 12496, -9118, -20776]], ![![142587, 84462, 12490, -8839, -20360]], ![![137883, 81639, 12056, -8566, -19703]]]
  g := ![![![-11, -99, -59, 22, 104], ![162, 190, 153, -410, 88], ![-534, 543, 138, 1310, -1640], ![153, -2057, -1073, -233, 2576], ![201, 1321, 772, -642, -1031]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [56, 34, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 38, 46], [34, 20, 13], [0, 1]]
 g := ![![[3, 12, 53], [51, 29, 28], [40, 20], [10, 1, 20], [1]], ![[45, 30, 10, 22], [57, 28, 52, 57], [12, 29], [13, 16, 29, 28], [4, 28, 20, 45]], ![[20, 31, 23, 2], [3, 32, 18, 39], [16, 4], [35, 25, 17, 43], [12, 25, 4, 14]]]
 h' := ![![[9, 38, 46], [35, 58, 42], [17, 24, 21], [30, 26, 16], [3, 25, 43], [0, 1]], ![[34, 20, 13], [29, 6, 27], [28, 49, 49], [46, 13, 41], [33, 37, 4], [9, 38, 46]], ![[0, 1], [47, 54, 49], [30, 45, 48], [10, 20, 2], [46, 56, 12], [34, 20, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 33], []]
 b := ![[], [17, 1, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [56, 34, 16, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-644176, -1236984, -507029, 986625, 1053630]
  a := ![1, -6, -8, -2, 21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-515999, -1549326, -889831, 986625, 1053630]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49915, 29725, 4467, -3014, -7064]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![49915, 29725, 4467, -3014, -7064]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![28, 7, 1, 0, 0], ![20, 49, 0, 1, 0], ![25, 11, 0, 0, 1]] where
  M :=![![![49915, 29725, 4467, -3014, -7064], ![84768, 50332, 7497, -5194, -12056], ![144672, 85403, 12496, -9118, -20776], ![82272, 47589, 6519, -5683, -12208], ![130152, 75851, 10653, -8702, -19085]]]
  hmulB := by decide  
  f := ![![![257, 195, -309, 22, 104]], ![![-1248, 30, 567, -410, 88]], ![![-44, 93, -59, -16, 32]], ![![-772, 67, 282, -337, 152]], ![![-269, 122, 27, -78, 43]]]
  g := ![![![2741, 3794, 4467, -3014, -7064], ![4748, 6525, 7497, -5194, -12056], ![8416, 11411, 12496, -9118, -20776], ![5400, 7029, 6519, -5683, -12208], ![8187, 10807, 10653, -8702, -19085]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [42, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 58], [0, 1]]
 g := ![![[21, 26], [24, 45], [41], [19, 27], [3, 1]], ![[40, 33], [41, 14], [41], [41, 32], [6, 58]]]
 h' := ![![[3, 58], [54, 47], [6, 35], [28, 49], [51, 26], [0, 1]], ![[0, 1], [18, 12], [52, 24], [57, 10], [11, 33], [3, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [10, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [42, 56, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-954, -78, 602, 291, -426]
  a := ![4, 2, 2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-220, -235, 602, 291, -426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![257, 195, -309, 22, 104]] ![![49915, 29725, 4467, -3014, -7064]]
  ![![59, 0, 0, 0, 0]] where
 M := ![![![59, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-709, 432, 62, 50, -110]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-709, 432, 62, 50, -110]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![7, 38, 47, 1, 0], ![49, 20, 33, 0, 1]] where
  M :=![![![-709, 432, 62, 50, -110], ![1320, -807, -108, -96, 200], ![-2400, 1508, 185, 184, -384], ![1644, -988, -144, -151, 268], ![-1674, 1032, 162, 130, -293]]]
  hmulB := by decide  
  f := ![![![5411, 3232, 490, -322, -762]], ![![9144, 5461, 828, -544, -1288]], ![![15456, 9228, 1397, -920, -2176]], ![![18365, 10966, 1661, -1093, -2586]], ![![15929, 9512, 1441, -948, -2243]]]
  g := ![![![71, 12, 22, 50, -110], ![-128, -19, -36, -96, 200], ![248, 36, 69, 184, -384], ![-171, -10, -31, -151, 268], ![193, 32, 61, 130, -293]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [20, 46, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 53, 13], [41, 7, 48], [0, 1]]
 g := ![![[8, 42, 25], [42, 4], [9, 36, 9], [42, 56, 9], [1]], ![[44, 24, 30, 47], [54, 34], [49, 40, 37, 19], [8, 54, 33, 5], [22, 0, 34, 1]], ![[42, 45, 38, 45], [9, 57], [35, 17, 25, 60], [32, 29, 7, 49], [43, 36, 8, 60]]]
 h' := ![![[23, 53, 13], [23, 46, 56], [3, 38, 2], [14, 32, 3], [41, 15, 3], [0, 1]], ![[41, 7, 48], [32, 34, 14], [40, 11, 20], [13, 3, 10], [15, 17, 33], [23, 53, 13]], ![[0, 1], [18, 42, 52], [36, 12, 39], [45, 26, 48], [46, 29, 25], [41, 7, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 47], []]
 b := ![[], [12, 51, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [20, 46, 58, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1772299139, 579118458, -199210520, -545224821, -530880504]
  a := ![7, 23, 45, -23, -136]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![518065862, 523201176, 704023159, -545224821, -530880504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-415, 87, 155, -50, -36]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![-415, 87, 155, -50, -36]] 
 ![![61, 0, 0, 0, 0], ![37, 1, 0, 0, 0], ![34, 0, 1, 0, 0], ![54, 0, 0, 1, 0], ![30, 0, 0, 0, 1]] where
  M :=![![![-415, 87, 155, -50, -36], ![432, -246, 43, 238, -200], ![2400, 37, -1522, -314, 952], ![-5928, 1195, 2215, -689, -528], ![2892, -931, -635, 746, -263]]]
  hmulB := by decide  
  f := ![![![5960813, -3626753, -521667, -437794, 932660]], ![![3432101, -2088201, -300364, -252072, 537004]], ![![3666914, -2231069, -320914, -269318, 573744]], ![![5045118, -3069611, -441529, -370541, 789384]], ![![3166674, -1926705, -277135, -232578, 495473]]]
  g := ![![![-84, 87, 155, -50, -36], ![20, -246, 43, 238, -200], ![675, 37, -1522, -314, 952], ![-1187, 1195, 2215, -689, -528], ![435, -931, -635, 746, -263]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, -1, 10, 3, -7]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![-14, -1, 10, 3, -7]] 
 ![![61, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![47, 0, 0, 0, 1]] where
  M :=![![![-14, -1, 10, 3, -7], ![84, -14, -35, 6, 12], ![-144, 55, 22, -46, 24], ![-186, -19, 139, 43, -98], ![243, -23, -122, -1, 58]]]
  hmulB := by decide  
  f := ![![![-1580, -917, -144, 89, 209]], ![![-1388, -808, -127, 78, 184]], ![![-1132, -658, -104, 63, 149]], ![![-186, -113, -19, 9, 24]], ![![-1273, -742, -118, 70, 167]]]
  g := ![![![-1, -1, 10, 3, -7], ![27, -14, -35, 6, 12], ![-78, 55, 22, -46, 24], ![-9, -19, 139, 43, -98], ![61, -23, -122, -1, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-709, 432, 62, 50, -110]] ![![-415, 87, 155, -50, -36]]
  ![![15139, -3501, -5083, 2288, 678]] where
 M := ![![![15139, -3501, -5083, 2288, 678]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![15139, -3501, -5083, 2288, 678]] ![![-14, -1, 10, 3, -7]]
  ![![61, 0, 0, 0, 0]] where
 M := ![![![-34892, -304756, 397415, 355935, -454877]]]
 hmul := by decide  
 g := ![![![![-572, -4996, 6515, 5835, -7457]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)


lemma PB1705I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB1705I1 : PrimesBelowBoundCertificateInterval O 23 61 1705 where
  m := 9
  g := ![4, 3, 2, 2, 2, 3, 1, 2, 3]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB1705I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0, I31N1, I31N2]
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1, I47N2]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1, I61N2]
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
    · exact ![841, 29, 29, 29]
    · exact ![29791, 31, 31]
    · exact ![50653, 1369]
    · exact ![2825761, 41]
    · exact ![79507, 1849]
    · exact ![103823, 47, 47]
    · exact ![418195493]
    · exact ![205379, 3481]
    · exact ![226981, 61, 61]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
      exact NI29N3
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
      exact NI47N2
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
      exact NI61N2
  β := ![I29N0, I29N1, I29N2, I29N3, I31N1, I31N2, I37N1, I41N1, I47N1, I47N2, I61N1, I61N2]
  Il := ![[I29N0, I29N1, I29N2, I29N3], [I31N1, I31N2], [I37N1], [I41N1], [], [I47N1, I47N2], [], [], [I61N1, I61N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
