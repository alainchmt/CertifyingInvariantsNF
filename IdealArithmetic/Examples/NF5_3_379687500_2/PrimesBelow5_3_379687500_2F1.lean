
import IdealArithmetic.Examples.NF5_3_379687500_2.RI5_3_379687500_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1843, -1028, -115, 399, 2310]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![-1843, -1028, -115, 399, 2310]] 
 ![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![21, 11, 1, 0, 0], ![19, 17, 0, 1, 0], ![2, 5, 0, 0, 1]] where
  M :=![![![-1843, -1028, -115, 399, 2310], ![-3150, -1801, -198, 694, 4032], ![-5084, -2682, -313, 1056, 6068], ![-2266, -1785, -159, 633, 3832], ![-1886, -971, -115, 386, 2209]]]
  hmulB := by decide  
  f := ![![![165, -17, 8, -17, -134]], ![![-862, -833, -156, 368, 2212]], ![![-229, -278, -49, 115, 682]], ![![-183, -381, -59, 140, 806]], ![![-184, -176, -33, 78, 469]]]
  g := ![![![-401, -624, -115, 399, 2310], ![-698, -1089, -198, 694, 4032], ![-1059, -1639, -313, 1056, 6068], ![-642, -1033, -159, 633, 3832], ![-387, -597, -115, 386, 2209]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [17, 12, 1] where
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
 g := ![![[28, 9], [25], [20, 5], [17, 1]], ![[7, 20], [25], [18, 24], [5, 28]]]
 h' := ![![[17, 28], [16, 26], [8, 24], [1, 11], [0, 1]], ![[0, 1], [23, 3], [10, 5], [14, 18], [17, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [9, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [17, 12, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1253852, -1179768, -75129, 472993, 2818039]
  a := ![935, 890, 79, -369, -2189]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-493072, -775325, -75129, 472993, 2818039]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1447, 831, 91, -320, -1860]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![1447, 831, 91, -320, -1860]] 
 ![![29, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![23, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![1447, 831, 91, -320, -1860], ![2320, 1207, 142, -478, -2740], ![4540, 3036, 299, -1124, -6664], ![-26, -1500, -48, 421, 2900], ![1762, 1242, 118, -454, -2709]]]
  hmulB := by decide  
  f := ![![![715, 393, 11, -206, -1136]], ![![308, 187, 6, -94, -516]], ![![1213, 771, 40, -382, -2120]], ![![1859, 1101, 51, -561, -3116]], ![![536, 294, 6, -154, -845]]]
  g := ![![![1714, 831, 91, -320, -1860], ![2536, 1207, 142, -478, -2740], ![6103, 3036, 299, -1124, -6664], ![-2541, -1500, -48, 421, 2900], ![2476, 1242, 118, -454, -2709]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47425, 31656, 1731, -15391, -85314]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![47425, 31656, 1731, -15391, -85314]] 
 ![![29, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![47425, 31656, 1731, -15391, -85314], ![227678, 151975, 8310, -73890, -409580], ![1093060, 729618, 39895, -354740, -1966360], ![2077330, 1386621, 75819, -674175, -3737020], ![-165298, -110337, -6033, 53646, 297365]]]
  hmulB := by decide  
  f := ![![![165, 3, 30, -35, -190]], ![![90, 19, 12, -20, -120]], ![![-215, -243, -23, 89, 570]], ![![560, 777, 75, -273, -1704]], ![![-69, -138, -9, 43, 271]]]
  g := ![![![1548, 31656, 1731, -15391, -85314], ![7432, 151975, 8310, -73890, -409580], ![35681, 729618, 39895, -354740, -1966360], ![67811, 1386621, 75819, -674175, -3737020], ![-5396, -110337, -6033, 53646, 297365]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2

def I29N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -18, -1, 9, 50]] i)))

def SI29N3: IdealEqSpanCertificate' Table ![![-27, -18, -1, 9, 50]] 
 ![![29, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![27, 0, 0, 1, 0], ![17, 0, 0, 0, 1]] where
  M :=![![![-27, -18, -1, 9, 50], ![-130, -85, -4, 42, 232], ![-644, -438, -23, 212, 1172], ![-1290, -867, -51, 421, 2340], ![110, 75, 5, -36, -201]]]
  hmulB := by decide  
  f := ![![![113, 141, 10, -47, -298]], ![![93, 110, 8, -37, -234]], ![![165, 231, 15, -75, -478]], ![![-93, -192, -9, 58, 378]], ![![101, 138, 9, -45, -287]]]
  g := ![![![-21, -18, -1, 9, 50], ![-97, -85, -4, 42, 232], ![-479, -438, -23, 212, 1172], ![-957, -867, -51, 421, 2340], ![81, 75, 5, -36, -201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N3 : Nat.card (O ⧸ I29N3) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N3)

lemma isPrimeI29N3 : Ideal.IsPrime I29N3 := prime_ideal_of_norm_prime hp29.out _ NI29N3
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![-1843, -1028, -115, 399, 2310]] ![![1447, 831, 91, -320, -1860]]
  ![![-1514035, -850949, -94646, 329643, 1910370]] where
 M := ![![![-1514035, -850949, -94646, 329643, 1910370]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![-1514035, -850949, -94646, 329643, 1910370]] ![![47425, 31656, 1731, -15391, -85314]]
  ![![-2280127, -1279850, -142538, 495830, 2873160]] where
 M := ![![![-2280127, -1279850, -142538, 495830, 2873160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI29N2 : IdealMulLeCertificate' Table 
  ![![-2280127, -1279850, -142538, 495830, 2873160]] ![![-27, -18, -1, 9, 50]]
  ![![29, 0, 0, 0, 0]] where
 M := ![![![-3834699, -2136430, -243629, 817771, 4750954]]]
 hmul := by decide  
 g := ![![![![-132231, -73670, -8401, 28199, 163826]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 5 2 4 [2, 20, 20, 16, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 19, 21, 21, 12], [20, 30, 24, 8, 4], [9, 1, 0, 3, 21], [9, 11, 17, 30, 25], [0, 1]]
 g := ![![[25, 20, 13, 12, 19], [15, 25, 1], [4, 19, 1], []], ![[17, 28, 16, 28, 15, 6, 27, 11], [30, 13, 22, 17, 4, 30, 20, 3], [13, 26, 5, 0, 24, 25, 12, 27], [23, 25, 21, 26, 2, 0, 23, 23]], ![[18, 8, 28, 2, 25, 1, 7, 7], [26, 25, 17, 19, 21, 8, 12, 20], [7, 12, 27, 9, 22, 13, 12, 19], [28, 18, 20, 26, 29, 17, 19, 2]], ![[8, 6, 6, 23, 19, 9, 13, 12], [14, 28, 26, 6, 5, 6, 29, 26], [20, 4, 12, 18, 4, 20, 2, 11], [16, 12, 21, 19, 6, 27, 4, 23]], ![[2, 18, 26, 17, 12, 19, 14, 2], [11, 27, 8, 22, 28, 26, 30, 5], [16, 13, 16, 25, 25, 13, 6, 7], [25, 19, 4, 6, 11, 18, 4, 1]]]
 h' := ![![[12, 19, 21, 21, 12], [1, 24, 1, 3, 9], [23, 6, 3, 1], [0, 0, 0, 1], [0, 1]], ![[20, 30, 24, 8, 4], [19, 19, 24, 23, 9], [29, 3, 29, 30, 15], [8, 10, 17, 12, 14], [12, 19, 21, 21, 12]], ![[9, 1, 0, 3, 21], [14, 23, 5, 12, 5], [26, 9, 3, 24, 25], [8, 2, 0, 3, 11], [20, 30, 24, 8, 4]], ![[9, 11, 17, 30, 25], [12, 23, 13, 11, 25], [1, 13, 16, 18, 27], [15, 23, 14, 24, 8], [9, 1, 0, 3, 21]], ![[0, 1], [11, 4, 19, 13, 14], [18, 0, 11, 20, 26], [28, 27, 0, 22, 29], [9, 11, 17, 30, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 2, 8, 27], [], [], []]
 b := ![[], [2, 21, 26, 26, 21], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 5
  hpos := by decide
  P := [2, 20, 20, 16, 12, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31402233703834939, -44307469720171103, -2606592608875191, 14786894733908530, 93232417764422082]
  a := ![-1313, -1315, -111, 518, 3074]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1012975280768869, -1429273216779713, -84083632544361, 476996604319630, 3007497347239422]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 28629151 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀

instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 5 2 5 [31, 12, 21, 20, 17, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 18, 8, 9, 11], [16, 3, 4, 22, 16], [35, 34, 13, 34, 19], [35, 18, 12, 9, 28], [0, 1]]
 g := ![![[26, 35, 0, 19, 21], [23, 19, 1, 21], [17, 1, 10, 20, 1], [], []], ![[11, 13, 22, 31, 14, 8, 28, 12], [22, 6, 8, 21], [15, 12, 29, 0, 36, 5, 30, 27], [25, 16, 17, 30], [11, 25, 28, 10]], ![[4, 20, 18, 2, 0, 4, 24, 9], [35, 34, 27, 30], [35, 9, 6, 22, 8, 6, 31, 11], [33, 2, 5, 9], [13, 10, 15, 34]], ![[13, 12, 21, 17, 5, 8, 4, 6], [24, 12, 15, 7], [26, 24, 26, 25, 5, 30, 15, 20], [1, 33, 1, 4], [24, 20, 2, 28]], ![[9, 0, 26, 27, 29, 2, 14, 1], [7, 17, 30, 27], [4, 0, 0, 26, 33, 9, 2, 11], [29, 17, 8, 3], [19, 25, 15, 7]]]
 h' := ![![[8, 18, 8, 9, 11], [34, 35, 31, 23, 13], [28, 24, 24, 9, 24], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[16, 3, 4, 22, 16], [22, 6, 10, 15, 19], [1, 6, 8, 24, 13], [30, 28, 18, 35, 27], [19, 10, 15, 3, 20], [8, 18, 8, 9, 11]], ![[35, 34, 13, 34, 19], [22, 27, 11, 19, 10], [16, 18, 7, 31, 20], [14, 23, 17, 4, 22], [1, 0, 19, 23, 34], [16, 3, 4, 22, 16]], ![[35, 18, 12, 9, 28], [22, 0, 34, 22, 30], [10, 33, 14, 28, 9], [6, 1, 23, 7, 15], [0, 29, 2, 29, 35], [35, 34, 13, 34, 19]], ![[0, 1], [8, 6, 25, 32, 2], [22, 30, 21, 19, 8], [1, 22, 16, 28, 9], [7, 35, 0, 19, 22], [35, 18, 12, 9, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 12, 4, 20], [], [], []]
 b := ![[], [16, 8, 19, 17, 15], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 5
  hpos := by decide
  P := [31, 12, 21, 20, 17, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![242223296016, 225380180103, 12785243662, -91155485749, -535876054422]
  a := ![129, 120, 11, -51, -302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6546575568, 6091356219, 345547126, -2463661777, -14483136606]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 69343957 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-973, -1564, -93, 495, 3186]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-973, -1564, -93, 495, 3186]] 
 ![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![29, 33, 1, 0, 0], ![40, 7, 0, 1, 0], ![3, 13, 0, 0, 1]] where
  M :=![![![-973, -1564, -93, 495, 3186], ![5058, 8045, 476, -2562, -16452], ![-25116, -40554, -2405, 12832, 82608], ![78350, 124839, 7395, -39709, -255104], ![-13282, -21211, -1257, 6740, 43317]]]
  hmulB := by decide  
  f := ![![![-901, -367, -100, 231, 1478]], ![![2114, 3061, 502, -1212, -7088]], ![![1249, 2204, 345, -837, -4842]], ![![-1050, -282, -99, 225, 1484]], ![![711, 1047, 171, -413, -2413]]]
  g := ![![![-674, -1058, -93, 495, 3186], ![3490, 5467, 476, -2562, -16452], ![-17475, -27437, -2405, 12832, 82608], ![54087, 84759, 7395, -39709, -255104], ![-9180, -14391, -1257, 6740, 43317]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [29, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 40], [0, 1]]
 g := ![![[22, 32], [16], [10], [32, 37], [1]], ![[24, 9], [16], [10], [1, 4], [1]]]
 h' := ![![[18, 40], [30, 14], [17, 4], [15, 16], [12, 18], [0, 1]], ![[0, 1], [36, 27], [7, 37], [16, 25], [8, 23], [18, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [6, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [29, 23, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2893733, -2660120, -168520, 1076734, 6409708]
  a := ![-1401, -1316, -119, 552, 3280]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1470857, -2145422, -168520, 1076734, 6409708]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2993, -1680, -187, 651, 3772]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-2993, -1680, -187, 651, 3772]] 
 ![![41, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![21, 0, 0, 0, 1]] where
  M :=![![![-2993, -1680, -187, 651, 3772], ![-5054, -2839, -316, 1100, 6374], ![-8528, -4782, -533, 1854, 10742], ![-2938, -1659, -183, 641, 3718], ![-3182, -1785, -199, 692, 4009]]]
  hmulB := by decide  
  f := ![![![307, 225, 10, -105, -576]], ![![42, 29, 2, -14, -78]], ![![196, 126, 7, -62, -346]], ![![328, 213, 9, -105, -574]], ![![135, 102, 5, -47, -259]]]
  g := ![![![-2005, -1680, -187, 651, 3772], ![-3388, -2839, -316, 1100, 6374], ![-5710, -4782, -533, 1854, 10742], ![-1976, -1659, -183, 641, 3718], ![-2131, -1785, -199, 692, 4009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, -14, 0, 8, 44]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-31, -14, 0, 8, 44]] 
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![31, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![-31, -14, 0, 8, 44], ![-128, -95, -2, 44, 236], ![-872, -648, -49, 304, 1700], ![-1604, -936, -54, 481, 2696], ![152, 76, 6, -42, -241]]]
  hmulB := by decide  
  f := ![![![-6487, -3602, -404, 1400, 8100]], ![![-3754, -2091, -234, 812, 4700]], ![![-1696, -920, -105, 360, 2076]], ![![-5133, -2926, -322, 1129, 6556]], ![![-6011, -3326, -374, 1294, 7483]]]
  g := ![![![-39, -14, 0, 8, 44], ![-198, -95, -2, 44, 236], ![-1428, -648, -49, 304, 1700], ![-2323, -936, -54, 481, 2696], ![211, 76, 6, -42, -241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2

def I41N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, -85, -15, 36, 214]] i)))

def SI41N3: IdealEqSpanCertificate' Table ![![-77, -85, -15, 36, 214]] 
 ![![41, 0, 0, 0, 0], ![27, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![32, 0, 0, 0, 1]] where
  M :=![![![-77, -85, -15, 36, 214], ![-128, 83, 2, -8, -10], ![1080, 888, 175, -414, -2514], ![-546, -1566, -222, 547, 3090], ![30, 284, 36, -90, -493]]]
  hmulB := by decide  
  f := ![![![-429, -439, -31, 154, 946]], ![![-275, -262, -19, 94, 572]], ![![-261, -315, -20, 108, 672]], ![![-120, 110, 2, -13, -146]], ![![-394, -438, -30, 150, 931]]]
  g := ![![![-143, -85, -15, 36, 214], ![-43, 83, 2, -8, -10], ![1749, 888, 175, -414, -2514], ![-1852, -1566, -222, 547, 3090], ![274, 284, 36, -90, -493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N3 : Nat.card (O ⧸ I41N3) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N3)

lemma isPrimeI41N3 : Ideal.IsPrime I41N3 := prime_ideal_of_norm_prime hp41.out _ NI41N3
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-973, -1564, -93, 495, 3186]] ![![-2993, -1680, -187, 651, 3772]]
  ![![17587, 11347, 1145, -4238, -25014]] where
 M := ![![![17587, 11347, 1145, -4238, -25014]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![17587, 11347, 1145, -4238, -25014]] ![![-31, -14, 0, 8, 44]]
  ![![-429, -439, -31, 154, 946]] where
 M := ![![![-429, -439, -31, 154, 946]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI41N2 : IdealMulLeCertificate' Table 
  ![![-429, -439, -31, 154, 946]] ![![-77, -85, -15, 36, 214]]
  ![![41, 0, 0, 0, 0]] where
 M := ![![![41, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2, I41N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
    exact isPrimeI41N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1 ⊙ MulI41N2)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]] where
  M :=![![![43, 0, 0, 0, 0], ![0, 43, 0, 0, 0], ![0, 0, 43, 0, 0], ![0, 0, 0, 43, 0], ![0, 0, 0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 5 2 5 [30, 2, 27, 42, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 36, 11, 38, 33], [13, 13, 42, 13, 11], [15, 36, 31, 37, 19], [37, 0, 2, 41, 23], [0, 1]]
 g := ![![[1, 39, 42, 23, 23], [20, 13, 0, 10, 38], [30, 34, 31, 21], [1], []], ![[3, 15, 19, 30, 0, 17, 22, 39], [14, 42, 2, 27, 15, 21, 21, 30], [40, 25, 11, 10], [27, 39, 40, 14, 16, 8, 18, 32], [19, 1, 31, 14]], ![[26, 10, 38, 17, 29, 22, 29, 16], [12, 41, 33, 33, 32, 37, 36, 10], [3, 32, 20, 4], [35, 24, 3, 17, 10, 41, 26, 11], [12, 5, 6, 35]], ![[22, 31, 20, 6, 8, 22], [15, 9, 14, 30, 11, 38, 2, 7], [10, 38, 17, 4], [37, 39, 41, 36, 1, 32, 1, 12], [10, 15, 23, 17]], ![[6, 37, 28, 35, 14, 30, 39, 41], [30, 30, 17, 26, 3, 26, 7, 14], [8, 32, 31, 13], [5, 28, 19, 30, 0, 20, 21, 25], [4, 0, 19, 13]]]
 h' := ![![[13, 36, 11, 38, 33], [2, 0, 36, 38, 18], [0, 29, 31, 16, 34], [13, 41, 16, 1, 35], [0, 0, 1], [0, 1]], ![[13, 13, 42, 13, 11], [27, 11, 29, 40, 40], [27, 15, 22, 6, 13], [18, 39, 24, 7, 28], [29, 8, 8, 0, 33], [13, 36, 11, 38, 33]], ![[15, 36, 31, 37, 19], [9, 8, 34, 14, 8], [11, 15, 25, 39, 30], [31, 29, 37, 13, 2], [24, 35, 16, 30, 1], [13, 13, 42, 13, 11]], ![[37, 0, 2, 41, 23], [32, 41, 27, 24], [32, 5, 38, 37, 18], [17, 33, 36, 20, 41], [11, 8, 32, 26, 35], [15, 36, 31, 37, 19]], ![[0, 1], [23, 26, 3, 13, 20], [22, 22, 13, 31, 34], [41, 30, 16, 2, 23], [2, 35, 29, 30, 17], [37, 0, 2, 41, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 37, 21, 20], [], [], []]
 b := ![[], [18, 27, 10, 30, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 5
  hpos := by decide
  P := [30, 2, 27, 42, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![83827352941066120, 100296671188600857, 5819444072620843, -35931928625132644, -220548306646147874]
  a := ![1656, 1578, 142, -652, -3877]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1949473324210840, 2332480725316299, 135335908665601, -835626247096108, -5129030387119718]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 147008443 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-241, 21, -13, 26, 204]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-241, 21, -13, 26, 204]] 
 ![![47, 0, 0, 0, 0], ![0, 47, 0, 0, 0], ![0, 0, 47, 0, 0], ![0, 0, 0, 47, 0], ![29, 16, 8, 31, 1]] where
  M :=![![![-241, 21, -13, 26, 204], ![1292, 1259, 230, -554, -3320], ![1220, -1920, -161, 416, 1948], ![-8698, -4854, -1158, 2645, 16552], ![1946, 1320, 284, -662, -4077]]]
  hmulB := by decide  
  f := ![![![-367, -207, -23, 80, 464]], ![![-608, -335, -38, 130, 752]], ![![-1044, -612, -67, 232, 1356]], ![![-214, -24, -12, 15, 64]], ![![-761, -367, -47, 145, 827]]]
  g := ![![![-131, -69, -35, -134, 204], ![2076, 1157, 570, 2178, -3320], ![-1176, -704, -335, -1276, 1948], ![-10398, -5738, -2842, -10861, 16552], ![2557, 1416, 700, 2675, -4077]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 4 2 5 [44, 16, 2, 29, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 2, 41, 18], [2, 37, 7, 24], [8, 7, 46, 5], [0, 1]]
 g := ![![[34, 39, 2, 24], [19, 32, 45, 8], [10, 44, 12, 2], [18, 1], []], ![[11, 9, 7, 19, 44, 8], [28, 11, 11, 29, 46, 4], [3, 33, 39, 38, 24, 2], [22, 39, 27, 39, 1, 6], [15, 23, 42]], ![[18, 32, 30, 10, 2, 12], [31, 27, 46, 18, 39, 28], [33, 40, 40, 10, 19, 7], [20, 15, 40, 26, 7, 6], [34, 35, 12]], ![[43, 11, 3, 22, 5, 23], [33, 9, 19, 16, 36, 10], [31, 40, 13, 6, 11, 5], [3, 43, 7, 9, 37, 19], [45, 17, 25]]]
 h' := ![![[8, 2, 41, 18], [10, 34, 46, 27], [30, 21, 22, 33], [7, 44, 42, 40], [0, 0, 1], [0, 1]], ![[2, 37, 7, 24], [40, 16, 38, 15], [26, 4, 15, 18], [33, 37, 14, 31], [15, 2, 12, 4], [8, 2, 41, 18]], ![[8, 7, 46, 5], [27, 28, 5, 27], [22, 36, 12, 3], [19, 15, 27, 22], [12, 38, 6, 24], [2, 37, 7, 24]], ![[0, 1], [5, 16, 5, 25], [0, 33, 45, 40], [37, 45, 11, 1], [11, 7, 28, 19], [8, 7, 46, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 31, 12], []]
 b := ![[], [], [5, 3, 1, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 4
  hpos := by decide
  P := [44, 16, 2, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-28732277236, -45963229608, -2745026904, 14608617808, 93884945952]
  a := ![-170, -162, -16, 62, 398]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-58540334252, -32938773720, -16038821160, -61613291632, 93884945952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 4879681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-367, -207, -23, 80, 464]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-367, -207, -23, 80, 464]] 
 ![![47, 0, 0, 0, 0], ![43, 1, 0, 0, 0], ![31, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![-367, -207, -23, 80, 464], ![-608, -335, -38, 130, 752], ![-1044, -612, -67, 232, 1356], ![-214, -24, -12, 15, 64], ![-410, -246, -26, 94, 549]]]
  hmulB := by decide  
  f := ![![![-241, 21, -13, 26, 204]], ![![-193, 46, -7, 12, 116]], ![![-133, -27, -12, 26, 176]], ![![-303, -93, -31, 69, 452]], ![![-15, 33, 3, -8, -39]]]
  g := ![![![49, -207, -23, 80, 464], ![79, -335, -38, 130, 752], ![151, -612, -67, 232, 1356], ![3, -24, -12, 15, 64], ![59, -246, -26, 94, 549]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-241, 21, -13, 26, 204]] ![![-367, -207, -23, 80, 464]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 79, 6, -37, -214]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![113, 79, 6, -37, -214]] 
 ![![53, 0, 0, 0, 0], ![0, 53, 0, 0, 0], ![0, 0, 53, 0, 0], ![0, 0, 0, 53, 0], ![23, 40, 50, 45, 1]] where
  M :=![![![113, 79, 6, -37, -214], ![298, 115, -2, -76, -388], ![2056, 1746, 89, -752, -4252], ![3364, 1539, 135, -965, -5080], ![-256, -65, -15, 66, 323]]]
  hmulB := by decide  
  f := ![![![-271, -152, -17, 59, 342]], ![![-454, -253, -28, 98, 568]], ![![-756, -426, -47, 164, 948]], ![![-290, -177, -21, 69, 404]], ![![-1425, -812, -91, 314, 1821]]]
  g := ![![![95, 163, 202, 181, -214], ![174, 295, 366, 328, -388], ![1884, 3242, 4013, 3596, -4252], ![2268, 3863, 4795, 4295, -5080], ![-145, -245, -305, -273, 323]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 4 2 5 [33, 39, 45, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 16, 0, 43], [33, 44, 45, 46], [21, 45, 8, 17], [0, 1]]
 g := ![![[10, 1, 17, 49], [12, 36, 52], [5, 25, 11, 28], [23, 42, 1], []], ![[28, 0, 7, 14, 49, 42], [41, 4, 52], [42, 39, 24, 30, 37, 10], [45, 50, 47], [24, 51, 35, 32, 29, 7]], ![[2, 43, 26, 13, 33, 46], [6, 38, 10], [42, 20, 18, 16, 6, 24], [25, 42, 9], [1, 33, 13, 48, 0, 28]], ![[42, 8, 31, 25, 10, 44], [25, 34, 36], [44, 46, 17, 10, 12, 38], [23, 12, 36], [32, 22, 43, 12, 10, 37]]]
 h' := ![![[41, 16, 0, 43], [11, 14, 17, 7], [47, 11, 4, 23], [36, 49, 50, 44], [0, 0, 0, 1], [0, 1]], ![[33, 44, 45, 46], [15, 41, 35, 21], [19, 2, 1, 23], [45, 40, 35, 30], [24, 0, 22, 43], [41, 16, 0, 43]], ![[21, 45, 8, 17], [29, 8, 5, 52], [11, 15, 22, 13], [22, 45, 44, 25], [23, 50, 50, 3], [33, 44, 45, 46]], ![[0, 1], [38, 43, 49, 26], [11, 25, 26, 47], [30, 25, 30, 7], [43, 3, 34, 6], [21, 45, 8, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [24, 24, 50], []]
 b := ![[], [], [21, 7, 23, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 4
  hpos := by decide
  P := [33, 39, 45, 11, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-237364971216383, -236107755865924, -13462472924948, 92257252574460, 549136175831660]
  a := ![-2743, -2614, -230, 1086, 6422]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-242782962553671, -418897260172308, -518307004990716, -464506993582080, 549136175831660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 7890481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 152, 17, -59, -342]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![271, 152, 17, -59, -342]] 
 ![![53, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![47, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![271, 152, 17, -59, -342], ![454, 253, 28, -98, -568], ![756, 426, 47, -164, -948], ![290, 177, 21, -69, -404], ![282, 155, 17, -60, -347]]]
  hmulB := by decide  
  f := ![![![-113, -79, -6, 37, 214]], ![![-44, -29, -2, 14, 80]], ![![-139, -103, -7, 47, 270]], ![![-72, -35, -3, 21, 112]], ![![-57, -42, -3, 19, 111]]]
  g := ![![![130, 152, 17, -59, -342], ![216, 253, 28, -98, -568], ![359, 426, 47, -164, -948], ![153, 177, 21, -69, -404], ![132, 155, 17, -60, -347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![113, 79, 6, -37, -214]] ![![271, 152, 17, -59, -342]]
  ![![53, 0, 0, 0, 0]] where
 M := ![![![-53, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129, -51, -9, 26, 160]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-129, -51, -9, 26, 160]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![0, 0, 59, 0, 0], ![13, 3, 56, 1, 0], ![24, 18, 48, 0, 1]] where
  M :=![![![-129, -51, -9, 26, 160], ![60, 139, 30, -62, -372], ![124, -312, -17, 60, 248], ![-1690, -1170, -234, 569, 3508], ![258, 228, 48, -110, -677]]]
  hmulB := by decide  
  f := ![![![245, 165, 9, -80, -444]], ![![1168, 773, 42, -378, -2092]], ![![5684, 3828, 209, -1852, -10280]], ![![5689, 3828, 209, -1853, -10284]], ![![5066, 3408, 186, -1650, -9157]]]
  g := ![![![-73, -51, -155, 26, 160], ![166, 119, 362, -62, -372], ![-112, -84, -259, 60, 248], ![-1581, -1119, -3398, 569, 3508], ![304, 216, 656, -110, -677]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [6, 35, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 14, 17], [20, 44, 42], [0, 1]]
 g := ![![[17, 43, 7], [18, 0, 27], [58, 57], [4, 4, 57], [1]], ![[46, 29, 53, 12], [27, 0, 34, 3], [19, 20], [44, 26, 41, 28], [46, 44, 29, 16]], ![[30, 49, 21, 2], [2, 36, 58, 42], [56, 46], [39, 42, 13, 32], [18, 11, 48, 43]]]
 h' := ![![[16, 14, 17], [10, 24, 19], [51, 55, 33], [35, 49, 23], [53, 24, 36], [0, 1]], ![[20, 44, 42], [44, 3, 5], [25, 55, 27], [32, 50, 16], [44, 28, 45], [16, 14, 17]], ![[0, 1], [3, 32, 35], [35, 8, 58], [28, 19, 20], [45, 7, 37], [20, 44, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 55], []]
 b := ![[], [53, 38, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [6, 35, 23, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6215959, -8645352, -504311, 2896408, 18253386]
  a := ![-129, -126, -11, 50, 302]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8168653, -5862636, -17607893, 2896408, 18253386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![245, 165, 9, -80, -444]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![245, 165, 9, -80, -444]] 
 ![![59, 0, 0, 0, 0], ![0, 59, 0, 0, 0], ![28, 7, 1, 0, 0], ![6, 45, 0, 1, 0], ![19, 10, 0, 0, 1]] where
  M :=![![![245, 165, 9, -80, -444], ![1168, 773, 42, -378, -2092], ![5684, 3828, 209, -1852, -10280], ![10658, 7020, 384, -3441, -19028], ![-842, -546, -30, 270, 1489]]]
  hmulB := by decide  
  f := ![![![-129, -51, -9, 26, 160]], ![![60, 139, 30, -62, -372]], ![![-52, -13, -1, 6, 36]], ![![4, 81, 18, -35, -208]], ![![-27, 11, 3, -4, -23]]]
  g := ![![![151, 138, 9, -80, -444], ![712, 651, 42, -378, -2092], ![3496, 3195, 209, -1852, -10280], ![6476, 5923, 384, -3441, -19028], ![-507, -464, -30, 270, 1489]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P1 : CertificateIrreducibleZModOfList' 59 2 2 5 [45, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 58], [0, 1]]
 g := ![![[6, 21], [44, 36], [51], [43, 41], [25, 1]], ![[0, 38], [0, 23], [51], [6, 18], [50, 58]]]
 h' := ![![[25, 58], [26, 32], [32, 53], [12, 13], [55, 49], [0, 1]], ![[0, 1], [0, 27], [0, 6], [42, 46], [41, 10], [25, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [10, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N1 : CertifiedPrimeIdeal' SI59N1 59 where
  n := 2
  hpos := by decide
  P := [45, 34, 1]
  hirr := P59P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4464675, -4335483, -272337, 1709819, 10240041]
  a := ![-1738, -1656, -145, 684, 4069]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3417948, -3080871, -272337, 1709819, 10240041]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N1 B_one_repr
lemma NI59N1 : Nat.card (O ⧸ I59N1) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-129, -51, -9, 26, 160]] ![![245, 165, 9, -80, -444]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 5 2 5 [51, 49, 47, 5, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 4, 55, 45, 32], [54, 46, 12, 36, 31], [21, 36, 5, 28, 38], [21, 35, 50, 13, 21], [0, 1]]
 g := ![![[8, 58, 26, 15, 5], [28, 30, 37, 60], [57, 5, 19, 41, 42], [44, 54, 1], []], ![[2, 46, 49, 56, 57, 39, 46, 30], [17, 48, 58, 46], [52, 35, 45, 32, 53, 33, 54, 26], [44, 20, 39, 5, 21, 59, 26, 30], [24, 8, 12, 22, 49, 3, 59, 11]], ![[12, 49, 44, 3, 44, 57, 26, 55], [24, 59, 24, 47], [21, 28, 36, 53, 56, 26, 54, 29], [27, 17, 60, 33, 32, 23, 7, 54], [20, 45, 48, 9, 53, 31, 49, 23]], ![[45, 25, 45, 6, 43, 50, 57, 44], [9, 32, 10, 22], [22, 38, 41, 21, 56, 43, 18, 28], [40, 24, 34, 47, 53, 10, 47, 10], [49, 18, 3, 13, 60, 52, 41, 33]], ![[9, 29, 29, 21, 48, 43, 32, 53], [20, 24, 30, 25], [30, 30, 9, 35, 23, 12, 56, 18], [26, 15, 27, 38, 4, 34, 26, 53], [31, 44, 56, 13, 31, 23, 13, 50]]]
 h' := ![![[19, 4, 55, 45, 32], [50, 10, 17, 53, 35], [21, 49, 24, 43, 50], [13, 31, 54, 60, 46], [0, 0, 0, 1], [0, 1]], ![[54, 46, 12, 36, 31], [26, 33, 53, 60, 52], [51, 60, 0, 14, 31], [60, 37, 46, 46, 27], [23, 3, 29, 59, 9], [19, 4, 55, 45, 32]], ![[21, 36, 5, 28, 38], [54, 7, 55, 42, 7], [34, 15, 45, 31, 48], [50, 52, 28, 52, 34], [40, 10, 47, 59, 13], [54, 46, 12, 36, 31]], ![[21, 35, 50, 13, 21], [34, 40, 18, 40, 21], [35, 45, 21, 44, 49], [27, 5, 21, 36, 52], [52, 23, 13, 47, 46], [21, 36, 5, 28, 38]], ![[0, 1], [29, 32, 40, 49, 7], [45, 14, 32, 51, 5], [40, 58, 34, 50, 24], [55, 25, 33, 17, 54], [21, 35, 50, 13, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 54, 29, 39], [], [], []]
 b := ![[], [57, 3, 6, 50, 35], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 5
  hpos := by decide
  P := [51, 49, 47, 5, 7, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8992996196875778, -10524027292716598, -609481458245927, 3808300448271578, 23289180314636916]
  a := ![-1061, -1010, -91, 418, 2484]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-147426167161898, -172525037585518, -9991499315507, 62431154889698, 381789841223556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 844596301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀



lemma PB953I1_primes (p : ℕ) :
  p ∈ Set.range ![29, 31, 37, 41, 43, 47, 53, 59, 61] ↔ Nat.Prime p ∧ 23 < p ∧ p ≤ 61 := by
  rw [← List.mem_ofFn']
  convert primes_range 23 61 (by omega)

def PB953I1 : PrimesBelowBoundCertificateInterval O 23 61 953 where
  m := 9
  g := ![4, 1, 1, 4, 1, 2, 2, 2, 1]
  P := ![29, 31, 37, 41, 43, 47, 53, 59, 61]
  hP := PB953I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I29N0, I29N1, I29N2, I29N3]
    · exact ![I31N0]
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2, I41N3]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0]
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
    · exact ![28629151]
    · exact ![69343957]
    · exact ![1681, 41, 41, 41]
    · exact ![147008443]
    · exact ![4879681, 47]
    · exact ![7890481, 53]
    · exact ![205379, 3481]
    · exact ![844596301]
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
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
      exact NI41N3
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
  β := ![I29N0, I29N1, I29N2, I29N3, I41N1, I41N2, I41N3, I47N1, I53N1]
  Il := ![[I29N0, I29N1, I29N2, I29N3], [], [], [I41N1, I41N2, I41N3], [], [I47N1], [I53N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
