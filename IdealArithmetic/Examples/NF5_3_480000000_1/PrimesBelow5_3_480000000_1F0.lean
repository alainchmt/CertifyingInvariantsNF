
import IdealArithmetic.Examples.NF5_3_480000000_1.RI5_3_480000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0, 2, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 1, 0, 2, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 1, 0, 2, -1], ![-8, -5, -2, -9, 5], ![20, 12, 4, 20, -11], ![-40, -23, -7, -40, 22], ![56, 33, 11, 57, -31]]]
  hmulB := by decide  
  f := ![![![-5, 3, -3, -1, 1]], ![![4, -1, 4, 1, -1]], ![![-4, 1, -2, 0, 1]], ![![2, 0, -1, 1, 1]], ![![2, 2, -1, 2, 2]]]
  g := ![![![1, 1, 0, 2, -1], ![-4, -5, -2, -9, 5], ![10, 12, 4, 20, -11], ![-20, -23, -7, -40, 22], ![28, 33, 11, 57, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-121, -72, 10, 15, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-121, -72, 10, 15, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-121, -72, 10, 15, 0], ![0, -126, -174, 5, 45], ![180, 23, -131, -19, 30], ![120, 172, 129, -19, -36], ![64, 60, 25, -9, -8]]]
  hmulB := by decide  
  f := ![![![166, -52, 104, 29, -33]], ![![-132, 38, -81, -26, 27]], ![![191, -52, 116, 41, -42]], ![![47, -36, 40, -11, -3]], ![![135, -19, 74, 47, -41]]]
  g := ![![![-73, -72, 10, 15, 0], ![62, -126, -174, 5, 45], ![150, 23, -131, -19, 30], ![23, 172, 129, -19, -36], ![28, 60, 25, -9, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0, 2, -1]] ![![-121, -72, 10, 15, 0]]
  ![![-66, 14, 79, 6, -19]] where
 M := ![![![-66, 14, 79, 6, -19]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-66, 14, 79, 6, -19]] ![![-121, -72, 10, 15, 0]]
  ![![21710, 4697, -13146, -2364, 2936]] where
 M := ![![![21710, 4697, -13146, -2364, 2936]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![21710, 4697, -13146, -2364, 2936]] ![![-121, -72, 10, 15, 0]]
  ![![-5088966, -2687748, 890392, 617401, -121399]] where
 M := ![![![-5088966, -2687748, 890392, 617401, -121399]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-5088966, -2687748, 890392, 617401, -121399]] ![![-121, -72, 10, 15, 0]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![842354030, 824449848, 376746894, -117328706, -115492144]]]
 hmul := by decide  
 g := ![![![![421177015, 412224924, 188373447, -58664353, -57746072]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![147, 91, 26, 154, -84]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![147, 91, 26, 154, -84]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![147, 91, 26, 154, -84], ![-672, -401, -126, -690, 378], ![1512, 891, 289, 1542, -846], ![-3048, -1785, -588, -3098, 1701], ![4304, 2521, 830, 4375, -2402]]]
  hmulB := by decide  
  f := ![![![1, -31, -44, 2, 12]], ![![32, 5, -22, -2, 6]], ![![24, 21, 7, 0, 0]], ![![-16, 13, 32, 8, -3]], ![![14, -3, -18, 15, 16]]]
  g := ![![![105, 91, 26, 154, -84], ![-476, -401, -126, -690, 378], ![1068, 891, 289, 1542, -846], ![-2150, -1785, -588, -3098, 1701], ![3036, 2521, 830, 4375, -2402]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 2, 1, -1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 1, 2, 1, -1]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 1, 2, 1, -1], ![-8, -1, 0, -4, 2], ![8, 3, 3, 9, -5], ![-16, -11, -6, -17, 10], ![24, 13, 4, 24, -13]]]
  hmulB := by decide  
  f := ![![![-15, -11, 0, -11, -9]], ![![-29, -20, 0, -21, -17]], ![![-61, -42, 1, -44, -36]], ![![-130, -89, 2, -93, -76]], ![![-282, -193, 4, -202, -165]]]
  g := ![![![0, 1, 2, 1, -1], ![-1, -1, 0, -4, 2], ![-2, 3, 3, 9, -5], ![5, -11, -6, -17, 10], ![-5, 13, 4, 24, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 2, 0, 2, 2]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 2, 0, 2, 2]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 2, 0, 2, 2], ![16, 11, 0, 12, 8], ![32, 22, -1, 22, 22], ![80, 54, 0, 59, 40], ![160, 110, -4, 112, 103]]]
  hmulB := by decide  
  f := ![![![1, -14, -8, 2, 2]], ![![6, -9, -16, 0, 4]], ![![11, 0, -1, 0, 0]], ![![-5, 0, 8, 1, -2]], ![![0, 2, 4, 0, -1]]]
  g := ![![![-1, 2, 0, 2, 2], ![-6, 11, 0, 12, 8], ![-11, 22, -1, 22, 22], ![-29, 54, 0, 59, 40], ![-56, 110, -4, 112, 103]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2

def I3N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![491, -208, 337, 43, -100]] i)))

def SI3N3: IdealEqSpanCertificate' Table ![![491, -208, 337, 43, -100]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![491, -208, 337, 43, -100], ![-800, 285, -502, -69, 29], ![116, -544, 354, -366, -89], ![44, 53, 73, 260, -608], ![-1796, -1311, -45, -1637, -195]]]
  hmulB := by decide  
  f := ![![![29905, -35, -27091, -2997, 6368]], ![![36918, 12527, -16086, -4201, 3371]], ![![6471, 8382, 5723, -983, -1619]], ![![-13489, -10021, -1640, 1752, 713]], ![![1719, -2191, -4580, -85, 1148]]]
  g := ![![![209, -208, 337, 43, -100], ![-276, 285, -502, -69, 29], ![435, -544, 354, -366, -89], ![71, 53, 73, 260, -608], ![901, -1311, -45, -1637, -195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N3 : Nat.card (O ⧸ I3N3) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N3)

lemma isPrimeI3N3 : Ideal.IsPrime I3N3 := prime_ideal_of_norm_prime hp3.out _ NI3N3
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![147, 91, 26, 154, -84]] ![![3, 1, 2, 1, -1]]
  ![![-4559, -2652, -888, -4617, 2537]] where
 M := ![![![-4559, -2652, -888, -4617, 2537]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-4559, -2652, -888, -4617, 2537]] ![![3, 1, 2, 1, -1]]
  ![![135195, 79197, 26068, 137434, -75456]] where
 M := ![![![135195, 79197, 26068, 137434, -75456]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![135195, 79197, 26068, 137434, -75456]] ![![3, 2, 0, 2, 2]]
  ![![1428673, 836329, 275756, 1451784, -797146]] where
 M := ![![![1428673, 836329, 275756, 1451784, -797146]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![1428673, 836329, 275756, 1451784, -797146]] ![![491, -208, 337, 43, -100]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![1559955651, 913181475, 301095069, 1585191384, -870397245]]]
 hmul := by decide  
 g := ![![![![519985217, 304393825, 100365023, 528397128, -290132415]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N1, I3N2, I3N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N2
    exact isPrimeI3N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, -45, 88, 23, -27]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![139, -45, 88, 23, -27]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![139, -45, 88, 23, -27], ![-216, 69, -136, -36, 42], ![168, -53, 105, 29, -33], ![-24, 5, -14, -7, 6], ![48, -11, 28, 12, -11]]]
  hmulB := by decide  
  f := ![![![-1, 1, 2, 5, 3]], ![![4, 3, 0, 8, 6]], ![![14, 9, -1, 11, 9]], ![![28, 21, 2, 23, 18]], ![![62, 43, 0, 46, 37]]]
  g := ![![![21, -45, 88, 23, -27], ![-32, 69, -136, -36, 42], ![24, -53, 105, 29, -33], ![0, 5, -14, -7, 6], ![2, -11, 28, 12, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![139, -45, 88, 23, -27]] ![![139, -45, 88, 23, -27]]
  ![![41977, -13612, 26514, 6884, -8112]] where
 M := ![![![41977, -13612, 26514, 6884, -8112]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![41977, -13612, 26514, 6884, -8112]] ![![139, -45, 88, 23, -27]]
  ![![12674755, -4109783, 8005666, 2078877, -2449509]] where
 M := ![![![12674755, -4109783, 8005666, 2078877, -2449509]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![12674755, -4109783, 8005666, 2078877, -2449509]] ![![139, -45, 88, 23, -27]]
  ![![3826986481, -1240900316, 2417213328, 627689620, -739598388]] where
 M := ![![![3826986481, -1240900316, 2417213328, 627689620, -739598388]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![3826986481, -1240900316, 2417213328, 627689620, -739598388]] ![![139, -45, 88, 23, -27]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![1155512154715, -374674789465, 729848243200, 189523278955, -223312768095]]]
 hmul := by decide  
 g := ![![![![231102430943, -74934957893, 145969648640, 37904655791, -44662553619]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3265, 7959, 13943, 10, -3537]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-3265, 7959, 13943, 10, -3537]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![6, 2, 4, 1, 0], ![0, 3, 3, 0, 1]] where
  M :=![![![-3265, 7959, 13943, 10, -3537], ![-28296, -7017, 15898, 3117, -3507], ![-14028, -16525, -10134, 2065, 2922], ![25836, -2300, -26539, -2498, 6312], ![6660, -3004, -10171, -549, 2489]]]
  hmulB := by decide  
  f := ![![![-37783, 12286, -23887, -6178, 7329]], ![![58632, -18847, 36928, 9707, -11205]], ![![-44820, 14914, -28554, -7143, 8958]], ![![-40314, 13483, -25727, -6387, 8109]], ![![4512, -966, 2531, 1012, -487]]]
  g := ![![![-475, 2650, 3502, 10, -3537], ![-6714, -390, 1993, 3117, -3507], ![-3774, -4203, -3880, 2065, 2922], ![5832, -2320, -5069, -2498, 6312], ![1422, -1339, -2206, -549, 2489]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [4, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 0, 1], [5, 6, 6], [0, 1]]
 g := ![![[2, 0, 2], [1]], ![[4, 1, 0, 4], [5, 5, 4, 1]], ![[5, 5, 6, 6], [1, 6, 0, 6]]]
 h' := ![![[6, 0, 1], [3, 6, 4], [0, 1]], ![[5, 6, 6], [0, 3, 2], [6, 0, 1]], ![[0, 1], [2, 5, 1], [5, 6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 6], []]
 b := ![[], [6, 4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [4, 1, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-656132, -466902, 49931, -410906, -606689]
  a := ![0, 1, 1, 0, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![258472, 310711, 501946, -410906, -606689]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37783, 12286, -23887, -6178, 7329]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-37783, 12286, -23887, -6178, 7329]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 3, 1, 0, 0], ![6, 1, 0, 1, 0], ![2, 2, 0, 0, 1]] where
  M :=![![![-37783, 12286, -23887, -6178, 7329], ![58632, -18847, 36928, 9707, -11205], ![-44820, 14914, -28554, -7143, 8958], ![6516, -1297, 3593, 1517, -633], ![-9852, 5037, -7405, -608, 3332]]]
  hmulB := by decide  
  f := ![![![-3265, 7959, 13943, 10, -3537]], ![![-28296, -7017, 15898, 3117, -3507]], ![![-16463, 317, 15325, 1638, -3612]], ![![-3150, 5491, 10431, 97, -2631]], ![![-8066, -160, 7073, 815, -1657]]]
  g := ![![![14866, 10781, -23887, -6178, 7329], ![-23120, -16704, 36928, 9707, -11205], ![17556, 12829, -28554, -7143, 8958], ![-2755, -1761, 3593, 1517, -633], ![3451, 3028, -7405, -608, 3332]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 4, 1] where
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
 g := ![![[3, 2], [3, 1]], ![[2, 5], [6, 6]]]
 h' := ![![[3, 6], [3, 3], [0, 1]], ![[0, 1], [5, 4], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [4, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [6, 4, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135691, 100026, -17532, 73244, 165332]
  a := ![3, -2, 0, -3, -61]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-78111, -35898, -17532, 73244, 165332]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-3265, 7959, 13943, 10, -3537]] ![![-37783, 12286, -23887, -6178, 7329]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![7, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, -3, -2, 3]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-5, 1, -3, -2, 3]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![2, 8, 9, 1, 0], ![7, 2, 5, 0, 1]] where
  M :=![![![-5, 1, -3, -2, 3], ![24, 9, 6, 17, -3], ![-12, -1, -8, -13, 24], ![84, 52, 9, 74, -6], ![12, 16, -15, -11, 85]]]
  hmulB := by decide  
  f := ![![![-31, -26, -9, 4, 3]], ![![24, -29, -60, -1, 15]], ![![60, 20, -28, -7, 6]], ![![62, -5, -63, -6, 15]], ![![13, -11, -28, -1, 7]]]
  g := ![![![-2, 1, 0, -2, 3], ![1, -11, -12, 17, -3], ![-14, 5, -1, -13, 24], ![-2, -48, -57, 74, -6], ![-51, -6, -31, -11, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 7, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 5, 7], [3, 5, 4], [0, 1]]
 g := ![![[1, 0, 9], [7, 6, 1], []], ![[3, 8, 1, 2], [9, 3, 7, 10], [1, 5]], ![[7, 8, 0, 4], [7, 3, 8, 1], [4, 5]]]
 h' := ![![[3, 5, 7], [10, 2, 3], [0, 0, 1], [0, 1]], ![[3, 5, 4], [8, 3, 7], [1, 5, 5], [3, 5, 7]], ![[0, 1], [2, 6, 1], [10, 6, 5], [3, 5, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8], []]
 b := ![[], [1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 7, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-601731, -417676, 23558, -409269, -433545]
  a := ![1, 0, 1, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![295602, 338506, 534064, -409269, -433545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![325, 168, -62, -38, 10]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![325, 168, -62, -38, 10]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![325, 168, -62, -38, 10], ![80, 351, 412, -16, -104], ![-416, -6, 367, 56, -76], ![-344, -418, -268, 81, 98], ![-104, -94, -40, 82, 61]]]
  hmulB := by decide  
  f := ![![![-14833, -8428, -2986, -14834, 8174]], ![![-2146, -1153, -464, -2084, 1156]], ![![-18604, -10770, -3649, -18792, 10332]], ![![17027, 10126, 3210, 17451, -9564]], ![![-42772, -24938, -8304, -43370, 23825]]]
  g := ![![![-19, 168, -62, -38, 10], ![-286, 351, 412, -16, -104], ![-176, -6, 367, 56, -76], ![207, -418, -268, 81, 98], ![-18, -94, -40, 82, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139, -110, -13, -168, 89]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-139, -110, -13, -168, 89]] 
 ![![11, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![10, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![-139, -110, -13, -168, 89], ![712, 461, 116, 765, -415], ![-1660, -1006, -304, -1719, 940], ![3404, 1997, 655, 3463, -1901], ![-4804, -2821, -923, -4890, 2684]]]
  hmulB := by decide  
  f := ![![![79, 83, 37, 90, 61]], ![![109, 98, 29, 111, 80]], ![![185, 146, 23, 159, 121]], ![![334, 252, 27, 262, 204]], ![![636, 454, 17, 477, 381]]]
  g := ![![![176, -110, -13, -168, 89], ![-801, 461, 116, 765, -415], ![1800, -1006, -304, -1719, 940], ![-3626, 1997, 655, 3463, -1901], ![5120, -2821, -923, -4890, 2684]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-5, 1, -3, -2, 3]] ![![325, 168, -62, -38, 10]]
  ![![79, 83, 37, 90, 61]] where
 M := ![![![79, 83, 37, 90, 61]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![79, 83, 37, 90, 61]] ![![-139, -110, -13, -168, 89]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, 53, -107, -30, 31]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-173, 53, -107, -30, 31]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![6, 0, 6, 1, 0], ![4, 8, 12, 0, 1]] where
  M :=![![![-173, 53, -107, -30, 31], ![248, -95, 166, 33, -59], ![-236, 43, -128, -57, 20], ![-44, -56, 17, -46, -46], ![-212, -92, -31, -123, -83]]]
  hmulB := by decide  
  f := ![![![-17, -10, 1, 0, 1]], ![![8, -11, -20, 9, 1]], ![![4, -8, -20, -21, 14]], ![![-2, -5, -7, -7, 5]], ![![0, -19, -31, -18, 16]]]
  g := ![![![-9, -15, -23, -30, 31], ![22, 29, 52, 33, -59], ![2, -9, -2, -57, 20], ![32, 24, 65, -46, -46], ![66, 44, 131, -123, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [11, 10, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 7, 11], [6, 5, 2], [0, 1]]
 g := ![![[7, 1, 10], [8, 10], [1]], ![[8, 3, 4, 7], [8, 9], [12, 7, 2, 5]], ![[4, 10, 10, 8], [9, 9], [0, 5, 12, 8]]]
 h' := ![![[1, 7, 11], [7, 4, 6], [2, 3, 7], [0, 1]], ![[6, 5, 2], [4, 4, 9], [12, 6, 3], [1, 7, 11]], ![[0, 1], [4, 5, 11], [8, 4, 3], [6, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 4], []]
 b := ![[], [12, 11, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [11, 10, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![25177768, 19118705, -4463641, 12065688, 37361936]
  a := ![1, -4, -2, -5, 28]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15128008, -21521291, -40400077, 12065688, 37361936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4757, -350, -4785, -463, 1136]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![4757, -350, -4785, -463, 1136]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![4757, -350, -4785, -463, 1136], ![9088, 6115, 226, -1155, -253], ![-1012, 4602, 7270, -82, -1859], ![-11980, -4535, 4571, 1382, -926], ![-4108, -879, 2501, 447, -559]]]
  hmulB := by decide  
  f := ![![![18257, -5841, 11493, 3067, -3556]], ![![6238, -2011, 3934, 1033, -1207]], ![![12972, -4097, 8140, 2228, -2545]], ![![16520, -5394, 10451, 2671, -3167]], ![![13265, -4069, 8264, 2387, -2638]]]
  g := ![![![3113, -350, -4785, -463, 1136], ![-1021, 6115, 226, -1155, -253], ![-5313, 4602, 7270, -82, -1859], ![-2276, -4535, 4571, 1382, -926], ![-1475, -879, 2501, 447, -559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![371, 262, 50, 419, -225]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![371, 262, 50, 419, -225]] 
 ![![13, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![371, 262, 50, 419, -225], ![-1800, -1123, -314, -1894, 1032], ![4128, 2470, 771, 4245, -2325], ![-8400, -4924, -1618, -8542, 4689], ![11856, 6954, 2282, 12061, -6622]]]
  hmulB := by decide  
  f := ![![![-961, 1032, 2294, 55, -573]], ![![-944, 513, 1562, 74, -384]], ![![-643, 356, 1073, 50, -264]], ![![-163, 574, 940, -7, -240]], ![![-196, 296, 586, 7, -148]]]
  g := ![![![-316, 262, 50, 419, -225], ![1424, -1123, -314, -1894, 1032], ![-3188, 2470, 771, 4245, -2325], ![6412, -4924, -1618, -8542, 4689], ![-9053, 6954, 2282, 12061, -6622]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-173, 53, -107, -30, 31]] ![![4757, -350, -4785, -463, 1136]]
  ![![-961, 1032, 2294, 55, -573]] where
 M := ![![![-961, 1032, 2294, 55, -573]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-961, 1032, 2294, 55, -573]] ![![371, 262, 50, 419, -225]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [11, 13, 4, 16, 14, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 9, 2, 15, 3], [12, 5, 12, 12, 9], [2, 16, 12, 11, 4], [0, 3, 8, 13, 1], [0, 1]]
 g := ![![[1, 1, 15, 2, 16], [12, 10, 3, 1], [], []], ![[4, 12, 14, 8, 1, 4, 10, 14], [16, 3, 12, 15], [7, 16, 6, 15], [14, 2, 15, 9]], ![[7, 13, 15, 7, 6, 0, 15, 2], [8, 14, 14, 1], [10, 2, 7, 16], [0, 16, 0, 13]], ![[11, 0, 11, 6, 0, 6, 12, 4], [15, 9, 16, 13], [3, 7, 2, 9], [7, 12, 0, 16]], ![[0, 11, 13, 9, 5, 0, 3, 8], [6, 9], [11, 12, 5, 13], [4, 1, 12, 1]]]
 h' := ![![[6, 9, 2, 15, 3], [4, 6, 10, 7, 4], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[12, 5, 12, 12, 9], [7, 14, 14, 0, 4], [9, 0, 11, 11, 7], [1, 6, 11, 13, 7], [6, 9, 2, 15, 3]], ![[2, 16, 12, 11, 4], [5, 6, 5, 11, 15], [5, 6, 15, 14, 1], [8, 12, 3, 14, 4], [12, 5, 12, 12, 9]], ![[0, 3, 8, 13, 1], [1, 7, 15, 12, 16], [9, 12, 3, 6, 8], [12, 11, 1, 7, 14], [2, 16, 12, 11, 4]], ![[0, 1], [1, 1, 7, 4, 12], [13, 16, 5, 3], [7, 5, 1, 0, 9], [0, 3, 8, 13, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 3, 10, 16], [], [], []]
 b := ![[], [6, 14, 12, 11, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [11, 13, 4, 16, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1226136286079, 668471250182, 341514509532, 1397962496306, -1262258781486]
  a := ![-1, 7, 6, 9, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![72125663887, 39321838246, 20089088796, 82233088018, -74250516558]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47, 22, -36, -15, 13]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-47, 22, -36, -15, 13]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![11, 9, 6, 12, 1]] where
  M :=![![![-47, 22, -36, -15, 13], ![104, -3, 74, 34, -32], ![-128, -8, -37, -55, 35], ![88, 34, 10, 96, -49], ![-152, -76, -38, -133, 76]]]
  hmulB := by decide  
  f := ![![![-29, -20, 0, -21, -17]], ![![-136, -93, 2, -98, -80]], ![![-320, -218, 5, -229, -187]], ![![-680, -464, 10, -486, -397]], ![![-693, -473, 10, -496, -405]]]
  g := ![![![-10, -5, -6, -9, 13], ![24, 15, 14, 22, -32], ![-27, -17, -13, -25, 35], ![33, 25, 16, 36, -49], ![-52, -40, -26, -55, 76]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 4 2 4 [13, 2, 13, 11, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 0, 17, 4], [10, 10, 18, 10], [0, 8, 3, 5], [0, 1]]
 g := ![![[6, 17, 7, 4], [8, 8, 0, 7], [1], []], ![[1, 2, 18, 10, 1, 1], [4, 7, 3, 18, 1, 5], [9, 8, 16], [8, 17, 16]], ![[0, 14, 6, 11, 11, 12], [4, 15, 1, 13, 2, 13], [8, 1, 4], [11, 1, 5]], ![[0, 6, 18, 5, 15, 5], [1, 2, 14, 11, 14, 16], [8, 7, 4], [8, 2, 6]]]
 h' := ![![[17, 0, 17, 4], [10, 11, 8, 2], [6, 17, 6, 8], [0, 0, 1], [0, 1]], ![[10, 10, 18, 10], [6, 0, 4, 9], [3, 6, 4, 14], [14, 10, 4, 4], [17, 0, 17, 4]], ![[0, 8, 3, 5], [0, 3, 8, 9], [16, 12, 0, 8], [14, 13, 3, 17], [10, 10, 18, 10]], ![[0, 1], [6, 5, 18, 18], [15, 3, 9, 8], [10, 15, 11, 17], [0, 8, 3, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [10, 1, 3], []]
 b := ![[], [], [8, 18, 15, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 4
  hpos := by decide
  P := [13, 2, 13, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5420546483, -3166108224, -1061178512, -5530368100, 3107698404]
  a := ![0, -12, 0, -22, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2084485733, -1638704940, -1037229944, -2253828892, 3107698404]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 130321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 20, 0, 21, 17]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![29, 20, 0, 21, 17]] 
 ![![19, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![29, 20, 0, 21, 17], ![136, 93, -2, 98, 80], ![320, 218, -5, 229, 187], ![680, 464, -10, 486, 397], ![1544, 1054, -22, 1105, 902]]]
  hmulB := by decide  
  f := ![![![47, -22, 36, 15, -13]], ![![-3, -1, -2, -1, 1]], ![![29, -10, 19, 10, -8]], ![![30, -18, 26, 6, -7]], ![![8, 4, 2, 7, -4]]]
  g := ![![![-15, 20, 0, 21, 17], ![-69, 93, -2, 98, 80], ![-161, 218, -5, 229, 187], ![-342, 464, -10, 486, 397], ![-778, 1054, -22, 1105, 902]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-47, 22, -36, -15, 13]] ![![29, 20, 0, 21, 17]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-425, -89, -123, -194, -93]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-425, -89, -123, -194, -93]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![4, 11, 1, 0, 0], ![2, 8, 0, 1, 0], ![5, 13, 0, 0, 1]] where
  M :=![![![-425, -89, -123, -194, -93], ![-744, -819, 210, -703, -675], ![-2700, -1603, -116, -1801, -1392], ![-5196, -3578, 93, -3736, -3060], ![-11940, -8090, 129, -8513, -6929]]]
  hmulB := by decide  
  f := ![![![641, 40, -525, -68, 123]], ![![984, 799, 216, -121, -81]], ![![568, 409, 52, -70, -27]], ![![338, 253, 45, -39, -21]], ![![671, 452, 18, -83, -20]]]
  g := ![![![40, 175, -123, -194, -93], ![139, 490, 210, -703, -675], ![362, 1399, -116, -1801, -1392], ![748, 2829, 93, -3736, -3060], ![1705, 6464, 129, -8513, -6929]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [9, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 22], [0, 1]]
 g := ![![[10, 18], [11, 6], [18, 4], [1]], ![[0, 5], [0, 17], [3, 19], [1]]]
 h' := ![![[2, 22], [16, 15], [22, 12], [14, 2], [0, 1]], ![[0, 1], [0, 8], [0, 11], [18, 21], [2, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [10, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [9, 21, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1221, -348, -949, -2661, 5172]
  a := ![13, 5, 5, 6, -13]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-781, -1559, -949, -2661, 5172]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1807, 1190, 285, 1960, -1061]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![1807, 1190, 285, 1960, -1061]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![8, 21, 1, 0, 0], ![16, 12, 0, 1, 0], ![8, 16, 0, 0, 1]] where
  M :=![![![1807, 1190, 285, 1960, -1061], ![-8488, -5173, -1540, -8817, 4819], ![19276, 11442, 3644, 19735, -10816], ![-39020, -22861, -7523, -39671, 21785], ![55108, 32301, 10615, 56034, -30752]]]
  hmulB := by decide  
  f := ![![![2537, 5409, 5175, -470, -1393]], ![![-11144, 1217, 11758, 1069, -2803]], ![![-9780, 2678, 12542, 874, -3035]], ![![-3772, 4122, 9103, 214, -2274]], ![![-6844, 2594, 9771, 583, -2381]]]
  g := ![![![-1015, -493, 285, 1960, -1061], ![4624, 2429, -1540, -8817, 4819], ![-10396, -5602, 3644, 19735, -10816], ![20940, 11418, -7523, -39671, 21785], ![-29580, -16130, 10615, 56034, -30752]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 22], [0, 1]]
 g := ![![[0, 8], [0, 12], [], [1]], ![[0, 15], [0, 11], [], [1]]]
 h' := ![![[0, 22], [0, 10], [0, 9], [20], [0, 1]], ![[0, 1], [0, 13], [0, 14], [20], [0, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [3, 0, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4, 10, -25, -42, 144]
  a := ![-1, -2, 0, -3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12, -55, -25, -42, 144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-291575, -320278, -178602, 42004, 52444]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![-291575, -320278, -178602, 42004, 52444]] 
 ![![23, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-291575, -320278, -178602, 42004, 52444], ![419552, -249961, -724564, -32100, 178456], ![713824, 309684, -217861, -83918, 41078], ![-45464, 517616, 755884, -16079, -194566], ![81736, 213564, 220996, -16710, -58919]]]
  hmulB := by decide  
  f := ![![![-61345, 21678, -39990, -9320, 13952]], ![![-8483, 3745, -5998, -852, 2424]], ![![-61114, 22400, -40393, -8938, 14802]], ![![3400, 1848, 340, 2381, 998]], ![![1121, 4462, -2510, 2526, 4421]]]
  g := ![![![225505, -320278, -178602, 42004, 52444], ![757883, -249961, -724564, -32100, 178456], ![170316, 309684, -217861, -83918, 41078], ![-829062, 517616, 755884, -16079, -194566], ![-251699, 213564, 220996, -16710, -58919]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-425, -89, -123, -194, -93]] ![![1807, 1190, 285, 1960, -1061]]
  ![![61345, -21678, 39990, 9320, -13952]] where
 M := ![![![61345, -21678, 39990, 9320, -13952]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![61345, -21678, 39990, 9320, -13952]] ![![-291575, -320278, -178602, 42004, 52444]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![-23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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


lemma PB1072I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB1072I0 : PrimesBelowBoundCertificateInterval O 1 23 1072 where
  m := 9
  g := ![5, 5, 5, 2, 3, 3, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB1072I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N1, I2N1]
    · exact ![I3N0, I3N1, I3N1, I3N2, I3N3]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
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
    · exact ![343, 49]
    · exact ![1331, 11, 11]
    · exact ![2197, 13, 13]
    · exact ![1419857]
    · exact ![130321, 19]
    · exact ![529, 529, 23]
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
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N1
      exact NI3N2
      exact NI3N3
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
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I3N3, I5N0, I7N0, I7N1, I11N1, I11N2, I13N1, I13N2, I19N1, I23N0, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N1, I2N1], [I3N0, I3N1, I3N1, I3N2, I3N3], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N1, I11N2], [I13N1, I13N2], [], [I19N1], [I23N0, I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
