
import IdealArithmetic.Examples.NF5_1_13500000_3.RI5_1_13500000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -3, -2, 1, 3]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-5, -3, -2, 1, 3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5, -3, -2, 1, 3], ![-8, -6, -3, 0, 2], ![-8, -11, -2, -6, -8], ![8, -5, 6, -14, -27], ![0, -2, 0, -2, -3]]]
  hmulB := by decide  
  f := ![![![6, 0, -3, 1, 5]], ![![-8, 2, 2, -1, -3]], ![![8, -7, 2, 0, -2]], ![![11, 4, -8, 3, 8]], ![![0, -4, 3, -1, -2]]]
  g := ![![![-3, -3, -2, 1, 3], ![-4, -6, -3, 0, 2], ![-1, -11, -2, -6, -8], ![11, -5, 6, -14, -27], ![1, -2, 0, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-168, 61, 45, -15, -126]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-168, 61, 45, -15, -126]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-168, 61, 45, -15, -126], ![444, -138, -101, 30, 294], ![-1056, 373, 270, -82, -756], ![1126, -365, -273, 91, 791], ![-958, 324, 236, -72, -670]]]
  hmulB := by decide  
  f := ![![![-14, -76, 76, -14, -133]], ![![238, 24, -129, 48, 168]], ![![-480, 157, 72, -66, 0]], ![![-251, -249, 341, -84, -546]], ![![-17, 148, -128, 19, 235]]]
  g := ![![![-84, 61, 45, -15, -126], ![222, -138, -101, 30, 294], ![-528, 373, 270, -82, -756], ![563, -365, -273, 91, 791], ![-479, 324, 236, -72, -670]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -11, 6, 0, -13]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![9, -11, 6, 0, -13]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![9, -11, 6, 0, -13], ![52, 15, -37, 12, 52], ![-160, 27, 47, -26, -40], ![2, -77, 70, -11, -128], ![-42, 40, -18, -2, 45]]]
  hmulB := by decide  
  f := ![![![-10, 7, -7, 18, 34]], ![![-37, 4, -20, 38, 75]], ![![-121, -16, -61, 92, 191]], ![![-171, -42, -80, 103, 221]], ![![-30, -7, -15, 20, 43]]]
  g := ![![![7, -11, 6, 0, -13], ![31, 15, -37, 12, 52], ![-104, 27, 47, -26, -40], ![10, -77, 70, -11, -128], ![-31, 40, -18, -2, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-5, -3, -2, 1, 3]] ![![-168, 61, 45, -15, -126]]
  ![![-128, -30, -27, 24, 41]] where
 M := ![![![-128, -30, -27, 24, 41]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-128, -30, -27, 24, 41]] ![![-168, 61, 45, -15, -126]]
  ![![24442, -9215, -6896, 2466, 19234]] where
 M := ![![![24442, -9215, -6896, 2466, 19234]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![24442, -9215, -6896, 2466, 19234]] ![![9, -11, 6, 0, -13]]
  ![![41262, -13801, -10097, 3122, 28796]] where
 M := ![![![41262, -13801, -10097, 3122, 28796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![41262, -13801, -10097, 3122, 28796]] ![![9, -11, 6, 0, -13]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![66038, -22070, -16138, 4976, 46026]]]
 hmul := by decide  
 g := ![![![![33019, -11035, -8069, 2488, 23013]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 5, 5, -4, -10]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![11, 5, 5, -4, -10]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 1, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![11, 5, 5, -4, -10], ![24, 12, 9, -6, -16], ![40, 27, 16, -6, -20], ![16, 19, 7, 7, 6], ![8, 6, 2, 0, -1]]]
  hmulB := by decide  
  f := ![![![-55, 19, 13, -4, -38]], ![![136, -46, -33, 10, 96]], ![![-133, 44, 33, -10, -94]], ![![168, -55, -42, 13, 118]], ![![-104, 34, 26, -8, -73]]]
  g := ![![![2, 3, 5, -4, -10], ![5, 6, 9, -6, -16], ![8, 11, 16, -6, -20], ![3, 4, 7, 7, 6], ![2, 2, 2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![106008, -61344, -57264, 55041, 154561]
  a := ![17, -58, -22, -45, 58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![54424, -38795, -57264, 55041, 154561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 17, 21, -22, -50]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![47, 17, 21, -22, -50]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![47, 17, 21, -22, -50], ![112, 46, 49, -46, -108], ![248, 115, 106, -86, -212], ![196, 111, 79, -43, -124], ![52, 26, 22, -16, -41]]]
  hmulB := by decide  
  f := ![![![-27, 7, 9, -2, -26]], ![![14, -2, -5, 2, 8]], ![![-106, 29, 30, -10, -72]], ![![76, -33, -11, 5, 36]], ![![-77, 27, 17, -6, -47]]]
  g := ![![![7, 17, 21, -22, -50], ![10, 46, 49, -46, -108], ![6, 115, 106, -86, -212], ![-20, 111, 79, -43, -124], ![-1, 26, 22, -16, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![11, 5, 5, -4, -10]] ![![47, 17, 21, -22, -50]]
  ![![1013, 288, 470, -570, -1244]] where
 M := ![![![1013, 288, 470, -570, -1244]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![1013, 288, 470, -570, -1244]] ![![47, 17, 21, -22, -50]]
  ![![20019, -11095, 12807, -31540, -59710]] where
 M := ![![![20019, -11095, 12807, -31540, -59710]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![20019, -11095, 12807, -31540, -59710]] ![![47, 17, 21, -22, -50]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-6412371, -3750642, -2570994, 1280130, 3841296]]]
 hmul := by decide  
 g := ![![![![-2137457, -1250214, -856998, 426710, 1280432]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -4, -2, 0, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-3, -4, -2, 0, 2]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-3, -4, -2, 0, 2], ![-8, -5, 0, -4, -8], ![16, -12, 3, -16, -24], ![20, 4, 18, -27, -60], ![12, -4, 0, -4, -3]]]
  hmulB := by decide  
  f := ![![![33, 12, -26, 8, 38]], ![![-24, 3, 8, -4, -8]], ![![16, -20, 11, 0, -24]], ![![60, 12, -38, 13, 52]], ![![-15, -8, 14, -4, -21]]]
  g := ![![![-1, -4, -2, 0, 2], ![0, -5, 0, -4, -8], ![8, -12, 3, -16, -24], ![16, 4, 18, -27, -60], ![3, -4, 0, -4, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-3, -4, -2, 0, 2]] ![![-3, -4, -2, 0, 2]]
  ![![33, 48, 0, 40, 68]] where
 M := ![![![33, 48, 0, 40, 68]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![33, 48, 0, 40, 68]] ![![-3, -4, -2, 0, 2]]
  ![![1133, -484, 654, -1544, -2922]] where
 M := ![![![1133, -484, 654, -1544, -2922]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![1133, -484, 654, -1544, -2922]] ![![-3, -4, -2, 0, 2]]
  ![![-55007, -4448, -28096, 44848, 91848]] where
 M := ![![![-55007, -4448, -28096, 44848, 91848]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-55007, -4448, -28096, 44848, 91848]] ![![-3, -4, -2, 0, 2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![1750205, 391420, 832990, -1110960, -2366550]]]
 hmul := by decide  
 g := ![![![![350041, 78284, 166598, -222192, -473310]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![33, -14, -2, 4, -5]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![33, -14, -2, 4, -5]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![6, 1, 3, 1, 0], ![1, 5, 0, 0, 1]] where
  M :=![![![33, -14, -2, 4, -5], ![36, 35, -48, 12, 76], ![-256, 0, 115, -48, -136], ![158, -112, 32, 13, -102], ![-134, 48, 16, -18, 9]]]
  hmulB := by decide  
  f := ![![![17, 10, 6, -2, -7]], ![![20, 21, 8, 4, 0]], ![![16, 32, -3, 32, 56]], ![![16, 27, 1, 21, 34]], ![![17, 17, 6, 4, 2]]]
  g := ![![![2, 1, -2, 4, -5], ![-16, -51, -12, 12, 76], ![24, 104, 37, -48, -136], ![26, 55, -1, 13, -102], ![-5, 3, 10, -18, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [1, 4, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 5], [6, 3, 2], [0, 1]]
 g := ![![[2, 4, 2], [1]], ![[1, 0, 2, 5], [6, 5, 4, 6]], ![[0, 6, 2, 4], [6, 2, 5, 1]]]
 h' := ![![[5, 3, 5], [6, 3, 4], [0, 1]], ![[6, 3, 2], [0, 0, 6], [5, 3, 5]], ![[0, 1], [0, 4, 4], [6, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2], []]
 b := ![[], [4, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [1, 4, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![99089, 39415, 35339, -28958, -73488]
  a := ![-7, -5, 10, -11, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![49475, 62259, 17459, -28958, -73488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, -10, -6, 2, 7]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-17, -10, -6, 2, 7]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![-17, -10, -6, 2, 7], ![-20, -21, -8, -4, 0], ![-16, -32, 3, -32, -56], ![58, -12, 28, -59, -112], ![-2, -4, 4, -10, -21]]]
  hmulB := by decide  
  f := ![![![-33, 14, 2, -4, 5]], ![![-24, 3, 8, -4, -8]], ![![13, 10, -15, 4, 23]], ![![-32, 20, -4, -3, 16]], ![![134, -48, -16, 18, -9]]]
  g := ![![![7, -10, -6, 2, 1], ![16, -21, -8, -4, 0], ![23, -32, 3, -32, -8], ![12, -12, 28, -59, -16], ![2, -4, 4, -10, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[2, 2], [6, 1]], ![[0, 5], [5, 6]]]
 h' := ![![[6, 6], [4, 4], [0, 1]], ![[0, 1], [0, 3], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [4, 1, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33876, -6451, -19337, 21266, 49728]
  a := ![31, 27, -42, 50, 108]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6583, -6451, -19337, 21266, 7104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![33, -14, -2, 4, -5]] ![![-17, -10, -6, 2, 7]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, -6, 4, 9]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![13, 0, -6, 4, 9]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![10, 0, 3, 9, 1]] where
  M :=![![![13, 0, -6, 4, 9], ![-20, 11, -6, 4, 20], ![-64, -22, 27, 4, -24], ![66, -22, -44, 33, 66], ![-58, 0, 20, -6, -19]]]
  hmulB := by decide  
  f := ![![![-23, 8, 6, -2, -17]], ![![60, -19, -14, 4, 40]], ![![-144, 50, 37, -12, -104]], ![![154, -50, -36, 11, 104]], ![![54, -16, -11, 3, 33]]]
  g := ![![![-7, 0, -3, -7, 9], ![-20, 1, -6, -16, 20], ![16, -2, 9, 20, -24], ![-54, -2, -22, -51, 66], ![12, 0, 7, 15, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [1, 2, 4, 8, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 0, 1, 4], [7, 2, 3, 3], [8, 8, 7, 4], [0, 1]]
 g := ![![[1, 7, 1, 3], [3, 1], []], ![[1, 7, 9, 0, 9, 4], [3, 7, 1, 3, 10, 9], [6, 1, 5]], ![[0, 3, 3, 2, 0, 3], [2, 5, 7, 0, 4, 4], [10, 1, 9]], ![[0, 10, 4, 9, 7, 9], [0, 6, 1, 4, 9, 3], [9, 5, 5]]]
 h' := ![![[10, 0, 1, 4], [8, 4, 8, 5], [0, 0, 1], [0, 1]], ![[7, 2, 3, 3], [5, 0, 5, 1], [6, 9, 0, 7], [10, 0, 1, 4]], ![[8, 8, 7, 4], [8, 2, 9, 1], [6, 7, 6, 7], [7, 2, 3, 3]], ![[0, 1], [0, 5, 0, 4], [0, 6, 4, 8], [8, 8, 7, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [9, 9, 2], []]
 b := ![[], [], [2, 10, 7, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [1, 2, 4, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![459712128, -44598180, -131400631, -8252175, 286891587]
  a := ![-35, -7, 48, -31, -122]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-219018522, -4054380, -90188672, -235479678, 286891587]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, -8, -6, 2, 17]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![23, -8, -6, 2, 17]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![23, -8, -6, 2, 17], ![-60, 19, 14, -4, -40], ![144, -50, -37, 12, 104], ![-154, 50, 36, -11, -104], ![130, -44, -32, 10, 91]]]
  hmulB := by decide  
  f := ![![![-13, 0, 6, -4, -9]], ![![-10, -1, 6, -4, -10]], ![![-6, 2, 3, -4, -6]], ![![-6, 2, 4, -3, -6]], ![![-3, 0, 2, -2, -4]]]
  g := ![![![4, -8, -6, 2, 17], ![-10, 19, 14, -4, -40], ![26, -50, -37, 12, 104], ![-26, 50, 36, -11, -104], ![23, -44, -32, 10, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![13, 0, -6, 4, 9]] ![![23, -8, -6, 2, 17]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-725, 250, 182, -56, -514]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-725, 250, 182, -56, -514]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![7, 7, 0, 8, 1]] where
  M :=![![![-725, 250, 182, -56, -514], ![1832, -599, -442, 140, 1272], ![-4528, 1530, 1105, -324, -3128], ![4692, -1574, -1170, 387, 3352], ![-4052, 1356, 988, -300, -2813]]]
  hmulB := by decide  
  f := ![![![15, -18, 10, 0, -22]], ![![88, 25, -62, 20, 88]], ![![-272, 46, 81, -44, -72]], ![![12, -130, 114, -17, -208]], ![![57, -71, 40, 0, -87]]]
  g := ![![![221, 296, 14, 312, -514], ![-544, -731, -34, -772, 1272], ![1336, 1802, 85, 1900, -3128], ![-1444, -1926, -90, -2033, 3352], ![1203, 1619, 76, 1708, -2813]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [5, 6, 8, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 7, 0, 8], [11, 9, 8, 9], [3, 9, 5, 9], [0, 1]]
 g := ![![[3, 6, 9, 3], [6, 12, 1], []], ![[6, 2, 4, 11, 8, 5], [6, 10, 1], [0, 10, 7, 9, 8, 5]], ![[11, 10, 5, 1, 0, 9], [2, 8, 9], [8, 1, 11, 1, 6, 1]], ![[11, 4, 3, 3], [3, 1, 9], [1, 8, 12, 2, 5, 1]]]
 h' := ![![[11, 7, 0, 8], [9, 8, 5, 9], [0, 0, 0, 1], [0, 1]], ![[11, 9, 8, 9], [8, 7, 0, 5], [5, 8, 1, 12], [11, 7, 0, 8]], ![[3, 9, 5, 9], [6, 11, 5, 12], [4, 3, 5, 3], [11, 9, 8, 9]], ![[0, 1], [1, 0, 3], [9, 2, 7, 10], [3, 9, 5, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [7, 9, 3], []]
 b := ![[], [], [4, 1, 11, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [5, 6, 8, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156150939, -134129779, -7939009, 5074174, 153377372]
  a := ![-13, 7, 23, 2, -52]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70576205, -92905491, -610693, -93995754, 153377372]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 18, -10, 0, 22]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-15, 18, -10, 0, 22]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![-15, 18, -10, 0, 22], ![-88, -25, 62, -20, -88], ![272, -46, -81, 44, 72], ![-12, 130, -114, 17, 208], ![76, -68, 28, 4, -71]]]
  hmulB := by decide  
  f := ![![![725, -250, -182, 56, 514]], ![![361, -127, -92, 28, 258]], ![![906, -310, -225, 68, 636]], ![![141, -52, -36, 9, 98]], ![![479, -162, -118, 36, 335]]]
  g := ![![![-11, 18, -10, 0, 22], ![-3, -25, 62, -20, -88], ![68, -46, -81, 44, 72], ![-63, 130, -114, 17, 208], ![45, -68, 28, 4, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-725, 250, 182, -56, -514]] ![![-15, 18, -10, 0, 22]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![-13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7699, -2699, -3465, 3716, 8387]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-7699, -2699, -3465, 3716, 8387]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![6, 12, 9, 13, 1]] where
  M :=![![![-7699, -2699, -3465, 3716, 8387], ![-18684, -7448, -8221, 7934, 18476], ![-42168, -18971, -18100, 15294, 37172], ![-34414, -18763, -14085, 8521, 23476], ![-8978, -4322, -3794, 2914, 7321]]]
  hmulB := by decide  
  f := ![![![-229, -27, 129, -46, -177]], ![![524, -146, -105, 74, 64]], ![![40, 493, -462, 86, 780]], ![![-1650, -95, 821, -327, -990]], ![![-910, 86, 327, -159, -325]]]
  g := ![![![-3413, -6079, -4644, -6195, 8387], ![-7620, -13480, -10265, -13662, 18476], ![-15600, -27355, -20744, -27526, 37172], ![-10310, -17675, -13257, -17451, 23476], ![-3112, -5422, -4099, -5427, 7321]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [2, 2, 2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 14, 15, 13], [9, 13, 1, 6], [10, 6, 1, 15], [0, 1]]
 g := ![![[2, 16], [4, 0, 4], [1], []], ![[3, 11, 10, 14, 4, 15], [15], [16, 14, 8], [11, 1, 16]], ![[10, 16, 4, 8, 0, 12], [9, 12, 9], [2, 6, 15], [1, 8, 2]], ![[5, 2, 3, 5, 5, 8], [9, 1, 1], [4, 13, 4], [10, 5, 4]]]
 h' := ![![[13, 14, 15, 13], [13, 0, 13], [15, 15, 15, 15], [0, 0, 1], [0, 1]], ![[9, 13, 1, 6], [3, 0, 5, 14], [4, 8, 7], [11, 0, 3, 5], [13, 14, 15, 13]], ![[10, 6, 1, 15], [3, 3, 3, 11], [15, 10, 5, 3], [11, 12, 12, 10], [9, 13, 1, 6]], ![[0, 1], [16, 14, 13, 9], [0, 1, 7, 16], [12, 5, 1, 2], [10, 6, 1, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 0, 11], []]
 b := ![[], [], [2, 3, 16, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [2, 2, 2, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27891841, -10009004, -6923993, 1477804, 23979020]
  a := ![13, -1, -18, 8, 46]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6822487, -17515132, -13102069, -18249968, 23979020]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-229, -27, 129, -46, -177]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-229, -27, 129, -46, -177]] 
 ![![17, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-229, -27, 129, -46, -177], ![524, -146, -105, 74, 64], ![40, 493, -462, 86, 780], ![-1650, -95, 821, -327, -990], ![706, 174, -470, 162, 619]]]
  hmulB := by decide  
  f := ![![![-7699, -2699, -3465, 3716, 8387]], ![![-5175, -1867, -2318, 2434, 5527]], ![![-4292, -1751, -1880, 1774, 4160]], ![![-3383, -1580, -1440, 1157, 2861]], ![![-981, -413, -427, 390, 924]]]
  g := ![![![-11, -27, 129, -46, -177], ![116, -146, -105, 74, 64], ![-211, 493, -462, 86, 780], ![-124, -95, 821, -327, -990], ![-5, 174, -470, 162, 619]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-7699, -2699, -3465, 3716, 8387]] ![![-229, -27, 129, -46, -177]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [11, 15, 7, 11, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 12, 15, 8, 6], [18, 7, 15, 6, 4], [13, 11, 12, 10, 5], [12, 7, 15, 14, 4], [0, 1]]
 g := ![![[11, 7, 8, 5, 4], [18, 10, 12, 17, 1], [], []], ![[1, 5, 8, 0, 18, 5], [7, 11, 2, 3, 10, 12, 8, 16], [3, 5, 6, 9], [2, 9, 5, 17]], ![[18, 1, 9, 8, 12, 2, 10, 16], [7, 12, 12, 17, 2, 18, 11, 5], [13, 1, 14, 1], [14, 5, 16, 16]], ![[5, 5, 7, 18, 15, 3, 5, 7], [11, 8, 2, 13, 11, 2, 1, 16], [2, 14, 3, 7], [11, 16, 12, 6]], ![[13, 4, 15, 15, 11, 18, 11, 4], [1, 5, 17, 0, 5, 0, 16, 4], [8, 13, 4, 16], [18, 18, 4, 16]]]
 h' := ![![[12, 12, 15, 8, 6], [11, 0, 10, 11, 17], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[18, 7, 15, 6, 4], [17, 18, 3, 2], [12, 12, 13, 3, 16], [8, 7, 15, 15, 16], [12, 12, 15, 8, 6]], ![[13, 11, 12, 10, 5], [13, 16, 8, 6, 17], [10, 10, 18, 17, 14], [18, 6, 12, 11, 18], [18, 7, 15, 6, 4]], ![[12, 7, 15, 14, 4], [7, 17, 2, 16, 3], [2, 8, 16, 5, 8], [10, 2, 3, 7, 8], [13, 11, 12, 10, 5]], ![[0, 1], [2, 6, 15, 3, 1], [16, 8, 10, 13, 18], [3, 4, 7, 5, 15], [12, 7, 15, 14, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 7, 9, 12], [], [], []]
 b := ![[], [16, 13, 9, 13, 17], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [11, 15, 7, 11, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![306204331911, 43184595265, 93416379583, -129691059028, -221806655367]
  a := ![45, 13, -59, 47, 156]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![16116017469, 2272873435, 4916651557, -6825845212, -11674034493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2111, -79, -877, 382, 1009]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![2111, -79, -877, 382, 1009]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![5, 18, 14, 1, 0], ![2, 3, 5, 0, 1]] where
  M :=![![![2111, -79, -877, 382, 1009], ![-2508, 1616, -353, -226, 1312], ![-6152, -3087, 5596, -1610, -8412], ![14858, -1891, -4949, 2489, 4898], ![-7994, 10, 3586, -1490, -4297]]]
  hmulB := by decide  
  f := ![![![-17, 55, -29, 96, 179]], ![![-332, 50, -163, 326, 628]], ![![-1208, -169, -650, 978, 2052]], ![![-1085, -72, -568, 921, 1885]], ![![-320, -29, -173, 274, 567]]]
  g := ![![![-79, -434, -490, 382, 1009], ![-174, 76, -163, -226, 1312], ![814, 2223, 3052, -1610, -8412], ![-321, -2669, -2795, 2489, 4898], ![350, 1727, 1997, -1490, -4297]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [12, 16, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 8], [7, 22, 15], [0, 1]]
 g := ![![[15, 19, 12], [20, 21, 1], [13, 11, 1], []], ![[18, 11, 18, 3], [6, 8, 2, 1], [5, 12, 21, 8], [14, 18]], ![[5, 13, 6, 11], [15, 13, 1, 11], [5, 20], [7, 18]]]
 h' := ![![[4, 0, 8], [13, 5, 14], [5, 5, 1], [0, 0, 1], [0, 1]], ![[7, 22, 15], [21, 4, 3], [11, 20, 16], [9, 20, 22], [4, 0, 8]], ![[0, 1], [18, 14, 6], [5, 21, 6], [11, 3], [7, 22, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 10], []]
 b := ![[], [3, 7, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [12, 16, 12, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182643, -242648, -121581, 71068, 249578]
  a := ![19, 5, -26, 18, 66]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29211, -98722, -102801, 71068, 249578]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, -1, 1, 0, -1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-3, -1, 1, 0, -1]] 
 ![![23, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![16, 0, 0, 0, 1]] where
  M :=![![![-3, -1, 1, 0, -1], ![4, -2, -3, 2, 4], ![-8, 3, -6, 2, 12], ![-22, -5, 9, -3, -12], ![6, 2, -6, 2, 9]]]
  hmulB := by decide  
  f := ![![![45, -15, -11, 2, 29]], ![![9, -3, -2, 0, 5]], ![![52, -17, -12, 2, 32]], ![![3, 0, 0, -1, -1]], ![![42, -14, -10, 2, 27]]]
  g := ![![![0, -1, 1, 0, -1], ![0, -2, -3, 2, 4], ![-5, 3, -6, 2, 12], ![2, -5, 9, -3, -12], ![-2, 2, -6, 2, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![223, 12, 54, -88, -150]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![223, 12, 54, -88, -150]] 
 ![![23, 0, 0, 0, 0], ![11, 1, 0, 0, 0], ![17, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![11, 0, 0, 0, 1]] where
  M :=![![![223, 12, 54, -88, -150], ![248, 189, 240, -244, -632], ![1552, 244, 389, -496, -888], ![660, 628, 602, -481, -1380], ![652, -36, 16, -84, 15]]]
  hmulB := by decide  
  f := ![![![-1983, -4476, 4994, -1040, -8454]], ![![341, -2055, 1730, -244, -3206]], ![![-3801, -2424, 3931, -1072, -6050]], ![![-3028, -4356, 5354, -1217, -8820]], ![![-847, -1376, 1642, -364, -2727]]]
  g := ![![![97, 12, 54, -88, -150], ![215, 189, 240, -244, -632], ![433, 244, 389, -496, -888], ![278, 628, 602, -481, -1380], ![85, -36, 16, -84, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![2111, -79, -877, 382, 1009]] ![![-3, -1, 1, 0, -1]]
  ![![-1983, -4476, 4994, -1040, -8454]] where
 M := ![![![-1983, -4476, 4994, -1040, -8454]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![-1983, -4476, 4994, -1040, -8454]] ![![223, 12, 54, -88, -150]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB229I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB229I0 : PrimesBelowBoundCertificateInterval O 1 23 229 where
  m := 9
  g := ![5, 4, 5, 2, 2, 2, 2, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB229I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
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
    · exact ![9, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![343, 49]
    · exact ![14641, 11]
    · exact ![28561, 13]
    · exact ![83521, 17]
    · exact ![2476099]
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I13N1, I17N1, I23N1, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [I13N1], [I17N1], [], [I23N1, I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
