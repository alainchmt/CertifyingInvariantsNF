
import IdealArithmetic.Examples.NF5_1_8100000_3.RI5_1_8100000_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27, 58, -41, 23, 16]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![27, 58, -41, 23, 16]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![27, 58, -41, 23, 16], ![-9, -71, 90, -75, 30], ![-135, -144, -11, 75, -180], ![222, 450, -297, 154, 150], ![-193, -554, 499, -346, -19]]]
  hmulB := by decide  
  f := ![![![-2129, 874, -113, -136, -416]], ![![348, -149, 21, 27, 72]], ![![-117, 36, -5, -3, -18]], ![![-1222, 494, -67, -79, -238]], ![![-603, 250, -35, -43, -121]]]
  g := ![![![-6, 58, -41, 23, 16], ![18, -71, 90, -75, 30], ![-15, -144, -11, 75, -180], ![-41, 450, -297, 154, 150], ![86, -554, 499, -346, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-18358, 7567, -1002, -1216, -3619]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![-18358, 7567, -1002, -1216, -3619]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-18358, 7567, -1002, -1216, -3619], ![6022, -2481, 329, 399, 1187], ![-1975, 815, -107, -130, -389], ![-2687, 1107, -146, -177, -529], ![7952, -3279, 434, 527, 1568]]]
  hmulB := by decide  
  f := ![![![19, 25, -5, -5, 22]], ![![-15, -38, 32, -21, -5]], ![![23, 84, -85, 64, -10]], ![![76, 89, -5, -32, 96]], ![![-116, -202, 106, -37, -101]]]
  g := ![![![-10044, 7567, -1002, -1216, -3619], ![3294, -2481, 329, 399, 1187], ![-1082, 815, -107, -130, -389], ![-1471, 1107, -146, -177, -529], ![4351, -3279, 434, 527, 1568]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, 1, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![0, -1, 1, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, -1, 1, 0, 1], ![-2, -4, 1, 1, -1], ![3, 5, -6, 4, 3], ![0, -5, 5, -6, 3], ![-5, -3, -3, 3, -9]]]
  hmulB := by decide  
  f := ![![![771, -318, 42, 51, 152]], ![![259, -107, 14, 17, 51]], ![![427, -176, 23, 28, 84]], ![![442, -182, 24, 29, 87]], ![![-167, 69, -9, -11, -33]]]
  g := ![![![0, -1, 1, 0, 1], ![0, -4, 1, 1, -1], ![0, 5, -6, 4, 3], ![3, -5, 5, -6, 3], ![-1, -3, -3, 3, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![27, 58, -41, 23, 16]] ![![-18358, 7567, -1002, -1216, -3619]]
  ![![16, -7, 1, 1, 3]] where
 M := ![![![16, -7, 1, 1, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![16, -7, 1, 1, 3]] ![![-18358, 7567, -1002, -1216, -3619]]
  ![![-316688, 130524, -17286, -20975, -62427]] where
 M := ![![![-316688, 130524, -17286, -20975, -62427]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-316688, 130524, -17286, -20975, -62427]] ![![0, -1, 1, 0, 1]]
  ![![-771, 318, -42, -51, -152]] where
 M := ![![![-771, 318, -42, -51, -152]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-771, 318, -42, -51, -152]] ![![0, -1, 1, 0, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-2, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![348, -149, 21, 27, 72]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![348, -149, 21, 27, 72]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![348, -149, 21, 27, 72], ![-117, 36, -5, -3, -18], ![33, -35, 0, 5, 12], ![49, -29, -3, -2, 8], ![-149, 73, -13, -19, -37]]]
  hmulB := by decide  
  f := ![![![-34, -47, 13, 5, -38]], ![![27, 58, -41, 23, 16]], ![![-9, -71, 90, -75, 30]], ![![-81, -101, 15, 26, -98]], ![![121, 223, -129, 55, 97]]]
  g := ![![![68, -149, 21, 27, 72], ![-27, 36, -5, -3, -18], ![3, -35, 0, 5, 12], ![11, -29, -3, -2, 8], ![-25, 73, -13, -19, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 6, -4, 2, 2]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 6, -4, 2, 2]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![3, 6, -4, 2, 2], ![-2, -9, 10, -8, 2], ![-12, -10, -5, 10, -18], ![24, 46, -28, 13, 18], ![-24, -62, 52, -34, -7]]]
  hmulB := by decide  
  f := ![![![101, -42, 8, 10, 22]], ![![56, -25, 6, 8, 14]], ![![70, -34, 7, 10, 18]], ![![4, -6, 0, 1, 2]], ![![19, -8, 0, 0, 3]]]
  g := ![![![-1, 6, -4, 2, 2], ![-2, -9, 10, -8, 2], ![12, -10, -5, 10, -18], ![-10, 46, -28, 13, 18], ![1, -62, 52, -34, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![348, -149, 21, 27, 72]] ![![348, -149, 21, 27, 72]]
  ![![129825, -53478, 7036, 8526, 25542]] where
 M := ![![![129825, -53478, 7036, 8526, 25542]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![129825, -53478, 7036, 8526, 25542]] ![![3, 6, -4, 2, 2]]
  ![![3615, -1516, 196, 244, 720]] where
 M := ![![![3615, -1516, 196, 244, 720]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![3615, -1516, 196, 244, 720]] ![![3, 6, -4, 2, 2]]
  ![![101, -42, 8, 10, 22]] where
 M := ![![![101, -42, 8, 10, 22]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N3 : IdealMulLeCertificate' Table 
  ![![101, -42, 8, 10, 22]] ![![3, 6, -4, 2, 2]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1, I3N1, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N1
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1 ⊙ MulI3N2 ⊙ MulI3N3)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -3, 3, -2, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-1, -3, 3, -2, 0]] 
 ![![5, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-1, -3, 3, -2, 0], ![-2, 0, -3, 4, -4], ![12, 19, -8, 2, 12], ![-10, -27, 23, -15, -2], ![1, 19, -27, 23, -11]]]
  hmulB := by decide  
  f := ![![![333, -135, 17, 20, 64]], ![![45, -17, 2, 2, 8]], ![![274, -109, 14, 16, 52]], ![![10, -3, 1, 1, 2]], ![![-29, 11, -1, -1, -5]]]
  g := ![![![-2, -3, 3, -2, 0], ![2, 0, -3, 4, -4], ![5, 19, -8, 2, 12], ![-15, -27, 23, -15, -2], ![18, 19, -27, 23, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-1, -3, 3, -2, 0]] ![![-1, -3, 3, -2, 0]]
  ![![63, 114, -64, 26, 52]] where
 M := ![![![63, 114, -64, 26, 52]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![63, 114, -64, 26, 52]] ![![-1, -3, 3, -2, 0]]
  ![![-1267, -1119, -447, 1008, -1848]] where
 M := ![![![-1267, -1119, -447, 1008, -1848]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-1267, -1119, -447, 1008, -1848]] ![![-1, -3, 3, -2, 0]]
  ![![-13787, -67020, 76212, -60460, 17424]] where
 M := ![![![-13787, -67020, 76212, -60460, 17424]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-13787, -67020, 76212, -60460, 17424]] ![![-1, -3, 3, -2, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![1684395, 3452865, -2311025, 1219570, 1111880]]]
 hmul := by decide  
 g := ![![![![336879, 690573, -462205, 243914, 222376]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19617, -8084, 1070, 1298, 3866]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![19617, -8084, 1070, 1298, 3866]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![5, 4, 3, 5, 1]] where
  M :=![![![19617, -8084, 1070, 1298, 3866], ![-6434, 2655, -352, -428, -1270], ![2112, -864, 115, 138, 414], ![2872, -1180, 158, 191, 566], ![-8498, 3500, -462, -560, -1673]]]
  hmulB := by decide  
  f := ![![![-5, -12, 10, -6, -2]], ![![-2, 9, -16, 16, -10]], ![![36, 48, -11, -6, 42]], ![![-44, -100, 74, -43, -22]], ![![-17, -40, 31, -17, -7]]]
  g := ![![![41, -3364, -1504, -2576, 3866], ![-12, 1105, 494, 846, -1270], ![6, -360, -161, -276, 414], ![6, -492, -220, -377, 566], ![-19, 1456, 651, 1115, -1673]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 4, 6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2, 5], [6, 1, 1, 3], [0, 3, 1, 4], [0, 1]]
 g := ![![[0, 2, 6, 1], []], ![[6, 2, 2, 0, 3], [6, 4, 6]], ![[1, 4, 3, 1, 2, 3], [2, 4, 3, 0, 0, 6]], ![[0, 3, 1, 4, 4, 2], [5, 6, 6, 5, 5, 1]]]
 h' := ![![[0, 2, 5], [0, 0, 0, 1], [0, 1]], ![[6, 1, 1, 3], [6, 1, 3, 3], [0, 2, 5]], ![[0, 3, 1, 4], [1, 6, 3, 1], [6, 1, 1, 3]], ![[0, 1], [5, 0, 1, 2], [0, 3, 1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 0, 2], []]
 b := ![[], [], [3, 5, 5, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 4, 6, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1706758, 1869657, 577207, -1277790, 2235938]
  a := ![-5, -7, -3, -8, -10]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1353276, -1010585, -875801, -1779640, 2235938]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, -12, 10, -6, -2]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-5, -12, 10, -6, -2]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-5, -12, 10, -6, -2], ![-2, 9, -16, 16, -10], ![36, 48, -11, -6, 42], ![-44, -100, 74, -43, -22], ![26, 100, -106, 80, -15]]]
  hmulB := by decide  
  f := ![![![19617, -8084, 1070, 1298, 3866]], ![![13093, -5395, 714, 866, 2580]], ![![8709, -3588, 475, 576, 1716]], ![![11620, -4788, 634, 769, 2290]], ![![-1214, 500, -66, -80, -239]]]
  g := ![![![7, -12, 10, -6, -2], ![-9, 9, -16, 16, -10], ![-21, 48, -11, -6, 42], ![58, -100, 74, -43, -22], ![-68, 100, -106, 80, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![19617, -8084, 1070, 1298, 3866]] ![![-5, -12, 10, -6, -2]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193949, -79935, 10587, 12846, 38232]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![193949, -79935, 10587, 12846, 38232]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![6, 9, 5, 1, 0], ![6, 6, 10, 0, 1]] where
  M :=![![![193949, -79935, 10587, 12846, 38232], ![-63618, 26222, -3471, -4212, -12540], ![20868, -8601, 1142, 1386, 4116], ![28386, -11703, 1551, 1883, 5598], ![-84015, 34623, -4587, -5565, -16561]]]
  hmulB := by decide  
  f := ![![![25, 75, -69, 48, 0]], ![![48, 4, 75, -90, 96]], ![![-282, -447, 196, -36, -276]], ![![-54, -102, 64, -31, -42]], ![![-219, -405, 239, -105, -175]]]
  g := ![![![-10229, -38631, -39633, 12846, 38232], ![3354, 12670, 12999, -4212, -12540], ![-1104, -4161, -4268, 1386, 4116], ![-1500, -5658, -5804, 1883, 5598], ![4431, 16734, 17168, -5565, -16561]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 3, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 2, 10], [9, 8, 1], [0, 1]]
 g := ![![[10, 7, 5], [0, 6, 1], []], ![[8, 2, 7, 8], [0, 4, 6, 2], [2, 1]], ![[6, 3, 0, 1], [8, 0, 6, 4], [0, 1]]]
 h' := ![![[8, 2, 10], [0, 7, 7], [0, 0, 1], [0, 1]], ![[9, 8, 1], [7, 8, 5], [4, 7, 8], [8, 2, 10]], ![[0, 1], [3, 7, 10], [4, 4, 2], [9, 8, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 1], []]
 b := ![[], [10, 3, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 3, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2067924, -9048636, 12423871, -10321660, 1669289]
  a := ![9, -56, 5, -57, 15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4531482, 6711870, 4303571, -10321660, 1669289]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, -75, 69, -48, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-25, -75, 69, -48, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![6, 1, 1, 0, 0], ![8, 3, 0, 1, 0], ![4, 7, 0, 0, 1]] where
  M :=![![![-25, -75, 69, -48, 0], ![-48, -4, -75, 90, -96], ![282, 447, -196, 36, 276], ![-234, -627, 537, -361, -54], ![27, 459, -633, 543, -259]]]
  hmulB := by decide  
  f := ![![![-193949, 79935, -10587, -12846, -38232]], ![![63618, -26222, 3471, 4212, 12540]], ![![-101904, 41999, -5563, -6750, -20088]], ![![-126284, 52047, -6894, -8365, -24894]], ![![-22405, 9233, -1224, -1485, -4417]]]
  g := ![![![-5, 0, 69, -48, 0], ![6, 43, -75, 90, -96], ![6, -127, -196, 36, 276], ![-32, 27, 537, -361, -54], ![47, 116, -633, 543, -259]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[5, 4], [0, 5], [1]], ![[10, 7], [9, 6], [1]]]
 h' := ![![[4, 10], [0, 2], [3, 4], [0, 1]], ![[0, 1], [8, 9], [8, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [8, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [8, 7, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39, 0, -62, 55, 56]
  a := ![0, -4, 0, -5, -1]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-23, -45, -62, 55, 56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![193949, -79935, 10587, 12846, 38232]] ![![-25, -75, 69, -48, 0]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [8, 6, 11, 4, 3, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 10, 0, 7], [5, 2, 3, 3, 5], [7, 7, 4, 6, 7], [9, 2, 9, 4, 7], [0, 1]]
 g := ![![[3, 3, 2, 0, 12], [10, 1], []], ![[1, 12, 11, 5, 1, 8, 6, 7], [2, 11, 10, 3], [7, 12, 0, 6, 9, 0, 11, 5]], ![[0, 6, 2, 11, 4, 1, 2, 6], [2, 12, 8, 3], [9, 3, 7, 6, 3, 11, 6, 8]], ![[8, 12, 10, 7, 4, 4, 11, 11], [12, 1, 7, 12], [1, 5, 0, 12, 0, 10, 9, 5]], ![[2, 7, 10, 11, 12, 0, 2, 2], [2, 9, 1, 9], [5, 9, 2, 11, 10, 11, 1, 5]]]
 h' := ![![[2, 1, 10, 0, 7], [11, 10, 1, 1, 5], [0, 0, 0, 1], [0, 1]], ![[5, 2, 3, 3, 5], [0, 10, 2, 12, 12], [4, 4, 3, 4, 4], [2, 1, 10, 0, 7]], ![[7, 7, 4, 6, 7], [11, 10, 11, 5, 10], [1, 7, 8, 7, 4], [5, 2, 3, 3, 5]], ![[9, 2, 9, 4, 7], [4, 2, 8, 12, 10], [10, 8, 3, 10, 8], [7, 7, 4, 6, 7]], ![[0, 1], [10, 7, 4, 9, 2], [0, 7, 12, 4, 10], [9, 2, 9, 4, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 8, 11, 6], [], [], []]
 b := ![[], [11, 10, 6, 7, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [8, 6, 11, 4, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4800963414, 10051845258, -3229300490, 1966040999, 3333707663]
  a := ![9, 27, 5, 26, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![369304878, 773218866, -248407730, 151233923, 256439051]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6919, -12800, 7448, -3208, -5514]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-6919, -12800, 7448, -3208, -5514]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 14, 11, 2, 1]] where
  M :=![![![-6919, -12800, 7448, -3208, -5514], ![7820, 24891, -23828, 17202, -902], ![19006, 5704, 23087, -29552, 35306], ![-53992, -94440, 50072, -17943, -46754], ![64328, 147128, -110820, 66452, 32019]]]
  hmulB := by decide  
  f := ![![![-2199, 976, -32, -48, -386]], ![![724, -349, 204, 274, 290]], ![![-306, -248, 231, 392, 258]], ![![-424, -312, 32, 161, 118]], ![![402, -518, 313, 490, 425]]]
  g := ![![![-407, 3788, 4006, 460, -5514], ![460, 2207, -818, 1118, -902], ![1118, -28740, -21487, -5892, 35306], ![-3176, 32948, 33198, 4445, -46754], ![3784, -17714, -27237, 142, 32019]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 4 2 4 [10, 11, 1, 6, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 9, 3, 16], [8, 6, 7, 7], [2, 1, 7, 11], [0, 1]]
 g := ![![[5, 3, 6, 9], [12, 0, 2], [1], []], ![[9, 4, 0, 4, 9, 8], [3, 10, 9], [0, 9, 16], [11, 5, 1]], ![[0, 15, 2, 13, 3, 10], [11, 11, 9], [10, 4, 2], [2, 8, 15]], ![[12, 16, 1, 16, 10, 6], [3, 16, 8], [3, 7, 4], [16, 6, 2]]]
 h' := ![![[1, 9, 3, 16], [14, 3, 7, 14], [7, 6, 16, 11], [0, 0, 1], [0, 1]], ![[8, 6, 7, 7], [8, 6, 12, 3], [15, 12, 12, 14], [10, 0, 11, 4], [1, 9, 3, 16]], ![[2, 1, 7, 11], [9, 7, 3, 13], [0, 2, 9, 14], [10, 11, 10, 11], [8, 6, 7, 7]], ![[0, 1], [3, 1, 12, 4], [13, 14, 14, 12], [14, 6, 12, 2], [2, 1, 7, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 11], []]
 b := ![[], [], [7, 16, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 4
  hpos := by decide
  P := [10, 11, 1, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49190741, -162070191, 158639575, -114755869, 9797251]
  a := ![-11, -9, -5, -7, -21]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2893573, -17601865, 2992342, -7902963, 9797251]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 83521 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2199, 976, -32, -48, -386]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-2199, 976, -32, -48, -386]] 
 ![![17, 0, 0, 0, 0], ![14, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-2199, 976, -32, -48, -386], ![724, -349, 204, 274, 290], ![-306, -248, 231, 392, 258], ![-424, -312, 32, 161, 118], ![912, -568, -140, -140, 91]]]
  hmulB := by decide  
  f := ![![![-6919, -12800, 7448, -3208, -5514]], ![![-5238, -9077, 4732, -1630, -4594]], ![![-2138, -5688, 4863, -3248, -518]], ![![-5211, -9320, 5136, -1999, -4372]], ![![935, 3384, -3452, 2588, -387]]]
  g := ![![![-745, 976, -32, -48, -386], ![34, -349, 204, 274, 290], ![-144, -248, 231, 392, 258], ![121, -312, 32, 161, 118], ![591, -568, -140, -140, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-6919, -12800, 7448, -3208, -5514]] ![![-2199, 976, -32, -48, -386]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-177, -408, 308, -186, -86]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-177, -408, 308, -186, -86]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![8, 5, 15, 1, 0], ![0, 1, 17, 0, 1]] where
  M :=![![![-177, -408, 308, -186, -86], ![-14, 375, -580, 516, -286], ![1088, 1352, -197, -358, 1318], ![-1490, -3216, 2284, -1293, -874], ![1068, 3560, -3488, 2556, -233]]]
  hmulB := by decide  
  f := ![![![357241, -147240, 19500, 23662, 70422]], ![![-117182, 48293, -6396, -7760, -23098]], ![![38436, -15848, 2097, 2546, 7578]], ![![152676, -62933, 8333, 10113, 30098]], ![![20078, -8281, 1095, 1330, 3959]]]
  g := ![![![69, 32, 240, -186, -86], ![-218, -101, -182, 516, -286], ![208, 96, -907, -358, 1318], ![466, 217, 1923, -1293, -874], ![-1020, -473, -1993, 2556, -233]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [15, 11, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 6, 9], [16, 12, 10], [0, 1]]
 g := ![![[13, 3, 4], [9, 10, 16], [11, 1], []], ![[11, 17, 15, 5], [12, 3, 11, 9], [0, 11], [11, 5]], ![[13, 13, 3, 3], [15, 2, 8, 14], [10, 17], [10, 5]]]
 h' := ![![[14, 6, 9], [17, 15, 17], [6, 16, 15], [0, 0, 1], [0, 1]], ![[16, 12, 10], [13, 13, 16], [11, 18, 1], [12, 10, 12], [14, 6, 9]], ![[0, 1], [7, 10, 5], [9, 4, 3], [11, 9, 6], [16, 12, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 14], []]
 b := ![[], [3, 2, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [15, 11, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![461569, 379732, 211884, -412010, 691364]
  a := ![6, -4, 4, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![197771, 92022, -282166, -412010, 691364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-357241, 147240, -19500, -23662, -70422]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-357241, 147240, -19500, -23662, -70422]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![17, 8, 1, 0, 0], ![8, 15, 0, 1, 0], ![2, 13, 0, 0, 1]] where
  M :=![![![-357241, 147240, -19500, -23662, -70422], ![117182, -48293, 6396, 7760, 23098], ![-38436, 15848, -2097, -2546, -7578], ![-52286, 21552, -2852, -3461, -10306], ![154748, -63784, 8448, 10252, 30507]]]
  hmulB := by decide  
  f := ![![![177, 408, -308, 186, 86]], ![![14, -375, 580, -516, 286]], ![![107, 136, -21, -32, 128]], ![![164, 45, 208, -261, 308]], ![![-28, -401, 548, -468, 217]]]
  g := ![![![16021, 82824, -19500, -23662, -70422], ![-5254, -27165, 6396, 7760, 23098], ![1723, 8912, -2097, -2546, -7578], ![2342, 12119, -2852, -3461, -10306], ![-6942, -35881, 8448, 10252, 30507]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [11, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 18], [0, 1]]
 g := ![![[2, 7], [3, 1], [9], [1]], ![[0, 12], [0, 18], [9], [1]]]
 h' := ![![[16, 18], [5, 8], [3, 1], [8, 16], [0, 1]], ![[0, 1], [0, 11], [0, 18], [17, 3], [16, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [18, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [11, 3, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2611, -7331, 3421, -460, 70]
  a := ![19, 19, 10, 20, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3012, -1511, 3421, -460, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-177, -408, 308, -186, -86]] ![![-357241, 147240, -19500, -23662, -70422]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2484073, 1023815, -135589, -164524, -489670]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-2484073, 1023815, -135589, -164524, -489670]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![10, 6, 10, 1, 0], ![22, 5, 13, 0, 1]] where
  M :=![![![-2484073, 1023815, -135589, -164524, -489670], ![814816, -335836, 44475, 53968, 160622], ![-267276, 110149, -14592, -17704, -52686], ![-363574, 149847, -19849, -24085, -71672], ![1076045, -443487, 58733, 71265, 212111]]]
  hmulB := by decide  
  f := ![![![-101, -319, 303, -218, 10]], ![![-238, -66, -299, 378, -446]], ![![1270, 2071, -958, 226, 1202]], ![![404, 627, -259, 31, 404]], ![![569, 930, -434, 105, 537]]]
  g := ![![![431909, 193883, 342407, -164524, -489670], ![-141676, -63598, -112317, 53968, 160622], ![46472, 20861, 36842, -17704, -52686], ![63220, 28379, 50119, -24085, -71672], ![-187089, -83984, -148320, 71265, 212111]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [3, 13, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 19, 21], [11, 3, 2], [0, 1]]
 g := ![![[16, 17, 16], [17, 17, 12], [22, 9, 1], []], ![[9, 17, 7, 10], [1, 0, 7, 22], [16, 17, 0, 5], [6, 4]], ![[0, 15, 9, 9], [14, 0, 10, 4], [12, 16, 3, 9], [2, 4]]]
 h' := ![![[21, 19, 21], [18, 13, 19], [3, 9, 9], [0, 0, 1], [0, 1]], ![[11, 3, 2], [2, 14, 8], [20, 11, 9], [9, 18, 3], [21, 19, 21]], ![[0, 1], [0, 19, 19], [10, 3, 5], [0, 5, 19], [11, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 2], []]
 b := ![[], [12, 8, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [3, 13, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4158, 859, 6129, -7157, 8038]
  a := ![1, -3, 1, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-4396, 157, -1165, -7157, 8038]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-101, -319, 303, -218, 10]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-101, -319, 303, -218, 10]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![21, 3, 1, 0, 0], ![3, 18, 0, 1, 0], ![17, 12, 0, 0, 1]] where
  M :=![![![-101, -319, 303, -218, 10], ![-238, -66, -299, 378, -446], ![1270, 2071, -958, 226, 1202], ![-970, -2703, 2387, -1635, -152], ![-11, 1815, -2699, 2383, -1265]]]
  hmulB := by decide  
  f := ![![![-2484073, 1023815, -135589, -164524, -489670]], ![![814816, -335836, 44475, 53968, 160622]], ![![-2173407, 895772, -118632, -143948, -428430]], ![![297865, -122772, 16258, 19729, 58718]], ![![-1364148, 562232, -74460, -90349, -268905]]]
  g := ![![![-260, 112, 303, -218, 10], ![543, -27, -299, 378, -446], ![12, -589, -958, 226, 1202], ![-1896, 930, 2387, -1635, -152], ![3088, -774, -2699, 2383, -1265]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [7, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 22], [0, 1]]
 g := ![![[13, 9], [1, 13], [10, 1], [1]], ![[22, 14], [14, 10], [11, 22], [1]]]
 h' := ![![[1, 22], [16, 3], [22, 6], [16, 1], [0, 1]], ![[0, 1], [19, 20], [5, 17], [17, 22], [1, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [17, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [7, 22, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3253, -5556, 1843, 338, -2851]
  a := ![13, 9, 10, 5, 23]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![239, 741, 1843, 338, -2851]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-2484073, 1023815, -135589, -164524, -489670]] ![![-101, -319, 303, -218, 10]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![23, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


lemma PB178I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB178I0 : PrimesBelowBoundCertificateInterval O 1 23 178 where
  m := 9
  g := ![5, 5, 5, 2, 2, 1, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB178I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
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
    · exact ![3, 3, 3, 3, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![1331, 121]
    · exact ![371293]
    · exact ![83521, 17]
    · exact ![6859, 361]
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N1, I17N1]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N1], [], [I17N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
