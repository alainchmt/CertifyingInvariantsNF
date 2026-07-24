
import IdealArithmetic.Examples.NF5_1_1012500_1.RI5_1_1012500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 6, 1, -2, -1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 6, 1, -2, -1]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 6, 1, -2, -1], ![-6, 2, 5, 0, -2], ![-12, -6, 3, 2, 0], ![6, -3, -3, 1, 1], ![12, 3, -7, -2, 2]]]
  hmulB := by decide  
  f := ![![![4, -3, 1, 2, -2]], ![![-6, 2, -3, -4, 1]], ![![6, -6, 1, 2, -4]], ![![-15, 6, -7, -9, 3]], ![![3, -9, -2, -2, -6]]]
  g := ![![![1, 6, 1, -2, -1], ![-3, 2, 5, 0, -2], ![-6, -6, 3, 2, 0], ![3, -3, -3, 1, 1], ![6, 3, -7, -2, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1, 0, 1, 1, 0]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![1, 0, 1, 1, 0], ![0, 1, 1, 1, 1], ![6, 0, 4, 5, 1], ![0, 3, 1, 1, 2], ![12, 3, 9, 10, 3]]]
  hmulB := by decide  
  f := ![![![-4, 0, -1, -1, 1]], ![![1, -2, 0, 1, 0]], ![![-5, 3, -3, -3, 2]], ![![6, -3, 3, 3, -2]], ![![-6, 3, -1, -2, 1]]]
  g := ![![![0, 0, 1, 1, 0], ![-1, 1, 1, 1, 1], ![1, 0, 4, 5, 1], ![-2, 3, 1, 1, 2], ![0, 3, 9, 10, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -6, -10, 1, 4]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![13, -6, -10, 1, 4]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![13, -6, -10, 1, 4], ![24, 13, -8, -5, 1], ![6, 24, 7, -7, -5], ![-18, -9, 7, 4, -1], ![-24, -27, 3, 10, 3]]]
  hmulB := by decide  
  f := ![![![44, -24, 18, 23, -13]], ![![-17, 10, -7, -8, 5]], ![![91, -51, 38, 45, -26]], ![![-71, 42, -30, -32, 20]], ![![66, -39, 29, 28, -17]]]
  g := ![![![14, -6, -10, 1, 4], ![12, 13, -8, -5, 1], ![-9, 24, 7, -7, -5], ![-10, -9, 7, 4, -1], ![-5, -27, 3, 10, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 6, 1, -2, -1]] ![![2, 6, 1, -2, -1]]
  ![![-68, 21, 48, -2, -18]] where
 M := ![![![-68, 21, 48, -2, -18]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-68, 21, 48, -2, -18]] ![![2, 6, 1, -2, -1]]
  ![![-1066, -702, 313, 266, -12]] where
 M := ![![![-1066, -702, 313, 266, -12]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-1066, -702, 313, 266, -12]] ![![1, 0, 1, 1, 0]]
  ![![668, 60, -358, -57, 107]] where
 M := ![![![668, 60, -358, -57, 107]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![668, 60, -358, -57, 107]] ![![13, -6, -10, 1, 4]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![6434, -14196, -9744, 3716, 4900]]]
 hmul := by decide  
 g := ![![![![3217, -7098, -4872, 1858, 2450]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, -5, 3, 2, -2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![7, -5, 3, 2, -2]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 2, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![7, -5, 3, 2, -2], ![-12, 7, -6, -4, 2], ![12, -12, 5, 0, -4], ![-18, 12, -10, -3, 2], ![-6, -6, -4, -12, -1]]]
  hmulB := by decide  
  f := ![![![9, -9, -9, 2, 4]], ![![24, 9, -10, -4, 2]], ![![7, 5, -2, -2, 0]], ![![13, 1, -7, -1, 2]], ![![-4, -14, -4, 4, 3]]]
  g := ![![![2, -3, 3, 2, -2], ![-2, 5, -6, -4, 2], ![5, -4, 5, 0, -4], ![-3, 6, -10, -3, 2], ![4, 6, -4, -12, -1]]]
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
  c := ![260, 577, 488, 431, 473]
  a := ![0, -1, -4, -1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-535, -95, 488, 431, 473]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, -1, -2, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-3, 1, -1, -2, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-3, 1, -1, -2, 1], ![6, -3, 2, 4, -2], ![-12, 6, -5, -8, 4], ![18, -9, 7, 11, -6], ![-18, 9, -7, -10, 5]]]
  hmulB := by decide  
  f := ![![![-3, 0, 2, 0, -1]], ![![-2, -1, 0, 0, 0]], ![![0, -2, -1, 0, 0]], ![![0, 1, -1, -1, 0]], ![![0, 1, -1, -2, -1]]]
  g := ![![![-1, 1, -1, -2, 1], ![2, -3, 2, 4, -2], ![-4, 6, -5, -8, 4], ![6, -9, 7, 11, -6], ![-6, 9, -7, -10, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![7, -5, 3, 2, -2]] ![![-3, 1, -1, -2, 1]]
  ![![-15, 4, -4, -16, 7]] where
 M := ![![![-15, 4, -4, -16, 7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-15, 4, -4, -16, 7]] ![![-3, 1, -1, -2, 1]]
  ![![-297, 156, -118, -168, 92]] where
 M := ![![![-297, 156, -118, -168, 92]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-297, 156, -118, -168, 92]] ![![-3, 1, -1, -2, 1]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-1437, 867, -621, -606, 387]]]
 hmul := by decide  
 g := ![![![![-479, 289, -207, -202, 129]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 2, -2, -4, 2]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, 2, -2, -4, 2]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-5, 2, -2, -4, 2], ![12, -5, 4, 8, -4], ![-24, 12, -9, -16, 8], ![36, -18, 14, 23, -12], ![-36, 18, -14, -20, 11]]]
  hmulB := by decide  
  f := ![![![-1, 2, -2, -4, -2]], ![![-3, 1, -2, -4, -2]], ![![-5, -2, -3, -4, -2]], ![![-3, 0, -4, -5, -2]], ![![-8, -2, -10, -12, -5]]]
  g := ![![![-1, 2, -2, -4, 2], ![3, -5, 4, 8, -4], ![-7, 12, -9, -16, 8], ![11, -18, 14, 23, -12], ![-12, 18, -14, -20, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, 2, -2, -4, 2]] ![![-5, 2, -2, -4, 2]]
  ![![-119, 64, -48, -64, 36]] where
 M := ![![![-119, 64, -48, -64, 36]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![-119, 64, -48, -64, 36]] ![![-5, 2, -2, -4, 2]]
  ![![-1085, 666, -474, -436, 286]] where
 M := ![![![-1085, 666, -474, -436, 286]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-1085, 666, -474, -436, 286]] ![![-5, 2, -2, -4, 2]]
  ![![-1199, 1808, -1008, 1504, -248]] where
 M := ![![![-1199, 1808, -1008, 1504, -248]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![-1199, 1808, -1008, 1504, -248]] ![![-5, 2, -2, -4, 2]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![114955, -55070, 43230, 74940, -38470]]]
 hmul := by decide  
 g := ![![![![22991, -11014, 8646, 14988, -7694]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 26, 8, -8, -6]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![5, 26, 8, -8, -6]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![3, 4, 5, 1, 0], ![1, 2, 6, 0, 1]] where
  M :=![![![5, 26, 8, -8, -6], ![-36, 5, 22, 0, -8], ![-48, -36, 11, 12, 0], ![24, -6, -18, -1, 6], ![60, 18, -30, -12, 5]]]
  hmulB := by decide  
  f := ![![![-37, 22, -16, -16, 10]], ![![60, -37, 26, 24, -16]], ![![-96, 60, -43, -36, 24]], ![![-33, 20, -15, -13, 8]], ![![-79, 50, -36, -28, 19]]]
  g := ![![![5, 10, 12, -8, -6], ![-4, 3, 10, 0, -8], ![-12, -12, -7, 12, 0], ![3, -2, -7, -1, 6], ![13, 8, 0, -12, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 0, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 2, 2], [3, 4, 5], [0, 1]]
 g := ![![[6, 1, 4], [1]], ![[3, 4, 6, 2], [1, 1, 5, 1]], ![[1, 0, 0, 3], [4, 4, 4, 6]]]
 h' := ![![[6, 2, 2], [1, 0, 2], [0, 1]], ![[3, 4, 5], [0, 0, 1], [6, 2, 2]], ![[0, 1], [3, 0, 4], [3, 4, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 0, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-169650, 159558, -215782, -661736, 145379]
  a := ![3, -64, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![238597, 359392, 317232, -661736, 145379]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, 22, -16, -16, 10]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-37, 22, -16, -16, 10]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![5, 5, 1, 0, 0], ![6, 5, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-37, 22, -16, -16, 10], ![60, -37, 26, 24, -16], ![-96, 60, -43, -36, 24], ![120, -78, 54, 41, -30], ![-60, 42, -30, -12, 11]]]
  hmulB := by decide  
  f := ![![![5, 26, 8, -8, -6]], ![![-36, 5, 22, 0, -8]], ![![-29, 17, 23, -4, -10]], ![![-18, 25, 20, -7, -10]], ![![10, 10, -2, -4, -1]]]
  g := ![![![17, 26, -16, -16, 10], ![-26, -41, 26, 24, -16], ![41, 65, -43, -36, 24], ![-48, -79, 54, 41, -30], ![20, 36, -30, -12, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 4], [0, 1]], ![[0, 3], [0, 6]]]
 h' := ![![[0, 6], [0, 5], [0, 1]], ![[0, 1], [0, 2], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201, 132, 193, 217, 115]
  a := ![1, -3, -2, -1, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-328, -274, 193, 217, 115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![5, 26, 8, -8, -6]] ![![-37, 22, -16, -16, 10]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [1, 1, 5, 3, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 9, 3, 0, 10], [7, 4, 9, 1, 8], [9, 7, 6, 7, 3], [9, 1, 4, 3, 1], [0, 1]]
 g := ![![[8, 6, 8, 4, 3], [1], []], ![[9, 2, 2, 3, 7, 6], [4, 5, 9, 5, 7, 3, 5, 10], [0, 5, 6, 1]], ![[10, 3, 3, 3, 5, 4, 8, 2], [5, 0, 7, 8, 0, 3, 8, 6], [8, 10, 4, 9]], ![[0, 8, 6, 0, 9, 3, 1, 4], [0, 7, 5, 4, 1, 8, 10, 5], [0, 7, 8, 9]], ![[4, 3, 10, 8, 0, 7, 4, 5], [6, 1, 6, 7, 0, 8, 4, 1], [6, 9, 1, 1]]]
 h' := ![![[3, 9, 3, 0, 10], [10, 10, 6, 8, 6], [0, 0, 1], [0, 1]], ![[7, 4, 9, 1, 8], [8, 0, 5, 4], [9, 5, 0, 0, 1], [3, 9, 3, 0, 10]], ![[9, 7, 6, 7, 3], [3, 8, 5, 5, 5], [8, 5, 0, 10, 3], [7, 4, 9, 1, 8]], ![[9, 1, 4, 3, 1], [1, 5, 2, 4, 4], [4, 9, 10, 4, 8], [9, 7, 6, 7, 3]], ![[0, 1], [8, 10, 4, 1, 7], [9, 3, 0, 8, 10], [9, 1, 4, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 9, 6, 5], [], [], []]
 b := ![[], [4, 1, 3, 9, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [1, 1, 5, 3, 5, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4006752046, 1656158559, 3444948089, 3905872377, 1615396222]
  a := ![1, 19, 3, -1, 6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![364250186, 150559869, 313177099, 355079307, 146854202]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 0, -6, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-1, -2, 0, -6, 1]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![12, 11, 0, 7, 1]] where
  M :=![![![-1, -2, 0, -6, 1], ![6, -1, 0, 10, -6], ![-36, 6, -13, -34, 10], ![48, -21, 13, 41, -22], ![-84, 27, -39, -62, 19]]]
  hmulB := by decide  
  f := ![![![5, -1, -3, 0, 1]], ![![6, 5, -2, -2, 0]], ![![0, 6, 3, -2, -2]], ![![-6, -3, 1, 1, 0]], ![![6, 1, -4, -1, 1]]]
  g := ![![![-1, -1, 0, -1, 1], ![6, 5, 0, 4, -6], ![-12, -8, -1, -8, 10], ![24, 17, 1, 15, -22], ![-24, -14, -3, -15, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 4 2 3 [6, 6, 4, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 4, 6], [10, 9, 6, 1], [0, 10, 3, 6], [0, 1]]
 g := ![![[0, 6, 5, 3], [5, 10, 1], []], ![[7, 11, 5, 1, 9, 11], [2, 1, 9], [3, 6, 0, 5, 5, 8]], ![[2, 1, 9, 4, 1, 10], [11, 6, 10], [11, 7, 12, 8, 2, 1]], ![[0, 4, 1, 3, 6, 6], [11, 8, 3], [9, 11, 8, 11, 1, 8]]]
 h' := ![![[0, 6, 4, 6], [9, 1, 5, 4], [0, 0, 0, 1], [0, 1]], ![[10, 9, 6, 1], [0, 2, 0, 2], [8, 11, 4, 10], [0, 6, 4, 6]], ![[0, 10, 3, 6], [3, 8, 3, 6], [11, 5, 3, 6], [10, 9, 6, 1]], ![[0, 1], [3, 2, 5, 1], [11, 10, 6, 9], [0, 10, 3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 5, 9], []]
 b := ![[], [], [1, 1, 9, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 4
  hpos := by decide
  P := [6, 6, 4, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4383752, 4081953, 4779359, 5414632, 3346269]
  a := ![-1, 0, -2, 2, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2751652, -2517462, 367643, -1385327, 3346269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 28561 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 1, 3, 0, -1]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-5, 1, 3, 0, -1]] 
 ![![13, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![-5, 1, 3, 0, -1], ![-6, -5, 2, 2, 0], ![0, -6, -3, 2, 2], ![6, 3, -1, -1, 0], ![6, 9, 1, -2, -1]]]
  hmulB := by decide  
  f := ![![![1, 2, 0, 6, -1]], ![![0, 1, 0, 2, 0]], ![![3, 0, 1, 4, -1]], ![![-3, 3, -1, 1, 1]], ![![7, -1, 3, 8, -2]]]
  g := ![![![-1, 1, 3, 0, -1], ![0, -5, 2, 2, 0], ![1, -6, -3, 2, 2], ![0, 3, -1, -1, 0], ![-2, 9, 1, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-1, -2, 0, -6, 1]] ![![-5, 1, 3, 0, -1]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19, 7, -7, -10, 6]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-19, 7, -7, -10, 6]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![3, 8, 12, 1, 0], ![16, 6, 16, 0, 1]] where
  M :=![![![-19, 7, -7, -10, 6], ![36, -19, 12, 20, -10], ![-60, 36, -27, -36, 20], ![90, -48, 38, 49, -28], ![-78, 42, -28, -36, 21]]]
  hmulB := by decide  
  f := ![![![1, 1, 3, 2, 0]], ![![0, 1, 4, 4, 2]], ![![12, 0, 9, 12, 4]], ![![9, 1, 9, 11, 4]], ![![14, 2, 14, 16, 5]]]
  g := ![![![-5, 3, 1, -10, 6], ![8, -7, -4, 20, -10], ![-16, 12, 5, -36, 20], ![23, -16, -6, 49, -28], ![-18, 12, 4, -36, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [16, 9, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 1, 6], [9, 15, 11], [0, 1]]
 g := ![![[4, 16, 13], [16, 15], [13, 1], []], ![[8, 5, 14, 6], [0, 16], [3, 4], [4, 2]], ![[9, 11, 4, 7], [13, 2], [14, 1], [16, 2]]]
 h' := ![![[4, 1, 6], [15, 0, 9], [13, 3, 7], [0, 0, 1], [0, 1]], ![[9, 15, 11], [8, 4, 16], [12, 8, 4], [3, 8, 15], [4, 1, 6]], ![[0, 1], [4, 13, 9], [5, 6, 6], [12, 9, 1], [9, 15, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 2], []]
 b := ![[], [2, 6, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [16, 9, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-137456, -55920, -116942, -133970, -55388]
  a := ![0, 0, -6, -10, -4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![67686, 79304, 139818, -133970, -55388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 3, 2, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![1, 1, 3, 2, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![15, 11, 1, 0, 0], ![12, 1, 0, 1, 0], ![14, 2, 0, 0, 1]] where
  M :=![![![1, 1, 3, 2, 0], ![0, 1, 4, 4, 2], ![12, 0, 9, 12, 4], ![6, 6, 4, 5, 4], ![30, 12, 22, 24, 9]]]
  hmulB := by decide  
  f := ![![![-19, 7, -7, -10, 6]], ![![36, -19, 12, 20, -10]], ![![3, -4, 0, 2, 0]], ![![-6, 1, -2, -3, 2]], ![![-16, 6, -6, -8, 5]]]
  g := ![![![-4, -2, 3, 2, 0], ![-8, -3, 4, 4, 2], ![-19, -7, 9, 12, 4], ![-10, -3, 4, 5, 4], ![-42, -16, 22, 24, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16], [0, 1]]
 g := ![![[4, 2], [9], [9], [1]], ![[15, 15], [9], [9], [1]]]
 h' := ![![[14, 16], [15, 6], [14, 3], [12, 14], [0, 1]], ![[0, 1], [14, 11], [5, 14], [4, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111, 478, 182, 158, 247]
  a := ![13, -1, -2, 1, -6]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-469, -128, 182, 158, 247]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-19, 7, -7, -10, 6]] ![![1, 1, 3, 2, 0]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [10, 15, 0, 2, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 4, 15, 17, 4], [3, 16, 11, 17, 6], [10, 13, 14, 4, 15], [7, 4, 17, 0, 13], [0, 1]]
 g := ![![[16, 5, 17, 14, 1], [6, 8, 9, 12, 1], [], []], ![[16, 0, 15, 18, 13, 13, 4, 1], [10, 8, 14, 10, 8, 17, 17, 1], [16, 11], [0, 0, 5, 16]], ![[3, 18, 4, 15, 15, 16, 16, 16], [0, 10, 8, 8, 12, 10, 10, 16], [6, 0, 8, 1], [9, 1, 9, 17]], ![[2, 2, 11, 18, 5, 15, 1, 3], [16, 18, 5, 5, 13, 1, 3, 3], [13, 16, 16, 6], [7, 6, 8, 16]], ![[18, 15, 11, 16, 6, 6, 9, 2], [16, 18, 11, 13, 7, 15, 7, 15], [9, 12, 14, 16], [15, 6, 14, 17]]]
 h' := ![![[11, 4, 15, 17, 4], [16, 1, 18, 18, 18], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[3, 16, 11, 17, 6], [18, 11, 11, 10, 10], [3, 8, 0, 1, 9], [7, 12, 11, 12], [11, 4, 15, 17, 4]], ![[10, 13, 14, 4, 15], [8, 5, 7, 3, 3], [3, 1, 18, 6, 3], [14, 8, 8, 17, 1], [3, 16, 11, 17, 6]], ![[7, 4, 17, 0, 13], [4, 9, 17, 2, 2], [10, 6, 0, 10, 17], [11, 0, 13, 17, 14], [10, 13, 14, 4, 15]], ![[0, 1], [17, 12, 4, 5, 5], [3, 4, 1, 2, 8], [13, 18, 5, 11, 4], [7, 4, 17, 0, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 18, 12, 3], [], [], []]
 b := ![[], [17, 13, 0, 8, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [10, 15, 0, 2, 7, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2528539, 1790256, -866742, -1082943, 1007741]
  a := ![-1, -3, 1, -1, 2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-133081, 94224, -45618, -56997, 53039]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -12, 2, 4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-11, -12, 2, 4, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![15, 18, 9, 1, 0], ![21, 8, 12, 0, 1]] where
  M :=![![![-11, -12, 2, 4, 1], ![6, -11, -8, 4, 4], ![24, 6, -11, -4, 4], ![0, 9, 7, 1, -4], ![-24, 9, 15, -2, -3]]]
  hmulB := by decide  
  f := ![![![5, -3, 3, 2, -1]], ![![-6, 5, -2, 0, 2]], ![![12, -6, 7, 4, 0]], ![![3, 0, 3, 3, 1]], ![![9, -4, 6, 4, 0]]]
  g := ![![![-4, -4, -2, 4, 1], ![-6, -5, -4, 4, 4], ![0, 2, -1, -4, 4], ![3, 1, 2, 1, -4], ![3, 3, 3, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [1, 2, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 15, 22], [4, 7, 1], [0, 1]]
 g := ![![[8, 1, 4], [3, 16, 9], [14, 19, 1], []], ![[6, 0, 9, 7], [19, 2, 22, 14], [12, 14, 18, 20], [12, 1]], ![[2, 16, 15, 13], [18, 9], [19, 5, 0, 18], [10, 1]]]
 h' := ![![[15, 15, 22], [20, 13, 21], [9, 22, 20], [0, 0, 1], [0, 1]], ![[4, 7, 1], [19, 12, 19], [22, 21, 3], [6, 11, 7], [15, 15, 22]], ![[0, 1], [14, 21, 6], [10, 3], [6, 12, 15], [4, 7, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 3], []]
 b := ![[], [19, 0, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [1, 2, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-41900, 25965, -12628, -25134, 18791]
  a := ![3, 0, 3, -4, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2587, 14263, -518, -25134, 18791]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 3, -3, -2, 1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-5, 3, -3, -2, 1]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![18, 6, 1, 0, 0], ![6, 11, 0, 1, 0], ![15, 20, 0, 0, 1]] where
  M :=![![![-5, 3, -3, -2, 1], ![6, -5, 2, 0, -2], ![-12, 6, -7, -4, 0], ![6, -9, 3, -3, -2], ![-6, -3, -7, -2, -5]]]
  hmulB := by decide  
  f := ![![![11, 12, -2, -4, -1]], ![![-6, 11, 8, -4, -4]], ![![6, 12, 1, -4, -2]], ![![0, 8, 3, -3, -2]], ![![3, 17, 5, -6, -4]]]
  g := ![![![2, 1, -3, -2, 1], ![0, 1, 2, 0, -2], ![6, 4, -7, -4, 0], ![0, 2, 3, -3, -2], ![9, 7, -7, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 22], [0, 1]]
 g := ![![[22, 8], [10, 12], [9, 9], [1]], ![[0, 15], [0, 11], [13, 14], [1]]]
 h' := ![![[3, 22], [16, 10], [19, 9], [20, 3], [0, 1]], ![[0, 1], [0, 13], [0, 14], [6, 20], [3, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [22, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [3, 20, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42, 241, 109, 17, 269]
  a := ![1, 1, 1, -1, 4]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-267, -260, 109, 17, 269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-11, -12, 2, 4, 1]] ![![-5, 3, -3, -2, 1]]
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


lemma PB63I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB63I0 : PrimesBelowBoundCertificateInterval O 1 23 63 where
  m := 9
  g := ![5, 4, 5, 2, 1, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB63I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0, I2N1, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
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
    · exact ![343, 49]
    · exact ![161051]
    · exact ![28561, 13]
    · exact ![4913, 289]
    · exact ![2476099]
    · exact ![12167, 529]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N0
      exact NI2N1
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I13N1]
  Il := ![[I2N0, I2N0, I2N0, I2N1, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [], [I13N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
