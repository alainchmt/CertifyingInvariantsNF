
import IdealArithmetic.Examples.NF5_1_7812500_1.RI5_1_7812500_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 4, -3, -2, 6]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![-2, 4, -3, -2, 6]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2, 4, -3, -2, 6], ![4, -10, 6, 1, -6], ![-2, 11, -5, 7, -12], ![-14, 17, -14, -28, 66], ![-2, 4, -2, -2, 5]]]
  hmulB := by decide  
  f := ![![![145, 7, -43, -29, 114]], ![![29, 1, -9, -6, 24]], ![![12, -1, -5, -3, 12]], ![![6, -3, -4, -2, 6]], ![![13, -1, -5, -3, 11]]]
  g := ![![![-1, 4, -3, -2, 6], ![2, -10, 6, 1, -6], ![-1, 11, -5, 7, -12], ![-7, 17, -14, -28, 66], ![-1, 4, -2, -2, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 0, 0, -1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1, 0, 0, 0, -1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 0, 0, 0, -1], ![0, 2, 2, 1, -5], ![-2, 6, 5, 2, -7], ![-4, 7, 6, 2, 1], ![-2, 4, 3, 1, 0]]]
  hmulB := by decide  
  f := ![![![2, 1, -1, 0, 1]], ![![1, 1, -1, -1, 3]], ![![3, -3, 2, 2, -5]], ![![-3, 10, -7, -2, 9]], ![![1, 1, -1, 0, 1]]]
  g := ![![![1, 0, 0, 0, -1], ![0, 2, 2, 1, -5], ![-4, 6, 5, 2, -7], ![-10, 7, 6, 2, 1], ![-5, 4, 3, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 1, 5, 3, -11]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-13, 1, 5, 3, -11]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-13, 1, 5, 3, -11], ![-6, 1, 2, 1, -1], ![-2, -4, -4, -2, 13], ![4, -17, -16, -7, 29], ![0, -8, -7, -3, 13]]]
  hmulB := by decide  
  f := ![![![4, -9, 6, 3, -10]], ![![-1, 4, -2, 2, -3]], ![![1, -9, 4, -8, 14]], ![![21, -34, 27, 31, -81]], ![![2, -4, 3, 2, -6]]]
  g := ![![![-11, 1, 5, 3, -11], ![-5, 1, 2, 1, -1], ![4, -4, -4, -2, 13], ![22, -17, -16, -7, 29], ![9, -8, -7, -3, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![-2, 4, -3, -2, 6]] ![![1, 0, 0, 0, -1]]
  ![![0, 0, -1, 0, 1]] where
 M := ![![![0, 0, -1, 0, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![0, 0, -1, 0, 1]] ![![-13, 1, 5, 3, -11]]
  ![![2, -4, -3, -1, 0]] where
 M := ![![![2, -4, -3, -1, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, -4, -3, -1, 0]] ![![-13, 1, 5, 3, -11]]
  ![![0, 27, 30, 15, -86]] where
 M := ![![![0, 27, 30, 15, -86]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![0, 27, 30, 15, -86]] ![![-13, 1, 5, 3, -11]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![-162, 340, 296, 120, -320]]]
 hmul := by decide  
 g := ![![![![-81, 170, 148, 60, -160]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 8, -6, -8, 20]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-7, 8, -6, -8, 20]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![2, 0, 1, 1, 0], ![0, 1, 1, 0, 1]] where
  M :=![![![-7, 8, -6, -8, 20], ![16, -35, 24, 14, -44], ![-28, 74, -45, -2, 32], ![4, -62, 24, -67, 124], ![-4, 4, -4, -8, 19]]]
  hmulB := by decide  
  f := ![![![3, -12, -10, -4, 12]], ![![8, -13, -8, -2, -12]], ![![4, 18, 25, 14, -96]], ![![-6, 36, 39, 19, -100]], ![![0, 19, 23, 12, -73]]]
  g := ![![![3, -4, -6, -8, 20], ![-4, 3, 18, 14, -44], ![-8, 14, -25, -2, 32], ![46, -62, -11, -67, 124], ![4, -5, -5, -8, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 0, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 2], [1, 2, 1], [0, 1]]
 g := ![![[1]], ![[0, 2, 1, 2]], ![[2, 1, 2, 1]]]
 h' := ![![[1, 0, 2], [0, 1]], ![[1, 2, 1], [1, 0, 2]], ![[0, 1], [1, 2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [2, 1, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 0, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26008, -18888, 50255, 37487, -169704]
  a := ![5, -3, 16, 11, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16322, 50272, 60824, 37487, -169704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -12, -10, -4, 12]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, -12, -10, -4, 12]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] where
  M :=![![![3, -12, -10, -4, 12], ![8, -13, -8, -2, -12], ![4, 18, 25, 14, -96], ![-28, 114, 112, 51, -228], ![-12, 52, 52, 24, -111]]]
  hmulB := by decide  
  f := ![![![-7, 8, -6, -8, 20]], ![![3, -9, 6, 2, -8]], ![![-14, 30, -19, -6, 24]], ![![-1, -18, 6, -25, 48]], ![![-4, 4, -4, -8, 19]]]
  g := ![![![13, -12, -10, -4, 4], ![13, -13, -8, -2, -4], ![-26, 18, 25, 14, -32], ![-139, 114, 112, 51, -76], ![-64, 52, 52, 24, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
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

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![254, -199, 597, 342, -1707]
  a := ![4, -3, 13, 8, -35]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-361, -199, 597, 342, -569]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-7, 8, -6, -8, 20]] ![![3, -12, -10, -4, 12]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 1, -9, -6, 24]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![29, 1, -9, -6, 24]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![29, 1, -9, -6, 24], ![12, -1, -5, -3, 12], ![6, -3, -4, -2, 6], ![4, -2, -1, 0, -6], ![6, -1, -2, -1, 1]]]
  hmulB := by decide  
  f := ![![![3, -4, 3, 5, -12]], ![![-2, 4, -3, -2, 6]], ![![4, -10, 6, 1, -6]], ![![-2, 11, -5, 7, -12]], ![![1, -1, 1, 2, -5]]]
  g := ![![![1, 1, -9, -6, 24], ![0, -1, -5, -3, 12], ![0, -3, -4, -2, 6], ![2, -2, -1, 0, -6], ![1, -1, -2, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![29, 1, -9, -6, 24]] ![![29, 1, -9, -6, 24]]
  ![![919, 43, -272, -183, 714]] where
 M := ![![![919, 43, -272, -183, 714]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![919, 43, -272, -183, 714]] ![![29, 1, -9, -6, 24]]
  ![![29087, 1344, -8643, -5813, 22752]] where
 M := ![![![29087, 1344, -8643, -5813, 22752]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![29087, 1344, -8643, -5813, 22752]] ![![29, 1, -9, -6, 24]]
  ![![921053, 42546, -273622, -184020, 719988]] where
 M := ![![![921053, 42546, -273622, -184020, 719988]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![921053, 42546, -273622, -184020, 719988]] ![![29, 1, -9, -6, 24]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![29163205, 1347425, -8663675, -5826700, 22798200]]]
 hmul := by decide  
 g := ![![![![5832641, 269485, -1732735, -1165340, 4559640]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1833, -84, 544, 366, -1432]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-1833, -84, 544, 366, -1432]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![5, 0, 4, 3, 1]] where
  M :=![![![-1833, -84, 544, 366, -1432], ![-732, -35, 218, 146, -572], ![-292, -14, 87, 60, -232], ![-120, 0, 30, 19, -80], ![-312, -14, 92, 62, -243]]]
  hmulB := by decide  
  f := ![![![1, -4, -4, -2, 8]], ![![4, -9, -6, -2, 4]], ![![4, -2, -3, 0, -16]], ![![0, 20, 30, 13, -80]], ![![3, 6, 10, 5, -43]]]
  g := ![![![761, -12, 896, 666, -1432], ![304, -5, 358, 266, -572], ![124, -2, 145, 108, -232], ![40, 0, 50, 37, -80], ![129, -2, 152, 113, -243]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 0, 5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 3], [6, 4, 0, 5], [2, 5, 4, 2], [0, 1]]
 g := ![![[3, 4, 4, 1], []], ![[3, 2, 2, 6, 3], [2, 6, 6]], ![[3, 2, 3, 0, 5, 3], [2, 6, 2, 2, 3, 6]], ![[6, 1, 3, 2, 2, 4], [1, 4, 6, 2, 3, 1]]]
 h' := ![![[3, 4, 3], [0, 0, 0, 1], [0, 1]], ![[6, 4, 0, 5], [1, 2, 4, 6], [3, 4, 3]], ![[2, 5, 4, 2], [1, 4, 0, 3], [6, 4, 0, 5]], ![[0, 1], [2, 1, 3, 4], [2, 5, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [0, 6, 2], []]
 b := ![[], [], [6, 5, 6, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [6, 0, 5, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1837632466, -2662340751, 665145940, 956896328, -5530740683]
  a := ![-26, 23, -80, -56, 235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![4213047983, -380334393, 3255444096, 2507016911, -5530740683]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 4, 4, 2, -8]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1, 4, 4, 2, -8]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-1, 4, 4, 2, -8], ![-4, 9, 6, 2, -4], ![-4, 2, 3, 0, 16], ![0, -20, -30, -13, 80], ![0, -10, -12, -6, 37]]]
  hmulB := by decide  
  f := ![![![1833, 84, -544, -366, 1432]], ![![1152, 53, -342, -230, 900]], ![![1351, 62, -401, -270, 1056]], ![![279, 12, -82, -55, 216]], ![![1092, 50, -324, -218, 853]]]
  g := ![![![-1, 4, 4, 2, -8], ![-8, 9, 6, 2, -4], ![-13, 2, 3, 0, 16], ![-11, -20, -30, -13, 80], ![-6, -10, -12, -6, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-1833, -84, 544, 366, -1432]] ![![-1, 4, 4, 2, -8]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 3, 1, 0, -2]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-1, 3, 1, 0, -2]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 4, 1, 0, 0], ![2, 0, 0, 1, 0], ![3, 6, 0, 0, 1]] where
  M :=![![![-1, 3, 1, 0, -2], ![0, 1, 7, 3, -10], ![-6, 13, 0, 2, 4], ![-4, -8, -9, -14, 56], ![-2, -1, -4, -3, 19]]]
  hmulB := by decide  
  f := ![![![555, 26, -165, -111, 434]], ![![222, 10, -65, -44, 172]], ![![341, 16, -101, -68, 266]], ![![104, 5, -31, -21, 82]], ![![281, 13, -83, -56, 219]]]
  g := ![![![0, 1, 1, 0, -2], ![-1, 3, 7, 3, -10], ![-2, -1, 0, 2, 4], ![-9, -28, -9, -14, 56], ![-3, -9, -4, -3, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[7, 5], [6, 9], [1]], ![[0, 6], [0, 2], [1]]]
 h' := ![![[3, 10], [1, 7], [2, 3], [0, 1]], ![[0, 1], [0, 4], [0, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [6, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [9, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1692, -947, 5570, 4737, -14686]
  a := ![11, -6, 39, 29, -100]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![766, 5899, 5570, 4737, -14686]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, 3, 3, -8]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![3, -4, 3, 3, -8]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![8, 10, 1, 0, 0], ![8, 7, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![3, -4, 3, 3, -8], ![-6, 14, -9, -4, 14], ![8, -24, 14, -3, -2], ![6, 7, 1, 31, -64], ![2, -3, 2, 3, -7]]]
  hmulB := by decide  
  f := ![![![15, 1, -3, -2, 4]], ![![4, 9, 7, 3, -16]], ![![14, 11, 6, 2, -14]], ![![12, 9, 4, 1, -6]], ![![9, 2, -1, -1, 3]]]
  g := ![![![1, -5, 3, 3, -8], ![0, 12, -9, -4, 14], ![-6, -13, 14, -3, -2], ![18, -20, 1, 31, -64], ![1, -4, 2, 3, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10], [0, 1]]
 g := ![![[9, 5], [10, 4], [1]], ![[10, 6], [2, 7], [1]]]
 h' := ![![[9, 10], [10, 7], [1, 9], [0, 1]], ![[0, 1], [7, 4], [5, 2], [9, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [8, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [10, 2, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-206, 1988, -2452, 1480, -1656]
  a := ![-4, 2, -12, -20, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1742, 1468, -2452, 1480, -1656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 3, 1, -2]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![-1, 2, 3, 1, -2]] 
 ![![11, 0, 0, 0, 0], ![8, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![-1, 2, 3, 1, -2], ![-2, 2, -1, 0, 8], ![0, -10, -14, -9, 40], ![18, -49, -27, -9, 38], ![6, -19, -16, -7, 27]]]
  hmulB := by decide  
  f := ![![![5867, 271, -1743, -1172, 4586]], ![![4480, 207, -1331, -895, 3502]], ![![1152, 53, -342, -230, 900]], ![![3234, 150, -961, -646, 2528]], ![![4891, 226, -1453, -977, 3823]]]
  g := ![![![-1, 2, 3, 1, -2], ![-8, 2, -1, 0, 8], ![-18, -10, -14, -9, 40], ![16, -49, -27, -9, 38], ![-1, -19, -16, -7, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-1, 3, 1, 0, -2]] ![![3, -4, 3, 3, -8]]
  ![![-17, 28, -20, -24, 62]] where
 M := ![![![-17, 28, -20, -24, 62]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-17, 28, -20, -24, 62]] ![![-1, 2, 3, 1, -2]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![-99, 220, -143, -55, 220]]]
 hmul := by decide  
 g := ![![![![-9, 20, -13, -5, 20]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -14, 7, -7, 10]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![3, -14, 7, -7, 10]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![12, 2, 5, 1, 0], ![10, 0, 12, 0, 1]] where
  M :=![![![3, -14, 7, -7, 10], ![14, -14, 15, 32, -76], ![-64, 122, -86, -69, 196], ![138, -329, 213, 63, -262], ![6, -19, 12, -3, -1]]]
  hmulB := by decide  
  f := ![![![-55, 1, 19, 12, -46]], ![![-24, 3, 9, 5, -14]], ![![-10, -5, -4, -2, 20]], ![![-58, -3, 15, 10, -32]], ![![-52, -5, 10, 7, -15]]]
  g := ![![![-1, 0, -6, -7, 10], ![30, -6, 59, 32, -76], ![-92, 20, -161, -69, 196], ![154, -35, 234, 63, -262], ![4, -1, 3, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [6, 0, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 9], [0, 3], [0, 1]]
 g := ![![[], [], [1]], ![[], [], [1]], ![[], [], [1]]]
 h' := ![![[0, 9], [10], [7], [0, 1]], ![[0, 3], [10], [7], [0, 9]], ![[0, 1], [10], [7], [0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11], []]
 b := ![[], [0, 0, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [6, 0, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-474630, 1406907, 1278099, 539634, -1914949]
  a := ![-4, 8, -7, -3, 49]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![938404, 25203, 1658409, 539634, -1914949]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55, 1, 19, 12, -46]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-55, 1, 19, 12, -46]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![10, 8, 1, 0, 0], ![11, 11, 0, 1, 0], ![0, 7, 0, 0, 1]] where
  M :=![![![-55, 1, 19, 12, -46], ![-24, 3, 9, 5, -14], ![-10, -5, -4, -2, 20], ![4, -32, -31, -14, 64], ![-6, -15, -12, -5, 25]]]
  hmulB := by decide  
  f := ![![![3, -14, 7, -7, 10]], ![![14, -14, 15, 32, -76]], ![![6, -10, 8, 9, -24]], ![![25, -49, 35, 26, -76]], ![![8, -9, 9, 17, -41]]]
  g := ![![![-29, 3, 19, 12, -46], ![-13, -2, 9, 5, -14], ![4, -7, -4, -2, 20], ![36, -6, -31, -14, 64], ![13, -3, -12, -5, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[11, 10], [3], [10, 1]], ![[7, 3], [3], [7, 12]]]
 h' := ![![[10, 12], [2, 7], [2, 4], [0, 1]], ![[0, 1], [7, 6], [3, 9], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [5, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![169, -215, -160, -85, -290]
  a := ![2, -3, 6, 2, -19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![208, 310, -160, -85, -290]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![3, -14, 7, -7, 10]] ![![-55, 1, 19, 12, -46]]
  ![![13, 0, 0, 0, 0]] where
 M := ![![![13, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -4, -1, 1, 4]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![1, -4, -1, 1, 4]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![8, 6, 14, 1, 0], ![11, 6, 9, 0, 1]] where
  M :=![![![1, -4, -1, 1, 4], ![-2, -2, -19, -10, 38], ![20, -50, -8, -7, 10], ![14, 3, -21, 17, -76], ![10, -13, -6, 1, -23]]]
  hmulB := by decide  
  f := ![![![-1141, -53, 339, 228, -892]], ![![-456, -21, 135, 91, -356]], ![![-182, -9, 54, 36, -142]], ![![-852, -40, 253, 170, -666]], ![![-1007, -47, 299, 201, -787]]]
  g := ![![![-3, -2, -3, 1, 4], ![-20, -10, -13, -10, 38], ![-2, -4, 0, -7, 10], ![42, 21, 25, 17, -76], ![15, 7, 11, 1, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [4, 9, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 7, 10], [8, 9, 7], [0, 1]]
 g := ![![[2, 11, 1], [4, 13], [0, 1], []], ![[16, 4, 4, 7], [2, 4], [13, 13], [4, 15]], ![[15, 13, 16, 12], [14, 2], [5, 15], [7, 15]]]
 h' := ![![[9, 7, 10], [1, 14, 1], [0, 13, 8], [0, 0, 1], [0, 1]], ![[8, 9, 7], [5, 9, 13], [8, 8, 15], [14, 13, 9], [9, 7, 10]], ![[0, 1], [13, 11, 3], [1, 13, 11], [2, 4, 7], [8, 9, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 11], []]
 b := ![[], [15, 12, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [4, 9, 0, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![74890, -157192, 124677, 61145, -210690]
  a := ![-3, 3, -2, -10, 30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![111960, 43534, 68521, 61145, -210690]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1141, -53, 339, 228, -892]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-1141, -53, 339, 228, -892]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![3, 3, 1, 0, 0], ![8, 11, 0, 1, 0], ![9, 1, 0, 0, 1]] where
  M :=![![![-1141, -53, 339, 228, -892], ![-456, -21, 135, 91, -356], ![-182, -9, 54, 36, -142], ![-72, -4, 23, 16, -62], ![-194, -9, 58, 39, -153]]]
  hmulB := by decide  
  f := ![![![1, -4, -1, 1, 4]], ![![-2, -2, -19, -10, 38]], ![![1, -4, -4, -2, 8]], ![![0, -3, -14, -5, 22]], ![![1, -3, -2, 0, 3]]]
  g := ![![![238, -158, 339, 228, -892], ![95, -63, 135, 91, -356], ![38, -25, 54, 36, -142], ![17, -11, 23, 16, -62], ![41, -27, 58, 39, -153]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 3, 1] where
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
 g := ![![[3, 1], [16], [9], [1]], ![[0, 16], [16], [9], [1]]]
 h' := ![![[14, 16], [14, 16], [9, 13], [16, 14], [0, 1]], ![[0, 1], [0, 1], [4, 4], [8, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [13, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [1, 3, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![875, -559, 2726, 2097, -7154]
  a := ![-8, 5, -28, -20, 73]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2371, -1450, 2726, 2097, -7154]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![1, -4, -1, 1, 4]] ![![-1141, -53, 339, 228, -892]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [14, 15, 14, 11, 11, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 14, 1, 6, 12], [17, 2, 6, 8, 3], [14, 3, 7, 2, 9], [8, 18, 5, 3, 14], [0, 1]]
 g := ![![[9, 3, 11, 17, 9], [4, 18, 15, 8, 1], [], []], ![[13, 15, 18, 13, 15, 3, 8, 18], [3, 3, 17, 2, 5, 14, 13, 2], [12, 17, 5, 11], [13, 9, 4, 11]], ![[12, 5, 12, 6, 15, 1, 8, 8], [7, 15, 18, 3, 7, 13, 2, 12], [2, 9, 12, 6], [4, 11, 6, 9]], ![[18, 8, 10, 4, 6, 3, 11, 7], [14, 4, 6, 7, 14, 18, 16, 1], [10, 10, 11, 16], [4, 18, 0, 5]], ![[4, 14, 18, 6, 1, 16, 10, 12], [3, 1, 9, 12, 14, 18, 13, 8], [3, 11, 1, 4], [16, 18, 18, 6]]]
 h' := ![![[7, 14, 1, 6, 12], [1, 11, 15, 13, 3], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[17, 2, 6, 8, 3], [2, 1, 1, 4, 7], [3, 0, 8, 4, 15], [0, 8, 8, 9, 7], [7, 14, 1, 6, 12]], ![[14, 3, 7, 2, 9], [17, 14, 3, 5, 16], [16, 18, 8, 18, 2], [5, 6, 17, 15, 14], [17, 2, 6, 8, 3]], ![[8, 18, 5, 3, 14], [9, 1, 3, 4, 9], [4, 14, 9, 17, 6], [7, 0, 12, 17, 15], [14, 3, 7, 2, 9]], ![[0, 1], [11, 11, 16, 12, 3], [3, 6, 13, 18, 14], [11, 5, 0, 16, 2], [8, 18, 5, 3, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 1, 9, 2], [], [], []]
 b := ![[], [7, 16, 13, 7, 3], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [14, 15, 14, 11, 11, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-319489674, 893153140, 808307823, 340575703, -1106122810]
  a := ![-4, 4, -13, -7, 40]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-16815246, 47008060, 42542517, 17925037, -58216990]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![689, 45, -214, -139, 548]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![689, 45, -214, -139, 548]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![6, 6, 19, 6, 1]] where
  M :=![![![689, 45, -214, -139, 548], ![278, 2, -78, -67, 238], ![134, -27, -5, 19, -16], ![-38, 169, -128, -84, 262], ![112, 20, -44, -26, 103]]]
  hmulB := by decide  
  f := ![![![-5, 17, 16, 7, -28]], ![![-14, 30, 24, 9, -14]], ![![-18, 9, -5, -7, 92]], ![![14, -117, -126, -62, 334]], ![![-16, -13, -29, -19, 159]]]
  g := ![![![-113, -141, -462, -149, 548], ![-50, -62, -200, -65, 238], ![10, 3, 13, 5, -16], ![-70, -61, -222, -72, 262], ![-22, -26, -87, -28, 103]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 4 2 4 [1, 8, 17, 15, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18, 15, 11], [8, 17, 15, 1], [10, 10, 16, 11], [0, 1]]
 g := ![![[10, 21, 10, 12], [2, 18, 19, 1], [8, 1], []], ![[18, 20, 8, 15, 13, 17], [18, 15, 9, 5, 1, 15], [16, 6, 12, 10, 18, 22], [1, 10, 6]], ![[6, 22, 7, 8, 14, 9], [21, 10, 11, 3, 5, 9], [11, 3, 18, 20, 18, 18], [17, 15, 1]], ![[0, 22, 13, 14, 17, 14], [21, 16, 1, 11], [7, 1, 6, 3, 8, 7], [9, 9, 6]]]
 h' := ![![[13, 18, 15, 11], [21, 7, 15, 14], [15, 4, 17, 1], [0, 0, 1], [0, 1]], ![[8, 17, 15, 1], [5, 2, 20, 14], [0, 9, 8, 19], [7, 13, 13, 18], [13, 18, 15, 11]], ![[10, 10, 16, 11], [5, 0, 10, 3], [20, 22, 20, 3], [1, 6, 4, 8], [8, 17, 15, 1]], ![[0, 1], [0, 14, 1, 15], [3, 11, 1], [22, 4, 5, 20], [10, 10, 16, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [19, 22, 4], []]
 b := ![[], [], [15, 0, 1, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 4
  hpos := by decide
  P := [1, 8, 17, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-200733814, 442115358, -27637419, -52798665, 187188892]
  a := ![-11, 10, -59, -23, 106]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-57559442, -29609478, -155835929, -51127479, 187188892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 279841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -17, -16, -7, 28]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![5, -17, -16, -7, 28]] 
 ![![23, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![19, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![20, 0, 0, 0, 1]] where
  M :=![![![5, -17, -16, -7, 28], ![14, -30, -24, -9, 14], ![18, -9, 5, 7, -92], ![-14, 117, 126, 62, -334], ![-4, 50, 56, 28, -157]]]
  hmulB := by decide  
  f := ![![![-689, -45, 214, 139, -548]], ![![-72, -4, 22, 15, -58]], ![![-575, -36, 177, 114, -452]], ![![-238, -23, 80, 52, -202]], ![![-604, -40, 188, 122, -481]]]
  g := ![![![-7, -17, -16, -7, 28], ![14, -30, -24, -9, 14], ![75, -9, 5, 7, -92], ![154, 117, 126, 62, -334], ![76, 50, 56, 28, -157]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![689, 45, -214, -139, 548]] ![![5, -17, -16, -7, 28]]
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


lemma PB175I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB175I0 : PrimesBelowBoundCertificateInterval O 1 23 175 where
  m := 9
  g := ![5, 2, 5, 2, 3, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB175I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2, I2N2, I2N2]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
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
    · exact ![27, 9]
    · exact ![5, 5, 5, 5, 5]
    · exact ![2401, 7]
    · exact ![121, 121, 11]
    · exact ![2197, 169]
    · exact ![4913, 289]
    · exact ![2476099]
    · exact ![279841, 23]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
      exact NI2N2
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
      exact NI11N2
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
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I7N1, I11N0, I11N1, I11N2, I13N1, I23N1]
  Il := ![[I2N0, I2N1, I2N2, I2N2, I2N2], [I3N0, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N1], [I11N0, I11N1, I11N2], [I13N1], [], [], [I23N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
