
import IdealArithmetic.Examples.NF5_1_2700000_1.RI5_1_2700000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, -2, -3, -13]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![0, 1, -2, -3, -13]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, 1, -2, -3, -13], ![6, 2, 0, 10, 29], ![-20, -15, 13, -18, -25], ![28, 30, -31, 11, -33], ![-2, -9, 12, 10, 54]]]
  hmulB := by decide  
  f := ![![![11, 17, -1, -5, -10]], ![![5, 13, 3, -1, -5]], ![![2, 5, 17, 12, 13]], ![![-13, -25, 20, 22, 33]], ![![3, 6, -7, -7, -10]]]
  g := ![![![0, 1, -2, -3, -13], ![3, 2, 0, 10, 29], ![-10, -15, 13, -18, -25], ![14, 30, -31, 11, -33], ![-1, -9, 12, 10, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 6, -7, -7, -10]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![3, 6, -7, -7, -10]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 6, -7, -7, -10], ![14, 28, -19, -22, -34], ![44, 90, -45, -58, -94], ![36, 75, -24, -38, -66], ![-14, -29, 11, 16, 27]]]
  hmulB := by decide  
  f := ![![![-12, 7, -1, -2, -4]], ![![2, -3, 1, -1, -2]], ![![2, 5, -4, 2, -2]], ![![-9, -4, 7, 0, 16]], ![![0, 1, -2, -3, -13]]]
  g := ![![![5, 6, -7, -7, -10], ![18, 28, -19, -22, -34], ![51, 90, -45, -58, -94], ![37, 75, -24, -38, -66], ![-15, -29, 11, 16, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, -2, -2, -3]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![1, 2, -2, -2, -3]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 2, -2, -2, -3], ![4, 8, -5, -6, -9], ![12, 25, -12, -16, -27], ![10, 20, -6, -9, -15], ![-4, -8, 3, 4, 7]]]
  hmulB := by decide  
  f := ![![![-34, 19, -4, -10, -27]], ![![-7, 4, -1, -2, -6]], ![![-23, 12, -2, -6, -15]], ![![-13, 7, -2, -5, -15]], ![![-15, 9, -2, -4, -11]]]
  g := ![![![3, 2, -2, -2, -3], ![8, 8, -5, -6, -9], ![21, 25, -12, -16, -27], ![10, 20, -6, -9, -15], ![-5, -8, 3, 4, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![0, 1, -2, -3, -13]] ![![3, 6, -7, -7, -10]]
  ![![0, 0, 0, 0, 1]] where
 M := ![![![0, 0, 0, 0, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![0, 0, 0, 0, 1]] ![![3, 6, -7, -7, -10]]
  ![![-14, -29, 11, 16, 27]] where
 M := ![![![-14, -29, 11, 16, 27]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![-14, -29, 11, 16, 27]] ![![1, 2, -2, -2, -3]]
  ![![54, 119, 26, -10, -45]] where
 M := ![![![54, 119, 26, -10, -45]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![54, 119, 26, -10, -45]] ![![1, 2, -2, -2, -3]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![922, 1870, -1090, -1328, -2100]]]
 hmul := by decide  
 g := ![![![![461, 935, -545, -664, -1050]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, 2]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-1, -1, 1, 0, 2]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 2, 0, 1, 0], ![2, 1, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 0, 2], ![0, 1, -2, -2, -10], ![4, 0, 1, 8, 26], ![-10, -5, 3, -13, -30], ![4, 4, -4, 2, -3]]]
  hmulB := by decide  
  f := ![![![-11, 3, -1, -2, -6]], ![![4, -7, 0, 2, 6]], ![![-5, 1, -2, -2, -4]], ![![1, -2, -2, -1, 0]], ![![-6, -1, 0, 0, -1]]]
  g := ![![![-2, -1, 1, 0, 2], ![8, 5, -2, -2, -10], ![-19, -14, 1, 8, 26], ![20, 17, 3, -13, -30], ![4, 1, -4, 2, -3]]]
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
  c := ![-3467, -6701, 551, 2333, 24]
  a := ![15, 37, -35, -39, -90]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2133, -3797, 551, 2333, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 2, 0, 4]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![-1, -2, 2, 0, 4]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![-1, -2, 2, 0, 4], ![0, 3, -4, -4, -20], ![8, 0, 3, 16, 52], ![-20, -10, 6, -25, -60], ![8, 8, -8, 4, -5]]]
  hmulB := by decide  
  f := ![![![13, 14, -6, -8, -12]], ![![14, 23, -8, -12, -20]], ![![22, 36, -9, -16, -28]], ![![4, 10, 2, -1, -4]], ![![6, 4, -4, -4, -5]]]
  g := ![![![-3, -2, 2, 0, 4], ![14, 3, -4, -4, -20], ![-34, 0, 3, 16, 52], ![36, -10, 6, -25, -60], ![6, 8, -8, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-1, -1, 1, 0, 2]] ![![-1, -2, 2, 0, 4]]
  ![![25, 15, -11, 28, 58]] where
 M := ![![![25, 15, -11, 28, 58]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![25, 15, -11, 28, 58]] ![![-1, -2, 2, 0, 4]]
  ![![-209, 179, -339, -704, -2742]] where
 M := ![![![-209, 179, -339, -704, -2742]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N2 : IdealMulLeCertificate' Table 
  ![![-209, 179, -339, -704, -2742]] ![![-1, -2, 2, 0, 4]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![-10359, -13941, 15561, 492, 33906]]]
 hmul := by decide  
 g := ![![![![-3453, -4647, 5187, 164, 11302]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 4, -1, -2, -5]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![-5, 4, -1, -2, -5]] 
 ![![5, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![-5, 4, -1, -2, -5], ![4, 0, 0, 0, 1], ![0, 5, -1, -2, -5], ![2, 0, 1, 1, 3], ![0, -1, 0, 0, 0]]]
  hmulB := by decide  
  f := ![![![-1, 0, 1, 0, 1]], ![![0, 0, 0, 0, -1]], ![![0, -1, 1, 2, 5]], ![![-2, -2, 1, -1, -3]], ![![0, 1, 0, 0, 0]]]
  g := ![![![3, 4, -1, -2, -5], ![0, 0, 0, 0, 1], ![4, 5, -1, -2, -5], ![-2, 0, 1, 1, 3], ![0, -1, 0, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![-5, 4, -1, -2, -5]] ![![-5, 4, -1, -2, -5]]
  ![![37, -20, 4, 10, 28]] where
 M := ![![![37, -20, 4, 10, 28]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![37, -20, 4, 10, 28]] ![![-5, 4, -1, -2, -5]]
  ![![-245, 140, -31, -72, -195]] where
 M := ![![![-245, 140, -31, -72, -195]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![-245, 140, -31, -72, -195]] ![![-5, 4, -1, -2, -5]]
  ![![1641, -940, 204, 480, 1304]] where
 M := ![![![1641, -940, 204, 480, 1304]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![1641, -940, 204, 480, 1304]] ![![-5, 4, -1, -2, -5]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-11005, 6280, -1365, -3210, -8725]]]
 hmul := by decide  
 g := ![![![![-2201, 1256, -273, -642, -1745]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [4, 5, 0, 1, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 5, 0, 6, 4], [0, 6, 2, 2, 1], [2, 6, 1, 4, 4], [5, 3, 4, 2, 5], [0, 1]]
 g := ![![[3, 2, 1], []], ![[4, 2, 4, 1, 5, 3, 4, 1], [0, 4, 1, 4, 4, 3, 3, 1]], ![[3, 6, 1, 0, 1, 6, 1, 2], [3, 1, 0, 6, 3, 5, 1, 1]], ![[6, 5, 4, 0, 4, 2, 2, 2], [6, 2, 4, 1, 3, 4, 5, 1]], ![[3, 5, 6, 6, 5, 6, 3, 3], [3, 6, 0, 4, 1, 6, 1, 6]]]
 h' := ![![[2, 5, 0, 6, 4], [0, 0, 0, 1], [0, 1]], ![[0, 6, 2, 2, 1], [1, 2, 0, 1, 4], [2, 5, 0, 6, 4]], ![[2, 6, 1, 4, 4], [2, 2, 2, 0, 4], [0, 6, 2, 2, 1]], ![[5, 3, 4, 2, 5], [5, 6, 6, 5, 2], [2, 6, 1, 4, 4]], ![[0, 1], [1, 4, 6, 0, 4], [5, 3, 4, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4, 1], [], [], []]
 b := ![[], [4, 5, 6, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [4, 5, 0, 1, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-684200624050664, -1323725179979594, -1802238279948925, -656599808319574, -3998609867885997]
  a := ![188, 438, -436, -500, -1125]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-97742946292952, -189103597139942, -257462611421275, -93799972617082, -571229981126571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 41, -12, -20, -35]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![19, 41, -12, -20, -35]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![7, 7, 6, 10, 1]] where
  M :=![![![19, 41, -12, -20, -35], ![40, 84, -16, -34, -65], ![68, 145, -3, -38, -83], ![4, 15, 38, 23, 21], ![-8, -19, -10, -2, 2]]]
  hmulB := by decide  
  f := ![![![-15, 9, -2, -4, -11]], ![![8, -6, 2, 2, 7]], ![![-4, 5, -3, -2, -11]], ![![4, -5, 4, 5, 21]], ![![-3, 0, 2, 2, 10]]]
  g := ![![![24, 26, 18, 30, -35], ![45, 49, 34, 56, -65], ![59, 66, 45, 72, -83], ![-13, -12, -8, -17, 21], ![-2, -3, -2, -2, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 4 2 3 [6, 7, 6, 10, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 10, 0, 9], [4, 5, 2, 4], [10, 6, 9, 9], [0, 1]]
 g := ![![[4, 7, 1, 3], [1, 1], []], ![[2, 6, 2, 4, 7, 4], [6, 6, 3, 4, 3, 5], [6, 4, 4]], ![[9, 6, 6, 9, 10, 5], [4, 1, 5, 10, 0, 3], [2, 10, 5]], ![[4, 0, 8, 4, 2, 5], [10, 0, 9, 3, 4, 3], [1, 1, 4]]]
 h' := ![![[9, 10, 0, 9], [5, 9, 9, 6], [0, 0, 1], [0, 1]], ![[4, 5, 2, 4], [6, 4, 3, 8], [1, 4, 1, 6], [9, 10, 0, 9]], ![[10, 6, 9, 9], [7, 3, 6, 2], [4, 10, 6, 3], [4, 5, 2, 4]], ![[0, 1], [3, 6, 4, 6], [6, 8, 3, 2], [10, 6, 9, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [6, 6, 8], []]
 b := ![[], [], [5, 3, 7, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 4
  hpos := by decide
  P := [6, 7, 6, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![62515492, 134995053, -66540428, -75437168, -213785777]
  a := ![15, 36, -34, -39, -89]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![141728721, 148317772, 110561294, 187492782, -213785777]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 14641 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, 9, -2, -4, -11]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![-15, 9, -2, -4, -11]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-15, 9, -2, -4, -11], ![8, -6, 2, 2, 7], ![-4, 5, -3, -2, -11], ![4, -5, 4, 5, 21], ![0, -1, 0, -2, -6]]]
  hmulB := by decide  
  f := ![![![19, 41, -12, -20, -35]], ![![14, 30, -8, -14, -25]], ![![20, 43, -9, -18, -33]], ![![9, 20, -2, -7, -14]], ![![1, 2, -2, -2, -3]]]
  g := ![![![-2, 9, -2, -4, -11], ![1, -6, 2, 2, 7], ![1, 5, -3, -2, -11], ![-4, -5, 4, 5, 21], ![2, -1, 0, -2, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![19, 41, -12, -20, -35]] ![![-15, 9, -2, -4, -11]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![11, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [3, 0, 8, 7, 12, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 8, 3, 7], [11, 0, 9, 3, 2], [3, 5, 10, 9, 2], [10, 12, 4, 7, 9], [0, 1]]
 g := ![![[12, 9, 12, 8, 10], [1, 1], []], ![[1, 6, 4, 0, 10, 12, 5], [5, 1, 4, 9], [3, 12, 8, 4, 5]], ![[7, 11, 4, 5, 5, 2, 4, 5], [5, 11, 2, 4], [3, 11, 3, 4, 12, 7, 5, 8]], ![[5, 4, 1, 5, 2, 0, 11, 5], [6, 3, 10, 12], [12, 6, 3, 0, 8, 3, 12, 8]], ![[12, 6, 5, 2, 8, 3], [12, 1, 6, 3], [3, 1, 6, 4, 11, 12, 12, 1]]]
 h' := ![![[3, 8, 3, 7], [10, 10, 5, 11, 7], [0, 0, 0, 1], [0, 1]], ![[11, 0, 9, 3, 2], [10, 3, 10, 7, 6], [5, 11, 11, 3, 10], [3, 8, 3, 7]], ![[3, 5, 10, 9, 2], [1, 10, 1, 2, 3], [9, 6, 10, 6, 2], [11, 0, 9, 3, 2]], ![[10, 12, 4, 7, 9], [11, 4, 0, 3, 10], [4, 0, 0, 5, 5], [3, 5, 10, 9, 2]], ![[0, 1], [12, 12, 10, 3], [3, 9, 5, 11, 9], [10, 12, 4, 7, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 12, 12], [], [], []]
 b := ![[], [9, 6, 4, 1, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [3, 0, 8, 7, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2162505983807, 6577477259990, 12995985882568, 2446729740260, 24010264801354]
  a := ![-69, -163, 161, 182, 415]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![166346614139, 505959789230, 999691221736, 188209980020, 1846943446258]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [4, 12, 0, 9, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12, 4, 13, 8], [0, 7, 3, 3, 6], [5, 12, 9, 8, 9], [10, 2, 1, 10, 11], [0, 1]]
 g := ![![[0, 5, 0, 9, 2], [11, 12, 15, 1], [], []], ![[0, 8, 12, 4, 5, 16, 4, 8], [7, 8, 0, 9], [7, 5, 15, 1], [4, 7, 12, 13]], ![[3, 11, 3, 10, 8, 11, 3, 5], [12, 10, 5, 8], [3, 10, 4, 2], [7, 14, 15, 2]], ![[0, 3, 9, 7, 5, 4], [1, 14, 4, 15], [12, 8, 8, 4], [11, 9, 16, 13]], ![[11, 14, 11, 13, 11, 11], [0, 5, 9, 4], [14, 11, 7, 15], [0, 12, 12, 2]]]
 h' := ![![[0, 12, 4, 13, 8], [7, 7, 0, 6, 11], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[0, 7, 3, 3, 6], [4, 6, 1, 7, 16], [7, 16, 2, 3, 3], [1, 9, 12, 0, 16], [0, 12, 4, 13, 8]], ![[5, 12, 9, 8, 9], [1, 1, 8, 15, 7], [7, 12, 10, 14, 5], [6, 13, 8, 12, 6], [0, 7, 3, 3, 6]], ![[10, 2, 1, 10, 11], [11, 3, 0, 5], [7, 16, 7, 0, 10], [15, 3, 11, 4, 2], [5, 12, 9, 8, 9]], ![[0, 1], [1, 0, 8, 1], [16, 7, 15, 0, 15], [15, 9, 2, 1, 10], [10, 2, 1, 10, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 7, 5, 12], [], [], []]
 b := ![[], [8, 0, 1, 2, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [4, 12, 0, 9, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6164362044, 6220545140, -6971505486, 1959552396, -4294816080]
  a := ![14, 35, -31, -34, -85]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![362609532, 365914420, -410088558, 115267788, -252636240]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -22, 10, 14, 26]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![3, -22, 10, 14, 26]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![2, 7, 15, 1, 0], ![10, 10, 4, 0, 1]] where
  M :=![![![3, -22, 10, 14, 26], ![-28, -41, 18, 24, 38], ![-48, -110, 35, 56, 98], ![-32, -60, 8, 21, 42], ![12, 28, -6, -12, -23]]]
  hmulB := by decide  
  f := ![![![1, -2, 2, 2, 10]], ![![-4, 1, -2, -8, -26]], ![![16, 10, -7, 16, 34]], ![![10, 7, -5, 9, 18]], ![![2, 2, -2, 0, -3]]]
  g := ![![![-15, -20, -16, 14, 26], ![-24, -31, -26, 24, 38], ![-60, -78, -63, 56, 98], ![-26, -33, -25, 21, 42], ![14, 18, 14, -12, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [10, 1, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 2, 8], [10, 16, 11], [0, 1]]
 g := ![![[8, 17, 17], [6, 17, 9], [6, 1], []], ![[6, 15, 4, 10], [3, 6, 9, 10], [7, 9], [17, 7]], ![[17, 9, 12, 11], [13, 6, 10, 1], [18, 4], [14, 7]]]
 h' := ![![[15, 2, 8], [16, 4, 6], [16, 3, 16], [0, 0, 1], [0, 1]], ![[10, 16, 11], [7, 17, 14], [10, 11, 14], [17, 11, 16], [15, 2, 8]], ![[0, 1], [6, 17, 18], [14, 5, 8], [17, 8, 2], [10, 16, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 13], []]
 b := ![[], [9, 1, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [10, 1, 13, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36706, 87160, 200930, 136190, 201024]
  a := ![8, 20, -22, -30, -48]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-118206, -151390, -139264, 136190, 201024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 13, -6, -8, -13]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![7, 13, -6, -8, -13]] 
 ![![19, 0, 0, 0, 0], ![13, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![7, 13, -6, -8, -13], ![16, 34, -12, -18, -31], ![36, 75, -19, -34, -61], ![16, 35, 0, -9, -21], ![-8, -17, 2, 6, 12]]]
  hmulB := by decide  
  f := ![![![29, -7, -4, 8, 7]], ![![19, -5, -2, 6, 8]], ![![2, -1, -1, -2, -9]], ![![11, 0, -2, 7, 14]], ![![9, -4, 0, 2, 3]]]
  g := ![![![-1, 13, -6, -8, -13], ![-5, 34, -12, -18, -31], ![-16, 75, -19, -34, -61], ![-13, 35, 0, -9, -21], ![5, -17, 2, 6, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, -20, -4, 2, 8]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![-9, -20, -4, 2, 8]] 
 ![![19, 0, 0, 0, 0], ![15, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![14, 0, 0, 1, 0], ![13, 0, 0, 0, 1]] where
  M :=![![![-9, -20, -4, 2, 8], ![-4, -11, -24, -16, -16], ![32, 60, -83, -80, -112], ![64, 130, -74, -91, -144], ![-20, -40, 28, 32, 49]]]
  hmulB := by decide  
  f := ![![![197, -120, 32, 62, 184]], ![![149, -91, 24, 46, 136]], ![![37, -20, 5, 14, 40]], ![![138, -90, 26, 41, 128]], ![![135, -80, 20, 42, 121]]]
  g := ![![![9, -20, -4, 2, 8], ![35, -11, -24, -16, -16], ![103, 60, -83, -80, -112], ![78, 130, -74, -91, -144], ![-31, -40, 28, 32, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![3, -22, 10, 14, 26]] ![![7, 13, -6, -8, -13]]
  ![![45, 89, 108, 62, 51]] where
 M := ![![![45, 89, 108, 62, 51]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![45, 89, 108, 62, 51]] ![![-9, -20, -4, 2, 8]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![5643, 10621, -14440, -13984, -19589]]]
 hmul := by decide  
 g := ![![![![297, 559, -760, -736, -1031]]]]
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
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -20, 11, -56, -139]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-43, -20, 11, -56, -139]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![16, 14, 3, 1, 0], ![21, 18, 5, 0, 1]] where
  M :=![![![-43, -20, 11, -56, -139], ![112, 98, -94, 76, 23], ![-152, -245, 285, 70, 797], ![6, 270, -381, -407, -1971], ![156, 35, 14, 264, 792]]]
  hmulB := by decide  
  f := ![![![-61, 20, -13, -18, -43]], ![![36, -14, -22, -12, -1]], ![![24, 95, -83, -90, -139]], ![![-14, 23, -36, -35, -54]], ![![-23, 26, -46, -44, -68]]]
  g := ![![![164, 142, 38, -56, -139], ![-69, -60, -19, 76, 23], ![-783, -677, -170, 70, 797], ![2083, 1802, 465, -407, -1971], ![-900, -779, -206, 264, 792]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [13, 21, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 21, 9], [13, 1, 14], [0, 1]]
 g := ![![[0, 21, 8], [10, 8, 2], [10, 13, 1], []], ![[22, 5, 12, 2], [6, 2, 4, 13], [12, 22, 17, 9], [5, 12]], ![[8, 22, 1, 19], [8, 9, 16, 11], [20, 17, 8, 10], [0, 12]]]
 h' := ![![[0, 21, 9], [8, 3, 13], [8, 12, 5], [0, 0, 1], [0, 1]], ![[13, 1, 14], [14, 5, 17], [5, 5, 21], [4, 15, 1], [0, 21, 9]], ![[0, 1], [13, 15, 16], [20, 6, 20], [8, 8, 21], [13, 1, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 18], []]
 b := ![[], [6, 21, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [13, 21, 10, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![336569, 426776, -437982, 11152, -745896]
  a := ![15, 37, -20, -24, -77]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![687911, 595512, 141654, 11152, -745896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, -20, 13, 18, 43]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![61, -20, 13, 18, 43]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![15, 18, 1, 0, 0], ![7, 9, 0, 1, 0], ![10, 16, 0, 0, 1]] where
  M :=![![![61, -20, 13, 18, 43], ![-36, 14, 22, 12, 1], ![-24, -95, 83, 90, 139], ![-78, -120, 63, 79, 123], ![16, 45, -26, -32, -52]]]
  hmulB := by decide  
  f := ![![![43, 20, -11, 56, 139]], ![![-112, -98, 94, -76, -23]], ![![-53, -53, 54, -26, 38]], ![![-31, -44, 50, 5, 119]], ![![-66, -61, 60, -40, 10]]]
  g := ![![![-30, -48, 13, 18, 43], ![-20, -22, 22, 12, 1], ![-143, -201, 83, 90, 139], ![-122, -171, 63, 79, 123], ![50, 71, -26, -32, -52]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [8, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 22], [0, 1]]
 g := ![![[13, 3], [22, 4], [5, 6], [1]], ![[0, 20], [20, 19], [2, 17], [1]]]
 h' := ![![[11, 22], [8, 16], [6, 2], [15, 11], [0, 1]], ![[0, 1], [0, 7], [5, 21], [21, 12], [11, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [4, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [8, 12, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-943, -1780, 453, 594, 770]
  a := ![5, 11, -13, -16, -31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-852, -1200, 453, 594, 770]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-43, -20, 11, -56, -139]] ![![61, -20, 13, 18, 43]]
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


lemma PB103I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB103I0 : PrimesBelowBoundCertificateInterval O 1 23 103 where
  m := 9
  g := ![5, 4, 5, 1, 2, 1, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB103I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N1, I3N1]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
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
    · exact ![16807]
    · exact ![14641, 11]
    · exact ![371293]
    · exact ![1419857]
    · exact ![6859, 19, 19]
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I5N0, I11N1, I19N1, I19N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N1, I3N1], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [I11N1], [], [], [I19N1, I19N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
