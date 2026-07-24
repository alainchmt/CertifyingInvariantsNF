
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-2, 2, 5], ![232, 32, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, -2], ![-2, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 2, 5], ![116, 32, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![-2, 3, 5], ![232, 32, 0]]]
  hmulB := by decide  
  f := ![![![3, -3, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, -2, -2], ![1, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-5, 3, 5], ![100, 32, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![-20, 0, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-2, 2, 5]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![9, 1, 2], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-20, 0, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![-40, 0, 2], ![212, 12, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![-20, 0, 1]], ![![106, 6, 0]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-21, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-21, -1, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 2, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-21, -1, 1], ![234, 9, -6], ![-384, 8, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -2, 3]], ![![-7, -1, 1], ![78, 7, -6], ![-128, -6, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3150, 1963, 815]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1050, 111, 815]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![-2, 2, 5], ![232, 32, -1]]]
  hmulB := by decide  
  f := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, 2, 7], ![2, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-4, 2, 5], ![78, 32, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-21, -1, 1]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![-63, -3, 3], ![234, 9, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![0, 1, 0]]], ![![![-21, -1, 1]], ![![78, 3, -2]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-23, -1, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-23, -1, 1]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-23, -1, 1], ![234, 7, -6], ![-384, 8, 11]]]
  hmulB := by decide  
  f := ![![![102, -21, 29], ![-385, -40, 0]], ![![31, -1, 2], ![-34, -4, 0]], ![![52, -13, 18], ![-233, -24, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-3, 0, 5]], ![![-5, -1, 1], ![49, 7, -6], ![-85, 8, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-22, -1, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-22, -1, 1]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-22, -1, 1], ![234, 8, -6], ![-384, 8, 12]]]
  hmulB := by decide  
  f := ![![![43, -6, 12], ![-150, -15, 0]], ![![19, 0, 1], ![-17, -2, 0]], ![![30, -5, 10], ![-121, -12, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-4, 0, 5]], ![![-5, -1, 1], ![50, 8, -6], ![-88, 8, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![-2, 4, 5], ![232, 32, 1]]]
  hmulB := by decide  
  f := ![![![597, 46, 3], ![250, 0, -15]], ![![198, 15, 1], ![86, 0, -5]], ![![357, 27, 2], ![153, 0, -9]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-3, 0, 5]], ![![0, 1, 0], ![-5, 4, 5], ![33, 32, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-23, -1, 1]] ![![5, 0, 0], ![-22, -1, 1]]
  ![![5, 0, 0], ![1, 1, 0]] where
 M := ![![![25, 0, 0], ![-110, -5, 5]], ![![-115, -5, 5], ![-112, 23, -5]]]
 hmul := by decide  
 g := ![![![![4, -1, 0], ![5, 0, 0]], ![![-22, -1, 1], ![0, 0, 0]]], ![![![-23, -1, 1], ![0, 0, 0]], ![![-22, 5, -1], ![-2, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![5, 5, 0], ![0, 5, 5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![2, 1, 0]]], ![![![1, 1, 0]], ![![0, 1, 1]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-23, 1, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-23, 1, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 1, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-23, 1, 1], ![230, 11, 4], ![80, 72, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -1, 7]], ![![-4, 0, 1], ![30, 1, 4], ![5, 9, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6], [0, 1]]
 g := ![![[6, 1], [5, 1]], ![[4, 6], [3, 6]]]
 h' := ![![[5, 6], [3, 6], [0, 1]], ![[0, 1], [5, 1], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10740, 7288, 4628]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4840, 380, 4628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![-2, 5, 5], ![232, 32, 2]]]
  hmulB := by decide  
  f := ![![![58, -151, -150], ![7, 210, 0]], ![![21, -61, -60], ![8, 84, 0]], ![![41, -108, -107], ![6, 150, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-6, 5, 5], ![18, 32, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-23, 1, 1]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![-161, 7, 7], ![161, 14, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![3, 1, 0]]], ![![![-23, 1, 1]], ![![23, 2, 1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-21, -6, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-21, -6, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 5, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-21, -6, 1], ![244, -1, -31], ![-1544, -152, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -5, 11]], ![![-2, -1, 1], ![25, 14, -31], ![-142, -22, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 0, 1] where
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
 g := ![![[0, 9], [], [1]], ![[0, 2], [], [1]]]
 h' := ![![[0, 10], [0, 3], [6], [0, 1]], ![[0, 1], [0, 8], [6], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [0, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [5, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5863743, 3195046, 1287072]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![416061, -294574, 1287072]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-2, 1, 0]] 
 ![![11, 0, 0], ![9, 1, 0], ![4, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-2, 1, 0], ![-2, 0, 5], ![232, 32, -3]]]
  hmulB := by decide  
  f := ![![![-95, -2, 250], ![22, -550, 0]], ![![-75, -2, 200], ![23, -440, 0]], ![![-34, -1, 91], ![11, -200, 0]]]
  g := ![![![1, 0, 0], ![-9, 11, 0], ![-4, 0, 11]], ![![-1, 1, 0], ![-2, 0, 5], ![-4, 32, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-21, -6, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![-231, -66, 11], ![286, 11, -33]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-2, 1, 0]]], ![![![-21, -6, 1]], ![![26, 1, -3]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![4, 1, 0]] 
 ![![13, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![-2, 6, 5], ![232, 32, 3]]]
  hmulB := by decide  
  f := ![![![-3, -1, 0], ![13, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -4, -3], ![4, 8, 0]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![-2, 6, 5], ![8, 32, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![13, 0, 0], ![-18, 2, 1]] where
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![52, 13, 0], ![14, 10, 5]]]
 hmul := by decide  
 g := ![![![![13, 0, 0], ![0, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-18, 2, 1]] ![![13, 0, 0], ![4, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![-234, 26, 13], ![156, 26, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![4, 1, 0]]], ![![![-18, 2, 1]], ![![12, 2, 1]]]]
 hle2 := by decide  

def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![2, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![2, 1, 0]] 
 ![![17, 0, 0], ![2, 1, 0], ![15, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![2, 1, 0], ![-2, 4, 5], ![232, 32, 1]]]
  hmulB := by decide  
  f := ![![![179, -361, -450], ![17, 1530, 0]], ![![20, -40, -50], ![1, 170, 0]], ![![159, -318, -397], ![6, 1350, 0]]]
  g := ![![![1, 0, 0], ![-2, 17, 0], ![-15, 0, 17]], ![![0, 1, 0], ![-5, 4, 5], ![9, 32, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![3, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![3, 1, 0]] 
 ![![17, 0, 0], ![3, 1, 0], ![0, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![3, 1, 0], ![-2, 5, 5], ![232, 32, 2]]]
  hmulB := by decide  
  f := ![![![-2, -1, 0], ![17, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -3, -2], ![16, 7, 0]]]
  g := ![![![1, 0, 0], ![-3, 17, 0], ![0, 0, 17]], ![![0, 1, 0], ![-1, 5, 5], ![8, 32, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![5, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![-2, -4, 5], ![232, 32, -7]]]
  hmulB := by decide  
  f := ![![![313, 676, -840], ![-68, 2856, 0]], ![![205, 434, -540], ![-33, 1836, 0]], ![![97, 198, -247], ![-6, 840, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-5, 0, 17]], ![![-1, 1, 0], ![1, -4, 5], ![-5, 32, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![2, 1, 0]] ![![17, 0, 0], ![3, 1, 0]]
  ![![17, 0, 0], ![-23, -2, 1]] where
 M := ![![![289, 0, 0], ![51, 17, 0]], ![![34, 17, 0], ![4, 7, 5]]]
 hmul := by decide  
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![3, 1, 0], ![0, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-23, -2, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![-391, -34, 17], ![374, 17, -17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-6, 1, 0]]], ![![![-23, -2, 1]], ![![22, 1, -1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-15, -10, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-15, -10, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![4, 9, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-15, -10, 1], ![252, -3, -51], ![-2472, -280, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -9, 19]], ![![-1, -1, 1], ![24, 24, -51], ![-136, -28, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 18], [0, 1]]
 g := ![![[13, 4], [16, 6], [1], [1]], ![[9, 15], [10, 13], [1], [1]]]
 h' := ![![[18, 18], [9, 2], [6, 5], [16, 18], [0, 1]], ![[0, 1], [7, 17], [1, 14], [17, 1], [18, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [7, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [3, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5169, 8049, 4593]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1239, -1752, 4593]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-6, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-6, 1, 0]] 
 ![![19, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-6, 1, 0], ![-2, -4, 5], ![232, 32, -7]]]
  hmulB := by decide  
  f := ![![![-53, -121, 150], ![19, -570, 0]], ![![-33, -81, 100], ![20, -380, 0]], ![![-26, -64, 79], ![16, -300, 0]]]
  g := ![![![1, 0, 0], ![-13, 19, 0], ![-10, 0, 19]], ![![-1, 1, 0], ![0, -4, 5], ![-6, 32, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-15, -10, 1]] ![![19, 0, 0], ![-6, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-114, 19, 0]], ![![-285, -190, 19], ![342, 57, -57]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-6, 1, 0]]], ![![![-15, -10, 1]], ![![18, 3, -3]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-10, 4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-10, 4, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![13, 4, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-10, 4, 1], ![224, 30, 19], ![776, 168, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -4, 23]], ![![-1, 0, 1], ![-1, -2, 19], ![23, 4, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [15, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 22], [0, 1]]
 g := ![![[13, 8], [9, 12], [11, 6], [1]], ![[17, 15], [15, 11], [14, 17], [1]]]
 h' := ![![[12, 22], [3, 13], [19, 14], [8, 12], [0, 1]], ![[0, 1], [21, 10], [3, 9], [14, 11], [12, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [15, 11, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3183, 1933, 765]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-294, -49, 765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![4, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![4, 1, 0]] 
 ![![23, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![4, 1, 0], ![-2, 6, 5], ![232, 32, 3]]]
  hmulB := by decide  
  f := ![![![-107, 324, 270], ![0, -1242, 0]], ![![-18, 54, 45], ![1, -207, 0]], ![![-20, 56, 47], ![8, -216, 0]]]
  g := ![![![1, 0, 0], ![-4, 23, 0], ![-4, 0, 23]], ![![0, 1, 0], ![-2, 6, 5], ![4, 32, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-10, 4, 1]] ![![23, 0, 0], ![4, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![92, 23, 0]], ![![-230, 92, 23], ![184, 46, 23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![4, 1, 0]]], ![![![-10, 4, 1]], ![![8, 2, 1]]]]
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
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [11, 28, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 25, 16], [7, 3, 13], [0, 1]]
 g := ![![[18, 28, 28], [20, 5], [25, 12, 28], [1]], ![[12, 26, 9, 23], [1, 16], [13, 2, 12, 25], [17, 21, 28, 7]], ![[18, 0, 17, 28], [9, 20], [14, 16, 23, 4], [28, 25, 16, 22]]]
 h' := ![![[5, 25, 16], [5, 8, 17], [15, 14, 11], [18, 1, 12], [0, 1]], ![[7, 3, 13], [14, 14, 5], [24, 13, 25], [25, 8, 23], [5, 25, 16]], ![[0, 1], [22, 7, 7], [11, 2, 22], [6, 20, 23], [7, 3, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 27], []]
 b := ![[], [27, 20, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [11, 28, 17, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46542593, 11121413, 3336363]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1604917, 383497, 115047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 24389 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def PBC29 : ContainsPrimesAboveP 29 ![I29N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![29, 0, 0]]) timesTableT_eq_Table B_one_repr 29 (by decide) 𝕀

instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![879063, 37471, -33485]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![879063, 37471, -33485]] 
 ![![31, 0, 0], ![0, 31, 0], ![7, 14, 1]] where
  M :=![![![879063, 37471, -33485], ![-7843462, -117515, 220840], ![13782992, -140328, -263413]]]
  hmulB := by decide  
  f := ![![![-1998226265, -469975213, -140003415]], ![![-31540841854, -7418285971, -2209872650]], ![![-17526229037, -4122102371, -1227954992]]]
  g := ![![![35918, 16331, -33485], ![-302882, -103525, 220840], ![504093, 114434, -263413]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [14, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 30], [0, 1]]
 g := ![![[17, 20], [18, 10], [1, 18], [10, 1]], ![[0, 11], [25, 21], [26, 13], [20, 30]]]
 h' := ![![[10, 30], [27, 19], [17, 14], [15, 24], [0, 1]], ![[0, 1], [0, 12], [2, 17], [7, 7], [10, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [27, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [14, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5932, 3047, 1885]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-617, -753, 1885]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1998226265, 469975213, 140003415]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![1998226265, 469975213, 140003415]] 
 ![![31, 0, 0], ![24, 1, 0], ![5, 0, 1]] where
  M :=![![![1998226265, 469975213, 140003415], ![31540841854, 7418285971, 2209872650], ![87753730336, 20639343416, 6148363747]]]
  hmulB := by decide  
  f := ![![![-879063, -37471, 33485]], ![![-427550, -25219, 18800]], ![![-586397, -1517, 13898]]]
  g := ![![![-321974062, 469975213, 140003415], ![-5082173700, 7418285971, 2209872650], ![-14139752593, 20639343416, 6148363747]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![879063, 37471, -33485]] ![![1998226265, 469975213, 140003415]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0)


lemma PB273I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB273I0 : PrimesBelowBoundCertificateInterval O 1 31 273 where
  m := 11
  g := ![3, 2, 3, 2, 2, 3, 3, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB273I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1]
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
    · exact PBC29
    · exact PBC31
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2]
    · exact ![9, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![961, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
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
      exact NI13N0
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I5N2, I7N0, I7N1, I11N0, I11N1, I13N0, I17N0, I17N1, I17N2, I19N1, I23N1, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1], [I13N0, I13N0, I13N0], [I17N0, I17N1, I17N2], [I19N1], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
