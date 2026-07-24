
import IdealArithmetic.Examples.NF3_1_456435_2.RI3_1_456435_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![2, 3, 8], ![155, 17, -3]]]
  hmulB := by decide  
  f := ![![![156, 13, -3], ![8, 0, -2]], ![![0, 0, 0], ![1, 0, 0]], ![![78, 6, -1], ![5, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-3, 3, 8], ![79, 17, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![2, 4, 8], ![155, 17, -2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 1]], ![![0, 1, 0], ![-1, 4, 4], ![69, 17, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P1 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [0, 1]]
 g := ![![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[0, 1], [1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], []]
 b := ![[], [1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N1 : CertifiedPrimeIdeal' SI2N1 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3477, 1687, 1508]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2582, 1687, 754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![0, 2, 0], ![2, 4, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 1, 0]], ![![1, 2, 4]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![2, 2, 8], ![155, 17, -4]]]
  hmulB := by decide  
  f := ![![![-7, -8, -32], ![0, 12, 0]], ![![-6, 3, -8], ![-14, 3, 0]], ![![-4, -6, -21], ![2, 8, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-6, 2, 8], ![43, 17, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0], ![-12, -1, 1]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![3, 1, 8]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![11, 2, -1], ![3, 0, 0]]], ![![![11, 2, -1], ![3, 0, 0]], ![![-3, 0, 3], ![-1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-12, -1, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-36, -3, 3], ![165, 3, -12]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![-12, -1, 1]], ![![55, 1, -4]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![2, 4, 8], ![155, 17, -2]]]
  hmulB := by decide  
  f := ![![![6, 11, 24], ![5, -15, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 2, 5], ![2, -3, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-1, 0, 5]], ![![0, 1, 0], ![-2, 4, 8], ![28, 17, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![2, 5, 8], ![155, 17, -1]]]
  hmulB := by decide  
  f := ![![![-5, -15, -24], ![0, 15, 0]], ![![-2, -5, -8], ![1, 5, 0]], ![![-4, -12, -19], ![0, 12, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-4, 0, 5]], ![![0, 1, 0], ![-8, 5, 8], ![25, 17, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0], ![-12, 2, 1]] where
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![5, 5, 0], ![4, 6, 8]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![8, 0, 1], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-12, 2, 1]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![-60, 10, 5], ![135, 15, 15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![2, 1, 0]]], ![![![-12, 2, 1]], ![![27, 3, 3]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![2, 3, 8], ![155, 17, -3]]]
  hmulB := by decide  
  f := ![![![-7, -12, -32], ![0, 28, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -4, -9], ![4, 8, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-2, 3, 8], ![23, 17, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![-12, 3, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![2, 3, 8]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 1], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-12, 3, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![-84, 21, 7], ![161, 14, 21]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![-12, 3, 1]], ![![23, 2, 3]]]]
 hle2 := by decide  

def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-7, 3, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-7, 3, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![4, 3, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-7, 3, 1], ![161, 19, 21], ![353, 64, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -3, 11]], ![![-1, 0, 1], ![7, -4, 21], ![31, 5, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [1, 0, 1] where
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

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4252252, 5783517, 3772968]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-985420, -503217, 3772968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![1, 1, 0]] 
 ![![11, 0, 0], ![1, 1, 0], ![8, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, 1, 0], ![2, 4, 8], ![155, 17, -2]]]
  hmulB := by decide  
  f := ![![![12, 23, 48], ![11, -66, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![9, 17, 35], ![5, -48, 0]]]
  g := ![![![1, 0, 0], ![-1, 11, 0], ![-8, 0, 11]], ![![0, 1, 0], ![-6, 4, 8], ![14, 17, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-7, 3, 1]] ![![11, 0, 0], ![1, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![11, 11, 0]], ![![-77, 33, 11], ![154, 22, 22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![1, 1, 0]]], ![![![-7, 3, 1]], ![![14, 2, 2]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-326, -13, 23]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-326, -13, 23]] 
 ![![13, 0, 0], ![0, 13, 0], ![9, 0, 1]] where
  M :=![![![-326, -13, 23], ![3539, 26, -173], ![-4591, 78, 150]]]
  hmulB := by decide  
  f := ![![![-1338, -288, -127]], ![![-20261, -4361, -1923]], ![![-3266, -703, -310]]]
  g := ![![![-41, -1, 23], ![392, 2, -173], ![-457, 6, 150]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 12], [0, 1]]
 g := ![![[12, 10], [3], [8, 1]], ![[1, 3], [3], [3, 12]]]
 h' := ![![[8, 12], [3, 6], [1, 4], [0, 1]], ![[0, 1], [12, 7], [7, 9], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [10, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2774, 4017, 3040]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2318, 309, 3040]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1338, 288, 127]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![1338, 288, 127]] 
 ![![13, 0, 0], ![3, 1, 0], ![11, 0, 1]] where
  M :=![![![1338, 288, 127], ![20261, 4361, 1923], ![30416, 6547, 2887]]]
  hmulB := by decide  
  f := ![![![326, 13, -23]], ![![-197, 1, 8]], ![![629, 5, -31]]]
  g := ![![![-71, 288, 127], ![-1075, 4361, 1923], ![-1614, 6547, 2887]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-326, -13, 23]] ![![1338, 288, 127]]
  ![![13, 0, 0]] where
 M := ![![![-13, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [4, 16, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 3, 13], [9, 13, 4], [0, 1]]
 g := ![![[2, 2, 2], [9, 4], [1, 1], []], ![[3, 11, 6, 8], [13, 16], [7, 16], [9, 16]], ![[0, 4, 14, 4], [4, 2], [15, 9], [1, 16]]]
 h' := ![![[9, 3, 13], [14, 0, 6], [13, 14, 2], [0, 0, 1], [0, 1]], ![[9, 13, 4], [12, 11, 10], [8, 6, 4], [11, 16, 13], [9, 3, 13]], ![[0, 1], [0, 6, 1], [4, 14, 11], [9, 1, 3], [9, 13, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 4], []]
 b := ![[], [8, 11, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [4, 16, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5972219, -1478405, -576232]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-351307, -86965, -33896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 4913 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-9, 7, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-9, 7, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![10, 7, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-9, 7, 1], ![169, 29, 53], ![973, 132, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -7, 19]], ![![-1, 0, 1], ![-19, -18, 53], ![57, 11, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [10, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 18], [0, 1]]
 g := ![![[8, 5], [1, 9], [16], [1]], ![[7, 14], [3, 10], [16], [1]]]
 h' := ![![[15, 18], [9, 10], [16, 16], [9, 15], [0, 1]], ![[0, 1], [7, 9], [9, 3], [6, 4], [15, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [16, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [10, 4, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![318271, 251797, 153353]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63961, -43246, 153353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![4, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![4, 1, 0]] 
 ![![19, 0, 0], ![4, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![4, 1, 0], ![2, 7, 8], ![155, 17, 1]]]
  hmulB := by decide  
  f := ![![![-121, -453, -520], ![-38, 1235, 0]], ![![-26, -91, -104], ![1, 247, 0]], ![![-69, -262, -301], ![-27, 715, 0]]]
  g := ![![![1, 0, 0], ![-4, 19, 0], ![-11, 0, 19]], ![![0, 1, 0], ![-6, 7, 8], ![4, 17, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-9, 7, 1]] ![![19, 0, 0], ![4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![76, 19, 0]], ![![-171, 133, 19], ![133, 57, 57]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![4, 1, 0]]], ![![![-9, 7, 1]], ![![7, 3, 3]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-9, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-9, 1, 0]] 
 ![![23, 0, 0], ![14, 1, 0], ![5, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-9, 1, 0], ![2, -6, 8], ![155, 17, -12]]]
  hmulB := by decide  
  f := ![![![-102, 387, -520], ![69, 1495, 0]], ![![-59, 232, -312], ![47, 897, 0]], ![![-21, 84, -113], ![18, 325, 0]]]
  g := ![![![1, 0, 0], ![-14, 23, 0], ![-5, 0, 23]], ![![-1, 1, 0], ![2, -6, 8], ![-1, 17, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-7, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-7, 1, 0]] 
 ![![23, 0, 0], ![16, 1, 0], ![14, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-7, 1, 0], ![2, -4, 8], ![155, 17, -10]]]
  hmulB := by decide  
  f := ![![![304, -671, 1352], ![-115, -3887, 0]], ![![214, -465, 936], ![-68, -2691, 0]], ![![189, -409, 823], ![-57, -2366, 0]]]
  g := ![![![1, 0, 0], ![-16, 23, 0], ![-14, 0, 23]], ![![-1, 1, 0], ![-2, -4, 8], ![1, 17, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-9, 1, 0]] ![![23, 0, 0], ![-7, 1, 0]]
  ![![23, 0, 0], ![-12, 7, 1]] where
 M := ![![![529, 0, 0], ![-161, 23, 0]], ![![-207, 23, 0], ![65, -13, 8]]]
 hmul := by decide  
 g := ![![![![23, 0, 0], ![0, 0, 0]], ![![5, -6, -1], ![23, 0, 0]]], ![![![3, -6, -1], ![23, 0, 0]], ![![7, -3, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-12, 7, 1]] ![![23, 0, 0], ![-7, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-161, 23, 0]], ![![-276, 161, 23], ![253, -23, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-7, 1, 0]]], ![![![-12, 7, 1]], ![![11, -1, 2]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![6, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![6, 1, 0]] 
 ![![29, 0, 0], ![6, 1, 0], ![8, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![6, 1, 0], ![2, 9, 8], ![155, 17, 3]]]
  hmulB := by decide  
  f := ![![![-9, -45, -40], ![0, 145, 0]], ![![-2, -9, -8], ![1, 29, 0]], ![![-6, -13, -11], ![17, 40, 0]]]
  g := ![![![1, 0, 0], ![-6, 29, 0], ![-8, 0, 29]], ![![0, 1, 0], ![-4, 9, 8], ![1, 17, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-748, -161, -71]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![-748, -161, -71]] 
 ![![29, 0, 0], ![24, 1, 0], ![28, 0, 1]] where
  M :=![![![-748, -161, -71], ![-11327, -2438, -1075], ![-17003, -3660, -1614]]]
  hmulB := by decide  
  f := ![![![-432, -6, 23]], ![![-235, -7, 15]], ![![-538, 1, 23]]]
  g := ![![![176, -161, -71], ![2665, -2438, -1075], ![4001, -3660, -1614]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-1, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-1, 1, 0]] 
 ![![29, 0, 0], ![28, 1, 0], ![15, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-1, 1, 0], ![2, 2, 8], ![155, 17, -4]]]
  hmulB := by decide  
  f := ![![![1233, 1232, 4928], ![0, -17864, 0]], ![![1189, 1188, 4752], ![1, -17226, 0]], ![![638, 637, 2549], ![7, -9240, 0]]]
  g := ![![![1, 0, 0], ![-28, 29, 0], ![-15, 0, 29]], ![![-1, 1, 0], ![-6, 2, 8], ![-9, 17, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![6, 1, 0]] ![![-748, -161, -71]]
  ![![29, 0, 0], ![-18, -14, 1]] where
 M := ![![![-21692, -4669, -2059]], ![![-15815, -3404, -1501]]]
 hmul := by decide  
 g := ![![![![-532, 7, -83], ![348, 0, 0]]], ![![![-379, 12, -61], ![268, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-18, -14, 1]] ![![29, 0, 0], ![-1, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-29, 29, 0]], ![![-522, -406, 29], ![145, -29, -116]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-1, 1, 0]]], ![![![-18, -14, 1]], ![![5, -1, -4]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [14, 21, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 0, 18], [6, 30, 13], [0, 1]]
 g := ![![[15, 9, 20], [17, 28, 25], [11, 8, 14], [1]], ![[6, 20, 14, 1], [11, 27, 25, 28], [26, 9, 28, 19], [16, 18, 21, 4]], ![[15, 25, 23, 29], [18, 12, 15, 23], [28, 9, 23, 3], [5, 21, 30, 27]]]
 h' := ![![[7, 0, 18], [10, 27, 12], [1, 8, 26], [17, 10, 13], [0, 1]], ![[6, 30, 13], [2, 20, 9], [28, 2, 25], [26, 1, 12], [7, 0, 18]], ![[0, 1], [2, 15, 10], [1, 21, 11], [22, 20, 6], [6, 30, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 8], []]
 b := ![[], [24, 21, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [14, 21, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12059, -10881, -3069]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-389, -351, -99]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 29791 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def PBC31 : ContainsPrimesAboveP 31 ![I31N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![31, 0, 0]]) timesTableT_eq_Table B_one_repr 31 (by decide) 𝕀



lemma PB192I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB192I0 : PrimesBelowBoundCertificateInterval O 1 31 192 where
  m := 11
  g := ![2, 3, 3, 3, 2, 2, 1, 2, 3, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB192I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1, I23N1]
    · exact ![I29N0, I29N1, I29N2]
    · exact ![I31N0]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![29, 29, 29]
    · exact ![29791]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I11N0, I11N1, I13N0, I13N1, I19N1, I23N0, I23N1, I29N0, I29N1, I29N2]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N1], [I7N0, I7N0, I7N0], [I11N0, I11N1], [I13N0, I13N1], [], [I19N1], [I23N0, I23N1, I23N1], [I29N0, I29N1, I29N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
