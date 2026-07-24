
import IdealArithmetic.Examples.NF3_1_977075_1.RI3_1_977075_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 1], ![-332, 73, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 1], ![-166, 73, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-49, 5, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-49, 5, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-49, 5, 1], ![-332, 24, 6], ![-1992, 106, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![25, -2, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 2]], ![![-25, 2, 1], ![-169, 9, 6], ![-1011, 38, 30]]]
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
  c := ![997, -3205, 655]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171, -1930, 655]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![-49, 5, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![-98, 10, 2]], ![![0, 2, 0], ![-332, 24, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![-49, 5, 1]]], ![![![0, 1, 0]], ![![-166, 12, 3]]]]
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
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 0, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 1], [2, 2, 2], [0, 1]]
 g := ![![[1]], ![[0, 1, 1, 1]], ![[2, 2, 2, 2]]]
 h' := ![![[2, 0, 1], [0, 1]], ![[2, 2, 2], [2, 0, 1]], ![[0, 1], [2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 2], []]
 b := ![[], [1, 1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 0, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-451491, 143115, -31563]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-150497, 47705, -10521]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 27 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![0, -2, 1], ![-332, 73, -1]]]
  hmulB := by decide  
  f := ![![![11, -5, 0], ![25, 0, 0]], ![![5, -2, 0], ![11, 0, 0]], ![![1, 2, -1], ![2, 6, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-1, 0, 5]], ![![-1, 1, 0], ![1, -2, 1], ![-110, 73, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0], ![-51, 6, 1]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 1]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![49, -5, -1], ![5, 0, 0]]], ![![![49, -5, -1], ![5, 0, 0]], ![![11, -2, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-51, 6, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-255, 30, 5], ![-230, 10, 5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-2, 1, 0]]], ![![![-51, 6, 1]], ![![-46, 2, 1]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-52, 7, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-52, 7, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-52, 7, 1], ![-332, 21, 8], ![-2656, 252, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![8, -1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, 0, 7]], ![![-8, 1, 1], ![-52, 3, 8], ![-396, 36, 29]]]
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
  c := ![-988, -2765, 649]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-512, -395, 649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![0, -1, 1], ![-332, 73, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![21, 0, 0]], ![![2, -1, 0], ![8, 0, 0]], ![![2, -1, 0], ![8, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![-6, 0, 7]], ![![-1, 1, 0], ![0, -1, 1], ![-110, 73, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-52, 7, 1]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![-364, 49, 7], ![-280, 14, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![-52, 7, 1]], ![![-40, 2, 1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-4, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-4, 1, 0]] 
 ![![11, 0, 0], ![7, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-4, 1, 0], ![0, -4, 1], ![-332, 73, -3]]]
  hmulB := by decide  
  f := ![![![21, -5, 0], ![55, 0, 0]], ![![17, -4, 0], ![45, 0, 0]], ![![10, -2, 0], ![26, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 11, 0], ![-6, 0, 11]], ![![-1, 1, 0], ![2, -4, 1], ![-75, 73, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-4, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![11, 0, 0], ![-50, 3, 1]] where
 M := ![![![121, 0, 0], ![-44, 11, 0]], ![![-44, 11, 0], ![16, -8, 1]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![46, -2, -1], ![11, 0, 0]]], ![![![46, -2, -1], ![11, 0, 0]], ![![6, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-50, 3, 1]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-44, 11, 0]], ![![-550, 33, 11], ![-132, 11, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-4, 1, 0]]], ![![![-50, 3, 1]], ![![-12, 1, 0]]]]
 hle2 := by decide  

def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-45, -2, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-45, -2, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![7, 11, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-45, -2, 1], ![-332, 28, -1], ![332, -405, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -11, 13]], ![![-4, -1, 1], ![-25, 3, -1], ![11, -54, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 5, 1] where
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
 g := ![![[1, 1], [10], [8, 1]], ![[9, 12], [10], [3, 12]]]
 h' := ![![[8, 12], [3, 1], [12, 7], [0, 1]], ![[0, 1], [11, 12], [3, 6], [8, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [12, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-991, -118, 72]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-115, -70, 72]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![1, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![1, 1, 0]] 
 ![![13, 0, 0], ![1, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![1, 1, 0], ![0, 1, 1], ![-332, 73, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![13, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![12, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 13, 0], ![-12, 0, 13]], ![![0, 1, 0], ![-1, 1, 1], ![-33, 73, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-45, -2, 1]] ![![13, 0, 0], ![1, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![13, 13, 0]], ![![-585, -26, 13], ![-377, 26, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![1, 1, 0]]], ![![![-45, -2, 1]], ![![-29, 2, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![4, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![4, 1, 0]] 
 ![![17, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![4, 1, 0], ![0, 4, 1], ![-332, 73, 5]]]
  hmulB := by decide  
  f := ![![![29, 7, 0], ![-119, 0, 0]], ![![4, 1, 0], ![-16, 0, 0]], ![![-3, -1, 0], ![13, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 17, 0], ![-1, 0, 17]], ![![0, 1, 0], ![-1, 4, 1], ![-37, 73, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![8, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![8, 1, 0]] 
 ![![17, 0, 0], ![8, 1, 0], ![4, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![8, 1, 0], ![0, 8, 1], ![-332, 73, 9]]]
  hmulB := by decide  
  f := ![![![25, 3, 0], ![-51, 0, 0]], ![![8, 1, 0], ![-16, 0, 0]], ![![4, 0, 0], ![-8, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 17, 0], ![-4, 0, 17]], ![![0, 1, 0], ![-4, 8, 1], ![-56, 73, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![4, 1, 0]] ![![17, 0, 0], ![4, 1, 0]]
  ![![17, 0, 0], ![-52, 8, 1]] where
 M := ![![![289, 0, 0], ![68, 17, 0]], ![![68, 17, 0], ![16, 8, 1]]]
 hmul := by decide  
 g := ![![![![17, 0, 0], ![0, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-52, 8, 1]] ![![17, 0, 0], ![8, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![136, 17, 0]], ![![-884, 136, 17], ![-748, 85, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![8, 1, 0]]], ![![![-52, 8, 1]], ![![-44, 5, 1]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-9, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-9, 1, 0]] 
 ![![19, 0, 0], ![10, 1, 0], ![14, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-9, 1, 0], ![0, -9, 1], ![-332, 73, -8]]]
  hmulB := by decide  
  f := ![![![172, -19, 0], ![361, 0, 0]], ![![100, -11, 0], ![210, 0, 0]], ![![140, -15, 0], ![294, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 19, 0], ![-14, 0, 19]], ![![-1, 1, 0], ![4, -9, 1], ![-50, 73, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-2, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-2, 1, 0]] 
 ![![19, 0, 0], ![17, 1, 0], ![15, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-2, 1, 0], ![0, -2, 1], ![-332, 73, -1]]]
  hmulB := by decide  
  f := ![![![25, -12, 0], ![228, 0, 0]], ![![23, -11, 0], ![210, 0, 0]], ![![21, -10, 0], ![192, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 19, 0], ![-15, 0, 19]], ![![-1, 1, 0], ![1, -2, 1], ![-82, 73, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-9, 1, 0]] ![![19, 0, 0], ![-9, 1, 0]]
  ![![19, 0, 0], ![-52, 1, 1]] where
 M := ![![![361, 0, 0], ![-171, 19, 0]], ![![-171, 19, 0], ![81, -18, 1]]]
 hmul := by decide  
 g := ![![![![19, 0, 0], ![0, 0, 0]], ![![43, 0, -1], ![19, 0, 0]]], ![![![43, 0, -1], ![19, 0, 0]], ![![7, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-52, 1, 1]] ![![19, 0, 0], ![-2, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-38, 19, 0]], ![![-988, 19, 19], ![-228, 19, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-2, 1, 0]]], ![![![-52, 1, 1]], ![![-12, 1, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-54, 6, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-54, 6, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![15, 6, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-54, 6, 1], ![-332, 19, 7], ![-2324, 179, 26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -6, 23]], ![![-3, 0, 1], ![-19, -1, 7], ![-118, 1, 26]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [5, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 22], [0, 1]]
 g := ![![[12, 2], [10, 6], [18, 12], [1]], ![[7, 21], [18, 17], [11, 11], [1]]]
 h' := ![![[9, 22], [19, 18], [2, 12], [18, 9], [0, 1]], ![[0, 1], [20, 5], [18, 11], [7, 14], [9, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [19, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [5, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12928, 2819, 489]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-881, -5, 489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-7, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-7, 1, 0]] 
 ![![23, 0, 0], ![16, 1, 0], ![20, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-7, 1, 0], ![0, -7, 1], ![-332, 73, -6]]]
  hmulB := by decide  
  f := ![![![99, -14, 0], ![322, 0, 0]], ![![78, -11, 0], ![254, 0, 0]], ![![94, -13, 0], ![306, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 23, 0], ![-20, 0, 23]], ![![-1, 1, 0], ![4, -7, 1], ![-60, 73, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-54, 6, 1]] ![![23, 0, 0], ![-7, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-161, 23, 0]], ![![-1242, 138, 23], ![46, -23, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-7, 1, 0]]], ![![![-54, 6, 1]], ![![2, -1, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [7, 16, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 14, 15], [4, 14, 14], [0, 1]]
 g := ![![[5, 15, 28], [4, 28], [21, 27, 4], [1]], ![[3, 18, 5, 12], [0, 28], [8, 7, 9, 10], [6, 6, 3, 11]], ![[9, 19, 12, 21], [], [10, 9, 10, 3], [28, 23, 18, 18]]]
 h' := ![![[23, 14, 15], [5, 20, 17], [27, 17, 12], [22, 13, 27], [0, 1]], ![[4, 14, 14], [7, 8, 16], [6, 17, 17], [3, 11, 22], [23, 14, 15]], ![[0, 1], [9, 1, 25], [26, 24], [13, 5, 9], [4, 14, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 9], []]
 b := ![[], [22, 17, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [7, 16, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-284200, 93409, -8613]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9800, 3221, -297]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![1, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![1, 1, 0]] 
 ![![31, 0, 0], ![1, 1, 0], ![30, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![1, 1, 0], ![0, 1, 1], ![-332, 73, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![31, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![30, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 31, 0], ![-30, 0, 31]], ![![0, 1, 0], ![-1, 1, 1], ![-15, 73, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![13, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![13, 1, 0]] 
 ![![31, 0, 0], ![13, 1, 0], ![17, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![13, 1, 0], ![0, 13, 1], ![-332, 73, 14]]]
  hmulB := by decide  
  f := ![![![105, 8, 0], ![-248, 0, 0]], ![![39, 3, 0], ![-92, 0, 0]], ![![45, 3, 0], ![-106, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 31, 0], ![-17, 0, 31]], ![![0, 1, 0], ![-6, 13, 1], ![-49, 73, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-15, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-15, 1, 0]] 
 ![![31, 0, 0], ![16, 1, 0], ![23, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-15, 1, 0], ![0, -15, 1], ![-332, 73, -14]]]
  hmulB := by decide  
  f := ![![![466, -31, 0], ![961, 0, 0]], ![![256, -17, 0], ![528, 0, 0]], ![![368, -24, 0], ![759, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 31, 0], ![-23, 0, 31]], ![![-1, 1, 0], ![7, -15, 1], ![-38, 73, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![1, 1, 0]] ![![31, 0, 0], ![13, 1, 0]]
  ![![31, 0, 0], ![-49, 14, 1]] where
 M := ![![![961, 0, 0], ![403, 31, 0]], ![![31, 31, 0], ![13, 14, 1]]]
 hmul := by decide  
 g := ![![![![31, 0, 0], ![0, 0, 0]], ![![13, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-49, 14, 1]] ![![31, 0, 0], ![-15, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-465, 31, 0]], ![![-1519, 434, 31], ![403, -186, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-15, 1, 0]]], ![![![-49, 14, 1]], ![![13, -6, 0]]]]
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


lemma PB280I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB280I0 : PrimesBelowBoundCertificateInterval O 1 31 280 where
  m := 11
  g := ![2, 1, 3, 2, 3, 2, 3, 3, 2, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB280I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N0, I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N0, I17N1]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
    · exact ![I31N0, I31N1, I31N2]
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
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![31, 31, 31]
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
    · dsimp ; intro j
      fin_cases j
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
      exact NI11N0
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N0
      exact NI17N1
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
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
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I11N0, I13N0, I13N1, I17N0, I17N1, I19N0, I19N1, I23N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N1], [I11N0, I11N0, I11N0], [I13N0, I13N1], [I17N0, I17N0, I17N1], [I19N0, I19N0, I19N1], [I23N1], [], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
