
import IdealArithmetic.Examples.NF3_1_125083_1.RI3_1_125083_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 1], ![70, -7, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 1], ![35, -7, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![5, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![5, 1, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![5, 1, 1], ![70, -2, 2], ![140, 56, 0]]]
  hmulB := by decide  
  f := ![![![-4, -1, -1], ![2, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 2]], ![![2, 0, 1], ![34, -2, 2], ![70, 28, 0]]]
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
  c := ![-209, 653, -65]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, 359, -65]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![5, 1, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![10, 2, 2]], ![![0, 2, 0], ![70, -2, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![5, 1, 1]]], ![![![0, 1, 0]], ![![35, -1, 1]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![4, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![4, 0, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![4, 0, 1], ![70, -3, 1], ![70, 63, -2]]]
  hmulB := by decide  
  f := ![![![-3, 0, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, 0, 3]], ![![1, 0, 1], ![23, -1, 1], ![24, 21, -2]]]
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
  c := ![4027, -51, 121]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1302, -17, 121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![0, -1, 1], ![70, -7, 0]]]
  hmulB := by decide  
  f := ![![![2, 1, -2], ![3, 6, 0]], ![![1, 1, -1], ![1, 3, 0]], ![![1, 1, -1], ![1, 4, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![0, -1, 1], ![28, -7, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![4, 0, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![12, 0, 3], ![66, -3, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![4, 0, 1]], ![![22, -1, 0]]]]
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
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 0, 1], ![70, -7, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 0, 1], ![14, -7, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, -1, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, -1, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 4, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, -1, 1], ![70, -5, 0], ![0, 70, -5]]]
  hmulB := by decide  
  f := ![![![-1, 1, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -4, 5]], ![![0, -1, 1], ![14, -1, 0], ![2, 18, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[1, 4], [1]], ![[4, 1], [1]]]
 h' := ![![[2, 4], [2, 2], [0, 1]], ![[0, 1], [1, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P5P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![217, 614, -74]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, 182, -74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![2, -1, 1]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![10, -5, 5]], ![![0, 5, 0], ![70, -5, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![2, -1, 1]]], ![![![0, 1, 0]], ![![14, -1, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0)

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![70, -7, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![10, -7, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![0, -1, 1], ![70, -7, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![21, 0, 0]], ![![2, -1, 0], ![8, 0, 0]], ![![2, -1, 0], ![8, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![-6, 0, 7]], ![![-1, 1, 0], ![0, -1, 1], ![16, -7, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![7, 0, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![0, 0, 1]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![7, 0, 1]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![49, 0, 7], ![63, 0, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![7, 0, 1]], ![![9, 0, 0]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N0, I7N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N0
    exact isPrimeI7N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1)
instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 10, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 3, 9], [7, 7, 2], [0, 1]]
 g := ![![[9, 8, 3], [2, 1, 1], []], ![[5, 9, 8, 9], [7, 4, 10, 1], [3, 4]], ![[9, 2, 8, 6], [1, 2, 3, 7], [10, 4]]]
 h' := ![![[5, 3, 9], [6, 5, 6], [0, 0, 1], [0, 1]], ![[7, 7, 2], [4, 10, 10], [1, 1, 7], [5, 3, 9]], ![[0, 1], [9, 7, 6], [2, 10, 3], [7, 7, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 5], []]
 b := ![[], [1, 8, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 10, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-902, 781, -363]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82, 71, -33]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 1331 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17, 16, -3]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-17, 16, -3]] 
 ![![13, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![-17, 16, -3], ![-210, 4, 13], ![910, -301, 17]]]
  hmulB := by decide  
  f := ![![![3981, 631, 220]], ![![3022, 479, 167]], ![![5501, 872, 304]]]
  g := ![![![-8, 16, -3], ![-21, 4, 13], ![205, -301, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-5, 1, 0]] 
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-5, 1, 0], ![0, -5, 1], ![70, -7, -4]]]
  hmulB := by decide  
  f := ![![![51, -10, 0], ![130, 0, 0]], ![![36, -7, 0], ![92, 0, 0]], ![![7, -1, 0], ![18, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 13, 0], ![-1, 0, 13]], ![![-1, 1, 0], ![3, -5, 1], ![10, -7, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![0, -2, 1], ![70, -7, -1]]]
  hmulB := by decide  
  f := ![![![19, -9, 0], ![117, 0, 0]], ![![17, -8, 0], ![105, 0, 0]], ![![15, -7, 0], ![93, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-9, 0, 13]], ![![-1, 1, 0], ![1, -2, 1], ![12, -7, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-17, 16, -3]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![13, 0, 0], ![9, 1, 1]] where
 M := ![![![-221, 208, -39], ![-125, -76, 28]]]
 hmul := by decide  
 g := ![![![![-17, 16, -3], ![0, 0, 0]], ![![-11, -6, 2], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![9, 1, 1]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![117, 13, 13], ![52, 0, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-2, 1, 0]]], ![![![9, 1, 1]], ![![4, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![3, -6, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![3, -6, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 11, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![3, -6, 1], ![70, -4, -5], ![-350, 105, -9]]]
  hmulB := by decide  
  f := ![![![-2, 6, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -11, 17]], ![![0, -1, 1], ![5, 3, -5], ![-19, 12, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 16], [0, 1]]
 g := ![![[5, 8], [9], [15], [1]], ![[0, 9], [9], [15], [1]]]
 h' := ![![[10, 16], [1, 5], [0, 3], [2, 10], [0, 1]], ![[0, 1], [0, 12], [13, 14], [0, 7], [10, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [13, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [15, 7, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2753, -32, 402]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![91, -262, 402]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![5, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![5, 1, 0]] 
 ![![17, 0, 0], ![5, 1, 0], ![9, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![5, 1, 0], ![0, 5, 1], ![70, -7, 6]]]
  hmulB := by decide  
  f := ![![![26, 5, 0], ![-85, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![12, 2, 0], ![-39, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 17, 0], ![-9, 0, 17]], ![![0, 1, 0], ![-2, 5, 1], ![3, -7, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![3, -6, 1]] ![![17, 0, 0], ![5, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![85, 17, 0]], ![![51, -102, 17], ![85, -34, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![5, 1, 0]]], ![![![3, -6, 1]], ![![5, -2, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 5, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-1, 5, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![18, 5, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-1, 5, 1], ![70, -8, 6], ![420, 28, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -5, 19]], ![![-1, 0, 1], ![-2, -2, 6], ![24, 2, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [1, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 18], [0, 1]]
 g := ![![[6, 1], [13, 6], [17], [1]], ![[0, 18], [15, 13], [17], [1]]]
 h' := ![![[13, 18], [6, 1], [3, 5], [18, 13], [0, 1]], ![[0, 1], [0, 18], [11, 14], [16, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [1, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-354, 117, -7]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 8, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-6, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-6, 1, 0]] 
 ![![19, 0, 0], ![13, 1, 0], ![2, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-6, 1, 0], ![0, -6, 1], ![70, -7, -5]]]
  hmulB := by decide  
  f := ![![![109, -18, 0], ![342, 0, 0]], ![![79, -13, 0], ![248, 0, 0]], ![![14, -2, 0], ![44, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 19, 0], ![-2, 0, 19]], ![![-1, 1, 0], ![4, -6, 1], ![9, -7, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-1, 5, 1]] ![![19, 0, 0], ![-6, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-114, 19, 0]], ![![-19, 95, 19], ![76, -38, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-6, 1, 0]]], ![![![-1, 5, 1]], ![![4, -2, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![5, -10, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![5, -10, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![5, 13, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![5, -10, 1], ![70, -2, -9], ![-630, 133, -11]]]
  hmulB := by decide  
  f := ![![![-4, 10, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -13, 23]], ![![0, -1, 1], ![5, 5, -9], ![-25, 12, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [21, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 22], [0, 1]]
 g := ![![[3, 9], [13, 4], [10, 13], [1]], ![[11, 14], [14, 19], [19, 10], [1]]]
 h' := ![![[6, 22], [3, 3], [20, 21], [2, 6], [0, 1]], ![[0, 1], [21, 20], [8, 2], [15, 17], [6, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [20, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [21, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![581, 241, 15]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 2, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![9, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![9, 1, 0]] 
 ![![23, 0, 0], ![9, 1, 0], ![11, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![9, 1, 0], ![0, 9, 1], ![70, -7, 10]]]
  hmulB := by decide  
  f := ![![![73, 8, 0], ![-184, 0, 0]], ![![27, 3, 0], ![-68, 0, 0]], ![![31, 3, 0], ![-78, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 23, 0], ![-11, 0, 23]], ![![0, 1, 0], ![-4, 9, 1], ![1, -7, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![5, -10, 1]] ![![23, 0, 0], ![9, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![207, 23, 0]], ![![115, -230, 23], ![115, -92, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![9, 1, 0]]], ![![![5, -10, 1]], ![![5, -4, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [20, 1, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 7, 28], [7, 21, 1], [0, 1]]
 g := ![![[12, 21, 9], [25, 23], [10, 1, 1], [1]], ![[7, 20], [9, 20], [17, 13, 2, 6], [28, 11, 22, 28]], ![[9, 20, 25, 9], [26, 4], [0, 2, 8, 6], [22, 5, 4, 1]]]
 h' := ![![[21, 7, 28], [2, 24, 26], [3, 22, 9], [9, 28, 28], [0, 1]], ![[7, 21, 1], [23, 26], [0, 0, 22], [1, 23, 9], [21, 7, 28]], ![[0, 1], [18, 8, 3], [4, 7, 27], [19, 7, 21], [7, 21, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [18, 21, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [20, 1, 1, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36714, 28362, -9802]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1266, 978, -338]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![10, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![10, 1, 0]] 
 ![![31, 0, 0], ![10, 1, 0], ![24, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![10, 1, 0], ![0, 10, 1], ![70, -7, 11]]]
  hmulB := by decide  
  f := ![![![121, 12, 0], ![-372, 0, 0]], ![![30, 3, 0], ![-92, 0, 0]], ![![84, 8, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 31, 0], ![-24, 0, 31]], ![![0, 1, 0], ![-4, 10, 1], ![-4, -7, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-8, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-8, 1, 0]] 
 ![![31, 0, 0], ![23, 1, 0], ![29, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-8, 1, 0], ![0, -8, 1], ![70, -7, -7]]]
  hmulB := by decide  
  f := ![![![49, -6, 0], ![186, 0, 0]], ![![41, -5, 0], ![156, 0, 0]], ![![51, -6, 0], ![194, 1, 0]]]
  g := ![![![1, 0, 0], ![-23, 31, 0], ![-29, 0, 31]], ![![-1, 1, 0], ![5, -8, 1], ![14, -7, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![31, 0, 0], ![28, 1, 0], ![22, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 1], ![70, -7, -2]]]
  hmulB := by decide  
  f := ![![![13, 2, 1]], ![![14, 2, 1]], ![![16, 3, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 1], ![10, -7, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![10, 1, 0]] ![![31, 0, 0], ![-8, 1, 0]]
  ![![13, 2, 1]] where
 M := ![![![961, 0, 0], ![-248, 31, 0]], ![![310, 31, 0], ![-80, 2, 1]]]
 hmul := by decide  
 g := ![![![![-93, 31, 0]], ![![24, -11, 1]]], ![![![-30, 7, 1]], ![![10, -3, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![13, 2, 1]] ![![-3, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![31, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB101I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB101I0 : PrimesBelowBoundCertificateInterval O 1 31 101 where
  m := 11
  g := ![2, 2, 2, 3, 1, 3, 2, 2, 2, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB101I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
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
    · exact ![9, 3]
    · exact ![5, 25]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
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
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I13N2, I17N1, I19N1, I23N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N1], [], [I13N0, I13N1, I13N2], [I17N1], [I19N1], [I23N1], [], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
