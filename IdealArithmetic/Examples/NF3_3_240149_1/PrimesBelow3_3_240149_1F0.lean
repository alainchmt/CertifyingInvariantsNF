
import IdealArithmetic.Examples.NF3_3_240149_1.RI3_3_240149_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-16, 1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-16, 1, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-16, 1, 1], ![-48, 8, 6], ![-54, 19, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![16, 0, -1], ![2, 0, 0]], ![![8, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -1, 2]], ![![-8, 0, 1], ![-24, 1, 6], ![-27, 5, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1562, -1671, 2935]
  a := ![2, -2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![781, -2303, 2935]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, 0, 5], ![-49, 24, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-2, 0, 5], ![-25, 24, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-16, 1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-32, 2, 2], ![-48, 8, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-16, 1, 1]], ![![-24, 4, 3]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![1, 0, 5], ![-49, 24, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -5], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -3], ![0, 2, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-3, 0, 5], ![-17, 24, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-15, 1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-15, 1, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 1, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-15, 1, 1], ![-48, 9, 6], ![-54, 19, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-14, 0, 0], ![-6, 1, 0]], ![![5, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -1, 3]], ![![-5, 0, 1], ![-16, 1, 6], ![-18, 3, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
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

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-310800, -353263, 1668317]
  a := ![-65, 1, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103600, -673860, 1668317]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-15, 1, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-45, 3, 3]], ![![0, 3, 0], ![-48, 9, 6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-15, 1, 1]]], ![![![0, 1, 0]], ![![-16, 3, 2]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![1, 1, 5], ![-49, 24, 2]]]
  hmulB := by decide  
  f := ![![![145, -75, -6], ![15, 0, 15]], ![![0, 0, 0], ![1, 0, 0]], ![![29, -15, -1], ![3, 0, 3]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-1, 0, 5]], ![![0, 1, 0], ![-1, 1, 5], ![-15, 24, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-15, 0, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-15, 0, 1]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-15, 0, 1], ![-49, 9, 1], ![-5, -5, 9]]]
  hmulB := by decide  
  f := ![![![20, -9, 1], ![-10, 5, 0]], ![![-2, -7, 2], ![-14, 4, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![0, 0, 5]], ![![-3, 0, 1], ![-17, 9, 1], ![3, -5, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![32, 1, -2]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![32, 1, -2]] 
 ![![5, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![32, 1, -2], ![99, -16, 3], ![-39, 34, -15]]]
  hmulB := by decide  
  f := ![![![28, -171, 81], ![135, -45, 0]], ![![-5, -126, 61], ![103, -33, 0]], ![![-20, -35, 18], ![31, -9, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![-1, 0, 5]], ![![6, 1, -2], ![32, -16, 3], ![-32, 34, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![-15, 0, 1]]
  ![![5, 0, 0], ![-17, 2, 1]] where
 M := ![![![25, 0, 0], ![-75, 0, 5]], ![![5, 5, 0], ![-64, 9, 2]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![2, -2, 0], ![5, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![11, -1, -1], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-17, 2, 1]] ![![5, 0, 0], ![32, 1, -2]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![160, 5, -10]], ![![-85, 10, 5], ![-385, -15, 25]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![32, 1, -2]]], ![![![-17, 2, 1]], ![![-77, -3, 5]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![1, 2, 5], ![-49, 24, 3]]]
  hmulB := by decide  
  f := ![![![-13, -31, -80], ![-7, 112, 0]], ![![-4, -8, -20], ![1, 28, 0]], ![![-11, -23, -57], ![1, 80, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-4, 2, 5], ![-16, 24, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0], ![-13, -2, 1]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![5, 4, 5]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![10, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-13, -2, 1]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![-91, -14, 7], ![-77, 7, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![2, 1, 0]]], ![![![-13, -2, 1]], ![![-11, 1, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-14, -4, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-14, -4, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![8, 7, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-14, -4, 1], ![-53, 10, -19], ![191, -101, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -7, 11]], ![![-2, -1, 1], ![9, 13, -19], ![13, -13, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[2, 4], [7, 3], [1]], ![[0, 7], [0, 8], [1]]]
 h' := ![![[5, 10], [1, 2], [8, 5], [0, 1]], ![[0, 1], [0, 9], [0, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [8, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [3, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![469, -1131, 2865]
  a := ![-2, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2041, -1926, 2865]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![5, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![1, -3, 5], ![-49, 24, -2]]]
  hmulB := by decide  
  f := ![![![-57, 206, -350], ![44, 770, 0]], ![![-40, 147, -250], ![34, 550, 0]], ![![-27, 94, -159], ![16, 350, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-5, 0, 11]], ![![-1, 1, 0], ![0, -3, 5], ![-21, 24, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-14, -4, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-154, -44, 11], ![-11, 22, -22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-3, 1, 0]]], ![![![-14, -4, 1]], ![![-1, 2, -2]]]]
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
 ![![13, 0, 0], ![4, 1, 0], ![10, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![1, 4, 5], ![-49, 24, 5]]]
  hmulB := by decide  
  f := ![![![-93, -436, -550], ![-52, 1430, 0]], ![![-29, -131, -165], ![-12, 429, 0]], ![![-70, -335, -423], ![-45, 1100, 0]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![-10, 0, 13]], ![![0, 1, 0], ![-5, 4, 5], ![-15, 24, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![4, 1, 0]]
  ![![13, 0, 0], ![-20, -1, 1]] where
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![52, 13, 0], ![17, 8, 5]]]
 hmul := by decide  
 g := ![![![![13, 0, 0], ![0, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![9, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-20, -1, 1]] ![![13, 0, 0], ![4, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![52, 13, 0]], ![![-260, -13, 13], ![-130, 0, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![4, 1, 0]]], ![![![-20, -1, 1]], ![![-10, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-16, -4, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-16, -4, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![1, 13, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-16, -4, 1], ![-53, 8, -19], ![191, -101, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -13, 17]], ![![-1, -1, 1], ![-2, 15, -19], ![11, -9, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [15, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 16], [0, 1]]
 g := ![![[15, 8], [8], [16], [1]], ![[0, 9], [8], [16], [1]]]
 h' := ![![[13, 16], [3, 5], [2, 5], [2, 13], [0, 1]], ![[0, 1], [0, 12], [16, 12], [1, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [14, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [15, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-602, 113, 605]
  a := ![-1, -1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-71, -456, 605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![2, 1, 0]] 
 ![![17, 0, 0], ![2, 1, 0], ![13, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![2, 1, 0], ![1, 2, 5], ![-49, 24, 3]]]
  hmulB := by decide  
  f := ![![![-44, -90, -225], ![0, 765, 0]], ![![-5, -10, -25], ![1, 85, 0]], ![![-34, -69, -172], ![3, 585, 0]]]
  g := ![![![1, 0, 0], ![-2, 17, 0], ![-13, 0, 17]], ![![0, 1, 0], ![-4, 2, 5], ![-8, 24, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-16, -4, 1]] ![![17, 0, 0], ![2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![34, 17, 0]], ![![-272, -68, 17], ![-85, 0, -17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![2, 1, 0]]], ![![![-16, -4, 1]], ![![-5, 0, -1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-14, -7, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-14, -7, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![5, 12, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-14, -7, 1], ![-56, 10, -34], ![338, -173, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -12, 19]], ![![-1, -1, 1], ![6, 22, -34], ![17, -11, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [10, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 18], [0, 1]]
 g := ![![[18, 16], [12, 4], [5], [1]], ![[7, 3], [14, 15], [5], [1]]]
 h' := ![![[10, 18], [13, 15], [12, 2], [9, 10], [0, 1]], ![[0, 1], [11, 4], [13, 17], [14, 9], [10, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [16, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [10, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16770, 8050, 4208]
  a := ![2, 19, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1990, -2234, 4208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-4, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-4, 1, 0]] 
 ![![19, 0, 0], ![15, 1, 0], ![16, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-4, 1, 0], ![1, -4, 5], ![-49, 24, -3]]]
  hmulB := by decide  
  f := ![![![-227, 1002, -1260], ![114, 4788, 0]], ![![-177, 787, -990], ![96, 3762, 0]], ![![-192, 844, -1061], ![92, 4032, 0]]]
  g := ![![![1, 0, 0], ![-15, 19, 0], ![-16, 0, 19]], ![![-1, 1, 0], ![-1, -4, 5], ![-19, 24, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-14, -7, 1]] ![![19, 0, 0], ![-4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-76, 19, 0]], ![![-266, -133, 19], ![0, 38, -38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-4, 1, 0]]], ![![![-14, -7, 1]], ![![0, 2, -2]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [13, 3, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10, 2], [22, 12, 21], [0, 1]]
 g := ![![[21, 11, 12], [2, 0, 13], [1, 2, 1], []], ![[20, 2, 11, 12], [15, 11, 10, 1], [15, 14, 19, 12], [2, 4]], ![[5, 3, 0, 15], [1, 1, 22, 5], [17, 22, 6, 7], [6, 4]]]
 h' := ![![[3, 10, 2], [20, 2, 14], [10, 17, 6], [0, 0, 1], [0, 1]], ![[22, 12, 21], [18, 2, 11], [5, 21, 14], [6, 2, 12], [3, 10, 2]], ![[0, 1], [21, 19, 21], [14, 8, 3], [15, 21, 10], [22, 12, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 11], []]
 b := ![[], [7, 6, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [13, 3, 21, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-918781, 574839, -412965]
  a := ![-2, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39947, 24993, -17955]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 12167 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀


def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![8, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![8, 1, 0]] 
 ![![29, 0, 0], ![8, 1, 0], ![28, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![8, 1, 0], ![1, 8, 5], ![-49, 24, 9]]]
  hmulB := by decide  
  f := ![![![-101, -879, -550], ![-29, 3190, 0]], ![![-30, -240, -150], ![1, 870, 0]], ![![-92, -848, -531], ![-48, 3080, 0]]]
  g := ![![![1, 0, 0], ![-8, 29, 0], ![-28, 0, 29]], ![![0, 1, 0], ![-7, 8, 5], ![-17, 24, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![12, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![12, 1, 0]] 
 ![![29, 0, 0], ![12, 1, 0], ![12, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![12, 1, 0], ![1, 12, 5], ![-49, 24, 13]]]
  hmulB := by decide  
  f := ![![![-77, -1222, -510], ![-58, 2958, 0]], ![![-30, -503, -210], ![-28, 1218, 0]], ![![-36, -506, -211], ![-14, 1224, 0]]]
  g := ![![![1, 0, 0], ![-12, 29, 0], ![-12, 0, 29]], ![![0, 1, 0], ![-7, 12, 5], ![-17, 24, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![8, 1, 0]] ![![29, 0, 0], ![8, 1, 0]]
  ![![29, 0, 0], ![-16, 9, 1]] where
 M := ![![![841, 0, 0], ![232, 29, 0]], ![![232, 29, 0], ![65, 16, 5]]]
 hmul := by decide  
 g := ![![![![29, 0, 0], ![0, 0, 0]], ![![8, 1, 0], ![0, 0, 0]]], ![![![8, 1, 0], ![0, 0, 0]], ![![5, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-16, 9, 1]] ![![29, 0, 0], ![12, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![348, 29, 0]], ![![-464, 261, 29], ![-232, 116, 58]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![12, 1, 0]]], ![![![-16, 9, 1]], ![![-8, 4, 2]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-13, 9, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-13, 9, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![18, 9, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-13, 9, 1], ![-40, 11, 46], ![-446, 211, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -9, 31]], ![![-1, 0, 1], ![-28, -13, 46], ![-26, 1, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [17, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 30], [0, 1]]
 g := ![![[6, 28], [5, 19], [18, 4], [22, 1]], ![[2, 3], [20, 12], [13, 27], [13, 30]]]
 h' := ![![[22, 30], [8, 20], [4, 22], [29, 2], [0, 1]], ![[0, 1], [14, 11], [23, 9], [11, 29], [22, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [16, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [17, 9, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1440, -7, 2555]
  a := ![2, 1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1530, -742, 2555]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-15, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-15, 1, 0]] 
 ![![31, 0, 0], ![16, 1, 0], ![11, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-15, 1, 0], ![1, -15, 5], ![-49, 24, -14]]]
  hmulB := by decide  
  f := ![![![-6, 329, -110], ![31, 682, 0]], ![![5, 164, -55], ![32, 341, 0]], ![![9, 116, -39], ![34, 242, 0]]]
  g := ![![![1, 0, 0], ![-16, 31, 0], ![-11, 0, 31]], ![![-1, 1, 0], ![6, -15, 5], ![-9, 24, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-13, 9, 1]] ![![31, 0, 0], ![-15, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-465, 31, 0]], ![![-403, 279, 31], ![155, -124, 31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-15, 1, 0]]], ![![![-13, 9, 1]], ![![5, -4, 1]]]]
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


lemma PB109I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB109I0 : PrimesBelowBoundCertificateInterval O 1 31 109 where
  m := 11
  g := ![2, 2, 3, 3, 2, 3, 2, 2, 1, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB109I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N0, I29N1]
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
    · exact ![4, 2]
    · exact ![3, 9]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![12167]
    · exact ![29, 29, 29]
    · exact ![961, 31]
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
      exact NI5N2
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
      exact NI13N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I5N2, I7N0, I11N1, I13N0, I17N1, I19N1, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1, I5N2], [I7N0, I7N0, I7N0], [I11N1], [I13N0, I13N0, I13N0], [I17N1], [I19N1], [], [I29N0, I29N0, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
