
import IdealArithmetic.Examples.NF3_1_387059_1.RI3_1_387059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![2, -1, 4], ![8, -30, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, -1, 2], ![4, -30, 1]]]
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
  c := ![-746, 593, -1420]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-373, 593, -710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![2, 0, 4], ![8, -30, 3]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![5, -14, 2], ![-2, 0, -1]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, 0, 4], ![19, -30, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![0, 2, 0], ![2, 0, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 1, 0]], ![![1, 0, 2]]]]
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 1], [2, 0, 2], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 1]], ![[2, 0, 2, 2]]]
 h' := ![![[2, 2, 1], [0, 1]], ![[2, 0, 2], [2, 2, 1]], ![[0, 1], [2, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [0, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 1, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-40996119, -198906228, -209525028]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13665373, -66302076, -69841676]
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

instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 0, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 1, 1], [0, 3, 4], [0, 1]]
 g := ![![[4, 2, 1], []], ![[1, 3, 4, 4], [4, 1]], ![[0, 3, 0, 4], [1, 1]]]
 h' := ![![[2, 1, 1], [0, 0, 1], [0, 1]], ![[0, 3, 4], [1, 2, 3], [2, 1, 1]], ![[0, 1], [3, 3, 1], [0, 3, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 3], []]
 b := ![[], [4, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 0, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-280760, 75240, -617895]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56152, 15048, -123579]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![2, -1, 4], ![8, -30, 2]]]
  hmulB := by decide  
  f := ![![![-7, 3, -16], ![7, 28, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-4, 2, -9], ![2, 16, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-4, 0, 7]], ![![0, 1, 0], ![-2, -1, 4], ![0, -30, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![19, 3, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![19, 3, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 3, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![19, 3, 1], ![14, -14, 14], ![15, -103, -4]]]
  hmulB := by decide  
  f := ![![![-18, -3, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -3, 7]], ![![2, 0, 1], ![-8, -8, 14], ![5, -13, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 6], [0, 1]]
 g := ![![[5, 2], [3, 1]], ![[4, 5], [6, 6]]]
 h' := ![![[3, 6], [6, 4], [0, 1]], ![[0, 1], [4, 3], [3, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-416, -111, -1052]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![692, 435, -1052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![19, 3, 1]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![133, 21, 7]], ![![0, 7, 0], ![14, -14, 14]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![19, 3, 1]]], ![![![0, 1, 0]], ![![2, -2, 2]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![4, 1, 0]] 
 ![![11, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![4, 1, 0], ![2, 3, 4], ![8, -30, 6]]]
  hmulB := by decide  
  f := ![![![-23, -36, -48], ![0, 132, 0]], ![![-8, -12, -16], ![1, 44, 0]], ![![-7, -10, -13], ![2, 36, 0]]]
  g := ![![![1, 0, 0], ![-4, 11, 0], ![-3, 0, 11]], ![![0, 1, 0], ![-2, 3, 4], ![10, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-4, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-4, 1, 0]] 
 ![![11, 0, 0], ![7, 1, 0], ![1, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-4, 1, 0], ![2, -5, 4], ![8, -30, -2]]]
  hmulB := by decide  
  f := ![![![17, -40, 32], ![0, -88, 0]], ![![11, -25, 20], ![1, -55, 0]], ![![3, -4, 3], ![4, -8, 0]]]
  g := ![![![1, 0, 0], ![-7, 11, 0], ![-1, 0, 11]], ![![-1, 1, 0], ![3, -5, 4], ![20, -30, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-1, 1, 0]] 
 ![![11, 0, 0], ![10, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![2, -2, 4], ![8, -30, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![6, 3, 0]]]
  g := ![![![1, 0, 0], ![-10, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![2, -2, 4], ![28, -30, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![4, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![11, 0, 0], ![24, -3, 1]] where
 M := ![![![121, 0, 0], ![-44, 11, 0]], ![![44, 11, 0], ![-14, -1, 4]]]
 hmul := by decide  
 g := ![![![![-13, 3, -1], ![11, 0, 0]], ![![-4, 1, 0], ![0, 0, 0]]], ![![![-20, 4, -1], ![11, 0, 0]], ![![-10, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![24, -3, 1]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![264, -33, 11], ![-22, 0, -11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-1, 1, 0]]], ![![![24, -3, 1]], ![![-2, 0, -1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![4, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![4, 1, 0]] 
 ![![13, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![4, 1, 0], ![2, 3, 4], ![8, -30, 6]]]
  hmulB := by decide  
  f := ![![![53, 88, 120], ![26, -390, 0]], ![![14, 26, 36], ![14, -117, 0]], ![![16, 27, 37], ![9, -120, 0]]]
  g := ![![![1, 0, 0], ![-4, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-2, 3, 4], ![8, -30, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-3, 1, 0]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-3, 1, 0], ![2, -4, 4], ![8, -30, -1]]]
  hmulB := by decide  
  f := ![![![-86, 189, -192], ![39, 624, 0]], ![![-65, 142, -144], ![27, 468, 0]], ![![-26, 58, -59], ![14, 192, 0]]]
  g := ![![![1, 0, 0], ![-10, 13, 0], ![-4, 0, 13]], ![![-1, 1, 0], ![2, -4, 4], ![24, -30, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![2, -3, 4], ![8, -30, 0]]]
  hmulB := by decide  
  f := ![![![71, -107, 144], ![-13, -468, 0]], ![![59, -89, 120], ![-12, -390, 0]], ![![66, -99, 133], ![-9, -432, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-12, 0, 13]], ![![-1, 1, 0], ![-1, -3, 4], ![26, -30, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![4, 1, 0]] ![![13, 0, 0], ![-3, 1, 0]]
  ![![13, 0, 0], ![17, 0, 1]] where
 M := ![![![169, 0, 0], ![-39, 13, 0]], ![![52, 13, 0], ![-10, 0, 4]]]
 hmul := by decide  
 g := ![![![![-4, 0, -1], ![13, 0, 0]], ![![-3, 1, 0], ![0, 0, 0]]], ![![![-13, 1, -1], ![13, 0, 0]], ![![-6, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![17, 0, 1]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![221, 0, 13], ![-26, -13, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-2, 1, 0]]], ![![![17, 0, 1]], ![![-2, -1, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![14, -1, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![14, -1, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![14, 16, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![14, -1, 1], ![6, -15, -2], ![-17, 17, -17]]]
  hmulB := by decide  
  f := ![![![-13, 1, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -16, 17]], ![![0, -1, 1], ![2, 1, -2], ![13, 17, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [12, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16], [0, 1]]
 g := ![![[4, 16], [2], [9], [1]], ![[1, 1], [2], [9], [1]]]
 h' := ![![[3, 16], [14, 13], [2, 6], [5, 3], [0, 1]], ![[0, 1], [2, 4], [3, 11], [14, 14], [3, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [13, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [12, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16523, -21516, -51295]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41271, 47012, -51295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![2, 1, 0]] 
 ![![17, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![2, 1, 0], ![2, 1, 4], ![8, -30, 4]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![17, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -3], ![4, 13, 0]]]
  g := ![![![1, 0, 0], ![-2, 17, 0], ![0, 0, 17]], ![![0, 1, 0], ![0, 1, 4], ![4, -30, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![14, -1, 1]] ![![17, 0, 0], ![2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![34, 17, 0]], ![![238, -17, 17], ![34, -17, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![2, 1, 0]]], ![![![14, -1, 1]], ![![2, -1, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0]] 
 ![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [7, 3, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4, 7], [18, 14, 12], [0, 1]]
 g := ![![[0, 3, 7], [2, 12, 4], [18, 1], []], ![[11, 1], [3, 8, 9, 7], [5, 6], [7, 11]], ![[13, 8, 15, 8], [11, 8, 15, 12], [8, 16], [2, 11]]]
 h' := ![![[0, 4, 7], [5, 16, 11], [7, 15, 17], [0, 0, 1], [0, 1]], ![[18, 14, 12], [17, 12], [10, 9, 1], [8, 16, 14], [0, 4, 7]], ![[0, 1], [17, 10, 8], [18, 14, 1], [6, 3, 4], [18, 14, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 17], []]
 b := ![[], [0, 11, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [7, 3, 1, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-703, 3135, 114]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, 165, 6]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 6859 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [4, 7, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 11, 19], [20, 11, 4], [0, 1]]
 g := ![![[17, 20, 2], [4, 2, 3], [20, 21, 1], []], ![[20, 10, 18, 5], [12, 11, 21, 21], [16, 13, 17, 22], [18, 16]], ![[5, 4, 22, 2], [17, 15, 0, 12], [20, 8, 13, 1], [10, 16]]]
 h' := ![![[1, 11, 19], [7, 16, 18], [12, 6, 16], [0, 0, 1], [0, 1]], ![[20, 11, 4], [10, 4, 19], [9, 0, 14], [21, 16, 11], [1, 11, 19]], ![[0, 1], [22, 3, 9], [4, 17, 16], [15, 7, 11], [20, 11, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 8], []]
 b := ![[], [19, 5, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [4, 7, 2, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![285890, 238924, 808680]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12430, 10388, 35160]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [23, 1, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 9, 24], [3, 19, 5], [0, 1]]
 g := ![![[22, 9, 13], [17, 6], [11, 6, 13], [1]], ![[11, 11, 24, 13], [3, 6], [0, 0, 20, 4], [27, 0, 11, 20]], ![[3, 26, 22, 4], [], [15, 12, 27, 1], [1, 24, 1, 9]]]
 h' := ![![[16, 9, 24], [21, 9, 19], [8, 3, 8], [6, 28, 19], [0, 1]], ![[3, 19, 5], [25, 15, 26], [23, 16, 21], [24, 12, 18], [16, 9, 24]], ![[0, 1], [20, 5, 13], [22, 10], [4, 18, 21], [3, 19, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 13], []]
 b := ![[], [26, 9, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [23, 1, 10, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18357, -94250, -97005]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-633, -3250, -3345]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [14, 2, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 2, 11], [9, 28, 20], [0, 1]]
 g := ![![[6, 18, 20], [15, 14, 14], [15, 25, 14], [1]], ![[10, 16, 25, 11], [5, 10, 23, 11], [23, 18, 2, 17], [16, 13, 8, 29]], ![[5, 28, 18, 1], [3, 29, 30, 14], [8, 15, 25, 10], [9, 8, 1, 2]]]
 h' := ![![[9, 2, 11], [7, 9, 12], [7, 2, 18], [17, 29, 18], [0, 1]], ![[9, 28, 20], [12, 16, 1], [4, 1, 30], [9, 24, 17], [9, 2, 11]], ![[0, 1], [5, 6, 18], [9, 28, 14], [14, 9, 27], [9, 28, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 12], []]
 b := ![[], [15, 0, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [14, 2, 13, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2418, -1290220, -728376]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, -41620, -23496]
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



lemma PB177I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB177I0 : PrimesBelowBoundCertificateInterval O 1 31 177 where
  m := 11
  g := ![2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB177I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0]
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
    · exact ![4, 2]
    · exact ![27]
    · exact ![125]
    · exact ![7, 49]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![12167]
    · exact ![24389]
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
    · dsimp ; intro j
      fin_cases j
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
      exact NI13N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N0, I13N1, I13N2, I17N1]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0], [I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N0, I13N1, I13N2], [I17N1], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
