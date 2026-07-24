
import IdealArithmetic.Examples.NF3_1_120204_1.RI3_1_120204_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 3], ![66, -6, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 3], ![33, -6, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![4, 0, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 0, 3]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-2, 0, 1], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![4, 0, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![8, 0, 2], ![66, -2, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![4, 0, 1]], ![![33, -1, 0]]]]
 hle2 := by decide  

def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![3, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![3, 0, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![3, 0, 1], ![66, -3, 0], ![0, 22, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 15, -2], ![0, 0, -2]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 0, 1], ![22, -3, 0], ![0, 22, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![3, 0, 1]] ![![3, 0, 0], ![3, 0, 1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 M := ![![![9, 0, 0], ![9, 0, 3]], ![![9, 0, 3], ![9, 22, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![3, 0, 1], ![0, 0, 0]]], ![![![3, 0, 1], ![0, 0, 0]], ![![3, 6, 0], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![3, 0, 1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![9, 0, 3]], ![![0, 3, 0], ![66, -3, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![3, 0, 1]]], ![![![0, 1, 0]], ![![22, -1, 0]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [1, 1, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 3], [0, 4, 2], [0, 1]]
 g := ![![[3, 2, 1], []], ![[2, 1, 3, 3], [3, 4]], ![[0, 3], [4, 4]]]
 h' := ![![[2, 0, 3], [0, 0, 1], [0, 1]], ![[0, 4, 2], [1, 3, 4], [2, 0, 3]], ![[0, 1], [1, 2], [0, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 3], []]
 b := ![[], [3, 0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [1, 1, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65, 5, -190]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 1, -38]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![1, 1, 0]] 
 ![![7, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![1, 1, 0], ![0, 1, 3], ![66, -6, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![2, -2, 0]]]
  g := ![![![1, 0, 0], ![-1, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-1, 1, 3], ![10, -6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![0, -2, 3], ![66, -6, -2]]]
  hmulB := by decide  
  f := ![![![13, -6, 0], ![42, 0, 0]], ![![11, -5, 0], ![36, 0, 0]], ![![3, 0, -2], ![10, 5, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-1, 0, 7]], ![![-1, 1, 0], ![1, -2, 3], ![14, -6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![7, 0, 0], ![5, 3, 1]] where
 M := ![![![49, 0, 0], ![7, 7, 0]], ![![7, 7, 0], ![1, 2, 3]]]
 hmul := by decide  
 g := ![![![![2, -3, -1], ![7, 0, 0]], ![![-4, -2, -1], ![7, 0, 0]]], ![![![-4, -2, -1], ![7, 0, 0]], ![![-2, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![5, 3, 1]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![35, 21, 7], ![56, -7, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-2, 1, 0]]], ![![![5, 3, 1]], ![![8, -1, 1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 0, 3], ![66, -6, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 4, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 0, 3], ![6, -6, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![2, 1, 0]] 
 ![![11, 0, 0], ![2, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![2, 1, 0], ![0, 2, 3], ![66, -6, 2]]]
  hmulB := by decide  
  f := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]], ![![2, 0, -1], ![-8, 4, 0]]]
  g := ![![![1, 0, 0], ![-2, 11, 0], ![-6, 0, 11]], ![![0, 1, 0], ![-2, 2, 3], ![6, -6, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-2, 1, 0]] 
 ![![11, 0, 0], ![9, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-2, 1, 0], ![0, -2, 3], ![66, -6, -2]]]
  hmulB := by decide  
  f := ![![![17, -8, 0], ![88, 0, 0]], ![![15, -7, 0], ![78, 0, 0]], ![![10, -4, -1], ![52, 4, 0]]]
  g := ![![![1, 0, 0], ![-9, 11, 0], ![-6, 0, 11]], ![![-1, 1, 0], ![0, -2, 3], ![12, -6, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![11, 0, 0], ![0, -3, 1]] where
 M := ![![![121, 0, 0], ![22, 11, 0]], ![![0, 11, 0], ![0, 2, 3]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, -3, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![0, -33, 11], ![66, 0, -11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-2, 1, 0]]], ![![![0, -3, 1]], ![![6, 0, -1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![9, 1, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![9, 1, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![9, 1, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![9, 1, 1], ![66, 3, 3], ![66, 16, 3]]]
  hmulB := by decide  
  f := ![![![-8, -1, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -1, 13]], ![![0, 0, 1], ![3, 0, 3], ![3, 1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 12], [0, 1]]
 g := ![![[11, 12], [12], [11, 1]], ![[0, 1], [12], [9, 12]]]
 h' := ![![[11, 12], [3, 8], [11, 5], [0, 1]], ![[0, 1], [0, 5], [1, 8], [11, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [3, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-781, 270, -42]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31, 24, -42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-3, 1, 0]] 
 ![![13, 0, 0], ![10, 1, 0], ![10, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-3, 1, 0], ![0, -3, 3], ![66, -6, -3]]]
  hmulB := by decide  
  f := ![![![34, -11, 0], ![143, 0, 0]], ![![28, -9, 0], ![118, 0, 0]], ![![28, -7, -2], ![118, 9, 0]]]
  g := ![![![1, 0, 0], ![-10, 13, 0], ![-10, 0, 13]], ![![-1, 1, 0], ![0, -3, 3], ![12, -6, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![9, 1, 1]] ![![13, 0, 0], ![-3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-39, 13, 0]], ![![117, 13, 13], ![39, 0, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-3, 1, 0]]], ![![![9, 1, 1]], ![![3, 0, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -5, -3]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-43, -5, -3]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 13, 1]] where
  M :=![![![-43, -5, -3], ![-198, -25, -15], ![-330, -36, -25]]]
  hmulB := by decide  
  f := ![![![-5, 1, 0]], ![![0, -5, 3]], ![![3, -4, 2]]]
  g := ![![![-2, 2, -3], ![-9, 10, -15], ![-15, 17, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [14, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16], [0, 1]]
 g := ![![[4, 1], [4], [8], [1]], ![[16, 16], [4], [8], [1]]]
 h' := ![![[12, 16], [13, 1], [16, 15], [3, 12], [0, 1]], ![[0, 1], [8, 16], [9, 2], [11, 5], [12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [4, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [14, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3658, -89, 120]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![194, -97, 120]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, -1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![5, -1, 0]] 
 ![![17, 0, 0], ![12, 1, 0], ![3, 0, 1]] where
  M :=![![![5, -1, 0], ![0, 5, -3], ![-66, 6, 5]]]
  hmulB := by decide  
  f := ![![![43, 5, 3]], ![![42, 5, 3]], ![![27, 3, 2]]]
  g := ![![![1, -1, 0], ![-3, 5, -3], ![-9, 6, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-43, -5, -3]] ![![5, -1, 0]]
  ![![17, 0, 0]] where
 M := ![![![-17, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [3, 4, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 18, 2], [2, 0, 17], [0, 1]]
 g := ![![[13, 15, 11], [6, 13, 9], [1, 1], []], ![[10, 0, 13, 15], [17, 2, 5, 12], [], [0, 4]], ![[11, 16, 15, 4], [11, 5, 18, 11], [0, 1], [4, 4]]]
 h' := ![![[18, 18, 2], [1, 3, 7], [16, 12, 16], [0, 0, 1], [0, 1]], ![[2, 0, 17], [5, 3, 6], [1, 18, 5], [1, 9], [18, 18, 2]], ![[0, 1], [8, 13, 6], [7, 8, 17], [11, 10, 18], [2, 0, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 10], []]
 b := ![[], [6, 2, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [3, 4, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-57988, 12445, -228]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3052, 655, -12]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![7, -10, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![7, -10, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![7, 13, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![7, -10, 1], ![66, 1, -30], ![-660, 82, 1]]]
  hmulB := by decide  
  f := ![![![-6, 10, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -13, 23]], ![![0, -1, 1], ![12, 17, -30], ![-29, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 17, 1] where
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
 g := ![![[10, 6], [18, 13], [7, 13], [1]], ![[0, 17], [4, 10], [16, 10], [1]]]
 h' := ![![[6, 22], [20, 12], [18, 6], [19, 6], [0, 1]], ![[0, 1], [0, 11], [8, 17], [9, 17], [6, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [21, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [4, 17, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![136, -7, -20]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 11, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![7, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![7, 1, 0]] 
 ![![23, 0, 0], ![7, 1, 0], ![22, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![7, 1, 0], ![0, 7, 3], ![66, -6, 7]]]
  hmulB := by decide  
  f := ![![![43, 6, 0], ![-138, 0, 0]], ![![7, 1, 0], ![-22, 0, 0]], ![![46, 4, -1], ![-148, 8, 0]]]
  g := ![![![1, 0, 0], ![-7, 23, 0], ![-22, 0, 23]], ![![0, 1, 0], ![-5, 7, 3], ![-2, -6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![7, -10, 1]] ![![23, 0, 0], ![7, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![161, 23, 0]], ![![161, -230, 23], ![115, -69, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![7, 1, 0]]], ![![![7, -10, 1]], ![![5, -3, -1]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![6, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![6, 1, 0]] 
 ![![29, 0, 0], ![6, 1, 0], ![17, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![6, 1, 0], ![0, 6, 3], ![66, -6, 6]]]
  hmulB := by decide  
  f := ![![![19, 3, 0], ![-87, 0, 0]], ![![-6, -1, 0], ![30, 0, 0]], ![![7, -1, -1], ![-31, 10, 0]]]
  g := ![![![1, 0, 0], ![-6, 29, 0], ![-17, 0, 29]], ![![0, 1, 0], ![-3, 6, 3], ![0, -6, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![7, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![7, 1, 0]] 
 ![![29, 0, 0], ![7, 1, 0], ![3, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![7, 1, 0], ![0, 7, 3], ![66, -6, 7]]]
  hmulB := by decide  
  f := ![![![106, 15, 0], ![-435, 0, 0]], ![![14, 2, 0], ![-57, 0, 0]], ![![10, -1, -1], ![-41, 10, 0]]]
  g := ![![![1, 0, 0], ![-7, 29, 0], ![-3, 0, 29]], ![![0, 1, 0], ![-2, 7, 3], ![3, -6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-13, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-13, 1, 0]] 
 ![![29, 0, 0], ![16, 1, 0], ![21, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-13, 1, 0], ![0, -13, 3], ![66, -6, -13]]]
  hmulB := by decide  
  f := ![![![196, -15, 0], ![435, 0, 0]], ![![118, -9, 0], ![262, 0, 0]], ![![150, -7, -1], ![333, 10, 0]]]
  g := ![![![1, 0, 0], ![-16, 29, 0], ![-21, 0, 29]], ![![-1, 1, 0], ![5, -13, 3], ![15, -6, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![6, 1, 0]] ![![29, 0, 0], ![7, 1, 0]]
  ![![29, 0, 0], ![14, 14, 1]] where
 M := ![![![841, 0, 0], ![203, 29, 0]], ![![174, 29, 0], ![42, 13, 3]]]
 hmul := by decide  
 g := ![![![![15, -14, -1], ![29, 0, 0]], ![![-7, -13, -1], ![29, 0, 0]]], ![![![-8, -13, -1], ![29, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![14, 14, 1]] ![![29, 0, 0], ![-13, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-377, 29, 0]], ![![406, 406, 29], ![-116, -174, 29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-13, 1, 0]]], ![![![14, 14, 1]], ![![-4, -6, 1]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![1, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![1, 1, 0]] 
 ![![31, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![1, 1, 0], ![0, 1, 3], ![66, -6, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![31, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![10, -10, 0]]]
  g := ![![![1, 0, 0], ![-1, 31, 0], ![-10, 0, 31]], ![![0, 1, 0], ![-1, 1, 3], ![2, -6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![3, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![3, 1, 0]] 
 ![![31, 0, 0], ![3, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![3, 1, 0], ![0, 3, 3], ![66, -6, 3]]]
  hmulB := by decide  
  f := ![![![52, 17, 0], ![-527, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![46, 13, -2], ![-466, 21, 0]]]
  g := ![![![1, 0, 0], ![-3, 31, 0], ![-28, 0, 31]], ![![0, 1, 0], ![-3, 3, 3], ![0, -6, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-4, 1, 0]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-4, 1, 0]] 
 ![![31, 0, 0], ![27, 1, 0], ![5, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-4, 1, 0], ![0, -4, 3], ![66, -6, -4]]]
  hmulB := by decide  
  f := ![![![41, -10, 0], ![310, 0, 0]], ![![37, -9, 0], ![280, 0, 0]], ![![11, 0, -2], ![84, 21, 0]]]
  g := ![![![1, 0, 0], ![-27, 31, 0], ![-5, 0, 31]], ![![-1, 1, 0], ![3, -4, 3], ![8, -6, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![1, 1, 0]] ![![31, 0, 0], ![3, 1, 0]]
  ![![31, 0, 0], ![1, -9, 1]] where
 M := ![![![961, 0, 0], ![93, 31, 0]], ![![31, 31, 0], ![3, 4, 3]]]
 hmul := by decide  
 g := ![![![![30, 9, -1], ![31, 0, 0]], ![![3, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![1, -9, 1]] ![![31, 0, 0], ![-4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-124, 31, 0]], ![![31, -279, 31], ![62, 31, -31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-4, 1, 0]]], ![![![1, -9, 1]], ![![2, 1, -1]]]]
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


lemma PB99I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB99I0 : PrimesBelowBoundCertificateInterval O 1 31 99 where
  m := 11
  g := ![3, 3, 1, 3, 3, 2, 2, 1, 2, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB99I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N2]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![529, 23]
    · exact ![29, 29, 29]
    · exact ![31, 31, 31]
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
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I7N0, I7N1, I11N0, I11N1, I11N2, I13N1, I17N1, I23N1, I29N0, I29N1, I29N2, I31N0, I31N1, I31N2]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N0], [], [I7N0, I7N0, I7N1], [I11N0, I11N1, I11N2], [I13N1], [I17N1], [], [I23N1], [I29N0, I29N1, I29N2], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
