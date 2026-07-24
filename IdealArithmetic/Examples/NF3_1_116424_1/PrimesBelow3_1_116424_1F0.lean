
import IdealArithmetic.Examples.NF3_1_116424_1.RI3_1_116424_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-2, 2, 5], ![54, -13, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, -2], ![-2, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 2, 5], ![27, -13, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![-2, 3, 5], ![54, -13, -1]]]
  hmulB := by decide  
  f := ![![![3, -3, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, -2, -2], ![1, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-5, 3, 5], ![34, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![8, 1, 1]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![0, 2, 0], ![-2, 3, 5]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-7, 0, -1], ![2, 0, 0]]], ![![![-8, 0, -1], ![2, 0, 0]], ![![3, 2, 3], ![-1, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![8, 1, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![16, 2, 2], ![60, -2, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![8, 1, 1]], ![![30, -1, 2]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![-2, 3, 5], ![54, -13, -1]]]
  hmulB := by decide  
  f := ![![![3, -3, -5], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![2, -2, -3], ![0, 2, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-5, 3, 5], ![23, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![7, 2, 1]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![-1, 4, 5]]]
 hmul := by decide  
 g := ![![![![-4, -2, -1], ![3, 0, 0]], ![![-6, -1, -1], ![3, 0, 0]]], ![![![-6, -1, -1], ![3, 0, 0]], ![![-5, 0, 1], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![7, 2, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![21, 6, 3], ![57, 0, 9]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![7, 2, 1]], ![![19, 0, 3]]]]
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
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![-2, 3, 5], ![54, -13, -1]]]
  hmulB := by decide  
  f := ![![![105, -30, -2], ![20, 0, -10]], ![![0, 0, 0], ![1, 0, 0]], ![![63, -18, -1], ![12, 0, -6]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-3, 0, 5]], ![![0, 1, 0], ![-4, 3, 5], ![14, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![8, 1, 1]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![8, 1, 1]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![8, 1, 1], ![52, -3, 3], ![16, 3, -5]]]
  hmulB := by decide  
  f := ![![![57, -31, -7], ![95, -20, 0]], ![![18, -9, -2], ![28, -6, 0]], ![![5, -7, -2], ![23, -4, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-1, 0, 5]], ![![1, 1, 1], ![11, -3, 3], ![3, 3, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![7, 1, 1]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![7, 1, 1]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![7, 1, 1], ![52, -4, 3], ![16, 3, -6]]]
  hmulB := by decide  
  f := ![![![161, -80, -17], ![220, -45, 0]], ![![63, -32, -7], ![89, -18, 0]], ![![-13, 5, 1], ![-13, 3, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![0, 0, 5]], ![![1, 1, 1], ![12, -4, 3], ![2, 3, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![8, 1, 1]]
  ![![5, 0, 0], ![10, 2, 1]] where
 M := ![![![25, 0, 0], ![40, 5, 5]], ![![5, 5, 0], ![60, -2, 4]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![-2, -1, 0], ![5, 0, 0]]], ![![![-9, -1, -1], ![5, 0, 0]], ![![-6, -4, -1], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![10, 2, 1]] ![![5, 0, 0], ![7, 1, 1]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![35, 5, 5]], ![![50, 10, 5], ![190, 5, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![7, 1, 1]]], ![![![10, 2, 1]], ![![38, 1, 2]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-2, 2, 5], ![54, -13, -2]]]
  hmulB := by decide  
  f := ![![![-7, 7, 20], ![7, -28, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, 1, 3], ![1, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-1, 0, 7]], ![![0, 1, 0], ![-1, 2, 5], ![8, -13, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![8, -1, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![-2, 2, 5]]]
 hmul := by decide  
 g := ![![![![-1, 1, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 1], ![-2, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![8, -1, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![56, -7, 7], ![56, -7, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![8, -1, 1]], ![![8, -1, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![1, 1, 0]] 
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, 1, 0], ![-2, 3, 5], ![54, -13, -1]]]
  hmulB := by decide  
  f := ![![![-18, 26, 45], ![11, -99, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-16, 24, 41], ![6, -90, 0]]]
  g := ![![![1, 0, 0], ![-1, 11, 0], ![-10, 0, 11]], ![![0, 1, 0], ![-5, 3, 5], ![7, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-2, 1, 0]] 
 ![![11, 0, 0], ![9, 1, 0], ![4, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-2, 1, 0], ![-2, 0, 5], ![54, -13, -4]]]
  hmulB := by decide  
  f := ![![![-95, -2, 250], ![22, -550, 0]], ![![-75, -2, 200], ![23, -440, 0]], ![![-34, -1, 91], ![11, -200, 0]]]
  g := ![![![1, 0, 0], ![-9, 11, 0], ![-4, 0, 11]], ![![-1, 1, 0], ![-2, 0, 5], ![17, -13, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![1, 1, 0]]
  ![![11, 0, 0], ![13, 3, 1]] where
 M := ![![![121, 0, 0], ![11, 11, 0]], ![![11, 11, 0], ![-1, 4, 5]]]
 hmul := by decide  
 g := ![![![![-2, -3, -1], ![11, 0, 0]], ![![-12, -2, -1], ![11, 0, 0]]], ![![![-12, -2, -1], ![11, 0, 0]], ![![-6, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![13, 3, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![143, 33, 11], ![22, 0, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-2, 1, 0]]], ![![![13, 3, 1]], ![![2, 0, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N0, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N0
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [4, 10, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 10, 5], [12, 2, 8], [0, 1]]
 g := ![![[4, 11, 1], [3, 3], [1]], ![[7, 0, 8, 11], [6, 10], [12, 0, 3, 8]], ![[10, 12, 3, 5], [11, 9], [8, 10, 0, 5]]]
 h' := ![![[10, 10, 5], [4, 12, 12], [9, 3, 9], [0, 1]], ![[12, 2, 8], [11, 7, 6], [3, 7, 7], [10, 10, 5]], ![[0, 1], [5, 7, 8], [6, 3, 10], [12, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 3], []]
 b := ![[], [10, 10, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [4, 10, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8944, 11752, -24180]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-688, 904, -1860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [6, 7, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 14, 7], [10, 2, 10], [0, 1]]
 g := ![![[4, 13, 1], [6, 4], [3, 1], []], ![[6, 6, 0, 12], [5, 4], [8, 4], [3, 15]], ![[4, 4, 6, 7], [5, 16], [4, 9], [0, 15]]]
 h' := ![![[10, 14, 7], [16, 5, 1], [16, 7, 2], [0, 0, 1], [0, 1]], ![[10, 2, 10], [12, 1, 3], [12, 11, 2], [14, 16, 2], [10, 14, 7]], ![[0, 1], [13, 11, 13], [14, 16, 13], [15, 1, 14], [10, 2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 14], []]
 b := ![[], [1, 16, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [6, 7, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1667836, -539716, 168436]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98108, -31748, 9908]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![0, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![0, 1, 0]] 
 ![![19, 0, 0], ![0, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![-2, 2, 5], ![54, -13, -2]]]
  hmulB := by decide  
  f := ![![![-19, 19, 50], ![19, -190, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-11, 11, 29], ![11, -110, 0]]]
  g := ![![![1, 0, 0], ![0, 19, 0], ![-11, 0, 19]], ![![0, 1, 0], ![-3, 2, 5], ![4, -13, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![16, 8, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![16, 8, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![16, 8, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![16, 8, 1], ![38, 19, 38], ![394, -88, -11]]]
  hmulB := by decide  
  f := ![![![-15, -8, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -8, 19]], ![![0, 0, 1], ![-30, -15, 38], ![30, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 18], [0, 1]]
 g := ![![[3, 6], [6, 11], [6], [1]], ![[11, 13], [8, 8], [6], [1]]]
 h' := ![![[14, 18], [9, 5], [16, 12], [11, 14], [0, 1]], ![[0, 1], [3, 14], [13, 7], [17, 5], [14, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [17, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1241274, -24185, -472335]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![463086, 197605, -472335]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 0]] ![![19, 0, 0], ![16, 8, 1]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![304, 152, 19]], ![![0, 19, 0], ![38, 19, 38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![16, 8, 1]]], ![![![0, 1, 0]], ![![2, 1, 2]]]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [16, 0, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 20, 18], [18, 2, 5], [0, 1]]
 g := ![![[21, 19, 2], [19, 13, 4], [16, 4, 1], []], ![[9, 16, 6, 8], [11, 14, 14, 3], [8, 0, 18, 3], [15, 2]], ![[16, 5, 15, 20], [20, 21, 18, 11], [2, 11, 10, 22], [5, 2]]]
 h' := ![![[9, 20, 18], [18, 8, 5], [20, 5, 2], [0, 0, 1], [0, 1]], ![[18, 2, 5], [8, 6, 16], [0, 20, 2], [2, 6, 2], [9, 20, 18]], ![[0, 1], [2, 9, 2], [0, 21, 19], [14, 17, 20], [18, 2, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 14], []]
 b := ![[], [17, 21, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [16, 0, 19, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1438466, 516534, -260958]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-62542, 22458, -11346]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-6, 13, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-6, 13, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![23, 13, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-6, 13, 1], ![28, 7, 63], ![664, -153, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -13, 29]], ![![-1, 0, 1], ![-49, -28, 63], ![57, 14, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [26, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 28], [0, 1]]
 g := ![![[23, 9], [22], [14, 6], [11, 1]], ![[6, 20], [22], [22, 23], [22, 28]]]
 h' := ![![[11, 28], [3, 26], [13, 14], [4, 8], [0, 1]], ![[0, 1], [28, 3], [22, 15], [5, 21], [11, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [16, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [26, 18, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![718, -38, -400]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![342, 178, -400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-5, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-5, 1, 0]] 
 ![![29, 0, 0], ![24, 1, 0], ![14, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-5, 1, 0], ![-2, -3, 5], ![54, -13, -7]]]
  hmulB := by decide  
  f := ![![![93, 138, -230], ![0, 1334, 0]], ![![77, 114, -190], ![1, 1102, 0]], ![![48, 66, -111], ![18, 644, 0]]]
  g := ![![![1, 0, 0], ![-24, 29, 0], ![-14, 0, 29]], ![![-1, 1, 0], ![0, -3, 5], ![16, -13, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-6, 13, 1]] ![![29, 0, 0], ![-5, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-145, 29, 0]], ![![-174, 377, 29], ![58, -58, 58]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-5, 1, 0]]], ![![![-6, 13, 1]], ![![2, -2, 2]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-5, -10, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-5, -10, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![26, 21, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-5, -10, 1], ![74, -38, -52], ![-578, 146, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -21, 31]], ![![-1, -1, 1], ![46, 34, -52], ![-22, 2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 30], [0, 1]]
 g := ![![[3, 18], [10, 18], [1, 5], [5, 1]], ![[0, 13], [7, 13], [26, 26], [10, 30]]]
 h' := ![![[5, 30], [27, 7], [12, 7], [29, 6], [0, 1]], ![[0, 1], [0, 24], [16, 24], [28, 25], [5, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [23, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16332, -2242, 1365]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-618, -997, 1365]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-10, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-10, 1, 0]] 
 ![![31, 0, 0], ![21, 1, 0], ![27, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-10, 1, 0], ![-2, -8, 5], ![54, -13, -12]]]
  hmulB := by decide  
  f := ![![![97, 384, -240], ![0, 1488, 0]], ![![65, 256, -160], ![1, 992, 0]], ![![89, 334, -209], ![14, 1296, 0]]]
  g := ![![![1, 0, 0], ![-21, 31, 0], ![-27, 0, 31]], ![![-1, 1, 0], ![1, -8, 5], ![21, -13, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-5, -10, 1]] ![![31, 0, 0], ![-10, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-310, 31, 0]], ![![-155, -310, 31], ![124, 62, -62]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-10, 1, 0]]], ![![![-5, -10, 1]], ![![4, 2, -2]]]]
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


lemma PB97I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB97I0 : PrimesBelowBoundCertificateInterval O 1 31 97 where
  m := 11
  g := ![3, 3, 3, 3, 3, 1, 1, 2, 1, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB97I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![19, 361]
    · exact ![12167]
    · exact ![841, 29]
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
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I5N2, I7N0, I11N0, I11N1, I19N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1, I5N2], [I7N0, I7N0, I7N0], [I11N0, I11N0, I11N1], [], [], [I19N0], [], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
