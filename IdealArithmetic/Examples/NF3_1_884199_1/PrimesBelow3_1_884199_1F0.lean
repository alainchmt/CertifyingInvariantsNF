
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 3 2 1 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 1]], ![[0, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 1, 1], [0, 0, 1]], ![[0, 1], [0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [1, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6517872, -2109602, -466394]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3258936, -1054801, -233197]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 8 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀


def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-38, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-38, -1, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-38, -1, 1], ![327, 19, -3], ![-436, 51, 20]]]
  hmulB := by decide  
  f := ![![![9, 21, 11], ![-51, -6, 0]], ![![5, -3, -2], ![9, 1, 0]], ![![3, 7, 4], ![-17, -2, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![-13, -1, 1], ![110, 19, -3], ![-152, 51, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![0, 0, 3], ![327, 58, -1]]]
  hmulB := by decide  
  f := ![![![606, 165, -2], ![-147, 0, -6]], ![![304, 82, -1], ![-71, 0, -3]], ![![404, 110, -1], ![-98, 0, -4]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-2, 0, 3], ![71, 58, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-38, -1, 1]] ![![3, 0, 0], ![-38, -1, 1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 M := ![![![9, 0, 0], ![-114, -3, 3]], ![![-114, -3, 3], ![681, 70, -15]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-38, -1, 1], ![0, 0, 0]]], ![![![-38, -1, 1], ![0, 0, 0]], ![![227, 21, -5], ![7, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![0, 3, 0], ![0, 0, 3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![0, 1, 0]], ![![0, 0, 1]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![0, 3, 3], ![327, 58, 2]]]
  hmulB := by decide  
  f := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]], ![![1, -1, -1], ![-1, 2, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-3, 0, 5]], ![![0, 1, 0], ![-3, 3, 3], ![41, 58, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![0, -1, 3], ![327, 58, -2]]]
  hmulB := by decide  
  f := ![![![1, 2, -6], ![0, 10, 0]], ![![1, 1, -3], ![1, 5, 0]], ![![1, 0, -1], ![2, 2, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-1, 0, 5]], ![![-1, 1, 0], ![0, -1, 3], ![31, 58, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![0, 0, 3], ![327, 58, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 2, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![0, 0, 3], ![19, 58, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0], ![-38, -3, 1]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![10, 5, 0], ![-4, 1, 3]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![36, 4, -1], ![5, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![22, 2, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-38, -3, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-190, -15, 5], ![365, 20, -10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![-38, -3, 1]], ![![73, 4, -2]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-37, -2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-37, -2, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![5, 5, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-37, -2, 1], ![327, 19, -6], ![-763, -7, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -5, 7]], ![![-6, -1, 1], ![51, 7, -6], ![-124, -16, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 6], [0, 1]]
 g := ![![[4, 2], [4, 1]], ![[5, 5], [1, 6]]]
 h' := ![![[4, 6], [4, 3], [0, 1]], ![[0, 1], [2, 4], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [3, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![549, 3307, 1458]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-963, -569, 1458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![0, 0, 3], ![327, 58, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -2], ![0, 5, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![0, 0, 3], ![-3, 58, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-37, -2, 1]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![-259, -14, 7], ![364, 21, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![-37, -2, 1]], ![![52, 3, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![3, 1, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![7, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![3, 1, 0], ![0, 4, 3], ![327, 58, 3]]]
  hmulB := by decide  
  f := ![![![7, 2, 0], ![-22, 0, 0]], ![![-3, -1, 0], ![12, 0, 0]], ![![5, 0, -1], ![-16, 4, 0]]]
  g := ![![![1, 0, 0], ![-3, 11, 0], ![-7, 0, 11]], ![![0, 1, 0], ![-3, 4, 3], ![12, 58, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![9, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![0, -2, 3], ![327, 58, -3]]]
  hmulB := by decide  
  f := ![![![19, -6, 0], ![66, 0, 0]], ![![16, -5, 0], ![56, 0, 0]], ![![15, -4, -1], ![52, 4, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-9, 0, 11]], ![![-1, 1, 0], ![-1, -2, 3], ![-10, 58, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-1, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-1, 1, 0]] 
 ![![11, 0, 0], ![10, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![0, 0, 3], ![327, 58, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 4, 0]]]
  g := ![![![1, 0, 0], ![-10, 11, 0], ![0, 0, 11]], ![![-1, 1, 0], ![0, 0, 3], ![-23, 58, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![3, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0], ![-36, -7, 1]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![33, 11, 0], ![-9, 1, 3]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![33, 8, -1], ![11, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![9, 2, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-36, -7, 1]] ![![11, 0, 0], ![-1, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-11, 11, 0]], ![![-396, -77, 11], ![363, 22, -22]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-1, 1, 0]]], ![![![-36, -7, 1]], ![![33, 2, -2]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [10, 7, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 4], [1, 12, 9], [0, 1]]
 g := ![![[1, 12, 10], [8, 3], [1]], ![[0, 8, 1, 3], [0, 10], [6, 5, 9, 12]], ![[3, 8, 11, 4], [9, 4], [6, 9, 8, 1]]]
 h' := ![![[3, 0, 4], [7, 2, 6], [3, 6, 4], [0, 1]], ![[1, 12, 9], [10, 5, 2], [6, 12, 7], [3, 0, 4]], ![[0, 1], [11, 6, 5], [6, 8, 2], [1, 12, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 12], []]
 b := ![[], [0, 7, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [10, 7, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-235092, -32591, -25012]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18084, -2507, -1924]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-136674, -35067, -6631]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-136674, -35067, -6631]] 
 ![![17, 0, 0], ![0, 17, 0], ![11, 13, 1]] where
  M :=![![![-136674, -35067, -6631], ![-2168337, -556339, -105201], ![-10744130, -2756665, -521272]]]
  hmulB := by decide  
  f := ![![![-1679, -23, 26]], ![![8502, -194, -69]], ![![4806, -75, -46]]]
  g := ![![![-3749, 3008, -6631], ![-59478, 47722, -105201], ![-294714, 236463, -521272]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 16], [0, 1]]
 g := ![![[9, 2], [13], [16], [1]], ![[0, 15], [13], [16], [1]]]
 h' := ![![[4, 16], [10, 6], [5, 9], [8, 4], [0, 1]], ![[0, 1], [0, 11], [7, 8], [7, 13], [4, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [10, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [9, 13, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3838, 6939, 2749]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1553, -1694, 2749]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1679, 23, -26]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![1679, 23, -26]] 
 ![![17, 0, 0], ![12, 1, 0], ![16, 0, 1]] where
  M :=![![![1679, 23, -26], ![-8502, 194, 69], ![10355, -1500, 171]]]
  hmulB := by decide  
  f := ![![![136674, 35067, 6631]], ![![224025, 57479, 10869]], ![![760642, 195161, 36904]]]
  g := ![![![107, 23, -26], ![-702, 194, 69], ![1507, -1500, 171]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-136674, -35067, -6631]] ![![1679, 23, -26]]
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


def P19P0 : CertificateIrreducibleZModOfList' 19 3 2 4 [9, 6, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 7], [3, 15, 12], [0, 1]]
 g := ![![[8, 13, 4], [8, 7, 6], [7, 1], []], ![[13, 10, 5, 7], [11, 9, 17, 6], [2, 16], [5, 11]], ![[12, 4, 0, 12], [12, 5, 14, 8], [9, 9], [0, 11]]]
 h' := ![![[4, 3, 7], [4, 1, 2], [13, 6, 5], [0, 0, 1], [0, 1]], ![[3, 15, 12], [7, 2, 18], [6, 6, 3], [9, 9, 15], [4, 3, 7]], ![[0, 1], [6, 16, 18], [0, 7, 11], [9, 10, 3], [3, 15, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 11], []]
 b := ![[], [10, 10, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 3
  hpos := by decide
  P := [9, 6, 12, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6472084, -2062944, -448875]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-340636, -108576, -23625]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [19, 9, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 6, 8], [13, 16, 15], [0, 1]]
 g := ![![[7, 19, 4], [22, 4, 18], [16, 18, 1], []], ![[2, 20, 22, 16], [12, 10, 18, 4], [18, 6, 17, 1], [6, 18]], ![[20, 19, 21, 20], [10, 10, 3, 15], [21, 22, 5, 11], [22, 18]]]
 h' := ![![[5, 6, 8], [19, 4, 2], [18, 20, 15], [0, 0, 1], [0, 1]], ![[13, 16, 15], [22, 19, 18], [2, 2, 9], [3, 9, 16], [5, 6, 8]], ![[0, 1], [10, 0, 3], [16, 1, 22], [4, 14, 6], [13, 16, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 6], []]
 b := ![[], [6, 3, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [19, 9, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3944415843, 1233302596, 266694361]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![171496341, 53621852, 11595407]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49, -13, 2]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![49, -13, 2]] 
 ![![29, 0, 0], ![0, 29, 0], ![10, 8, 1]] where
  M :=![![![49, -13, 2], ![654, 152, -39], ![-4469, -536, 165]]]
  hmulB := by decide  
  f := ![![![-144, -37, -7]], ![![-2289, -587, -111]], ![![-1072, -275, -52]]]
  g := ![![![1, -1, 2], ![36, 16, -39], ![-211, -64, 165]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 28], [0, 1]]
 g := ![![[19, 16], [6], [0, 16], [9, 1]], ![[18, 13], [6], [28, 13], [18, 28]]]
 h' := ![![[9, 28], [12, 25], [0, 8], [18, 25], [0, 1]], ![[0, 1], [5, 4], [14, 21], [11, 4], [9, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [19, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2951, 1717, 588]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-101, -103, 588]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![144, 37, 7]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![144, 37, 7]] 
 ![![29, 0, 0], ![5, 1, 0], ![19, 0, 1]] where
  M :=![![![144, 37, 7], ![2289, 587, 111], ![11336, 2909, 550]]]
  hmulB := by decide  
  f := ![![![-49, 13, -2]], ![![-31, -3, 1]], ![![122, 27, -7]]]
  g := ![![![-6, 37, 7], ![-95, 587, 111], ![-471, 2909, 550]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![49, -13, 2]] ![![144, 37, 7]]
  ![![29, 0, 0]] where
 M := ![![![-29, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![7, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![7, 1, 0]] 
 ![![31, 0, 0], ![7, 1, 0], ![2, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![7, 1, 0], ![0, 8, 3], ![327, 58, 7]]]
  hmulB := by decide  
  f := ![![![50, 7, 0], ![-217, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-4, -6, -2], ![18, 21, 0]]]
  g := ![![![1, 0, 0], ![-7, 31, 0], ![-2, 0, 31]], ![![0, 1, 0], ![-2, 8, 3], ![-3, 58, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![10, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![10, 1, 0]] 
 ![![31, 0, 0], ![10, 1, 0], ![15, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![10, 1, 0], ![0, 11, 3], ![327, 58, 10]]]
  hmulB := by decide  
  f := ![![![181, 18, 0], ![-558, 0, 0]], ![![50, 5, 0], ![-154, 0, 0]], ![![85, 1, -2], ![-262, 21, 0]]]
  g := ![![![1, 0, 0], ![-10, 31, 0], ![-15, 0, 31]], ![![0, 1, 0], ![-5, 11, 3], ![-13, 58, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1

def I31N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2355, -307, 32]] i)))

def SI31N2: IdealEqSpanCertificate' Table ![![2355, -307, 32]] 
 ![![31, 0, 0], ![13, 1, 0], ![22, 0, 1]] where
  M :=![![![2355, -307, 32], ![10464, 3904, -921], ![-103877, -14318, 4211]]]
  hmulB := by decide  
  f := ![![![3252866, 834601, 157819]], ![![3028841, 777122, 146950]], ![![10557268, 2708721, 512206]]]
  g := ![![![182, -307, 32], ![-646, 3904, -921], ![-335, -14318, 4211]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N2 : Nat.card (O ⧸ I31N2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N2)

lemma isPrimeI31N2 : Ideal.IsPrime I31N2 := prime_ideal_of_norm_prime hp31.out _ NI31N2
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![7, 1, 0]] ![![31, 0, 0], ![10, 1, 0]]
  ![![-3252866, -834601, -157819]] where
 M := ![![![961, 0, 0], ![310, 31, 0]], ![![217, 31, 0], ![70, 18, 3]]]
 hmul := by decide  
 g := ![![![![-73005, 9517, -992]], ![![-34014, -834, 601]]], ![![![-26949, -1755, 697]], ![![-1341, -188, 55]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-3252866, -834601, -157819]] ![![2355, -307, 32]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB267I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB267I0 : PrimesBelowBoundCertificateInterval O 1 31 267 where
  m := 11
  g := ![1, 3, 3, 2, 3, 1, 2, 1, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB267I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0, I3N0, I3N1]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
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
    · exact ![8]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![289, 17]
    · exact ![6859]
    · exact ![12167]
    · exact ![841, 29]
    · exact ![31, 31, 31]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
      exact NI11N2
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
      exact NI31N2
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I5N2, I7N0, I7N1, I11N0, I11N1, I11N2, I17N1, I29N1, I31N0, I31N1, I31N2]
  Il := ![[I2N0], [I3N0, I3N0, I3N1], [I5N0, I5N1, I5N2], [I7N0, I7N1], [I11N0, I11N1, I11N2], [], [I17N1], [], [], [I29N1], [I31N0, I31N1, I31N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
