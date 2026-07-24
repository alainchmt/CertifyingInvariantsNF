
import IdealArithmetic.Examples.NF3_1_672300_4.RI3_1_672300_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![2, -1, 7], ![156, -9, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![1, 0, 4], ![-1, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, -1, 7], ![78, -9, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![6, 1, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, -1, 7]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-6, 0, -1], ![2, 0, 0]]], ![![![-6, 0, -1], ![2, 0, 0]], ![![-2, -1, 3], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![6, 1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![12, 2, 2], ![158, -4, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![6, 1, 1]], ![![79, -2, 4]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![2, -2, 7], ![156, -9, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![2, -2, 5], ![2, -2, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![2, -2, 7], ![58, -9, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0], ![6, 0, 1]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![3, -3, 7]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-1, 1, 0], ![0, 0, 0]]], ![![![-1, 1, 0], ![0, 0, 0]], ![![-1, -1, 2], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![6, 0, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![18, 0, 3], ![150, -3, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![6, 0, 1]], ![![50, -1, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![2, -1, 7], ![156, -9, 1]]]
  hmulB := by decide  
  f := ![![![-1, 4, -7], ![-15, 5, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, 0, -4], ![3, 3, 0]]]
  g := ![![![1, 0, 0], ![0, 5, 0], ![-1, 0, 5]], ![![0, 1, 0], ![-1, -1, 7], ![31, -9, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![5, 0, 0], ![6, 2, 1]] where
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![0, 5, 0], ![2, -1, 7]]]
 hmul := by decide  
 g := ![![![![-1, -2, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-2, -1, 1], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![6, 2, 1]] ![![5, 0, 0], ![0, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![30, 10, 5], ![160, -5, 15]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![0, 1, 0]]], ![![![6, 2, 1]], ![![32, -1, 3]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![2, 1, 7], ![156, -9, 3]]]
  hmulB := by decide  
  f := ![![![1159, -117, 24], ![315, 0, -56]], ![![288, -30, 6], ![85, 0, -14]], ![![330, -34, 7], ![94, 0, -16]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-2, 1, 7], ![24, -9, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![7, 0, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![7, 0, 1]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![7, 0, 1], ![156, -2, 1], ![42, 21, -2]]]
  hmulB := by decide  
  f := ![![![231, -6, -31], ![238, -21, 0]], ![![202, -5, -26], ![200, -18, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![0, 0, 7]], ![![1, 0, 1], ![24, -2, 1], ![-12, 21, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-6, -3, -1]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-6, -3, -1]] 
 ![![7, 0, 0], ![6, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-6, -3, -1], ![-162, 6, -22], ![-510, 6, 0]]]
  hmulB := by decide  
  f := ![![![805, -294, 94], ![-574, 56, 0]], ![![660, -242, 77], ![-473, 46, 0]], ![![230, -84, 27], ![-164, 16, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![-2, 0, 7]], ![![2, -3, -1], ![-22, 6, -22], ![-78, 6, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![7, 0, 1]]
  ![![7, 0, 0], ![3, -3, 1]] where
 M := ![![![49, 0, 0], ![49, 0, 7]], ![![14, 7, 0], ![170, -2, 3]]]
 hmul := by decide  
 g := ![![![![4, 3, -1], ![7, 0, 0]], ![![4, 3, 0], ![7, 0, 0]]], ![![![-1, 4, -1], ![7, 0, 0]], ![![20, 4, -1], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![3, -3, 1]] ![![7, 0, 0], ![-6, -3, -1]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-42, -21, -7]], ![![21, -21, 7], ![-42, -21, 63]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-6, -3, -1]]], ![![![3, -3, 1]], ![![-6, -3, 9]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [7, 5, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 2, 5], [2, 8, 6], [0, 1]]
 g := ![![[2, 5, 4], [7, 10, 1], []], ![[9, 7, 10, 1], [6, 6, 4, 1], [6, 3]], ![[9, 0, 3, 6], [3, 2, 2, 2], [5, 3]]]
 h' := ![![[8, 2, 5], [6, 5, 2], [0, 0, 1], [0, 1]], ![[2, 8, 6], [2, 5, 8], [0, 3, 8], [8, 2, 5]], ![[0, 1], [9, 1, 1], [2, 8, 2], [2, 8, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [3, 8, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [7, 5, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1004311, 124509, -47278]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91301, 11319, -4298]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 2, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 2, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![2, 2, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 2, 1], ![160, -9, 15], ![354, 3, -5]]]
  hmulB := by decide  
  f := ![![![-1, -2, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -2, 13]], ![![0, 0, 1], ![10, -3, 15], ![28, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 12], [0, 1]]
 g := ![![[6, 1], [3], [7, 1]], ![[0, 12], [3], [1, 12]]]
 h' := ![![[7, 12], [7, 12], [6, 9], [0, 1]], ![[0, 1], [0, 1], [4, 4], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [12, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14366, 8319, -2633]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-700, 1045, -2633]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![5, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![2, -3, 7], ![156, -9, -1]]]
  hmulB := by decide  
  f := ![![![71, -107, 252], ![-13, -468, 0]], ![![59, -89, 210], ![-12, -390, 0]], ![![27, -41, 97], ![-7, -180, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-5, 0, 13]], ![![-1, 1, 0], ![0, -3, 7], ![20, -9, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![2, 2, 1]] ![![13, 0, 0], ![-2, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-26, 13, 0]], ![![26, 26, 13], ![156, -13, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-2, 1, 0]]], ![![![2, 2, 1]], ![![12, -1, 1]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![4, 1, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![4, 1, 0]] 
 ![![17, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![4, 1, 0], ![2, 3, 7], ![156, -9, 5]]]
  hmulB := by decide  
  f := ![![![337, 539, 1274], ![119, -3094, 0]], ![![76, 124, 294], ![35, -714, 0]], ![![17, 31, 75], ![19, -182, 0]]]
  g := ![![![1, 0, 0], ![-4, 17, 0], ![-1, 0, 17]], ![![0, 1, 0], ![-1, 3, 7], ![11, -9, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 1, 1]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![19, 1, 1]] 
 ![![17, 0, 0], ![6, 1, 0], ![13, 0, 1]] where
  M :=![![![19, 1, 1], ![158, 9, 8], ![198, 12, 11]]]
  hmulB := by decide  
  f := ![![![3, 1, -1]], ![![-8, 1, 0]], ![![9, -1, 0]]]
  g := ![![![0, 1, 1], ![0, 9, 8], ![-1, 12, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![7, 1, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0], ![7, 1, 0]] 
 ![![17, 0, 0], ![7, 1, 0], ![4, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![7, 1, 0], ![2, 6, 7], ![156, -9, 8]]]
  hmulB := by decide  
  f := ![![![-108, -387, -455], ![-51, 1105, 0]], ![![-45, -155, -182], ![-16, 442, 0]], ![![-25, -91, -107], ![-13, 260, 0]]]
  g := ![![![1, 0, 0], ![-7, 17, 0], ![-4, 0, 17]], ![![0, 1, 0], ![-4, 6, 7], ![11, -9, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![4, 1, 0]] ![![19, 1, 1]]
  ![![17, 0, 0], ![11, -6, 1]] where
 M := ![![![323, 17, 17]], ![![234, 13, 12]]]
 hmul := by decide  
 g := ![![![![8, 7, 0], ![17, 0, 0]]], ![![![6, 5, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![11, -6, 1]] ![![17, 0, 0], ![7, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![119, 17, 0]], ![![187, -102, 17], ![221, -34, -34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![7, 1, 0]]], ![![![11, -6, 1]], ![![13, -2, -2]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![7, 6, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![7, 6, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![7, 6, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![7, 6, 1], ![168, -8, 43], ![978, -33, 4]]]
  hmulB := by decide  
  f := ![![![-6, -6, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -6, 19]], ![![0, 0, 1], ![-7, -14, 43], ![50, -3, 4]]]
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
  c := ![1543367, 838519, -331108]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![203217, 148693, -331108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-5, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-5, 1, 0]] 
 ![![19, 0, 0], ![14, 1, 0], ![15, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-5, 1, 0], ![2, -6, 7], ![156, -9, -4]]]
  hmulB := by decide  
  f := ![![![271, -894, 1050], ![-114, -2850, 0]], ![![201, -656, 770], ![-75, -2090, 0]], ![![215, -706, 829], ![-86, -2250, 0]]]
  g := ![![![1, 0, 0], ![-14, 19, 0], ![-15, 0, 19]], ![![-1, 1, 0], ![-1, -6, 7], ![18, -9, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![7, 6, 1]] ![![19, 0, 0], ![-5, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-95, 19, 0]], ![![133, 114, 19], ![133, -38, 38]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-5, 1, 0]]], ![![![7, 6, 1]], ![![7, -2, 2]]]]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [3, 9, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 20, 15], [8, 2, 8], [0, 1]]
 g := ![![[7, 15, 12], [21, 16, 6], [22, 10, 1], []], ![[9, 5, 4, 21], [0, 16, 0, 17], [9, 2, 8, 14], [21, 18]], ![[13, 21, 7, 3], [3, 6, 12, 3], [21, 4, 21, 3], [5, 18]]]
 h' := ![![[2, 20, 15], [6, 2, 14], [3, 2, 12], [0, 0, 1], [0, 1]], ![[8, 2, 8], [12, 12, 12], [12, 16, 8], [10, 21, 2], [2, 20, 15]], ![[0, 1], [18, 9, 20], [9, 5, 3], [3, 2, 20], [8, 2, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 10], []]
 b := ![[], [15, 1, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [3, 9, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22228258, 2446096, -242972]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-966446, 106352, -10564]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![2, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![2, 1, 0]] 
 ![![29, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![2, 1, 0], ![2, 1, 7], ![156, -9, 3]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![29, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -6], ![4, 25, 0]]]
  g := ![![![1, 0, 0], ![-2, 29, 0], ![0, 0, 29]], ![![0, 1, 0], ![0, 1, 7], ![6, -9, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![12, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![12, 1, 0]] 
 ![![29, 0, 0], ![12, 1, 0], ![27, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![12, 1, 0], ![2, 11, 7], ![156, -9, 13]]]
  hmulB := by decide  
  f := ![![![-647, -4474, -2856], ![-406, 11832, 0]], ![![-276, -1843, -1176], ![-144, 4872, 0]], ![![-609, -4166, -2659], ![-362, 11016, 0]]]
  g := ![![![1, 0, 0], ![-12, 29, 0], ![-27, 0, 29]], ![![0, 1, 0], ![-11, 11, 7], ![-3, -9, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1

def I29N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-14, 1, 0]] i)))

def SI29N2: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-14, 1, 0]] 
 ![![29, 0, 0], ![15, 1, 0], ![20, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-14, 1, 0], ![2, -15, 7], ![156, -9, -13]]]
  hmulB := by decide  
  f := ![![![-61, 777, -364], ![87, 1508, 0]], ![![-23, 388, -182], ![59, 754, 0]], ![![-44, 536, -251], ![56, 1040, 0]]]
  g := ![![![1, 0, 0], ![-15, 29, 0], ![-20, 0, 29]], ![![-1, 1, 0], ![3, -15, 7], ![19, -9, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N2 : Nat.card (O ⧸ I29N2) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N2)

lemma isPrimeI29N2 : Ideal.IsPrime I29N2 := prime_ideal_of_norm_prime hp29.out _ NI29N2
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![2, 1, 0]] ![![29, 0, 0], ![12, 1, 0]]
  ![![29, 0, 0], ![12, 6, 1]] where
 M := ![![![841, 0, 0], ![348, 29, 0]], ![![58, 29, 0], ![26, 13, 7]]]
 hmul := by decide  
 g := ![![![![17, -6, -1], ![29, 0, 0]], ![![0, -5, -1], ![29, 0, 0]]], ![![![-10, -5, -1], ![29, 0, 0]], ![![-2, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![12, 6, 1]] ![![29, 0, 0], ![-14, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-406, 29, 0]], ![![348, 174, 29], ![0, -87, 29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-14, 1, 0]]], ![![![12, 6, 1]], ![![0, -3, 1]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [20, 18, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 3, 8], [2, 27, 23], [0, 1]]
 g := ![![[22, 8, 28], [14, 26, 10], [0, 18, 16], [1]], ![[13, 9, 17, 9], [14, 30, 19, 2], [28, 12, 3, 4], [18, 14, 16, 16]], ![[18, 7, 21, 17], [12, 2, 23, 23], [12, 26, 11, 15], [28, 4, 9, 15]]]
 h' := ![![[25, 3, 8], [30, 3, 20], [0, 9, 14], [11, 13, 27], [0, 1]], ![[2, 27, 23], [15, 23, 6], [7, 12, 16], [13, 30, 27], [25, 3, 8]], ![[0, 1], [5, 5, 5], [18, 10, 1], [6, 19, 8], [2, 27, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 29], []]
 b := ![[], [30, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [20, 18, 4, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-998138, 127596, -48608]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32198, 4116, -1568]
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



lemma PB233I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB233I0 : PrimesBelowBoundCertificateInterval O 1 31 233 where
  m := 11
  g := ![3, 3, 3, 3, 1, 2, 3, 2, 1, 3, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB233I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
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
    · exact ![2, 2, 2]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![12167]
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
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
      exact NI29N2
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I5N0, I7N0, I7N1, I7N2, I13N0, I13N1, I17N0, I17N1, I17N2, I19N1, I29N0, I29N1, I29N2]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N0, I3N0], [I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [], [I13N0, I13N1], [I17N0, I17N1, I17N2], [I19N1], [], [I29N0, I29N1, I29N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
