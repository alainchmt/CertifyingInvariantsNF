
import IdealArithmetic.Examples.NF3_1_412776_3.RI3_1_412776_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![14, 1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![14, 1, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![14, 1, 1], ![112, -7, 2], ![112, 35, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-14, 7, 2], ![-6, 1, 0]], ![![-7, -8, -3], ![9, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![7, 1, 1], ![56, -7, 2], ![56, 35, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![15, 1, 1]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![15, 1, 1], ![112, -6, 2], ![112, 35, -6]]]
  hmulB := by decide  
  f := ![![![-7, 27, -14], ![16, 0, -2]], ![![-11, -14, 6], ![-6, 0, 1]], ![![-11, 13, -7], ![9, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![7, 1, 1], ![55, -6, 2], ![59, 35, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![14, 1, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![2, 0, 0], ![0, 1, 0]] where
 M := ![![![4, 0, 0], ![30, 2, 2]], ![![28, 2, 2], ![434, 43, 10]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![15, 0, 1], ![2, 0, 0]]], ![![![14, 0, 1], ![2, 0, 0]], ![![217, 17, 5], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![15, 1, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![30, 2, 2]], ![![0, 2, 0], ![112, -6, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![15, 1, 1]]], ![![![0, 1, 0]], ![![56, -3, 1]]]]
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
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![0, 1, 2], ![112, -21, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![1, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-1, 1, 2], ![44, -21, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![14, 1, 1]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, 2, 2]]]
 hmul := by decide  
 g := ![![![![-11, -1, -1], ![3, 0, 0]], ![![-13, 0, -1], ![3, 0, 0]]], ![![![-13, 0, -1], ![3, 0, 0]], ![![5, 1, 1], ![-1, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![14, 1, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![42, 3, 3], ![126, -6, 3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![14, 1, 1]], ![![42, -2, 1]]]]
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


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [3, 2, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 0, 2], [3, 4, 3], [0, 1]]
 g := ![![[2, 2, 1], []], ![[1, 2, 1, 2], [3, 4]], ![[4, 2], [2, 4]]]
 h' := ![![[4, 0, 2], [0, 0, 1], [0, 1]], ![[3, 4, 3], [2, 2, 4], [4, 0, 2]], ![[0, 1], [3, 3], [3, 4, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 4], []]
 b := ![[], [4, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [3, 2, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1235, 775, -710]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![247, 155, -142]
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


def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 2], ![112, -21, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 4, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 2], ![16, -21, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![14, 0, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![0, 0, 2]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-4, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![14, 0, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![98, 0, 7], ![112, -7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![14, 0, 1]], ![![16, -1, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![12, 1, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![12, 1, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 1, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![12, 1, 1], ![112, -9, 2], ![112, 35, -9]]]
  hmulB := by decide  
  f := ![![![-11, -1, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 11]], ![![1, 0, 1], ![10, -1, 2], ![11, 4, -9]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 10], [0, 1]]
 g := ![![[5, 3], [3, 4], [1]], ![[0, 8], [0, 7], [1]]]
 h' := ![![[2, 10], [10, 6], [7, 2], [0, 1]], ![[0, 1], [0, 5], [0, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [9, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [4, 9, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1348, 742, -160]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108, 82, -160]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-2, 1, 0]] 
 ![![11, 0, 0], ![9, 1, 0], ![9, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-2, 1, 0], ![0, -2, 2], ![112, -21, -2]]]
  hmulB := by decide  
  f := ![![![17, -8, 0], ![88, 0, 0]], ![![15, -7, 0], ![78, 0, 0]], ![![15, -6, -1], ![78, 6, 0]]]
  g := ![![![1, 0, 0], ![-9, 11, 0], ![-9, 0, 11]], ![![-1, 1, 0], ![0, -2, 2], ![29, -21, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![12, 1, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![132, 11, 11], ![88, -11, 0]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-2, 1, 0]]], ![![![12, 1, 1]], ![![8, -1, 0]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![0, 3, 2], ![112, -21, 3]]]
  hmulB := by decide  
  f := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![2, -1, -1], ![-8, 7, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-2, 0, 13]], ![![0, 1, 0], ![-1, 3, 2], ![13, -21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![5, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![5, 1, 0]] 
 ![![13, 0, 0], ![5, 1, 0], ![7, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![5, 1, 0], ![0, 5, 2], ![112, -21, 5]]]
  hmulB := by decide  
  f := ![![![21, 4, 0], ![-52, 0, 0]], ![![5, 1, 0], ![-12, 0, 0]], ![![9, -1, -1], ![-22, 7, 0]]]
  g := ![![![1, 0, 0], ![-5, 13, 0], ![-7, 0, 13]], ![![0, 1, 0], ![-3, 5, 2], ![14, -21, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![3, 1, 0]] ![![13, 0, 0], ![5, 1, 0]]
  ![![13, 0, 0], ![14, 4, 1]] where
 M := ![![![169, 0, 0], ![65, 13, 0]], ![![39, 13, 0], ![15, 8, 2]]]
 hmul := by decide  
 g := ![![![![-1, -4, -1], ![13, 0, 0]], ![![-9, -3, -1], ![13, 0, 0]]], ![![![-11, -3, -1], ![13, 0, 0]], ![![-1, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![14, 4, 1]] ![![13, 0, 0], ![5, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![65, 13, 0]], ![![182, 52, 13], ![182, 13, 13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![5, 1, 0]]], ![![![14, 4, 1]], ![![14, 1, 1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [7, 13, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 6, 12], [8, 10, 5], [0, 1]]
 g := ![![[8, 4, 13], [8, 16], [3, 1], []], ![[10, 5, 1, 10], [4, 9], [13, 15], [15, 8]], ![[10, 1, 12, 3], [12, 1], [15, 2], [5, 8]]]
 h' := ![![[12, 6, 12], [11, 16, 9], [13, 5, 13], [0, 0, 1], [0, 1]], ![[8, 10, 5], [10, 0, 10], [2, 16, 3], [5, 12, 10], [12, 6, 12]], ![[0, 1], [9, 1, 15], [5, 13, 1], [12, 5, 6], [8, 10, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 10], []]
 b := ![[], [14, 16, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [7, 13, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-178857, -3638, -7106]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10521, -214, -418]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![10, -2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![10, -2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![10, 17, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![10, -2, 1], ![112, -11, -4], ![-224, 98, -11]]]
  hmulB := by decide  
  f := ![![![-9, 2, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -17, 19]], ![![0, -1, 1], ![8, 3, -4], ![-6, 15, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [5, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 18], [0, 1]]
 g := ![![[3, 4], [6, 6], [16], [1]], ![[0, 15], [11, 13], [16], [1]]]
 h' := ![![[4, 18], [8, 17], [2, 5], [14, 4], [0, 1]], ![[0, 1], [0, 2], [3, 14], [11, 15], [4, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [18, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [5, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-651, 647, -238]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![91, 247, -238]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![4, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![4, 1, 0]] 
 ![![19, 0, 0], ![4, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![4, 1, 0], ![0, 4, 2], ![112, -21, 4]]]
  hmulB := by decide  
  f := ![![![13, 3, 0], ![-57, 0, 0]], ![![-4, -1, 0], ![20, 0, 0]], ![![5, -1, -1], ![-21, 10, 0]]]
  g := ![![![1, 0, 0], ![-4, 19, 0], ![-11, 0, 19]], ![![0, 1, 0], ![-2, 4, 2], ![8, -21, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![10, -2, 1]] ![![19, 0, 0], ![4, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![76, 19, 0]], ![![190, -38, 19], ![152, -19, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![4, 1, 0]]], ![![![10, -2, 1]], ![![8, -1, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![25, 5, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![25, 5, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![2, 5, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![25, 5, 1], ![112, 4, 10], ![560, -49, 4]]]
  hmulB := by decide  
  f := ![![![-24, -5, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -5, 23]], ![![1, 0, 1], ![4, -2, 10], ![24, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [11, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 22], [0, 1]]
 g := ![![[20, 3], [8, 8], [21, 8], [1]], ![[4, 20], [19, 15], [9, 15], [1]]]
 h' := ![![[10, 22], [4, 16], [22, 13], [12, 10], [0, 1]], ![[0, 1], [3, 7], [14, 10], [20, 13], [10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [1, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [11, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![235, 1, -32]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 7, -32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-10, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-10, 1, 0]] 
 ![![23, 0, 0], ![13, 1, 0], ![19, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-10, 1, 0], ![0, -10, 2], ![112, -21, -10]]]
  hmulB := by decide  
  f := ![![![111, -11, 0], ![253, 0, 0]], ![![61, -6, 0], ![139, 0, 0]], ![![103, -5, -1], ![235, 12, 0]]]
  g := ![![![1, 0, 0], ![-13, 23, 0], ![-19, 0, 23]], ![![-1, 1, 0], ![4, -10, 2], ![25, -21, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![25, 5, 1]] ![![23, 0, 0], ![-10, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-230, 23, 0]], ![![575, 115, 23], ![-138, -46, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-10, 1, 0]]], ![![![25, 5, 1]], ![![-6, -2, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![11, 13, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![11, 13, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![11, 13, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![11, 13, 1], ![112, -10, 26], ![1456, -217, -10]]]
  hmulB := by decide  
  f := ![![![-10, -13, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -13, 29]], ![![0, 0, 1], ![-6, -12, 26], ![54, -3, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [16, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 28], [0, 1]]
 g := ![![[11, 20], [23], [17, 28], [27, 1]], ![[0, 9], [23], [19, 1], [25, 28]]]
 h' := ![![[27, 28], [14, 7], [18, 20], [3, 17], [0, 1]], ![[0, 1], [0, 22], [7, 9], [27, 12], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [16, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4275, -666, 705]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-120, -339, 705]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![3, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![3, 1, 0]] 
 ![![29, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![3, 1, 0], ![0, 3, 2], ![112, -21, 3]]]
  hmulB := by decide  
  f := ![![![25, 8, 0], ![-232, 0, 0]], ![![-3, -1, 0], ![30, 0, 0]], ![![8, 1, -1], ![-74, 15, 0]]]
  g := ![![![1, 0, 0], ![-3, 29, 0], ![-10, 0, 29]], ![![0, 1, 0], ![-1, 3, 2], ![5, -21, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![11, 13, 1]] ![![29, 0, 0], ![3, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![87, 29, 0]], ![![319, 377, 29], ![145, 29, 29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![3, 1, 0]]], ![![![11, 13, 1]], ![![5, 1, 1]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0]] 
 ![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [7, 10, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 16, 3], [30, 14, 28], [0, 1]]
 g := ![![[12, 24, 4], [17, 6, 1], [25, 11, 2], [1]], ![[17, 11, 9, 26], [4, 23, 10, 22], [29, 11, 22, 22], [1, 21, 28, 27]], ![[6, 17, 17, 8], [13, 20, 12, 2], [15, 14, 21, 4], [13, 23, 7, 4]]]
 h' := ![![[9, 16, 3], [5, 2, 29], [11, 1, 30], [24, 21, 8], [0, 1]], ![[30, 14, 28], [12, 28, 9], [30, 14, 20], [9, 11, 20], [9, 16, 3]], ![[0, 1], [19, 1, 24], [18, 16, 12], [1, 30, 3], [30, 14, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 9], []]
 b := ![[], [29, 13, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [7, 10, 23, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34813, 5704, 1674]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1123, 184, 54]
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



lemma PB182I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB182I0 : PrimesBelowBoundCertificateInterval O 1 31 182 where
  m := 11
  g := ![3, 3, 1, 3, 2, 3, 1, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB182I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1]
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
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![13, 13, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![841, 29]
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
      exact NI2N1
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
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I5N0, I7N0, I11N0, I11N1, I13N0, I13N1, I19N1, I23N1, I29N1]
  Il := ![[I2N0, I2N1, I2N1], [I3N0, I3N0, I3N0], [I5N0], [I7N0, I7N0, I7N0], [I11N0, I11N1], [I13N0, I13N1, I13N1], [], [I19N1], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
