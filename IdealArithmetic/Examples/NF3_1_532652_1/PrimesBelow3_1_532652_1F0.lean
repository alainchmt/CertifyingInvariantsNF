
import IdealArithmetic.Examples.NF3_1_532652_1.RI3_1_532652_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![716, 265, 28]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![716, 265, 28]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![716, 265, 28], ![6776, 2508, 265], ![64130, 23736, 2508]]]
  hmulB := by decide  
  f := ![![![24, -12, 1]], ![![121, 44, -6]], ![![-1452, -263, 44]]]
  g := ![![![358, 265, 28], ![3388, 2508, 265], ![32065, 23736, 2508]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![716, 265, 28]] ![![716, 265, 28]]
  ![![4103936, 1518968, 160497]] where
 M := ![![![4103936, 1518968, 160497]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![4103936, 1518968, 160497]] ![![716, 265, 28]]
  ![![2, 0, 0]] where
 M := ![![![23523617954, 8706671576, 919963204]]]
 hmul := by decide  
 g := ![![![![11761808977, 4353335788, 459981602]]]]
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
  c := ![-104301, -43314, -4884]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34767, -14438, -1628]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-43, -4, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-43, -4, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 1, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-43, -4, 1], ![242, 21, -4], ![-968, -14, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![9, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -1, 5]], ![![-9, -1, 1], ![50, 5, -4], ![-202, -7, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 4], [0, 1]]
 g := ![![[1, 1], [1]], ![[0, 4], [1]]]
 h' := ![![[4, 4], [4, 4], [0, 1]], ![[0, 1], [0, 1], [4, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3549, -13, 192]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![633, -41, 192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![0, -1, 1], ![242, 64, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![15, 0, 0]], ![![2, -1, 0], ![6, 0, 0]], ![![2, -1, 0], ![6, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![-4, 0, 5]], ![![-1, 1, 0], ![0, -1, 1], ![-2, 64, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-43, -4, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-215, -20, 5], ![285, 25, -5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![-43, -4, 1]], ![![57, 5, -1]]]]
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
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-41, -3, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-41, -3, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![1, 4, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-41, -3, 1], ![242, 23, -3], ![-726, 50, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -4, 7]], ![![-6, -1, 1], ![35, 5, -3], ![-107, -6, 23]]]
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
  c := ![-1444, 1798, 565]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-287, -66, 565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![0, 3, 1], ![242, 64, 3]]]
  hmulB := by decide  
  f := ![![![4, 1, 0], ![-7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![2, 0, 0], ![-3, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-2, 3, 1], ![5, 64, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-41, -3, 1]] ![![7, 0, 0], ![3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![-287, -21, 7], ![119, 14, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![3, 1, 0]]], ![![![-41, -3, 1]], ![![17, 2, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![0, 1, 0]] 
 ![![11, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 0, 1], ![242, 64, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![0, 1, 0], ![0, 0, 1], ![22, 64, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![3, 1, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![3, 1, 0], ![0, 3, 1], ![242, 64, 3]]]
  hmulB := by decide  
  f := ![![![7, 2, 0], ![-22, 0, 0]], ![![-3, -1, 0], ![12, 0, 0]], ![![-2, -1, 0], ![8, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 11, 0], ![-2, 0, 11]], ![![0, 1, 0], ![-1, 3, 1], ![4, 64, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![0, -3, 1], ![242, 64, -3]]]
  hmulB := by decide  
  f := ![![![19, -6, 0], ![66, 0, 0]], ![![16, -5, 0], ![56, 0, 0]], ![![4, -1, 0], ![14, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-2, 0, 11]], ![![-1, 1, 0], ![2, -3, 1], ![-24, 64, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![11, 0, 0], ![-44, -8, 1]] where
 M := ![![![121, 0, 0], ![33, 11, 0]], ![![0, 11, 0], ![0, 3, 1]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![3, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-44, -8, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-484, -88, 11], ![374, 44, -11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-3, 1, 0]]], ![![![-44, -8, 1]], ![![34, 4, -1]]]]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [2, 4, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 7, 6], [11, 5, 7], [0, 1]]
 g := ![![[11, 12, 4], [5, 4], [1]], ![[7, 10, 12, 2], [5, 1], [12, 5, 5, 8]], ![[10, 3, 4, 6], [4, 1], [0, 11, 4, 5]]]
 h' := ![![[4, 7, 6], [7, 1, 2], [11, 9, 2], [0, 1]], ![[11, 5, 7], [4, 1, 3], [1, 5, 12], [4, 7, 6]], ![[0, 1], [4, 11, 8], [5, 12, 12], [11, 5, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 12], []]
 b := ![[], [3, 8, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [2, 4, 11, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-99944, -39988, -4303]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7688, -3076, -331]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [4, 12, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 3], [9, 16, 14], [0, 1]]
 g := ![![[12, 2, 1], [16, 16], [12, 1], []], ![[2, 7, 0, 3], [8, 4], [7, 1], [6, 9]], ![[15, 4, 1, 5], [0, 4], [], [12, 9]]]
 h' := ![![[3, 0, 3], [13, 12, 1], [3, 5, 13], [0, 0, 1], [0, 1]], ![[9, 16, 14], [0, 11, 1], [10, 7, 2], [2, 11, 16], [3, 0, 3]], ![[0, 1], [1, 11, 15], [1, 5, 2], [16, 6], [9, 16, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 6], []]
 b := ![[], [10, 13, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [4, 12, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2674848, 987377, 90627]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![157344, 58081, 5331]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-39, 5, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-39, 5, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![18, 5, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-39, 5, 1], ![242, 25, 5], ![1210, 562, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -5, 19]], ![![-3, 0, 1], ![8, 0, 5], ![40, 23, 25]]]
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
  c := ![-1456, -130, 69]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-142, -25, 69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-5, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-5, 1, 0]] 
 ![![19, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-5, 1, 0], ![0, -5, 1], ![242, 64, -5]]]
  hmulB := by decide  
  f := ![![![31, -6, 0], ![114, 0, 0]], ![![26, -5, 0], ![96, 0, 0]], ![![27, -5, 0], ![100, 1, 0]]]
  g := ![![![1, 0, 0], ![-14, 19, 0], ![-13, 0, 19]], ![![-1, 1, 0], ![3, -5, 1], ![-31, 64, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-39, 5, 1]] ![![19, 0, 0], ![-5, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-95, 19, 0]], ![![-741, 95, 19], ![437, 0, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-5, 1, 0]]], ![![![-39, 5, 1]], ![![23, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-39, 5, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-39, 5, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![7, 5, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-39, 5, 1], ![242, 25, 5], ![1210, 562, 25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -5, 23]], ![![-2, 0, 1], ![9, 0, 5], ![45, 19, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [18, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 22], [0, 1]]
 g := ![![[8, 9], [22, 4], [0, 13], [1]], ![[0, 14], [21, 19], [14, 10], [1]]]
 h' := ![![[17, 22], [18, 3], [0, 21], [5, 17], [0, 1]], ![[0, 1], [0, 20], [12, 2], [18, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [4, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [18, 6, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![986, 1230, 269]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-39, -5, 269]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-5, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-5, 1, 0]] 
 ![![23, 0, 0], ![18, 1, 0], ![21, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-5, 1, 0], ![0, -5, 1], ![242, 64, -5]]]
  hmulB := by decide  
  f := ![![![91, -18, 0], ![414, 0, 0]], ![![66, -13, 0], ![300, 0, 0]], ![![77, -15, 0], ![350, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 23, 0], ![-21, 0, 23]], ![![-1, 1, 0], ![3, -5, 1], ![-35, 64, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-39, 5, 1]] ![![23, 0, 0], ![-5, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-115, 23, 0]], ![![-897, 115, 23], ![437, 0, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-5, 1, 0]]], ![![![-39, 5, 1]], ![![19, 0, 0]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [28, 20, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 11, 25], [8, 17, 4], [0, 1]]
 g := ![![[22, 12, 22], [6, 5], [24, 19, 1], [1]], ![[1, 17, 24, 16], [1, 9], [3, 18, 9, 6], [26, 14, 0, 23]], ![[21, 26, 9, 5], [14, 6], [17, 20, 7, 20], [9, 1, 10, 6]]]
 h' := ![![[22, 11, 25], [2, 19, 15], [24, 4, 11], [1, 9, 1], [0, 1]], ![[8, 17, 4], [17, 19, 5], [4, 11, 26], [2, 9, 10], [22, 11, 25]], ![[0, 1], [1, 20, 9], [25, 14, 21], [28, 11, 18], [8, 17, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 6], []]
 b := ![[], [2, 13, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [28, 20, 28, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1960980, -218080, 54520]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67620, -7520, 1880]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-48, 4, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-48, 4, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![14, 4, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-48, 4, 1], ![242, 16, 4], ![968, 498, 16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -4, 31]], ![![-2, 0, 1], ![6, 0, 4], ![24, 14, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [21, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 30], [0, 1]]
 g := ![![[8, 18], [12, 16], [5, 18], [18, 1]], ![[22, 13], [21, 15], [19, 13], [5, 30]]]
 h' := ![![[18, 30], [27, 24], [19, 27], [25, 24], [0, 1]], ![[0, 1], [25, 7], [9, 4], [23, 7], [18, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [21, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [21, 13, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-125, 75, 104]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-51, -11, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-4, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-4, 1, 0]] 
 ![![31, 0, 0], ![27, 1, 0], ![15, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-4, 1, 0], ![0, -4, 1], ![242, 64, -4]]]
  hmulB := by decide  
  f := ![![![41, -10, 0], ![310, 0, 0]], ![![37, -9, 0], ![280, 0, 0]], ![![25, -6, 0], ![190, 1, 0]]]
  g := ![![![1, 0, 0], ![-27, 31, 0], ![-15, 0, 31]], ![![-1, 1, 0], ![3, -4, 1], ![-46, 64, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-48, 4, 1]] ![![31, 0, 0], ![-4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-124, 31, 0]], ![![-1488, 124, 31], ![434, 0, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-4, 1, 0]]], ![![![-48, 4, 1]], ![![14, 0, 0]]]]
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


lemma PB207I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB207I0 : PrimesBelowBoundCertificateInterval O 1 31 207 where
  m := 11
  g := ![3, 1, 2, 2, 3, 1, 1, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB207I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0]
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
    · exact ![27]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![2197]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
    · exact ![24389]
    · exact ![961, 31]
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
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
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
  β := ![I2N0, I3N0, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I11N2, I19N1, I23N1, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0], [I5N0, I5N1], [I7N0, I7N1], [I11N0, I11N1, I11N2], [], [], [I19N1], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
