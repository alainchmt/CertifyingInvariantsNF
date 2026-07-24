
import IdealArithmetic.Examples.NF3_1_796835_2.RI3_1_796835_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![3, 4, 9], ![-141, -20, -3]]]
  hmulB := by decide  
  f := ![![![4, 3, 9], ![2, -2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![2, 1, 5], ![2, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-3, 4, 9], ![-69, -20, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![14, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![14, 1, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![14, 1, 1], ![-138, -2, 6], ![-38, -29, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-14, 0, -1], ![2, 0, 0]], ![![-7, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -1, 2]], ![![7, 0, 1], ![-69, -4, 6], ![-19, -11, -7]]]
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
  c := ![-5458, -8985, -6625]
  a := ![-6, -8, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2729, -1180, -6625]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![14, 1, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![28, 2, 2]], ![![0, 2, 0], ![-138, -2, 6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![14, 1, 1]]], ![![![0, 1, 0]], ![![-69, -1, 3]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![13, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![13, 0, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![13, 0, 1], ![-141, -7, -3], ![103, -9, -5]]]
  hmulB := by decide  
  f := ![![![-12, 0, -1], ![3, 0, 0]], ![![3, 5, -5], ![21, 2, 0]], ![![-4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-1, 0, 3]], ![![4, 0, 1], ![-46, -7, -3], ![36, -9, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-14, 1, -1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-14, 1, -1]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-14, 1, -1], ![144, 10, 12], ![-244, -11, 1]]]
  hmulB := by decide  
  f := ![![![19, 19, 3], ![-27, -3, 0]], ![![8, -7, 0], ![12, 1, 0]], ![![8, 13, 2], ![-19, -2, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![-4, 1, -1], ![40, 10, 12], ![-82, -11, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![3, 3, 9], ![-141, -20, -4]]]
  hmulB := by decide  
  f := ![![![521, 124, 16], ![-132, 0, 12]], ![![261, 62, 8], ![-65, 0, 6]], ![![348, 82, 11], ![-86, 0, 8]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-7, 3, 9], ![-31, -20, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![13, 0, 1]] ![![3, 0, 0], ![-14, 1, -1]]
  ![![3, 0, 0], ![0, 1, 0]] where
 M := ![![![9, 0, 0], ![-42, 3, -3]], ![![39, 0, 3], ![-426, 2, -12]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-14, 0, -1], ![3, 0, 0]]], ![![![12, 0, -2], ![-4, 1, 0]], ![![-137, 0, 11], ![22, -5, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![0, 3, 0], ![3, 3, 9]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![0, 1, 0]], ![![1, 1, 3]]]]
 hle2 := by decide  


def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N1, I3N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N1
    exact isPrimeI3N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![235061283387153, -3415056810760, 10034796551414]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![235061283387153, -3415056810760, 10034796551414]] 
 ![![5, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![235061283387153, -3415056810760, 10034796551414], ![-1425151484181654, 20705125115833, -60839900951082], ![1515107055112802, -22012032747526, 64680115893981]]]
  hmulB := by decide  
  f := ![![![-10021959, -266204, 1304458]], ![![-36945438, -7435187, -1261842]], ![![30370004, -1389690, -6018935]]]
  g := ![![![42998338056865, -3415056810760, 10034796551414], ![-260694336455898, 20705125115833, -60839900951082], ![277149364664968, -22012032747526, 64680115893981]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-74768640332009, -838962171828, 10810829712612]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![-74768640332009, -838962171828, 10810829712612]] 
 ![![5, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![-74768640332009, -838962171828, 10810829712612], ![-1526843875993776, -294341083271561, -39983148684288], ![1231809126626784, -80518223976948, -266846688643541]]]
  hmulB := by decide  
  f := ![![![-75324571281703697588589844477, 1094343085626232655237231124, -3215615677931286667562465796]], ![![31077310943675065547531998540, -451502607613620599088535913, 1326694418540961445914522864]], ![![-157361815005407224300348588676, 2286210346272371504853298836, -6717796209508876441685403341]]]
  g := ![![![-22931222099029, -838962171828, 10810829712612], ![-37909389634076, -294341083271561, -39983148684288], ![524253755421748, -80518223976948, -266846688643541]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![235061283387153, -3415056810760, 10034796551414]] ![![235061283387153, -3415056810760, 10034796551414]]
  ![![75324571281703697588589844477, -1094343085626232655237231124, 3215615677931286667562465796]] where
 M := ![![![75324571281703697588589844477, -1094343085626232655237231124, 3215615677931286667562465796]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![75324571281703697588589844477, -1094343085626232655237231124, 3215615677931286667562465796]] ![![-74768640332009, -838962171828, 10810829712612]]
  ![![5, 0, 0]] where
 M := ![![![-5, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![14, -2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![14, -2, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 5, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![14, -2, 1], ![-147, -14, -21], ![385, 31, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -5, 7]], ![![2, -1, 1], ![-21, 13, -21], ![55, 3, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 6], [0, 1]]
 g := ![![[6, 4], [2, 1]], ![[0, 3], [4, 6]]]
 h' := ![![[2, 6], [3, 2], [0, 1]], ![[0, 1], [0, 5], [2, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 5, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6286, -5994, -4164]
  a := ![-5, -7, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-898, 2118, -4164]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![3, 4, 9], ![-141, -20, -3]]]
  hmulB := by decide  
  f := ![![![-14, -20, -45], ![0, 35, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-10, -14, -32], ![-2, 25, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-6, 4, 9], ![-18, -20, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![14, -2, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![98, -14, 7], ![-147, -14, -21]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![14, -2, 1]], ![![-21, -2, -3]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [9, 1, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 2, 2], [5, 8, 9], [0, 1]]
 g := ![![[10, 10, 1], [8, 3, 1], []], ![[1, 3, 8, 10], [10, 4, 4, 7], [9, 4]], ![[1, 0, 9, 5], [5, 5, 2, 3], [2, 4]]]
 h' := ![![[9, 2, 2], [5, 9, 1], [0, 0, 1], [0, 1]], ![[5, 8, 9], [9, 9, 4], [0, 2, 8], [9, 2, 2]], ![[0, 1], [2, 4, 6], [7, 9, 2], [5, 8, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 1], []]
 b := ![[], [10, 7, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [9, 1, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6303134618, 1580531656, 525361441]
  a := ![42, 62, 125]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![573012238, 143684696, 47760131]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558]] 
 ![![13, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558], ![-65481937290167765451568533, 5154566832534770332363279, 15007722862270917648028761], ![-206927186877874481285419341, -41238047735554728152864322, -6685926770447986420867610]]]
  hmulB := by decide  
  f := ![![![584426135420596634986371587033533282529026302271852, -8490757922337351547531999349776259552311237490526, 24949227213295038059822463680814923910095769050433]], ![![-92739136089171221625544386839238455374179379961171, 1347348290461312416128178355309594454509309333768, -3959045699057009682151194651320877850823489874177]], ![![469590139361641694485324001198194068440911839034321, -6822378320173670598299244886993397104144778585037, 20046863707806012060881007196265625111124557541336]]]
  g := ![![![-113293895448024944255501, 1835345028135478321211715, 503460796982795747625558], ![-11240853543799270567164361, 5154566832534770332363279, 15007722862270917648028761], ![-1171637604143355614653201, -41238047735554728152864322, -6685926770447986420867610]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558]] ![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558]]
  ![![-162229402772293150451282560583753259374162243480132, 3165596760476017131382816104161721859003514959794, 28146728243651805320450418082849539221022685022817]] where
 M := ![![![-162229402772293150451282560583753259374162243480132, 3165596760476017131382816104161721859003514959794, 28146728243651805320450418082849539221022685022817]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-162229402772293150451282560583753259374162243480132, 3165596760476017131382816104161721859003514959794, 28146728243651805320450418082849539221022685022817]] ![![7882402659648772000027579, 1835345028135478321211715, 503460796982795747625558]]
  ![![13, 0, 0]] where
 M := ![![![-7310370179715889072418841434757620881857626095615498840479995289304667226227, -1442145770640186664400805614718316135378603051127090440049210419062556376928, -222354709403611046917515642643492884293687763985983354360252286065064035792]]]
 hmul := by decide  
 g := ![![![![-562336167670453005570680110365970837065971238124269141575384253023435940479, -110934290049245128030831201132178164259892542394391572311477724543273567456, -17104208415662388224424280203345606484129827998921796489250175851158771984]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![8, 2, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![8, 2, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![8, 2, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![8, 2, 1], ![-135, -4, 15], ![-179, -49, -16]]]
  hmulB := by decide  
  f := ![![![-7, -2, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -2, 17]], ![![0, 0, 1], ![-15, -2, 15], ![-3, -1, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [12, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 16], [0, 1]]
 g := ![![[3, 13], [2], [4], [1]], ![[11, 4], [2], [4], [1]]]
 h' := ![![[15, 16], [12, 9], [11, 6], [5, 15], [0, 1]], ![[0, 1], [11, 8], [16, 11], [9, 2], [15, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [7, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [12, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2781, -1473, -864]
  a := ![2, 4, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![243, 15, -864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![2, 1, 0]] 
 ![![17, 0, 0], ![2, 1, 0], ![16, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![2, 1, 0], ![3, 6, 9], ![-141, -20, -1]]]
  hmulB := by decide  
  f := ![![![105, 214, 324], ![34, -612, 0]], ![![10, 23, 36], ![18, -68, 0]], ![![98, 201, 305], ![39, -576, 0]]]
  g := ![![![1, 0, 0], ![-2, 17, 0], ![-16, 0, 17]], ![![0, 1, 0], ![-9, 6, 9], ![-5, -20, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![8, 2, 1]] ![![17, 0, 0], ![2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![34, 17, 0]], ![![136, 34, 17], ![-119, 0, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![2, 1, 0]]], ![![![8, 2, 1]], ![![-7, 0, 1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![5, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![5, 1, 0]] 
 ![![19, 0, 0], ![5, 1, 0], ![8, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![5, 1, 0], ![3, 9, 9], ![-141, -20, 2]]]
  hmulB := by decide  
  f := ![![![-140, -465, -468], ![-57, 988, 0]], ![![-39, -117, -117], ![1, 247, 0]], ![![-60, -196, -197], ![-20, 416, 0]]]
  g := ![![![1, 0, 0], ![-5, 19, 0], ![-8, 0, 19]], ![![0, 1, 0], ![-6, 9, 9], ![-3, -20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-5, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-5, 1, 0]] 
 ![![19, 0, 0], ![14, 1, 0], ![4, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-5, 1, 0], ![3, -1, 9], ![-141, -20, -8]]]
  hmulB := by decide  
  f := ![![![296, -101, 945], ![-76, -1995, 0]], ![![217, -74, 693], ![-56, -1463, 0]], ![![66, -22, 199], ![-2, -420, 0]]]
  g := ![![![1, 0, 0], ![-14, 19, 0], ![-4, 0, 19]], ![![-1, 1, 0], ![-1, -1, 9], ![9, -20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-1, 1, 0]] 
 ![![19, 0, 0], ![18, 1, 0], ![7, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-1, 1, 0], ![3, 3, 9], ![-141, -20, -4]]]
  hmulB := by decide  
  f := ![![![865, 864, 2592], ![0, -5472, 0]], ![![817, 816, 2448], ![1, -5168, 0]], ![![319, 318, 955], ![6, -2016, 0]]]
  g := ![![![1, 0, 0], ![-18, 19, 0], ![-7, 0, 19]], ![![-1, 1, 0], ![-6, 3, 9], ![13, -20, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![5, 1, 0]] ![![19, 0, 0], ![-5, 1, 0]]
  ![![19, 0, 0], ![6, -8, 1]] where
 M := ![![![361, 0, 0], ![-95, 19, 0]], ![![95, 19, 0], ![-22, 4, 9]]]
 hmul := by decide  
 g := ![![![![13, 8, -1], ![19, 0, 0]], ![![-5, 1, 0], ![0, 0, 0]]], ![![![-1, 9, -1], ![19, 0, 0]], ![![-4, 4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![6, -8, 1]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-19, 19, 0]], ![![114, -152, 19], ![-171, -38, -76]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-1, 1, 0]]], ![![![6, -8, 1]], ![![-9, -2, -4]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![9, 1, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![9, 1, 0]] 
 ![![23, 0, 0], ![9, 1, 0], ![18, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![9, 1, 0], ![3, 13, 9], ![-141, -20, 6]]]
  hmulB := by decide  
  f := ![![![604, 3259, 2268], ![391, -5796, 0]], ![![231, 1267, 882], ![162, -2254, 0]], ![![468, 2550, 1775], ![318, -4536, 0]]]
  g := ![![![1, 0, 0], ![-9, 23, 0], ![-18, 0, 23]], ![![0, 1, 0], ![-12, 13, 9], ![-3, -20, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-5, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-5, 1, 0]] 
 ![![23, 0, 0], ![18, 1, 0], ![10, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-5, 1, 0], ![3, -1, 9], ![-141, -20, -8]]]
  hmulB := by decide  
  f := ![![![234, -79, 729], ![-46, -1863, 0]], ![![185, -62, 567], ![-22, -1449, 0]], ![![105, -35, 317], ![-5, -810, 0]]]
  g := ![![![1, 0, 0], ![-18, 23, 0], ![-10, 0, 23]], ![![-1, 1, 0], ![-3, -1, 9], ![13, -20, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![9, 1, 0]] ![![23, 0, 0], ![-5, 1, 0]]
  ![![23, 0, 0], ![3, 6, 1]] where
 M := ![![![529, 0, 0], ![-115, 23, 0]], ![![207, 23, 0], ![-42, 8, 9]]]
 hmul := by decide  
 g := ![![![![20, -6, -1], ![23, 0, 0]], ![![-5, 1, 0], ![0, 0, 0]]], ![![![6, -5, -1], ![23, 0, 0]], ![![-3, -2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![3, 6, 1]] ![![23, 0, 0], ![-5, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-115, 23, 0]], ![![69, 138, 23], ![-138, -23, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-5, 1, 0]]], ![![![3, 6, 1]], ![![-6, -1, 2]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
instance hp29 : Fact (Nat.Prime 29) := {out := by norm_num}

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![17, 11, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![17, 11, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![17, 11, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![17, 11, 1], ![-108, 41, 96], ![-1448, -229, -34]]]
  hmulB := by decide  
  f := ![![![-16, -11, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -11, 29]], ![![0, 0, 1], ![-60, -35, 96], ![-30, 5, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [1, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 28], [0, 1]]
 g := ![![[23, 1], [7], [28, 7], [6, 1]], ![[0, 28], [7], [12, 22], [12, 28]]]
 h' := ![![[6, 28], [23, 1], [1, 23], [23, 6], [0, 1]], ![[0, 1], [0, 28], [23, 6], [1, 23], [6, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [2, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [1, 23, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14508, -14831, -9927]
  a := ![8, 11, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5319, 3254, -9927]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-9, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-9, 1, 0]] 
 ![![29, 0, 0], ![20, 1, 0], ![5, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-9, 1, 0], ![3, -5, 9], ![-141, -20, -12]]]
  hmulB := by decide  
  f := ![![![262, -477, 864], ![-87, -2784, 0]], ![![181, -328, 594], ![-57, -1914, 0]], ![![52, -83, 149], ![7, -480, 0]]]
  g := ![![![1, 0, 0], ![-20, 29, 0], ![-5, 0, 29]], ![![-1, 1, 0], ![2, -5, 9], ![11, -20, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![17, 11, 1]] ![![29, 0, 0], ![-9, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-261, 29, 0]], ![![493, 319, 29], ![-261, -58, 87]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-9, 1, 0]]], ![![![17, 11, 1]], ![![-9, -2, 3]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [20, 25, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 25, 21], [23, 5, 10], [0, 1]]
 g := ![![[25, 22, 2], [22, 6, 9], [5, 19, 20], [1]], ![[0, 28, 0, 17], [11, 24, 0, 30], [1, 0, 23, 26], [23, 16, 1, 23]], ![[0, 17, 23, 5], [15, 27, 26, 7], [4, 18, 13, 20], [4, 26, 9, 8]]]
 h' := ![![[27, 25, 21], [25, 30, 8], [24, 19, 3], [11, 6, 19], [0, 1]], ![[23, 5, 10], [8, 6, 19], [6, 10, 11], [3, 26, 4], [27, 25, 21]], ![[0, 1], [0, 26, 4], [3, 2, 17], [28, 30, 8], [23, 5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 5], []]
 b := ![[], [15, 12, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [20, 25, 12, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3285380, -833125, -280550]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-105980, -26875, -9050]
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



lemma PB253I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB253I0 : PrimesBelowBoundCertificateInterval O 1 31 253 where
  m := 11
  g := ![2, 3, 3, 2, 1, 3, 2, 3, 3, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB253I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N0, I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N1]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![5, 5, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![19, 19, 19]
    · exact ![23, 23, 23]
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
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
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
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N1
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I5N0, I5N1, I7N0, I7N1, I13N0, I17N1, I19N0, I19N1, I19N2, I23N0, I23N1, I29N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1, I3N2], [I5N0, I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N0, I13N0], [I17N1], [I19N0, I19N1, I19N2], [I23N0, I23N1, I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
