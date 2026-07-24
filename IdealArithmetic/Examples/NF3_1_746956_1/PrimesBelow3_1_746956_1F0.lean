
import IdealArithmetic.Examples.NF3_1_746956_1.RI3_1_746956_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![-1, 4, 11], ![106, -23, -4]]]
  hmulB := by decide  
  f := ![![![0, 3, 11], ![2, -2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 1, 6], ![2, -1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-6, 4, 11], ![55, -23, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![15, 2, 1]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-1, 4, 11]]]
 hmul := by decide  
 g := ![![![![-13, -2, -1], ![2, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-8, 1, 5], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![15, 2, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![30, 4, 2], ![104, 0, 18]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![15, 2, 1]], ![![52, 0, 9]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![14, 0, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![14, 0, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![14, 0, 1], ![106, -9, -4], ![-75, 18, -6]]]
  hmulB := by decide  
  f := ![![![-13, 0, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, 0, 3]], ![![4, 0, 1], ![38, -3, -4], ![-21, 6, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2], [0, 1]]
 g := ![![[2, 1]], ![[1, 2]]]
 h' := ![![[2, 2], [0, 1]], ![[0, 1], [2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2564, -267, -2618]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2600, -89, -2618]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![-1, 5, 11], ![106, -23, -3]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 2, 4], ![-1, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![-2, 5, 11], ![43, -23, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![14, 0, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![42, 0, 3], ![120, -9, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![14, 0, 1]], ![![40, -3, -1]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [2, 4, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 3], [2, 3, 2], [0, 1]]
 g := ![![[1, 0, 1], []], ![[0, 2, 1, 2], [1, 4]], ![[0, 2, 2, 2], [2, 4]]]
 h' := ![![[3, 1, 3], [0, 0, 1], [0, 1]], ![[2, 3, 2], [2, 4, 3], [3, 1, 3]], ![[0, 1], [0, 1, 1], [2, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 4], []]
 b := ![[], [1, 2, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [2, 4, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![50433230, -12125835, 14331565]
  a := ![-3, 9, 32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10086646, -2425167, 2866313]
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
 ![![7, 0, 0], ![0, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![-1, 4, 11], ![106, -23, -4]]]
  hmulB := by decide  
  f := ![![![0, 3, 11], ![7, -7, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 2, 8], ![6, -5, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![-5, 0, 7]], ![![0, 1, 0], ![-8, 4, 11], ![18, -23, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![12, 1, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![-1, 4, 11]]]
 hmul := by decide  
 g := ![![![![-5, -1, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-7, 0, 1], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![12, 1, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![84, 7, 7], ![105, -7, 7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![12, 1, 1]], ![![15, -1, 1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![3, 1, 0]] 
 ![![11, 0, 0], ![3, 1, 0], ![1, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![3, 1, 0], ![-1, 7, 11], ![106, -23, -1]]]
  hmulB := by decide  
  f := ![![![1189, -304, -12], ![308, 0, -132]], ![![297, -76, -3], ![78, 0, -33]], ![![107, -28, -1], ![32, 0, -12]]]
  g := ![![![1, 0, 0], ![-3, 11, 0], ![-1, 0, 11]], ![![0, 1, 0], ![-3, 7, 11], ![16, -23, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![4, 1, 0]] 
 ![![11, 0, 0], ![4, 1, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![4, 1, 0], ![-1, 8, 11], ![106, -23, 0]]]
  hmulB := by decide  
  f := ![![![-3, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-4, 11, 0], ![0, 0, 1]], ![![0, 1, 0], ![-3, 8, 1], ![18, -23, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [6, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 10], [0, 1]]
 g := ![![[5, 1], [2, 9], [1]], ![[8, 10], [7, 2], [1]]]
 h' := ![![[3, 10], [10, 10], [5, 3], [0, 1]], ![[0, 1], [7, 1], [3, 8], [3, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [6, 8, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![638951, -112614, -104071]
  a := ![1, -67, -75]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99037, -112614, -9461]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![3, 1, 0]] ![![11, 0, 0], ![4, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![44, 11, 0]], ![![33, 11, 0], ![11, 11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![4, 1, 0]]], ![![![3, 1, 0]], ![![1, 1, 1]]]]
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
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![11, 4, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![11, 4, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![11, 4, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![11, 4, 1], ![102, 4, 40], ![349, -74, -25]]]
  hmulB := by decide  
  f := ![![![-10, -4, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -4, 13]], ![![0, 0, 1], ![-26, -12, 40], ![48, 2, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [4, 6, 1] where
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
 g := ![![[8, 10], [10], [7, 1]], ![[0, 3], [10], [1, 12]]]
 h' := ![![[7, 12], [3, 7], [11, 6], [0, 1]], ![[0, 1], [0, 6], [1, 7], [7, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [4, 6, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9029, 3992, -22324]
  a := ![3, -10, -32]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18195, 7176, -22324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-1, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-1, 1, 0]] 
 ![![13, 0, 0], ![12, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-1, 1, 0], ![-1, 3, 11], ![106, -23, -5]]]
  hmulB := by decide  
  f := ![![![72, -215, -792], ![-13, 936, 0]], ![![66, -197, -726], ![-12, 858, 0]], ![![66, -198, -731], ![-18, 864, 0]]]
  g := ![![![1, 0, 0], ![-12, 13, 0], ![-12, 0, 13]], ![![-1, 1, 0], ![-13, 3, 11], ![34, -23, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![11, 4, 1]] ![![13, 0, 0], ![-1, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-13, 13, 0]], ![![143, 52, 13], ![91, 0, 39]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-1, 1, 0]]], ![![![11, 4, 1]], ![![7, 0, 3]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![13, 7, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![13, 7, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![13, 7, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![13, 7, 1], ![99, 18, 73], ![667, -143, -35]]]
  hmulB := by decide  
  f := ![![![-12, -7, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -7, 17]], ![![0, 0, 1], ![-50, -29, 73], ![66, 6, -35]]]
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
  c := ![2580, -282, -2651]
  a := ![1, -5, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2179, 1075, -2651]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-5, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-5, 1, 0]] 
 ![![17, 0, 0], ![12, 1, 0], ![1, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-5, 1, 0], ![-1, -1, 11], ![106, -23, -9]]]
  hmulB := by decide  
  f := ![![![-14, -21, 220], ![17, -340, 0]], ![![-8, -15, 154], ![18, -238, 0]], ![![3, -2, 13], ![14, -20, 0]]]
  g := ![![![1, 0, 0], ![-12, 17, 0], ![-1, 0, 17]], ![![-1, 1, 0], ![0, -1, 11], ![23, -23, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![13, 7, 1]] ![![17, 0, 0], ![-5, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-85, 17, 0]], ![![221, 119, 17], ![34, -17, 68]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-5, 1, 0]]], ![![![13, 7, 1]], ![![2, -1, 4]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![17, 8, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![17, 8, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![17, 8, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![17, 8, 1], ![98, 26, 84], ![773, -166, -35]]]
  hmulB := by decide  
  f := ![![![-16, -8, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -8, 19]], ![![0, 0, 1], ![-70, -34, 84], ![72, 6, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [8, 5, 1] where
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

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [8, 5, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49684, -8280, 1188]
  a := ![-1, 24, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1552, -936, 1188]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-8, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-8, 1, 0]] 
 ![![19, 0, 0], ![11, 1, 0], ![16, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-8, 1, 0], ![-1, -4, 11], ![106, -23, -12]]]
  hmulB := by decide  
  f := ![![![-82, -365, 1001], ![19, -1729, 0]], ![![-43, -209, 572], ![20, -988, 0]], ![![-64, -308, 843], ![28, -1456, 0]]]
  g := ![![![1, 0, 0], ![-11, 19, 0], ![-16, 0, 19]], ![![-1, 1, 0], ![-7, -4, 11], ![29, -23, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![17, 8, 1]] ![![19, 0, 0], ![-8, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-152, 19, 0]], ![![323, 152, 19], ![-38, -38, 76]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-8, 1, 0]]], ![![![17, 8, 1]], ![![-2, -2, 4]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![6, 4, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![6, 4, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![6, 4, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![6, 4, 1], ![102, -1, 40], ![349, -74, -30]]]
  hmulB := by decide  
  f := ![![![-5, -4, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -4, 23]], ![![0, 0, 1], ![-6, -7, 40], ![23, 2, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [13, 6, 1] where
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
 g := ![![[4, 16], [16, 18], [9, 13], [1]], ![[0, 7], [0, 5], [0, 10], [1]]]
 h' := ![![[17, 22], [22, 19], [21, 15], [10, 17], [0, 1]], ![[0, 1], [0, 4], [0, 8], [0, 6], [17, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [9, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [13, 6, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5600, -54, -10329]
  a := ![-2, 9, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2938, 1794, -10329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![6, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![6, 1, 0]] 
 ![![23, 0, 0], ![6, 1, 0], ![7, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![6, 1, 0], ![-1, 10, 11], ![106, -23, 2]]]
  hmulB := by decide  
  f := ![![![-25, 199, 220], ![23, -460, 0]], ![![-5, 50, 55], ![1, -115, 0]], ![![-11, 60, 67], ![20, -140, 0]]]
  g := ![![![1, 0, 0], ![-6, 23, 0], ![-7, 0, 23]], ![![0, 1, 0], ![-6, 10, 11], ![10, -23, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![6, 4, 1]] ![![23, 0, 0], ![6, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![138, 23, 0]], ![![138, 92, 23], ![138, 23, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![6, 1, 0]]], ![![![6, 4, 1]], ![![6, 1, 2]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![3, 12, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![3, 12, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![3, 12, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![3, 12, 1], ![94, 28, 128], ![1197, -258, -65]]]
  hmulB := by decide  
  f := ![![![-2, -12, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -12, 29]], ![![0, 0, 1], ![-10, -52, 128], ![48, 18, -65]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [27, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 28], [0, 1]]
 g := ![![[4, 6], [9], [14, 6], [8, 1]], ![[23, 23], [9], [4, 23], [16, 28]]]
 h' := ![![[8, 28], [19, 8], [28, 3], [16, 8], [0, 1]], ![[0, 1], [25, 21], [23, 26], [22, 21], [8, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [13, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [27, 21, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3427, -705, -530]
  a := ![0, -5, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![173, 195, -530]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-12, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-12, 1, 0]] 
 ![![29, 0, 0], ![17, 1, 0], ![7, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-12, 1, 0], ![-1, -8, 11], ![106, -23, -16]]]
  hmulB := by decide  
  f := ![![![-239, -2114, 2904], ![58, -7656, 0]], ![![-141, -1233, 1694], ![30, -4466, 0]], ![![-49, -511, 701], ![35, -1848, 0]]]
  g := ![![![1, 0, 0], ![-17, 29, 0], ![-7, 0, 29]], ![![-1, 1, 0], ![2, -8, 11], ![21, -23, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![3, 12, 1]] ![![29, 0, 0], ![-12, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-348, 29, 0]], ![![87, 348, 29], ![58, -116, 116]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-12, 1, 0]]], ![![![3, 12, 1]], ![![2, -4, 4]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [4, 0, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 22, 4], [25, 8, 27], [0, 1]]
 g := ![![[10, 10, 8], [0, 2, 4], [29, 4, 8], [1]], ![[29, 21, 26, 5], [30, 11, 15, 1], [8, 20, 30, 2], [13, 30, 3, 2]], ![[14, 28, 11, 6], [27, 23, 8, 6], [29, 5, 16, 12], [23, 19, 11, 29]]]
 h' := ![![[22, 22, 4], [0, 25, 15], [8, 0, 29], [27, 0, 16], [0, 1]], ![[25, 8, 27], [25, 5, 3], [16, 21, 15], [25, 18, 4], [22, 22, 4]], ![[0, 1], [30, 1, 13], [15, 10, 18], [2, 13, 11], [25, 8, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 16], []]
 b := ![[], [10, 27, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [4, 0, 15, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![46723448, -10606464, 3392640]
  a := ![-2, 0, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1507208, -342144, 109440]
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



lemma PB245I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB245I0 : PrimesBelowBoundCertificateInterval O 1 31 245 where
  m := 11
  g := ![3, 2, 1, 3, 2, 2, 2, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB245I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1]
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
    · exact ![9, 3]
    · exact ![125]
    · exact ![7, 7, 7]
    · exact ![11, 121]
    · exact ![169, 13]
    · exact ![289, 17]
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
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
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
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I3N0, I3N1, I5N0, I7N0, I11N0, I11N1, I13N0, I13N1, I17N1, I19N1, I23N1, I29N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0], [I7N0, I7N0, I7N0], [I11N0, I11N1], [I13N0, I13N1], [I17N1], [I19N1], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
