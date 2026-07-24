
import IdealArithmetic.Examples.NF3_1_484300_1.RI3_1_484300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![1, 1, 3], ![-122, -16, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![-1, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 1, 3], ![-53, -16, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![12, 0, 1]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![2, 2, 3]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![-5, 1, 1], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![12, 0, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![24, 0, 2], ![-110, -4, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![12, 0, 1]], ![![-55, -2, 1]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![1, 1, 3], ![-122, -16, 2]]]
  hmulB := by decide  
  f := ![![![219, 6, -4], ![78, 0, 6]], ![![0, 0, 0], ![1, 0, 0]], ![![73, 2, -1], ![26, 0, 2]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-1, 1, 3], ![-36, -16, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![1, -1, 3], ![-122, -16, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 1]], ![![-1, 1, 0], ![1, -1, 1], ![-30, -16, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
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

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1174, -1816, -765]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1602, -1816, -255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![3, 3, 0], ![0, 0, 3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![1, 1, 0]], ![![0, 0, 1]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![1, -2, 3], ![-122, -16, -1]]]
  hmulB := by decide  
  f := ![![![-5, 15, -24], ![5, 40, 0]], ![![-1, 7, -12], ![6, 20, 0]], ![![-4, 12, -19], ![4, 32, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-4, 0, 5]], ![![-1, 1, 0], ![-1, -2, 3], ![-14, -16, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0], ![10, -3, 1]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![5, -4, 3]]]
 hmul := by decide  
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-2, 1, 0], ![0, 0, 0]], ![![-5, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![10, -3, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![50, -15, 5], ![-145, 0, -10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-2, 1, 0]]], ![![![10, -3, 1]], ![![-29, 0, -2]]]]
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
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 3 2 2 [6, 3, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 1, 6], [5, 5, 1], [0, 1]]
 g := ![![[3, 2, 1], [1]], ![[5, 6, 0, 6], [1, 4, 2, 6]], ![[2, 0, 5, 4], [2, 5, 2, 1]]]
 h' := ![![[3, 1, 6], [1, 4, 1], [0, 1]], ![[5, 5, 1], [0, 0, 1], [3, 1, 6]], ![[0, 1], [1, 3, 5], [5, 5, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 6], []]
 b := ![[], [4, 5, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 3
  hpos := by decide
  P := [6, 3, 6, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14029794317, -3149906991, -326211655]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2004256331, -449986713, -46601665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![8, 2, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![8, 2, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![8, 2, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![8, 2, 1], ![-120, -8, 7], ![-290, -78, -6]]]
  hmulB := by decide  
  f := ![![![-7, -2, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -2, 11]], ![![0, 0, 1], ![-16, -2, 7], ![-22, -6, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 10], [0, 1]]
 g := ![![[6, 4], [0, 5], [1]], ![[1, 7], [2, 6], [1]]]
 h' := ![![[7, 10], [0, 2], [3, 7], [0, 1]], ![[0, 1], [3, 9], [8, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [8, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-541, -2030, -795]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![529, -40, -795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![4, 1, 0]] 
 ![![11, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![4, 1, 0], ![1, 4, 3], ![-122, -16, 5]]]
  hmulB := by decide  
  f := ![![![0, 11, 9], ![11, -33, 0]], ![![1, 4, 3], ![1, -11, 0]], ![![0, 6, 5], ![6, -18, 0]]]
  g := ![![![1, 0, 0], ![-4, 11, 0], ![-6, 0, 11]], ![![0, 1, 0], ![-3, 4, 3], ![-8, -16, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![8, 2, 1]] ![![11, 0, 0], ![4, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![44, 11, 0]], ![![88, 22, 11], ![-88, 0, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![4, 1, 0]]], ![![![8, 2, 1]], ![![-8, 0, 1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![14, -3, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![14, -3, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![1, 10, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![14, -3, 1], ![-125, -2, -8], ![320, 2, -5]]]
  hmulB := by decide  
  f := ![![![-13, 3, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -10, 13]], ![![1, -1, 1], ![-9, 6, -8], ![25, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 12], [0, 1]]
 g := ![![[9, 1], [1], [5, 1]], ![[1, 12], [1], [10, 12]]]
 h' := ![![[5, 12], [11, 12], [10, 1], [0, 1]], ![[0, 1], [6, 1], [2, 12], [5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [10, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [11, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1141, -516, -153]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, 78, -153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-5, 1, 0]] 
 ![![13, 0, 0], ![8, 1, 0], ![5, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-5, 1, 0], ![1, -5, 3], ![-122, -16, -4]]]
  hmulB := by decide  
  f := ![![![-14, 99, -60], ![13, 260, 0]], ![![-6, 59, -36], ![14, 156, 0]], ![![-5, 38, -23], ![6, 100, 0]]]
  g := ![![![1, 0, 0], ![-8, 13, 0], ![-5, 0, 13]], ![![-1, 1, 0], ![2, -5, 3], ![2, -16, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![14, -3, 1]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-65, 13, 0]], ![![182, -39, 13], ![-195, 13, -13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-5, 1, 0]]], ![![![14, -3, 1]], ![![-15, 1, -1]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0]] 
 ![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [9, 1, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 9, 13], [5, 7, 4], [0, 1]]
 g := ![![[8, 15, 4], [], [1, 1], []], ![[15, 14, 8, 15], [10, 2], [2, 15], [12, 16]], ![[0, 15, 16, 15], [9, 2], [3, 13], [4, 16]]]
 h' := ![![[13, 9, 13], [13, 10, 15], [8, 7], [0, 0, 1], [0, 1]], ![[5, 7, 4], [4, 2, 14], [14, 12, 6], [10, 10, 7], [13, 9, 13]], ![[0, 1], [0, 5, 5], [9, 15, 11], [6, 7, 9], [5, 7, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 1], []]
 b := ![[], [16, 3, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [9, 1, 16, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-275349, -677110, -413287]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16197, -39830, -24311]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-568706, 43577, -22304]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![-568706, 43577, -22304]] 
 ![![19, 0, 0], ![0, 19, 0], ![1, 5, 1]] where
  M :=![![![-568706, 43577, -22304], ![2764665, -211842, 108427], ![-4290410, 328752, -168265]]]
  hmulB := by decide  
  f := ![![![-54, 37, 31]], ![![-3745, -550, 142]], ![![-1301, -249, 12]]]
  g := ![![![-28758, 8163, -22304], ![139802, -39683, 108427], ![-216955, 61583, -168265]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 15, 1] where
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
 g := ![![[7, 5], [1, 4], [16], [1]], ![[8, 14], [17, 15], [16], [1]]]
 h' := ![![[4, 18], [6, 10], [18, 17], [6, 4], [0, 1]], ![[0, 1], [8, 9], [10, 2], [3, 15], [4, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [2, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [13, 15, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2506, -637, -458]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![156, 87, -458]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![54, -37, -31]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![54, -37, -31]] 
 ![![19, 0, 0], ![3, 1, 0], ![10, 0, 1]] where
  M :=![![![54, -37, -31], ![3745, 550, -142], ![5940, 2018, 513]]]
  hmulB := by decide  
  f := ![![![568706, -43577, 22304]], ![![-55713, 4269, -2185]], ![![525130, -40238, 20595]]]
  g := ![![![25, -37, -31], ![185, 550, -142], ![-276, 2018, 513]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![-568706, 43577, -22304]] ![![54, -37, -31]]
  ![![19, 0, 0]] where
 M := ![![![-19, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 0, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-7, 0, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![16, 0, 1]] where
  M :=![![![-7, 0, 1], ![-122, -23, 1], ![-46, -46, -23]]]
  hmulB := by decide  
  f := ![![![25, -2, 1]], ![![-124, 9, -5]], ![![26, -2, 1]]]
  g := ![![![-1, 0, 1], ![-6, -1, 1], ![14, -2, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [5, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 22], [0, 1]]
 g := ![![[10, 13], [11, 2], [22, 16], [1]], ![[4, 10], [3, 21], [4, 7], [1]]]
 h' := ![![[19, 22], [14, 17], [5, 18], [18, 19], [0, 1]], ![[0, 1], [15, 6], [2, 5], [11, 4], [19, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [1, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [5, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3102, -1840, -513]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![222, -80, -513]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25, 2, -1]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![-25, 2, -1]] 
 ![![23, 0, 0], ![22, 1, 0], ![0, 0, 1]] where
  M :=![![![-25, 2, -1], ![124, -9, 5], ![-198, 14, -7]]]
  hmulB := by decide  
  f := ![![![7, 0, -1]], ![![12, 1, -1]], ![![2, 2, 1]]]
  g := ![![![-3, 2, -1], ![14, -9, 5], ![-22, 14, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-7, 0, 1]] ![![-25, 2, -1]]
  ![![23, 0, 0]] where
 M := ![![![-23, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![2, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![2, 1, 0]] 
 ![![29, 0, 0], ![2, 1, 0], ![28, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![2, 1, 0], ![1, 2, 3], ![-122, -16, 3]]]
  hmulB := by decide  
  f := ![![![-134, -270, -405], ![0, 3915, 0]], ![![-9, -18, -27], ![1, 261, 0]], ![![-130, -261, -391], ![9, 3780, 0]]]
  g := ![![![1, 0, 0], ![-2, 29, 0], ![-28, 0, 29]], ![![0, 1, 0], ![-3, 2, 3], ![-6, -16, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![13, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![13, 1, 0]] 
 ![![29, 0, 0], ![13, 1, 0], ![2, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![13, 1, 0], ![1, 13, 3], ![-122, -16, 14]]]
  hmulB := by decide  
  f := ![![![121, 2568, 594], ![174, -5742, 0]], ![![49, 1141, 264], ![88, -2552, 0]], ![![7, 177, 41], ![15, -396, 0]]]
  g := ![![![1, 0, 0], ![-13, 29, 0], ![-2, 0, 29]], ![![0, 1, 0], ![-6, 13, 3], ![2, -16, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![2, 1, 0]] ![![29, 0, 0], ![13, 1, 0]]
  ![![29, 0, 0], ![9, 5, 1]] where
 M := ![![![841, 0, 0], ![377, 29, 0]], ![![58, 29, 0], ![27, 15, 3]]]
 hmul := by decide  
 g := ![![![![20, -5, -1], ![29, 0, 0]], ![![4, -4, -1], ![29, 0, 0]]], ![![![-7, -4, -1], ![29, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![9, 5, 1]] ![![29, 0, 0], ![13, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![377, 29, 0]], ![![261, 145, 29], ![0, 58, 29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![13, 1, 0]]], ![![![9, 5, 1]], ![![0, 2, 1]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N1, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N1
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5445467, -417258, 213565]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![5445467, -417258, 213565]] 
 ![![31, 0, 0], ![0, 31, 0], ![27, 21, 1]] where
  M :=![![![5445467, -417258, 213565], ![-26472188, 2028427, -1038209], ![41081486, -3147862, 1611169]]]
  hmulB := by decide  
  f := ![![![1355, 212, -43]], ![![5458, 2043, 593]], ![![4107, 1523, 437]]]
  g := ![![![-10348, -158133, 213565], ![50305, 768736, -1038209], ![-78067, -1192981, 1611169]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [19, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 30], [0, 1]]
 g := ![![[6, 18], [11, 2], [17, 20], [10, 1]], ![[0, 13], [0, 29], [0, 11], [20, 30]]]
 h' := ![![[10, 30], [8, 24], [18, 23], [27, 19], [0, 1]], ![[0, 1], [0, 7], [0, 8], [0, 12], [10, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [3, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [19, 21, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4661, -4600, -1710]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1339, 1010, -1710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1355, -212, 43]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![-1355, -212, 43]] 
 ![![31, 0, 0], ![29, 1, 0], ![30, 0, 1]] where
  M :=![![![-1355, -212, 43], ![-5458, -2043, -593], ![23886, 1414, -2255]]]
  hmulB := by decide  
  f := ![![![-5445467, 417258, -213565]], ![![-4240205, 324905, -166296]], ![![-6595016, 505342, -258649]]]
  g := ![![![113, -212, 43], ![2309, -2043, -593], ![1630, 1414, -2255]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![5445467, -417258, 213565]] ![![-1355, -212, 43]]
  ![![31, 0, 0]] where
 M := ![![![-31, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB197I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB197I0 : PrimesBelowBoundCertificateInterval O 1 31 197 where
  m := 11
  g := ![3, 2, 3, 1, 2, 2, 1, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB197I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0, I11N1]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N1, I29N1]
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
    · exact ![3, 9]
    · exact ![5, 5, 5]
    · exact ![343]
    · exact ![121, 11]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
    · exact ![529, 23]
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
      exact NI2N0
      exact NI2N0
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N0
    · dsimp ; intro j
      fin_cases j
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
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I11N0, I11N1, I13N0, I13N1, I19N1, I23N1, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0, I5N0, I5N0], [], [I11N0, I11N1], [I13N0, I13N1], [], [I19N1], [I23N1], [I29N0, I29N1, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
