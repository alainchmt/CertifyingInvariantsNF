
import IdealArithmetic.Examples.NF3_1_45227_1.RI3_1_45227_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, 0, 3], ![7, -16, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -3], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-1, 0, 3], ![3, -16, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![12, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![12, 1, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![0, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![12, 1, 1], ![8, -4, 4], ![4, -19, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![-12, 0, -1], ![2, 0, 0]], ![![-6, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -1, 2]], ![![6, 0, 1], ![4, -4, 4], ![2, -8, -3]]]
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
  c := ![-332, 291, -765]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-166, 528, -765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![12, 1, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![24, 2, 2]], ![![0, 2, 0], ![8, -4, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![12, 1, 1]]], ![![![0, 1, 0]], ![![4, -2, 2]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![1, 1, 3], ![7, -16, 2]]]
  hmulB := by decide  
  f := ![![![8, -16, 2], ![0, 0, -3]], ![![0, 0, 0], ![1, 0, 0]], ![![2, -6, 1], ![2, 0, -1]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-1, 1, 3], ![7, -16, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![12, 0, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![12, 0, 1]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![12, 0, 1], ![7, -4, 1], ![-3, -3, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![4, 3, 0], ![-2, 2, 0]], ![![-4, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![4, 0, 1], ![5, -4, 1], ![1, -3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-11, 1, -1]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-11, 1, -1]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-11, 1, -1], ![-6, 5, 2], ![10, -13, 6]]]
  hmulB := by decide  
  f := ![![![7, -5, -2], ![0, 3, 0]], ![![10, -2, 0], ![2, 1, 0]], ![![6, -2, 0], ![1, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-1, 0, 3]], ![![-4, 1, -1], ![-6, 5, 2], ![10, -13, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![12, 0, 1]]
  ![![3, 0, 0], ![11, 1, 1]] where
 M := ![![![9, 0, 0], ![36, 0, 3]], ![![3, 3, 0], ![19, -4, 2]]]
 hmul := by decide  
 g := ![![![![-8, -1, -1], ![3, 0, 0]], ![![-10, -2, -1], ![6, 0, 0]]], ![![![-10, 0, -1], ![3, 0, 0]], ![![-1, -2, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![11, 1, 1]] ![![3, 0, 0], ![-11, 1, -1]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-33, 3, -3]], ![![33, 3, 3], ![-117, 3, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-11, 1, -1]]], ![![![11, 1, 1]], ![![-39, 1, -1]]]]
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
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![11, -2, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![11, -2, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 3, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![11, -2, 1], ![5, -5, -5], ![-17, 29, -7]]]
  hmulB := by decide  
  f := ![![![-10, 2, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -3, 5]], ![![2, -1, 1], ![2, 2, -5], ![-2, 10, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 4], [0, 1]]
 g := ![![[2, 1], [1]], ![[3, 4], [1]]]
 h' := ![![[1, 4], [3, 1], [0, 1]], ![[0, 1], [4, 4], [1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [2, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-49349, -47417, -258329]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41796, 145514, -258329]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![1, 0, 3], ![7, -16, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -3], ![0, 5, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 2, 0]]]
  g := ![![![1, 0, 0], ![0, 5, 0], ![-2, 0, 5]], ![![0, 1, 0], ![-1, 0, 3], ![1, -16, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![11, -2, 1]] ![![5, 0, 0], ![0, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![55, -10, 5], ![5, -5, -5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![0, 1, 0]]], ![![![11, -2, 1]], ![![1, -1, -1]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![1, 2, 3], ![7, -16, 3]]]
  hmulB := by decide  
  f := ![![![-13, -31, -48], ![-7, 112, 0]], ![![-4, -8, -12], ![1, 28, 0]], ![![-12, -27, -41], ![-3, 96, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-6, 0, 7]], ![![0, 1, 0], ![-3, 2, 3], ![3, -16, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0], ![11, -1, 1]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![5, 4, 3]]]
 hmul := by decide  
 g := ![![![![-4, 1, -1], ![7, 0, 0]], ![![-9, 2, -1], ![7, 0, 0]]], ![![![-9, 2, -1], ![7, 0, 0]], ![![-4, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![11, -1, 1]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![77, -7, 7], ![28, -7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![2, 1, 0]]], ![![![11, -1, 1]], ![![4, -1, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0]] 
 ![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 9, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 5, 4], [8, 5, 7], [0, 1]]
 g := ![![[8, 6, 4], [3, 10, 1], []], ![[8, 4, 8, 5], [5, 4, 1, 1], [2, 5]], ![[1, 10], [10, 6, 3, 10], [10, 5]]]
 h' := ![![[2, 5, 4], [9, 3, 9], [0, 0, 1], [0, 1]], ![[8, 5, 7], [6, 3, 2], [10, 6, 5], [2, 5, 4]], ![[0, 1], [10, 5], [6, 5, 5], [8, 5, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 5], []]
 b := ![[], [10, 3, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 9, 1, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24750, 4037, -84579]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2250, 367, -7689]
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


def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -7, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![3, -7, 0]] 
 ![![13, 0, 0], ![7, 1, 0], ![10, 0, 1]] where
  M :=![![![3, -7, 0], ![-7, 3, -21], ![-49, 112, -4]]]
  hmulB := by decide  
  f := ![![![2340, -28, 147]], ![![1337, -16, 84]], ![![1751, -21, 110]]]
  g := ![![![4, -7, 0], ![14, 3, -21], ![-61, 112, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![411841, -4935, 25872]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![411841, -4935, 25872]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![411841, -4935, 25872], ![176169, -2111, 11067], ![-112161, 1344, -7046]]]
  hmulB := by decide  
  f := ![![![58, -42, 147]], ![![125, -212, 126]], ![![-3, -21, -44]]]
  g := ![![![11974, -4935, 25872], ![5122, -2111, 11067], ![-3261, 1344, -7046]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![3, -7, 0]] ![![3, -7, 0]]
  ![![58, -42, 147]] where
 M := ![![![58, -42, 147]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI13N1 : IdealMulLeCertificate' Table 
  ![![58, -42, 147]] ![![411841, -4935, 25872]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N0, I13N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N0
    exact isPrimeI13N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![9, -4, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![9, -4, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![9, 13, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![9, -4, 1], ![3, -7, -11], ![-31, 61, -11]]]
  hmulB := by decide  
  f := ![![![-8, 4, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -13, 17]], ![![0, -1, 1], ![6, 8, -11], ![4, 12, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [11, 2, 1] where
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
 g := ![![[11, 2], [4], [4], [1]], ![[7, 15], [4], [4], [1]]]
 h' := ![![[15, 16], [3, 11], [9, 2], [6, 15], [0, 1]], ![[0, 1], [15, 6], [5, 15], [10, 2], [15, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [6, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [11, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![26, -123, -135]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73, 96, -135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![11, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![1, -6, 3], ![7, -16, -5]]]
  hmulB := by decide  
  f := ![![![125, -919, 462], ![-85, -2618, 0]], ![![82, -591, 297], ![-50, -1683, 0]], ![![83, -595, 299], ![-49, -1694, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-11, 0, 17]], ![![-1, 1, 0], ![2, -6, 3], ![14, -16, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![9, -4, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![153, -68, 17], ![-51, 17, -17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-6, 1, 0]]], ![![![9, -4, 1]], ![![-3, 1, -1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, -9, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, -9, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![3, 10, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, -9, 1], ![-2, -13, -26], ![-66, 141, -22]]]
  hmulB := by decide  
  f := ![![![-2, 9, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -10, 19]], ![![0, -1, 1], ![4, 13, -26], ![0, 19, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [4, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 18], [0, 1]]
 g := ![![[2, 5], [18, 7], [7], [1]], ![[0, 14], [0, 12], [7], [1]]]
 h' := ![![[11, 18], [4, 10], [7, 8], [15, 11], [0, 1]], ![[0, 1], [0, 9], [0, 11], [3, 8], [11, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [3, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [4, 8, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1640, -2887, 933]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-61, -643, 933]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![7, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![7, 1, 0]] 
 ![![19, 0, 0], ![7, 1, 0], ![3, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![7, 1, 0], ![1, 7, 3], ![7, -16, 8]]]
  hmulB := by decide  
  f := ![![![-47, -384, -165], ![-19, 1045, 0]], ![![-20, -140, -60], ![1, 380, 0]], ![![-10, -61, -26], ![4, 165, 0]]]
  g := ![![![1, 0, 0], ![-7, 19, 0], ![-3, 0, 19]], ![![0, 1, 0], ![-3, 7, 3], ![5, -16, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![3, -9, 1]] ![![19, 0, 0], ![7, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![133, 19, 0]], ![![57, -171, 19], ![19, -76, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![7, 1, 0]]], ![![![3, -9, 1]], ![![1, -4, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![9, 7, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![9, 7, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![9, 7, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![9, 7, 1], ![14, -7, 22], ![46, -115, 0]]]
  hmulB := by decide  
  f := ![![![-8, -7, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -7, 23]], ![![0, 0, 1], ![-8, -7, 22], ![2, -5, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [19, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 22], [0, 1]]
 g := ![![[6, 1], [8, 13], [9, 1], [1]], ![[7, 22], [21, 10], [10, 22], [1]]]
 h' := ![![[1, 22], [9, 22], [13, 6], [4, 1], [0, 1]], ![[0, 1], [8, 1], [19, 17], [5, 22], [1, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [19, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [19, 22, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-297, 459, -493]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![180, 170, -493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![1, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![1, 1, 0]] 
 ![![23, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![1, 1, 0], ![1, 1, 3], ![7, -16, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![23, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![-8, 8, 0]]]
  g := ![![![1, 0, 0], ![-1, 23, 0], ![0, 0, 23]], ![![0, 1, 0], ![0, 1, 3], ![1, -16, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![9, 7, 1]] ![![23, 0, 0], ![1, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![23, 23, 0]], ![![207, 161, 23], ![23, 0, 23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![1, 1, 0]]], ![![![9, 7, 1]], ![![1, 0, 1]]]]
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [27, 26, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 22, 27], [11, 6, 2], [0, 1]]
 g := ![![[18, 1, 22], [23, 1], [6, 24, 5], [1]], ![[20, 2, 3, 3], [26, 1], [23, 25, 4, 14], [22, 12, 4, 21]], ![[16, 13, 19, 3], [11, 4], [12, 14, 22, 3], [23, 26, 13, 8]]]
 h' := ![![[7, 22, 27], [16, 11, 15], [12, 12, 28], [2, 3, 18], [0, 1]], ![[11, 6, 2], [0, 28, 10], [21, 25, 28], [10, 18, 15], [7, 22, 27]], ![[0, 1], [18, 19, 4], [5, 21, 2], [14, 8, 25], [11, 6, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 19], []]
 b := ![[], [15, 20, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [27, 26, 11, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6989, 42833, 41412]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-241, 1477, 1428]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [30, 11, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 27, 22], [15, 3, 9], [0, 1]]
 g := ![![[11, 8, 4], [27, 9, 18], [4, 16, 25], [1]], ![[0, 28, 30, 23], [22, 1, 27, 23], [29, 28, 10, 15], [12, 26, 7, 15]], ![[8, 17, 0, 7], [8, 26, 8, 5], [1, 25, 28, 28], [5, 2, 29, 16]]]
 h' := ![![[11, 27, 22], [27, 7, 2], [4, 4, 24], [1, 20, 26], [0, 1]], ![[15, 3, 9], [21, 30, 5], [13, 29, 5], [10, 23, 22], [11, 27, 22]], ![[0, 1], [4, 25, 24], [16, 29, 2], [1, 19, 14], [15, 3, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 24], []]
 b := ![[], [0, 6, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [30, 11, 5, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24025, -93000, -234360]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-775, -3000, -7560]
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



lemma PB61I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB61I0 : PrimesBelowBoundCertificateInterval O 1 31 61 where
  m := 11
  g := ![2, 3, 2, 3, 1, 3, 2, 2, 2, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB61I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0]
    · exact ![I13N0, I13N0, I13N1]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![1331]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![529, 23]
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
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N0
      exact NI7N0
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
  β := ![I2N0, I2N1, I3N0, I3N1, I3N2, I5N0, I5N1, I7N0, I13N0, I13N1, I17N1, I19N1, I23N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1, I3N2], [I5N0, I5N1], [I7N0, I7N0, I7N0], [], [I13N0, I13N0, I13N1], [I17N1], [I19N1], [I23N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
