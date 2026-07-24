
import IdealArithmetic.Examples.NF3_1_466627_1.RI3_1_466627_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-69, -7, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-69, -7, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-69, -7, 1], ![412, 38, -6], ![-2472, -230, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![35, 4, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 2]], ![![-35, -4, 1], ![209, 22, -6], ![-1252, -131, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 2 2 1 [1, 1, 1] where
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

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 2
  hpos := by decide
  P := [1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1235, 3389, 961]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1098, 1214, 961]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 1], ![412, 107, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 0, 1], ![206, 107, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-69, -7, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-138, -14, 2], ![412, 38, -6]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-69, -7, 1]], ![![206, 19, -3]]]]
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
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-68, -6, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-68, -6, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-68, -6, 1], ![412, 39, -5], ![-2060, -123, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![23, 2, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, 0, 3]], ![![-23, -2, 1], ![139, 13, -5], ![-698, -41, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 2], [0, 1]]
 g := ![![[0, 1]], ![[0, 2]]]
 h' := ![![[0, 2], [0, 1]], ![[0, 1], [0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3685, 177, 235]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1150, 59, 235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![0, -1, 1], ![412, 107, 0]]]
  hmulB := by decide  
  f := ![![![2, 1, -2], ![3, 6, 0]], ![![1, 1, -1], ![1, 3, 0]], ![![1, 1, -1], ![1, 4, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![0, -1, 1], ![66, 107, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-68, -6, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-204, -18, 3], ![480, 45, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![-68, -6, 1]], ![![160, 15, -2]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-71, -8, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-71, -8, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 2, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-71, -8, 1], ![412, 36, -7], ![-2884, -337, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![15, 2, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -2, 5]], ![![-15, -2, 1], ![88, 10, -7], ![-600, -79, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 4], [0, 1]]
 g := ![![[1, 4], [1]], ![[4, 1], [1]]]
 h' := ![![[2, 4], [2, 2], [0, 1]], ![[0, 1], [1, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1243, 4034, 952]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-513, 426, 952]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![0, 2, 1], ![412, 107, 3]]]
  hmulB := by decide  
  f := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]], ![![-1, -1, 0], ![3, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-1, 0, 5]], ![![0, 1, 0], ![-1, 2, 1], ![39, 107, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-71, -8, 1]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![-355, -40, 5], ![270, 20, -5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![2, 1, 0]]], ![![![-71, -8, 1]], ![![54, 4, -1]]]]
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
 ![![7, 0, 0], ![2, 1, 0], ![3, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![0, 2, 1], ![412, 107, 3]]]
  hmulB := by decide  
  f := ![![![5, 2, 0], ![-14, 0, 0]], ![![-2, -1, 0], ![8, 0, 0]], ![![1, 0, 0], ![-2, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-3, 0, 7]], ![![0, 1, 0], ![-1, 2, 1], ![27, 107, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0], ![-66, -10, 1]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![4, 4, 1]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![2, 1, 0], ![0, 0, 0]], ![![10, 2, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-66, -10, 1]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![-462, -70, 7], ![280, 21, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![2, 1, 0]]], ![![![-66, -10, 1]], ![![40, 3, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-5, 1, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-5, 1, 0]] 
 ![![11, 0, 0], ![6, 1, 0], ![8, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-5, 1, 0], ![0, -5, 1], ![412, 107, -4]]]
  hmulB := by decide  
  f := ![![![56, -11, 0], ![121, 0, 0]], ![![36, -7, 0], ![78, 0, 0]], ![![38, -7, 0], ![82, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 11, 0], ![-8, 0, 11]], ![![-1, 1, 0], ![2, -5, 1], ![-18, 107, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-4, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-4, 1, 0]] 
 ![![11, 0, 0], ![7, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-4, 1, 0], ![0, -4, 1], ![412, 107, -3]]]
  hmulB := by decide  
  f := ![![![21, -5, 0], ![55, 0, 0]], ![![17, -4, 0], ![45, 0, 0]], ![![10, -2, 0], ![26, 1, 0]]]
  g := ![![![1, 0, 0], ![-7, 11, 0], ![-6, 0, 11]], ![![-1, 1, 0], ![2, -4, 1], ![-29, 107, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![0, -3, 1], ![412, 107, -2]]]
  hmulB := by decide  
  f := ![![![19, -6, 0], ![66, 0, 0]], ![![16, -5, 0], ![56, 0, 0]], ![![4, -1, 0], ![14, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-2, 0, 11]], ![![-1, 1, 0], ![2, -3, 1], ![-40, 107, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-5, 1, 0]] ![![11, 0, 0], ![-4, 1, 0]]
  ![![11, 0, 0], ![-68, -9, 1]] where
 M := ![![![121, 0, 0], ![-44, 11, 0]], ![![-55, 11, 0], ![20, -9, 1]]]
 hmul := by decide  
 g := ![![![![11, 0, 0], ![0, 0, 0]], ![![64, 10, -1], ![11, 0, 0]]], ![![![63, 10, -1], ![11, 0, 0]], ![![8, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![-68, -9, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-748, -99, 11], ![616, 66, -11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-3, 1, 0]]], ![![![-68, -9, 1]], ![![56, 6, -1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-75, -11, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-75, -11, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![3, 2, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-75, -11, 1], ![412, 32, -10], ![-4120, -658, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -2, 13]], ![![-6, -1, 1], ![34, 4, -10], ![-322, -54, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 12], [0, 1]]
 g := ![![[8, 4], [9], [4, 1]], ![[11, 9], [9], [8, 12]]]
 h' := ![![[4, 12], [2, 11], [2, 10], [0, 1]], ![[0, 1], [7, 2], [3, 3], [4, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1242, 724, 102]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![72, 40, 102]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-3, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-3, 1, 0]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-3, 1, 0], ![0, -3, 1], ![412, 107, -2]]]
  hmulB := by decide  
  f := ![![![34, -11, 0], ![143, 0, 0]], ![![28, -9, 0], ![118, 0, 0]], ![![10, -3, 0], ![42, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 13, 0], ![-4, 0, 13]], ![![-1, 1, 0], ![2, -3, 1], ![-50, 107, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-75, -11, 1]] ![![13, 0, 0], ![-3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-39, 13, 0]], ![![-975, -143, 13], ![637, 65, -13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-3, 1, 0]]], ![![![-75, -11, 1]], ![![49, 5, -1]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-65, -11, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-65, -11, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![3, 6, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-65, -11, 1], ![412, 42, -10], ![-4120, -658, 32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -6, 17]], ![![-4, -1, 1], ![26, 6, -10], ![-248, -50, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [4, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 16], [0, 1]]
 g := ![![[12, 13], [9], [9], [1]], ![[0, 4], [9], [9], [1]]]
 h' := ![![[3, 16], [7, 9], [14, 3], [13, 3], [0, 1]], ![[0, 1], [0, 8], [6, 14], [5, 14], [3, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [2, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [4, 14, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16087, 4889, 523]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![854, 103, 523]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-7, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-7, 1, 0]] 
 ![![17, 0, 0], ![10, 1, 0], ![2, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-7, 1, 0], ![0, -7, 1], ![412, 107, -6]]]
  hmulB := by decide  
  f := ![![![64, -9, 0], ![153, 0, 0]], ![![36, -5, 0], ![86, 0, 0]], ![![10, -1, 0], ![24, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 17, 0], ![-2, 0, 17]], ![![-1, 1, 0], ![4, -7, 1], ![-38, 107, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-65, -11, 1]] ![![17, 0, 0], ![-7, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-119, 17, 0]], ![![-1105, -187, 17], ![867, 119, -17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-7, 1, 0]]], ![![![-65, -11, 1]], ![![51, 7, -1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-77, -14, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-77, -14, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![18, 5, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-77, -14, 1], ![412, 30, -13], ![-5356, -979, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -5, 19]], ![![-5, -1, 1], ![34, 5, -13], ![-298, -56, 17]]]
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
  c := ![-2064, -111, 107]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-210, -34, 107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-6, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-6, 1, 0]] 
 ![![19, 0, 0], ![13, 1, 0], ![2, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-6, 1, 0], ![0, -6, 1], ![412, 107, -5]]]
  hmulB := by decide  
  f := ![![![109, -18, 0], ![342, 0, 0]], ![![79, -13, 0], ![248, 0, 0]], ![![14, -2, 0], ![44, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 19, 0], ![-2, 0, 19]], ![![-1, 1, 0], ![4, -6, 1], ![-51, 107, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-77, -14, 1]] ![![19, 0, 0], ![-6, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-114, 19, 0]], ![![-1463, -266, 19], ![874, 114, -19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-6, 1, 0]]], ![![![-77, -14, 1]], ![![46, 6, -1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-77, -18, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-77, -18, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![15, 5, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-77, -18, 1], ![412, 30, -17], ![-7004, -1407, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -5, 23]], ![![-4, -1, 1], ![29, 5, -17], ![-313, -64, 13]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [6, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 22], [0, 1]]
 g := ![![[14, 4], [5, 8], [2, 18], [1]], ![[0, 19], [0, 15], [8, 5], [1]]]
 h' := ![![[8, 22], [16, 21], [11, 13], [17, 8], [0, 1]], ![[0, 1], [0, 2], [0, 10], [12, 15], [8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [14, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [6, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3302, 2519, 467]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-161, 8, 467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-6, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-6, 1, 0]] 
 ![![23, 0, 0], ![17, 1, 0], ![10, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-6, 1, 0], ![0, -6, 1], ![412, 107, -5]]]
  hmulB := by decide  
  f := ![![![37, -6, 0], ![138, 0, 0]], ![![31, -5, 0], ![116, 0, 0]], ![![26, -4, 0], ![98, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 23, 0], ![-10, 0, 23]], ![![-1, 1, 0], ![4, -6, 1], ![-59, 107, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-77, -18, 1]] ![![23, 0, 0], ![-6, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-138, 23, 0]], ![![-1771, -414, 23], ![874, 138, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-6, 1, 0]]], ![![![-77, -18, 1]], ![![38, 6, -1]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-70, -16, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-70, -16, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![17, 13, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-70, -16, 1], ![412, 37, -15], ![-6180, -1193, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -13, 29]], ![![-3, -1, 1], ![23, 8, -15], ![-226, -51, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [18, 2, 1] where
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
 g := ![![[13, 9], [28], [21, 22], [27, 1]], ![[24, 20], [28], [6, 7], [25, 28]]]
 h' := ![![[27, 28], [19, 26], [28, 17], [7, 15], [0, 1]], ![[0, 1], [25, 3], [23, 12], [6, 14], [27, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [6, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [18, 2, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14806, -2264, 504]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-806, -304, 504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-14, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-14, 1, 0]] 
 ![![29, 0, 0], ![15, 1, 0], ![7, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-14, 1, 0], ![0, -14, 1], ![412, 107, -13]]]
  hmulB := by decide  
  f := ![![![407, -29, 0], ![841, 0, 0]], ![![225, -16, 0], ![465, 0, 0]], ![![105, -7, 0], ![217, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 29, 0], ![-7, 0, 29]], ![![-1, 1, 0], ![7, -14, 1], ![-38, 107, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-70, -16, 1]] ![![29, 0, 0], ![-14, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-406, 29, 0]], ![![-2030, -464, 29], ![1392, 261, -29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-14, 1, 0]]], ![![![-70, -16, 1]], ![![48, 9, -1]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [26, 14, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 11, 22], [10, 19, 9], [0, 1]]
 g := ![![[30, 8, 10], [8, 4, 14], [7, 16, 25], [1]], ![[27, 18, 14, 21], [7, 15, 4, 26], [17, 23, 16, 11], [15, 27, 20, 15]], ![[12, 20, 12, 9], [21, 7, 11, 4], [0, 30, 13, 16], [12, 5, 16, 16]]]
 h' := ![![[26, 11, 22], [9, 17, 17], [4, 7, 13], [5, 17, 5], [0, 1]], ![[10, 19, 9], [26, 18, 15], [16, 28, 29], [12, 6, 4], [26, 11, 22]], ![[0, 1], [26, 27, 30], [19, 27, 20], [6, 8, 22], [10, 19, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 9], []]
 b := ![[], [27, 11, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [26, 14, 26, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105679, 95759, 19189]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3409, 3089, 619]
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



lemma PB194I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB194I0 : PrimesBelowBoundCertificateInterval O 1 31 194 where
  m := 11
  g := ![2, 2, 2, 3, 3, 2, 2, 2, 2, 2, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB194I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N0, I7N0]
    · exact ![I11N0, I11N1, I11N2]
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
    · exact ![4, 2]
    · exact ![9, 3]
    · exact ![25, 5]
    · exact ![7, 7, 7]
    · exact ![11, 11, 11]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
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
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I11N0, I11N1, I11N2, I13N0, I13N1, I17N1, I19N1, I23N1, I29N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N0], [I11N0, I11N1, I11N2], [I13N0, I13N1], [I17N1], [I19N1], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
