
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 1, 2], ![152, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![76, 0, 0], ![0, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![0, 1, 2], ![76, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 1], ![152, 2, 1], ![0, 76, 1]]]
  hmulB := by decide  
  f := ![![![130, -21, -22], ![46, -2, 0]], ![![65, -10, -11], ![23, -1, 0]], ![![-65, 10, 11], ![-22, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 1, 1], ![75, 2, 1], ![-38, 76, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 0, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 0, 1], ![152, 1, -1], ![-152, 76, 2]]]
  hmulB := by decide  
  f := ![![![0, 0, -1], ![2, 0, 0]], ![![-63, 0, 13], ![-25, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 0, 1], ![76, 1, -1], ![-115, 76, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 1, 1]]
  ![![2, 0, 0], ![0, 0, 1]] where
 M := ![![![4, 0, 0], ![2, 2, 2]], ![![0, 2, 0], ![152, 2, 1]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![2, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 1, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 0, 1]] ![![2, 0, 0], ![1, 0, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 0, 2]], ![![0, 0, 2], ![-152, 76, 2]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 0, 1]]], ![![![0, 0, 1]], ![![-76, 38, 1]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N2
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


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [2, 2, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1], [2, 1], [0, 1]]
 g := ![![[1]], ![[1]], ![[1]]]
 h' := ![![[1, 1], [0, 1]], ![[2, 1], [1, 1]], ![[0, 1], [2, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], []]
 b := ![[], [1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [2, 2, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-312966, -3432, -2067]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104322, -1144, -689]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 2, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 2, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![4, 2, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 2, 1], ![152, 1, 3], ![152, 76, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -2, 5]], ![![-1, 0, 1], ![28, -1, 3], ![32, 16, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [4, 3, 1] where
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
 g := ![![[2, 4], [1]], ![[0, 1], [1]]]
 h' := ![![[2, 4], [1, 2], [0, 1]], ![[0, 1], [0, 3], [2, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [4, 3, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1214, 1218, 14]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-254, 238, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![0, 3, 2], ![152, 0, 1]]]
  hmulB := by decide  
  f := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]], ![![-2, -3, -1], ![6, 3, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![-2, 0, 5]], ![![0, 1, 0], ![-2, 3, 2], ![30, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-1, 2, 1]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![-5, 10, 5], ![150, 5, 5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![2, 1, 0]]], ![![![-1, 2, 1]], ![![30, 1, 1]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 2, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![4, 2, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 2, 1], ![152, -1, 3], ![152, 76, -4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -2, 7]], ![![-1, 0, 1], ![20, -1, 3], ![24, 12, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6], [0, 1]]
 g := ![![[0, 4], [0, 1]], ![[0, 3], [0, 6]]]
 h' := ![![[0, 6], [0, 5], [0, 1]], ![[0, 1], [0, 2], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [0, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3946, 76, 129]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![490, -26, 129]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![0, -2, 2], ![152, 0, -4]]]
  hmulB := by decide  
  f := ![![![22, -7, 0], ![49, 0, 0]], ![![10, -3, 0], ![22, 0, 0]], ![![10, -2, -1], ![22, 4, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-4, 0, 7]], ![![-1, 1, 0], ![0, -2, 2], ![24, 0, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-3, 2, 1]] ![![7, 0, 0], ![-3, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-21, 7, 0]], ![![-21, 14, 7], ![161, -7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-3, 1, 0]]], ![![![-3, 2, 1]], ![![23, -1, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [9, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 3, 6], [10, 7, 5], [0, 1]]
 g := ![![[5, 3, 5], [9, 9, 1], []], ![[4, 3, 5, 2], [0, 8, 4, 8], [8, 3]], ![[0, 6, 4, 4], [10, 1, 5, 1], [9, 3]]]
 h' := ![![[10, 3, 6], [7, 8, 7], [0, 0, 1], [0, 1]], ![[10, 7, 5], [8, 7, 9], [6, 7, 7], [10, 3, 6]], ![[0, 1], [0, 7, 6], [8, 4, 3], [10, 7, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 4], []]
 b := ![[], [8, 3, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [9, 6, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1444894, 2266, 5665]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-131354, 206, 515]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29899, -580, 1730]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-29899, -580, 1730]] 
 ![![13, 0, 0], ![0, 13, 0], ![1, 5, 1]] where
  M :=![![![-29899, -580, 1730], ![262960, -30479, -2890], ![-351120, 131480, -27589]]]
  hmulB := by decide  
  f := ![![![-93912487, -16266060, -4184990]], ![![-636118480, -110178547, -28347130]], ![![-393140579, -68093695, -17519389]]]
  g := ![![![-2433, -710, 1730], ![20450, -1233, -2890], ![-24887, 20725, -27589]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [5, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 12], [0, 1]]
 g := ![![[11, 10], [3], [10, 1]], ![[7, 3], [3], [7, 12]]]
 h' := ![![[10, 12], [2, 7], [2, 4], [0, 1]], ![[0, 1], [7, 6], [3, 9], [10, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [5, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![60657, 34016, 506]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4627, 2422, 506]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-93912487, -16266060, -4184990]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![-93912487, -16266060, -4184990]] 
 ![![13, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![-93912487, -16266060, -4184990], ![-636118480, -110178547, -28347130], ![-1836322640, -318059240, -81831417]]]
  hmulB := by decide  
  f := ![![![-29899, -580, 1730]], ![![11028, -2523, 310]], ![![-33909, 9980, -1723]]]
  g := ![![![-1253329, -16266060, -4184990], ![-8489454, -110178547, -28347130], ![-24507033, -318059240, -81831417]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-29899, -580, 1730]] ![![-93912487, -16266060, -4184990]]
  ![![13, 0, 0]] where
 M := ![![![13, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [8, 12, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 4, 7], [6, 12, 10], [0, 1]]
 g := ![![[1], [7, 13], [15, 1], []], ![[4, 16, 4, 3], [9, 1], [14, 8], [9, 15]], ![[3, 14, 2, 14], [6, 13], [9, 16], [6, 15]]]
 h' := ![![[9, 4, 7], [13, 1], [16, 16, 9], [0, 0, 1], [0, 1]], ![[6, 12, 10], [5, 4, 7], [3, 3, 16], [9, 14, 12], [9, 4, 7]], ![[0, 1], [2, 12, 10], [4, 15, 9], [5, 3, 4], [6, 12, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 16], []]
 b := ![[], [0, 13, 5], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [8, 12, 2, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12461, 1394, 697]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![733, 82, 41]
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
 ![![19, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![0, 1, 2], ![152, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![9, 10, 0]]]
  g := ![![![1, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![0, 1, 2], ![8, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![1, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![1, 1, 0]] 
 ![![19, 0, 0], ![1, 1, 0], ![18, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![1, 1, 0], ![0, 2, 2], ![152, 0, 0]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![19, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -2, -1], ![18, 10, 0]]]
  g := ![![![1, 0, 0], ![-1, 19, 0], ![-18, 0, 19]], ![![0, 1, 0], ![-2, 2, 2], ![8, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-1, 1, 0]] 
 ![![19, 0, 0], ![18, 1, 0], ![0, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-1, 1, 0], ![0, 0, 2], ![152, 0, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 10, 0]]]
  g := ![![![1, 0, 0], ![-18, 19, 0], ![0, 0, 19]], ![![-1, 1, 0], ![0, 0, 2], ![8, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 0]] ![![19, 0, 0], ![1, 1, 0]]
  ![![19, 0, 0], ![0, 1, 1]] where
 M := ![![![361, 0, 0], ![19, 19, 0]], ![![0, 19, 0], ![0, 2, 2]]]
 hmul := by decide  
 g := ![![![![-5, 0, 0], ![-3, 3, 0]], ![![1, 0, -1], ![19, 0, 0]]], ![![![0, 0, -1], ![19, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 1]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-19, 19, 0]], ![![0, 19, 19], ![152, 0, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-1, 1, 0]]], ![![![0, 1, 1]], ![![8, 0, 0]]]]
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
instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-11, 3, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-11, 3, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![12, 3, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-11, 3, 1], ![152, -8, 5], ![304, 76, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -3, 23]], ![![-1, 0, 1], ![4, -1, 5], ![20, 5, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [6, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 22], [0, 1]]
 g := ![![[10, 4], [3, 8], [0, 12], [1]], ![[0, 19], [6, 15], [16, 11], [1]]]
 h' := ![![[9, 22], [5, 2], [0, 10], [17, 9], [0, 1]], ![[0, 1], [0, 21], [21, 13], [6, 14], [9, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [6, 14, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![766, 1951, 83]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, 74, 83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-5, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-5, 1, 0]] 
 ![![23, 0, 0], ![18, 1, 0], ![13, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-5, 1, 0], ![0, -4, 2], ![152, 0, -6]]]
  hmulB := by decide  
  f := ![![![81, -16, 0], ![368, 0, 0]], ![![66, -13, 0], ![300, 0, 0]], ![![51, -8, -1], ![232, 12, 0]]]
  g := ![![![1, 0, 0], ![-18, 23, 0], ![-13, 0, 23]], ![![-1, 1, 0], ![2, -4, 2], ![10, 0, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-11, 3, 1]] ![![23, 0, 0], ![-5, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-115, 23, 0]], ![![-253, 69, 23], ![207, -23, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-5, 1, 0]]], ![![![-11, 3, 1]], ![![9, -1, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![2, -5, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![2, -5, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![2, 24, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![2, -5, 1], ![152, -3, -11], ![-912, 76, 8]]]
  hmulB := by decide  
  f := ![![![-1, 5, -1], ![29, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -24, 29]], ![![0, -1, 1], ![6, 9, -11], ![-32, -4, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [4, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 28], [0, 1]]
 g := ![![[25, 22], [23], [12, 23], [16, 1]], ![[0, 7], [23], [3, 6], [3, 28]]]
 h' := ![![[16, 28], [8, 14], [10, 20], [23, 20], [0, 1]], ![[0, 1], [0, 15], [11, 9], [24, 9], [16, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [2, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [4, 13, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9154, 2664, -34]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![318, 120, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![11, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![11, 1, 0]] 
 ![![29, 0, 0], ![11, 1, 0], ![21, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![11, 1, 0], ![0, 12, 2], ![152, 0, 10]]]
  hmulB := by decide  
  f := ![![![45, 4, 0], ![-116, 0, 0]], ![![11, 1, 0], ![-28, 0, 0]], ![![25, -4, -1], ![-64, 15, 0]]]
  g := ![![![1, 0, 0], ![-11, 29, 0], ![-21, 0, 29]], ![![0, 1, 0], ![-6, 12, 2], ![-2, 0, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![2, -5, 1]] ![![29, 0, 0], ![11, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![319, 29, 0]], ![![58, -145, 29], ![174, -58, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![11, 1, 0]]], ![![![2, -5, 1]], ![![6, -2, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-14, 15, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-14, 15, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![17, 15, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-14, 15, 1], ![152, 1, 29], ![2128, 76, -28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -15, 31]], ![![-1, 0, 1], ![-11, -14, 29], ![84, 16, -28]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 30], [0, 1]]
 g := ![![[20, 25], [24, 9], [6, 14], [24, 1]], ![[0, 6], [23, 22], [1, 17], [17, 30]]]
 h' := ![![[24, 30], [4, 5], [1, 28], [4, 13], [0, 1]], ![[0, 1], [0, 26], [22, 3], [6, 18], [24, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [19, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [5, 7, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![113, 76, 34]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -14, 34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![2, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![2, 1, 0]] 
 ![![31, 0, 0], ![2, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![2, 1, 0], ![0, 3, 2], ![152, 0, 1]]]
  hmulB := by decide  
  f := ![![![25, 12, 0], ![-372, 0, 0]], ![![-2, -1, 0], ![32, 0, 0]], ![![24, 10, -1], ![-358, 16, 0]]]
  g := ![![![1, 0, 0], ![-2, 31, 0], ![-28, 0, 31]], ![![0, 1, 0], ![-2, 3, 2], ![4, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-14, 15, 1]] ![![31, 0, 0], ![2, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![62, 31, 0]], ![![-434, 465, 31], ![124, 31, 31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![2, 1, 0]]], ![![![-14, 15, 1]], ![![4, 1, 1]]]]
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


lemma PB224I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB224I0 : PrimesBelowBoundCertificateInterval O 1 31 224 where
  m := 11
  g := ![3, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB224I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N2]
    · exact ![I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1]
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
    · exact ![27]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![19, 19, 19]
    · exact ![529, 23]
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
      exact NI2N2
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
      exact NI19N2
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
      exact NI31N1
  β := ![I2N0, I2N1, I2N2, I3N0, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I19N0, I19N1, I19N2, I23N1, I29N1, I31N1]
  Il := ![[I2N0, I2N1, I2N2], [I3N0], [I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N1], [], [I19N0, I19N1, I19N2], [I23N1], [I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
