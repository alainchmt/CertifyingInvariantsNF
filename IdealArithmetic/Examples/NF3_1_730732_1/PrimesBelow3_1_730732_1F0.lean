
import IdealArithmetic.Examples.NF3_1_730732_1.RI3_1_730732_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![58461, 20445, -1487]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![58461, 20445, -1487]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![58461, 20445, -1487], ![178067, 111993, 39403], ![-2061593, -630443, 132438]]]
  hmulB := by decide  
  f := ![![![39673474463, -1770226169, 972127926]], ![![-32571155931, 1453321479, -798098243]], ![![59311445584, -2646470331, 1453321479]]]
  g := ![![![19008, 20445, -1487], ![33037, 111993, 39403], ![-715575, -630443, 132438]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![58461, 20445, -1487]] ![![58461, 20445, -1487]]
  ![![10123857127, 4422400771, 521727522]] where
 M := ![![![10123857127, 4422400771, 521727522]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![10123857127, 4422400771, 521727522]] ![![58461, 20445, -1487]]
  ![![2, 0, 0]] where
 M := ![![![303744642328658, 373340724355872, 228298231590500]]]
 hmul := by decide  
 g := ![![![![151872321164329, 186670362177936, 114149115795250]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![24, -2, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![24, -2, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 1, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![24, -2, 1], ![-108, -12, -3], ![141, 1, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-8, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -1, 3]], ![![8, -1, 1], ![-36, -3, -3], ![47, 5, -14]]]
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
  c := ![-705, -427, -136]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-235, -97, -136]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![1, 0, 2], ![-106, -36, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -2], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 2, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-1, 0, 2], ![-36, -36, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![24, -2, 1]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![72, -6, 3], ![-108, -12, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![0, 1, 0]]], ![![![24, -2, 1]], ![![-36, -4, -1]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![22, -1, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![22, -1, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 4, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![22, -1, 1], ![-107, -14, -1], ![35, -35, -15]]]
  hmulB := by decide  
  f := ![![![-21, 1, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -4, 5]], ![![4, -1, 1], ![-21, -2, -1], ![13, 5, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 4], [0, 1]]
 g := ![![[], [1]], ![[], [1]]]
 h' := ![![[0, 4], [2], [0, 1]], ![[0, 1], [2], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [3, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![356, -1063, -892]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![428, 501, -892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![1, 1, 2], ![-106, -36, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -1], ![2, 3, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 1, 2], ![-14, -36, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![22, -1, 1]] ![![5, 0, 0], ![1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![110, -5, 5], ![-85, -15, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![1, 1, 0]]], ![![![22, -1, 1]], ![![-17, -3, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![23, -1, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![23, -1, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![2, 6, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![23, -1, 1], ![-107, -13, -1], ![35, -35, -14]]]
  hmulB := by decide  
  f := ![![![-22, 1, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-3, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -6, 7]], ![![3, -1, 1], ![-15, -1, -1], ![9, 7, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
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
 g := ![![[2, 2], [4, 1]], ![[3, 5], [1, 6]]]
 h' := ![![[4, 6], [1, 4], [0, 1]], ![[0, 1], [3, 3], [4, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [6, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-291248, -304651, -148564]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![840, 83819, -148564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![1, 1, 0]] 
 ![![7, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![1, 1, 0], ![1, 1, 2], ![-106, -36, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -1], ![3, 4, 0]]]
  g := ![![![1, 0, 0], ![-1, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 1, 2], ![-10, -36, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![23, -1, 1]] ![![7, 0, 0], ![1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![7, 7, 0]], ![![161, -7, 7], ![-84, -14, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![1, 1, 0]]], ![![![23, -1, 1]], ![![-12, -2, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 6, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 4, 1], [5, 6, 10], [0, 1]]
 g := ![![[7, 5, 9], [3, 3, 1], []], ![[0, 9, 0, 5], [10, 7, 0, 3], [0, 1]], ![[3, 5, 9, 10], [6, 10, 1, 6], [2, 1]]]
 h' := ![![[9, 4, 1], [7, 0, 8], [0, 0, 1], [0, 1]], ![[5, 6, 10], [6, 8, 4], [4, 1, 6], [9, 4, 1]], ![[0, 1], [6, 3, 10], [4, 10, 4], [5, 6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 9], []]
 b := ![[], [6, 3, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [5, 6, 8, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-978868, -547910, -158279]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-88988, -49810, -14389]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![25, -4, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![25, -4, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![12, 9, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![25, -4, 1], ![-110, -11, -7], ![353, 73, -15]]]
  hmulB := by decide  
  f := ![![![-24, 4, -1], ![13, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -9, 13]], ![![1, -1, 1], ![-2, 4, -7], ![41, 16, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [8, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 12], [0, 1]]
 g := ![![[], [12], [0, 1]], ![[], [12], [0, 12]]]
 h' := ![![[0, 12], [8], [0, 5], [0, 1]], ![[0, 1], [8], [0, 8], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [0, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [8, 0, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-698, -426, -134]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, 60, -134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-6, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-6, 1, 0]] 
 ![![13, 0, 0], ![7, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-6, 1, 0], ![1, -6, 2], ![-106, -36, -5]]]
  hmulB := by decide  
  f := ![![![-3, 59, -20], ![13, 130, 0]], ![![2, 29, -10], ![14, 65, 0]], ![![0, 9, -3], ![3, 20, 0]]]
  g := ![![![1, 0, 0], ![-7, 13, 0], ![-2, 0, 13]], ![![-1, 1, 0], ![3, -6, 2], ![12, -36, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![25, -4, 1]] ![![13, 0, 0], ![-6, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-78, 13, 0]], ![![325, -52, 13], ![-260, 13, -13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-6, 1, 0]]], ![![![25, -4, 1]], ![![-20, 1, -1]]]]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 3 2 4 [13, 5, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 13, 9], [15, 3, 8], [0, 1]]
 g := ![![[8, 1, 16], [10, 2], [13, 1], []], ![[0, 15, 11, 2], [3, 2], [12, 9], [12, 13]], ![[2, 15, 9, 15], [9, 8], [0, 16], [13, 13]]]
 h' := ![![[15, 13, 9], [7, 6, 4], [1, 7, 11], [0, 0, 1], [0, 1]], ![[15, 3, 8], [16, 8, 15], [15, 9, 11], [1, 8, 3], [15, 13, 9]], ![[0, 1], [15, 3, 15], [8, 1, 12], [5, 9, 13], [15, 3, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 13], []]
 b := ![[], [15, 0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 3
  hpos := by decide
  P := [13, 5, 4, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154360, -228701, -271898]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9080, -13453, -15994]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1592, -71, 39]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![1592, -71, 39]] 
 ![![19, 0, 0], ![0, 19, 0], ![15, 5, 1]] where
  M :=![![![1592, -71, 39], ![-4205, 188, -103], ![4757, -213, 117]]]
  hmulB := by decide  
  f := ![![![3, 0, -1]], ![![106, 39, -1]], ![![34, 14, 1]]]
  g := ![![![53, -14, 39], ![-140, 37, -103], ![158, -42, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [9, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 18], [0, 1]]
 g := ![![[2, 17], [7, 4], [1], [1]], ![[0, 2], [11, 15], [1], [1]]]
 h' := ![![[1, 18], [13, 6], [15, 2], [10, 1], [0, 1]], ![[0, 1], [0, 13], [17, 17], [11, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [13, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [9, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1255, 51, -366]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![355, 99, -366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 0, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![-3, 0, 1]] 
 ![![19, 0, 0], ![8, 1, 0], ![16, 0, 1]] where
  M :=![![![-3, 0, 1], ![-106, -39, 1], ![-71, -71, -39]]]
  hmulB := by decide  
  f := ![![![-1592, 71, -39]], ![![-449, 20, -11]], ![![-1591, 71, -39]]]
  g := ![![![-1, 0, 1], ![10, -39, 1], ![59, -71, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![1592, -71, 39]] ![![-3, 0, 1]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0]] 
 ![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [8, 14, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 19, 6], [5, 3, 17], [0, 1]]
 g := ![![[7, 20, 8], [20, 22, 3], [11, 18, 1], []], ![[11, 11, 22, 1], [14, 11, 8, 4], [14, 19, 7, 8], [2, 13]], ![[7, 20, 14, 10], [22, 0, 20, 10], [13, 7, 11, 19], [14, 13]]]
 h' := ![![[13, 19, 6], [1, 20, 13], [4, 1, 7], [0, 0, 1], [0, 1]], ![[5, 3, 17], [19, 3, 21], [7, 0, 4], [15, 17, 3], [13, 19, 6]], ![[0, 1], [5, 0, 12], [21, 22, 12], [5, 6, 19], [5, 3, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 5], []]
 b := ![[], [13, 21, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [8, 14, 5, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![801343, 368575, 58420]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34841, 16025, 2540]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![845071622, -37707005, 20706977]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![845071622, -37707005, 20706977]] 
 ![![29, 0, 0], ![0, 29, 0], ![4, 5, 1]] where
  M :=![![![845071622, -37707005, 20706977], ![-2232646567, 99620450, -54707033], ![2526747163, -112743187, 61913445]]]
  hmulB := by decide  
  f := ![![![7451, 2294, -465]], ![![51584, 24191, 4123]], ![![2675, 2778, 1560]]]
  g := ![![![26284266, -4870410, 20706977], ![-69442015, 12867435, -54707033], ![78589427, -14562428, 61913445]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [9, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 28], [0, 1]]
 g := ![![[18, 13], [22], [25, 13], [12, 1]], ![[0, 16], [22], [7, 16], [24, 28]]]
 h' := ![![[12, 28], [25, 10], [7, 15], [8, 19], [0, 1]], ![[0, 1], [0, 19], [13, 14], [4, 10], [12, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [13, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [9, 17, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1826, -1775, -935]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, 100, -935]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7451, 2294, -465]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![7451, 2294, -465]] 
 ![![29, 0, 0], ![18, 1, 0], ![27, 0, 1]] where
  M :=![![![7451, 2294, -465], ![51584, 24191, 4123], ![-210149, -49569, 26485]]]
  hmulB := by decide  
  f := ![![![845071622, -37707005, 20706977]], ![![447539401, -19969160, 10966157]], ![![873920033, -38994218, 21413856]]]
  g := ![![![-734, 2294, -465], ![-17075, 24191, 4123], ![-1138, -49569, 26485]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![845071622, -37707005, 20706977]] ![![7451, 2294, -465]]
  ![![29, 0, 0]] where
 M := ![![![29, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8537981, 2987748, -215542]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![8537981, 2987748, -215542]] 
 ![![31, 0, 0], ![6, 1, 0], ![29, 0, 1]] where
  M :=![![![8537981, 2987748, -215542], ![25835200, 16297493, 5759954], ![-301397806, -92255446, 19285241]]]
  hmulB := by decide  
  f := ![![![-845688205410297, 37734516885536, -20722085279798]], ![![-91608183094118, 4087547289537, -2244695586694]], ![![-872695119093541, 38939562473126, -21383841663425]]]
  g := ![![![-101219, 2987748, -215542], ![-7709304, 16297493, 5759954], ![-9907649, -92255446, 19285241]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2675, 2778, 1560]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![2675, 2778, 1560]] 
 ![![31, 0, 0], ![12, 1, 0], ![6, 0, 1]] where
  M :=![![![2675, 2778, 1560], ![-162582, -53485, 7116], ![-405228, -210768, -50707]]]
  hmulB := by decide  
  f := ![![![-4211888983, 187934034, -103204848]], ![![-1271452254, 56732063, -31154676]], ![![-1221445074, 54500748, -29929339]]]
  g := ![![![-1291, 2778, 1560], ![14082, -53485, 7116], ![78330, -210768, -50707]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![8537981, 2987748, -215542]] ![![2675, 2778, 1560]]
  ![![-375571292585, -90651834306, 45509553322]] where
 M := ![![![-375571292585, -90651834306, 45509553322]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI31N1 : IdealMulLeCertificate' Table 
  ![![-375571292585, -90651834306, 45509553322]] ![![2675, 2778, 1560]]
  ![![31, 0, 0]] where
 M := ![![![-4708041956094199, -5786781227516016, -3538622589652750]]]
 hmul := by decide  
 g := ![![![![-151872321164329, -186670362177936, -114149115795250]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N1, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N1
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB242I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB242I0 : PrimesBelowBoundCertificateInterval O 1 31 242 where
  m := 11
  g := ![3, 2, 2, 2, 1, 2, 1, 2, 1, 2, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB242I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N0]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0]
    · exact ![I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0, I29N1]
    · exact ![I31N0, I31N1, I31N1]
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
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![4913]
    · exact ![361, 19]
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
      exact NI2N0
      exact NI2N0
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
      exact NI31N1
  β := ![I2N0, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I13N0, I13N1, I19N1, I29N1, I31N0, I31N1]
  Il := ![[I2N0, I2N0, I2N0], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1], [], [I13N0, I13N1], [], [I19N1], [], [I29N1], [I31N0, I31N1, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
