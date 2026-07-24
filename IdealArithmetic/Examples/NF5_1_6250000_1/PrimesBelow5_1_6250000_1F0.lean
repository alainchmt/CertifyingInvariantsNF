
import IdealArithmetic.Examples.NF5_1_6250000_1.RI5_1_6250000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![3, -1, 2, 3, 12], ![0, 0, 0, -2, -3]]]
  hmulB := by decide  
  f := ![![![4, -2, 1, 3, 12], ![2, 2, 0, -2, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![2, 0, 0, 2, 6], ![-1, 2, 0, -1, 0]], ![![0, 0, 0, 1, 2], ![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![-1, 1, 0, 2, 0], ![0, -1, 2, 3, 12], ![1, 0, 0, -2, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![2, 0, -2, -1, -3], ![-3, 1, -2, -1, -3], ![-3, -4, -1, -1, -3], ![0, -2, -2, 1, 0], ![0, 1, 1, 0, 2]]]
  hmulB := by decide  
  f := ![![![18, 0, 7, 4, 12], ![-2, 8, 2, 0, 0]], ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]], ![![9, 0, 4, 2, 6], ![-1, 4, 1, 0, 0]], ![![8, -4, -6, -4, -12], ![-8, 2, -2, 1, 0]], ![![13, 0, 5, 4, 11], ![-1, 6, 2, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![2, 0, -2, -1, -3], ![-1, 1, -2, -1, -3], ![1, -4, -1, -1, -3], ![2, -2, -2, 1, 0], ![-1, 1, 1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![4, -2, -1, -1, -2], ![-3, 4, -4, -1, -6], ![-3, -6, 2, 1, 6], ![3, -3, 0, -2, 0], ![-2, 3, -1, 0, -3]]]
  hmulB := by decide  
  f := ![![![0, -2, 5, 2, 8], ![2, 2, 0, 0, 0]], ![![-4, 6, -4, 0, -6], ![0, -2, 0, 1, 0]], ![![0, -1, 3, 1, 4], ![1, 1, 0, 0, 0]], ![![-2, 0, 3, 2, 5], ![2, 1, 0, 0, 0]], ![![12, -23, 25, 5, 40], ![5, 11, 0, -3, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 2, 0, 0, 0], ![-1, 0, 2, 0, 0], ![-1, 0, 0, 2, 0], ![0, 0, 0, 0, 2]], ![![4, -2, -1, -1, -2], ![-1, 4, -4, -1, -6], ![0, -6, 2, 1, 6], ![4, -3, 0, -2, 0], ![-2, 3, -1, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![1, 4, -3, -1, -5]] where
 M := ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![0, 2, 0, 0, 0], ![-3, 1, -2, -1, -3]]]
 hmul := by decide  
 g := ![![![![-3, 4, 3, 1, 7], ![-2, -8, 0, -4, 0]], ![![-10, 12, 4, 1, 12], ![-6, -20, 0, -10, 0]]], ![![![-3, 0, 2, 1, 3], ![0, -2, 0, 0, 0]], ![![-3, 0, 0, 0, 0], ![0, -1, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![1, 4, -3, -1, -5]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![3, 3, -2, -1, -4]] where
 M := ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![2, 8, -6, -2, -10], ![-1, 13, -10, -3, -16]]]
 hmul := by decide  
 g := ![![![![5, -7, 0, -1, 4], ![2, 4, 0, 0, 0]], ![![5, -7, -2, -2, 1], ![2, 4, 0, 0, 0]]], ![![![-11, 7, 2, 3, -1], ![2, -6, 0, 0, 0]], ![![-23, 19, 3, 6, -6], ![1, -14, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![3, 3, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]]
  ![![2, 0, 0, 0, 0], ![2, 5, -5, -2, -8]] where
 M := ![![![4, 0, 0, 0, 0], ![8, -4, -2, -2, -4]], ![![6, 6, -4, -2, -8], ![14, 9, -15, -6, -24]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, -7, 4, 1, 6], ![2, 0, 0, 0, 0]]], ![![![1, -2, 3, 1, 4], ![2, 0, 0, 0, 0]], ![![4, -3, 0, 0, 0], ![3, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![2, 0, 0, 0, 0], ![2, 5, -5, -2, -8]] ![![2, 0, 0, 0, 0], ![4, -2, -1, -1, -2]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![4, 0, 0, 0, 0], ![8, -4, -2, -2, -4]], ![![4, 10, -10, -4, -16], ![18, 28, -24, -8, -40]]]
 hmul := by decide  
 g := ![![![![2, 0, 0, 0, 0]], ![![4, -2, -1, -1, -2]]], ![![![2, 5, -5, -2, -8]], ![![9, 14, -12, -4, -20]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N1, I2N1, I2N2, I2N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
    exact isPrimeI2N2
    exact isPrimeI2N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2 ⊙ MulI2N3)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 3]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![3, -1, 2, 3, 12], ![0, 0, 0, -2, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, 0, 0, 0, 1], ![0, 0, 0, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![1, -1, 2, 3, 4], ![0, 0, 0, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2], [0, 1]]
 g := ![![[1, 1]], ![[2, 2]]]
 h' := ![![[1, 2], [0, 1]], ![[0, 1], [1, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5583, -3658, 3709, 4702, 22416]
  a := ![-17, 4, -15, -20, -68]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1861, -3658, 3709, 4702, 7472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 2, 1, 0, 0], ![1, 1, 0, 1, 0], ![0, 1, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![2, 3, -3, -1, -5], ![-3, 0, 1, 1, 3], ![3, -3, 2, -1, 3], ![0, 3, -3, -3, -12], ![-2, -1, 1, 2, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![1, 0, 0, 1, 1], ![0, 3, 0, 0, -3]], ![![1, -2, 2, 1, 3], ![2, 3, 0, 0, -2]], ![![0, -1, 1, 1, 2], ![1, 1, 0, 0, -1]], ![![-1, -2, 2, 1, 4], ![2, 1, 0, 0, -1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -2, 3, 0, 0], ![-1, -1, 0, 3, 0], ![0, -1, 0, 0, 3]], ![![3, 5, -3, -1, -5], ![-2, -2, 1, 1, 3], ![0, -3, 2, -1, 3], ![3, 8, -3, -3, -12], ![-2, -3, 1, 2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P1 : CertificateIrreducibleZModOfList' 3 2 2 1 [1, 0, 1] where
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

def PI3N1 : CertifiedPrimeIdeal' SI3N1 3 where
  n := 2
  hpos := by decide
  P := [1, 0, 1]
  hirr := P3P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1598, -1642, 1331, 3328, 9954]
  a := ![-11, 1, -10, -16, -45]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1464, -5862, 1331, 3328, 9954]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N1 B_one_repr
lemma NI3N1 : Nat.card (O ⧸ I3N1) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![3, -1, 2, 4, 12], ![0, 0, 0, -2, -2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0, 0, 0], ![3, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, -1, 0, 0, 0], ![2, 1, 0, 0, 0]], ![![0, -1, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![0, 2, 2, 4, -1], ![0, 2, -8, 0, -2]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![0, -1, 2, 4, 12], ![0, 0, 0, -2, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N2 : Nat.card (O ⧸ I3N2) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N2)

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := prime_ideal_of_norm_prime hp3.out _ NI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] ![![3, 0, 0, 0, 0], ![2, 3, -3, -1, -5]]
  ![![3, 0, 0, 0, 0], ![0, -6, 4, 1, 6]] where
 M := ![![![9, 0, 0, 0, 0], ![6, 9, -9, -3, -15]], ![![0, 3, 0, 0, 0], ![-3, 0, 1, 1, 3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![2, 3, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![0, 1, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-1, 2, -1, 0, -1], ![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0, 0, 0], ![0, -6, 4, 1, 6]] ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![9, 0, 0, 0, 0], ![3, 3, 0, 0, 0]], ![![0, -18, 12, 3, 18], ![3, -3, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0, 0, 0]], ![![1, 1, 0, 0, 0]]], ![![![0, -6, 4, 1, 6]], ![![1, -1, 0, 0, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0], ![0, 5, 0, 0, 0], ![0, 0, 5, 0, 0], ![0, 0, 0, 5, 0], ![0, 0, 0, 0, 5]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 1, 2, 2, 0], ![3, -1, 2, 5, 12], ![0, 0, 0, -2, -1]]]
  hmulB := by decide  
  f := ![![![111, 56, 49, 70, 96], ![-215, -15, -75, -40, 0]], ![![54, 26, 23, 34, 48], ![-104, -5, -35, -20, 0]], ![![55, 27, 25, 36, 48], ![-107, -4, -40, -20, 0]], ![![53, 26, 24, 35, 48], ![-101, -6, -37, -20, 0]], ![![88, 44, 39, 56, 77], ![-170, -11, -60, -32, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 5, 0, 0, 0], ![-1, 0, 5, 0, 0], ![-3, 0, 0, 5, 0], ![-4, 0, 0, 0, 5]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, 1, 2, 2, 0], ![-12, -1, 2, 5, 12], ![2, 0, 0, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![1, -1, -2, -1, -3]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![10, 5, 0, 0, 0], ![4, 4, 1, 0, 0]]]
 hmul := by decide  
 g := ![![![![1135, -10, 780, 270, 690], ![-550, 1600, 100, 0, 0]], ![![1045, 0, 720, 253, 639], ![-505, 1470, 100, 0, 0]]], ![![![1045, 0, 720, 253, 639], ![-505, 1470, 100, 0, 0]], ![![615, 1, 423, 149, 375], ![-299, 864, 60, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![1, -1, -2, -1, -3]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![1, 6, -3, -1, -5]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![5, -5, -10, -5, -15], ![-1, -2, -7, -3, -9]]]
 hmul := by decide  
 g := ![![![![-35, 15, 45, 10, 20], ![-25, -75, 0, 0, 0]], ![![-6, 4, 9, 2, 4], ![-5, -15, 0, 0, 0]]], ![![![-15, 5, 16, 3, 5], ![-10, -30, 0, 0, 0]], ![![-2, -1, 1, 0, 0], ![0, -3, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![1, 6, -3, -1, -5]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0], ![1, 4, 2, 1, 2]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![5, 30, -15, -5, -25], ![-1, 11, -2, -1, -7]]]
 hmul := by decide  
 g := ![![![![4, -4, -2, -1, -2], ![5, 0, 0, 0, 0]], ![![1, -3, -2, -1, -2], ![5, 0, 0, 0, 0]]], ![![![0, 4, -5, -2, -7], ![2, 1, 0, 0, 0]], ![![0, 3, 0, 0, -1], ![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![5, 0, 0, 0, 0], ![1, 4, 2, 1, 2]] ![![5, 0, 0, 0, 0], ![2, 1, 0, 0, 0]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![25, 0, 0, 0, 0], ![10, 5, 0, 0, 0]], ![![5, 20, 10, 5, 10], ![5, 10, 10, 5, 10]]]
 hmul := by decide  
 g := ![![![![5, 0, 0, 0, 0]], ![![2, 1, 0, 0, 0]]], ![![![1, 4, 2, 1, 2]], ![![1, 2, 2, 1, 2]]]]
 hle2 := by decide  

def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N0, I5N0, I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2 ⊙ MulI5N3)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, 0, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1, 1, 1, 0, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![6, 3, 1, 0, 0], ![5, 6, 0, 1, 0], ![2, 5, 0, 0, 1]] where
  M :=![![![1, 1, 1, 0, 1], ![0, 2, 1, 0, -3], ![0, 1, 2, 8, 9], ![12, -4, 8, 5, 36], ![-2, 2, -2, -6, -15]]]
  hmulB := by decide  
  f := ![![![-15, -13, 15, 6, 25]], ![![18, -6, -1, -2, -3]], ![![-6, -11, 11, 4, 18]], ![![3, -15, 11, 3, 17]], ![![10, -8, 3, 0, 4]]]
  g := ![![![-1, -1, 1, 0, 1], ![0, 2, 1, 0, -3], ![-10, -14, 2, 8, 9], ![-19, -34, 8, 5, 36], ![10, 17, -2, -6, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [2, 2, 1] where
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
 g := ![![[1, 4], [5, 1]], ![[0, 3], [3, 6]]]
 h' := ![![[5, 6], [4, 2], [0, 1]], ![[0, 1], [0, 5], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [4, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [2, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56808, -42059, 41534, 70569, 265830]
  a := ![60, -8, 57, 77, 239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-153843, -274175, 41534, 70569, 265830]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, 0, 1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-1, -1, 1, 0, 1]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![2, 2, 1, 0, 0], ![5, 3, 0, 1, 0], ![4, 4, 0, 0, 1]] where
  M :=![![![-1, -1, 1, 0, 1], ![0, 0, -1, 0, -3], ![0, -1, 0, 4, 9], ![6, -2, 4, -3, 12], ![-2, 2, -2, -2, -11]]]
  hmulB := by decide  
  f := ![![![-5, 1, -5, -2, -7]], ![![-6, -8, -3, -2, -3]], ![![-4, -3, -4, -2, -5]], ![![-7, -3, -6, -3, -8]], ![![-6, -4, -4, -2, -5]]]
  g := ![![![-1, -1, 1, 0, 1], ![2, 2, -1, 0, -3], ![-8, -7, 0, 4, 9], ![-5, -7, 4, -3, 12], ![8, 8, -2, -2, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 2 2 2 [5, 3, 1] where
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

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 2
  hpos := by decide
  P := [5, 3, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20511, -8351, 11659, 1754, 54021]
  a := ![-28, 11, -23, -24, -111]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-32523, -36145, 11659, 1754, 54021]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 0, 0, 1]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![1, 0, 0, 0, 1]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 0, 0, 0, 1], ![0, 1, 0, -2, -3], ![-6, 2, -3, 0, -15], ![0, -5, 1, 13, 24], ![4, 0, 2, -4, 3]]]
  hmulB := by decide  
  f := ![![![15, 0, 10, 4, 13]], ![![6, 3, 4, 2, 5]], ![![9, 2, 9, 4, 12]], ![![9, 1, 7, 3, 9]], ![![1, 0, 0, 0, 0]]]
  g := ![![![0, 0, 0, 0, 1], ![1, 1, 0, -2, -3], ![2, 2, -3, 0, -15], ![-8, -5, 1, 13, 24], ![1, 0, 2, -4, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 1, 0, 1]] ![![-1, -1, 1, 0, 1]]
  ![![-3, 0, -2, 2, -4]] where
 M := ![![![-3, 0, -2, 2, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![-3, 0, -2, 2, -4]] ![![1, 0, 0, 0, 1]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, -14, 0, 42, 63]]]
 hmul := by decide  
 g := ![![![![-1, -2, 0, 6, 9]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![9, 3, 1, 0, 0], ![3, 6, 0, 1, 0], ![10, 4, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-3, 9, -3, -1, -5], ![-3, -5, 7, 1, 3], ![3, 3, -3, 11, 3], ![18, -3, 9, 10, 60], ![-2, -1, 1, -10, -19]]]
  hmulB := by decide  
  f := ![![![787, 466, -1226, -118, -294], ![660, 2200, -22, 0, 0]], ![![1305, 782, -2039, -189, -489], ![1089, 3652, -44, 0, 0]], ![![969, 579, -1513, -144, -364], ![809, 2712, -29, 0, 0]], ![![927, 552, -1446, -135, -346], ![776, 2592, -30, 0, 0]], ![![1190, 708, -1856, -176, -445], ![996, 3328, -36, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-9, -3, 11, 0, 0], ![-3, -6, 0, 11, 0], ![-10, -4, 0, 0, 11]], ![![7, 4, -3, -1, -5], ![-9, -4, 7, 1, 3], ![-3, -6, -3, 11, 3], ![-63, -30, 9, 10, 60], ![19, 12, 1, -10, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [4, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 10], [0, 1]]
 g := ![![[0, 3], [], [1]], ![[0, 8], [], [1]]]
 h' := ![![[0, 10], [0, 5], [7], [0, 1]], ![[0, 1], [0, 6], [7], [0, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8320, 4308, 2740, -18300, -14976]
  a := ![18, -16, 16, -2, 72]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![17120, 15072, 2740, -18300, -14976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![5, 4, 1, 0, 0], ![1, 6, 0, 1, 0], ![4, 5, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-1, 4, -2, -1, -3], ![-3, -2, 2, -1, -3], ![-3, 0, -4, 7, -3], ![12, -6, 6, 10, 48], ![0, 1, 1, -8, -13]]]
  hmulB := by decide  
  f := ![![![10769, 7216, -6996, 3236, 10716], ![-286, 39116, 462, 0, 0]], ![![1769, 1185, -1148, 531, 1761], ![-44, 6424, 77, 0, 0]], ![![5376, 3604, -3493, 1615, 5349], ![-146, 19528, 231, 0, 0]], ![![1944, 1302, -1262, 584, 1935], ![-49, 7060, 84, 0, 0]], ![![4720, 3163, -3066, 1418, 4697], ![-125, 17144, 203, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-5, -4, 11, 0, 0], ![-1, -6, 0, 11, 0], ![-4, -5, 0, 0, 11]], ![![2, 3, -2, -1, -3], ![0, 1, 2, -1, -3], ![2, -1, -4, 7, -3], ![-20, -30, 6, 10, 48], ![5, 10, 1, -8, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [2, 9, 1] where
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
 g := ![![[10, 5], [0, 4], [1]], ![[9, 6], [8, 7], [1]]]
 h' := ![![[2, 10], [0, 7], [9, 2], [0, 1]], ![[0, 1], [3, 4], [2, 9], [2, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [5, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [2, 9, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6730, -2341, 3699, -642, 15405]
  a := ![-10, 8, -6, -9, -53]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6613, -8210, 3699, -642, 15405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![8, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![4, 1, 0, 0, 0], ![0, 4, 1, 0, 0], ![0, 1, 4, 2, 0], ![3, -1, 2, 7, 12], ![0, 0, 0, -2, 1]]]
  hmulB := by decide  
  f := ![![![1130, 286, 225, 319, 420], ![-2816, -77, -407, -385, 0]], ![![485, 123, 97, 137, 180], ![-1209, -33, -176, -165, 0]], ![![646, 163, 128, 182, 240], ![-1610, -43, -231, -220, 0]], ![![807, 205, 161, 228, 300], ![-2011, -57, -291, -275, 0]], ![![510, 128, 102, 145, 191], ![-1270, -32, -185, -175, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-8, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 4, 1, 0, 0], ![-4, 1, 4, 2, 0], ![-11, -1, 2, 7, 12], ![1, 0, 0, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N2 : Nat.card (O ⧸ I11N2) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N2)

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := prime_ideal_of_norm_prime hp11.out _ NI11N2
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![-3, 9, -3, -1, -5]] ![![11, 0, 0, 0, 0], ![-1, 4, -2, -1, -3]]
  ![![11, 0, 0, 0, 0], ![1, -14, 17, 6, 27]] where
 M := ![![![121, 0, 0, 0, 0], ![-11, 44, -22, -11, -33]], ![![-33, 99, -33, -11, -55], ![-27, -29, 25, 3, 8]]]
 hmul := by decide  
 g := ![![![![10, 14, -17, -6, -27], ![11, 0, 0, 0, 0]], ![![-1, 4, -2, -1, -3], ![0, 0, 0, 0, 0]]], ![![![-3, 9, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-3, 5, -7, -3, -14], ![6, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0, 0, 0], ![1, -14, 17, 6, 27]] ![![11, 0, 0, 0, 0], ![4, 1, 0, 0, 0]]
  ![![11, 0, 0, 0, 0]] where
 M := ![![![121, 0, 0, 0, 0], ![44, 11, 0, 0, 0]], ![![11, -154, 187, 66, 297], ![22, -44, 66, 22, 99]]]
 hmul := by decide  
 g := ![![![![11, 0, 0, 0, 0]], ![![4, 1, 0, 0, 0]]], ![![![1, -14, 17, 6, 27]], ![![2, -4, 6, 2, 9]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [7, 7, 8, 7, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 5, 11, 6], [2, 7, 8, 10, 2], [5, 9, 2, 11, 10], [1, 4, 5, 12, 1], [0, 1]]
 g := ![![[11, 0, 9, 10, 3], [9, 1], []], ![[11, 3, 0, 11, 7, 8, 5], [9, 3, 5, 9], [3, 4, 1, 12, 8]], ![[12, 6, 6, 2, 11, 6], [12, 5, 5, 10], [5, 11, 12, 11, 4, 2, 10, 8]], ![[12, 8, 2, 1, 11, 7, 8, 9], [4, 12, 9, 10], [3, 0, 7, 11, 12, 4, 2, 12]], ![[11, 7, 4, 12, 2, 4, 3, 4], [3, 10, 4, 4], [7, 5, 1, 4, 9, 0, 6, 1]]]
 h' := ![![[1, 5, 11, 6], [2, 8, 12, 7, 9], [0, 0, 0, 1], [0, 1]], ![[2, 7, 8, 10, 2], [12, 2, 4, 2, 9], [6, 5, 10, 4, 10], [1, 5, 11, 6]], ![[5, 9, 2, 11, 10], [8, 2, 6, 4], [12, 11, 7, 6, 7], [2, 7, 8, 10, 2]], ![[1, 4, 5, 12, 1], [11, 5, 6, 4, 6], [0, 4, 5, 10, 7], [5, 9, 2, 11, 10]], ![[0, 1], [8, 9, 11, 9, 2], [4, 6, 4, 5, 2], [1, 4, 5, 12, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 4, 12], [], [], []]
 b := ![[], [8, 12, 7, 8, 11], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [7, 7, 8, 7, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![991515343, -768585012, 645953607, 957056685, 4319709225]
  a := ![2, -4, 1, -3, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![76270411, -59121924, 49688739, 73619745, 332285325]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 371293 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]] where
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [4, 11, 3, 0, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 0, 2, 0, 14], [2, 14, 8, 6, 13], [15, 13, 5, 12, 8], [4, 6, 2, 16, 16], [0, 1]]
 g := ![![[11, 7, 7, 4, 8], [2, 2, 11, 1], [], []], ![[13, 14, 14, 2, 9, 1, 15, 6], [10, 0, 6, 4], [1, 15, 9, 8], [5, 6, 14, 9]], ![[7, 7, 15, 2, 12, 4, 7, 9], [1, 6, 6, 2], [1, 12, 8, 8], [3, 3, 9, 16]], ![[15, 5, 4, 15, 4, 11, 6, 15], [6, 16, 12, 4], [11, 3, 16, 8], [6, 16, 12, 13]], ![[4, 0, 6, 14, 3, 11, 9, 13], [7, 4, 8, 13], [8, 9, 1, 8], [8, 4, 13, 1]]]
 h' := ![![[7, 0, 2, 0, 14], [9, 4, 13, 5, 12], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[2, 14, 8, 6, 13], [10, 15, 3, 0, 7], [4, 5, 4, 1, 15], [12, 6, 10, 13, 12], [7, 0, 2, 0, 14]], ![[15, 13, 5, 12, 8], [9, 2, 3, 12, 11], [9, 3, 2, 7, 11], [9, 11, 14, 8, 12], [2, 14, 8, 6, 13]], ![[4, 6, 2, 16, 16], [11, 9, 6, 10, 2], [16, 7, 11, 8, 15], [14, 5, 9, 3, 5], [15, 13, 5, 12, 8]], ![[0, 1], [15, 4, 9, 7, 2], [3, 2, 0, 1, 9], [1, 12, 0, 10, 5], [4, 6, 2, 16, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 6, 5, 4], [], [], []]
 b := ![[], [0, 15, 11, 4, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [4, 11, 3, 0, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1163088417104, 1004816088240, -783599994525, -1380611951580, -5564579136840]
  a := ![24, -11, 24, 16, 93]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-68416965712, 59106828720, -46094117325, -81212467740, -327328184520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 1419857 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def PBC17 : ContainsPrimesAboveP 17 ![I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![17, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 17 (by decide) 𝕀

instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![4, 5, -3, -1, -5]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![4, 5, -3, -1, -5]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![2, 17, 1, 0, 0], ![2, 9, 0, 1, 0], ![9, 6, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![4, 5, -3, -1, -5], ![-3, 2, 3, 1, 3], ![3, -1, 4, 3, 3], ![6, 1, 1, 5, 12], ![-2, -1, 1, -2, 0]]]
  hmulB := by decide  
  f := ![![![-101731, 85109, 103245, 34235, 98815], ![-43111, -699732, 2052, 0, 0]], ![![-170094, 142312, 172629, 57243, 165219], ![-72105, -1169982, 3420, 0, 0]], ![![-162304, 135788, 164722, 54621, 157653], ![-68787, -1116378, 3264, 0, 0]], ![![-91280, 76369, 92640, 30719, 88664], ![-38690, -627858, 1836, 0, 0]], ![![-101901, 85257, 103419, 34293, 98980], ![-43197, -700920, 2052, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-2, -17, 19, 0, 0], ![-2, -9, 0, 19, 0], ![-9, -6, 0, 0, 19]], ![![3, 5, -3, -1, -5], ![-2, -4, 3, 1, 3], ![-2, -6, 4, 3, 3], ![-6, -7, 1, 5, 12], ![0, 0, 1, -2, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [3, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 18], [0, 1]]
 g := ![![[16, 7], [1, 5], [5], [1]], ![[3, 12], [8, 14], [5], [1]]]
 h' := ![![[9, 18], [16, 11], [13, 10], [16, 9], [0, 1]], ![[0, 1], [1, 8], [8, 9], [2, 10], [9, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [15, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [3, 10, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8017, -3735, 4790, 2301, 24034]
  a := ![18, -6, 15, 17, 71]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-11709, -13162, 4790, 2301, 24034]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![-4, 4, -3, -1, -5]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![-4, 4, -3, -1, -5]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![18, 12, 1, 0, 0], ![6, 4, 0, 1, 0], ![4, 14, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![-4, 4, -3, -1, -5], ![-3, -6, 2, 1, 3], ![3, -2, -4, 1, 3], ![3, 2, -1, -6, 0], ![-2, -1, 1, 0, -5]]]
  hmulB := by decide  
  f := ![![![-87497, -149680, 46539, 24231, 68511], ![-39729, -500650, 532, 0, 0]], ![![-113859, -194777, 60559, 31532, 89154], ![-51699, -651491, 684, 0, 0]], ![![-154472, -264248, 82159, 42778, 120950], ![-70148, -883864, 934, 0, 0]], ![![-51602, -88272, 27445, 14290, 40403], ![-23435, -295256, 312, 0, 0]], ![![-102318, -175030, 54419, 28335, 80114], ![-46465, -585446, 616, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-18, -12, 19, 0, 0], ![-6, -4, 0, 19, 0], ![-4, -14, 0, 0, 19]], ![![4, 6, -3, -1, -5], ![-3, -4, 2, 1, 3], ![3, 0, -4, 1, 3], ![3, 2, -1, -6, 0], ![0, 3, 1, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 15, 1] where
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

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [13, 15, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37, 153, -19, -82, -480]
  a := ![1, 2, 1, 3, 0]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![143, 391, -19, -82, -480]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![14, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![0, 1, 9, 2, 0], ![3, -1, 2, 12, 12], ![0, 0, 0, -2, 6]]]
  hmulB := by decide  
  f := ![![![-451970, -98156, -705265, -154584, 3024], ![955757, -65873, 1497276, -4788, 0]], ![![-226026, -49093, -352687, -77304, 1512], ![477965, -32927, 748752, -2394, 0]], ![![-351478, -76335, -548468, -120216, 2352], ![743252, -51223, 1164396, -3724, 0]], ![![-426858, -92700, -666088, -145997, 2856], ![902654, -62220, 1414104, -4522, 0]], ![![-142734, -31004, -222716, -48816, 955], ![301832, -20788, 472824, -1512, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 19, 0, 0, 0], ![-14, 0, 19, 0, 0], ![-18, 0, 0, 19, 0], ![-6, 0, 0, 0, 19]], ![![0, 1, 0, 0, 0], ![-5, 9, 1, 0, 0], ![-9, 1, 9, 2, 0], ![-16, -1, 2, 12, 12], ![0, 0, 0, -2, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![4, 5, -3, -1, -5]] ![![19, 0, 0, 0, 0], ![-4, 4, -3, -1, -5]]
  ![![19, 0, 0, 0, 0], ![-8, -30, 17, 5, 28]] where
 M := ![![![361, 0, 0, 0, 0], ![-76, 76, -57, -19, -95]], ![![76, 95, -57, -19, -95], ![-33, -5, 6, 4, 11]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, 4, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![4, 5, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![5, 25, -14, -4, -23], ![16, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0, 0, 0], ![-8, -30, 17, 5, 28]] ![![19, 0, 0, 0, 0], ![9, 1, 0, 0, 0]]
  ![![19, 0, 0, 0, 0]] where
 M := ![![![361, 0, 0, 0, 0], ![171, 19, 0, 0, 0]], ![![-152, -570, 323, 95, 532], ![-57, -266, 133, 38, 228]]]
 hmul := by decide  
 g := ![![![![19, 0, 0, 0, 0]], ![![9, 1, 0, 0, 0]]], ![![![-8, -30, 17, 5, 28]], ![![-3, -14, 7, 2, 12]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-6, 2, -3, -1, -5]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-6, 2, -3, -1, -5]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![14, 18, 1, 0, 0], ![12, 18, 0, 1, 0], ![18, 22, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-6, 2, -3, -1, -5], ![-3, -8, 0, 1, 3], ![3, -4, -6, -3, 3], ![-3, 4, -5, -14, -24], ![-2, -1, 1, 4, -1]]]
  hmulB := by decide  
  f := ![![![-24092, -60954, -477, 7518, 22092], ![-4071, -176364, 207, 0, 0]], ![![-158025, -399781, -3147, 49300, 144890], ![-26749, -1156716, 1311, 0, 0]], ![![-137975, -349060, -2746, 43046, 126508], ![-23351, -1009962, 1149, 0, 0]], ![![-136242, -344674, -2712, 42505, 124918], ![-23060, -997272, 1134, 0, 0]], ![![-170010, -430102, -3384, 53040, 155879], ![-28776, -1244448, 1416, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-14, -18, 23, 0, 0], ![-12, -18, 0, 23, 0], ![-18, -22, 0, 0, 23]], ![![6, 8, -3, -1, -5], ![-3, -4, 0, 1, 3], ![3, 4, -6, -3, 3], ![29, 38, -5, -14, -24], ![-2, -3, 1, 4, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [17, 15, 1] where
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
 g := ![![[9, 18], [5, 13], [10, 18], [1]], ![[15, 5], [17, 10], [16, 5], [1]]]
 h' := ![![[8, 22], [7, 15], [14, 17], [6, 8], [0, 1]], ![[0, 1], [12, 8], [12, 6], [1, 15], [8, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [21, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [17, 15, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![77965, -32875, 45487, 14650, 217605]
  a := ![-58, 23, -59, -56, -239]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-202241, -256637, 45487, 14650, 217605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-2, 14, -3, -1, -5]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-2, 14, -3, -1, -5]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![11, 9, 1, 0, 0], ![8, 0, 0, 1, 0], ![6, 1, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-2, 14, -3, -1, -5], ![-3, -4, 12, 1, 3], ![3, 8, -2, 21, 3], ![33, -8, 19, 26, 120], ![-2, -1, 1, -20, -33]]]
  hmulB := by decide  
  f := ![![![165622, 108498, -587019, -41622, -117636], ![155595, 1163616, -2415, 0, 0]], ![![212097, 138937, -751734, -53289, -150639], ![199272, 1490124, -3105, 0, 0]], ![![161180, 105587, -571273, -40501, -114479], ![151426, 1132404, -2355, 0, 0]], ![![57608, 37736, -204180, -14477, -40916], ![54124, 404736, -840, 0, 0]], ![![52429, 34333, -185817, -13174, -37233], ![49273, 368340, -765, 0, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![-11, -9, 23, 0, 0], ![-8, 0, 0, 23, 0], ![-6, -1, 0, 0, 23]], ![![3, 2, -3, -1, -5], ![-7, -5, 12, 1, 3], ![-7, 1, -2, 21, 3], ![-48, -13, 19, 26, 120], ![15, 1, 1, -20, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P1 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 22], [0, 1]]
 g := ![![[1, 8], [13, 12], [14, 9], [1]], ![[0, 15], [0, 11], [10, 14], [1]]]
 h' := ![![[20, 22], [7, 10], [4, 9], [20, 20], [0, 1]], ![[0, 1], [0, 13], [0, 14], [6, 3], [20, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [1, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N1 : CertifiedPrimeIdeal' SI23N1 23 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P23P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6901, -3001, 4019, 1336, 19455]
  a := ![-17, 7, -16, -16, -69]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-7162, -2549, 4019, 1336, 19455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N1 B_one_repr
lemma NI23N1 : Nat.card (O ⧸ I23N1) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N1

def I23N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def SI23N2: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![19, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![3, -1, 2, -1, 12], ![0, 0, 0, -2, -7]]]
  hmulB := by decide  
  f := ![![![12258, -13600, 44514, -22333, 1092], ![68908, 3496, 255783, -2093, 0]], ![![10372, -11512, 37689, -18909, 924], ![58306, 2967, 216568, -1771, 0]], ![![3773, -4183, 13693, -6870, 336], ![21210, 1082, 78683, -644, 0]], ![![8485, -9412, 30818, -15462, 756], ![47698, 2440, 177089, -1449, 0]], ![![1068, -1180, 3870, -1942, 95], ![6004, 322, 22242, -182, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-19, 23, 0, 0, 0], ![-7, 0, 23, 0, 0], ![-16, 0, 0, 23, 0], ![-2, 0, 0, 0, 23]], ![![-1, 1, 0, 0, 0], ![3, -4, 1, 0, 0], ![-1, 1, -4, 2, 0], ![0, -1, 2, -1, 12], ![2, 0, 0, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N2 : Nat.card (O ⧸ I23N2) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N2)

lemma isPrimeI23N2 : Ideal.IsPrime I23N2 := prime_ideal_of_norm_prime hp23.out _ NI23N2
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![-6, 2, -3, -1, -5]] ![![23, 0, 0, 0, 0], ![-2, 14, -3, -1, -5]]
  ![![23, 0, 0, 0, 0], ![22, -19, -15, -9, -22]] where
 M := ![![![529, 0, 0, 0, 0], ![-46, 322, -69, -23, -115]], ![![-138, 46, -69, -23, -115], ![-26, -103, 24, 19, 72]]]
 hmul := by decide  
 g := ![![![![1, 19, 15, 9, 22], ![23, 0, 0, 0, 0]], ![![-2, 14, -3, -1, -5], ![0, 0, 0, 0, 0]]], ![![![-6, 2, -3, -1, -5], ![0, 0, 0, 0, 0]], ![![-4, -2, 3, 2, 6], ![3, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI23N1 : IdealMulLeCertificate' Table 
  ![![23, 0, 0, 0, 0], ![22, -19, -15, -9, -22]] ![![23, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]]
  ![![23, 0, 0, 0, 0]] where
 M := ![![![529, 0, 0, 0, 0], ![-92, 23, 0, 0, 0]], ![![506, -437, -345, -207, -506], ![-115, 92, 23, 23, 46]]]
 hmul := by decide  
 g := ![![![![23, 0, 0, 0, 0]], ![![-4, 1, 0, 0, 0]]], ![![![22, -19, -15, -9, -22]], ![![-5, 4, 1, 1, 2]]]]
 hle2 := by decide  


def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N1, I23N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N1
    exact isPrimeI23N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)


lemma PB156I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB156I0 : PrimesBelowBoundCertificateInterval O 1 23 156 where
  m := 9
  g := ![5, 3, 5, 3, 3, 1, 1, 3, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB156I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1, I11N2]
    · exact ![I13N0]
    · exact ![I17N0]
    · exact ![I19N0, I19N1, I19N2]
    · exact ![I23N0, I23N1, I23N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2, 2, 2, 2, 2]
    · exact ![9, 9, 3]
    · exact ![5, 5, 5, 5, 5]
    · exact ![49, 49, 7]
    · exact ![121, 121, 11]
    · exact ![371293]
    · exact ![1419857]
    · exact ![361, 361, 19]
    · exact ![529, 529, 23]
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
      exact NI2N2
      exact NI2N2
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
      exact NI3N2
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
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
      exact NI19N2
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
      exact NI23N1
      exact NI23N2
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I7N0, I7N1, I7N2, I11N0, I11N1, I11N2, I19N2, I23N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2], [I11N0, I11N1, I11N2], [], [], [I19N2], [I23N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
