
import IdealArithmetic.Examples.NF8_0_12960000_2.RI8_0_12960000_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 0, 1, 1, -1, -1, 1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![1, 0, 1, 1, -1, -1, 1, 1]] 
 ![![2, 0, 0, 0, 0, 0, 0, 0], ![0, 2, 0, 0, 0, 0, 0, 0], ![1, 1, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0], ![0, 1, 0, 0, 1, 0, 0, 0], ![1, 1, 0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 0, 1, 0], ![1, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![1, 0, 1, 1, -1, -1, 1, 1], ![-1, 1, -1, 1, 0, -1, -1, 1], ![-1, -1, 0, -1, 0, 0, -1, -1], ![0, -1, 0, 0, 0, 0, -1, -1], ![0, 0, 0, 0, 1, 0, -1, -1], ![0, 0, 1, 0, 1, 1, -1, -1], ![0, 0, 0, 0, 1, 1, 0, -1], ![1, 0, 1, 0, 1, 1, 1, 0]]]
  hmulB := by decide  
  f := ![![![-1, -1, -2, 1, 1, 0, -2, 0]], ![![0, -1, -1, -2, 1, 1, 0, -2]], ![![0, -1, -1, -1, 1, 1, -1, -1]], ![![0, 0, -1, 1, 0, 0, 0, 0]], ![![0, 0, 0, -1, 1, 0, 0, 0]], ![![-1, -1, -2, 0, 0, 1, -1, -1]], ![![0, -1, -1, -1, 1, 0, 0, -1]], ![![-1, 0, -1, 1, 0, 0, -2, 1]]]
  g := ![![![-1, 0, 1, 1, -1, -1, 1, 1], ![0, 2, -1, 1, 0, -1, -1, 1], ![1, 0, 0, -1, 0, 0, -1, -1], ![1, 0, 0, 0, 0, 0, -1, -1], ![1, 0, 0, 0, 1, 0, -1, -1], ![0, -1, 1, 0, 1, 1, -1, -1], ![0, -1, 0, 0, 1, 1, 0, -1], ![-1, -2, 1, 0, 1, 1, 1, 0]]]
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
  c := ![27, 4, 23, -17, 31, -39, 29, 47]
  a := ![-2, 2, 1, -3, 0, -1, -3, 3]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8, -20, 23, -17, 31, -39, 29, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1, 1, -1, -1, 1, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![1, 1, 1, 1, -1, -1, 1, 1]] 
 ![![2, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![1, 0, 0, 1, 0, 0, 0, 0], ![1, 0, 0, 0, 1, 0, 0, 0], ![1, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 2, 0], ![0, 0, 0, 0, 0, 0, 1, 1]] where
  M :=![![![1, 1, 1, 1, -1, -1, 1, 1], ![-1, 1, 0, 1, 0, -1, -1, 1], ![-1, -1, 0, 0, 0, 0, -1, -1], ![0, -1, 0, 0, 1, 0, -1, -1], ![0, 0, 0, 0, 1, 1, -1, -1], ![1, 0, 1, 0, 1, 1, 1, -1], ![0, 0, 0, 0, 1, 1, 0, 0], ![1, 0, 0, 0, 0, 1, 2, 0]]]
  hmulB := by decide  
  f := ![![![1, -1, -1, 1, 1, -1, 0, 0]], ![![0, 0, -1, 0, 1, 0, -1, 0]], ![![1, -1, 0, 0, 0, 0, 1, -1]], ![![1, 0, 0, 1, 1, -1, 0, 1]], ![![0, 0, -1, 1, 0, 0, 0, 0]], ![![1, -1, 0, 0, 1, -1, 1, 0]], ![![-1, 1, 0, 0, -1, 1, -1, 1]], ![![0, 0, 0, 0, -1, 0, 1, 0]]]
  g := ![![![0, 1, 1, 1, -1, -1, 0, 1], ![-1, 1, 0, 1, 0, -1, -1, 1], ![0, -1, 0, 0, 0, 0, 0, -1], ![0, -1, 0, 0, 1, 0, 0, -1], ![-1, 0, 0, 0, 1, 1, 0, -1], ![-1, 0, 1, 0, 1, 1, 1, -1], ![-1, 0, 0, 0, 1, 1, 0, 0], ![0, 0, 0, 0, 0, 1, 1, 0]]]
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
  c := ![68, -97, 317, -134, 462, -198, -298, -24]
  a := ![8, -1, 0, 2, -10, 2, 21, -2]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-141, -97, 317, -134, 462, -198, -137, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![1, 0, 1, 1, -1, -1, 1, 1]] ![![1, 0, 1, 1, -1, -1, 1, 1]]
  ![![1, -2, 1, 0, -1, 0, 2, 0]] where
 M := ![![![1, -2, 1, 0, -1, 0, 2, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![1, -2, 1, 0, -1, 0, 2, 0]] ![![1, 1, 1, 1, -1, -1, 1, 1]]
  ![![2, -2, 1, -1, 0, 2, 3, -1]] where
 M := ![![![2, -2, 1, -1, 0, 2, 3, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![2, -2, 1, -1, 0, 2, 3, -1]] ![![1, 1, 1, 1, -1, -1, 1, 1]]
  ![![2, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![4, 0, 4, 0, 2, 4, 4, -2]]]
 hmul := by decide  
 g := ![![![![2, 0, 2, 0, 1, 2, 2, -1]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1 ⊙ MulI2N2)

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 1, 0, -1, 0, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![2, 0, 1, 0, -1, 0, 1, 0]] 
 ![![3, 0, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0, 0], ![2, 0, 1, 0, 1, 0, 0, 0], ![0, 2, 0, 1, 0, 1, 0, 0], ![1, 0, 2, 0, 0, 0, 1, 0], ![0, 1, 0, 2, 0, 0, 0, 1]] where
  M :=![![![2, 0, 1, 0, -1, 0, 1, 0], ![0, 2, 0, 1, 0, -1, 0, 1], ![-1, 0, 1, 0, 0, 0, -1, 0], ![0, -1, 0, 1, 0, 0, 0, -1], ![0, 0, 0, 0, 2, 0, -1, 0], ![0, 0, 0, 0, 0, 2, 0, -1], ![0, 0, 0, 0, 1, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, -1, 0, 1, 0, -1, 0]], ![![0, 1, 0, -1, 0, 1, 0, -1]], ![![1, 0, 2, 0, 0, 0, 1, 0]], ![![0, 1, 0, 2, 0, 0, 0, 1]], ![![1, 0, 0, 0, 1, 0, 0, 0]], ![![0, 1, 0, 0, 0, 1, 0, 0]], ![![1, 0, 1, 0, 0, 0, 1, 0]], ![![0, 1, 0, 1, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, -1, 0, 1, 0], ![0, 1, 0, 0, 0, -1, 0, 1], ![0, 0, 1, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 0, 0, 0, -1], ![-1, 0, 0, 0, 2, 0, -1, 0], ![0, -1, 0, 0, 0, 2, 0, -1], ![-1, 0, -1, 0, 1, 0, 1, 0], ![0, -1, 0, -1, 0, 1, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 4 2 1 [2, 0, 0, 1, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [0, 2, 2, 1], [2, 0, 1, 1], [0, 1]]
 g := ![![[]], ![[0, 2, 2, 1, 2, 1]], ![[2, 0, 1, 1, 2, 1]], ![[1, 1, 0, 1, 2, 1]]]
 h' := ![![[0, 0, 0, 1], [0, 1]], ![[0, 2, 2, 1], [0, 0, 0, 1]], ![[2, 0, 1, 1], [0, 2, 2, 1]], ![[0, 1], [2, 0, 1, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [2, 2, 2], []]
 b := ![[], [], [2, 1, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 4
  hpos := by decide
  P := [2, 0, 0, 1, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5275, -4553, -13211, -5707, -21194, -8944, 7383, -2739]
  a := ![0, 2, -4, -1, -3, 1, -1, 3]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![9910, 5358, -2261, 2905, -21194, -8944, 7383, -2739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 81 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 1, 0, -1, 0, 1, 0]] ![![2, 0, 1, 0, -1, 0, 1, 0]]
  ![![3, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![3, 0, 3, 0, -3, 0, 3, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 1, 0, -1, 0, 1, 0]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0)

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -1, 0, 1, 0, 0, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![1, -1, 0, 1, 0, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0], ![3, 3, 1, 0, 0, 0, 0, 0], ![1, 4, 0, 1, 0, 0, 0, 0], ![3, 4, 0, 0, 1, 0, 0, 0], ![3, 1, 0, 0, 0, 1, 0, 0], ![4, 0, 0, 0, 0, 0, 1, 0], ![0, 4, 0, 0, 0, 0, 0, 1]] where
  M :=![![![1, -1, 0, 1, 0, 0, 0, 0], ![0, 1, -1, 0, 1, 0, 0, 0], ![0, 0, 1, -1, 0, 1, 0, 0], ![1, 0, 0, 1, -1, 0, 2, 0], ![0, 1, 0, 0, 1, -1, 0, 2], ![-1, 0, -1, 0, -2, 1, 0, 0], ![0, 0, 0, -1, 0, -1, 1, 0], ![-1, 0, 0, 0, -1, 0, -2, 1]]]
  hmulB := by decide  
  f := ![![![4, 7, 4, 4, -3, -3, 4, 6]], ![![-3, 4, 1, 4, -2, -3, 0, 4]], ![![0, 6, 3, 5, -3, -4, 2, 6]], ![![-2, 4, 1, 4, -2, -3, 0, 4]], ![![0, 7, 3, 5, -3, -4, 2, 6]], ![![2, 5, 3, 3, -2, -2, 2, 4]], ![![3, 5, 3, 3, -2, -2, 3, 4]], ![![-2, 3, 1, 3, -1, -2, 0, 3]]]
  g := ![![![0, -1, 0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 1, 0, 0, 0], ![-1, 0, 1, -1, 0, 1, 0, 0], ![-1, 0, 0, 1, -1, 0, 2, 0], ![0, -2, 0, 0, 1, -1, 0, 2], ![1, 2, -1, 0, -2, 1, 0, 0], ![0, 1, 0, -1, 0, -1, 1, 0], ![2, 0, 0, 0, -1, 0, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [2, 0, 1] where
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
 h' := ![![[0, 4], [3], [0, 1]], ![[0, 1], [3], [0, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [0, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [2, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3, 16, -19, 12, -24, 0, 41, -16]
  a := ![4, -1, 7, -4, 0, 1, 5, -2]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10, 37, -19, 12, -24, 0, 41, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 2, 0, -1, 0, 1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![2, 2, 0, -1, 0, 1, 1, 0]] 
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0], ![3, 2, 1, 0, 0, 0, 0, 0], ![4, 4, 0, 1, 0, 0, 0, 0], ![3, 1, 0, 0, 1, 0, 0, 0], ![2, 1, 0, 0, 0, 1, 0, 0], ![4, 0, 0, 0, 0, 0, 1, 0], ![0, 4, 0, 0, 0, 0, 0, 1]] where
  M :=![![![2, 2, 0, -1, 0, 1, 1, 0], ![1, 2, 2, 0, -1, 0, 2, 1], ![0, 1, 1, 2, -1, -1, 1, 2], ![-1, 0, -1, 1, 0, -1, 0, 1], ![-1, -1, -1, -1, 0, 0, -1, 0], ![0, -1, -1, -1, -1, 0, 0, -1], ![-1, -1, 0, 0, 0, -1, -1, 0], ![-1, -1, -1, 0, 0, 0, -2, -1]]]
  hmulB := by decide  
  f := ![![![3, -4, 3, -3, -1, 1, 3, -2]], ![![1, 3, -2, 3, -1, -1, 0, 3]], ![![2, -1, 1, -1, -1, 0, 2, 0]], ![![3, -1, 1, 0, -2, 0, 2, 1]], ![![2, -2, 1, -1, -1, 0, 2, -1]], ![![1, -1, 1, -1, 0, 0, 0, 0]], ![![2, -3, 2, -2, -1, 1, 2, -2]], ![![1, 2, -1, 2, 0, -1, 0, 2]]]
  g := ![![![0, 1, 0, -1, 0, 1, 1, 0], ![-2, -1, 2, 0, -1, 0, 2, 1], ![-2, -3, 1, 2, -1, -1, 1, 2], ![0, -1, -1, 1, 0, -1, 0, 1], ![2, 1, -1, -1, 0, 0, -1, 0], ![2, 2, -1, -1, -1, 0, 0, -1], ![1, 0, 0, 0, 0, -1, -1, 0], ![2, 1, -1, 0, 0, 0, -2, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P1 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 4, 1] where
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
 g := ![![[4, 1], [1]], ![[0, 4], [1]]]
 h' := ![![[1, 4], [4, 1], [0, 1]], ![[0, 1], [0, 4], [1, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [3, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N1 : CertifiedPrimeIdeal' SI5N1 5 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P5P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-63, 98, 349, -18, 540, -78, -688, 300]
  a := ![-1, 10, 4, 0, -1, 1, -1, 17]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![50, -438, 349, -18, 540, -78, -688, 300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N1 B_one_repr
lemma NI5N1 : Nat.card (O ⧸ I5N1) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![1, -1, 0, 1, 0, 0, 0, 0]] ![![1, -1, 0, 1, 0, 0, 0, 0]]
  ![![2, -2, 1, 2, -2, 0, 2, 0]] where
 M := ![![![2, -2, 1, 2, -2, 0, 2, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![2, -2, 1, 2, -2, 0, 2, 0]] ![![2, 2, 0, -1, 0, 1, 1, 0]]
  ![![0, 1, -3, 4, 1, -3, -1, 2]] where
 M := ![![![0, 1, -3, 4, 1, -3, -1, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI5N2 : IdealMulLeCertificate' Table 
  ![![0, 1, -3, 4, 1, -3, -1, 2]] ![![2, 2, 0, -1, 0, 1, 1, 0]]
  ![![5, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![-5, 0, -5, 0, 5, 0, -5, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, -1, 0, 1, 0, -1, 0]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N0, I5N1, I5N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1 ⊙ MulI5N2)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 1, 0, -1, 0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![3, 0, 1, 0, -1, 0, 1, 0]] 
 ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![5, 0, 4, 0, 1, 0, 0, 0], ![0, 5, 0, 4, 0, 1, 0, 0], ![1, 0, 5, 0, 0, 0, 1, 0], ![0, 1, 0, 5, 0, 0, 0, 1]] where
  M :=![![![3, 0, 1, 0, -1, 0, 1, 0], ![0, 3, 0, 1, 0, -1, 0, 1], ![-1, 0, 2, 0, 0, 0, -1, 0], ![0, -1, 0, 2, 0, 0, 0, -1], ![0, 0, 0, 0, 3, 0, -1, 0], ![0, 0, 0, 0, 0, 3, 0, -1], ![0, 0, 0, 0, 1, 0, 2, 0], ![0, 0, 0, 0, 0, 1, 0, 2]]]
  hmulB := by decide  
  f := ![![![2, 0, -1, 0, 1, 0, -1, 0]], ![![0, 2, 0, -1, 0, 1, 0, -1]], ![![1, 0, 3, 0, 0, 0, 1, 0]], ![![0, 1, 0, 3, 0, 0, 0, 1]], ![![2, 0, 1, 0, 1, 0, 0, 0]], ![![0, 2, 0, 1, 0, 1, 0, 0]], ![![1, 0, 2, 0, 0, 0, 1, 0]], ![![0, 1, 0, 2, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, -1, 0, 1, 0], ![0, 1, 0, 0, 0, -1, 0, 1], ![0, 0, 1, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 0, 0, 0, -1], ![-2, 0, -1, 0, 3, 0, -1, 0], ![0, -2, 0, -1, 0, 3, 0, -1], ![-1, 0, -2, 0, 1, 0, 2, 0], ![0, -1, 0, -2, 0, 1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 4 2 2 [5, 4, 6, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 4, 6, 3], [1, 6, 3, 2], [0, 3, 5, 2], [0, 1]]
 g := ![![[3, 1, 0, 1], []], ![[5, 0, 6, 1, 0, 3], [6, 4, 3, 4, 1, 6]], ![[6, 4, 4, 0, 1, 4], [1, 0, 0, 1, 1, 1]], ![[0, 5, 4, 4, 3, 4], [1, 4, 4, 5, 4, 1]]]
 h' := ![![[6, 4, 6, 3], [0, 0, 0, 1], [0, 1]], ![[1, 6, 3, 2], [4, 3, 1, 6], [6, 4, 6, 3]], ![[0, 3, 5, 2], [3, 0, 6, 3], [1, 6, 3, 2]], ![[0, 1], [2, 4, 0, 4], [0, 3, 5, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [5, 5, 6], []]
 b := ![[], [], [4, 5, 2, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 4
  hpos := by decide
  P := [5, 4, 6, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2420347, 1139284, 1935446, 2165648, 3209199, 3499904, 3198495, -505068]
  a := ![-4, -26, 0, 1, 1, 3, -10, -27]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-2403449, -2265024, -3841975, -1329804, 3209199, 3499904, 3198495, -505068]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 1, 0, -1, 0, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-2, 0, 1, 0, -1, 0, 1, 0]] 
 ![![7, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 0, 0, 0, 0, 0, 0], ![0, 0, 7, 0, 0, 0, 0, 0], ![0, 0, 0, 7, 0, 0, 0, 0], ![3, 0, 2, 0, 1, 0, 0, 0], ![0, 3, 0, 2, 0, 1, 0, 0], ![1, 0, 3, 0, 0, 0, 1, 0], ![0, 1, 0, 3, 0, 0, 0, 1]] where
  M :=![![![-2, 0, 1, 0, -1, 0, 1, 0], ![0, -2, 0, 1, 0, -1, 0, 1], ![-1, 0, -3, 0, 0, 0, -1, 0], ![0, -1, 0, -3, 0, 0, 0, -1], ![0, 0, 0, 0, -2, 0, -1, 0], ![0, 0, 0, 0, 0, -2, 0, -1], ![0, 0, 0, 0, 1, 0, -3, 0], ![0, 0, 0, 0, 0, 1, 0, -3]]]
  hmulB := by decide  
  f := ![![![-3, 0, -1, 0, 1, 0, -1, 0]], ![![0, -3, 0, -1, 0, 1, 0, -1]], ![![1, 0, -2, 0, 0, 0, 1, 0]], ![![0, 1, 0, -2, 0, 0, 0, 1]], ![![-1, 0, -1, 0, 0, 0, 0, 0]], ![![0, -1, 0, -1, 0, 0, 0, 0]], ![![0, 0, -1, 0, 0, 0, 0, 0]], ![![0, 0, 0, -1, 0, 0, 0, 0]]]
  g := ![![![0, 0, 0, 0, -1, 0, 1, 0], ![0, 0, 0, 0, 0, -1, 0, 1], ![0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![1, 0, 1, 0, -2, 0, -1, 0], ![0, 1, 0, 1, 0, -2, 0, -1], ![0, 0, 1, 0, 1, 0, -3, 0], ![0, 0, 0, 1, 0, 1, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P1 : CertificateIrreducibleZModOfList' 7 4 2 2 [6, 4, 5, 0, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 4, 5, 5], [4, 6, 6, 1], [0, 3, 3, 1], [0, 1]]
 g := ![![[3, 2, 0, 1], []], ![[5, 0, 3, 1, 0, 5], [5, 2, 3, 1, 4, 6]], ![[6, 1, 2, 0, 2, 2], [2, 0, 0, 2, 4, 1]], ![[0, 3, 2, 4, 6, 2], [2, 2, 4, 3, 2, 1]]]
 h' := ![![[3, 4, 5, 5], [0, 0, 0, 1], [0, 1]], ![[4, 6, 6, 1], [4, 6, 4, 6], [3, 4, 5, 5]], ![[0, 3, 3, 1], [3, 0, 3, 3], [4, 6, 6, 1]], ![[0, 1], [2, 1, 0, 4], [0, 3, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [3, 6, 6], []]
 b := ![[], [], [1, 6, 2, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N1 : CertifiedPrimeIdeal' SI7N1 7 where
  n := 4
  hpos := by decide
  P := [6, 4, 5, 0, 1]
  hirr := P7P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164634, -89468, -109476, -119444, -177006, -193236, -253872, -41158]
  a := ![2, 5, 0, 1, 5, 1, 5, 7]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![88608, 75914, 143736, 55786, -177006, -193236, -253872, -41158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N1 B_one_repr
lemma NI7N1 : Nat.card (O ⧸ I7N1) = 2401 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 1, 0, -1, 0, 1, 0]] ![![-2, 0, 1, 0, -1, 0, 1, 0]]
  ![![7, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![-7, 0, 0, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0, 0, 0, 0]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 0, 1, 0, -1, 0, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![1, 2, 0, 1, 0, -1, 0, 1]] 
 ![![11, 0, 0, 0, 0, 0, 0, 0], ![0, 11, 0, 0, 0, 0, 0, 0], ![4, 1, 1, 0, 0, 0, 0, 0], ![7, 3, 0, 1, 0, 0, 0, 0], ![10, 4, 0, 0, 1, 0, 0, 0], ![6, 6, 0, 0, 0, 1, 0, 0], ![5, 0, 0, 0, 0, 0, 1, 0], ![0, 5, 0, 0, 0, 0, 0, 1]] where
  M :=![![![1, 2, 0, 1, 0, -1, 0, 1], ![-1, 1, 1, 0, 0, 0, -1, 0], ![0, -1, 1, 1, 0, 0, 0, -1], ![0, 0, 0, 1, 2, 0, -1, 0], ![0, 0, 0, 0, 1, 2, 0, -1], ![2, 0, 1, 0, 1, 1, 3, 0], ![0, 0, 0, 0, 0, 1, 1, 1], ![1, 0, -1, 0, -1, 0, 3, 1]]]
  hmulB := by decide  
  f := ![![![5, -10, 0, -5, 0, 2, 3, -8]], ![![2, 5, -2, 0, 3, 0, -4, 3]], ![![2, -3, 0, -2, 0, 1, 1, -3]], ![![4, -5, 0, -3, 1, 1, 1, -4]], ![![5, -7, -1, -4, 1, 2, 1, -6]], ![![4, -3, -1, -3, 2, 1, 0, -3]], ![![2, -4, 0, -2, 0, 1, 1, -3]], ![![1, 2, -1, 0, 1, 0, -1, 1]]]
  g := ![![![0, 0, 0, 1, 0, -1, 0, 1], ![0, 0, 1, 0, 0, 0, -1, 0], ![-1, 0, 1, 1, 0, 0, 0, -1], ![-2, -1, 0, 1, 2, 0, -1, 0], ![-2, -1, 0, 0, 1, 2, 0, -1], ![-3, -1, 1, 0, 1, 1, 3, 0], ![-1, -1, 0, 0, 0, 1, 1, 1], ![0, 0, -1, 0, -1, 0, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[5, 4], [0, 5], [1]], ![[10, 7], [9, 6], [1]]]
 h' := ![![[4, 10], [0, 2], [3, 4], [0, 1]], ![[0, 1], [8, 9], [8, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [8, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [8, 7, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-261, -48, -185, -68, -266, -61, -350, -66]
  a := ![-11, 2, -8, 0, -1, -1, -17, 0]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![521, 191, -185, -68, -266, -61, -350, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 3, 1, 3, 0, -2, 0, 3]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![0, 3, 1, 3, 0, -2, 0, 3]] 
 ![![11, 0, 0, 0, 0, 0, 0, 0], ![0, 11, 0, 0, 0, 0, 0, 0], ![3, 5, 1, 0, 0, 0, 0, 0], ![7, 0, 0, 1, 0, 0, 0, 0], ![0, 7, 0, 0, 1, 0, 0, 0], ![1, 9, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 0, 1, 0], ![0, 9, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, 3, 1, 3, 0, -2, 0, 3], ![-2, 0, 0, 1, 0, 0, -1, 0], ![0, -2, 0, 0, 1, 0, 0, -1], ![0, 0, -1, 0, 1, 1, -1, 0], ![1, 0, 0, -1, 0, 1, 2, -1], ![1, 1, 1, 0, 0, 0, 1, 2], ![0, -1, -1, -1, -1, 1, 1, -1], ![1, 0, 0, -1, 0, -1, 1, 1]]]
  hmulB := by decide  
  f := ![![![1, -9, 1, 0, -3, 0, 1, -4]], ![![0, 1, -5, 1, 4, -3, -4, 1]], ![![0, -2, -2, 0, 1, -1, -2, -1]], ![![1, -6, 1, 0, -2, 0, 1, -3]], ![![0, 1, -3, 1, 3, -2, -3, 1]], ![![0, 0, -4, 1, 3, -2, -3, 0]], ![![1, -7, 1, 0, -2, 0, 1, -3]], ![![0, 1, -4, 1, 3, -2, -3, 1]]]
  g := ![![![-2, -1, 1, 3, 0, -2, 0, 3], ![0, 0, 0, 1, 0, 0, -1, 0], ![0, 0, 0, 0, 1, 0, 0, -1], ![1, -1, -1, 0, 1, 1, -1, 0], ![-1, 0, 0, -1, 0, 1, 2, -1], ![-1, -2, 1, 0, 0, 0, 1, 2], ![0, 1, -1, -1, -1, 1, 1, -1], ![0, 0, 0, -1, 0, -1, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P1 : CertificateIrreducibleZModOfList' 11 2 2 3 [9, 4, 1] where
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
 g := ![![[9, 5], [8, 5], [1]], ![[0, 6], [10, 6], [1]]]
 h' := ![![[7, 10], [5, 4], [2, 7], [0, 1]], ![[0, 1], [0, 7], [7, 4], [7, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N1 : CertifiedPrimeIdeal' SI11N1 11 where
  n := 2
  hpos := by decide
  P := [9, 4, 1]
  hirr := P11P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-257, -122, -165, -194, -176, -274, -704, 16]
  a := ![-20, 0, 1, -1, -3, -4, -21, 1]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![746, 387, -165, -194, -176, -274, -704, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N1 B_one_repr
lemma NI11N1 : Nat.card (O ⧸ I11N1) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N1

def I11N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, 2, -1, -1, 0, 1, -1]] i)))

def SI11N2: IdealEqSpanCertificate' Table ![![0, -1, 2, -1, -1, 0, 1, -1]] 
 ![![11, 0, 0, 0, 0, 0, 0, 0], ![0, 11, 0, 0, 0, 0, 0, 0], ![3, 6, 1, 0, 0, 0, 0, 0], ![4, 0, 0, 1, 0, 0, 0, 0], ![0, 4, 0, 0, 1, 0, 0, 0], ![10, 9, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 0, 1, 0], ![0, 9, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, -1, 2, -1, -1, 0, 1, -1], ![0, 0, 0, 2, 0, -1, -1, 1], ![-1, 0, -1, 0, 1, 0, -1, -1], ![0, -1, 1, -1, 1, 1, -1, -1], ![1, 0, 0, 1, 0, 1, 1, -1], ![1, 1, 1, 0, 2, 0, 1, 1], ![0, 1, -1, 1, 0, 1, 0, 1], ![1, 0, 0, -1, 0, 0, 3, 0]]]
  hmulB := by decide  
  f := ![![![-9, -4, -9, 0, 5, 0, -9, -3]], ![![0, -9, -1, -9, 3, 5, -3, -9]], ![![-2, -6, -3, -5, 3, 3, -4, -6]], ![![-3, -1, -3, 0, 2, 0, -3, -1]], ![![0, -3, 0, -3, 1, 2, -1, -3]], ![![-8, -11, -9, -7, 7, 4, -10, -10]], ![![-7, -3, -7, 0, 4, 0, -7, -2]], ![![0, -7, -1, -7, 2, 4, -2, -7]]]
  g := ![![![-1, 0, 2, -1, -1, 0, 1, -1], ![1, 0, 0, 2, 0, -1, -1, 1], ![1, 1, -1, 0, 1, 0, -1, -1], ![0, -1, 1, -1, 1, 1, -1, -1], ![-2, 0, 0, 1, 0, 1, 1, -1], ![-1, -2, 1, 0, 2, 0, 1, 1], ![-1, -1, -1, 1, 0, 1, 0, 1], ![-2, 0, 0, -1, 0, 0, 3, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P2 : CertificateIrreducibleZModOfList' 11 2 2 3 [5, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 10], [0, 1]]
 g := ![![[8, 9], [2, 5], [1]], ![[0, 2], [0, 6], [1]]]
 h' := ![![[4, 10], [1, 8], [6, 4], [0, 1]], ![[0, 1], [0, 3], [0, 7], [4, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N2 : CertifiedPrimeIdeal' SI11N2 11 where
  n := 2
  hpos := by decide
  P := [5, 7, 1]
  hirr := P11P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-255, 147, -94, 131, -145, 248, -552, 234]
  a := ![6, -9, 0, -5, 1, -4, 11, -10]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![181, -277, -94, 131, -145, 248, -552, 234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N2 : Ideal.IsPrime I11N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N2 B_one_repr
lemma NI11N2 : Nat.card (O ⧸ I11N2) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N2

def I11N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, 0, 1, 0, -1, 0, 1]] i)))

def SI11N3: IdealEqSpanCertificate' Table ![![-1, 2, 0, 1, 0, -1, 0, 1]] 
 ![![11, 0, 0, 0, 0, 0, 0, 0], ![0, 11, 0, 0, 0, 0, 0, 0], ![4, 10, 1, 0, 0, 0, 0, 0], ![4, 3, 0, 1, 0, 0, 0, 0], ![10, 7, 0, 0, 1, 0, 0, 0], ![5, 6, 0, 0, 0, 1, 0, 0], ![5, 0, 0, 0, 0, 0, 1, 0], ![0, 5, 0, 0, 0, 0, 0, 1]] where
  M :=![![![-1, 2, 0, 1, 0, -1, 0, 1], ![-1, -1, 1, 0, 0, 0, -1, 0], ![0, -1, -1, 1, 0, 0, 0, -1], ![0, 0, 0, -1, 2, 0, -1, 0], ![0, 0, 0, 0, -1, 2, 0, -1], ![2, 0, 1, 0, 1, -1, 3, 0], ![0, 0, 0, 0, 0, 1, -1, 1], ![1, 0, -1, 0, -1, 0, 3, -1]]]
  hmulB := by decide  
  f := ![![![-5, -10, 0, -5, 0, 2, -3, -8]], ![![2, -5, -2, 0, 3, 0, -4, -3]], ![![0, -8, -2, -2, 3, 1, -5, -6]], ![![-1, -5, 0, -2, 1, 1, -2, -4]], ![![-3, -12, -1, -4, 2, 2, -5, -9]], ![![-1, -7, -1, -2, 2, 1, -3, -5]], ![![-2, -4, 0, -2, 0, 1, -1, -3]], ![![1, -2, -1, 0, 1, 0, -1, -1]]]
  g := ![![![0, 0, 0, 1, 0, -1, 0, 1], ![0, -1, 1, 0, 0, 0, -1, 0], ![0, 1, -1, 1, 0, 0, 0, -1], ![-1, -1, 0, -1, 2, 0, -1, 0], ![0, 0, 0, 0, -1, 2, 0, -1], ![-2, -1, 1, 0, 1, -1, 3, 0], ![0, -1, 0, 0, 0, 1, -1, 1], ![0, 2, -1, 0, -1, 0, 3, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P3 : CertificateIrreducibleZModOfList' 11 2 2 3 [8, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 10], [0, 1]]
 g := ![![[4, 9], [7, 1], [1]], ![[2, 2], [8, 10], [1]]]
 h' := ![![[1, 10], [10, 8], [3, 1], [0, 1]], ![[0, 1], [7, 3], [4, 10], [1, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [6, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N3 : CertifiedPrimeIdeal' SI11N3 11 where
  n := 2
  hpos := by decide
  P := [8, 10, 1]
  hirr := P11P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![185, 17454, 121220, 236, 193815, -128, -194518, 50592]
  a := ![-46, 160, 3, 0, -2, -1, -47, 313]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-131869, -254941, 121220, 236, 193815, -128, -194518, 50592]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N3 : Ideal.IsPrime I11N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N3 B_one_repr
lemma NI11N3 : Nat.card (O ⧸ I11N3) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N3
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![1, 2, 0, 1, 0, -1, 0, 1]] ![![0, 3, 1, 3, 0, -2, 0, 3]]
  ![![-4, 2, -1, 4, 1, -2, -3, 2]] where
 M := ![![![-4, 2, -1, 4, 1, -2, -3, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![-4, 2, -1, 4, 1, -2, -3, 2]] ![![0, -1, 2, -1, -1, 0, 1, -1]]
  ![![2, -5, -2, 0, 3, 0, -4, -3]] where
 M := ![![![2, -5, -2, 0, 3, 0, -4, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI11N2 : IdealMulLeCertificate' Table 
  ![![2, -5, -2, 0, 3, 0, -4, -3]] ![![-1, 2, 0, 1, 0, -1, 0, 1]]
  ![![11, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![0, 11, 0, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![0, 1, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N2, I11N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N2
    exact isPrimeI11N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1 ⊙ MulI11N2)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -2, 1, 1, 0, -1, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![0, -2, 1, 1, 0, -1, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0, 0, 0], ![6, 4, 1, 0, 0, 0, 0, 0], ![2, 3, 0, 1, 0, 0, 0, 0], ![8, 3, 0, 0, 1, 0, 0, 0], ![8, 9, 0, 0, 0, 1, 0, 0], ![6, 12, 0, 0, 0, 0, 1, 0], ![6, 10, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, -2, 1, 1, 0, -1, 0, 0], ![-1, 0, -2, 1, 1, 0, -2, 0], ![0, -1, 0, -2, 1, 1, 0, -2], ![1, 0, 1, 0, 0, 1, 0, 0], ![1, 1, 0, 1, 0, 0, 2, 0], ![0, 1, 1, 0, 1, 0, 0, 2], ![0, 1, -1, 0, -1, 1, 1, 0], ![1, 0, 1, -1, 0, -1, 2, 1]]]
  hmulB := by decide  
  f := ![![![-4, 6, -3, 11, 0, -7, -4, 8]], ![![-7, -4, -2, -3, 3, 0, -6, -4]], ![![-4, 1, -2, 4, 1, -3, -4, 2]], ![![-2, 0, -1, 1, 1, -1, -2, 0]], ![![-4, 3, -2, 6, 1, -4, -4, 4]], ![![-7, 1, -3, 5, 2, -4, -6, 2]], ![![-8, -1, -3, 2, 3, -3, -7, 0]], ![![-7, 0, -3, 3, 2, -3, -6, 1]]]
  g := ![![![0, 0, 1, 1, 0, -1, 0, 0], ![1, 2, -2, 1, 1, 0, -2, 0], ![0, 1, 0, -2, 1, 1, 0, -2], ![-1, -1, 1, 0, 0, 1, 0, 0], ![-1, -2, 0, 1, 0, 0, 2, 0], ![-2, -2, 1, 0, 1, 0, 0, 2], ![0, -1, -1, 0, -1, 1, 1, 0], ![-1, -2, 1, -1, 0, -1, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [10, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12], [0, 1]]
 g := ![![[1, 4], [1], [3, 1]], ![[0, 9], [1], [6, 12]]]
 h' := ![![[3, 12], [6, 11], [9, 12], [0, 1]], ![[0, 1], [0, 2], [6, 1], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [2, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [10, 10, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3, -22, -22, -24, -13, -20, -20, -4]
  a := ![2, 0, 0, 0, 2, 2, 3, 1]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![45, 49, -22, -24, -13, -20, -20, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 2, 1, -1, 0, 1, 0, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![0, 2, 1, -1, 0, 1, 0, 0]] 
 ![![13, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0, 0, 0], ![6, 9, 1, 0, 0, 0, 0, 0], ![11, 3, 0, 1, 0, 0, 0, 0], ![8, 10, 0, 0, 1, 0, 0, 0], ![5, 9, 0, 0, 0, 1, 0, 0], ![6, 1, 0, 0, 0, 0, 1, 0], ![7, 10, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, 2, 1, -1, 0, 1, 0, 0], ![1, 0, 2, 1, -1, 0, 2, 0], ![0, 1, 0, 2, 1, -1, 0, 2], ![-1, 0, -1, 0, 0, 1, 0, 0], ![1, -1, 0, -1, 0, 0, 2, 0], ![0, 1, -1, 0, -1, 0, 0, 2], ![0, -1, -1, 0, -1, -1, 1, 0], ![-1, 0, -1, -1, 0, -1, -2, 1]]]
  hmulB := by decide  
  f := ![![![-4, -6, -3, -11, 0, 7, -4, -8]], ![![7, -4, 2, -3, -3, 0, 6, -4]], ![![3, -5, 0, -7, -2, 3, 2, -6]], ![![-2, -6, -2, -10, -1, 6, -2, -8]], ![![3, -7, 0, -9, -2, 4, 2, -8]], ![![3, -5, 0, -6, -2, 3, 2, -6]], ![![-1, -3, -1, -5, 0, 3, -1, -4]], ![![3, -6, 0, -8, -2, 4, 2, -7]]]
  g := ![![![0, -1, 1, -1, 0, 1, 0, 0], ![-2, -1, 2, 1, -1, 0, 2, 0], ![-3, -2, 0, 2, 1, -1, 0, 2], ![0, 0, -1, 0, 0, 1, 0, 0], ![0, 0, 0, -1, 0, 0, 2, 0], ![0, 0, -1, 0, -1, 0, 0, 2], ![1, 2, -1, 0, -1, -1, 1, 0], ![2, 1, -1, -1, 0, -1, -2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P1 : CertificateIrreducibleZModOfList' 13 2 2 3 [11, 0, 1] where
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
 g := ![![[], [4], [0, 1]], ![[], [4], [0, 12]]]
 h' := ![![[0, 12], [8], [0, 2], [0, 1]], ![[0, 1], [8], [0, 11], [0, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [0, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N1 : CertifiedPrimeIdeal' SI13N1 13 where
  n := 2
  hpos := by decide
  P := [11, 0, 1]
  hirr := P13P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-65, 218, -166, 130, -297, 194, 101, 342]
  a := ![3, -3, 1, 2, 11, 0, 5, -6]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-161, -75, -166, 130, -297, 194, 101, 342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N1 B_one_repr
lemma NI13N1 : Nat.card (O ⧸ I13N1) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 1, -2, 0, 1, 0, -1]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![0, 1, 1, -2, 0, 1, 0, -1]] 
 ![![13, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0, 0, 0], ![2, 12, 1, 0, 0, 0, 0, 0], ![2, 1, 0, 1, 0, 0, 0, 0], ![11, 3, 0, 0, 1, 0, 0, 0], ![7, 1, 0, 0, 0, 1, 0, 0], ![6, 4, 0, 0, 0, 0, 1, 0], ![5, 10, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, 1, 1, -2, 0, 1, 0, -1], ![1, 0, 2, 1, -1, 0, 1, 0], ![0, 1, 0, 2, 1, -1, 0, 1], ![-1, 0, 0, 0, 1, 1, -1, 0], ![1, -1, 0, 0, 0, 1, 2, -1], ![1, 1, 0, 0, 1, 0, 1, 2], ![0, 0, -1, 1, -1, 0, 1, 1], ![0, 0, -1, -1, 0, -1, 1, 1]]]
  hmulB := by decide  
  f := ![![![-3, -5, -4, -11, 0, 7, -3, -10]], ![![7, -3, 5, -4, -1, 0, 4, -3]], ![![6, -3, 4, -5, -1, 1, 3, -4]], ![![0, -1, 0, -2, 0, 1, 0, -2]], ![![-1, -5, -2, -10, 0, 6, -2, -9]], ![![-1, -3, -2, -6, 0, 4, -1, -6]], ![![1, -3, 0, -6, 0, 3, 0, -5]], ![![4, -4, 2, -7, -1, 3, 2, -6]]]
  g := ![![![0, 0, 1, -2, 0, 1, 0, -1], ![0, -2, 2, 1, -1, 0, 1, 0], ![-1, -1, 0, 2, 1, -1, 0, 1], ![-1, 0, 0, 0, 1, 1, -1, 0], ![-1, 0, 0, 0, 0, 1, 2, -1], ![-2, -2, 0, 0, 1, 0, 1, 2], ![0, 0, -1, 1, -1, 0, 1, 1], ![0, 0, -1, -1, 0, -1, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P2 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [3, 12], [0, 1]]
 g := ![![[10, 1], [12], [3, 1]], ![[0, 12], [12], [6, 12]]]
 h' := ![![[3, 12], [10, 1], [10, 8], [0, 1]], ![[0, 1], [0, 12], [8, 5], [3, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [11, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N2 : CertifiedPrimeIdeal' SI13N2 13 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P13P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61, 0, -58, 30, -69, -2, 144, -26]
  a := ![1, 1, -4, 2, -5, 0, 1, 1]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![12, 43, -58, 30, -69, -2, 144, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N2 B_one_repr
lemma NI13N2 : Nat.card (O ⧸ I13N2) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N2

def I13N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, 1, 2, 0, -1, 0, 1]] i)))

def SI13N3: IdealEqSpanCertificate' Table ![![0, -1, 1, 2, 0, -1, 0, 1]] 
 ![![13, 0, 0, 0, 0, 0, 0, 0], ![0, 13, 0, 0, 0, 0, 0, 0], ![2, 1, 1, 0, 0, 0, 0, 0], ![11, 1, 0, 1, 0, 0, 0, 0], ![11, 10, 0, 0, 1, 0, 0, 0], ![6, 1, 0, 0, 0, 1, 0, 0], ![6, 9, 0, 0, 0, 0, 1, 0], ![8, 10, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, -1, 1, 2, 0, -1, 0, 1], ![-1, 0, -2, 1, 1, 0, -1, 0], ![0, -1, 0, -2, 1, 1, 0, -1], ![1, 0, 0, 0, -1, 1, 1, 0], ![1, 1, 0, 0, 0, -1, 2, 1], ![-1, 1, 0, 0, -1, 0, -1, 2], ![0, 0, -1, -1, -1, 0, 1, -1], ![0, 0, 1, -1, 0, -1, -1, 1]]]
  hmulB := by decide  
  f := ![![![-3, 5, -4, 11, 0, -7, -3, 10]], ![![-7, -3, -5, -4, 1, 0, -4, -3]], ![![-1, 0, -1, 1, 0, -1, -1, 1]], ![![-3, 4, -4, 9, 0, -6, -3, 8]], ![![-8, 2, -7, 6, 1, -6, -6, 6]], ![![-2, 2, -2, 5, 0, -3, -2, 4]], ![![-6, 0, -5, 2, 1, -3, -4, 2]], ![![-7, 1, -6, 4, 1, -4, -5, 4]]]
  g := ![![![-2, -1, 1, 2, 0, -1, 0, 1], ![-1, 0, -2, 1, 1, 0, -1, 0], ![1, 0, 0, -2, 1, 1, 0, -1], ![0, 0, 0, 0, -1, 1, 1, 0], ![-1, -2, 0, 0, 0, -1, 2, 1], ![0, 0, 0, 0, -1, 0, -1, 2], ![2, 1, -1, -1, -1, 0, 1, -1], ![1, 0, 1, -1, 0, -1, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P3 : CertificateIrreducibleZModOfList' 13 2 2 3 [6, 9, 1] where
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

def PI13N3 : CertifiedPrimeIdeal' SI13N3 13 where
  n := 2
  hpos := by decide
  P := [6, 9, 1]
  hirr := P13P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6, 3, -11, 14, -21, -29, -48, -20]
  a := ![5, 3, 1, 2, 1, -1, 8, 4]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![55, 67, -11, 14, -21, -29, -48, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N3 : Ideal.IsPrime I13N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N3 B_one_repr
lemma NI13N3 : Nat.card (O ⧸ I13N3) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N3
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![0, -2, 1, 1, 0, -1, 0, 0]] ![![0, 2, 1, -1, 0, 1, 0, 0]]
  ![![-3, 0, -4, 0, 4, 0, -4, 0]] where
 M := ![![![-3, 0, -4, 0, 4, 0, -4, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![-3, 0, -4, 0, 4, 0, -4, 0]] ![![0, 1, 1, -2, 0, 1, 0, -1]]
  ![![4, -11, 1, -6, 0, 5, 4, -9]] where
 M := ![![![4, -11, 1, -6, 0, 5, 4, -9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI13N2 : IdealMulLeCertificate' Table 
  ![![4, -11, 1, -6, 0, 5, 4, -9]] ![![0, -1, 1, 2, 0, -1, 0, 1]]
  ![![13, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![0, 0, 13, 0, -13, 0, 13, 0]]]
 hmul := by decide  
 g := ![![![![0, 0, 1, 0, -1, 0, 1, 0]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2, I13N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
    exact isPrimeI13N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1 ⊙ MulI13N2)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -2, -4, -1, 2, 1, -3, -2]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-2, -2, -4, -1, 2, 1, -3, -2]] 
 ![![17, 0, 0, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0, 0, 0], ![13, 15, 1, 0, 0, 0, 0, 0], ![9, 9, 0, 1, 0, 0, 0, 0], ![2, 10, 0, 0, 1, 0, 0, 0], ![6, 5, 0, 0, 0, 1, 0, 0], ![2, 8, 0, 0, 0, 0, 1, 0], ![15, 1, 0, 0, 0, 0, 0, 1]] where
  M :=![![![-2, -2, -4, -1, 2, 1, -3, -2], ![1, -2, 0, -4, 1, 2, 0, -3], ![2, 1, 1, 0, -1, 1, 1, 0], ![1, 2, 1, 1, 0, -1, 2, 1], ![-1, 1, 1, 1, 0, 0, -1, 2], ![0, -1, -1, 1, -1, 0, 2, -1], ![1, 1, 2, 0, 0, -1, 1, 2], ![-1, 1, -1, 2, -2, 0, 0, 1]]]
  hmulB := by decide  
  f := ![![![3, -6, 9, -5, -7, -1, 5, -4]], ![![-1, 3, -2, 9, -1, -7, -6, 5]], ![![1, -2, 5, 4, -6, -7, -2, 1]], ![![1, -2, 4, 2, -4, -4, -1, 0]], ![![0, 1, 0, 5, -1, -4, -3, 2]], ![![1, -1, 3, 1, -2, -2, 0, 0]], ![![0, 1, 0, 4, -1, -3, -2, 2]], ![![3, -5, 8, -4, -6, -1, 5, -3]]]
  g := ![![![5, 4, -4, -1, 2, 1, -3, -2], ![4, 1, 0, -4, 1, 2, 0, -3], ![-1, -1, 1, 0, -1, 1, 1, 0], ![-2, -2, 1, 1, 0, -1, 2, 1], ![-3, -1, 1, 1, 0, 0, -1, 2], ![1, 0, -1, 1, -1, 0, 2, -1], ![-3, -2, 2, 0, 0, -1, 1, 2], ![-1, 1, -1, 2, -2, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [13, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 16], [0, 1]]
 g := ![![[3, 4], [8], [8], [1]], ![[0, 13], [8], [8], [1]]]
 h' := ![![[12, 16], [7, 15], [14, 5], [4, 12], [0, 1]], ![[0, 1], [0, 2], [6, 12], [12, 5], [12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [9, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [13, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17, 35, -98, 32, -151, 50, 94, 42]
  a := ![2, -1, 2, 0, 7, 0, 4, -2]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![9, 99, -98, 32, -151, 50, 94, 42]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 2, -1, -1, 1, 3, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![4, 1, 2, -1, -1, 1, 3, 0]] 
 ![![17, 0, 0, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0, 0, 0], ![13, 7, 1, 0, 0, 0, 0, 0], ![11, 15, 0, 1, 0, 0, 0, 0], ![9, 8, 0, 0, 1, 0, 0, 0], ![15, 4, 0, 0, 0, 1, 0, 0], ![0, 2, 0, 0, 0, 0, 1, 0], ![8, 3, 0, 0, 0, 0, 0, 1]] where
  M :=![![![4, 1, 2, -1, -1, 1, 3, 0], ![1, 4, 1, 2, -1, -1, 2, 3], ![-1, 1, 1, 1, -1, -1, 1, 2], ![-1, -1, -1, 1, -1, -1, 0, 1], ![-1, -1, -2, -1, 0, -1, -1, 0], ![-1, -1, -1, -2, -1, 0, -2, -1], ![-2, -1, -1, 0, 0, -1, -2, -1], ![-1, -2, 0, -1, 1, 0, -3, -2]]]
  hmulB := by decide  
  f := ![![![3, 5, -6, 6, 2, -1, -4, 7]], ![![-1, 3, -2, -6, -1, 2, 5, -4]], ![![2, 5, -5, 2, 1, 0, -1, 4]], ![![1, 6, -6, -1, 0, 1, 2, 1]], ![![1, 4, -4, 0, 1, 0, 0, 2]], ![![2, 5, -6, 4, 1, 0, -3, 5]], ![![0, 0, 0, -1, 0, 0, 1, -1]], ![![1, 3, -3, 2, 1, 0, -2, 3]]]
  g := ![![![-1, 0, 2, -1, -1, 1, 3, 0], ![-2, -2, 1, 2, -1, -1, 2, 3], ![-1, -1, 1, 1, -1, -1, 1, 2], ![1, 0, -1, 1, -1, -1, 0, 1], ![3, 2, -2, -1, 0, -1, -1, 0], ![3, 3, -1, -2, -1, 0, -2, -1], ![2, 1, -1, 0, 0, -1, -2, -1], ![1, 1, 0, -1, 1, 0, -3, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [16, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 16], [0, 1]]
 g := ![![[5, 16], [1], [8], [1]], ![[0, 1], [1], [8], [1]]]
 h' := ![![[5, 16], [14, 4], [9, 16], [1, 5], [0, 1]], ![[0, 1], [0, 13], [4, 1], [9, 12], [5, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [16, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [16, 12, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-160, 244, 241, 10, 359, -18, -727, 624]
  a := ![-6, 8, 4, 1, -1, 1, -7, 14]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-668, -283, 241, 10, 359, -18, -727, 624]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -1, 1, -1, -1, 1, 1, -2]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-1, -1, 1, -1, -1, 1, 1, -2]] 
 ![![17, 0, 0, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0, 0, 0], ![13, 10, 1, 0, 0, 0, 0, 0], ![6, 15, 0, 1, 0, 0, 0, 0], ![9, 9, 0, 0, 1, 0, 0, 0], ![2, 4, 0, 0, 0, 1, 0, 0], ![0, 15, 0, 0, 0, 0, 1, 0], ![9, 3, 0, 0, 0, 0, 0, 1]] where
  M :=![![![-1, -1, 1, -1, -1, 1, 1, -2], ![1, -1, 1, 1, 1, -1, 0, 1], ![-1, 1, -2, 1, 0, 1, -1, 0], ![1, -1, 1, -2, 1, 0, 2, -1], ![0, 1, 0, 1, -1, 1, -1, 2], ![1, 0, -1, 0, -1, -1, 4, -1], ![0, 1, 0, 0, 1, -1, -2, 3], ![-1, 0, -2, 0, -3, 1, 1, -2]]]
  hmulB := by decide  
  f := ![![![-16, -3, -8, 4, 3, -5, -10, 3]], ![![-5, -16, -6, -8, 1, 3, -7, -10]], ![![-15, -12, -10, -2, 3, -2, -12, -4]], ![![-10, -15, -8, -6, 2, 1, -10, -8]], ![![-11, -10, -7, -2, 2, -1, -9, -4]], ![![-3, -4, -2, -1, 1, 0, -3, -2]], ![![-4, -14, -5, -7, 1, 3, -6, -9]], ![![-9, -4, -5, 1, 2, -2, -6, 0]]]
  g := ![![![1, 0, 1, -1, -1, 1, 1, -2], ![-2, -2, 1, 1, 1, -1, 0, 1], ![1, 1, -2, 1, 0, 1, -1, 0], ![0, -1, 1, -2, 1, 0, 2, -1], ![-1, 0, 0, 1, -1, 1, -1, 2], ![2, -2, -1, 0, -1, -1, 4, -1], ![-2, 1, 0, 0, 1, -1, -2, 3], ![4, 2, -2, 0, -3, 1, 1, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P2 : CertificateIrreducibleZModOfList' 17 2 2 4 [10, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 16], [0, 1]]
 g := ![![[2, 2], [1], [9], [1]], ![[13, 15], [1], [9], [1]]]
 h' := ![![[14, 16], [5, 11], [10, 16], [7, 14], [0, 1]], ![[0, 1], [6, 6], [13, 1], [16, 3], [14, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [16, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N2 : CertifiedPrimeIdeal' SI17N2 17 where
  n := 2
  hpos := by decide
  P := [10, 3, 1]
  hirr := P17P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![135, -338, 897, -299, 1411, -539, -1075, -393]
  a := ![4, 14, 6, -1, 3, -1, 6, 27]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1048, 114, 897, -299, 1411, -539, -1075, -393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N2 B_one_repr
lemma NI17N2 : Nat.card (O ⧸ I17N2) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N2

def I17N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, 1, -1, -1, 1, 1, 0]] i)))

def SI17N3: IdealEqSpanCertificate' Table ![![-1, 0, 1, -1, -1, 1, 1, 0]] 
 ![![17, 0, 0, 0, 0, 0, 0, 0], ![0, 17, 0, 0, 0, 0, 0, 0], ![13, 2, 1, 0, 0, 0, 0, 0], ![8, 9, 0, 1, 0, 0, 0, 0], ![2, 7, 0, 0, 1, 0, 0, 0], ![11, 5, 0, 0, 0, 1, 0, 0], ![2, 9, 0, 0, 0, 0, 1, 0], ![2, 1, 0, 0, 0, 0, 0, 1]] where
  M :=![![![-1, 0, 1, -1, -1, 1, 1, 0], ![1, -1, 0, 1, -1, -1, 2, 1], ![-1, 1, -2, 0, 0, -1, -1, 2], ![-1, -1, -1, -2, -2, 0, 0, -1], ![0, -1, 0, -1, -1, -2, -1, 0], ![-2, 0, -1, 0, -1, -1, -4, -1], ![0, -1, 0, 0, 1, -1, -2, -2], ![-1, 0, 1, 0, 2, 1, -4, -2]]]
  hmulB := by decide  
  f := ![![![-16, -4, -8, 3, 6, -1, -13, 2]], ![![-1, -16, -6, -8, 1, 6, 0, -13]], ![![-12, -5, -7, 1, 5, 0, -10, 0]], ![![-8, -10, -7, -3, 3, 3, -6, -6]], ![![-2, -7, -3, -3, 1, 2, -1, -5]], ![![-11, -7, -7, 0, 4, 1, -9, -2]], ![![-2, -9, -4, -4, 1, 3, -1, -7]], ![![-2, -1, -1, 0, 1, 0, -2, 0]]]
  g := ![![![-1, 0, 1, -1, -1, 1, 1, 0], ![0, -1, 0, 1, -1, -1, 2, 1], ![2, 1, -2, 0, 0, -1, -1, 2], ![2, 2, -1, -2, -2, 0, 0, -1], ![2, 2, 0, -1, -1, -2, -1, 0], ![2, 3, -1, 0, -1, -1, -4, -1], ![1, 1, 0, 0, 1, -1, -2, -2], ![-1, 1, 1, 0, 2, 1, -4, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P3 : CertificateIrreducibleZModOfList' 17 2 2 4 [11, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16], [0, 1]]
 g := ![![[4, 8], [4], [15], [1]], ![[9, 9], [4], [15], [1]]]
 h' := ![![[7, 16], [5, 5], [7, 2], [6, 7], [0, 1]], ![[0, 1], [6, 12], [4, 15], [4, 10], [7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [15, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N3 : CertifiedPrimeIdeal' SI17N3 17 where
  n := 2
  hpos := by decide
  P := [11, 10, 1]
  hirr := P17P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-206, 1884, 6274, 6, 5796, -158, -6327, 4182]
  a := ![-7, 82, 1, 0, 0, 0, -14, 79]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-5140, 133, 6274, 6, 5796, -158, -6327, 4182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N3 : Ideal.IsPrime I17N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N3 B_one_repr
lemma NI17N3 : Nat.card (O ⧸ I17N3) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N3
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-2, -2, -4, -1, 2, 1, -3, -2]] ![![4, 1, 2, -1, -1, 1, 3, 0]]
  ![![0, -9, -11, -9, 6, 6, -6, -9]] where
 M := ![![![0, -9, -11, -9, 6, 6, -6, -9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![0, -9, -11, -9, 6, 6, -6, -9]] ![![-1, -1, 1, -1, -1, 1, 1, -2]]
  ![![8, 7, 16, 4, -9, -5, 14, 6]] where
 M := ![![![8, 7, 16, 4, -9, -5, 14, 6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N2 : IdealMulLeCertificate' Table 
  ![![8, 7, 16, 4, -9, -5, 14, 6]] ![![-1, 0, 1, -1, -1, 1, 1, 0]]
  ![![17, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![-17, 0, -17, 0, 17, 0, -17, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, -1, 0, 1, 0, -1, 0]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2, I17N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
    exact isPrimeI17N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1 ⊙ MulI17N2)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -2, 0, 1, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![0, -2, 0, 1, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0, 0, 0], ![17, 0, 1, 0, 0, 0, 0, 0], ![0, 17, 0, 1, 0, 0, 0, 0], ![15, 0, 0, 0, 1, 0, 0, 0], ![0, 15, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![0, 6, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, -2, 0, 1, 0, 0, 0, 0], ![0, 0, -2, 0, 1, 0, 0, 0], ![0, 0, 0, -2, 0, 1, 0, 0], ![1, 0, 0, 0, -2, 0, 2, 0], ![0, 1, 0, 0, 0, -2, 0, 2], ![-2, 0, -1, 0, -2, 0, -2, 0], ![0, 0, 0, -1, 0, -1, 0, -1], ![-1, 0, 1, 0, 0, 0, -3, 0]]]
  hmulB := by decide  
  f := ![![![0, 14, 0, 17, 0, -10, 0, 18]], ![![-10, 0, -4, 0, -1, 0, -2, 0]], ![![0, 12, 0, 15, 0, -9, 0, 16]], ![![-9, 0, -4, 0, -1, 0, -2, 0]], ![![0, 11, 0, 13, 0, -8, 0, 14]], ![![-8, 0, -3, 0, -1, 0, -2, 0]], ![![0, 4, 0, 5, 0, -3, 0, 5]], ![![-3, 0, -1, 0, 0, 0, -1, 0]]]
  g := ![![![0, -1, 0, 1, 0, 0, 0, 0], ![1, 0, -2, 0, 1, 0, 0, 0], ![0, 1, 0, -2, 0, 1, 0, 0], ![1, 0, 0, 0, -2, 0, 2, 0], ![0, 1, 0, 0, 0, -2, 0, 2], ![3, 0, -1, 0, -2, 0, -2, 0], ![0, 2, 0, -1, 0, -1, 0, -1], ![0, 0, 1, 0, 0, 0, -3, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [2, 18, 1] where
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
 g := ![![[9, 4], [16, 9], [1], [1]], ![[13, 15], [6, 10], [1], [1]]]
 h' := ![![[1, 18], [6, 2], [2, 16], [17, 1], [0, 1]], ![[0, 1], [8, 17], [18, 3], [18, 18], [1, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [8, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [2, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21, -702, -815, -502, -1123, -556, 1659, -1054]
  a := ![1, 4, 0, -6, 29, 0, 2, 7]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![1093, 1184, -815, -502, -1123, -556, 1659, -1054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 2, 1, -1, -1, 2, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![2, 1, 2, 1, -1, -1, 2, 1]] 
 ![![19, 0, 0, 0, 0, 0, 0, 0], ![5, 1, 0, 0, 0, 0, 0, 0], ![13, 0, 1, 0, 0, 0, 0, 0], ![11, 0, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 0, 1, 0, 0, 0], ![9, 0, 0, 0, 0, 1, 0, 0], ![16, 0, 0, 0, 0, 0, 1, 0], ![15, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![2, 1, 2, 1, -1, -1, 2, 1], ![-1, 2, 0, 2, 0, -1, -1, 2], ![-1, -1, 0, 0, 0, 0, 0, -1], ![0, -1, 0, 0, 1, 0, -1, 0], ![0, 0, -1, 0, 0, 1, 0, -1], ![1, 0, 1, -1, 1, 0, 1, 0], ![-1, 0, -1, 0, 0, 1, -1, 0], ![1, -1, 0, -1, 0, 0, 2, -1]]]
  hmulB := by decide  
  f := ![![![1, -4, -11, 6, 6, -5, -9, -2]], ![![0, -1, -3, 1, 2, -1, -3, -1]], ![![1, -3, -7, 4, 4, -3, -6, -2]], ![![1, -2, -6, 4, 4, -3, -5, -1]], ![![0, 0, -1, 1, 1, 0, -1, 0]], ![![1, -2, -5, 3, 3, -2, -3, -1]], ![![1, -3, -9, 5, 5, -4, -7, -1]], ![![1, -3, -9, 5, 4, -4, -6, -1]]]
  g := ![![![-4, 1, 2, 1, -1, -1, 2, 1], ![-2, 2, 0, 2, 0, -1, -1, 2], ![1, -1, 0, 0, 0, 0, 0, -1], ![1, -1, 0, 0, 1, 0, -1, 0], ![1, 0, -1, 0, 0, 1, 0, -1], ![-1, 0, 1, -1, 1, 0, 1, 0], ![1, 0, -1, 0, 0, 1, -1, 0], ![0, -1, 0, -1, 0, 0, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1

def I19N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -2, 1, 0, 0, 0, 0, -1]] i)))

def SI19N2: IdealEqSpanCertificate' Table ![![0, -2, 1, 0, 0, 0, 0, -1]] 
 ![![19, 0, 0, 0, 0, 0, 0, 0], ![14, 1, 0, 0, 0, 0, 0, 0], ![13, 0, 1, 0, 0, 0, 0, 0], ![8, 0, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 0, 1, 0, 0, 0], ![10, 0, 0, 0, 0, 1, 0, 0], ![16, 0, 0, 0, 0, 0, 1, 0], ![4, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, -2, 1, 0, 0, 0, 0, -1], ![0, 0, -1, 1, 1, 0, -1, 0], ![0, 0, 0, -1, 1, 1, 0, -1], ![1, 0, 1, 0, 0, 1, 1, 0], ![1, 1, 0, 1, 0, 0, 2, 1], ![0, 1, 0, 0, 0, 0, 1, 2], ![0, 1, -1, 0, -1, 0, 1, 1], ![0, 0, 0, -1, -1, -1, 1, 1]]]
  hmulB := by decide  
  f := ![![![-10, 17, -4, 22, -3, -12, -5, 18]], ![![-8, 12, -3, 16, -2, -9, -4, 13]], ![![-7, 11, -3, 15, -2, -8, -4, 12]], ![![-4, 7, -2, 9, -1, -5, -2, 7]], ![![-1, 2, 0, 2, 0, -1, -1, 2]], ![![-5, 9, -2, 12, -2, -6, -2, 9]], ![![-8, 14, -3, 18, -2, -10, -4, 15]], ![![-2, 4, -1, 5, -1, -2, -1, 4]]]
  g := ![![![1, -2, 1, 0, 0, 0, 0, -1], ![1, 0, -1, 1, 1, 0, -1, 0], ![0, 0, 0, -1, 1, 1, 0, -1], ![-2, 0, 1, 0, 0, 1, 1, 0], ![-3, 1, 0, 1, 0, 0, 2, 1], ![-2, 1, 0, 0, 0, 0, 1, 2], ![-1, 1, -1, 0, -1, 0, 1, 1], ![0, 0, 0, -1, -1, -1, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N2 : Nat.card (O ⧸ I19N2) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N2)

lemma isPrimeI19N2 : Ideal.IsPrime I19N2 := prime_ideal_of_norm_prime hp19.out _ NI19N2

def I19N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 2, 0, 3, 0, -2, 0, 2]] i)))

def SI19N3: IdealEqSpanCertificate' Table ![![0, 2, 0, 3, 0, -2, 0, 2]] 
 ![![19, 0, 0, 0, 0, 0, 0, 0], ![0, 19, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![0, 16, 0, 1, 0, 0, 0, 0], ![10, 0, 0, 0, 1, 0, 0, 0], ![0, 10, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![0, 6, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, 2, 0, 3, 0, -2, 0, 2], ![-2, 0, 0, 0, 1, 0, -2, 0], ![0, -2, 0, 0, 0, 1, 0, -2], ![1, 0, 0, 0, 2, 0, 0, 0], ![0, 1, 0, 0, 0, 2, 0, 0], ![2, 0, 1, 0, 0, 0, 4, 0], ![0, 0, 0, -1, 0, 1, 0, 1], ![1, 0, -1, 0, -2, 0, 3, 0]]]
  hmulB := by decide  
  f := ![![![0, -14, 0, 3, 0, -4, 0, -4]], ![![-4, 0, -10, 0, 7, 0, -12, 0]], ![![0, -12, 0, 2, 0, -3, 0, -4]], ![![-3, 0, -8, 0, 6, 0, -10, 0]], ![![0, -7, 0, 2, 0, -2, 0, -2]], ![![-2, 0, -5, 0, 4, 0, -6, 0]], ![![0, -4, 0, 1, 0, -1, 0, -1]], ![![-1, 0, -3, 0, 2, 0, -3, 0]]]
  g := ![![![0, -2, 0, 3, 0, -2, 0, 2], ![0, 0, 0, 0, 1, 0, -2, 0], ![0, 0, 0, 0, 0, 1, 0, -2], ![-1, 0, 0, 0, 2, 0, 0, 0], ![0, -1, 0, 0, 0, 2, 0, 0], ![-2, 0, 1, 0, 0, 0, 4, 0], ![0, 0, 0, -1, 0, 1, 0, 1], ![1, 0, -1, 0, -2, 0, 3, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P3 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 6, 1] where
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
 g := ![![[18, 17], [11, 9], [17], [1]], ![[11, 2], [14, 10], [17], [1]]]
 h' := ![![[13, 18], [9, 13], [5, 16], [6, 13], [0, 1]], ![[0, 1], [7, 6], [4, 3], [4, 6], [13, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [17, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N3 : CertifiedPrimeIdeal' SI19N3 19 where
  n := 2
  hpos := by decide
  P := [13, 6, 1]
  hirr := P19P3
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-368, 208, 1550, 304, 2507, 472, -3471, 84]
  a := ![-1, -18, 0, -2, 4, -2, 0, -37]
  z := ![1, 0, 0, 0, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1548, -520, 1550, 304, 2507, 472, -3471, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N3 : Ideal.IsPrime I19N3 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N3 B_one_repr
lemma NI19N3 : Nat.card (O ⧸ I19N3) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N3

def I19N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 2, -1, 2, 0, -1, -1, 2]] i)))

def SI19N4: IdealEqSpanCertificate' Table ![![-1, 2, -1, 2, 0, -1, -1, 2]] 
 ![![19, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![10, 0, 1, 0, 0, 0, 0, 0], ![8, 0, 0, 1, 0, 0, 0, 0], ![14, 0, 0, 0, 1, 0, 0, 0], ![15, 0, 0, 0, 0, 1, 0, 0], ![16, 0, 0, 0, 0, 0, 1, 0], ![9, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![-1, 2, -1, 2, 0, -1, -1, 2], ![-1, -1, 0, -1, 0, 0, 0, -1], ![0, -1, 0, 0, 0, 0, -1, 0], ![0, 0, -1, 0, 0, 0, 0, -1], ![0, 0, 1, -1, 1, 0, -1, 0], ![0, 0, 0, 1, -1, 1, 0, -1], ![1, -1, 1, -1, 1, 0, 1, -1], ![0, 1, 0, 1, 0, 1, -1, 1]]]
  hmulB := by decide  
  f := ![![![-6, -17, 4, 5, 3, -1, -4, -5]], ![![-1, -3, 0, 1, 1, 0, -1, -1]], ![![-3, -9, 2, 2, 2, 0, -2, -3]], ![![-2, -7, 2, 2, 1, 0, -1, -2]], ![![-4, -12, 3, 4, 2, -1, -2, -3]], ![![-5, -13, 3, 4, 2, -1, -3, -3]], ![![-5, -14, 3, 4, 2, -1, -3, -4]], ![![-3, -8, 2, 2, 1, -1, -2, -2]]]
  g := ![![![0, 2, -1, 2, 0, -1, -1, 2], ![1, -1, 0, -1, 0, 0, 0, -1], ![1, -1, 0, 0, 0, 0, -1, 0], ![1, 0, -1, 0, 0, 0, 0, -1], ![0, 0, 1, -1, 1, 0, -1, 0], ![0, 0, 0, 1, -1, 1, 0, -1], ![-1, -1, 1, -1, 1, 0, 1, -1], ![-1, 1, 0, 1, 0, 1, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N4 : Nat.card (O ⧸ I19N4) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N4)

lemma isPrimeI19N4 : Ideal.IsPrime I19N4 := prime_ideal_of_norm_prime hp19.out _ NI19N4

def I19N5 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -1, -2, 0, 1, 0, -1, 0]] i)))

def SI19N5: IdealEqSpanCertificate' Table ![![0, -1, -2, 0, 1, 0, -1, 0]] 
 ![![19, 0, 0, 0, 0, 0, 0, 0], ![16, 1, 0, 0, 0, 0, 0, 0], ![10, 0, 1, 0, 0, 0, 0, 0], ![11, 0, 0, 1, 0, 0, 0, 0], ![14, 0, 0, 0, 1, 0, 0, 0], ![4, 0, 0, 0, 0, 1, 0, 0], ![16, 0, 0, 0, 0, 0, 1, 0], ![10, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![0, -1, -2, 0, 1, 0, -1, 0], ![0, 0, -1, -2, 0, 1, 0, -1], ![1, 0, 1, -1, -1, 0, 1, 0], ![0, 1, 0, 1, -1, -1, 0, 1], ![-1, 0, 0, 0, 0, -1, -1, 0], ![-1, -1, 0, 0, 0, 0, -2, -1], ![0, 0, 1, 0, 0, 0, 0, -1], ![0, 0, 1, 1, 1, 0, -1, 0]]]
  hmulB := by decide  
  f := ![![![12, 4, 11, 10, -6, -2, 8, 9]], ![![10, 4, 9, 9, -5, -2, 7, 8]], ![![6, 2, 6, 5, -3, -1, 4, 5]], ![![7, 2, 6, 6, -4, -1, 5, 5]], ![![9, 3, 8, 7, -4, -2, 6, 7]], ![![2, 1, 2, 2, -2, 0, 1, 2]], ![![10, 3, 9, 8, -5, -2, 7, 7]], ![![6, 2, 6, 5, -3, -1, 3, 5]]]
  g := ![![![2, -1, -2, 0, 1, 0, -1, 0], ![2, 0, -1, -2, 0, 1, 0, -1], ![0, 0, 1, -1, -1, 0, 1, 0], ![-1, 1, 0, 1, -1, -1, 0, 1], ![1, 0, 0, 0, 0, -1, -1, 0], ![3, -1, 0, 0, 0, 0, -2, -1], ![0, 0, 1, 0, 0, 0, 0, -1], ![-1, 0, 1, 1, 1, 0, -1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N5 : Nat.card (O ⧸ I19N5) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N5)

lemma isPrimeI19N5 : Ideal.IsPrime I19N5 := prime_ideal_of_norm_prime hp19.out _ NI19N5
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![0, -2, 0, 1, 0, 0, 0, 0]] ![![2, 1, 2, 1, -1, -1, 2, 1]]
  ![![2, -5, 0, -4, 1, 2, 1, -4]] where
 M := ![![![2, -5, 0, -4, 1, 2, 1, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N1 : IdealMulLeCertificate' Table 
  ![![2, -5, 0, -4, 1, 2, 1, -4]] ![![0, -2, 1, 0, 0, 0, 0, -1]]
  ![![-3, 0, 2, 0, -2, 0, 2, 0]] where
 M := ![![![-3, 0, 2, 0, -2, 0, 2, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N2 : IdealMulLeCertificate' Table 
  ![![-3, 0, 2, 0, -2, 0, 2, 0]] ![![0, 2, 0, 3, 0, -2, 0, 2]]
  ![![0, -12, 0, -11, 0, 6, 0, -8]] where
 M := ![![![0, -12, 0, -11, 0, 6, 0, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N3 : IdealMulLeCertificate' Table 
  ![![0, -12, 0, -11, 0, 6, 0, -8]] ![![-1, 2, -1, 2, 0, -1, -1, 2]]
  ![![12, 4, 11, 10, -6, -2, 8, 9]] where
 M := ![![![12, 4, 11, 10, -6, -2, 8, 9]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI19N4 : IdealMulLeCertificate' Table 
  ![![12, 4, 11, 10, -6, -2, 8, 9]] ![![0, -1, -2, 0, 1, 0, -1, 0]]
  ![![19, 0, 0, 0, 0, 0, 0, 0]] where
 M := ![![![19, 0, 0, 0, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N1, I19N2, I19N3, I19N4, I19N5] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N1
    exact isPrimeI19N2
    exact isPrimeI19N3
    exact isPrimeI19N4
    exact isPrimeI19N5
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1 ⊙ MulI19N2 ⊙ MulI19N3 ⊙ MulI19N4)


lemma PB23I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 22 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 22 (by omega)

def PB23I0 : PrimesBelowBoundCertificateInterval O 1 22 23 where
  m := 8
  g := ![4, 2, 4, 2, 4, 4, 4, 6]
  P := ![2, 3, 5, 7, 11, 13, 17, 19]
  hP := PB23I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1, I2N1]
    · exact ![I3N0, I3N0]
    · exact ![I5N0, I5N0, I5N1, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N2, I11N3]
    · exact ![I13N0, I13N1, I13N2, I13N3]
    · exact ![I17N0, I17N1, I17N2, I17N3]
    · exact ![I19N0, I19N1, I19N2, I19N3, I19N4, I19N5]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![4, 4, 4, 4]
    · exact ![81, 81]
    · exact ![25, 25, 25, 25]
    · exact ![2401, 2401]
    · exact ![121, 121, 121, 121]
    · exact ![169, 169, 169, 169]
    · exact ![289, 289, 289, 289]
    · exact ![361, 19, 19, 361, 19, 19]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI2N0
      exact NI2N0
      exact NI2N1
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N0
      exact NI5N1
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
      exact NI11N3
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
      exact NI13N3
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
      exact NI17N3
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N1
      exact NI19N2
      exact NI19N3
      exact NI19N4
      exact NI19N5
  β := ![I2N0, I2N1, I19N1, I19N2, I19N4, I19N5]
  Il := ![[I2N0, I2N0, I2N1, I2N1], [], [], [], [], [], [], [I19N1, I19N2, I19N4, I19N5]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
