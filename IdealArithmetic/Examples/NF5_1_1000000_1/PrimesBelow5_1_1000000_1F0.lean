
import IdealArithmetic.Examples.NF5_1_1000000_1.RI5_1_1000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 2, -4, -1, 3]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![7, 2, -4, -1, 3]] 
 ![![2, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![7, 2, -4, -1, 3], ![9, 5, 3, -9, -5], ![-15, -2, 14, -3, -13], ![-24, -11, -1, 17, 6], ![9, 1, -8, 2, 7]]]
  hmulB := by decide  
  f := ![![![11, 22, 5, 12, 10]], ![![15, 19, 5, 11, 7]], ![![21, 38, 8, 21, 15]], ![![15, 23, 6, 13, 10]], ![![16, 31, 6, 17, 12]]]
  g := ![![![2, 2, -4, -1, 3], ![7, 5, 3, -9, -5], ![-1, -2, 14, -3, -13], ![-15, -11, -1, 17, 6], ![1, 1, -8, 2, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 9, 1, 5, 2]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![5, 9, 1, 5, 2]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![5, 9, 1, 5, 2], ![6, 13, 4, 7, 8], ![24, 25, 6, 15, 6], ![6, 19, 3, 10, 8], ![18, 10, 4, 7, 1]]]
  hmulB := by decide  
  f := ![![![16, 7, -1, -10, -2]], ![![5, 5, 8, -11, -10]], ![![-19, -6, 7, 6, -4]], ![![5, -3, -15, 11, 16]], ![![23, 9, -5, -11, 1]]]
  g := ![![![-6, 9, 1, 5, 2], ![-13, 13, 4, 7, 8], ![-14, 25, 6, 15, 6], ![-17, 19, 3, 10, 8], ![-2, 10, 4, 7, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1

def I2N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 0, 0, 1]] i)))

def SI2N2: IdealEqSpanCertificate' Table ![![-2, 0, 0, 0, 1]] 
 ![![2, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![-2, 0, 0, 0, 1], ![3, -1, 0, 0, -1], ![-3, 2, -1, 0, 1], ![0, -1, 1, -1, 0], ![-3, 2, -1, 1, 0]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0, -1, -1]], ![![-2, -2, 0, -1, -1]], ![![-2, -3, -1, -1, -1]], ![![0, -1, -1, -1, 0]], ![![0, -1, 0, -1, -1]]]
  g := ![![![-1, 0, 0, 0, 1], ![2, -1, 0, 0, -1], ![-2, 2, -1, 0, 1], ![0, -1, 1, -1, 0], ![-2, 2, -1, 1, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N2 : Nat.card (O ⧸ I2N2) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N2)

lemma isPrimeI2N2 : Ideal.IsPrime I2N2 := prime_ideal_of_norm_prime hp2.out _ NI2N2
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![7, 2, -4, -1, 3]] ![![5, 9, 1, 5, 2]]
  ![![-1, 0, 0, 0, 1]] where
 M := ![![![-1, 0, 0, 0, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N1 : IdealMulLeCertificate' Table 
  ![![-1, 0, 0, 0, 1]] ![![5, 9, 1, 5, 2]]
  ![![13, 1, 3, 2, -1]] where
 M := ![![![13, 1, 3, 2, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N2 : IdealMulLeCertificate' Table 
  ![![13, 1, 3, 2, -1]] ![![-2, 0, 0, 0, 1]]
  ![![-29, 1, 0, -3, 15]] where
 M := ![![![-29, 1, 0, -3, 15]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI2N3 : IdealMulLeCertificate' Table 
  ![![-29, 1, 0, -3, 15]] ![![-2, 0, 0, 0, 1]]
  ![![2, 0, 0, 0, 0]] where
 M := ![![![16, 32, -18, 18, -30]]]
 hmul := by decide  
 g := ![![![![8, 16, -9, 9, -15]]]]
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
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -1, 0, 1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![-2, -1, 0, 1, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 1, 1, 0, 0], ![2, 1, 0, 1, 0], ![2, 1, 0, 0, 1]] where
  M :=![![![-2, -1, 0, 1, 1], ![3, 0, -2, 1, 1], ![3, 3, -1, -3, 1], ![0, 0, 4, -3, -4], ![-6, 0, 0, 2, 1]]]
  hmulB := by decide  
  f := ![![![6, 9, 2, 5, 3]], ![![9, 16, 4, 9, 7]], ![![14, 21, 5, 12, 8]], ![![11, 18, 4, 10, 7]], ![![11, 16, 4, 9, 6]]]
  g := ![![![-2, -1, 0, 1, 1], ![1, 0, -2, 1, 1], ![3, 2, -1, -3, 1], ![2, 1, 4, -3, -4], ![-4, -1, 0, 2, 1]]]
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
  c := ![41, 274, 76, 313, 134]
  a := ![0, -7, 2, -8, -11]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-335, -83, 76, 313, 134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -2, 1, -1, 1]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![0, -2, 1, -1, 1]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![0, -2, 1, -1, 1], ![3, 1, -1, 1, -3], ![-9, 0, 0, -1, 5], ![6, -3, 1, -1, -2], ![-12, 3, -1, 0, 5]]]
  hmulB := by decide  
  f := ![![![-4, -2, 1, 1, -1]], ![![-1, -1, -1, 1, 1]], ![![3, 0, -2, -1, 1]], ![![2, 1, 1, -3, -2]], ![![-2, -1, 1, 0, -1]]]
  g := ![![![0, -2, 1, -1, 1], ![1, 1, -1, 1, -3], ![-3, 0, 0, -1, 5], ![2, -3, 1, -1, -2], ![-4, 3, -1, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1

def I3N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, -11, -3, -6, -4]] i)))

def SI3N2: IdealEqSpanCertificate' Table ![![-7, -11, -3, -6, -4]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![2, 2, 1, 0, 0], ![1, 1, 0, 1, 0], ![1, 2, 0, 0, 1]] where
  M :=![![![-7, -11, -3, -6, -4], ![-12, -20, -5, -12, -8], ![-24, -37, -8, -22, -16], ![-18, -25, -5, -13, -10], ![-12, -19, -5, -10, -7]]]
  hmulB := by decide  
  f := ![![![-9, 3, -1, 0, 4]], ![![12, -6, 3, -2, -4]], ![![-2, 1, 0, 0, 0]], ![![-1, -2, 1, -1, 2]], ![![5, 0, 0, 0, -3]]]
  g := ![![![3, 3, -3, -6, -4], ![6, 6, -5, -12, -8], ![10, 11, -8, -22, -16], ![5, 6, -5, -13, -10], ![5, 5, -5, -10, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P2 : CertificateIrreducibleZModOfList' 3 2 2 1 [2, 1, 1] where
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

def PI3N2 : CertifiedPrimeIdeal' SI3N2 3 where
  n := 2
  hpos := by decide
  P := [2, 1, 1]
  hirr := P3P2
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11906, 22538, 8022, 14198, 6936]
  a := ![3, -62, -1, -63, -58]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-8424, -7192, 8022, 14198, 6936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N2 : Ideal.IsPrime I3N2 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N2 B_one_repr
lemma NI3N2 : Nat.card (O ⧸ I3N2) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N2
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![-2, -1, 0, 1, 1]] ![![0, -2, 1, -1, 1]]
  ![![-9, 3, -1, 0, 4]] where
 M := ![![![-9, 3, -1, 0, 4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI3N1 : IdealMulLeCertificate' Table 
  ![![-9, 3, -1, 0, 4]] ![![-7, -11, -3, -6, -4]]
  ![![3, 0, 0, 0, 0]] where
 M := ![![![3, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, -3, 0, -1, -3]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![4, -3, 0, -1, -3]] 
 ![![5, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![4, -3, 0, -1, -3], ![-9, 0, -2, -1, 1], ![3, -11, 1, -5, -3], ![0, -2, -2, -1, -4], ![0, -8, 2, -4, 1]]]
  hmulB := by decide  
  f := ![![![-16, -7, 2, 9, 1]], ![![-9, -5, -2, 8, 4]], ![![7, 2, -3, -2, 2]], ![![-4, 0, 6, -3, -6]], ![![-6, -2, 2, 2, -1]]]
  g := ![![![3, -3, 0, -1, -3], ![-1, 0, -2, -1, 1], ![9, -11, 1, -5, -3], ![2, -2, -2, -1, -4], ![6, -8, 2, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![4, -3, 0, -1, -3]] ![![4, -3, 0, -1, -3]]
  ![![43, 14, 2, 12, -14]] where
 M := ![![![43, 14, 2, 12, -14]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![43, 14, 2, 12, -14]] ![![4, -3, 0, -1, -3]]
  ![![52, -63, -78, -23, -183]] where
 M := ![![![52, -63, -78, -23, -183]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![52, -63, -78, -23, -183]] ![![4, -3, 0, -1, -3]]
  ![![541, 2212, -272, 1156, -76]] where
 M := ![![![541, 2212, -272, 1156, -76]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![541, 2212, -272, 1156, -76]] ![![4, -3, 0, -1, -3]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![-18560, -335, -7160, -2245, -3295]]]
 hmul := by decide  
 g := ![![![![-3712, -67, -1432, -449, -659]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 5 2 2 [6, 4, 3, 0, 2, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 4, 2, 3], [6, 6, 3, 1, 2], [6, 1, 2, 1], [3, 3, 5, 3, 2], [0, 1]]
 g := ![![[4, 5, 1], []], ![[4, 6, 0, 1, 4, 5, 1, 6], [1, 2, 0, 5, 4, 4, 0, 6]], ![[0, 5, 4, 0, 4, 1, 5, 1], [0, 5, 4, 0, 6, 1, 3, 1]], ![[3, 1, 5, 4, 3, 1, 1], [1, 0, 0, 4, 1]], ![[1, 4, 4, 3, 4, 5, 6, 4], [4, 2, 1, 6, 1, 4, 6, 1]]]
 h' := ![![[4, 3, 4, 2, 3], [0, 0, 0, 1], [0, 1]], ![[6, 6, 3, 1, 2], [2, 2, 2, 4, 3], [4, 3, 4, 2, 3]], ![[6, 1, 2, 1], [6, 2, 4, 3, 2], [6, 6, 3, 1, 2]], ![[3, 3, 5, 3, 2], [0, 6, 0, 3, 6], [6, 1, 2, 1]], ![[0, 1], [3, 4, 1, 3, 3], [3, 3, 5, 3, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 3, 0, 4], [], [], []]
 b := ![[], [0, 0, 3, 6, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 5
  hpos := by decide
  P := [6, 4, 3, 0, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5454554, -8189916, -1660806, -4815160, -3560900]
  a := ![1, -6, 1, -7, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-779222, -1169988, -237258, -687880, -508700]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 16807 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def PBC7 : ContainsPrimesAboveP 7 ![I7N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![7, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 7 (by decide) 𝕀

instance hp11 : Fact (Nat.Prime 11) := {out := by norm_num}

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [8, 6, 2, 5, 6, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 5, 4, 6, 6], [3, 10, 0, 6, 6], [5, 6, 7, 7, 10], [1, 0, 0, 3], [0, 1]]
 g := ![![[6, 7, 2, 9, 3], [1], []], ![[5, 0, 9, 6, 5, 0, 0, 6], [3, 10, 9, 7, 10, 6, 2, 6], [9, 9, 10, 3]], ![[6, 5, 8, 7, 8, 0, 1, 7], [1, 7, 1, 7, 3, 0, 0, 6], [1, 5, 10, 3]], ![[6, 6, 3, 7, 5, 6, 6, 8], [4, 4, 7, 1, 2, 1, 9, 6], [10, 7, 2, 1]], ![[0, 4, 4, 6, 10, 2, 4], [2, 10, 3, 5, 5, 8, 4], [1, 9]]]
 h' := ![![[7, 5, 4, 6, 6], [3, 5, 9, 6, 5], [0, 0, 1], [0, 1]], ![[3, 10, 0, 6, 6], [5, 9, 8, 8, 1], [10, 10, 6, 10, 1], [7, 5, 4, 6, 6]], ![[5, 6, 7, 7, 10], [6, 10, 7, 6, 6], [1, 3, 10, 3, 10], [3, 10, 0, 6, 6]], ![[1, 0, 0, 3], [1, 10, 5, 0, 6], [0, 10, 6, 4, 7], [5, 6, 7, 7, 10]], ![[0, 1], [0, 10, 4, 2, 4], [4, 10, 10, 5, 4], [1, 0, 0, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 9, 3, 9], [], [], []]
 b := ![[], [2, 10, 8, 3, 4], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [8, 6, 2, 5, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8900040820, 13418103732, 3114687994, 7263671866, 5211108584]
  a := ![1, 25, -3, 24, 33]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![809094620, 1219827612, 283153454, 660333806, 473737144]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 161051 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def PBC11 : ContainsPrimesAboveP 11 ![I11N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![11, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 11 (by decide) 𝕀

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


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [12, 10, 6, 4, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 6, 5, 2, 11], [11, 2, 0, 2, 3], [12, 1, 6, 3, 2], [1, 3, 2, 6, 10], [0, 1]]
 g := ![![[11, 9, 8, 2, 1], [9, 1], []], ![[5, 1, 7, 11, 2, 5, 5, 6], [8, 12, 6, 9], [0, 10, 2, 12, 5, 0, 4, 5]], ![[10, 5, 0, 12, 1, 10, 12, 4], [4, 5, 5, 9], [10, 7, 12, 10, 8, 1, 11, 1]], ![[11, 5, 3, 0, 3, 6, 0, 8], [4, 10, 2, 9], [10, 8, 12, 2, 9, 0, 4, 8]], ![[9, 3, 2, 4, 2, 2, 12, 12], [11, 7, 5, 3], [1, 12, 4, 3, 10, 6, 10, 12]]]
 h' := ![![[11, 6, 5, 2, 11], [9, 2, 1, 10, 12], [0, 0, 0, 1], [0, 1]], ![[11, 2, 0, 2, 3], [7, 11, 5, 2, 7], [5, 4, 6, 7, 3], [11, 6, 5, 2, 11]], ![[12, 1, 6, 3, 2], [8, 1, 3, 6, 6], [2, 9, 1, 9, 3], [11, 2, 0, 2, 3]], ![[1, 3, 2, 6, 10], [7, 6, 6, 4, 11], [9, 2, 4, 2, 3], [12, 1, 6, 3, 2]], ![[0, 1], [2, 6, 11, 4, 3], [2, 11, 2, 7, 4], [1, 3, 2, 6, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 1, 10, 12], [], [], []]
 b := ![[], [8, 6, 10, 9, 6], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [12, 10, 6, 4, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![40084681, -2582710, -16237962, -26238537, 240292]
  a := ![-1, -7, 5, -5, -18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![3083437, -198670, -1249074, -2018349, 18484]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, -2, 1, 1, -7]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![16, -2, 1, 1, -7]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![1, 13, 1, 0, 0], ![2, 10, 0, 1, 0], ![3, 6, 0, 0, 1]] where
  M :=![![![16, -2, 1, 1, -7], ![-21, 11, -3, 3, 9], ![27, -12, 8, -3, -3], ![6, 9, -3, 5, -6], ![12, -15, 9, -6, 5]]]
  hmulB := by decide  
  f := ![![![-4, 2, 11, -7, -11]], ![![-33, -11, 9, 15, -3]], ![![-26, -9, 6, 13, -1]], ![![-16, -5, 5, 7, -2]], ![![-12, -3, 6, 3, -4]]]
  g := ![![![2, 1, 1, 1, -7], ![-3, -2, -3, 3, 9], ![2, -4, 8, -3, -3], ![1, 2, -3, 5, -6], ![0, -6, 9, -6, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [9, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 16], [0, 1]]
 g := ![![[1, 2], [2], [13], [1]], ![[0, 15], [2], [13], [1]]]
 h' := ![![[8, 16], [3, 6], [15, 11], [8, 8], [0, 1]], ![[0, 1], [0, 11], [1, 6], [4, 9], [8, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [10, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [9, 9, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-231, 1036, -254, -418, 292]
  a := ![0, -4, -2, -14, 12]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1, 398, -254, -418, 292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -18, -8, -10, -14]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![-11, -18, -8, -10, -14]] 
 ![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![11, 2, 1, 0, 0], ![6, 4, 0, 1, 0], ![6, 7, 0, 0, 1]] where
  M :=![![![-11, -18, -8, -10, -14], ![-42, -43, -8, -26, -6], ![-18, -82, -17, -42, -46], ![-48, -40, -16, -25, -16], ![12, -52, -4, -24, -29]]]
  hmulB := by decide  
  f := ![![![41, 2, -48, 18, 46]], ![![138, 57, -16, -78, -10]], ![![41, 10, -25, -4, 20]], ![![30, 8, -16, -5, 12]], ![![72, 23, -28, -22, 17]]]
  g := ![![![13, 8, -8, -10, -14], ![14, 7, -8, -26, -6], ![41, 26, -17, -42, -46], ![22, 12, -16, -25, -16], ![22, 15, -4, -24, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P1 : CertificateIrreducibleZModOfList' 17 2 2 4 [16, 4, 1] where
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
 g := ![![[13, 16], [16], [16], [1]], ![[0, 1], [16], [16], [1]]]
 h' := ![![[13, 16], [16, 4], [0, 13], [1, 13], [0, 1]], ![[0, 1], [0, 13], [16, 4], [0, 4], [13, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [10, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N1 : CertifiedPrimeIdeal' SI17N1 17 where
  n := 2
  hpos := by decide
  P := [16, 4, 1]
  hirr := P17P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![264, 66, -24, 241, -170]
  a := ![13, -7, 4, -6, -15]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![6, 20, -24, 241, -170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N1 B_one_repr
lemma NI17N1 : Nat.card (O ⧸ I17N1) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 0, -2, 2, 2]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![-1, 0, -2, 2, 2]] 
 ![![17, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![-1, 0, -2, 2, 2], ![6, 1, -2, -2, 2], ![6, 4, 3, -6, -6], ![-12, -2, 6, 1, -4], ![0, -2, -2, 4, 1]]]
  hmulB := by decide  
  f := ![![![67, 112, 26, 62, 46]], ![![16, 25, 6, 14, 10]], ![![65, 108, 25, 60, 44]], ![![21, 34, 8, 19, 14]], ![![11, 18, 4, 10, 7]]]
  g := ![![![1, 0, -2, 2, 2], ![2, 1, -2, -2, 2], ![-1, 4, 3, -6, -6], ![-5, -2, 6, 1, -4], ![1, -2, -2, 4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![16, -2, 1, 1, -7]] ![![-11, -18, -8, -10, -14]]
  ![![-242, 40, -117, -7, -71]] where
 M := ![![![-242, 40, -117, -7, -71]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![-242, 40, -117, -7, -71]] ![![-1, 0, -2, 2, 2]]
  ![![17, 0, 0, 0, 0]] where
 M := ![![![-136, -272, 153, -153, 255]]]
 hmul := by decide  
 g := ![![![![-8, -16, 9, -9, 15]]]]
 hle2 := by decide  


def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N1, I17N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N1
    exact isPrimeI17N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)
instance hp19 : Fact (Nat.Prime 19) := {out := by norm_num}

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [9, 1, 9, 15, 9, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 11, 6, 5, 17], [1, 16, 1, 4, 1], [2, 4, 1, 12, 17], [18, 6, 11, 17, 3], [0, 1]]
 g := ![![[16, 8, 15, 12, 4], [15, 7, 9, 10, 1], [], []], ![[16, 2, 14, 12, 11, 3, 17, 1], [13, 7, 14, 15, 4, 9, 11, 1], [7, 7, 4, 17], [7, 8, 1, 4]], ![[11, 7, 4, 15, 11, 14, 17, 17], [0, 5, 16, 4, 13, 3, 10, 1], [6, 14, 0, 16], [14, 12, 18, 1]], ![[10, 3, 10, 17, 9, 16, 11, 1], [7, 6, 18, 9, 11, 3, 0, 9], [17, 6, 16, 17], [16, 0, 11, 4]], ![[10, 10, 10, 15, 16, 6, 17, 18], [13, 1, 8, 9, 8, 14, 9, 14], [15, 13, 14, 7], [1, 12, 2, 9]]]
 h' := ![![[8, 11, 6, 5, 17], [17, 17, 5, 12, 2], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[1, 16, 1, 4, 1], [7, 7, 14, 0, 3], [14, 10, 1, 10, 3], [1, 2, 4, 17, 13], [8, 11, 6, 5, 17]], ![[2, 4, 1, 12, 17], [5, 2, 6, 18, 6], [10, 5, 7, 2, 18], [8, 5, 15, 18, 4], [1, 16, 1, 4, 1]], ![[18, 6, 11, 17, 3], [4, 7, 10, 1, 3], [10, 5, 7, 1, 9], [12, 0, 5, 16, 13], [2, 4, 1, 12, 17]], ![[0, 1], [10, 5, 3, 7, 5], [5, 18, 4, 6, 7], [11, 12, 13, 6, 8], [18, 6, 11, 17, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 6, 2, 10], [], [], []]
 b := ![[], [14, 5, 6, 11, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [9, 1, 9, 15, 9, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39178, 12065, -10735, -27550, 21565]
  a := ![-1, -1, -1, -2, 3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2062, 635, -565, -1450, 1135]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 2476099 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def PBC19 : ContainsPrimesAboveP 19 ![I19N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![19, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 19 (by decide) 𝕀

instance hp23 : Fact (Nat.Prime 23) := {out := by norm_num}

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0, 0, 0]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0, 0, 0]] 
 ![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]] where
  M :=![![![23, 0, 0, 0, 0], ![0, 23, 0, 0, 0], ![0, 0, 23, 0, 0], ![0, 0, 0, 23, 0], ![0, 0, 0, 0, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [9, 15, 0, 12, 7, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 16, 9, 9, 4], [2, 4, 14, 21, 8], [5, 22, 3, 20, 4], [8, 3, 20, 19, 7], [0, 1]]
 g := ![![[5, 3, 16, 21, 16], [12, 17, 22, 9, 3], [1], []], ![[19, 10, 9, 0, 7, 15, 2, 18], [14, 14, 20, 20, 10, 9, 5, 3], [3, 21, 15, 4, 3, 5, 4, 12], [3, 11, 6, 16]], ![[11, 17, 19, 22, 6, 1, 1, 16], [22, 5, 0, 22, 0, 1, 11, 9], [14, 4, 14, 7, 5, 12, 22, 2], [12, 14, 3, 18]], ![[11, 16, 10, 10, 10, 9, 11, 6], [16, 1, 22, 8, 20, 4, 13, 3], [11, 3, 18, 16, 9, 17, 17, 13], [11, 11, 2, 16]], ![[18, 12, 9, 13, 3, 5, 11, 19], [0, 6, 12, 8, 10, 15, 19, 15], [4, 12, 22, 4, 17, 4, 8, 21], [20, 17, 15, 3]]]
 h' := ![![[1, 16, 9, 9, 4], [7, 1, 1, 15, 19], [14, 8, 0, 11, 16], [0, 0, 1], [0, 1]], ![[2, 4, 14, 21, 8], [14, 19, 10, 11, 4], [5, 7, 11, 5, 15], [20, 3, 9, 13, 7], [1, 16, 9, 9, 4]], ![[5, 22, 3, 20, 4], [11, 3, 3, 19, 5], [1, 13, 9, 19, 21], [11, 9, 19, 6, 12], [2, 4, 14, 21, 8]], ![[8, 3, 20, 19, 7], [16, 7, 2, 0, 6], [3, 5, 10, 10, 8], [18, 2, 9, 3, 20], [5, 22, 3, 20, 4]], ![[0, 1], [16, 16, 7, 1, 12], [18, 13, 16, 1, 9], [22, 9, 8, 1, 7], [8, 3, 20, 19, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 18, 21, 17], [], [], []]
 b := ![[], [19, 20, 13, 22, 13], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [9, 15, 0, 12, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2685618, -645518, 2079775, -647841, 14098264]
  a := ![3, 3, 0, -1, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![116766, -28066, 90425, -28167, 612968]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 6436343 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def PBC23 : ContainsPrimesAboveP 23 ![I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![23, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 23 (by decide) 𝕀



lemma PB63I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 23 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 23 (by omega)

def PB63I0 : PrimesBelowBoundCertificateInterval O 1 23 63 where
  m := 9
  g := ![5, 3, 5, 1, 1, 1, 3, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB63I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1, I2N1, I2N2, I2N2]
    · exact ![I3N0, I3N1, I3N2]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0]
    · exact ![I23N0]
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
    · exact ![9, 3, 9]
    · exact ![5, 5, 5, 5, 5]
    · exact ![16807]
    · exact ![161051]
    · exact ![371293]
    · exact ![289, 289, 17]
    · exact ![2476099]
    · exact ![6436343]
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
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N1
      exact NI17N2
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I2N0, I2N1, I2N2, I3N0, I3N1, I3N2, I5N0, I17N2]
  Il := ![[I2N0, I2N1, I2N1, I2N2, I2N2], [I3N0, I3N1, I3N2], [I5N0, I5N0, I5N0, I5N0, I5N0], [], [], [], [I17N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
