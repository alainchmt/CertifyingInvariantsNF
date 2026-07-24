
import IdealArithmetic.Examples.NF3_1_466627_2.RI3_1_466627_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-9, -1, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-9, -1, 1]] 
 ![![2, 0, 0], ![0, 2, 0], ![1, 1, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-9, -1, 1], ![133, 5, -1], ![-133, 119, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![5, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -1, 2]], ![![-5, -1, 1], ![67, 3, -1], ![-69, 57, 5]]]
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
  c := ![-1595, 1031, 127]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-861, 452, 127]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![0, 1, 1], ![133, 14, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![1, -1, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-1, 1, 1], ![59, 14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-9, -1, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![-18, -2, 2], ![124, 4, 0]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![-9, -1, 1]], ![![62, 2, 0]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-10, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-10, -1, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![2, 2, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-10, -1, 1], ![133, 4, -1], ![-133, 119, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -2, 3]], ![![-4, -1, 1], ![45, 2, -1], ![-47, 37, 4]]]
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
  c := ![-796, 1115, 121]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-346, 291, 121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![0, 1, 1], ![133, 14, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![2, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-1, 1, 1], ![39, 14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-10, -1, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![-30, -3, 3], ![123, 3, 0]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![-10, -1, 1]], ![![41, 1, 0]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-8, -1, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-8, -1, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![2, 4, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-8, -1, 1], ![133, 6, -1], ![-133, 119, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -4, 5]], ![![-2, -1, 1], ![27, 2, -1], ![-29, 19, 6]]]
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
  c := ![269, 158, 12]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49, 22, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![0, 1, 1], ![133, 14, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![4, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-4, 0, 5]], ![![0, 1, 0], ![-1, 1, 1], ![23, 14, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![-8, -1, 1]] ![![5, 0, 0], ![1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![-40, -5, 5], ![125, 5, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![1, 1, 0]]], ![![![-8, -1, 1]], ![![25, 1, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![133, 14, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![19, 14, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0], ![-7, 0, 1]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![0, 0, 1]]]
 hmul := by decide  
 g := ![![![![7, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-7, 0, 1]] ![![7, 0, 0], ![0, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![-49, 0, 7], ![133, 7, 0]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![0, 1, 0]]], ![![![-7, 0, 1]], ![![19, 1, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [8, 6, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 9, 5], [5, 1, 6], [0, 1]]
 g := ![![[5, 1, 9], [9, 9, 1], []], ![[5, 1, 4, 4], [10, 8, 4, 5], [7, 3]], ![[6, 0, 7, 2], [0, 6, 1, 2], [6, 3]]]
 h' := ![![[4, 9, 5], [5, 6, 8], [0, 0, 1], [0, 1]], ![[5, 1, 6], [6, 3, 5], [4, 6, 1], [4, 9, 5]], ![[0, 1], [5, 2, 9], [10, 5, 9], [5, 1, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 4], []]
 b := ![[], [9, 6, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [8, 6, 2, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1061357, 258533, 24827]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![96487, 23503, 2257]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-15, 5, 1]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-15, 5, 1]] 
 ![![13, 0, 0], ![0, 13, 0], ![11, 5, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-15, 5, 1], ![133, -1, 5], ![665, 203, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -5, 13]], ![![-2, 0, 1], ![6, -2, 5], ![52, 16, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [1, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 12], [0, 1]]
 g := ![![[7, 1], [3], [6, 1]], ![[0, 12], [3], [12, 12]]]
 h' := ![![[6, 12], [7, 1], [7, 9], [0, 1]], ![[0, 1], [0, 12], [9, 4], [6, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [1, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [1, 7, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-803, 64, 18]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -2, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-5, 1, 0]] 
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-5, 1, 0], ![0, -5, 1], ![133, 14, -5]]]
  hmulB := by decide  
  f := ![![![51, -10, 0], ![130, 0, 0]], ![![36, -7, 0], ![92, 0, 0]], ![![7, -1, 0], ![18, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 13, 0], ![-1, 0, 13]], ![![-1, 1, 0], ![3, -5, 1], ![2, 14, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![-15, 5, 1]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-65, 13, 0]], ![![-195, 65, 13], ![208, -26, 0]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-5, 1, 0]]], ![![![-15, 5, 1]], ![![16, -2, 0]]]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-10, 2, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-10, 2, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![7, 2, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-10, 2, 1], ![133, 4, 2], ![266, 161, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -2, 17]], ![![-1, 0, 1], ![7, 0, 2], ![14, 9, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [5, 5, 1] where
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
 g := ![![[1, 1], [15], [8], [1]], ![[13, 16], [15], [8], [1]]]
 h' := ![![[12, 16], [14, 16], [2, 10], [12, 12], [0, 1]], ![[0, 1], [2, 1], [3, 7], [3, 5], [12, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [16, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [5, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![537, 593, 67]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 27, 67]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-2, 1, 0]] 
 ![![17, 0, 0], ![15, 1, 0], ![13, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-2, 1, 0], ![0, -2, 1], ![133, 14, -2]]]
  hmulB := by decide  
  f := ![![![23, -11, 0], ![187, 0, 0]], ![![21, -10, 0], ![171, 0, 0]], ![![19, -9, 0], ![155, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 17, 0], ![-13, 0, 17]], ![![-1, 1, 0], ![1, -2, 1], ![-3, 14, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-10, 2, 1]] ![![17, 0, 0], ![-2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-34, 17, 0]], ![![-170, 34, 17], ![153, 0, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-2, 1, 0]]], ![![![-10, 2, 1]], ![![9, 0, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![0, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![0, 1, 0]] 
 ![![19, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![0, 0, 1], ![133, 14, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![0, 1, 0], ![0, 0, 1], ![7, 14, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-14, 0, 1]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-14, 0, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![5, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-14, 0, 1], ![133, 0, 0], ![0, 133, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, 0, 19]], ![![-1, 0, 1], ![7, 0, 0], ![0, 7, 0]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P1 : CertificateIrreducibleZModOfList' 19 2 2 4 [13, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 18], [0, 1]]
 g := ![![[10, 6], [10, 17], [9], [1]], ![[9, 13], [4, 2], [9], [1]]]
 h' := ![![[3, 18], [3, 5], [14, 6], [6, 3], [0, 1]], ![[0, 1], [18, 14], [13, 13], [15, 16], [3, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [7, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N1 : CertifiedPrimeIdeal' SI19N1 19 where
  n := 2
  hpos := by decide
  P := [13, 16, 1]
  hirr := P19P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5271, -228, 196]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-329, -12, 196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N1 B_one_repr
lemma NI19N1 : Nat.card (O ⧸ I19N1) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![0, 1, 0]] ![![19, 0, 0], ![-14, 0, 1]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-266, 0, 19]], ![![0, 19, 0], ![133, 0, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-14, 0, 1]]], ![![![0, 1, 0]], ![![7, 0, 0]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-2, -9, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-2, -9, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![21, 14, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-2, -9, 1], ![133, 12, -9], ![-1197, 7, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -14, 23]], ![![-1, -1, 1], ![14, 6, -9], ![-63, -7, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [4, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 22], [0, 1]]
 g := ![![[9, 6], [7, 3], [0, 8], [1]], ![[0, 17], [14, 20], [11, 15], [1]]]
 h' := ![![[10, 22], [18, 12], [0, 7], [19, 10], [0, 1]], ![[0, 1], [0, 11], [1, 16], [4, 13], [10, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [16, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [4, 13, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76, 66, 54]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46, -30, 54]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![9, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![9, 1, 0]] 
 ![![23, 0, 0], ![9, 1, 0], ![11, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![9, 1, 0], ![0, 9, 1], ![133, 14, 9]]]
  hmulB := by decide  
  f := ![![![73, 8, 0], ![-184, 0, 0]], ![![27, 3, 0], ![-68, 0, 0]], ![![31, 3, 0], ![-78, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 23, 0], ![-11, 0, 23]], ![![0, 1, 0], ![-4, 9, 1], ![-4, 14, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![-2, -9, 1]] ![![23, 0, 0], ![9, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![207, 23, 0]], ![![-46, -207, 23], ![115, -69, 0]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![9, 1, 0]]], ![![![-2, -9, 1]], ![![5, -3, 0]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-9, 11, 1]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-9, 11, 1]] 
 ![![29, 0, 0], ![0, 29, 0], ![20, 11, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-9, 11, 1], ![133, 5, 11], ![1463, 287, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -11, 29]], ![![-1, 0, 1], ![-3, -4, 11], ![47, 8, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 2 2 4 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 28], [0, 1]]
 g := ![![[5, 25], [25], [], [23, 1]], ![[0, 4], [25], [], [17, 28]]]
 h' := ![![[23, 28], [28, 24], [0, 24], [13], [0, 1]], ![[0, 1], [0, 5], [1, 5], [13], [23, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [21, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 2
  hpos := by decide
  P := [7, 6, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1078, 213, 22]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, -1, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI29N0 B_one_repr
lemma NI29N0 : Nat.card (O ⧸ I29N0) = 841 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-11, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-11, 1, 0]] 
 ![![29, 0, 0], ![18, 1, 0], ![24, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-11, 1, 0], ![0, -11, 1], ![133, 14, -11]]]
  hmulB := by decide  
  f := ![![![133, -12, 0], ![348, 0, 0]], ![![100, -9, 0], ![262, 0, 0]], ![![126, -11, 0], ![330, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 29, 0], ![-24, 0, 29]], ![![-1, 1, 0], ![6, -11, 1], ![5, 14, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![-9, 11, 1]] ![![29, 0, 0], ![-11, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-319, 29, 0]], ![![-261, 319, 29], ![232, -116, 0]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-11, 1, 0]]], ![![![-9, 11, 1]], ![![8, -4, 0]]]]
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


def P31P0 : CertificateIrreducibleZModOfList' 31 3 2 4 [19, 1, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 12, 27], [30, 18, 4], [0, 1]]
 g := ![![[28, 29, 10], [11, 15, 8], [22, 13, 5], [1]], ![[11, 21, 20, 17], [21, 2, 7, 24], [27, 30, 29, 12], [25, 24, 30, 29]], ![[22, 28, 22, 8], [16, 26, 14, 28], [15, 20, 8, 9], [2, 28, 15, 2]]]
 h' := ![![[26, 12, 27], [8, 22, 14], [16, 30, 15], [12, 30, 25], [0, 1]], ![[30, 18, 4], [15, 23, 9], [29, 11, 26], [20, 16, 20], [26, 12, 27]], ![[0, 1], [4, 17, 8], [23, 21, 21], [23, 16, 17], [30, 18, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 21], []]
 b := ![[], [30, 26, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 3
  hpos := by decide
  P := [19, 1, 6, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11129, -3844, 124]
  a := ![-3, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-359, -124, 4]
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
  g := ![2, 2, 2, 3, 1, 2, 2, 2, 2, 2, 1]
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
    · exact ![I11N0]
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
    · exact ![1331]
    · exact ![169, 13]
    · exact ![289, 17]
    · exact ![19, 361]
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
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I13N0, I13N1, I17N1, I19N0, I23N1, I29N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N0, I7N0], [], [I13N0, I13N1], [I17N1], [I19N0], [I23N1], [I29N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
