
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![2, -1, 4], ![152, -26, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, -1, 2], ![76, -26, 1]]]
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
  c := ![-1404, 2287, -1224]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-702, 2287, -612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![2, 0, 4], ![152, -26, 3]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![65, -24, 2], ![22, 0, -1]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, 0, 4], ![89, -26, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![0, 2, 0], ![2, 0, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 1, 0]], ![![1, 0, 2]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![18, -1, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![18, -1, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 2, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![18, -1, 1], ![150, -7, -2], ![-51, 51, -9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-6, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -2, 3]], ![![6, -1, 1], ![50, -1, -2], ![-17, 23, -9]]]
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
  c := ![424056, 112202, -100646]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![141352, 104498, -100646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![2, -2, 4], ![152, -26, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![2, -2, 3], ![2, -2, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![2, -2, 4], ![68, -26, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![18, -1, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![54, -3, 3], ![132, -6, -3]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![18, -1, 1]], ![![44, -2, -1]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![16, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![16, 0, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![1, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![16, 0, 1], ![152, -10, 2], ![101, 25, -9]]]
  hmulB := by decide  
  f := ![![![-15, 0, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-3, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, 0, 5]], ![![3, 0, 1], ![30, -2, 2], ![22, 5, -9]]]
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
  c := ![-2, 3405, -2052]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![410, 681, -2052]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![2, -3, 4], ![152, -26, 0]]]
  hmulB := by decide  
  f := ![![![7, -11, 16], ![-5, -20, 0]], ![![5, -6, 8], ![1, -10, 0]], ![![6, -9, 13], ![-3, -16, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-4, 0, 5]], ![![-1, 1, 0], ![-1, -3, 4], ![46, -26, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![16, 0, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![80, 0, 5], ![120, -10, 0]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-2, 1, 0]]], ![![![16, 0, 1]], ![![24, -2, 0]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![15, -2, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![15, -2, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![1, 5, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![15, -2, 1], ![148, -9, -6], ![-203, 77, -14]]]
  hmulB := by decide  
  f := ![![![-14, 2, -1], ![7, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -5, 7]], ![![2, -1, 1], ![22, 3, -6], ![-27, 21, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [6, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 6], [0, 1]]
 g := ![![[6, 4], [6, 1]], ![[2, 3], [5, 6]]]
 h' := ![![[6, 6], [6, 2], [0, 1]], ![[0, 1], [4, 5], [6, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [4, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [6, 1, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1826, 1206, -890]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![388, 808, -890]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![2, -2, 4], ![152, -26, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![4, 2, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![2, -2, 4], ![44, -26, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![15, -2, 1]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![105, -14, 7], ![133, -7, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![15, -2, 1]], ![![19, -1, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 3, -1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![-8, 3, -1]] 
 ![![11, 0, 0], ![5, 1, 0], ![1, 0, 1]] where
  M :=![![![-8, 3, -1], ![-146, 15, 10], ![355, -103, 23]]]
  hmulB := by decide  
  f := ![![![1375, 34, 45]], ![![1253, 31, 41]], ![![1008, 25, 33]]]
  g := ![![![-2, 3, -1], ![-21, 15, 10], ![77, -103, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N0 : Nat.card (O ⧸ I11N0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N0)

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := prime_ideal_of_norm_prime hp11.out _ NI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![2, -4, 4], ![152, -26, -1]]]
  hmulB := by decide  
  f := ![![![40, -83, 84], ![-11, -231, 0]], ![![28, -59, 60], ![-10, -165, 0]], ![![12, -23, 23], ![1, -63, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-3, 0, 11]], ![![-1, 1, 0], ![2, -4, 4], ![33, -26, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![-8, 3, -1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0], ![16, 3, 1]] where
 M := ![![![-88, 33, -11], ![-122, 6, 13]]]
 hmul := by decide  
 g := ![![![![-8, 3, -1], ![0, 0, 0]], ![![-14, 0, 1], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI11N1 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![16, 3, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![176, 33, 11], ![110, -22, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-3, 1, 0]]], ![![![16, 3, 1]], ![![10, -2, 1]]]]
 hle2 := by decide  


def PBC11 : ContainsPrimesAboveP 11 ![I11N0, I11N1, I11N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI11N0
    exact isPrimeI11N1
    exact isPrimeI11N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 11 (by decide) (𝕀 ⊙ MulI11N0 ⊙ MulI11N1)
instance hp13 : Fact (Nat.Prime 13) := {out := by norm_num}

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![6, 1, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![6, 1, 0]] 
 ![![13, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![6, 1, 0], ![2, 5, 4], ![152, -26, 8]]]
  hmulB := by decide  
  f := ![![![49, 162, 132], ![39, -429, 0]], ![![18, 73, 60], ![27, -195, 0]], ![![18, 74, 61], ![28, -198, 0]]]
  g := ![![![1, 0, 0], ![-6, 13, 0], ![-6, 0, 13]], ![![0, 1, 0], ![-4, 5, 4], ![20, -26, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N0 : Nat.card (O ⧸ I13N0) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N0)

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := prime_ideal_of_norm_prime hp13.out _ NI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-4, 1, 0]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-4, 1, 0]] 
 ![![13, 0, 0], ![9, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-4, 1, 0], ![2, -5, 4], ![152, -26, -2]]]
  hmulB := by decide  
  f := ![![![-27, 88, -72], ![26, 234, 0]], ![![-19, 59, -48], ![14, 156, 0]], ![![-2, 13, -11], ![11, 36, 0]]]
  g := ![![![1, 0, 0], ![-9, 13, 0], ![-2, 0, 13]], ![![-1, 1, 0], ![3, -5, 4], ![30, -26, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1

def I13N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-3, 1, 0]] i)))

def SI13N2: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-3, 1, 0]] 
 ![![13, 0, 0], ![10, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-3, 1, 0], ![2, -4, 4], ![152, -26, -1]]]
  hmulB := by decide  
  f := ![![![-86, 189, -192], ![39, 624, 0]], ![![-65, 142, -144], ![27, 468, 0]], ![![-26, 58, -59], ![14, 192, 0]]]
  g := ![![![1, 0, 0], ![-10, 13, 0], ![-4, 0, 13]], ![![-1, 1, 0], ![2, -4, 4], ![32, -26, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N2 : Nat.card (O ⧸ I13N2) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N2)

lemma isPrimeI13N2 : Ideal.IsPrime I13N2 := prime_ideal_of_norm_prime hp13.out _ NI13N2
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![6, 1, 0]] ![![13, 0, 0], ![-4, 1, 0]]
  ![![13, 0, 0], ![14, -3, 1]] where
 M := ![![![169, 0, 0], ![-52, 13, 0]], ![![78, 13, 0], ![-22, 1, 4]]]
 hmul := by decide  
 g := ![![![![-1, 3, -1], ![13, 0, 0]], ![![-4, 1, 0], ![0, 0, 0]]], ![![![-8, 4, -1], ![13, 0, 0]], ![![-6, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI13N1 : IdealMulLeCertificate' Table 
  ![![13, 0, 0], ![14, -3, 1]] ![![13, 0, 0], ![-3, 1, 0]]
  ![![13, 0, 0]] where
 M := ![![![169, 0, 0], ![-39, 13, 0]], ![![182, -39, 13], ![104, 0, -13]]]
 hmul := by decide  
 g := ![![![![13, 0, 0]], ![![-3, 1, 0]]], ![![![14, -3, 1]], ![![8, 0, -1]]]]
 hle2 := by decide  


def PBC13 : ContainsPrimesAboveP 13 ![I13N0, I13N1, I13N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
    exact isPrimeI13N1
    exact isPrimeI13N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 13 (by decide) (𝕀 ⊙ MulI13N0 ⊙ MulI13N1)
instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![10, -1, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![10, -1, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![10, 16, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![10, -1, 1], ![150, -15, -2], ![-51, 51, -17]]]
  hmulB := by decide  
  f := ![![![-9, 1, -1], ![17, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -16, 17]], ![![0, -1, 1], ![10, 1, -2], ![7, 19, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [1, 10, 1] where
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
 g := ![![[10, 1], [2], [15], [1]], ![[0, 16], [2], [15], [1]]]
 h' := ![![[7, 16], [7, 16], [3, 6], [16, 7], [0, 1]], ![[0, 1], [0, 1], [11, 11], [14, 10], [7, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [13, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [1, 10, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![174384, 48406, -44071]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36182, 44326, -44071]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![2, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![2, 1, 0]] 
 ![![17, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![2, 1, 0], ![2, 1, 4], ![152, -26, 4]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![17, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -3], ![4, 13, 0]]]
  g := ![![![1, 0, 0], ![-2, 17, 0], ![0, 0, 17]], ![![0, 1, 0], ![0, 1, 4], ![12, -26, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![10, -1, 1]] ![![17, 0, 0], ![2, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![34, 17, 0]], ![![170, -17, 17], ![170, -17, 0]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![2, 1, 0]]], ![![![10, -1, 1]], ![![10, -1, 0]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![14, 3, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![14, 3, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![14, 3, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![14, 3, 1], ![158, -15, 14], ![557, -53, -5]]]
  hmulB := by decide  
  f := ![![![-13, -3, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -3, 19]], ![![0, 0, 1], ![-2, -3, 14], ![33, -2, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [10, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 18], [0, 1]]
 g := ![![[4, 4], [6, 17], [4], [1]], ![[15, 15], [10, 2], [4], [1]]]
 h' := ![![[17, 18], [16, 17], [3, 13], [9, 17], [0, 1]], ![[0, 1], [1, 2], [15, 6], [13, 2], [17, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [18, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [10, 2, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![417, -26, -15]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![33, 1, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![5, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![5, 1, 0]] 
 ![![19, 0, 0], ![5, 1, 0], ![5, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![5, 1, 0], ![2, 4, 4], ![152, -26, 7]]]
  hmulB := by decide  
  f := ![![![-39, -80, -80], ![0, 380, 0]], ![![-10, -20, -20], ![1, 95, 0]], ![![-10, -21, -21], ![-1, 100, 0]]]
  g := ![![![1, 0, 0], ![-5, 19, 0], ![-5, 0, 19]], ![![0, 1, 0], ![-2, 4, 4], ![13, -26, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![14, 3, 1]] ![![19, 0, 0], ![5, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![95, 19, 0]], ![![266, 57, 19], ![228, 0, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![5, 1, 0]]], ![![![14, 3, 1]], ![![12, 0, 1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-12038736766, -297888727, -394007603]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![-12038736766, -297888727, -394007603]] 
 ![![23, 0, 0], ![15, 1, 0], ![17, 0, 1]] where
  M :=![![![-12038736766, -297888727, -394007603], ![-60484933110, -1496650361, -1979570114], ![-85073854407, -2105083173, -2784324145]]]
  hmulB := by decide  
  f := ![![![-174623, 49096, -10195]], ![![-176991, 33817, 1003]], ![![150622, -30293, 223]]]
  g := ![![![-37925070, -297888727, -394007603], ![-190542859, -1496650361, -1979570114], ![-268004189, -2105083173, -2784324145]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N0 : Nat.card (O ⧸ I23N0) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N0)

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := prime_ideal_of_norm_prime hp23.out _ NI23N0
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![-12038736766, -297888727, -394007603]] ![![-12038736766, -297888727, -394007603]]
  ![![196468708100731246147, 4861458015823581648, 6430090319932811211]] where
 M := ![![![196468708100731246147, 4861458015823581648, 6430090319932811211]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI23N1 : IdealMulLeCertificate' Table 
  ![![196468708100731246147, 4861458015823581648, 6430090319932811211]] ![![-12038736766, -297888727, -394007603]]
  ![![23, 0, 0]] where
 M := ![![![-3206312590186781973001619662759, -79337591179190873240507512300, -104937217474185603200916113108]]]
 hmul := by decide  
 g := ![![![![-139404895225512259695722594033, -3449460486051777097413370100, -4562487716268939269605048396]]]]
 hle2 := by decide  

def PBC23 : ContainsPrimesAboveP 23 ![I23N0, I23N0, I23N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI23N0
    exact isPrimeI23N0
    exact isPrimeI23N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 23 (by decide) (𝕀 ⊙ MulI23N0 ⊙ MulI23N1)
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


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [12, 26, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 19, 18], [17, 9, 11], [0, 1]]
 g := ![![[9, 1, 4], [22, 16], [12, 28, 16], [1]], ![[1, 14, 18, 12], [3, 28], [28, 19, 11, 3], [17, 0, 12, 3]], ![[22, 11, 19, 14], [5, 24], [18, 4, 7, 10], [8, 11, 2, 26]]]
 h' := ![![[8, 19, 18], [27, 26, 2], [1, 18, 4], [17, 3, 25], [0, 1]], ![[17, 9, 11], [0, 7, 22], [23, 6, 12], [18, 16, 18], [8, 19, 18]], ![[0, 1], [23, 25, 5], [24, 5, 13], [3, 10, 15], [17, 9, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], []]
 b := ![[], [24, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [12, 26, 4, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3627291, -1627770, 686662]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![125079, -56130, 23678]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![8, -12, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![8, -12, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![8, 19, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![8, -12, 1], ![128, -6, -46], ![-1723, 337, -41]]]
  hmulB := by decide  
  f := ![![![-7, 12, -1], ![31, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -19, 31]], ![![0, -1, 1], ![16, 28, -46], ![-45, 36, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [16, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 30], [0, 1]]
 g := ![![[13, 2], [20, 4], [23, 9], [9, 1]], ![[0, 29], [25, 27], [11, 22], [18, 30]]]
 h' := ![![[9, 30], [21, 8], [4, 29], [11, 3], [0, 1]], ![[0, 1], [0, 23], [17, 2], [7, 28], [9, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [6, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [16, 22, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2456, 625, -685]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![256, 440, -685]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![15, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![15, 1, 0]] 
 ![![31, 0, 0], ![15, 1, 0], ![10, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![15, 1, 0], ![2, 14, 4], ![152, -26, 17]]]
  hmulB := by decide  
  f := ![![![788, 7693, 2204], ![651, -17081, 0]], ![![382, 3714, 1064], ![311, -8246, 0]], ![![245, 2481, 711], ![229, -5510, 0]]]
  g := ![![![1, 0, 0], ![-15, 31, 0], ![-10, 0, 31]], ![![0, 1, 0], ![-8, 14, 4], ![12, -26, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![8, -12, 1]] ![![31, 0, 0], ![15, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![465, 31, 0]], ![![248, -372, 31], ![248, -186, -31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![15, 1, 0]]], ![![![8, -12, 1]], ![![8, -6, -1]]]]
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


lemma PB253I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB253I0 : PrimesBelowBoundCertificateInterval O 1 31 253 where
  m := 11
  g := ![2, 2, 2, 2, 3, 3, 2, 2, 3, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB253I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0, I11N1, I11N1]
    · exact ![I13N0, I13N1, I13N2]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N0, I23N0]
    · exact ![I29N0]
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
    · exact ![4, 2]
    · exact ![9, 3]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![11, 11, 11]
    · exact ![13, 13, 13]
    · exact ![289, 17]
    · exact ![361, 19]
    · exact ![23, 23, 23]
    · exact ![24389]
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
      exact NI11N1
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
      exact NI13N1
      exact NI13N2
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
      exact NI23N0
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I5N1, I7N0, I7N1, I11N0, I11N1, I13N0, I13N1, I13N2, I17N1, I19N1, I23N0, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N1], [I5N0, I5N1], [I7N0, I7N1], [I11N0, I11N1, I11N1], [I13N0, I13N1, I13N2], [I17N1], [I19N1], [I23N0, I23N0, I23N0], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
