
import IdealArithmetic.Examples.NF3_1_524291_1.RI3_1_524291_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![2, -1, 4], ![140, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![0, 0, 1]], ![![0, 1, 0], ![1, -1, 2], ![70, 0, 1]]]
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
  c := ![-704, 1685, 50]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-352, 1685, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![2, 0, 4], ![140, 0, 3]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![58, -12, 2], ![24, 0, -1]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![1, 0, 4], ![70, 0, 3]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 3 2 1 [1, 1, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 2, 1], [2, 0, 2], [0, 1]]
 g := ![![[1]], ![[0, 0, 1, 1]], ![[2, 0, 2, 2]]]
 h' := ![![[2, 2, 1], [0, 1]], ![[2, 0, 2], [2, 2, 1]], ![[0, 1], [2, 0, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 2], []]
 b := ![[], [0, 0, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 3
  hpos := by decide
  P := [1, 1, 2, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1521202407, -38587488, -50354412]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-507067469, -12862496, -16784804]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![2, 1, 0]] 
 ![![5, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![2, 1, 0], ![2, 1, 4], ![140, 0, 4]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -3], ![1, 4, 0]]]
  g := ![![![1, 0, 0], ![-2, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 1, 4], ![28, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-2, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-2, 1, 0], ![2, -3, 4], ![140, 0, 0]]]
  hmulB := by decide  
  f := ![![![7, -11, 16], ![-5, -20, 0]], ![![5, -6, 8], ![1, -10, 0]], ![![6, -9, 13], ![-3, -16, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-4, 0, 5]], ![![-1, 1, 0], ![-1, -3, 4], ![28, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1

def I5N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![2, -2, 4], ![140, 0, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![-1, 1, -3], ![3, 4, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![2, -2, 4], ![28, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N2 : Nat.card (O ⧸ I5N2) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N2)

lemma isPrimeI5N2 : Ideal.IsPrime I5N2 := prime_ideal_of_norm_prime hp5.out _ NI5N2
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0], ![2, 1, 1]] where
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![10, 5, 0], ![-2, -1, 4]]]
 hmul := by decide  
 g := ![![![![3, -1, -1], ![5, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![0, 0, -1], ![5, 0, 0]], ![![-2, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI5N1 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![2, 1, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![10, 5, 5], ![140, 0, 5]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![2, 1, 1]], ![![28, 0, 1]]]]
 hle2 := by decide  


def PBC5 : ContainsPrimesAboveP 5 ![I5N0, I5N1, I5N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
    exact isPrimeI5N1
    exact isPrimeI5N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 5 (by decide) (𝕀 ⊙ MulI5N0 ⊙ MulI5N1)
instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![2, 1, 4], ![140, 0, 4]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, -1, -1], ![5, 2, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 1, 4], ![20, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![2, -3, 4], ![140, 0, 0]]]
  hmulB := by decide  
  f := ![![![17, -26, 36], ![-7, -63, 0]], ![![13, -18, 24], ![1, -42, 0]], ![![16, -23, 31], ![-1, -54, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-6, 0, 7]], ![![-1, 1, 0], ![-1, -3, 4], ![20, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![2, -2, 4], ![140, 0, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![4, 2, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![2, -2, 4], ![20, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![7, 0, 0], ![3, -2, 1]] where
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![14, 7, 0], ![-2, -1, 4]]]
 hmul := by decide  
 g := ![![![![4, 2, -1], ![7, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-1, 3, -1], ![7, 0, 0]], ![![-2, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![3, -2, 1]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![21, -14, 7], ![133, 7, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![-1, 1, 0]]], ![![![3, -2, 1]], ![![19, 1, -1]]]]
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

def I11N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 3, 1]] i)))

def SI11N0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![1, 3, 1]] 
 ![![11, 0, 0], ![0, 11, 0], ![1, 3, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, 3, 1], ![146, -2, 14], ![525, 35, 8]]]
  hmulB := by decide  
  f := ![![![0, -3, -1], ![11, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -3, 11]], ![![0, 0, 1], ![12, -4, 14], ![47, 1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P11P0 : CertificateIrreducibleZModOfList' 11 2 2 3 [7, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 10], [0, 1]]
 g := ![![[4, 3], [0, 3], [1]], ![[8, 8], [4, 8], [1]]]
 h' := ![![[5, 10], [0, 6], [4, 5], [0, 1]], ![[0, 1], [8, 5], [7, 6], [5, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [2, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 2
  hpos := by decide
  P := [7, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![962, 2820, 27]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85, 249, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI11N0 : Ideal.IsPrime I11N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI11N0 B_one_repr
lemma NI11N0 : Nat.card (O ⧸ I11N0) = 121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI11N0

def I11N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def SI11N1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![3, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![2, -4, 4], ![140, 0, -1]]]
  hmulB := by decide  
  f := ![![![40, -83, 84], ![-11, -231, 0]], ![![28, -59, 60], ![-10, -165, 0]], ![![12, -23, 23], ![1, -63, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-3, 0, 11]], ![![-1, 1, 0], ![2, -4, 4], ![13, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI11N1 : Nat.card (O ⧸ I11N1) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI11N1)

lemma isPrimeI11N1 : Ideal.IsPrime I11N1 := prime_ideal_of_norm_prime hp11.out _ NI11N1
def MulI11N0 : IdealMulLeCertificate' Table 
  ![![11, 0, 0], ![1, 3, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![11, 0, 0]] where
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![11, 33, 11], ![143, -11, 11]]]
 hmul := by decide  
 g := ![![![![11, 0, 0]], ![![-3, 1, 0]]], ![![![1, 3, 1]], ![![13, -1, 1]]]]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [5, 10, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 3, 6], [8, 9, 7], [0, 1]]
 g := ![![[7, 6, 9], [6, 1], [1]], ![[7, 2, 9, 2], [3, 3], [12, 3, 4, 8]], ![[12, 8, 2, 5], [11, 12], [11, 1, 5, 5]]]
 h' := ![![[4, 3, 6], [8, 9, 3], [8, 3, 12], [0, 1]], ![[8, 9, 7], [1, 1, 3], [4, 9, 9], [4, 3, 6]], ![[0, 1], [1, 3, 7], [2, 1, 5], [8, 9, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 10], []]
 b := ![[], [11, 10, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [5, 10, 1, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1079741, -12558, -23062]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83057, -966, -1774]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 2197 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def PBC13 : ContainsPrimesAboveP 13 ![I13N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI13N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![13, 0, 0]]) timesTableT_eq_Table B_one_repr 13 (by decide) 𝕀

instance hp17 : Fact (Nat.Prime 17) := {out := by norm_num}

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-4, 5, 1]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-4, 5, 1]] 
 ![![17, 0, 0], ![0, 17, 0], ![13, 5, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-4, 5, 1], ![150, -9, 22], ![805, 35, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -5, 17]], ![![-1, 0, 1], ![-8, -7, 22], ![42, 0, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P17P0 : CertificateIrreducibleZModOfList' 17 2 2 4 [3, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 16], [0, 1]]
 g := ![![[2, 9], [15], [2], [1]], ![[16, 8], [15], [2], [1]]]
 h' := ![![[11, 16], [15, 3], [3, 7], [14, 11], [0, 1]], ![[0, 1], [14, 14], [12, 10], [16, 6], [11, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [4, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 2
  hpos := by decide
  P := [3, 6, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![182726, 64664, 3831]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7819, 2677, 3831]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI17N0 B_one_repr
lemma NI17N0 : Nat.card (O ⧸ I17N0) = 289 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-5, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-5, 1, 0]] 
 ![![17, 0, 0], ![12, 1, 0], ![10, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-5, 1, 0], ![2, -6, 4], ![140, 0, -3]]]
  hmulB := by decide  
  f := ![![![266, -893, 600], ![-119, -2550, 0]], ![![186, -625, 420], ![-84, -1785, 0]], ![![155, -525, 353], ![-75, -1500, 0]]]
  g := ![![![1, 0, 0], ![-12, 17, 0], ![-10, 0, 17]], ![![-1, 1, 0], ![2, -6, 4], ![10, 0, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![-4, 5, 1]] ![![17, 0, 0], ![-5, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-85, 17, 0]], ![![-68, 85, 17], ![170, -34, 17]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-5, 1, 0]]], ![![![-4, 5, 1]], ![![10, -2, 1]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![3, 2, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 2, 1], ![144, 1, 10], ![385, 35, 8]]]
  hmulB := by decide  
  f := ![![![-2, -2, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -2, 19]], ![![0, 0, 1], ![6, -1, 10], ![19, 1, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [11, 16, 1] where
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
 g := ![![[17, 7], [16, 1], [9], [1]], ![[0, 12], [0, 18], [9], [1]]]
 h' := ![![[3, 18], [14, 8], [3, 18], [8, 3], [0, 1]], ![[0, 1], [0, 11], [0, 1], [17, 16], [3, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [1, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [11, 16, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![398, 50, 25]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 0, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![9, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![9, 1, 0]] 
 ![![19, 0, 0], ![9, 1, 0], ![11, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![9, 1, 0], ![2, 8, 4], ![140, 0, 11]]]
  hmulB := by decide  
  f := ![![![192, 1079, 544], ![171, -2584, 0]], ![![92, 508, 256], ![77, -1216, 0]], ![![114, 625, 315], ![93, -1496, 0]]]
  g := ![![![1, 0, 0], ![-9, 19, 0], ![-11, 0, 19]], ![![0, 1, 0], ![-6, 8, 4], ![1, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![3, 2, 1]] ![![19, 0, 0], ![9, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![171, 19, 0]], ![![57, 38, 19], ![171, 19, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![9, 1, 0]]], ![![![3, 2, 1]], ![![9, 1, 1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![2, -8, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![2, -8, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![2, 15, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![2, -8, 1], ![124, 10, -30], ![-1015, 35, -13]]]
  hmulB := by decide  
  f := ![![![-1, 8, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -15, 23]], ![![0, -1, 1], ![8, 20, -30], ![-43, 10, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [22, 4, 1] where
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
 g := ![![[19, 13], [4, 13], [20, 16], [1]], ![[13, 10], [21, 10], [2, 7], [1]]]
 h' := ![![[19, 22], [4, 6], [20, 6], [1, 19], [0, 1]], ![[0, 1], [3, 17], [19, 17], [17, 4], [19, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [9, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [22, 4, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4975, 3468, 176]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![201, 36, 176]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![7, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![7, 1, 0]] 
 ![![23, 0, 0], ![7, 1, 0], ![13, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![7, 1, 0], ![2, 6, 4], ![140, 0, 9]]]
  hmulB := by decide  
  f := ![![![-92, -299, -200], ![-23, 1150, 0]], ![![-30, -90, -60], ![1, 345, 0]], ![![-52, -169, -113], ![-13, 650, 0]]]
  g := ![![![1, 0, 0], ![-7, 23, 0], ![-13, 0, 23]], ![![0, 1, 0], ![-4, 6, 4], ![1, 0, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![2, -8, 1]] ![![23, 0, 0], ![7, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![161, 23, 0]], ![![46, -184, 23], ![138, -46, -23]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![7, 1, 0]]], ![![![2, -8, 1]], ![![6, -2, -1]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![3, 1, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0], ![3, 1, 0]] 
 ![![29, 0, 0], ![3, 1, 0], ![28, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![3, 1, 0], ![2, 2, 4], ![140, 0, 5]]]
  hmulB := by decide  
  f := ![![![-416, -419, -840], ![-29, 6090, 0]], ![![-42, -42, -84], ![1, 609, 0]], ![![-400, -404, -811], ![-44, 5880, 0]]]
  g := ![![![1, 0, 0], ![-3, 29, 0], ![-28, 0, 29]], ![![0, 1, 0], ![-4, 2, 4], ![0, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N0 : Nat.card (O ⧸ I29N0) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N0)

lemma isPrimeI29N0 : Ideal.IsPrime I29N0 := prime_ideal_of_norm_prime hp29.out _ NI29N0

def I29N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0], ![-7, 1, 0]] i)))

def SI29N1: IdealEqSpanCertificate' Table ![![29, 0, 0], ![-7, 1, 0]] 
 ![![29, 0, 0], ![22, 1, 0], ![1, 0, 1]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]], ![![-7, 1, 0], ![2, -8, 4], ![140, 0, -5]]]
  hmulB := by decide  
  f := ![![![-145, 638, -320], ![58, 2320, 0]], ![![-105, 478, -240], ![59, 1740, 0]], ![![-5, 22, -11], ![2, 80, 0]]]
  g := ![![![1, 0, 0], ![-22, 29, 0], ![-1, 0, 29]], ![![-1, 1, 0], ![6, -8, 4], ![5, 0, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI29N1 : Nat.card (O ⧸ I29N1) = 29 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI29N1)

lemma isPrimeI29N1 : Ideal.IsPrime I29N1 := prime_ideal_of_norm_prime hp29.out _ NI29N1
def MulI29N0 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![3, 1, 0]] ![![29, 0, 0], ![3, 1, 0]]
  ![![29, 0, 0], ![10, -6, 1]] where
 M := ![![![841, 0, 0], ![87, 29, 0]], ![![87, 29, 0], ![11, 5, 4]]]
 hmul := by decide  
 g := ![![![![19, 6, -1], ![29, 0, 0]], ![![-7, 7, -1], ![29, 0, 0]]], ![![![-7, 7, -1], ![29, 0, 0]], ![![-1, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  
def MulI29N1 : IdealMulLeCertificate' Table 
  ![![29, 0, 0], ![10, -6, 1]] ![![29, 0, 0], ![-7, 1, 0]]
  ![![29, 0, 0]] where
 M := ![![![841, 0, 0], ![-203, 29, 0]], ![![290, -174, 29], ![58, 58, -29]]]
 hmul := by decide  
 g := ![![![![29, 0, 0]], ![![-7, 1, 0]]], ![![![10, -6, 1]], ![![2, 2, -1]]]]
 hle2 := by decide  


def PBC29 : ContainsPrimesAboveP 29 ![I29N0, I29N0, I29N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI29N0
    exact isPrimeI29N0
    exact isPrimeI29N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 29 (by decide) (𝕀 ⊙ MulI29N0 ⊙ MulI29N1)
instance hp31 : Fact (Nat.Prime 31) := {out := by norm_num}

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-11, 14, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-11, 14, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![20, 14, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-11, 14, 1], ![168, -25, 58], ![2065, 35, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -14, 31]], ![![-1, 0, 1], ![-32, -27, 58], ![55, -7, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [23, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 30], [0, 1]]
 g := ![![[21, 19], [29, 28], [18, 19], [13, 1]], ![[20, 12], [21, 3], [17, 12], [26, 30]]]
 h' := ![![[13, 30], [15, 9], [20, 11], [11, 22], [0, 1]], ![[0, 1], [8, 22], [8, 20], [18, 9], [13, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [5, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [23, 18, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2583, 875, -15]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![93, 35, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![4, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![4, 1, 0]] 
 ![![31, 0, 0], ![4, 1, 0], ![13, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![4, 1, 0], ![2, 3, 4], ![140, 0, 6]]]
  hmulB := by decide  
  f := ![![![-187, -287, -384], ![-31, 2976, 0]], ![![-24, -36, -48], ![1, 372, 0]], ![![-81, -121, -161], ![7, 1248, 0]]]
  g := ![![![1, 0, 0], ![-4, 31, 0], ![-13, 0, 31]], ![![0, 1, 0], ![-2, 3, 4], ![2, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-11, 14, 1]] ![![31, 0, 0], ![4, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![124, 31, 0]], ![![-341, 434, 31], ![124, 31, 62]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![4, 1, 0]]], ![![![-11, 14, 1]], ![![4, 1, 2]]]]
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


lemma PB205I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB205I0 : PrimesBelowBoundCertificateInterval O 1 31 205 where
  m := 11
  g := ![2, 1, 3, 3, 2, 1, 2, 2, 2, 3, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB205I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0]
    · exact ![I5N0, I5N1, I5N2]
    · exact ![I7N0, I7N1, I7N2]
    · exact ![I11N0, I11N1]
    · exact ![I13N0]
    · exact ![I17N0, I17N1]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
    · exact ![I29N0, I29N0, I29N1]
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
    · exact ![27]
    · exact ![5, 5, 5]
    · exact ![7, 7, 7]
    · exact ![121, 11]
    · exact ![2197]
    · exact ![289, 17]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
      exact NI5N1
      exact NI5N2
    · dsimp ; intro j
      fin_cases j
      exact NI7N0
      exact NI7N1
      exact NI7N2
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
      exact NI11N1
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
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
      exact NI29N0
      exact NI29N1
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I5N2, I7N0, I7N1, I7N2, I11N0, I11N1, I17N1, I19N1, I23N1, I29N0, I29N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0], [I5N0, I5N1, I5N2], [I7N0, I7N1, I7N2], [I11N0, I11N1], [], [I17N1], [I19N1], [I23N1], [I29N0, I29N0, I29N1], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
