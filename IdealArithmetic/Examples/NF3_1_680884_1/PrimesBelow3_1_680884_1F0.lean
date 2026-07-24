
import IdealArithmetic.Examples.NF3_1_680884_1.RI3_1_680884_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-46, -3, 1]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-46, -3, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-46, -3, 1], ![352, 27, -5], ![-851, -5, 24]]]
  hmulB := by decide  
  f := ![![![24, -49, -6], ![-36, 0, 2]], ![![12, -24, -3], ![-18, 0, 1]], ![![35, -23, -3], ![-17, 0, 1]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![-1, 0, 2]], ![![-22, -3, 1], ![165, 27, -5], ![-435, -5, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-46, -4, 1]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![-46, -4, 1]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![-46, -4, 1], ![351, 27, -7], ![-1206, -78, 23]]]
  hmulB := by decide  
  f := ![![![-28, 1, 0], ![14, 2, 0]], ![![-14, 1, 0], ![7, 1, 0]], ![![-6, 3, 0], ![15, 2, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 2]], ![![-21, -4, 1], ![162, 27, -7], ![-564, -78, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N1 : Nat.card (O ⧸ I2N1) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N1)

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := prime_ideal_of_norm_prime hp2.out _ NI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-46, -3, 1]] ![![2, 0, 0], ![-46, -3, 1]]
  ![![2, 0, 0], ![-47, -4, 1]] where
 M := ![![![4, 0, 0], ![-92, -6, 2]], ![![-92, -6, 2], ![209, 52, -7]]]
 hmul := by decide  
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![2, 0, 0]]], ![![![1, 1, 0], ![2, 0, 0]], ![![34, 20, -2], ![-3, 0, 0]]]]
 hle2 := by decide  
def MulI2N1 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![-47, -4, 1]] ![![2, 0, 0], ![-46, -4, 1]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![-92, -8, 2]], ![![-94, -8, 2], ![-448, 2, 4]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![-46, -4, 1]]], ![![![-47, -4, 1]], ![![-224, 1, 2]]]]
 hle2 := by decide  


def PBC2 : ContainsPrimesAboveP 2 ![I2N0, I2N0, I2N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
    exact isPrimeI2N0
    exact isPrimeI2N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 2 (by decide) (𝕀 ⊙ MulI2N0 ⊙ MulI2N1)
instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-48, -4, 1]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-48, -4, 1]] 
 ![![3, 0, 0], ![0, 3, 0], ![0, 2, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-48, -4, 1], ![351, 25, -7], ![-1206, -78, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![16, 2, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -2, 3]], ![![-16, -2, 1], ![117, 13, -7], ![-402, -40, 21]]]
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
  c := ![889422, 922420, 326306]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![296474, 89936, 326306]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 9 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def I3N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))

def SI3N1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![1, 1, 2], ![355, 73, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-1, -1, -1], ![1, 2, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![0, 1, 2], ![94, 73, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N1 : Nat.card (O ⧸ I3N1) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N1)

lemma isPrimeI3N1 : Ideal.IsPrime I3N1 := prime_ideal_of_norm_prime hp3.out _ NI3N1
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-48, -4, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![-144, -12, 3], ![303, 21, -6]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![1, 1, 0]]], ![![![-48, -4, 1]], ![![101, 7, -2]]]]
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

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0]] 
 ![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 3 2 2 [1, 1, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 1, 4], [4, 3, 1], [0, 1]]
 g := ![![[4, 0, 1], []], ![[0, 4, 1, 1], [3, 1]], ![[0, 4, 2, 1], [1, 1]]]
 h' := ![![[1, 1, 4], [0, 0, 1], [0, 1]], ![[4, 3, 1], [3, 3, 3], [1, 1, 4]], ![[0, 1], [0, 2, 1], [4, 3, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 4], []]
 b := ![[], [3, 3, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 3
  hpos := by decide
  P := [1, 1, 0, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9505850, -3523755, -695220]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1901170, -704751, -139044]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 125 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def PBC5 : ContainsPrimesAboveP 5 ![I5N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI5N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![5, 0, 0]]) timesTableT_eq_Table B_one_repr 5 (by decide) 𝕀

instance hp7 : Fact (Nat.Prime 7) := {out := by norm_num}

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-49, -5, 1]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-49, -5, 1]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 2, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-49, -5, 1], ![350, 24, -9], ![-1561, -151, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, -2, 7]], ![![-7, -1, 1], ![50, 6, -9], ![-223, -27, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [4, 0, 1] where
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
 g := ![![[0, 2], [0, 1]], ![[0, 5], [0, 6]]]
 h' := ![![[0, 6], [0, 3], [0, 1]], ![[0, 1], [0, 4], [0, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [0, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [4, 0, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2282, 1150, 302]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![326, 78, 302]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![1, 2, 2], ![355, 73, 3]]]
  hmulB := by decide  
  f := ![![![-13, -31, -32], ![-7, 112, 0]], ![![-4, -8, -8], ![1, 28, 0]], ![![-4, -9, -9], ![-1, 32, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-1, 2, 2], ![29, 73, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![7, 0, 0], ![-49, -5, 1]] ![![7, 0, 0], ![2, 1, 0]]
  ![![7, 0, 0]] where
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![-343, -35, 7], ![252, 14, -7]]]
 hmul := by decide  
 g := ![![![![7, 0, 0]], ![![2, 1, 0]]], ![![![-49, -5, 1]], ![![36, 2, -1]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [5, 0, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 9, 3], [1, 1, 8], [0, 1]]
 g := ![![[0, 1, 5], [1, 1, 1], []], ![[2, 6, 8, 5], [2, 4, 6, 3], [8, 9]], ![[3, 0, 8, 8], [8, 9, 4, 10], [3, 9]]]
 h' := ![![[0, 9, 3], [6, 6, 7], [0, 0, 1], [0, 1]], ![[1, 1, 8], [1, 3, 3], [4, 10, 1], [0, 9, 3]], ![[0, 1], [2, 2, 1], [8, 1, 9], [1, 1, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9], []]
 b := ![[], [0, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [5, 0, 10, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22821788, 6250948, 927817]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2074708, 568268, 84347]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![13, 0, 0]] 
 ![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 3 2 3 [9, 11, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 6, 8], [3, 6, 5], [0, 1]]
 g := ![![[6, 6, 10], [5, 1], [1]], ![[10, 12, 3, 7], [2, 3], [7, 9, 0, 5]], ![[3, 6, 8, 2], [6, 9], [5, 4, 3, 8]]]
 h' := ![![[11, 6, 8], [10, 4, 6], [4, 2, 1], [0, 1]], ![[3, 6, 5], [5, 8, 3], [7, 5, 9], [11, 6, 8]], ![[0, 1], [10, 1, 4], [8, 6, 3], [3, 6, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 10], []]
 b := ![[], [3, 12, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 3
  hpos := by decide
  P := [9, 11, 12, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-398736, -421707, -122694]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30672, -32439, -9438]
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


def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 2, 0]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-29, 2, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![8, 0, 1]] where
  M :=![![![-29, 2, 0], ![2, -29, 4], ![710, 146, -27]]]
  hmulB := by decide  
  f := ![![![199, 54, 8]], ![![299, 81, 12]], ![![1322, 358, 53]]]
  g := ![![![-3, 2, 0], ![17, -29, 4], ![-40, 146, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-29, 2, 0]] ![![-29, 2, 0]]
  ![![845, -116, 8]] where
 M := ![![![845, -116, 8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI17N1 : IdealMulLeCertificate' Table 
  ![![845, -116, 8]] ![![-29, 2, 0]]
  ![![17, 0, 0]] where
 M := ![![![-19057, 6222, -680]]]
 hmul := by decide  
 g := ![![![![-1121, 366, -40]]]]
 hle2 := by decide  

def PBC17 : ContainsPrimesAboveP 17 ![I17N0, I17N0, I17N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI17N0
    exact isPrimeI17N0
    exact isPrimeI17N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 17 (by decide) (𝕀 ⊙ MulI17N0 ⊙ MulI17N1)

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 1, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 1, 0]] 
 ![![19, 0, 0], ![3, 1, 0], ![15, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 1, 0], ![1, 3, 2], ![355, 73, 4]]]
  hmulB := by decide  
  f := ![![![-25, -78, -52], ![0, 494, 0]], ![![-4, -12, -8], ![1, 76, 0]], ![![-21, -62, -41], ![8, 390, 0]]]
  g := ![![![1, 0, 0], ![-3, 19, 0], ![-15, 0, 19]], ![![0, 1, 0], ![-2, 3, 2], ![4, 73, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N0 : Nat.card (O ⧸ I19N0) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N0)

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := prime_ideal_of_norm_prime hp19.out _ NI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-7, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-7, 1, 0]] 
 ![![19, 0, 0], ![12, 1, 0], ![14, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-7, 1, 0], ![1, -7, 2], ![355, 73, -6]]]
  hmulB := by decide  
  f := ![![![-83, 780, -224], ![76, 2128, 0]], ![![-48, 487, -140], ![58, 1330, 0]], ![![-56, 574, -165], ![70, 1568, 0]]]
  g := ![![![1, 0, 0], ![-12, 19, 0], ![-14, 0, 19]], ![![-1, 1, 0], ![3, -7, 2], ![-23, 73, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![3, 1, 0]] ![![19, 0, 0], ![3, 1, 0]]
  ![![19, 0, 0], ![-52, 3, 1]] where
 M := ![![![361, 0, 0], ![57, 19, 0]], ![![57, 19, 0], ![10, 6, 2]]]
 hmul := by decide  
 g := ![![![![19, 0, 0], ![0, 0, 0]], ![![3, 1, 0], ![0, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![6, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI19N1 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![-52, 3, 1]] ![![19, 0, 0], ![-7, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![-133, 19, 0]], ![![-988, 57, 19], ![722, 0, 0]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![-7, 1, 0]]], ![![![-52, 3, 1]], ![![38, 0, 0]]]]
 hle2 := by decide  


def PBC19 : ContainsPrimesAboveP 19 ![I19N0, I19N0, I19N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI19N0
    exact isPrimeI19N0
    exact isPrimeI19N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 19 (by decide) (𝕀 ⊙ MulI19N0 ⊙ MulI19N1)
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


def P23P0 : CertificateIrreducibleZModOfList' 23 3 2 4 [16, 8, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 13, 8], [7, 9, 15], [0, 1]]
 g := ![![[21, 18, 8], [7, 8, 13], [18, 16, 1], []], ![[4, 1], [0, 9, 21, 16], [18, 9, 8, 4], [13, 18]], ![[17, 1, 13, 5], [22, 4, 9, 21], [17, 21, 17, 5], [6, 18]]]
 h' := ![![[9, 13, 8], [3, 6, 10], [11, 14, 6], [0, 0, 1], [0, 1]], ![[7, 9, 15], [6, 16], [19, 16, 5], [11, 3, 9], [9, 13, 8]], ![[0, 1], [12, 1, 13], [11, 16, 12], [22, 20, 13], [7, 9, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 10], []]
 b := ![[], [2, 15, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 3
  hpos := by decide
  P := [16, 8, 7, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7203439, 2323115, 409768]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![313193, 101005, 17816]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [9, 9, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16, 21], [2, 12, 8], [0, 1]]
 g := ![![[25], [28, 7], [1, 16, 23], [1]], ![[10, 1, 25, 18], [23, 5], [3, 1, 14, 2], [19, 20, 1, 10]], ![[27, 9, 18, 11], [17, 25], [21, 1, 7, 2], [26, 18, 10, 19]]]
 h' := ![![[7, 16, 21], [3, 24], [20, 15, 23], [20, 20, 9], [0, 1]], ![[2, 12, 8], [26, 7, 11], [1, 28, 11], [27, 0, 6], [7, 16, 21]], ![[0, 1], [22, 27, 18], [28, 15, 24], [6, 9, 14], [2, 12, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 28], []]
 b := ![[], [3, 6, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [9, 9, 20, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11421911, -3878750, -709920]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-393859, -133750, -24480]
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


def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![5, 1, 0]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![5, 1, 0]] 
 ![![31, 0, 0], ![5, 1, 0], ![19, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![5, 1, 0], ![1, 5, 2], ![355, 73, 6]]]
  hmulB := by decide  
  f := ![![![-334, -1747, -700], ![-93, 10850, 0]], ![![-56, -280, -112], ![1, 1736, 0]], ![![-206, -1071, -429], ![-49, 6650, 0]]]
  g := ![![![1, 0, 0], ![-5, 31, 0], ![-19, 0, 31]], ![![0, 1, 0], ![-2, 5, 2], ![-4, 73, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N0 : Nat.card (O ⧸ I31N0) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N0)

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := prime_ideal_of_norm_prime hp31.out _ NI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-11, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-11, 1, 0]] 
 ![![31, 0, 0], ![20, 1, 0], ![2, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-11, 1, 0], ![1, -11, 2], ![355, 73, -10]]]
  hmulB := by decide  
  f := ![![![-47, 768, -140], ![62, 2170, 0]], ![![-33, 494, -90], ![32, 1395, 0]], ![![3, 49, -9], ![21, 140, 0]]]
  g := ![![![1, 0, 0], ![-20, 31, 0], ![-2, 0, 31]], ![![-1, 1, 0], ![7, -11, 2], ![-35, 73, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![5, 1, 0]] ![![31, 0, 0], ![5, 1, 0]]
  ![![31, 0, 0], ![-49, 5, 1]] where
 M := ![![![961, 0, 0], ![155, 31, 0]], ![![155, 31, 0], ![26, 10, 2]]]
 hmul := by decide  
 g := ![![![![31, 0, 0], ![0, 0, 0]], ![![5, 1, 0], ![0, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI31N1 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![-49, 5, 1]] ![![31, 0, 0], ![-11, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-341, 31, 0]], ![![-1519, 155, 31], ![899, -31, 0]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-11, 1, 0]]], ![![![-49, 5, 1]], ![![29, -1, 0]]]]
 hle2 := by decide  


def PBC31 : ContainsPrimesAboveP 31 ![I31N0, I31N0, I31N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI31N0
    exact isPrimeI31N0
    exact isPrimeI31N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 31 (by decide) (𝕀 ⊙ MulI31N0 ⊙ MulI31N1)


lemma PB234I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB234I0 : PrimesBelowBoundCertificateInterval O 1 31 234 where
  m := 11
  g := ![3, 2, 1, 2, 1, 1, 3, 3, 1, 1, 3]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB234I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N0, I2N1]
    · exact ![I3N0, I3N1]
    · exact ![I5N0]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0, I17N0, I17N0]
    · exact ![I19N0, I19N0, I19N1]
    · exact ![I23N0]
    · exact ![I29N0]
    · exact ![I31N0, I31N0, I31N1]
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
    · exact ![125]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![2197]
    · exact ![17, 17, 17]
    · exact ![19, 19, 19]
    · exact ![12167]
    · exact ![24389]
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
      exact NI2N1
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
      exact NI3N1
    · dsimp ; intro j
      fin_cases j
      exact NI5N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
      exact NI17N0
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
      exact NI19N0
      exact NI19N1
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
    · dsimp ; intro j
      fin_cases j
      exact NI29N0
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I3N1, I5N0, I7N0, I7N1, I17N0, I19N0, I19N1, I31N0, I31N1]
  Il := ![[I2N0, I2N0, I2N1], [I3N0, I3N1], [I5N0], [I7N0, I7N1], [], [], [I17N0, I17N0, I17N0], [I19N0, I19N0, I19N1], [], [], [I31N0, I31N0, I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
