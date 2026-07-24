
import IdealArithmetic.Examples.NF5_5_390625_1.RI5_5_390625_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp2 : Fact (Nat.Prime 2) := {out := by norm_num}

def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0, 0, 0]] 
 ![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]] where
  M :=![![![2, 0, 0, 0, 0], ![0, 2, 0, 0, 0], ![0, 0, 2, 0, 0], ![0, 0, 0, 2, 0], ![0, 0, 0, 0, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P2P0 : CertificateIrreducibleZModOfList' 2 5 2 1 [1, 0, 1, 1, 1, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 1], [0, 0, 0, 0, 1], [0, 0, 1, 1, 1], [1, 1, 0, 1], [0, 1]]
 g := ![![[]], ![[]], ![[0, 0, 1, 1]], ![[1, 1, 1, 1]], ![[1, 1]]]
 h' := ![![[0, 0, 1], [0, 1]], ![[0, 0, 0, 0, 1], [0, 0, 1]], ![[0, 0, 1, 1, 1], [0, 0, 0, 0, 1]], ![[1, 1, 0, 1], [0, 0, 1, 1, 1]], ![[0, 1], [1, 1, 0, 1]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], [], [], []]
 b := ![[], [0, 1, 0, 1], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI2N0 : CertifiedPrimeIdeal' SI2N0 2 where
  n := 5
  hpos := by decide
  P := [1, 0, 1, 1, 1, 1]
  hirr := P2P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11799636922, 6538869328, -11137137414, -43339069312, -48685826378]
  a := ![4, -5, -3, -7, -14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![5899818461, 3269434664, -5568568707, -21669534656, -24342913189]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N0 B_one_repr
lemma NI2N0 : Nat.card (O ⧸ I2N0) = 32 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N0

def PBC2 : ContainsPrimesAboveP 2 ![I2N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI2N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![2, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 2 (by decide) 𝕀

instance hp3 : Fact (Nat.Prime 3) := {out := by norm_num}

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P3P0 : CertificateIrreducibleZModOfList' 3 5 2 1 [1, 1, 0, 1, 0, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 0, 0, 1], [0, 0, 1, 1, 2], [2, 2, 0, 2, 2], [1, 0, 2, 2, 2], [0, 1]]
 g := ![![[]], ![[0, 0, 2, 0, 1]], ![[1, 0, 0, 0, 1, 1, 0, 2]], ![[1, 2, 2, 0, 2, 1, 0, 2]], ![[1, 1, 2, 0, 2, 1, 0, 2]]]
 h' := ![![[0, 0, 0, 1], [0, 1]], ![[0, 0, 1, 1, 2], [0, 0, 0, 1]], ![[2, 2, 0, 2, 2], [0, 0, 1, 1, 2]], ![[1, 0, 2, 2, 2], [2, 2, 0, 2, 2]], ![[0, 1], [1, 0, 2, 2, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1], [], [], []]
 b := ![[], [1, 0, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI3N0 : CertifiedPrimeIdeal' SI3N0 3 where
  n := 5
  hpos := by decide
  P := [1, 1, 0, 1, 0, 1]
  hirr := P3P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-88669087728, 222531267885, -91005492339, 17076283164, 260419292982]
  a := ![-5, -56, 5, 8, 19]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-29556362576, 74177089295, -30335164113, 5692094388, 86806430994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI3N0 B_one_repr
lemma NI3N0 : Nat.card (O ⧸ I3N0) = 243 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI3N0

def PBC3 : ContainsPrimesAboveP 3 ![I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![3, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 3 (by decide) 𝕀


def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 3, -1, 0, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![2, 3, -1, 0, 1]] 
 ![![5, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![2, 3, -1, 0, 1], ![1, 0, 3, -1, -3], ![-1, 5, -1, 0, 2], ![2, -5, 5, -1, -6], ![-1, 4, -4, 1, 5]]]
  hmulB := by decide  
  f := ![![![1, 2, -2, 1, 3]], ![![1, 1, -1, 1, 2]], ![![0, 3, -2, 2, 5]], ![![1, -2, 1, 4, 3]], ![![0, 4, -3, 1, 5]]]
  g := ![![![-2, 3, -1, 0, 1], ![1, 0, 3, -1, -3], ![-5, 5, -1, 0, 2], ![6, -5, 5, -1, -6], ![-5, 4, -4, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N0 : Nat.card (O ⧸ I5N0) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N0)

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := prime_ideal_of_norm_prime hp5.out _ NI5N0
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![2, 3, -1, 0, 1]] ![![2, 3, -1, 0, 1]]
  ![![7, 5, 4, -2, -4]] where
 M := ![![![7, 5, 4, -2, -4]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N1 : IdealMulLeCertificate' Table 
  ![![7, 5, 4, -2, -4]] ![![2, 3, -1, 0, 1]]
  ![![15, 35, 10, -7, -8]] where
 M := ![![![15, 35, 10, -7, -8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N2 : IdealMulLeCertificate' Table 
  ![![15, 35, 10, -7, -8]] ![![2, 3, -1, 0, 1]]
  ![![49, 98, 77, -36, -68]] where
 M := ![![![49, 98, 77, -36, -68]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  
def MulI5N3 : IdealMulLeCertificate' Table 
  ![![49, 98, 77, -36, -68]] ![![2, 3, -1, 0, 1]]
  ![![5, 0, 0, 0, 0]] where
 M := ![![![115, 440, 260, -130, -215]]]
 hmul := by decide  
 g := ![![![![23, 88, 52, -26, -43]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0, 0, 0]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 1, 1, 0], ![-2, 2, 1, 4, 7], ![1, -2, 0, 0, -2]]]
  hmulB := by decide  
  f := ![![![4, 6, -8, 2, 7]], ![![1, 0, 0, 0, 0]], ![![3, 7, -8, 2, 7]], ![![1, -1, 1, 0, 0]], ![![1, 3, -4, 1, 3]]]
  g := ![![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 0, 1, 1, 0], ![-4, 2, 1, 4, 7], ![1, -2, 0, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N0 : Nat.card (O ⧸ I7N0) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N0)

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := prime_ideal_of_norm_prime hp7.out _ NI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -4, -5, 2, 4]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![1, -4, -5, 2, 4]] 
 ![![7, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![1, -4, -5, 2, 4], ![0, -3, -2, 1, 2], ![0, -2, -2, 1, 1], ![-1, 0, -1, 1, 4], ![1, -1, 0, 0, -2]]]
  hmulB := by decide  
  f := ![![![3, -1, -8, 3, 7]], ![![1, -1, -2, 1, 2]], ![![1, 0, -4, 2, 4]], ![![0, -1, 0, 2, 3]], ![![1, 0, -3, 1, 2]]]
  g := ![![![2, -4, -5, 2, 4], ![1, -3, -2, 1, 2], ![1, -2, -2, 1, 1], ![-1, 0, -1, 1, 4], ![1, -1, 0, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1

def I7N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, -1, -6, 2, 5]] i)))

def SI7N2: IdealEqSpanCertificate' Table ![![2, -1, -6, 2, 5]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![2, -1, -6, 2, 5], ![1, -4, 1, 0, -1], ![-1, 3, -4, 1, 3], ![1, -5, 4, -1, -2], ![0, 3, -4, 1, 2]]]
  hmulB := by decide  
  f := ![![![2, -4, -6, 1, 3]], ![![1, -2, -3, 0, 1]], ![![2, -3, -5, -1, 0]], ![![3, -2, -7, -5, -3]], ![![2, -4, -5, 1, 2]]]
  g := ![![![-1, -1, -6, 2, 5], ![2, -4, 1, 0, -1], ![-2, 3, -4, 1, 3], ![2, -5, 4, -1, -2], ![-1, 3, -4, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N2 : Nat.card (O ⧸ I7N2) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N2)

lemma isPrimeI7N2 : Ideal.IsPrime I7N2 := prime_ideal_of_norm_prime hp7.out _ NI7N2

def I7N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 2, 2, -1, -2]] i)))

def SI7N3: IdealEqSpanCertificate' Table ![![1, 2, 2, -1, -2]] 
 ![![7, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![1, 2, 2, -1, -2], ![0, 3, 1, -1, -1], ![1, 0, 2, -2, -4], ![0, 5, -2, -4, -2], ![1, -3, 1, 0, -2]]]
  hmulB := by decide  
  f := ![![![10, -8, -5, 2, 2]], ![![4, -2, -3, 1, 2]], ![![8, -8, -2, 1, -1]], ![![7, -2, -7, 2, 6]], ![![3, -5, 1, 0, -3]]]
  g := ![![![-1, 2, 2, -1, -2], ![-1, 3, 1, -1, -1], ![1, 0, 2, -2, -4], ![3, 5, -2, -4, -2], ![1, -3, 1, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N3 : Nat.card (O ⧸ I7N3) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N3)

lemma isPrimeI7N3 : Ideal.IsPrime I7N3 := prime_ideal_of_norm_prime hp7.out _ NI7N3

def I7N4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, -3, 1, 0, -1]] i)))

def SI7N4: IdealEqSpanCertificate' Table ![![0, -3, 1, 0, -1]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![0, -3, 1, 0, -1], ![-1, 2, -3, 1, 3], ![1, -5, 3, 0, -2], ![-2, 5, -5, 3, 6], ![1, -4, 4, -1, -3]]]
  hmulB := by decide  
  f := ![![![-11, 2, 10, -3, -7]], ![![-8, 1, 7, -2, -5]], ![![-5, 1, 4, -1, -2]], ![![-9, 0, 9, -2, -7]], ![![-4, 2, 3, -1, -1]]]
  g := ![![![2, -3, 1, 0, -1], ![-2, 2, -3, 1, 3], ![3, -5, 3, 0, -2], ![-6, 5, -5, 3, 6], ![3, -4, 4, -1, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N4 : Nat.card (O ⧸ I7N4) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N4)

lemma isPrimeI7N4 : Ideal.IsPrime I7N4 := prime_ideal_of_norm_prime hp7.out _ NI7N4
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0, 0, 0]] ![![1, -4, -5, 2, 4]]
  ![![1, -7, -7, 3, 6]] where
 M := ![![![1, -7, -7, 3, 6]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N1 : IdealMulLeCertificate' Table 
  ![![1, -7, -7, 3, 6]] ![![2, -1, -6, 2, 5]]
  ![![5, 9, 3, -2, -3]] where
 M := ![![![5, 9, 3, -2, -3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N2 : IdealMulLeCertificate' Table 
  ![![5, 9, 3, -2, -3]] ![![1, 2, 2, -1, -2]]
  ![![5, 36, 26, -12, -21]] where
 M := ![![![5, 36, 26, -12, -21]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI7N3 : IdealMulLeCertificate' Table 
  ![![5, 36, 26, -12, -21]] ![![0, -3, 1, 0, -1]]
  ![![7, 0, 0, 0, 0]] where
 M := ![![![-7, -49, -49, 21, 42]]]
 hmul := by decide  
 g := ![![![![-1, -7, -7, 3, 6]]]]
 hle2 := by decide  


def PBC7 : ContainsPrimesAboveP 7 ![I7N0, I7N1, I7N2, I7N3, I7N4] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI7N0
    exact isPrimeI7N1
    exact isPrimeI7N2
    exact isPrimeI7N3
    exact isPrimeI7N4
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 7 (by decide) (𝕀 ⊙ MulI7N0 ⊙ MulI7N1 ⊙ MulI7N2 ⊙ MulI7N3)
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


def P11P0 : CertificateIrreducibleZModOfList' 11 5 2 3 [8, 2, 3, 2, 4, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 1, 6, 5], [4, 9, 3, 7], [1, 5, 8, 6, 9], [7, 6, 5, 4, 2], [0, 1]]
 g := ![![[2, 6, 1, 7, 5], [1], []], ![[10, 2, 10, 8, 0, 2, 3], [10, 0, 4, 2, 1, 10, 9], [4, 3]], ![[6, 8, 4, 4, 8, 3, 7], [10, 8, 8, 6, 8, 3, 2], [0, 5]], ![[2, 7, 2, 3, 1, 3, 0, 1], [10, 5, 6, 4, 5, 3, 0, 4], [4, 2, 4, 4]], ![[5, 5, 8, 4, 5, 7, 0, 7], [9, 7, 8, 1, 10, 1, 9, 8], [6, 6, 0, 4]]]
 h' := ![![[6, 1, 6, 5], [3, 9, 8, 9, 7], [0, 0, 1], [0, 1]], ![[4, 9, 3, 7], [5, 4, 8, 4, 4], [4, 2, 0, 0, 2], [6, 1, 6, 5]], ![[1, 5, 8, 6, 9], [9, 2, 5, 9, 10], [5, 10, 7, 7, 4], [4, 9, 3, 7]], ![[7, 6, 5, 4, 2], [1, 3, 8, 3, 4], [2, 8, 4, 5, 3], [1, 5, 8, 6, 9]], ![[0, 1], [1, 4, 4, 8, 8], [1, 2, 10, 10, 2], [7, 6, 5, 4, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 0, 8], [], [], []]
 b := ![[], [2, 0, 2, 3, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 5
  hpos := by decide
  P := [8, 2, 3, 2, 4, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![17499922, 10066419, -16757785, -64689383, -72348386]
  a := ![1, -3, 0, -2, -3]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1590902, 915129, -1523435, -5880853, -6577126]
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


def P13P0 : CertificateIrreducibleZModOfList' 13 5 2 3 [3, 4, 4, 12, 8, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 0, 11, 4, 7], [9, 11, 0, 12, 1], [6, 11, 5, 5, 6], [2, 3, 10, 5, 12], [0, 1]]
 g := ![![[4, 9, 1], [5, 1], []], ![[11, 12, 11, 3, 1, 0, 1, 6], [7, 9, 8, 1], [2, 10, 5, 9, 8, 5, 2, 5]], ![[2, 5, 11, 9, 1, 4, 1, 3], [11, 9], [9, 1, 0, 8, 9, 1, 2, 1]], ![[6, 3, 11, 5, 3, 6, 8, 6], [11, 3, 3, 4], [1, 2, 9, 8, 8, 11, 8, 8]], ![[8, 10, 4, 2, 0, 6, 3, 4], [4, 8, 11, 9], [12, 6, 8, 12, 11, 4, 10, 12]]]
 h' := ![![[1, 0, 11, 4, 7], [11, 3, 2, 1], [0, 0, 0, 1], [0, 1]], ![[9, 11, 0, 12, 1], [4, 0, 5, 8, 5], [8, 1, 9, 5, 12], [1, 0, 11, 4, 7]], ![[6, 11, 5, 5, 6], [6, 7, 10, 10, 4], [0, 8, 3, 3], [9, 11, 0, 12, 1]], ![[2, 3, 10, 5, 12], [5, 1, 9, 1, 1], [5, 8, 1, 1, 11], [6, 11, 5, 5, 6]], ![[0, 1], [5, 2, 0, 6, 3], [11, 9, 0, 3, 3], [2, 3, 10, 5, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 1, 3, 3], [], [], []]
 b := ![[], [12, 2, 6, 7, 7], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 5
  hpos := by decide
  P := [3, 4, 4, 12, 8, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-157343380688, -86900917987, 148320199794, 577583110858, 649092379156]
  a := ![-7, 27, 5, 10, 25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-12103336976, -6684685999, 11409246138, 44429470066, 49930183012]
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


def P17P0 : CertificateIrreducibleZModOfList' 17 5 2 4 [4, 1, 11, 2, 5, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 2, 9, 1, 8], [8, 6, 16, 3, 11], [1, 6, 9, 1, 9], [2, 2, 0, 12, 6], [0, 1]]
 g := ![![[4, 9, 2, 1, 15], [3, 6, 12, 1], [], []], ![[2, 13, 13, 11, 4, 15, 8, 9], [9, 14, 10, 9], [12, 6, 10, 4], [4, 7, 2, 13]], ![[3, 16, 6, 11, 0, 7, 11, 7], [16, 4, 15, 4], [8, 6, 0, 8], [15, 9, 5, 2]], ![[16, 10, 1, 13, 11, 7, 15, 16], [8, 4], [5, 14, 16, 9], [2, 15, 4, 13]], ![[1, 14, 7, 8, 11, 11, 15, 14], [7, 3, 2, 16], [2, 2, 7, 15], [4, 14, 15, 2]]]
 h' := ![![[1, 2, 9, 1, 8], [5, 7, 15, 14, 10], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[8, 6, 16, 3, 11], [13, 5, 11, 12, 4], [7, 5, 16, 5, 14], [2, 6, 14, 1, 15], [1, 2, 9, 1, 8]], ![[1, 6, 9, 1, 9], [5, 12, 13, 4, 8], [1, 5, 12, 4, 15], [4, 11, 13, 13, 12], [8, 6, 16, 3, 11]], ![[2, 2, 0, 12, 6], [10, 12, 6, 9, 7], [12, 10, 7, 2], [10, 1, 1, 4, 14], [1, 6, 9, 1, 9]], ![[0, 1], [6, 15, 6, 12, 5], [0, 14, 16, 6, 4], [5, 16, 5, 16, 10], [2, 2, 0, 12, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 11, 2, 11], [], [], []]
 b := ![[], [12, 2, 16, 5, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI17N0 : CertifiedPrimeIdeal' SI17N0 17 where
  n := 5
  hpos := by decide
  P := [4, 1, 11, 2, 5, 1]
  hirr := P17P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![485628879815, 129767622384, -367269299072, -1627629097530, -1949702340388]
  a := ![11, -12, -5, -15, -39]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![28566404695, 7633389552, -21604076416, -95742888090, -114688372964]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0, 0, 0]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0, 0, 0]] 
 ![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]] where
  M :=![![![19, 0, 0, 0, 0], ![0, 19, 0, 0, 0], ![0, 0, 19, 0, 0], ![0, 0, 0, 19, 0], ![0, 0, 0, 0, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 5 2 4 [15, 0, 1, 9, 18, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 11, 9, 2, 4], [9, 15, 7, 1, 12], [15, 2, 4, 1, 15], [1, 9, 18, 15, 7], [0, 1]]
 g := ![![[13, 10, 9, 18, 1], [15, 1, 11, 1, 1], [], []], ![[7, 18, 14, 9, 0, 15, 16, 6], [7, 17, 14, 10, 17, 18, 0, 9], [1, 5, 6, 5], [12, 2, 13, 16]], ![[17, 3, 7, 3, 13, 15, 3, 10], [12, 6, 5, 8, 12, 13, 18, 12], [7, 17], [1, 10, 16, 11]], ![[16, 0, 18, 15, 3, 16, 17, 18], [14, 9, 4, 8, 12, 8, 17, 14], [10, 3, 16, 7], [3, 4, 8, 16]], ![[18, 7, 18, 16, 18, 5, 2, 9], [0, 3, 2, 1, 4, 9, 3, 5], [18, 1, 17, 1], [6, 10, 12, 11]]]
 h' := ![![[14, 11, 9, 2, 4], [3, 4, 10, 1, 18], [0, 0, 0, 0, 1], [0, 0, 1], [0, 1]], ![[9, 15, 7, 1, 12], [0, 4, 8, 12, 7], [13, 5, 7, 6, 11], [16, 12, 14, 18, 9], [14, 11, 9, 2, 4]], ![[15, 2, 4, 1, 15], [7, 6, 13, 16, 2], [14, 5, 14, 18, 18], [9, 6, 15, 6], [9, 15, 7, 1, 12]], ![[1, 9, 18, 15, 7], [12, 13, 11, 8, 9], [7, 12, 15, 8, 14], [9, 0, 1, 3, 11], [15, 2, 4, 1, 15]], ![[0, 1], [17, 11, 15, 1, 2], [13, 16, 2, 6, 13], [6, 1, 7, 11, 18], [1, 9, 18, 15, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 16, 16, 18], [], [], []]
 b := ![[], [6, 3, 11, 17, 5], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 5
  hpos := by decide
  P := [15, 0, 1, 9, 18, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-59133194885, 150934856580, -64199738704, 11368305036, 172762659412]
  a := ![-4, 4, 4, -4, 14]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-3112273415, 7943939820, -3378933616, 598331844, 9092771548]
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


def P23P0 : CertificateIrreducibleZModOfList' 23 5 2 4 [9, 5, 11, 0, 22, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 9, 20, 3, 9], [9, 6, 15, 18, 20], [13, 3, 0, 12, 3], [13, 4, 11, 13, 14], [0, 1]]
 g := ![![[14, 13, 7, 8, 16], [22, 4, 2, 1, 1], [1], []], ![[8, 15, 1, 5, 18, 16], [13, 8, 19, 15, 9, 11, 2, 4], [3, 17, 12, 9, 13, 8, 22, 16], [10, 21, 20, 12]], ![[4, 8, 2, 0, 21, 20, 6, 14], [22, 1, 11, 20, 14, 2, 4, 17], [14, 20, 22, 12, 13, 18, 13, 14], [11, 20, 16, 9]], ![[8, 18, 22, 10, 13, 0, 12, 6], [17, 20, 8, 15, 21, 8, 7, 4], [16, 0, 5, 12, 18, 5, 12, 12], [6, 18, 12, 9]], ![[12, 1, 0, 11, 3, 2, 12, 22], [17, 22, 1, 6, 19, 11, 18, 20], [17, 15, 7, 14, 18, 21, 4, 17], [15, 2, 8, 12]]]
 h' := ![![[12, 9, 20, 3, 9], [9, 4, 17, 22, 4], [14, 18, 12, 0, 1], [0, 0, 1], [0, 1]], ![[9, 6, 15, 18, 20], [22, 12, 11, 14], [5, 17, 13, 22, 7], [8, 0, 5, 16, 9], [12, 9, 20, 3, 9]], ![[13, 3, 0, 12, 3], [13, 6, 14, 4, 16], [7, 16, 19, 7, 5], [5, 11, 10, 8, 16], [9, 6, 15, 18, 20]], ![[13, 4, 11, 13, 14], [16, 18, 18, 19, 18], [17, 12, 22, 2, 20], [0, 1, 21, 19, 2], [13, 3, 0, 12, 3]], ![[0, 1], [16, 6, 9, 10, 8], [17, 6, 3, 15, 13], [11, 11, 9, 3, 19], [13, 4, 11, 13, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 12, 19, 13], [], [], []]
 b := ![[], [6, 2, 12, 16, 19], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 5
  hpos := by decide
  P := [9, 5, 11, 0, 22, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-944908802844, -542928804071, 904475872068, 3492183204740, 3906217848490]
  a := ![-5, 17, 10, 15, 24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-41082991428, -23605600177, 39325037916, 151834052380, 169835558630]
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



lemma PB25I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 24 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 24 (by omega)

def PB25I0 : PrimesBelowBoundCertificateInterval O 1 24 25 where
  m := 9
  g := ![1, 1, 5, 5, 1, 1, 1, 1, 1]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23]
  hP := PB25I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0]
    · exact ![I3N0]
    · exact ![I5N0, I5N0, I5N0, I5N0, I5N0]
    · exact ![I7N0, I7N1, I7N2, I7N3, I7N4]
    · exact ![I11N0]
    · exact ![I13N0]
    · exact ![I17N0]
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
    · exact ![32]
    · exact ![243]
    · exact ![5, 5, 5, 5, 5]
    · exact ![7, 7, 7, 7, 7]
    · exact ![161051]
    · exact ![371293]
    · exact ![1419857]
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
    · dsimp ; intro j
      fin_cases j
      exact NI3N0
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
      exact NI7N3
      exact NI7N4
    · dsimp ; intro j
      fin_cases j
      exact NI11N0
    · dsimp ; intro j
      fin_cases j
      exact NI13N0
    · dsimp ; intro j
      fin_cases j
      exact NI17N0
    · dsimp ; intro j
      fin_cases j
      exact NI19N0
    · dsimp ; intro j
      fin_cases j
      exact NI23N0
  β := ![I5N0, I7N0, I7N1, I7N2, I7N3, I7N4]
  Il := ![[], [], [I5N0, I5N0, I5N0, I5N0, I5N0], [I7N0, I7N1, I7N2, I7N3, I7N4], [], [], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
