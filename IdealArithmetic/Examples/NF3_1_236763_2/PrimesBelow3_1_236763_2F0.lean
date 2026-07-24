
import IdealArithmetic.Examples.NF3_1_236763_2.RI3_1_236763_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I2N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))

def SI2N0: IdealEqSpanCertificate' Table ![![2, 0, 0], ![0, 1, 0]] 
 ![![2, 0, 0], ![0, 1, 0], ![1, 0, 1]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![0, 1, 0], ![2, 3, 8], ![47, -19, -3]]]
  hmulB := by decide  
  f := ![![![48, -16, -3], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]], ![![24, -8, -1], ![-3, 0, -1]]]
  g := ![![![1, 0, 0], ![0, 2, 0], ![-1, 0, 2]], ![![0, 1, 0], ![-3, 3, 8], ![25, -19, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI2N0 : Nat.card (O ⧸ I2N0) = 2 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI2N0)

lemma isPrimeI2N0 : Ideal.IsPrime I2N0 := prime_ideal_of_norm_prime hp2.out _ NI2N0

def I2N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))

def SI2N1: IdealEqSpanCertificate' Table ![![2, 0, 0], ![1, 1, 0]] 
 ![![2, 0, 0], ![1, 1, 0], ![0, 0, 2]] where
  M :=![![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]], ![![1, 1, 0], ![2, 4, 8], ![47, -19, -2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![0, 0, 0]]]
  g := ![![![1, 0, 0], ![-1, 2, 0], ![0, 0, 1]], ![![0, 1, 0], ![-1, 4, 4], ![33, -19, -1]]]
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
  c := ![-1533, 391, -1408]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-962, 391, -704]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI2N1 : Ideal.IsPrime I2N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI2N1 B_one_repr
lemma NI2N1 : Nat.card (O ⧸ I2N1) = 4 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI2N1
def MulI2N0 : IdealMulLeCertificate' Table 
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0]] where
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![0, 2, 0], ![2, 4, 8]]]
 hmul := by decide  
 g := ![![![![2, 0, 0]], ![![1, 1, 0]]], ![![![0, 1, 0]], ![![1, 2, 4]]]]
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

def I3N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))

def SI3N0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![2, 2, 8], ![47, -19, -4]]]
  hmulB := by decide  
  f := ![![![-7, -8, -32], ![0, 12, 0]], ![![-6, 3, -8], ![-14, 3, 0]], ![![-4, -6, -21], ![2, 8, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-6, 2, 8], ![31, -19, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI3N0 : Nat.card (O ⧸ I3N0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI3N0)

lemma isPrimeI3N0 : Ideal.IsPrime I3N0 := prime_ideal_of_norm_prime hp3.out _ NI3N0
def MulI3N0 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0], ![12, 2, 1]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![3, 1, 8]]]
 hmul := by decide  
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-1, 1, 0], ![0, 0, 0]]], ![![![-1, 1, 0], ![0, 0, 0]], ![![-7, -1, 2], ![2, 0, 0]]]]
 hle2 := by decide  
def MulI3N1 : IdealMulLeCertificate' Table 
  ![![3, 0, 0], ![12, 2, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![3, 0, 0]] where
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![36, 6, 3], ![39, -3, 12]]]
 hmul := by decide  
 g := ![![![![3, 0, 0]], ![![-1, 1, 0]]], ![![![12, 2, 1]], ![![13, -1, 4]]]]
 hle2 := by decide  

def PBC3 : ContainsPrimesAboveP 3 ![I3N0, I3N0, I3N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI3N0
    exact isPrimeI3N0
    exact isPrimeI3N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 3 (by decide) (𝕀 ⊙ MulI3N0 ⊙ MulI3N1)
instance hp5 : Fact (Nat.Prime 5) := {out := by norm_num}

def I5N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![13, 3, 1]] i)))

def SI5N0: IdealEqSpanCertificate' Table ![![5, 0, 0], ![13, 3, 1]] 
 ![![5, 0, 0], ![0, 5, 0], ![3, 3, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![13, 3, 1], ![53, 3, 21], ![101, -44, -13]]]
  hmulB := by decide  
  f := ![![![-12, -3, -1], ![5, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -3, 5]], ![![2, 0, 1], ![-2, -12, 21], ![28, -1, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P5P0 : CertificateIrreducibleZModOfList' 5 2 2 2 [1, 4, 1] where
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

def PI5N0 : CertifiedPrimeIdeal' SI5N0 5 where
  n := 2
  hpos := by decide
  P := [1, 4, 1]
  hirr := P5P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![118648, -498247, -3583784]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2174000, 2050621, -3583784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI5N0 : Ideal.IsPrime I5N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI5N0 B_one_repr
lemma NI5N0 : Nat.card (O ⧸ I5N0) = 25 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI5N0

def I5N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))

def SI5N1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-1, 1, 0]] 
 ![![5, 0, 0], ![4, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-1, 1, 0], ![2, 2, 8], ![47, -19, -4]]]
  hmulB := by decide  
  f := ![![![33, 32, 128], ![0, -80, 0]], ![![25, 24, 96], ![1, -60, 0]], ![![20, 19, 77], ![1, -48, 0]]]
  g := ![![![1, 0, 0], ![-4, 5, 0], ![-3, 0, 5]], ![![-1, 1, 0], ![-6, 2, 8], ![27, -19, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI5N1 : Nat.card (O ⧸ I5N1) = 5 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI5N1)

lemma isPrimeI5N1 : Ideal.IsPrime I5N1 := prime_ideal_of_norm_prime hp5.out _ NI5N1
def MulI5N0 : IdealMulLeCertificate' Table 
  ![![5, 0, 0], ![13, 3, 1]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![5, 0, 0]] where
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![65, 15, 5], ![40, 0, 20]]]
 hmul := by decide  
 g := ![![![![5, 0, 0]], ![![-1, 1, 0]]], ![![![13, 3, 1]], ![![8, 0, 4]]]]
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

def I7N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7325472, -273390, -391501]] i)))

def SI7N0: IdealEqSpanCertificate' Table ![![-7325472, -273390, -391501]] 
 ![![7, 0, 0], ![0, 7, 0], ![0, 1, 1]] where
  M :=![![![-7325472, -273390, -391501], ![-18947327, -707123, -1012617], ![2810710, 104897, 150215]]]
  hmulB := by decide  
  f := ![![![-572, 221, -1]], ![![395, 110, 1771]], ![![1546, -586, 79]]]
  g := ![![![-1046496, 16873, -391501], ![-2706761, 43642, -1012617], ![401530, -6474, 150215]]]
  hle1 := by decide   
  hle2 := by decide  


def P7P0 : CertificateIrreducibleZModOfList' 7 2 2 2 [3, 2, 1] where
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
 g := ![![[3, 1], [5, 1]], ![[1, 6], [3, 6]]]
 h' := ![![[5, 6], [6, 1], [0, 1]], ![[0, 1], [4, 6], [5, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [2, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI7N0 : CertifiedPrimeIdeal' SI7N0 7 where
  n := 2
  hpos := by decide
  P := [3, 2, 1]
  hirr := P7P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1834, 285, -3005]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-262, 470, -3005]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI7N0 : Ideal.IsPrime I7N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI7N0 B_one_repr
lemma NI7N0 : Nat.card (O ⧸ I7N0) = 49 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI7N0

def I7N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-572, 221, -1]] i)))

def SI7N1: IdealEqSpanCertificate' Table ![![-572, 221, -1]] 
 ![![7, 0, 0], ![2, 1, 0], ![6, 0, 1]] where
  M :=![![![-572, 221, -1], ![395, 110, 1771], ![10427, -4212, -1218]]]
  hmulB := by decide  
  f := ![![![-7325472, -273390, -391501]], ![![-4799753, -179129, -256517]], ![![-5877446, -219349, -314113]]]
  g := ![![![-144, 221, -1], ![-1493, 110, 1771], ![3737, -4212, -1218]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI7N1 : Nat.card (O ⧸ I7N1) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI7N1)

lemma isPrimeI7N1 : Ideal.IsPrime I7N1 := prime_ideal_of_norm_prime hp7.out _ NI7N1
def MulI7N0 : IdealMulLeCertificate' Table 
  ![![-7325472, -273390, -391501]] ![![-572, 221, -1]]
  ![![7, 0, 0]] where
 M := ![![![7, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P11P0 : CertificateIrreducibleZModOfList' 11 3 2 3 [1, 7, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 6, 2], [6, 4, 9], [0, 1]]
 g := ![![[1, 3, 1], [7, 5, 1], []], ![[1, 2, 9, 8], [8, 4, 0, 10], [0, 4]], ![[0, 10, 2, 4], [6, 2, 5, 5], [4, 4]]]
 h' := ![![[10, 6, 2], [4, 1, 10], [0, 0, 1], [0, 1]], ![[6, 4, 9], [2, 0, 9], [1, 6, 4], [10, 6, 2]], ![[0, 1], [0, 10, 3], [10, 5, 6], [6, 4, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 5], []]
 b := ![[], [6, 7, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI11N0 : CertifiedPrimeIdeal' SI11N0 11 where
  n := 3
  hpos := by decide
  P := [1, 7, 6, 1]
  hirr := P11P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-447601, 89518, -561132]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40691, 8138, -51012]
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

def I13N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5877446, -219349, -314113]] i)))

def SI13N0: IdealEqSpanCertificate' Table ![![-5877446, -219349, -314113]] 
 ![![13, 0, 0], ![0, 13, 0], ![6, 0, 1]] where
  M :=![![![-5877446, -219349, -314113], ![-15202009, -567346, -812453], ![2255117, 84162, 120522]]]
  hmulB := by decide  
  f := ![![![402, -144, 77]], ![![3331, -1493, -1383]], ![![-572, 221, -1]]]
  g := ![![![-307136, -16873, -314113], ![-794407, -43642, -812453], ![117845, 6474, 120522]]]
  hle1 := by decide   
  hle2 := by decide  


def P13P0 : CertificateIrreducibleZModOfList' 13 2 2 3 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 12], [0, 1]]
 g := ![![[12, 3], [10], [9, 1]], ![[0, 10], [10], [5, 12]]]
 h' := ![![[9, 12], [10, 9], [10, 7], [0, 1]], ![[0, 1], [0, 4], [8, 6], [9, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [8, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI13N0 : CertifiedPrimeIdeal' SI13N0 13 where
  n := 2
  hpos := by decide
  P := [9, 4, 1]
  hirr := P13P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![49638, -36491, -144763]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70632, -2807, -144763]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI13N0 : Ideal.IsPrime I13N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI13N0 B_one_repr
lemma NI13N0 : Nat.card (O ⧸ I13N0) = 169 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI13N0

def I13N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![402, -144, 77]] i)))

def SI13N1: IdealEqSpanCertificate' Table ![![402, -144, 77]] 
 ![![13, 0, 0], ![3, 1, 0], ![11, 0, 1]] where
  M :=![![![402, -144, 77], ![3331, -1493, -1383], ![-9848, 3737, -475]]]
  hmulB := by decide  
  f := ![![![-5877446, -219349, -314113]], ![![-2525719, -94261, -134984]], ![![-4799753, -179129, -256517]]]
  g := ![![![-1, -144, 77], ![1771, -1493, -1383], ![-1218, 3737, -475]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI13N1 : Nat.card (O ⧸ I13N1) = 13 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI13N1)

lemma isPrimeI13N1 : Ideal.IsPrime I13N1 := prime_ideal_of_norm_prime hp13.out _ NI13N1
def MulI13N0 : IdealMulLeCertificate' Table 
  ![![-5877446, -219349, -314113]] ![![402, -144, 77]]
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

def I17N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1546, 586, -79]] i)))

def SI17N0: IdealEqSpanCertificate' Table ![![-1546, 586, -79]] 
 ![![17, 0, 0], ![9, 1, 0], ![8, 0, 1]] where
  M :=![![![-1546, 586, -79], ![-2541, 1713, 4925], ![30702, -12161, -1961]]]
  hmulB := by decide  
  f := ![![![56533732, 2109865, 3021377]], ![![38531061, 1437997, 2059246]], ![![25328143, 945258, 1353632]]]
  g := ![![![-364, 586, -79], ![-3374, 1713, 4925], ![9167, -12161, -1961]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N0 : Nat.card (O ⧸ I17N0) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N0)

lemma isPrimeI17N0 : Ideal.IsPrime I17N0 := prime_ideal_of_norm_prime hp17.out _ NI17N0

def I17N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))

def SI17N1: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-6, 1, 0]] 
 ![![17, 0, 0], ![11, 1, 0], ![15, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-6, 1, 0], ![2, -3, 8], ![47, -19, -9]]]
  hmulB := by decide  
  f := ![![![151, -249, 672], ![-51, -1428, 0]], ![![97, -160, 432], ![-33, -918, 0]], ![![129, -219, 593], ![-57, -1260, 0]]]
  g := ![![![1, 0, 0], ![-11, 17, 0], ![-15, 0, 17]], ![![-1, 1, 0], ![-5, -3, 8], ![23, -19, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N1 : Nat.card (O ⧸ I17N1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N1)

lemma isPrimeI17N1 : Ideal.IsPrime I17N1 := prime_ideal_of_norm_prime hp17.out _ NI17N1

def I17N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-3, 1, 0]] i)))

def SI17N2: IdealEqSpanCertificate' Table ![![17, 0, 0], ![-3, 1, 0]] 
 ![![17, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![17, 0, 0], ![0, 17, 0], ![0, 0, 17]], ![![-3, 1, 0], ![2, 0, 8], ![47, -19, -6]]]
  hmulB := by decide  
  f := ![![![215, 2, 880], ![-34, -1870, 0]], ![![178, 1, 720], ![-16, -1530, 0]], ![![166, 1, 673], ![-17, -1430, 0]]]
  g := ![![![1, 0, 0], ![-14, 17, 0], ![-13, 0, 17]], ![![-1, 1, 0], ![-6, 0, 8], ![23, -19, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI17N2 : Nat.card (O ⧸ I17N2) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI17N2)

lemma isPrimeI17N2 : Ideal.IsPrime I17N2 := prime_ideal_of_norm_prime hp17.out _ NI17N2
def MulI17N0 : IdealMulLeCertificate' Table 
  ![![-1546, 586, -79]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![17, 0, 0], ![19, 5, 1]] where
 M := ![![![-26282, 9962, -1343], ![6735, -1803, 5399]]]
 hmul := by decide  
 g := ![![![![-805, 781, -40], ![-663, 0, 0]], ![![176, -164, 306], ![197, 0, 0]]]]
 hle2 := by decide  

def MulI17N1 : IdealMulLeCertificate' Table 
  ![![17, 0, 0], ![19, 5, 1]] ![![17, 0, 0], ![-3, 1, 0]]
  ![![17, 0, 0]] where
 M := ![![![289, 0, 0], ![-51, 17, 0]], ![![323, 85, 17], ![0, 0, 34]]]
 hmul := by decide  
 g := ![![![![17, 0, 0]], ![![-3, 1, 0]]], ![![![19, 5, 1]], ![![0, 0, 2]]]]
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

def I19N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![20, 2, 1]] i)))

def SI19N0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![20, 2, 1]] 
 ![![19, 0, 0], ![0, 19, 0], ![1, 2, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![20, 2, 1], ![51, 7, 13], ![54, -25, -3]]]
  hmulB := by decide  
  f := ![![![-19, -2, -1], ![19, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -2, 19]], ![![1, 0, 1], ![2, -1, 13], ![3, -1, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P19P0 : CertificateIrreducibleZModOfList' 19 2 2 4 [7, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 18], [0, 1]]
 g := ![![[16, 11], [17, 1], [4], [1]], ![[0, 8], [0, 18], [4], [1]]]
 h' := ![![[2, 18], [14, 12], [2, 18], [12, 2], [0, 1]], ![[0, 1], [0, 7], [0, 1], [16, 17], [2, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [11, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI19N0 : CertifiedPrimeIdeal' SI19N0 19 where
  n := 2
  hpos := by decide
  P := [7, 17, 1]
  hirr := P19P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-369, 117, -198]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, 27, -198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI19N0 : Ideal.IsPrime I19N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI19N0 B_one_repr
lemma NI19N0 : Nat.card (O ⧸ I19N0) = 361 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI19N0

def I19N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![6, 1, 0]] i)))

def SI19N1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![6, 1, 0]] 
 ![![19, 0, 0], ![6, 1, 0], ![3, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![6, 1, 0], ![2, 9, 8], ![47, -19, 3]]]
  hmulB := by decide  
  f := ![![![377, 2004, 1792], ![228, -4256, 0]], ![![116, 626, 560], ![77, -1330, 0]], ![![57, 316, 283], ![44, -672, 0]]]
  g := ![![![1, 0, 0], ![-6, 19, 0], ![-3, 0, 19]], ![![0, 1, 0], ![-4, 9, 8], ![8, -19, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI19N1 : Nat.card (O ⧸ I19N1) = 19 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI19N1)

lemma isPrimeI19N1 : Ideal.IsPrime I19N1 := prime_ideal_of_norm_prime hp19.out _ NI19N1
def MulI19N0 : IdealMulLeCertificate' Table 
  ![![19, 0, 0], ![20, 2, 1]] ![![19, 0, 0], ![6, 1, 0]]
  ![![19, 0, 0]] where
 M := ![![![361, 0, 0], ![114, 19, 0]], ![![380, 38, 19], ![171, 19, 19]]]
 hmul := by decide  
 g := ![![![![19, 0, 0]], ![![6, 1, 0]]], ![![![20, 2, 1]], ![![9, 1, 1]]]]
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

def I23N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![4, -8, 1]] i)))

def SI23N0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![4, -8, 1]] 
 ![![23, 0, 0], ![0, 23, 0], ![4, 15, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![4, -8, 1], ![31, -39, -67], ![-416, 165, 11]]]
  hmulB := by decide  
  f := ![![![-3, 8, -1], ![23, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -15, 23]], ![![0, -1, 1], ![13, 42, -67], ![-20, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P23P0 : CertificateIrreducibleZModOfList' 23 2 2 4 [3, 3, 1] where
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

def PI23N0 : CertifiedPrimeIdeal' SI23N0 23 where
  n := 2
  hpos := by decide
  P := [3, 3, 1]
  hirr := P23P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-789, -584, -6988]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1181, 4532, -6988]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI23N0 : Ideal.IsPrime I23N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI23N0 B_one_repr
lemma NI23N0 : Nat.card (O ⧸ I23N0) = 529 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI23N0

def I23N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-2, 1, 0]] i)))

def SI23N1: IdealEqSpanCertificate' Table ![![23, 0, 0], ![-2, 1, 0]] 
 ![![23, 0, 0], ![21, 1, 0], ![12, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![-2, 1, 0], ![2, 1, 8], ![47, -19, -5]]]
  hmulB := by decide  
  f := ![![![-239, -122, -968], ![23, 2783, 0]], ![![-217, -111, -880], ![24, 2530, 0]], ![![-124, -64, -505], ![20, 1452, 0]]]
  g := ![![![1, 0, 0], ![-21, 23, 0], ![-12, 0, 23]], ![![-1, 1, 0], ![-5, 1, 8], ![22, -19, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI23N1 : Nat.card (O ⧸ I23N1) = 23 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI23N1)

lemma isPrimeI23N1 : Ideal.IsPrime I23N1 := prime_ideal_of_norm_prime hp23.out _ NI23N1
def MulI23N0 : IdealMulLeCertificate' Table 
  ![![23, 0, 0], ![4, -8, 1]] ![![23, 0, 0], ![-2, 1, 0]]
  ![![23, 0, 0]] where
 M := ![![![529, 0, 0], ![-46, 23, 0]], ![![92, -184, 23], ![23, -23, -69]]]
 hmul := by decide  
 g := ![![![![23, 0, 0]], ![![-2, 1, 0]]], ![![![4, -8, 1]], ![![1, -1, -3]]]]
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

def I29N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0]] i)))

def SI29N0: IdealEqSpanCertificate' Table ![![29, 0, 0]] 
 ![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]] where
  M :=![![![29, 0, 0], ![0, 29, 0], ![0, 0, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P29P0 : CertificateIrreducibleZModOfList' 29 3 2 4 [19, 18, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 0, 21], [10, 28, 8], [0, 1]]
 g := ![![[6, 13, 23], [4, 1], [10, 20, 28], [1]], ![[7, 15, 5, 10], [5, 4], [15, 11, 9, 11], [7, 20, 4, 10]], ![[13, 20, 10, 21], [5, 9], [15, 22, 11, 8], [8, 4, 7, 19]]]
 h' := ![![[2, 0, 21], [6, 13, 20], [13, 4, 28], [10, 11, 12], [0, 1]], ![[10, 28, 8], [12, 17, 21], [22, 18, 27], [20, 16, 16], [2, 0, 21]], ![[0, 1], [25, 28, 17], [2, 7, 3], [7, 2, 1], [10, 28, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24, 22], []]
 b := ![[], [19, 5, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI29N0 : CertifiedPrimeIdeal' SI29N0 29 where
  n := 3
  hpos := by decide
  P := [19, 18, 17, 1]
  hirr := P29P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9810236, 1724630, -13880705]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-338284, 59470, -478645]
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

def I31N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![1, -2, 1]] i)))

def SI31N0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![1, -2, 1]] 
 ![![31, 0, 0], ![0, 31, 0], ![1, 29, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![1, -2, 1], ![43, -24, -19], ![-134, 51, -10]]]
  hmulB := by decide  
  f := ![![![0, 0, 1], ![-12, 1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -29, 31]], ![![0, -1, 1], ![2, 17, -19], ![-4, 11, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P31P0 : CertificateIrreducibleZModOfList' 31 2 2 4 [16, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30], [0, 1]]
 g := ![![[9, 2], [10, 16], [26, 20], [11, 1]], ![[0, 29], [0, 15], [29, 11], [22, 30]]]
 h' := ![![[11, 30], [26, 23], [18, 4], [10, 12], [0, 1]], ![[0, 1], [0, 8], [0, 27], [18, 19], [11, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [4, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI31N0 : CertifiedPrimeIdeal' SI31N0 31 where
  n := 2
  hpos := by decide
  P := [16, 20, 1]
  hirr := P31P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3628, -1676, -1828]
  a := ![-2, -8, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![176, 1656, -1828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI31N0 : Ideal.IsPrime I31N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI31N0 B_one_repr
lemma NI31N0 : Nat.card (O ⧸ I31N0) = 961 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI31N0

def I31N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-12, 1, 0]] i)))

def SI31N1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-12, 1, 0]] 
 ![![31, 0, 0], ![19, 1, 0], ![10, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-12, 1, 0], ![2, -9, 8], ![47, -19, -15]]]
  hmulB := by decide  
  f := ![![![337, -1777, 1584], ![-155, -6138, 0]], ![![207, -1086, 968], ![-92, -3751, 0]], ![![106, -573, 511], ![-57, -1980, 0]]]
  g := ![![![1, 0, 0], ![-19, 31, 0], ![-10, 0, 31]], ![![-1, 1, 0], ![3, -9, 8], ![18, -19, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI31N1 : Nat.card (O ⧸ I31N1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI31N1)

lemma isPrimeI31N1 : Ideal.IsPrime I31N1 := prime_ideal_of_norm_prime hp31.out _ NI31N1
def MulI31N0 : IdealMulLeCertificate' Table 
  ![![31, 0, 0], ![1, -2, 1]] ![![31, 0, 0], ![-12, 1, 0]]
  ![![31, 0, 0]] where
 M := ![![![961, 0, 0], ![-372, 31, 0]], ![![31, -62, 31], ![31, 0, -31]]]
 hmul := by decide  
 g := ![![![![31, 0, 0]], ![![-12, 1, 0]]], ![![![1, -2, 1]], ![![1, 0, -1]]]]
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


lemma PB138I0_primes (p : ℕ) :
  p ∈ Set.range ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31] ↔ Nat.Prime p ∧ 1 < p ∧ p ≤ 31 := by
  rw [← List.mem_ofFn']
  convert primes_range 1 31 (by omega)

def PB138I0 : PrimesBelowBoundCertificateInterval O 1 31 138 where
  m := 11
  g := ![2, 3, 2, 2, 1, 2, 3, 2, 2, 1, 2]
  P := ![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]
  hP := PB138I0_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I2N0, I2N1]
    · exact ![I3N0, I3N0, I3N0]
    · exact ![I5N0, I5N1]
    · exact ![I7N0, I7N1]
    · exact ![I11N0]
    · exact ![I13N0, I13N1]
    · exact ![I17N0, I17N1, I17N2]
    · exact ![I19N0, I19N1]
    · exact ![I23N0, I23N1]
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
    · exact ![2, 4]
    · exact ![3, 3, 3]
    · exact ![25, 5]
    · exact ![49, 7]
    · exact ![1331]
    · exact ![169, 13]
    · exact ![17, 17, 17]
    · exact ![361, 19]
    · exact ![529, 23]
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
      exact NI3N0
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
      exact NI17N1
      exact NI17N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI31N0
      exact NI31N1
  β := ![I2N0, I2N1, I3N0, I5N0, I5N1, I7N0, I7N1, I13N1, I17N0, I17N1, I17N2, I19N1, I23N1, I31N1]
  Il := ![[I2N0, I2N1], [I3N0, I3N0, I3N0], [I5N0, I5N1], [I7N0, I7N1], [], [I13N1], [I17N0, I17N1, I17N2], [I19N1], [I23N1], [], [I31N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
