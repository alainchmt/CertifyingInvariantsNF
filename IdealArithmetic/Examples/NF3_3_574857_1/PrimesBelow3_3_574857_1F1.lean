
import IdealArithmetic.Examples.NF3_3_574857_1.RI3_3_574857_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [28, 20, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 13, 15], [32, 23, 22], [0, 1]]
 g := ![![[25, 32, 34], [30, 16], [19, 29, 34], [35, 1], []], ![[8, 23, 35, 22], [34, 11], [22, 28, 22, 24], [31, 11], [14, 3]], ![[20, 29, 8, 17], [36, 28], [34, 2, 13, 24], [31, 21], [7, 3]]]
 h' := ![![[3, 13, 15], [22, 20, 21], [23, 20, 33], [19, 12, 21], [0, 0, 1], [0, 1]], ![[32, 23, 22], [31, 26, 6], [24, 35, 23], [4, 33, 34], [24, 10, 23], [3, 13, 15]], ![[0, 1], [31, 28, 10], [15, 19, 18], [31, 29, 19], [14, 27, 13], [32, 23, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 15], []]
 b := ![[], [2, 10, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [28, 20, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86247, -47323, -6327]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2331, -1279, -171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 50653 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def PBC37 : ContainsPrimesAboveP 37 ![I37N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![37, 0, 0]]) timesTableT_eq_Table B_one_repr 37 (by decide) 𝕀

instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [18, 28, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 28, 11], [32, 12, 30], [0, 1]]
 g := ![![[2, 11, 36], [23, 4], [38, 33], [29, 37, 1], []], ![[26, 2, 32, 7], [20, 4], [20, 1], [35, 39, 37, 26], [9, 39]], ![[32, 16, 9, 38], [], [30, 31], [9, 26, 16, 27], [31, 39]]]
 h' := ![![[5, 28, 11], [35, 11, 35], [11, 20, 2], [11, 39, 19], [0, 0, 1], [0, 1]], ![[32, 12, 30], [10, 6, 8], [1, 32, 39], [22, 12, 1], [27, 23, 12], [5, 28, 11]], ![[0, 1], [10, 24, 39], [25, 30], [27, 31, 21], [15, 18, 28], [32, 12, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 24], []]
 b := ![[], [8, 11, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [18, 28, 4, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![286426, 525989, 144361]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6986, 12829, 3521]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 68921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def PBC41 : ContainsPrimesAboveP 41 ![I41N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![41, 0, 0]]) timesTableT_eq_Table B_one_repr 41 (by decide) 𝕀

instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2425, 124, -38]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![2425, 124, -38]] 
 ![![43, 0, 0], ![0, 43, 0], ![12, 42, 1]] where
  M :=![![![2425, 124, -38], ![-7714, -425, 124], ![25172, 1586, -425]]]
  hmulB := by decide  
  f := ![![![-373, -176, -18]], ![![-3654, -1723, -176]], ![![-4504, -2124, -217]]]
  g := ![![![67, 40, -38], ![-214, -131, 124], ![704, 452, -425]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [10, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 42], [0, 1]]
 g := ![![[10, 13], [15, 41], [1], [30, 24], [1]], ![[0, 30], [0, 2], [1], [38, 19], [1]]]
 h' := ![![[29, 42], [22, 20], [34, 27], [1, 42], [33, 29], [0, 1]], ![[0, 1], [0, 23], [0, 16], [15, 1], [14, 14], [29, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [17, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [10, 14, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1193, 1393, 628]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-203, -581, 628]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![373, 176, 18]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![373, 176, 18]] 
 ![![43, 0, 0], ![1, 1, 0], ![42, 0, 1]] where
  M :=![![![373, 176, 18], ![3654, 1723, 176], ![35728, 16854, 1723]]]
  hmulB := by decide  
  f := ![![![-2425, -124, 38]], ![![123, 7, -2]], ![![-2954, -158, 47]]]
  g := ![![![-13, 176, 18], ![-127, 1723, 176], ![-1244, 16854, 1723]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![2425, 124, -38]] ![![373, 176, 18]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0)

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![47, 0, 0], ![5, 1, 0], ![22, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 1], ![203, 75, 5]]]
  hmulB := by decide  
  f := ![![![50, 5, -1]], ![![1, 0, 0]], ![![45, 6, -1]]]
  g := ![![![0, 1, 0], ![-1, 5, 1], ![-6, 75, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N0 : Nat.card (O ⧸ I47N0) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N0)

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := prime_ideal_of_norm_prime hp47.out _ NI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-10, 1, 0]] 
 ![![47, 0, 0], ![37, 1, 0], ![41, 0, 1]] where
  M :=![![![-10, 1, 0], ![0, -10, 1], ![203, 75, -10]]]
  hmulB := by decide  
  f := ![![![-25, -10, -1]], ![![-24, -10, -1]], ![![-65, -29, -3]]]
  g := ![![![-1, 1, 0], ![7, -10, 1], ![-46, 75, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![5, 1, 0]] ![![5, 1, 0]]
  ![![25, 10, 1]] where
 M := ![![![25, 10, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI47N1 : IdealMulLeCertificate' Table 
  ![![25, 10, 1]] ![![-10, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0 ⊙ MulI47N1)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 26, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![71, 26, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![18, 26, 1]] where
  M :=![![![71, 26, 1], ![203, 146, 26], ![5278, 2153, 146]]]
  hmulB := by decide  
  f := ![![![-654, -31, 10]], ![![2030, 96, -31]], ![![655, 31, -10]]]
  g := ![![![1, 0, 1], ![-5, -10, 26], ![50, -31, 146]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [33, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 52], [0, 1]]
 g := ![![[17, 42], [43], [7, 25], [40], [22, 1]], ![[40, 11], [43], [27, 28], [40], [44, 52]]]
 h' := ![![[22, 52], [2, 25], [34, 34], [49, 48], [16, 27], [0, 1]], ![[0, 1], [22, 28], [40, 19], [45, 5], [27, 26], [22, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [10, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [33, 31, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![439, 322, 45]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -16, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![654, 31, -10]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![654, 31, -10]] 
 ![![53, 0, 0], ![27, 1, 0], ![13, 0, 1]] where
  M :=![![![654, 31, -10], ![-2030, -96, 31], ![6293, 295, -96]]]
  hmulB := by decide  
  f := ![![![-71, -26, -1]], ![![-40, -16, -1]], ![![-117, -47, -3]]]
  g := ![![![-1, 31, -10], ![3, -96, 31], ![-8, 295, -96]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![71, 26, 1]] ![![654, 31, -10]]
  ![![53, 0, 0]] where
 M := ![![![-53, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0]] 
 ![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [1, 27, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 56, 8], [43, 2, 51], [0, 1]]
 g := ![![[8, 23, 5], [0, 10, 17], [46, 51], [42, 39, 45], [1]], ![[45, 23, 51, 8], [53, 45, 58, 43], [39, 17], [57, 47, 18, 18], [3, 8, 57, 40]], ![[14, 44, 20, 21], [38, 42, 11, 19], [38, 48], [30, 3, 44, 21], [14, 53, 46, 19]]]
 h' := ![![[51, 56, 8], [0, 39, 51], [7, 41, 31], [17, 8, 13], [58, 32, 35], [0, 1]], ![[43, 2, 51], [15, 8, 1], [27, 49, 36], [19, 31, 31], [16, 43, 31], [51, 56, 8]], ![[0, 1], [6, 12, 7], [22, 28, 51], [1, 20, 15], [20, 43, 52], [43, 2, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 30], []]
 b := ![[], [9, 17, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [1, 27, 24, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2509742, 1169262, 110271]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42538, 19818, 1869]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 205379 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def PBC59 : ContainsPrimesAboveP 59 ![I59N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![59, 0, 0]]) timesTableT_eq_Table B_one_repr 59 (by decide) 𝕀

instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -2, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-71, -2, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![51, 59, 1]] where
  M :=![![![-71, -2, 1], ![203, 4, -2], ![-406, 53, 4]]]
  hmulB := by decide  
  f := ![![![2, 1, 0]], ![![0, 2, 1]], ![![5, 4, 1]]]
  g := ![![![-2, -1, 1], ![5, 2, -2], ![-10, -3, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [28, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 60], [0, 1]]
 g := ![![[53, 13], [12], [17, 42], [22, 36], [41, 1]], ![[37, 48], [12], [31, 19], [34, 25], [21, 60]]]
 h' := ![![[41, 60], [52, 47], [12, 45], [55, 15], [11, 6], [0, 1]], ![[0, 1], [27, 14], [27, 16], [60, 46], [13, 55], [41, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [55, 36]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [28, 20, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1209, -193, 66]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75, -67, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![61, 0, 0], ![2, 1, 0], ![57, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![203, 75, 2]]]
  hmulB := by decide  
  f := ![![![-71, -2, 1]], ![![1, 0, 0]], ![![-73, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 75, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-71, -2, 1]] ![![2, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![61, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0]] 
 ![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [30, 35, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 29, 7], [33, 37, 60], [0, 1]]
 g := ![![[38, 42, 4], [17, 41, 60], [39, 65], [35, 55], [32, 1], []], ![[28, 15, 16, 12], [42, 57, 49, 48], [9, 55], [64, 1], [57, 29], [31, 49]], ![[8, 38, 29, 25], [34, 40, 51, 22], [0, 23], [15, 24], [45, 37], [45, 49]]]
 h' := ![![[66, 29, 7], [26, 55, 65], [65, 48, 23], [37, 21, 20], [45, 56, 51], [0, 0, 1], [0, 1]], ![[33, 37, 60], [20, 54, 43], [23, 52, 48], [62, 6, 16], [46, 16, 1], [9, 0, 37], [66, 29, 7]], ![[0, 1], [18, 25, 26], [1, 34, 63], [66, 40, 31], [39, 62, 15], [7, 0, 29], [33, 37, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 59], []]
 b := ![[], [43, 55, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [30, 35, 35, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![541025, 351348, 58491]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8075, 5244, 873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 300763 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def PBC67 : ContainsPrimesAboveP 67 ![I67N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![67, 0, 0]]) timesTableT_eq_Table B_one_repr 67 (by decide) 𝕀

instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-50, -14, -1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-50, -14, -1]] 
 ![![71, 0, 0], ![0, 71, 0], ![50, 14, 1]] where
  M :=![![![-50, -14, -1], ![-203, -125, -14], ![-2842, -1253, -125]]]
  hmulB := by decide  
  f := ![![![27, 7, -1]], ![![-203, -48, 7]], ![![-1, 0, 0]]]
  g := ![![![0, 0, -1], ![7, 1, -14], ![48, 7, -125]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [61, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 70], [0, 1]]
 g := ![![[62, 4], [64, 2], [12, 64], [9], [6], [1]], ![[57, 67], [26, 69], [3, 7], [9], [6], [1]]]
 h' := ![![[52, 70], [1, 69], [49, 59], [59, 8], [18, 3], [10, 52], [0, 1]], ![[0, 1], [39, 2], [64, 12], [49, 63], [32, 68], [16, 19], [52, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [32, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [61, 19, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8017, -2418, 446]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-427, -122, 446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-27, -7, 1]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-27, -7, 1]] 
 ![![71, 0, 0], ![57, 1, 0], ![17, 0, 1]] where
  M :=![![![-27, -7, 1], ![203, 48, -7], ![-1421, -322, 48]]]
  hmulB := by decide  
  f := ![![![50, 14, 1]], ![![43, 13, 1]], ![![52, 21, 2]]]
  g := ![![![5, -7, 1], ![-34, 48, -7], ![227, -322, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-50, -14, -1]] ![![-27, -7, 1]]
  ![![71, 0, 0]] where
 M := ![![![-71, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0]] 
 ![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [40, 54, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 3, 31], [31, 69, 42], [0, 1]]
 g := ![![[7, 6, 50], [71, 70], [69, 18], [0, 37, 24], [43, 1], []], ![[2, 37, 7, 20], [13, 49], [2, 54], [25, 7, 54, 10], [32, 16], [45, 12]], ![[3, 8, 16, 58], [35, 65], [68, 46], [21, 33, 19, 56], [41, 9], [34, 12]]]
 h' := ![![[12, 3, 31], [57, 59, 14], [14, 7, 56], [0, 55, 50], [32, 47, 43], [0, 0, 1], [0, 1]], ![[31, 69, 42], [65, 11, 21], [72, 14, 66], [58, 31, 45], [52, 17, 44], [23, 9, 69], [12, 3, 31]], ![[0, 1], [23, 3, 38], [6, 52, 24], [5, 60, 51], [27, 9, 59], [39, 64, 3], [31, 69, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 34], []]
 b := ![[], [23, 40, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [40, 54, 30, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-24674, 16425, 11826]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-338, 225, 162]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 389017 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def PBC73 : ContainsPrimesAboveP 73 ![I73N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![73, 0, 0]]) timesTableT_eq_Table B_one_repr 73 (by decide) 𝕀

instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-131, -26, 4]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![-131, -26, 4]] 
 ![![79, 0, 0], ![0, 79, 0], ![66, 33, 1]] where
  M :=![![![-131, -26, 4], ![812, 169, -26], ![-5278, -1138, 169]]]
  hmulB := by decide  
  f := ![![![-13, -2, 0]], ![![0, -13, -2]], ![![-16, -9, -1]]]
  g := ![![![-5, -2, 4], ![32, 13, -26], ![-208, -85, 169]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [63, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 78], [0, 1]]
 g := ![![[72, 64], [11, 19], [4, 16], [23, 46], [62], [1]], ![[14, 15], [16, 60], [29, 63], [6, 33], [62], [1]]]
 h' := ![![[46, 78], [18, 8], [64, 63], [52, 75], [63, 58], [16, 46], [0, 1]], ![[0, 1], [70, 71], [39, 16], [26, 4], [45, 21], [78, 33], [46, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [43, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [63, 33, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1721, 663, 56]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -15, 56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 2, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![13, 2, 0]] 
 ![![79, 0, 0], ![46, 1, 0], ![17, 0, 1]] where
  M :=![![![13, 2, 0], ![0, 13, 2], ![406, 150, 13]]]
  hmulB := by decide  
  f := ![![![131, 26, -4]], ![![66, 13, -2]], ![![95, 20, -3]]]
  g := ![![![-1, 2, 0], ![-8, 13, 2], ![-85, 150, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![-131, -26, 4]] ![![13, 2, 0]]
  ![![79, 0, 0]] where
 M := ![![![-79, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0)


lemma PB169I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB169I1 : PrimesBelowBoundCertificateInterval O 31 79 169 where
  m := 11
  g := ![1, 1, 2, 3, 2, 1, 2, 1, 2, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB169I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
    · exact ![I79N0, I79N1]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC37
    · exact PBC41
    · exact PBC43
    · exact PBC47
    · exact PBC53
    · exact PBC59
    · exact PBC61
    · exact PBC67
    · exact PBC71
    · exact PBC73
    · exact PBC79
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![47, 47, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
    · exact ![389017]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N1, I47N0, I47N1, I53N1, I61N1, I71N1, I79N1]
  Il := ![[], [], [I43N1], [I47N0, I47N0, I47N1], [I53N1], [], [I61N1], [], [I71N1], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
