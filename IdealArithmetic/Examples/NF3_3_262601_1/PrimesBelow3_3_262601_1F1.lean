
import IdealArithmetic.Examples.NF3_3_262601_1.RI3_3_262601_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [2, 19, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 11, 28], [23, 25, 9], [0, 1]]
 g := ![![[34, 15, 21], [33, 12], [35, 1, 27], [29, 1], []], ![[28, 30, 27, 33], [10, 10], [26, 2, 31, 30], [35, 33], [5, 7]], ![[11, 27], [4, 16], [35, 28, 7, 3], [6, 10], [24, 7]]]
 h' := ![![[6, 11, 28], [24, 20, 24], [4, 33, 7], [16, 2, 8], [0, 0, 1], [0, 1]], ![[23, 25, 9], [28, 32, 13], [14, 6, 26], [14, 21, 34], [26, 23, 25], [6, 11, 28]], ![[0, 1], [3, 22], [23, 35, 4], [25, 14, 32], [0, 14, 11], [23, 25, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 29], []]
 b := ![[], [6, 8, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [2, 19, 8, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-295038, -201280, -52244]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7974, -5440, -1412]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, 1, 0]] 
 ![![41, 0, 0], ![15, 1, 0], ![3, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, 1, 0], ![0, 16, 2], ![128, 44, 14]]]
  hmulB := by decide  
  f := ![![![106, 7, 0], ![-287, 0, 0]], ![![30, 2, 0], ![-81, 0, 0]], ![![-12, -9, -1], ![33, 21, 0]]]
  g := ![![![1, 0, 0], ![-15, 41, 0], ![-3, 0, 41]], ![![0, 1, 0], ![-6, 16, 2], ![-14, 44, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-9, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-9, 1, 0]] 
 ![![41, 0, 0], ![32, 1, 0], ![5, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-9, 1, 0], ![0, -8, 2], ![128, 44, -10]]]
  hmulB := by decide  
  f := ![![![325, -36, 0], ![1476, 0, 0]], ![![262, -29, 0], ![1190, 0, 0]], ![![55, -2, -1], ![250, 21, 0]]]
  g := ![![![1, 0, 0], ![-32, 41, 0], ![-5, 0, 41]], ![![-1, 1, 0], ![6, -8, 2], ![-30, 44, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-821, -154, 48]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-821, -154, 48]] 
 ![![41, 0, 0], ![35, 1, 0], ![26, 0, 1]] where
  M :=![![![-821, -154, 48], ![6144, 1137, -356], ![-25856, -4760, 1493]]]
  hmulB := by decide  
  f := ![![![-2981, -1442, -248]], ![![-3319, -1605, -276]], ![![-5618, -2716, -467]]]
  g := ![![![81, -154, 48], ![-595, 1137, -356], ![2486, -4760, 1493]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![15, 1, 0]] ![![41, 0, 0], ![-9, 1, 0]]
  ![![-2981, -1442, -248]] where
 M := ![![![1681, 0, 0], ![-369, 41, 0]], ![![615, 41, 0], ![-135, 7, 2]]]
 hmul := by decide  
 g := ![![![![-33661, -6314, 1968]], ![![13533, 2523, -788]]], ![![![-6171, -1173, 364]], ![![2491, 469, -146]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-2981, -1442, -248]] ![![-821, -154, 48]]
  ![![41, 0, 0]] where
 M := ![![![41, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1, I41N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
    exact isPrimeI41N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-547, -16, 14]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-547, -16, 14]] 
 ![![43, 0, 0], ![2, 1, 0], ![40, 0, 1]] where
  M :=![![![-547, -16, 14], ![1792, 53, -46], ![-3840, -116, 99]]]
  hmulB := by decide  
  f := ![![![-89, -40, -6]], ![![-22, -11, -2]], ![![-184, -84, -13]]]
  g := ![![![-25, -16, 14], ![82, 53, -46], ![-176, -116, 99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-1, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-1, 1, 0]] 
 ![![43, 0, 0], ![42, 1, 0], ![0, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-1, 1, 0], ![0, 0, 2], ![128, 44, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 22, 0]]]
  g := ![![![1, 0, 0], ![-42, 43, 0], ![0, 0, 43]], ![![-1, 1, 0], ![0, 0, 2], ![-40, 44, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-547, -16, 14]] ![![43, 0, 0], ![-1, 1, 0]]
  ![![43, 0, 0], ![-44, 1, 1]] where
 M := ![![![-23521, -688, 602], ![2339, 69, -60]]]
 hmul := by decide  
 g := ![![![![-239, -23, 7], ![301, 0, 0]], ![![37, 2, -1], ![-17, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-44, 1, 1]] ![![43, 0, 0], ![-1, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-43, 43, 0]], ![![-1892, 43, 43], ![172, 0, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-1, 1, 0]]], ![![![-44, 1, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N1, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N1
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [32, 39, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 6, 36], [24, 40, 11], [0, 1]]
 g := ![![[0, 42, 18], [37, 21, 4], [6, 7, 42], [20, 24, 1], []], ![[11, 39, 12, 8], [11, 36, 34, 4], [8, 44, 0, 36], [38, 13, 39, 25], [46, 27]], ![[32, 5, 10, 5], [44, 29, 32, 39], [14, 2, 0, 23], [4, 11, 41, 20], [24, 27]]]
 h' := ![![[0, 6, 36], [38, 16, 26], [43, 7, 45], [18, 3, 29], [0, 0, 1], [0, 1]], ![[24, 40, 11], [24, 31, 18], [26, 0, 31], [6, 16, 46], [32, 21, 40], [0, 6, 36]], ![[0, 1], [36, 0, 3], [31, 40, 18], [21, 28, 19], [43, 26, 6], [24, 40, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 17], []]
 b := ![[], [44, 9, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [32, 39, 23, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![230159, 352265, 135924]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4897, 7495, 2892]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 103823 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def PBC47 : ContainsPrimesAboveP 47 ![I47N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![47, 0, 0]]) timesTableT_eq_Table B_one_repr 47 (by decide) 𝕀

instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-50, 13, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-50, 13, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![3, 13, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-50, 13, 1], ![128, 7, 25], ![1536, 614, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -13, 53]], ![![-1, 0, 1], ![1, -6, 25], ![30, 16, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [21, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 52], [0, 1]]
 g := ![![[44, 28], [13], [40, 1], [7], [30, 1]], ![[36, 25], [13], [17, 52], [7], [7, 52]]]
 h' := ![![[30, 52], [3, 44], [8, 38], [48, 52], [6, 31], [0, 1]], ![[0, 1], [51, 9], [35, 15], [18, 1], [35, 22], [30, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [9, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [21, 23, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2517, 42, 150]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![39, -36, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-25, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-25, 1, 0]] 
 ![![53, 0, 0], ![28, 1, 0], ![18, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-25, 1, 0], ![0, -24, 2], ![128, 44, -26]]]
  hmulB := by decide  
  f := ![![![976, -39, 0], ![2067, 0, 0]], ![![526, -21, 0], ![1114, 0, 0]], ![![356, -2, -1], ![754, 27, 0]]]
  g := ![![![1, 0, 0], ![-28, 53, 0], ![-18, 0, 53]], ![![-1, 1, 0], ![12, -24, 2], ![-12, 44, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-50, 13, 1]] ![![53, 0, 0], ![-25, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1325, 53, 0]], ![![-2650, 689, 53], ![1378, -318, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-25, 1, 0]]], ![![![-50, 13, 1]], ![![26, -6, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [42, 56, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 40, 2], [21, 18, 57], [0, 1]]
 g := ![![[4, 25, 29], [28, 31, 1], [22, 28], [32, 40, 15], [1]], ![[0, 40, 13, 50], [17, 44, 42, 14], [7, 15], [51, 4, 11, 37], [24, 3, 12, 8]], ![[56, 14, 14, 4], [32, 58, 0, 26], [51, 5], [29, 24, 49, 21], [47, 42, 35, 51]]]
 h' := ![![[9, 40, 2], [4, 47, 18], [12, 30, 1], [13, 3, 21], [17, 3, 30], [0, 1]], ![[21, 18, 57], [9, 32, 5], [49, 55, 19], [44, 29, 30], [16, 49, 15], [9, 40, 2]], ![[0, 1], [17, 39, 36], [11, 33, 39], [41, 27, 8], [30, 7, 14], [21, 18, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 40], []]
 b := ![[], [27, 25, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [42, 56, 29, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-830720, -698088, -208034]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14080, -11832, -3526]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![10, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![10, 1, 0]] 
 ![![61, 0, 0], ![10, 1, 0], ![6, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![10, 1, 0], ![0, 11, 2], ![128, 44, 9]]]
  hmulB := by decide  
  f := ![![![391, 39, 0], ![-2379, 0, 0]], ![![50, 5, 0], ![-304, 0, 0]], ![![26, -3, -1], ![-158, 31, 0]]]
  g := ![![![1, 0, 0], ![-10, 61, 0], ![-6, 0, 61]], ![![0, 1, 0], ![-2, 11, 2], ![-6, 44, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![16, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![16, 1, 0]] 
 ![![61, 0, 0], ![16, 1, 0], ![47, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![16, 1, 0], ![0, 17, 2], ![128, 44, 15]]]
  hmulB := by decide  
  f := ![![![545, 34, 0], ![-2074, 0, 0]], ![![144, 9, 0], ![-548, 0, 0]], ![![411, 17, -1], ![-1564, 31, 0]]]
  g := ![![![1, 0, 0], ![-16, 61, 0], ![-47, 0, 61]], ![![0, 1, 0], ![-6, 17, 2], ![-21, 44, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![939, 172, -54]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![939, 172, -54]] 
 ![![61, 0, 0], ![35, 1, 0], ![41, 0, 1]] where
  M :=![![![939, 172, -54], ![-6912, -1265, 398], ![28928, 5300, -1663]]]
  hmulB := by decide  
  f := ![![![-5705, -164, 146]], ![![-2967, -85, 76]], ![![-4485, -128, 115]]]
  g := ![![![-47, 172, -54], ![345, -1265, 398], ![-1449, 5300, -1663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![10, 1, 0]] ![![61, 0, 0], ![16, 1, 0]]
  ![![-8127, -1490, 468]] where
 M := ![![![3721, 0, 0], ![976, 61, 0]], ![![610, 61, 0], ![160, 27, 2]]]
 hmul := by decide  
 g := ![![![![15433, 7198, 1220]], ![![6608, 3139, 536]]], ![![![5090, 2431, 416]], ![![2208, 1061, 182]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![-8127, -1490, 468]] ![![939, 172, -54]]
  ![![61, 0, 0]] where
 M := ![![![16205931, 2967406, -932446]]]
 hmul := by decide  
 g := ![![![![265671, 48646, -15286]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N1, I61N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N1
    exact isPrimeI61N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
instance hp67 : Fact (Nat.Prime 67) := {out := by norm_num}

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-20, 4, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-20, 4, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![47, 4, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-20, 4, 1], ![128, 28, 7], ![384, 218, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -4, 67]], ![![-1, 0, 1], ![-3, 0, 7], ![-9, 2, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [48, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 66], [0, 1]]
 g := ![![[57, 6], [31, 26], [14], [49], [54], [1]], ![[56, 61], [49, 41], [14], [49], [54], [1]]]
 h' := ![![[11, 66], [53, 41], [12, 48], [58, 58], [47, 7], [19, 11], [0, 1]], ![[0, 1], [35, 26], [4, 19], [26, 9], [57, 60], [6, 56], [11, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [14, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [48, 56, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![432, 798, 233]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-157, -2, 233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-7, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-7, 1, 0]] 
 ![![67, 0, 0], ![60, 1, 0], ![46, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-7, 1, 0], ![0, -6, 2], ![128, 44, -8]]]
  hmulB := by decide  
  f := ![![![365, -52, 0], ![3484, 0, 0]], ![![330, -47, 0], ![3150, 0, 0]], ![![246, -32, -1], ![2348, 34, 0]]]
  g := ![![![1, 0, 0], ![-60, 67, 0], ![-46, 0, 67]], ![![-1, 1, 0], ![4, -6, 2], ![-32, 44, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-20, 4, 1]] ![![67, 0, 0], ![-7, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-469, 67, 0]], ![![-1340, 268, 67], ![268, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-7, 1, 0]]], ![![![-20, 4, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4333, -2094, -360]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-4333, -2094, -360]] 
 ![![71, 0, 0], ![22, 1, 0], ![31, 0, 1]] where
  M :=![![![-4333, -2094, -360], ![-46080, -22267, -3828], ![-221952, -107256, -18439]]]
  hmulB := by decide  
  f := ![![![5245, 894, -288]], ![![1106, 185, -60]], ![![4421, 774, -247]]]
  g := ![![![745, -2094, -360], ![7922, -22267, -3828], ![38159, -107256, -18439]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-20, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-20, 1, 0]] 
 ![![71, 0, 0], ![51, 1, 0], ![23, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-20, 1, 0], ![0, -19, 2], ![128, 44, -21]]]
  hmulB := by decide  
  f := ![![![761, -38, 0], ![2698, 0, 0]], ![![541, -27, 0], ![1918, 0, 0]], ![![273, -4, -1], ![968, 36, 0]]]
  g := ![![![1, 0, 0], ![-51, 71, 0], ![-23, 0, 71]], ![![-1, 1, 0], ![13, -19, 2], ![-23, 44, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-2, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-2, 1, 0]] 
 ![![71, 0, 0], ![69, 1, 0], ![70, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-2, 1, 0], ![0, -1, 2], ![128, 44, -3]]]
  hmulB := by decide  
  f := ![![![3, 34, -70], ![71, 2485, 0]], ![![1, 34, -68], ![1, 2414, 0]], ![![2, 34, -69], ![36, 2450, 0]]]
  g := ![![![1, 0, 0], ![-69, 71, 0], ![-70, 0, 71]], ![![-1, 1, 0], ![-1, -1, 2], ![-38, 44, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-4333, -2094, -360]] ![![71, 0, 0], ![-20, 1, 0]]
  ![![71, 0, 0], ![-7, -34, 1]] where
 M := ![![![-307643, -148674, -25560], ![40580, 19613, 3372]]]
 hmul := by decide  
 g := ![![![![-4214, -1516, -377], ![1207, 0, 0]], ![![561, 225, 49], ![-107, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-7, -34, 1]] ![![71, 0, 0], ![-2, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-142, 71, 0]], ![![-497, -2414, 71], ![142, 71, -71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-2, 1, 0]]], ![![![-7, -34, 1]], ![![2, 1, -1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N1, I71N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N1
    exact isPrimeI71N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2681, 1294, 222]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![2681, 1294, 222]] 
 ![![73, 0, 0], ![0, 73, 0], ![42, 42, 1]] where
  M :=![![![2681, 1294, 222], ![28416, 13743, 2366], ![137216, 66260, 11377]]]
  hmulB := by decide  
  f := ![![![5713, 166, -146]], ![![-18688, -545, 478]], ![![-6918, -202, 177]]]
  g := ![![![-91, -110, 222], ![-972, -1173, 2366], ![-4666, -5638, 11377]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [34, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 72], [0, 1]]
 g := ![![[13, 2], [18], [41], [68, 48], [16], [1]], ![[5, 71], [18], [41], [22, 25], [16], [1]]]
 h' := ![![[69, 72], [51, 41], [58, 23], [24, 48], [28, 62], [39, 69], [0, 1]], ![[0, 1], [33, 32], [39, 50], [51, 25], [72, 11], [55, 4], [69, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [56, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [34, 4, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51111, 56002, 19931]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10767, -10700, 19931]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5713, -166, 146]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-5713, -166, 146]] 
 ![![73, 0, 0], ![63, 1, 0], ![28, 0, 1]] where
  M :=![![![-5713, -166, 146], ![18688, 545, -478], ![-39936, -1172, 1023]]]
  hmulB := by decide  
  f := ![![![-2681, -1294, -222]], ![![-2703, -1305, -224]], ![![-2908, -1404, -241]]]
  g := ![![![9, -166, 146], ![-31, 545, -478], ![72, -1172, 1023]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![2681, 1294, 222]] ![![-5713, -166, 146]]
  ![![73, 0, 0]] where
 M := ![![![-73, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [51, 2, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 28, 60], [22, 50, 19], [0, 1]]
 g := ![![[70, 16, 49], [51, 37, 8], [11, 44, 5], [41, 31, 76], [7, 1], []], ![[39, 51, 15, 57], [6, 22, 11, 53], [39, 55, 43, 33], [3, 76, 6, 43], [29, 51], [41, 45]], ![[67, 35, 44, 64], [29, 37, 5, 38], [16, 8, 31, 72], [76, 22, 75, 76], [69, 73], [3, 45]]]
 h' := ![![[64, 28, 60], [6, 50, 7], [71, 51, 61], [42, 18, 20], [38, 14, 47], [0, 0, 1], [0, 1]], ![[22, 50, 19], [19, 53, 32], [30, 5, 27], [56, 75, 26], [53, 4, 30], [30, 22, 50], [64, 28, 60]], ![[0, 1], [26, 55, 40], [54, 23, 70], [27, 65, 33], [24, 61, 2], [15, 57, 28], [22, 50, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 30], []]
 b := ![[], [39, 40, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [51, 2, 72, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61304, 32390, 6399]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![776, 410, 81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 493039 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def PBC79 : ContainsPrimesAboveP 79 ![I79N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![79, 0, 0]]) timesTableT_eq_Table B_one_repr 79 (by decide) 𝕀



lemma PB114I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB114I1 : PrimesBelowBoundCertificateInterval O 31 79 114 where
  m := 11
  g := ![1, 3, 3, 1, 2, 1, 3, 2, 3, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB114I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
    · exact ![I79N0]
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
    · exact ![41, 41, 41]
    · exact ![43, 43, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
    · exact ![493039]
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
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
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
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
      exact NI71N2
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N0, I41N1, I41N2, I43N0, I43N1, I53N1, I61N0, I61N1, I61N2, I67N1, I71N0, I71N1, I71N2, I73N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N0, I43N1, I43N1], [], [I53N1], [], [I61N0, I61N1, I61N2], [I67N1], [I71N0, I71N1, I71N2], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
