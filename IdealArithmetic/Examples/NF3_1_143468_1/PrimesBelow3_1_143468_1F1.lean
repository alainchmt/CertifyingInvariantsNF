
import IdealArithmetic.Examples.NF3_1_143468_1.RI3_1_143468_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-133, 13, 5]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![-133, 13, 5]] 
 ![![37, 0, 0], ![0, 37, 0], ![3, 10, 1]] where
  M :=![![![-133, 13, 5], ![-575, 32, 18], ![-2070, 19, 50]]]
  hmulB := by decide  
  f := ![![![-34, 15, -2]], ![![230, -100, 13]], ![![19, -8, 1]]]
  g := ![![![-4, -1, 5], ![-17, -4, 18], ![-60, -13, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [19, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 36], [0, 1]]
 g := ![![[20, 33], [34], [15, 7], [26], [1]], ![[23, 4], [34], [19, 30], [26], [1]]]
 h' := ![![[27, 36], [30, 12], [11, 16], [15, 9], [18, 27], [0, 1]], ![[0, 1], [21, 25], [36, 21], [36, 28], [7, 10], [27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6]]
 b := ![[], [15, 3]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [19, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-326, -26, 27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11, -8, 27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![34, -15, 2]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![34, -15, 2]] 
 ![![37, 0, 0], ![26, 1, 0], ![27, 0, 1]] where
  M :=![![![34, -15, 2], ![-230, 100, -13], ![1495, -659, 87]]]
  hmulB := by decide  
  f := ![![![133, -13, -5]], ![![109, -10, -4]], ![![153, -10, -5]]]
  g := ![![![10, -15, 2], ![-67, 100, -13], ![440, -659, 87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![-133, 13, 5]] ![![34, -15, 2]]
  ![![37, 0, 0]] where
 M := ![![![-37, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![19, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![19, 1, 0]] 
 ![![41, 0, 0], ![19, 1, 0], ![8, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![19, 1, 0], ![0, 19, 1], ![-115, 33, 20]]]
  hmulB := by decide  
  f := ![![![172, 9, 0], ![-369, 0, 0]], ![![76, 4, 0], ![-163, 0, 0]], ![![28, 1, 0], ![-60, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 41, 0], ![-8, 0, 41]], ![![0, 1, 0], ![-9, 19, 1], ![-22, 33, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-19, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-19, 1, 0]] 
 ![![41, 0, 0], ![22, 1, 0], ![8, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-19, 1, 0], ![0, -19, 1], ![-115, 33, -18]]]
  hmulB := by decide  
  f := ![![![400, -21, 0], ![861, 0, 0]], ![![210, -11, 0], ![452, 0, 0]], ![![104, -5, 0], ![224, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 41, 0], ![-8, 0, 41]], ![![-1, 1, 0], ![10, -19, 1], ![-17, 33, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -11, -1]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-29, -11, -1]] 
 ![![41, 0, 0], ![40, 1, 0], ![40, 0, 1]] where
  M :=![![![-29, -11, -1], ![115, -62, -12], ![1380, -281, -74]]]
  hmulB := by decide  
  f := ![![![1216, -533, 70]], ![![990, -434, 57]], ![![2485, -1089, 143]]]
  g := ![![![11, -11, -1], ![75, -62, -12], ![380, -281, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![19, 1, 0]] ![![41, 0, 0], ![-19, 1, 0]]
  ![![-1216, 533, -70]] where
 M := ![![![1681, 0, 0], ![-779, 41, 0]], ![![779, 41, 0], ![-361, 0, 1]]]
 hmul := by decide  
 g := ![![![![1189, 451, 41]], ![![-666, -147, -7]]], ![![![436, 271, 31]], ![![-289, -90, -7]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-1216, 533, -70]] ![![-29, -11, -1]]
  ![![41, 0, 0]] where
 M := ![![![-41, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [4, 12, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 15, 34], [28, 27, 9], [0, 1]]
 g := ![![[1, 14, 41], [29, 33, 4], [], [5, 24, 1], []], ![[15, 36, 25, 7], [32, 39, 31, 27], [6, 10], [11, 24, 30, 18], [40, 38]], ![[18, 41, 8, 1], [20, 39, 20, 4], [42, 10], [40, 19, 16, 4], [22, 38]]]
 h' := ![![[39, 15, 34], [13, 33, 27], [13, 5, 41], [23, 16], [0, 0, 1], [0, 1]], ![[28, 27, 9], [35, 14, 2], [23, 31, 30], [2, 25, 28], [28, 22, 27], [39, 15, 34]], ![[0, 1], [35, 39, 14], [8, 7, 15], [41, 2, 15], [8, 21, 15], [28, 27, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15], []]
 b := ![[], [4, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [4, 12, 19, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![362490, -224030, 34400]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8430, -5210, 800]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 79507 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def PBC43 : ContainsPrimesAboveP 43 ![I43N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![43, 0, 0]]) timesTableT_eq_Table B_one_repr 43 (by decide) 𝕀

instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-36, 21, 4]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-36, 21, 4]] 
 ![![47, 0, 0], ![0, 47, 0], ![38, 17, 1]] where
  M :=![![![-36, 21, 4], ![-460, 96, 25], ![-2875, 365, 121]]]
  hmulB := by decide  
  f := ![![![53, -23, 3]], ![![-345, 152, -20]], ![![-33, 15, -2]]]
  g := ![![![-4, -1, 4], ![-30, -7, 25], ![-159, -36, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [29, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 46], [0, 1]]
 g := ![![[1, 32], [5, 3], [5, 37], [41, 42], [1]], ![[13, 15], [12, 44], [13, 10], [45, 5], [1]]]
 h' := ![![[18, 46], [43, 19], [43, 12], [33, 32], [18, 18], [0, 1]], ![[0, 1], [9, 28], [24, 35], [45, 15], [13, 29], [18, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [15, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [29, 29, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2384, -247, 132]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-56, -53, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-53, 23, -3]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-53, 23, -3]] 
 ![![47, 0, 0], ![29, 1, 0], ![5, 0, 1]] where
  M :=![![![-53, 23, -3], ![345, -152, 20], ![-2300, 1005, -132]]]
  hmulB := by decide  
  f := ![![![36, -21, -4]], ![![32, -15, -3]], ![![65, -10, -3]]]
  g := ![![![-15, 23, -3], ![99, -152, 20], ![-655, 1005, -132]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-36, 21, 4]] ![![-53, 23, -3]]
  ![![47, 0, 0]] where
 M := ![![![-47, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC47 : ContainsPrimesAboveP 47 ![I47N0, I47N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI47N0
    exact isPrimeI47N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 47 (by decide) (𝕀 ⊙ MulI47N0)
instance hp53 : Fact (Nat.Prime 53) := {out := by norm_num}

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31, 1, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-31, 1, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![22, 1, 1]] where
  M :=![![![-31, 1, 1], ![-115, 2, 2], ![-230, -49, 4]]]
  hmulB := by decide  
  f := ![![![2, -1, 0]], ![![0, 2, -1]], ![![3, -1, 0]]]
  g := ![![![-1, 0, 1], ![-3, 0, 2], ![-6, -1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [15, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 52], [0, 1]]
 g := ![![[9, 46], [11], [1, 4], [7], [24, 1]], ![[0, 7], [11], [44, 49], [7], [48, 52]]]
 h' := ![![[24, 52], [7, 24], [38, 8], [16, 2], [11, 31], [0, 1]], ![[0, 1], [0, 29], [18, 45], [11, 51], [13, 22], [24, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [21, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [15, 29, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-300, -905, 208]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, -21, 208]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![53, 0, 0], ![51, 1, 0], ![49, 0, 1]] where
  M :=![![![-2, 1, 0], ![0, -2, 1], ![-115, 33, -1]]]
  hmulB := by decide  
  f := ![![![31, -1, -1]], ![![32, -1, -1]], ![![33, 0, -1]]]
  g := ![![![-1, 1, 0], ![1, -2, 1], ![-33, 33, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-31, 1, 1]] ![![-2, 1, 0]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [34, 5, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 15, 3], [20, 43, 56], [0, 1]]
 g := ![![[13, 12, 36], [45, 14, 17], [49, 35], [24, 10, 22], [1]], ![[8, 45, 22, 19], [24, 25, 24, 46], [11, 41], [17, 40, 16, 9], [44, 3, 44, 27]], ![[14, 48, 57, 10], [37, 32, 38, 32], [7, 48], [18, 27, 57, 47], [47, 13, 47, 32]]]
 h' := ![![[30, 15, 3], [4, 28, 6], [27, 36, 31], [10, 47, 34], [25, 54, 50], [0, 1]], ![[20, 43, 56], [42, 56, 47], [51, 36, 25], [22, 19, 10], [16, 58, 11], [30, 15, 3]], ![[0, 1], [22, 34, 6], [51, 46, 3], [42, 52, 15], [30, 6, 57], [20, 43, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 39], []]
 b := ![[], [44, 37, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [34, 5, 9, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3599, 2537, -590]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![61, 43, -10]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![6, 1, 0]] 
 ![![61, 0, 0], ![6, 1, 0], ![25, 0, 1]] where
  M :=![![![6, 1, 0], ![0, 6, 1], ![-115, 33, 7]]]
  hmulB := by decide  
  f := ![![![-9, 7, -1]], ![![1, 0, 0]], ![![-15, 8, -1]]]
  g := ![![![0, 1, 0], ![-1, 6, 1], ![-8, 33, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![27, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 20, 1], ![-115, 33, 21]]]
  hmulB := by decide  
  f := ![![![481, 24, 0], ![-1464, 0, 0]], ![![140, 7, 0], ![-426, 0, 0]], ![![207, 10, 0], ![-630, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-27, 0, 61]], ![![0, 1, 0], ![-7, 20, 1], ![-22, 33, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![3, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![0, -27, 1], ![-115, 33, -26]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![3538, 0, 0]], ![![892, -33, 0], ![2014, 0, 0]], ![![93, -3, 0], ![210, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-3, 0, 61]], ![![-1, 1, 0], ![15, -27, 1], ![-19, 33, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![6, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0], ![-2, 26, 1]] where
 M := ![![![366, 61, 0], ![120, 26, 1]]]
 hmul := by decide  
 g := ![![![![8, -25, -1], ![61, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-2, 26, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![-122, 1586, 61], ![-61, -671, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![-2, 26, 1]], ![![-1, -11, 0]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-46, 35, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-46, 35, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![21, 35, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-46, 35, 1], ![-115, -13, 36], ![-4140, 1073, 23]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -35, 67]], ![![-1, 0, 1], ![-13, -19, 36], ![-69, 4, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [3, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 66], [0, 1]]
 g := ![![[50, 56], [10, 36], [60], [65], [55], [1]], ![[25, 11], [37, 31], [60], [65], [55], [1]]]
 h' := ![![[51, 66], [37, 49], [60, 6], [21, 23], [45, 20], [64, 51], [0, 1]], ![[0, 1], [57, 18], [31, 61], [55, 44], [60, 47], [52, 16], [51, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [23, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [3, 16, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4465, 1514, 451]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-208, -213, 451]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![31, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![31, 1, 0]] 
 ![![67, 0, 0], ![31, 1, 0], ![44, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![31, 1, 0], ![0, 31, 1], ![-115, 33, 32]]]
  hmulB := by decide  
  f := ![![![342, 11, 0], ![-737, 0, 0]], ![![124, 4, 0], ![-267, 0, 0]], ![![170, 5, 0], ![-366, 1, 0]]]
  g := ![![![1, 0, 0], ![-31, 67, 0], ![-44, 0, 67]], ![![0, 1, 0], ![-15, 31, 1], ![-38, 33, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-46, 35, 1]] ![![67, 0, 0], ![31, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![2077, 67, 0]], ![![-3082, 2345, 67], ![-1541, 1072, 67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![31, 1, 0]]], ![![![-46, 35, 1]], ![![-23, 16, 1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![7, 13, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![7, 13, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![7, 13, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![7, 13, 1], ![-115, 40, 14], ![-1610, 347, 54]]]
  hmulB := by decide  
  f := ![![![-6, -13, -1], ![71, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -13, 71]], ![![0, 0, 1], ![-3, -2, 14], ![-28, -5, 54]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [12, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 70], [0, 1]]
 g := ![![[40, 6], [21, 5], [28, 49], [30], [5], [1]], ![[0, 65], [35, 66], [9, 22], [30], [5], [1]]]
 h' := ![![[17, 70], [32, 19], [19, 17], [22, 64], [13, 32], [59, 17], [0, 1]], ![[0, 1], [0, 52], [24, 54], [45, 7], [60, 39], [64, 54], [17, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [64, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [12, 54, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![534, -124, -15]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 1, -15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-14, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-14, 1, 0]] 
 ![![71, 0, 0], ![57, 1, 0], ![17, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-14, 1, 0], ![0, -14, 1], ![-115, 33, -13]]]
  hmulB := by decide  
  f := ![![![953, -68, 0], ![4828, 0, 0]], ![![771, -55, 0], ![3906, 0, 0]], ![![255, -18, 0], ![1292, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 71, 0], ![-17, 0, 71]], ![![-1, 1, 0], ![11, -14, 1], ![-25, 33, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![7, 13, 1]] ![![71, 0, 0], ![-14, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-994, 71, 0]], ![![497, 923, 71], ![-213, -142, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-14, 1, 0]]], ![![![7, 13, 1]], ![![-3, -2, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-86, -13, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![-86, -13, 0]] 
 ![![73, 0, 0], ![1, 1, 0], ![72, 0, 1]] where
  M :=![![![-86, -13, 0], ![0, -86, -13], ![1495, -429, -99]]]
  hmulB := by decide  
  f := ![![![2937, -1287, 169]], ![![-226, 99, -13]], ![![4658, -2041, 268]]]
  g := ![![![-1, -13, 0], ![14, -86, -13], ![124, -429, -99]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![17, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![17, 1, 0]] 
 ![![73, 0, 0], ![17, 1, 0], ![3, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![17, 1, 0], ![0, 17, 1], ![-115, 33, 18]]]
  hmulB := by decide  
  f := ![![![528, 31, 0], ![-2263, 0, 0]], ![![102, 6, 0], ![-437, 0, 0]], ![![4, 0, 0], ![-17, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 73, 0], ![-3, 0, 73]], ![![0, 1, 0], ![-4, 17, 1], ![-10, 33, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-19, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-19, 1, 0]] 
 ![![73, 0, 0], ![54, 1, 0], ![4, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-19, 1, 0], ![0, -19, 1], ![-115, 33, -18]]]
  hmulB := by decide  
  f := ![![![1103, -58, 0], ![4234, 0, 0]], ![![818, -43, 0], ![3140, 0, 0]], ![![62, -3, 0], ![238, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 73, 0], ![-4, 0, 73]], ![![-1, 1, 0], ![14, -19, 1], ![-25, 33, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![-86, -13, 0]] ![![73, 0, 0], ![17, 1, 0]]
  ![![73, 0, 0], ![-56, 18, 1]] where
 M := ![![![-6278, -949, 0], ![-1462, -307, -13]]]
 hmul := by decide  
 g := ![![![![-30, -31, -1], ![73, 0, 0]], ![![26, -19, -1], ![60, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-56, 18, 1]] ![![73, 0, 0], ![-19, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1387, 73, 0]], ![![-4088, 1314, 73], ![949, -365, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-19, 1, 0]]], ![![![-56, 18, 1]], ![![13, -5, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-48, -20, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-48, -20, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![31, 59, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-48, -20, 1], ![-115, -15, -19], ![2185, -742, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -59, 79]], ![![-1, -1, 1], ![6, 14, -19], ![41, 16, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [59, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 78], [0, 1]]
 g := ![![[19, 10], [1, 23], [37, 44], [5, 72], [67], [1]], ![[27, 69], [51, 56], [9, 35], [31, 7], [67], [1]]]
 h' := ![![[64, 78], [20, 22], [29, 55], [21, 26], [2, 54], [20, 64], [0, 1]], ![[0, 1], [6, 57], [73, 24], [26, 53], [61, 25], [8, 15], [64, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [66, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [59, 15, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-861, -181, 171]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-78, -130, 171]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![19, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![19, 1, 0]] 
 ![![79, 0, 0], ![19, 1, 0], ![34, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![19, 1, 0], ![0, 19, 1], ![-115, 33, 20]]]
  hmulB := by decide  
  f := ![![![400, 21, 0], ![-1659, 0, 0]], ![![76, 4, 0], ![-315, 0, 0]], ![![138, 7, 0], ![-572, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 79, 0], ![-34, 0, 79]], ![![0, 1, 0], ![-5, 19, 1], ![-18, 33, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-48, -20, 1]] ![![79, 0, 0], ![19, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![1501, 79, 0]], ![![-3792, -1580, 79], ![-1027, -395, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![19, 1, 0]]], ![![![-48, -20, 1]], ![![-13, -5, 0]]]]
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


lemma PB108I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB108I1 : PrimesBelowBoundCertificateInterval O 31 79 108 where
  m := 11
  g := ![2, 3, 1, 2, 2, 1, 3, 2, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB108I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0, I73N1, I73N2]
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
    · exact ![1369, 37]
    · exact ![41, 41, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![4489, 67]
    · exact ![5041, 71]
    · exact ![73, 73, 73]
    · exact ![6241, 79]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI37N0
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
      exact NI41N2
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
    · dsimp ; intro j
      fin_cases j
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
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
      exact NI71N1
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I41N0, I41N1, I41N2, I47N1, I53N1, I61N0, I61N1, I61N2, I67N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [I41N0, I41N1, I41N2], [], [I47N1], [I53N1], [], [I61N0, I61N1, I61N2], [I67N1], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
