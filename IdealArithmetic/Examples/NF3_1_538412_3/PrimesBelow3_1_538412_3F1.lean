
import IdealArithmetic.Examples.NF3_1_538412_3.RI3_1_538412_3
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [5, 21, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 5, 12], [31, 31, 25], [0, 1]]
 g := ![![[36, 3, 21], [36, 4], [22, 33, 30], [36, 1], []], ![[9, 35, 5, 16], [18, 9], [25, 27, 2, 1], [32, 36], [13, 33]], ![[3, 1, 24, 3], [25, 1], [21, 27, 27, 30], [7, 25], [0, 33]]]
 h' := ![![[5, 5, 12], [6, 18, 13], [1, 27, 35], [5, 16, 17], [0, 0, 1], [0, 1]], ![[31, 31, 25], [20, 4, 27], [31, 23, 3], [34, 33, 16], [34, 19, 31], [5, 5, 12]], ![[0, 1], [33, 15, 34], [26, 24, 36], [3, 25, 4], [36, 18, 5], [31, 31, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 3], []]
 b := ![[], [31, 32, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [5, 21, 1, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-394272, -47175, -28305]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10656, -1275, -765]
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


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![293, -10, -6]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![293, -10, -6]] 
 ![![41, 0, 0], ![25, 1, 0], ![12, 0, 1]] where
  M :=![![![293, -10, -6], ![-868, 247, -112], ![-1822, -212, 201]]]
  hmulB := by decide  
  f := ![![![-25903, -3282, -2602]], ![![-25027, -3171, -2514]], ![![-23046, -2920, -2315]]]
  g := ![![![15, -10, -6], ![-139, 247, -112], ![26, -212, 201]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![772, 180, -139]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![772, 180, -139]] 
 ![![41, 0, 0], ![32, 1, 0], ![35, 0, 1]] where
  M :=![![![772, 180, -139], ![-20932, -1117, 1522], ![18717, -383, -536]]]
  hmulB := by decide  
  f := ![![![1181638, 149717, 118697]], ![![1343418, 170215, 134948]], ![![1714175, 217191, 172191]]]
  g := ![![![-3, 180, -139], ![-938, -1117, 1522], ![1213, -383, -536]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![293, -10, -6]] ![![293, -10, -6]]
  ![![105461, -4128, -1844]] where
 M := ![![![105461, -4128, -1844]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![105461, -4128, -1844]] ![![772, 180, -139]]
  ![![41, 0, 0]] where
 M := ![![![133309040, 24300208, -19953511]]]
 hmul := by decide  
 g := ![![![![3251440, 592688, -486671]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0 ⊙ MulI41N1)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![370, -429, 241]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![370, -429, 241]] 
 ![![43, 0, 0], ![0, 43, 0], ![1, 5, 1]] where
  M :=![![![370, -429, 241], ![36526, 3879, -3808], ![-49755, -622, 2404]]]
  hmulB := by decide  
  f := ![![![161780, 20498, 16251]], ![![2364152, 299545, 237482]], ![![370757, 46976, 37243]]]
  g := ![![![3, -38, 241], ![938, 533, -3808], ![-1213, -294, 2404]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [27, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 42], [0, 1]]
 g := ![![[32, 36], [26, 13], [14], [23, 16], [1]], ![[17, 7], [17, 30], [14], [2, 27], [1]]]
 h' := ![![[39, 42], [29, 6], [26, 23], [24, 33], [16, 39], [0, 1]], ![[0, 1], [5, 37], [20, 20], [21, 10], [32, 4], [39, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [15, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [27, 4, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9574, 1752, 2294]
  a := ![-3, -5, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-276, -226, 2294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-161780, -20498, -16251]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-161780, -20498, -16251]] 
 ![![43, 0, 0], ![34, 1, 0], ![20, 0, 1]] where
  M :=![![![-161780, -20498, -16251], ![-2364152, -299545, -237482], ![-3960011, -501745, -397788]]]
  hmulB := by decide  
  f := ![![![-370, 429, -241]], ![![-1142, 249, -102]], ![![985, 214, -168]]]
  g := ![![![20004, -20498, -16251], ![292326, -299545, -237482], ![489653, -501745, -397788]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![370, -429, 241]] ![![-161780, -20498, -16251]]
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
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![13, -24, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![13, -24, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![13, 23, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![13, -24, 1], ![196, 72, -238], ![-3495, -247, -23]]]
  hmulB := by decide  
  f := ![![![-12, 24, -1], ![47, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -23, 47]], ![![0, -1, 1], ![70, 118, -238], ![-68, 6, -23]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [7, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 46], [0, 1]]
 g := ![![[36, 27], [27, 32], [21, 4], [25, 7], [1]], ![[0, 20], [0, 15], [0, 43], [0, 40], [1]]]
 h' := ![![[30, 46], [46, 11], [41, 19], [13, 45], [40, 30], [0, 1]], ![[0, 1], [0, 36], [0, 28], [0, 2], [0, 17], [30, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [12, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [7, 17, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![230546, 77931, 55309]
  a := ![1, 2, -69]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10393, -25408, 55309]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![3, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![3, 1, 0]] 
 ![![47, 0, 0], ![3, 1, 0], ![23, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![3, 1, 0], ![-2, 1, 10], ![148, 11, 5]]]
  hmulB := by decide  
  f := ![![![-319, 160, 1600], ![0, -7520, 0]], ![![-20, 10, 100], ![1, -470, 0]], ![![-157, 78, 783], ![14, -3680, 0]]]
  g := ![![![1, 0, 0], ![-3, 47, 0], ![-23, 0, 47]], ![![0, 1, 0], ![-5, 1, 10], ![0, 11, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![13, -24, 1]] ![![47, 0, 0], ![3, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![141, 47, 0]], ![![611, -1128, 47], ![235, 0, -235]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![3, 1, 0]]], ![![![13, -24, 1]], ![![5, 0, -5]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![0, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![0, 1, 0]] 
 ![![53, 0, 0], ![0, 1, 0], ![21, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![0, 1, 0], ![-2, -2, 10], ![148, 11, 2]]]
  hmulB := by decide  
  f := ![![![-53, -54, 270], ![0, -1431, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-21, -22, 107], ![32, -567, 0]]]
  g := ![![![1, 0, 0], ![0, 53, 0], ![-21, 0, 53]], ![![0, 1, 0], ![-4, -2, 10], ![2, 11, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![18, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![18, 1, 0]] 
 ![![53, 0, 0], ![18, 1, 0], ![24, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![18, 1, 0], ![-2, 16, 10], ![148, 11, 20]]]
  hmulB := by decide  
  f := ![![![-245, 1968, 1230], ![0, -6519, 0]], ![![-82, 656, 410], ![1, -2173, 0]], ![![-114, 891, 557], ![9, -2952, 0]]]
  g := ![![![1, 0, 0], ![-18, 53, 0], ![-24, 0, 53]], ![![0, 1, 0], ![-10, 16, 10], ![-10, 11, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-18, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-18, 1, 0]] 
 ![![53, 0, 0], ![35, 1, 0], ![38, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-18, 1, 0], ![-2, -20, 10], ![148, 11, -16]]]
  hmulB := by decide  
  f := ![![![4867, 51013, -25500], ![-689, 135150, 0]], ![![3223, 33668, -16830], ![-423, 89199, 0]], ![![3496, 36575, -18283], ![-475, 96900, 0]]]
  g := ![![![1, 0, 0], ![-35, 53, 0], ![-38, 0, 53]], ![![-1, 1, 0], ![6, -20, 10], ![7, 11, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![0, 1, 0]] ![![53, 0, 0], ![18, 1, 0]]
  ![![53, 0, 0], ![-32, -9, 1]] where
 M := ![![![2809, 0, 0], ![954, 53, 0]], ![![0, 53, 0], ![-2, 16, 10]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![18, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![6, 2, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-32, -9, 1]] ![![53, 0, 0], ![-18, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-954, 53, 0]], ![![-1696, -477, 53], ![742, 159, -106]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-18, 1, 0]]], ![![![-32, -9, 1]], ![![14, 3, -2]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N1, I53N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N1
    exact isPrimeI53N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [56, 37, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 53, 24], [18, 5, 35], [0, 1]]
 g := ![![[47, 38, 57], [55, 26, 22], [18, 17], [4, 43, 29], [1]], ![[21, 41, 58, 8], [42, 25, 6, 37], [20, 27], [46, 22, 18, 14], [19, 14, 46, 18]], ![[46, 35, 54, 17], [58, 33, 22, 4], [38, 25], [28, 6, 57, 4], [41, 11, 55, 41]]]
 h' := ![![[23, 53, 24], [47, 18, 23], [21, 30, 9], [12, 49, 31], [3, 22, 41], [0, 1]], ![[18, 5, 35], [55, 27, 16], [16, 37, 57], [30, 47, 33], [11, 24, 25], [23, 53, 24]], ![[0, 1], [37, 14, 20], [25, 51, 52], [18, 22, 54], [55, 13, 52], [18, 5, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 48], []]
 b := ![[], [23, 20, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [56, 37, 18, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4919184, -744108, -205792]
  a := ![3, 4, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-83376, -12612, -3488]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-13, -29, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-13, -29, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![48, 32, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-13, -29, 1], ![206, 56, -288], ![-4235, -302, -59]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -32, 61]], ![![-1, -1, 1], ![230, 152, -288], ![-23, 26, -59]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [54, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 60], [0, 1]]
 g := ![![[55, 58], [49], [45, 60], [59, 4], [19, 1]], ![[59, 3], [49], [26, 1], [13, 57], [38, 60]]]
 h' := ![![[19, 60], [16, 34], [10, 7], [47, 50], [11, 2], [0, 1]], ![[0, 1], [52, 27], [21, 54], [21, 11], [49, 59], [19, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [30, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [54, 42, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1522, 425, 80]
  a := ![1, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38, -35, 80]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-17, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-17, 1, 0]] 
 ![![61, 0, 0], ![44, 1, 0], ![59, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-17, 1, 0], ![-2, -19, 10], ![148, 11, -15]]]
  hmulB := by decide  
  f := ![![![844, 8171, -4300], ![-61, 26230, 0]], ![![604, 5891, -3100], ![-60, 18910, 0]], ![![818, 7903, -4159], ![-53, 25370, 0]]]
  g := ![![![1, 0, 0], ![-44, 61, 0], ![-59, 0, 61]], ![![-1, 1, 0], ![4, -19, 10], ![9, 11, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-13, -29, 1]] ![![61, 0, 0], ![-17, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1037, 61, 0]], ![![-793, -1769, 61], ![427, 549, -305]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-17, 1, 0]]], ![![![-13, -29, 1]], ![![7, 9, -5]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-23, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-23, 1, 0]] 
 ![![67, 0, 0], ![44, 1, 0], ![16, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-23, 1, 0], ![-2, -25, 10], ![148, 11, -21]]]
  hmulB := by decide  
  f := ![![![-3335, -44008, 17600], ![536, -117920, 0]], ![![-2194, -28880, 11550], ![336, -77385, 0]], ![![-782, -10510, 4203], ![170, -28160, 0]]]
  g := ![![![1, 0, 0], ![-44, 67, 0], ![-16, 0, 67]], ![![-1, 1, 0], ![14, -25, 10], ![0, 11, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-22, 1, 0]] 
 ![![67, 0, 0], ![45, 1, 0], ![14, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-22, 1, 0], ![-2, -24, 10], ![148, 11, -20]]]
  hmulB := by decide  
  f := ![![![247, 2952, -1230], ![0, 8241, 0]], ![![165, 1968, -820], ![1, 5494, 0]], ![![70, 616, -257], ![56, 1722, 0]]]
  g := ![![![1, 0, 0], ![-45, 67, 0], ![-14, 0, 67]], ![![-1, 1, 0], ![14, -24, 10], ![-1, 11, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-23, 1, 0]] ![![67, 0, 0], ![-22, 1, 0]]
  ![![67, 0, 0], ![-30, 2, 1]] where
 M := ![![![4489, 0, 0], ![-1474, 67, 0]], ![![-1541, 67, 0], ![504, -47, 10]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![8, -1, -1], ![67, 0, 0]]], ![![![7, -1, -1], ![67, 0, 0]], ![![12, -1, 0], ![10, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-30, 2, 1]] ![![67, 0, 0], ![-22, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1474, 67, 0]], ![![-2010, 134, 67], ![804, -67, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-22, 1, 0]]], ![![![-30, 2, 1]], ![![12, -1, 0]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, -7, 2]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![53, -7, 2]] 
 ![![71, 0, 0], ![0, 71, 0], ![62, 32, 1]] where
  M :=![![![53, -7, 2], ![310, 89, -66], ![-922, -43, 63]]]
  hmulB := by decide  
  f := ![![![-39, -5, -4]], ![![-582, -73, -58]], ![![-310, -39, -31]]]
  g := ![![![-1, -1, 2], ![62, 31, -66], ![-68, -29, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [7, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 70], [0, 1]]
 g := ![![[14, 29], [8, 27], [6, 54], [49], [19], [1]], ![[12, 42], [60, 44], [39, 17], [49], [19], [1]]]
 h' := ![![[44, 70], [15, 10], [29, 58], [39, 57], [58, 7], [64, 44], [0, 1]], ![[0, 1], [29, 61], [25, 13], [62, 14], [11, 64], [12, 27], [44, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [3, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [7, 27, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![33353, 2790, 4254]
  a := ![-1, 18, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3245, -1878, 4254]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39, 5, 4]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![39, 5, 4]] 
 ![![71, 0, 0], ![33, 1, 0], ![4, 0, 1]] where
  M :=![![![39, 5, 4], ![582, 73, 58], ![968, 123, 97]]]
  hmulB := by decide  
  f := ![![![-53, 7, -2]], ![![-29, 2, 0]], ![![10, 1, -1]]]
  g := ![![![-2, 5, 4], ![-29, 73, 58], ![-49, 123, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![53, -7, 2]] ![![39, 5, 4]]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [42, 2, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 45, 71], [70, 27, 2], [0, 1]]
 g := ![![[24, 25, 61], [32, 46], [51, 35], [0, 14, 72], [11, 1], []], ![[47, 51, 6, 4], [63, 25], [16, 35], [24, 25, 57, 6], [61, 72], [10, 4]], ![[45, 22, 29, 19], [45, 72], [], [35, 1, 12, 3], [36, 54], [6, 4]]]
 h' := ![![[14, 45, 71], [11, 27, 34], [48, 34, 51], [0, 61, 20], [49, 9, 46], [0, 0, 1], [0, 1]], ![[70, 27, 2], [0, 68, 61], [50, 65, 68], [24, 22, 53], [18, 4, 56], [68, 50, 27], [14, 45, 71]], ![[0, 1], [63, 51, 51], [36, 47, 27], [67, 63], [13, 60, 44], [49, 23, 45], [70, 27, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 33], []]
 b := ![[], [45, 48, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [42, 2, 62, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-252945, -49056, 31682]
  a := ![1, 4, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3465, -672, 434]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0]] 
 ![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [36, 1, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 49, 65], [53, 29, 14], [0, 1]]
 g := ![![[15, 26, 16], [29, 19, 25], [3, 49, 55], [42, 57, 21], [66, 1], []], ![[57, 35, 22, 62], [45, 0, 41, 44], [40, 60, 56, 38], [5, 73, 70, 9], [45, 51], [30, 38]], ![[7, 50, 36, 75], [26, 54, 14, 29], [10, 43, 22, 7], [63, 9, 17, 57], [57, 31], [2, 38]]]
 h' := ![![[13, 49, 65], [62, 49, 4], [50, 13, 74], [68, 75, 23], [73, 56, 10], [0, 0, 1], [0, 1]], ![[53, 29, 14], [57, 9, 62], [34, 72, 68], [77, 33, 12], [65, 3, 59], [37, 34, 29], [13, 49, 65]], ![[0, 1], [19, 21, 13], [10, 73, 16], [2, 50, 44], [75, 20, 10], [51, 45, 49], [53, 29, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 77], []]
 b := ![[], [74, 35, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [36, 1, 13, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2703380, 359213, 188020]
  a := ![-2, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34220, 4547, 2380]
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



lemma PB208I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB208I1 : PrimesBelowBoundCertificateInterval O 31 79 208 where
  m := 11
  g := ![1, 3, 2, 2, 3, 1, 2, 3, 2, 1, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB208I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N1]
    · exact ![I71N0, I71N1]
    · exact ![I73N0]
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
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![5041, 71]
    · exact ![389017]
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
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N1
      exact NI53N2
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
      exact NI67N1
      exact NI67N1
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
  β := ![I41N0, I41N1, I43N1, I47N1, I53N0, I53N1, I53N2, I61N1, I67N0, I67N1, I71N1]
  Il := ![[], [I41N0, I41N0, I41N1], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [], [I61N1], [I67N0, I67N1, I67N1], [I71N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
