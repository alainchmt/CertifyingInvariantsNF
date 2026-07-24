
import IdealArithmetic.Examples.NF3_1_865755_1.RI3_1_865755_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5285524, 1101285, 309840]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![5285524, 1101285, 309840]] 
 ![![37, 0, 0], ![0, 37, 0], ![0, 27, 1]] where
  M :=![![![5285524, 1101285, 309840], ![88647930, 18470569, 5196585], ![277513875, 57822435, 16267999]]]
  hmulB := by decide  
  f := ![![![-9812, -495, 345]], ![![95265, 3148, -2820]], ![![64890, 2223, -1946]]]
  g := ![![![142852, -196335, 309840], ![2395890, -3292898, 5196585], ![7500375, -10308474, 16267999]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [11, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 36], [0, 1]]
 g := ![![[6, 27], [7], [15, 9], [27], [1]], ![[0, 10], [7], [13, 28], [27], [1]]]
 h' := ![![[8, 36], [27, 29], [20, 28], [9, 3], [26, 8], [0, 1]], ![[0, 1], [0, 8], [22, 9], [33, 34], [16, 29], [8, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [30, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [11, 29, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3145, 1934, 850]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85, -568, 850]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9812, -495, 345]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![-9812, -495, 345]] 
 ![![37, 0, 0], ![14, 1, 0], ![25, 0, 1]] where
  M :=![![![-9812, -495, 345], ![95265, 3148, -2820], ![-171225, -2745, 4138]]]
  hmulB := by decide  
  f := ![![![5285524, 1101285, 309840]], ![![4395818, 915907, 257685]], ![![11071675, 2306880, 649027]]]
  g := ![![![-311, -495, 345], ![3289, 3148, -2820], ![-6385, -2745, 4138]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![5285524, 1101285, 309840]] ![![-9812, -495, 345]]
  ![![37, 0, 0]] where
 M := ![![![37, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0]] 
 ![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [24, 8, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 18, 39], [13, 22, 2], [0, 1]]
 g := ![![[26, 32, 25], [1, 8], [21, 2], [8, 4, 1], []], ![[11, 14, 4, 37], [36, 21], [28, 9], [3, 22, 39, 16], [26, 4]], ![[40, 15, 38, 25], [7, 33], [4, 32], [29, 34, 37, 33], [22, 4]]]
 h' := ![![[32, 18, 39], [25, 15, 36], [34, 11, 34], [13, 4, 17], [0, 0, 1], [0, 1]], ![[13, 22, 2], [22, 7, 24], [5, 2, 29], [12, 15, 38], [31, 28, 22], [32, 18, 39]], ![[0, 1], [6, 19, 22], [25, 28, 19], [30, 22, 27], [10, 13, 18], [13, 22, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 22], []]
 b := ![[], [37, 24, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [24, 8, 37, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20354122, 8647392, 3373890]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![496442, 210912, 82290]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-23, 7, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-23, 7, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![20, 7, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-23, 7, 1], ![293, 23, 34], ![1857, 321, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -7, 43]], ![![-1, 0, 1], ![-9, -5, 34], ![39, 6, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [32, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 42], [0, 1]]
 g := ![![[20, 16], [13, 36], [13], [20, 25], [1]], ![[14, 27], [21, 7], [13], [16, 18], [1]]]
 h' := ![![[5, 42], [14, 4], [39, 37], [5, 23], [11, 5], [0, 1]], ![[0, 1], [34, 39], [9, 6], [34, 20], [36, 38], [5, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [25, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [32, 38, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3061624, 1523120, 705829]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-257092, -79481, 705829]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![9, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![9, 1, 0]] 
 ![![43, 0, 0], ![9, 1, 0], ![34, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![9, 1, 0], ![2, 10, 5], ![279, 39, 8]]]
  hmulB := by decide  
  f := ![![![-770, -4075, -2040], ![-215, 17544, 0]], ![![-161, -849, -425], ![-42, 3655, 0]], ![![-608, -3222, -1613], ![-174, 13872, 0]]]
  g := ![![![1, 0, 0], ![-9, 43, 0], ![-34, 0, 43]], ![![0, 1, 0], ![-6, 10, 5], ![-8, 39, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-23, 7, 1]] ![![43, 0, 0], ![9, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![387, 43, 0]], ![![-989, 301, 43], ![86, 86, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![9, 1, 0]]], ![![![-23, 7, 1]], ![![2, 2, 1]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0]] 
 ![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [36, 5, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 44, 30], [23, 2, 17], [0, 1]]
 g := ![![[24, 12, 7], [6, 8, 17], [1, 6, 17], [20, 5, 1], []], ![[20, 27, 4, 44], [31, 12, 33, 45], [15, 1, 46, 35], [29, 14, 43, 26], [43, 7]], ![[30, 46, 6, 7], [30, 23, 21, 12], [8, 18, 1, 36], [10, 41, 26, 12], [9, 7]]]
 h' := ![![[29, 44, 30], [19, 38, 30], [11, 4, 8], [32, 2, 39], [0, 0, 1], [0, 1]], ![[23, 2, 17], [27, 20, 25], [17, 30, 42], [12, 46, 44], [45, 17, 2], [29, 44, 30]], ![[0, 1], [40, 36, 39], [4, 13, 44], [36, 46, 11], [17, 30, 44], [23, 2, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 11], []]
 b := ![[], [5, 25, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [36, 5, 42, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26996753, -8736689, -2953010]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-574399, -185887, -62830]
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


def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![15, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![15, 1, 0]] 
 ![![53, 0, 0], ![15, 1, 0], ![16, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![15, 1, 0], ![2, 16, 5], ![279, 39, 14]]]
  hmulB := by decide  
  f := ![![![1862, 16911, 5290], ![901, -56074, 0]], ![![523, 4779, 1495], ![266, -15847, 0]], ![![559, 5105, 1597], ![283, -16928, 0]]]
  g := ![![![1, 0, 0], ![-15, 53, 0], ![-16, 0, 53]], ![![0, 1, 0], ![-6, 16, 5], ![-10, 39, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![23, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![23, 1, 0]] 
 ![![53, 0, 0], ![23, 1, 0], ![49, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![23, 1, 0], ![2, 24, 5], ![279, 39, 22]]]
  hmulB := by decide  
  f := ![![![-1288, -20143, -4200], ![-901, 44520, 0]], ![![-567, -8729, -1820], ![-370, 19292, 0]], ![![-1196, -18623, -3883], ![-821, 41160, 0]]]
  g := ![![![1, 0, 0], ![-23, 53, 0], ![-49, 0, 53]], ![![0, 1, 0], ![-15, 24, 5], ![-32, 39, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![15, 1, 0]] ![![53, 0, 0], ![15, 1, 0]]
  ![![53, 0, 0], ![-50, -15, 1]] where
 M := ![![![2809, 0, 0], ![795, 53, 0]], ![![795, 53, 0], ![227, 31, 5]]]
 hmul := by decide  
 g := ![![![![53, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![15, 1, 0], ![0, 0, 0]], ![![9, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-50, -15, 1]] ![![53, 0, 0], ![23, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1219, 53, 0]], ![![-2650, -795, 53], ![-901, -371, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![23, 1, 0]]], ![![![-50, -15, 1]], ![![-17, -7, -1]]]]
 hle2 := by decide  


def PBC53 : ContainsPrimesAboveP 53 ![I53N0, I53N0, I53N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
    exact isPrimeI53N0
    exact isPrimeI53N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 53 (by decide) (𝕀 ⊙ MulI53N0 ⊙ MulI53N1)
instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-53, -13, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-53, -13, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![6, 46, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-53, -13, 1], ![253, -27, -66], ![-3723, -459, -1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -46, 59]], ![![-1, -1, 1], ![11, 51, -66], ![-63, -7, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [5, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 58], [0, 1]]
 g := ![![[0, 12], [], [49], [0, 25], [0, 1]], ![[0, 47], [], [49], [0, 34], [0, 58]]]
 h' := ![![[0, 58], [0, 22], [50], [0, 52], [0, 54], [0, 1]], ![[0, 1], [0, 37], [50], [0, 7], [0, 5], [0, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [0, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [5, 0, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3197, 1992, 995]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -742, 995]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![7, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![7, 1, 0]] 
 ![![59, 0, 0], ![7, 1, 0], ![1, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![7, 1, 0], ![2, 8, 5], ![279, 39, 6]]]
  hmulB := by decide  
  f := ![![![-835, -3398, -2125], ![-118, 25075, 0]], ![![-100, -400, -250], ![1, 2950, 0]], ![![-17, -58, -36], ![22, 425, 0]]]
  g := ![![![1, 0, 0], ![-7, 59, 0], ![-1, 0, 59]], ![![0, 1, 0], ![-1, 8, 5], ![0, 39, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-53, -13, 1]] ![![59, 0, 0], ![7, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![413, 59, 0]], ![![-3127, -767, 59], ![-118, -118, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![7, 1, 0]]], ![![![-53, -13, 1]], ![![-2, -2, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0)
instance hp61 : Fact (Nat.Prime 61) := {out := by norm_num}

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-5, 26, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-5, 26, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![56, 26, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-5, 26, 1], ![331, 60, 129], ![7158, 1062, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -26, 61]], ![![-1, 0, 1], ![-113, -54, 129], ![110, 14, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [31, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 60], [0, 1]]
 g := ![![[34, 56], [16], [48, 15], [17, 13], [44, 1]], ![[58, 5], [16], [37, 46], [40, 48], [27, 60]]]
 h' := ![![[44, 60], [19, 42], [37, 57], [22, 36], [39, 14], [0, 1]], ![[0, 1], [37, 19], [44, 4], [20, 25], [45, 47], [44, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [45, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [31, 17, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78295, 14742, 3983]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2373, -1456, 3983]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-7, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-7, 1, 0]] 
 ![![61, 0, 0], ![54, 1, 0], ![53, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-7, 1, 0], ![2, -6, 5], ![279, 39, -8]]]
  hmulB := by decide  
  f := ![![![-1018, 3117, -2600], ![183, 31720, 0]], ![![-898, 2757, -2300], ![184, 28060, 0]], ![![-883, 2708, -2259], ![172, 27560, 0]]]
  g := ![![![1, 0, 0], ![-54, 61, 0], ![-53, 0, 61]], ![![-1, 1, 0], ![1, -6, 5], ![-23, 39, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-5, 26, 1]] ![![61, 0, 0], ![-7, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-427, 61, 0]], ![![-305, 1586, 61], ![366, -122, 122]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-7, 1, 0]]], ![![![-5, 26, 1]], ![![6, -2, 2]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-33, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-33, 1, 0]] 
 ![![67, 0, 0], ![34, 1, 0], ![17, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-33, 1, 0], ![2, -32, 5], ![279, 39, -34]]]
  hmulB := by decide  
  f := ![![![-149, 3454, -540], ![134, 7236, 0]], ![![-74, 1727, -270], ![68, 3618, 0]], ![![-25, 876, -137], ![60, 1836, 0]]]
  g := ![![![1, 0, 0], ![-34, 67, 0], ![-17, 0, 67]], ![![-1, 1, 0], ![15, -32, 5], ![-7, 39, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-18, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-18, 1, 0]] 
 ![![67, 0, 0], ![49, 1, 0], ![33, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-18, 1, 0], ![2, -17, 5], ![279, 39, -19]]]
  hmulB := by decide  
  f := ![![![1555, -14577, 4290], ![-603, -57486, 0]], ![![1147, -10653, 3135], ![-401, -42009, 0]], ![![771, -7180, 2113], ![-278, -28314, 0]]]
  g := ![![![1, 0, 0], ![-49, 67, 0], ![-33, 0, 67]], ![![-1, 1, 0], ![10, -17, 5], ![-15, 39, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-16, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-16, 1, 0]] 
 ![![67, 0, 0], ![51, 1, 0], ![6, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-16, 1, 0], ![2, -15, 5], ![279, 39, -17]]]
  hmulB := by decide  
  f := ![![![429, -3448, 1150], ![-134, -15410, 0]], ![![335, -2624, 875], ![-66, -11725, 0]], ![![42, -309, 103], ![3, -1380, 0]]]
  g := ![![![1, 0, 0], ![-51, 67, 0], ![-6, 0, 67]], ![![-1, 1, 0], ![11, -15, 5], ![-24, 39, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-33, 1, 0]] ![![67, 0, 0], ![-18, 1, 0]]
  ![![67, 0, 0], ![-55, -10, 1]] where
 M := ![![![4489, 0, 0], ![-1206, 67, 0]], ![![-2211, 67, 0], ![596, -50, 5]]]
 hmul := by decide  
 g := ![![![![67, 0, 0], ![0, 0, 0]], ![![37, 11, -1], ![67, 0, 0]]], ![![![22, 11, -1], ![67, 0, 0]], ![![13, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-55, -10, 1]] ![![67, 0, 0], ![-16, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1072, 67, 0]], ![![-3685, -670, 67], ![1139, 134, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-16, 1, 0]]], ![![![-55, -10, 1]], ![![17, 2, -1]]]]
 hle2 := by decide  


def PBC67 : ContainsPrimesAboveP 67 ![I67N0, I67N1, I67N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI67N0
    exact isPrimeI67N1
    exact isPrimeI67N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 67 (by decide) (𝕀 ⊙ MulI67N0 ⊙ MulI67N1)
instance hp71 : Fact (Nat.Prime 71) := {out := by norm_num}

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [64, 46, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 16, 35], [6, 54, 36], [0, 1]]
 g := ![![[1, 46, 45], [25, 42, 50], [47, 46, 2], [29, 6], [13, 1], []], ![[66, 55, 43, 63], [30, 39, 16, 44], [58, 67, 26, 28], [23, 12], [32, 5], [5, 18]], ![[24, 8, 40, 57], [22, 30, 37, 64], [20, 11, 49, 5], [63, 16], [56, 43], [4, 18]]]
 h' := ![![[7, 16, 35], [33, 33, 51], [45, 24, 11], [35, 60, 12], [20, 48, 52], [0, 0, 1], [0, 1]], ![[6, 54, 36], [4, 45, 4], [1, 0, 14], [43, 57, 50], [38, 50, 15], [13, 49, 54], [7, 16, 35]], ![[0, 1], [16, 64, 16], [41, 47, 46], [27, 25, 9], [15, 44, 4], [64, 22, 16], [6, 54, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 2], []]
 b := ![[], [54, 54, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [64, 46, 58, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2111398, -985054, -350385]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29738, -13874, -4935]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 357911 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def PBC71 : ContainsPrimesAboveP 71 ![I71N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![71, 0, 0]]) timesTableT_eq_Table B_one_repr 71 (by decide) 𝕀

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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [29, 46, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 49, 46], [63, 23, 27], [0, 1]]
 g := ![![[68, 10, 72], [70, 16], [69, 24], [67, 39, 4], [62, 1], []], ![[40, 50, 25, 46], [0, 27], [52, 48], [14, 5, 49, 57], [52, 18], [66, 72]], ![[6, 43, 4, 71], [26, 50], [1, 69], [55, 63, 22, 65], [41, 65], [12, 72]]]
 h' := ![![[72, 49, 46], [6, 23, 46], [24, 24, 69], [28, 20, 43], [27, 39, 2], [0, 0, 1], [0, 1]], ![[63, 23, 27], [23, 63, 72], [60, 18, 63], [20, 33, 11], [31, 8, 15], [58, 34, 23], [72, 49, 46]], ![[0, 1], [48, 60, 28], [46, 31, 14], [41, 20, 19], [17, 26, 56], [44, 39, 49], [63, 23, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 35], []]
 b := ![[], [71, 54, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [29, 46, 11, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19675836, 5315349, 1701995]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![269532, 72813, 23315]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-62, -5, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-62, -5, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![17, 74, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-62, -5, 1], ![269, -28, -26], ![-1491, -147, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -74, 79]], ![![-1, -1, 1], ![9, 24, -26], ![-15, 15, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [6, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 78], [0, 1]]
 g := ![![[78, 40], [3, 11], [71, 18], [54, 38], [36], [1]], ![[2, 39], [69, 68], [21, 61], [45, 41], [36], [1]]]
 h' := ![![[6, 78], [61, 44], [48, 66], [71, 27], [57, 65], [73, 6], [0, 1]], ![[0, 1], [9, 35], [49, 13], [75, 52], [52, 14], [30, 73], [6, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [40, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [6, 73, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18016, 8410, 3295]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-481, -2980, 3295]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![26, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![26, 1, 0]] 
 ![![79, 0, 0], ![26, 1, 0], ![18, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![26, 1, 0], ![2, 27, 5], ![279, 39, 25]]]
  hmulB := by decide  
  f := ![![![1539, 24613, 4560], ![869, -72048, 0]], ![![496, 8096, 1500], ![317, -23700, 0]], ![![350, 5608, 1039], ![200, -16416, 0]]]
  g := ![![![1, 0, 0], ![-26, 79, 0], ![-18, 0, 79]], ![![0, 1, 0], ![-10, 27, 5], ![-15, 39, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-62, -5, 1]] ![![79, 0, 0], ![26, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![2054, 79, 0]], ![![-4898, -395, 79], ![-1343, -158, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![26, 1, 0]]], ![![![-62, -5, 1]], ![![-17, -2, 0]]]]
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


lemma PB264I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB264I1 : PrimesBelowBoundCertificateInterval O 31 79 264 where
  m := 11
  g := ![2, 1, 2, 1, 3, 2, 2, 3, 1, 1, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB264I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N0, I53N1]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0]
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
    · exact ![1369, 37]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![53, 53, 53]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![67, 67, 67]
    · exact ![357911]
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
      exact NI37N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
      exact NI53N0
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
      exact NI61N1
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I37N1, I43N1, I53N0, I53N1, I59N1, I61N1, I67N0, I67N1, I67N2, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N0, I53N0, I53N1], [I59N1], [I61N1], [I67N0, I67N1, I67N2], [], [], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
