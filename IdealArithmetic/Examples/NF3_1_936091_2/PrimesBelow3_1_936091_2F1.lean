
import IdealArithmetic.Examples.NF3_1_936091_2.RI3_1_936091_2
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [21, 3, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 30, 14], [23, 6, 23], [0, 1]]
 g := ![![[26, 26, 16], [23, 11], [11, 17, 3], [32, 1], []], ![[12, 4, 6, 23], [0, 33], [13, 30, 12, 29], [21, 36], [8, 11]], ![[31, 8, 0, 6], [11, 10], [33, 32, 11, 35], [8, 12], [36, 11]]]
 h' := ![![[9, 30, 14], [5, 4, 4], [28, 16, 14], [31, 31, 22], [0, 0, 1], [0, 1]], ![[23, 6, 23], [26, 2, 6], [27, 30, 12], [24, 22, 11], [24, 26, 6], [9, 30, 14]], ![[0, 1], [3, 31, 27], [30, 28, 11], [5, 21, 4], [32, 11, 30], [23, 6, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 35], []]
 b := ![[], [22, 25, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [21, 3, 5, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![221815, -27861, -143005]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5995, -753, -3865]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [8, 3, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 36, 9], [10, 4, 32], [0, 1]]
 g := ![![[3, 29, 21], [5, 40], [11, 9], [29, 27, 1], []], ![[24, 16], [31, 39], [4, 23], [22, 8, 32, 21], [6, 40]], ![[1, 36, 29, 16], [36, 31], [32, 25], [37, 14, 16, 21], [24, 40]]]
 h' := ![![[17, 36, 9], [21, 19, 29], [26, 21, 32], [14, 25, 38], [0, 0, 1], [0, 1]], ![[10, 4, 32], [35, 15], [18, 39, 30], [3, 5, 8], [36, 25, 4], [17, 36, 9]], ![[0, 1], [3, 7, 12], [39, 22, 20], [7, 11, 36], [31, 16, 36], [10, 4, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 33], []]
 b := ![[], [24, 39, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [8, 3, 14, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4547474, -2108876, 1764476]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![110914, -51436, 43036]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![23, -14, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![23, -14, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![23, 29, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![23, -14, 1], ![130, -38, -71], ![-1476, 489, 5]]]
  hmulB := by decide  
  f := ![![![-22, 14, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -29, 43]], ![![0, -1, 1], ![41, 47, -71], ![-37, 8, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [22, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 42], [0, 1]]
 g := ![![[20, 31], [16, 35], [24], [42, 14], [1]], ![[11, 12], [10, 8], [24], [31, 29], [1]]]
 h' := ![![[33, 42], [35, 17], [42, 32], [22, 14], [21, 33], [0, 1]], ![[0, 1], [37, 26], [23, 11], [11, 29], [35, 10], [33, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [35, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [22, 10, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3293176, -614451, -1237483]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![738495, 820292, -1237483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-15, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-15, 1, 0]] 
 ![![43, 0, 0], ![28, 1, 0], ![38, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-15, 1, 0], ![-2, -13, 5], ![102, -33, -16]]]
  hmulB := by decide  
  f := ![![![-289, -2082, 800], ![86, -6880, 0]], ![![-192, -1353, 520], ![44, -4472, 0]], ![![-254, -1840, 707], ![80, -6080, 0]]]
  g := ![![![1, 0, 0], ![-28, 43, 0], ![-38, 0, 43]], ![![-1, 1, 0], ![4, -13, 5], ![38, -33, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![23, -14, 1]] ![![43, 0, 0], ![-15, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-645, 43, 0]], ![![989, -602, 43], ![-215, 172, -86]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-15, 1, 0]]], ![![![23, -14, 1]], ![![-5, 4, -2]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [5, 1, 7, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 18, 20], [16, 28, 27], [0, 1]]
 g := ![![[14, 26, 34], [25, 14, 3], [39, 2, 25], [1, 40, 1], []], ![[40, 8, 32, 39], [23, 23, 3, 39], [41, 21, 44, 5], [24, 13, 12, 29], [35, 24]], ![[26, 32, 41, 32], [40, 43, 30, 25], [9, 31, 16, 6], [6, 34, 19, 6], [28, 24]]]
 h' := ![![[24, 18, 20], [16, 1, 38], [40, 23, 12], [42, 34, 42], [0, 0, 1], [0, 1]], ![[16, 28, 27], [3, 29, 3], [46, 39, 44], [28, 28, 23], [25, 4, 28], [24, 18, 20]], ![[0, 1], [22, 17, 6], [14, 32, 38], [6, 32, 29], [22, 43, 18], [16, 28, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 19], []]
 b := ![[], [39, 33, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [5, 1, 7, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3105572, 1671555, -1907025]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66076, 35565, -40575]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![36, 6, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![36, 6, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![36, 6, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![36, 6, 1], ![90, 15, 29], ![564, -171, -2]]]
  hmulB := by decide  
  f := ![![![-35, -6, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -6, 53]], ![![0, 0, 1], ![-18, -3, 29], ![12, -3, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [14, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 52], [0, 1]]
 g := ![![[28, 42], [46], [7, 13], [9], [32, 1]], ![[47, 11], [46], [52, 40], [9], [11, 52]]]
 h' := ![![[32, 52], [3, 28], [8, 29], [26, 38], [29, 3], [0, 1]], ![[0, 1], [51, 25], [35, 24], [23, 15], [19, 50], [32, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [25, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [14, 21, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1902, -372, -910]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![654, 96, -910]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![24, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![24, 1, 0]] 
 ![![53, 0, 0], ![24, 1, 0], ![2, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![24, 1, 0], ![-2, 26, 5], ![102, -33, 23]]]
  hmulB := by decide  
  f := ![![![997, -14200, -2730], ![212, 28938, 0]], ![![446, -6424, -1235], ![107, 13091, 0]], ![![34, -536, -103], ![16, 1092, 0]]]
  g := ![![![1, 0, 0], ![-24, 53, 0], ![-2, 0, 53]], ![![0, 1, 0], ![-12, 26, 5], ![16, -33, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![36, 6, 1]] ![![53, 0, 0], ![24, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![1272, 53, 0]], ![![1908, 318, 53], ![954, 159, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![24, 1, 0]]], ![![![36, 6, 1]], ![![18, 3, 1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [7, 26, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 8, 24], [26, 50, 35], [0, 1]]
 g := ![![[17, 47, 53], [39, 29, 9], [26, 20], [1, 47, 35], [1]], ![[8, 37, 16, 55], [31, 16, 8, 31], [41, 4], [51, 18, 20, 11], [26, 11, 55, 18]], ![[1, 45, 3, 19], [24, 42, 38, 12], [0, 29], [25, 39, 11, 22], [19, 4, 46, 41]]]
 h' := ![![[58, 8, 24], [22, 11, 17], [44, 46, 3], [52, 48, 43], [52, 33, 25], [0, 1]], ![[26, 50, 35], [53, 24, 52], [54, 27, 15], [20, 0, 57], [53, 38, 36], [58, 8, 24]], ![[0, 1], [36, 24, 49], [12, 45, 41], [22, 11, 18], [38, 47, 57], [26, 50, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 50], []]
 b := ![[], [36, 23, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [7, 26, 34, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5921004, 2446612, -793432]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100356, 41468, -13448]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0]] 
 ![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [12, 59, 21, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 11, 59], [19, 49, 2], [0, 1]]
 g := ![![[44, 22, 1], [38, 27], [2, 20, 47], [56, 49, 14], [1]], ![[6, 31, 4, 50], [9, 5], [14, 58, 50, 6], [28, 20, 26, 29], [20, 42, 56, 53]], ![[60, 19, 35, 37], [3, 4], [55, 9, 25, 26], [36, 23, 10, 29], [59, 35, 54, 8]]]
 h' := ![![[21, 11, 59], [59, 52, 1], [37, 9, 37], [60, 34, 48], [49, 2, 40], [0, 1]], ![[19, 49, 2], [17, 59, 6], [53, 28, 26], [22, 28, 27], [54, 59, 4], [21, 11, 59]], ![[0, 1], [3, 11, 54], [10, 24, 59], [4, 60, 47], [51, 0, 17], [19, 49, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 60], []]
 b := ![[], [47, 12, 30], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [12, 59, 21, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1601921, 729011, -577487]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26261, 11951, -9467]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 226981 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def PBC61 : ContainsPrimesAboveP 61 ![I61N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![61, 0, 0]]) timesTableT_eq_Table B_one_repr 61 (by decide) 𝕀

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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [31, 41, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 51, 25], [39, 15, 42], [0, 1]]
 g := ![![[3, 64, 17], [50, 64, 15], [55, 33], [0, 36], [13, 1], []], ![[26, 58, 34, 33], [34, 7, 66, 56], [41, 55], [58, 62], [63, 24], [22, 22]], ![[5, 63, 28, 28], [53, 36, 54, 45], [41, 36], [14, 64], [34, 55], [5, 22]]]
 h' := ![![[41, 51, 25], [58, 23, 33], [38, 29, 22], [1, 12, 57], [66, 39, 61], [0, 0, 1], [0, 1]], ![[39, 15, 42], [66, 8, 65], [23, 10, 50], [17, 25, 16], [26, 2, 14], [61, 52, 15], [41, 51, 25]], ![[0, 1], [4, 36, 36], [66, 28, 62], [8, 30, 61], [24, 26, 59], [26, 15, 51], [39, 15, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 17], []]
 b := ![[], [48, 20, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [31, 41, 54, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-425383, -155440, 940345]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6349, -2320, 14035]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-5, -32, 1]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-5, -32, 1]] 
 ![![71, 0, 0], ![0, 71, 0], ![66, 39, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-5, -32, 1], ![166, -102, -161], ![-3312, 1083, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -39, 71]], ![![-1, -1, 1], ![152, 87, -161], ![-42, 18, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [8, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 70], [0, 1]]
 g := ![![[0, 9], [0, 27], [], [], [], [1]], ![[0, 62], [0, 44], [], [], [], [1]]]
 h' := ![![[0, 70], [0, 68], [0, 58], [49], [64], [63], [0, 1]], ![[0, 1], [0, 3], [0, 13], [49], [64], [63], [0, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [0, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [8, 0, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19633, -3725, -7150]
  a := ![5, -10, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6923, 3875, -7150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![19, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![19, 1, 0]] 
 ![![71, 0, 0], ![19, 1, 0], ![5, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![19, 1, 0], ![-2, 21, 5], ![102, -33, 18]]]
  hmulB := by decide  
  f := ![![![-1150, 12286, 2925], ![-71, -41535, 0]], ![![-312, 3276, 780], ![1, -11076, 0]], ![![-85, 865, 206], ![10, -2925, 0]]]
  g := ![![![1, 0, 0], ![-19, 71, 0], ![-5, 0, 71]], ![![0, 1, 0], ![-6, 21, 5], ![9, -33, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-5, -32, 1]] ![![71, 0, 0], ![19, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![1349, 71, 0]], ![![-355, -2272, 71], ![71, -710, -142]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![19, 1, 0]]], ![![![-5, -32, 1]], ![![1, -10, -2]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-33, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-33, 1, 0]] 
 ![![73, 0, 0], ![40, 1, 0], ![14, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-33, 1, 0], ![-2, -31, 5], ![102, -33, -34]]]
  hmulB := by decide  
  f := ![![![-4712, -80739, 13020], ![1095, -190092, 0]], ![![-2587, -44214, 7130], ![585, -104098, 0]], ![![-877, -15485, 2497], ![269, -36456, 0]]]
  g := ![![![1, 0, 0], ![-40, 73, 0], ![-14, 0, 73]], ![![-1, 1, 0], ![16, -31, 5], ![26, -33, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2053041, 48304, 60789]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![2053041, 48304, 60789]] 
 ![![73, 0, 0], ![51, 1, 0], ![43, 0, 1]] where
  M :=![![![2053041, 48304, 60789], ![6103870, 143612, 180731], ![2009136, 47271, 59489]]]
  hmulB := by decide  
  f := ![![![-833, 163, 356]], ![![-89, -54, 255]], ![![-497, 154, 40]]]
  g := ![![![-41430, 48304, 60789], ![-123175, 143612, 180731], ![-40544, 47271, 59489]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-19, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-19, 1, 0]] 
 ![![73, 0, 0], ![54, 1, 0], ![8, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-19, 1, 0], ![-2, -17, 5], ![102, -33, -20]]]
  hmulB := by decide  
  f := ![![![-3013, -26594, 7820], ![438, -114172, 0]], ![![-2216, -19657, 5780], ![366, -84388, 0]], ![![-319, -2915, 857], ![91, -12512, 0]]]
  g := ![![![1, 0, 0], ![-54, 73, 0], ![-8, 0, 73]], ![![-1, 1, 0], ![12, -17, 5], ![28, -33, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-33, 1, 0]] ![![2053041, 48304, 60789]]
  ![![73, 0, 0], ![28, 4, 1]] where
 M := ![![![149871993, 3526192, 4437597]], ![![-61646483, -1450420, -1825306]]]
 hmul := by decide  
 g := ![![![![1789281, 10624, 51369], ![687660, 0, 0]]], ![![![-735995, -4372, -21130], ![-282816, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![28, 4, 1]] ![![73, 0, 0], ![-19, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1387, 73, 0]], ![![2044, 292, 73], ![-438, -73, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-19, 1, 0]]], ![![![28, 4, 1]], ![![-6, -1, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![555, -634, 1359]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![555, -634, 1359]] 
 ![![79, 0, 0], ![0, 79, 0], ![10, 69, 1]] where
  M :=![![![555, -634, 1359], ![139886, -45560, -4529], ![-129900, 57615, -42299]]]
  hmulB := by decide  
  f := ![![![-27697225, -651661, -820094]], ![![-82346266, -1937445, -2438211]], ![![-75771766, -1782760, -2243545]]]
  g := ![![![-165, -1195, 1359], ![2344, 3379, -4529], ![3710, 37674, -42299]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [22, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 78], [0, 1]]
 g := ![![[22, 18], [41, 21], [19, 20], [71, 49], [21], [1]], ![[0, 61], [68, 58], [56, 59], [55, 30], [21], [1]]]
 h' := ![![[69, 78], [46, 52], [56, 10], [18, 39], [22, 72], [57, 69], [0, 1]], ![[0, 1], [0, 27], [35, 69], [23, 40], [13, 7], [78, 10], [69, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [65, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [22, 10, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148063, -25218, -61563]
  a := ![-15, 27, 44]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9667, 53451, -61563]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![27697225, 651661, 820094]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![27697225, 651661, 820094]] 
 ![![79, 0, 0], ![51, 1, 0], ![12, 0, 1]] where
  M :=![![![27697225, 651661, 820094], ![82346266, 1937445, 2438211], ![27104910, 637725, 802556]]]
  hmulB := by decide  
  f := ![![![-555, 634, -1359]], ![![-2129, 986, -820]], ![![1560, -633, 329]]]
  g := ![![![-194666, 651661, 820094], ![-578759, 1937445, 2438211], ![-190503, 637725, 802556]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![555, -634, 1359]] ![![27697225, 651661, 820094]]
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


lemma PB274I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB274I1 : PrimesBelowBoundCertificateInterval O 31 79 274 where
  m := 11
  g := ![1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB274I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0]
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
    · exact ![50653]
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![300763]
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
      exact NI53N1
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
      exact NI73N1
      exact NI73N2
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I43N1, I53N1, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[], [], [I43N1], [], [I53N1], [], [], [], [I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
