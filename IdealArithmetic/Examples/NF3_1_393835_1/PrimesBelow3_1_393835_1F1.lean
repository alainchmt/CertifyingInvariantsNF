
import IdealArithmetic.Examples.NF3_1_393835_1.RI3_1_393835_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [3, 4, 16, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 20, 14], [4, 16, 23], [0, 1]]
 g := ![![[19, 12, 21], [36, 30], [16, 27, 12], [21, 1], []], ![[19, 5, 15, 6], [4, 26], [15, 9, 1, 19], [16, 34], [14, 11]], ![[36, 32, 4, 6], [14, 26], [31, 3, 25, 20], [4, 30], [5, 11]]]
 h' := ![![[17, 20, 14], [13, 35, 24], [26, 13, 17], [11, 24, 30], [0, 0, 1], [0, 1]], ![[4, 16, 23], [24, 10, 23], [6, 21, 10], [22, 6, 2], [25, 36, 16], [17, 20, 14]], ![[0, 1], [29, 29, 27], [21, 3, 10], [26, 7, 5], [1, 1, 20], [4, 16, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 28], []]
 b := ![[], [15, 12, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [3, 4, 16, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-180597, -72409, -7585]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4881, -1957, -205]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-46, -16, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-46, -16, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![36, 25, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-46, -16, 1], ![280, 35, -15], ![-4200, -935, 20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -25, 41]], ![![-2, -1, 1], ![20, 10, -15], ![-120, -35, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 40], [0, 1]]
 g := ![![[28, 21], [33], [9], [6, 20], [1]], ![[0, 20], [33], [9], [34, 21], [1]]]
 h' := ![![[26, 40], [25, 29], [3, 19], [29, 38], [39, 26], [0, 1]], ![[0, 1], [0, 12], [5, 22], [33, 3], [18, 15], [26, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [9, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 15, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-852, 2251, 769]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-696, -414, 769]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![15, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![15, 1, 0]] 
 ![![41, 0, 0], ![15, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![15, 1, 0], ![0, 15, 1], ![280, 81, 16]]]
  hmulB := by decide  
  f := ![![![136, 9, 0], ![-369, 0, 0]], ![![30, 2, 0], ![-81, 0, 0]], ![![66, 4, 0], ![-179, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-6, 15, 1], ![-31, 81, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-46, -16, 1]] ![![41, 0, 0], ![15, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![615, 41, 0]], ![![-1886, -656, 41], ![-410, -205, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![15, 1, 0]]], ![![![-46, -16, 1]], ![![-10, -5, 0]]]]
 hle2 := by decide  


def PBC41 : ContainsPrimesAboveP 41 ![I41N0, I41N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI41N0
    exact isPrimeI41N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 41 (by decide) (𝕀 ⊙ MulI41N0)
instance hp43 : Fact (Nat.Prime 43) := {out := by norm_num}

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-67, -27, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-67, -27, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![19, 16, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-67, -27, 1], ![280, 14, -26], ![-7280, -1826, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -16, 43]], ![![-2, -1, 1], ![18, 10, -26], ![-164, -38, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [19, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 42], [0, 1]]
 g := ![![[10, 25], [27, 10], [38], [12, 23], [1]], ![[33, 18], [19, 33], [38], [28, 20], [1]]]
 h' := ![![[25, 42], [3, 5], [6, 28], [30, 9], [24, 25], [0, 1]], ![[0, 1], [42, 38], [18, 15], [40, 34], [4, 18], [25, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [19, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [19, 18, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2683, 89, 191]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -69, 191]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-17, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-17, 1, 0]] 
 ![![43, 0, 0], ![26, 1, 0], ![12, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-17, 1, 0], ![0, -17, 1], ![280, 81, -16]]]
  hmulB := by decide  
  f := ![![![715, -42, 0], ![1806, 0, 0]], ![![426, -25, 0], ![1076, 0, 0]], ![![228, -13, 0], ![576, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 43, 0], ![-12, 0, 43]], ![![-1, 1, 0], ![10, -17, 1], ![-38, 81, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-67, -27, 1]] ![![43, 0, 0], ![-17, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-731, 43, 0]], ![![-2881, -1161, 43], ![1419, 473, -43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-17, 1, 0]]], ![![![-67, -27, 1]], ![![33, 11, -1]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [17, 23, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 43, 22], [38, 3, 25], [0, 1]]
 g := ![![[28, 39, 24], [5, 7, 1], [19, 35, 12], [14, 32, 1], []], ![[21, 16, 15, 46], [24, 1, 43, 38], [6, 11, 6, 45], [22, 13, 18, 10], [37, 14]], ![[22, 42, 3, 25], [33, 22, 10, 17], [1, 3, 26, 32], [15, 45, 27, 24], [34, 14]]]
 h' := ![![[41, 43, 22], [9, 37, 20], [6, 11, 1], [44, 27, 24], [0, 0, 1], [0, 1]], ![[38, 3, 25], [6, 41, 28], [5, 43, 10], [32, 6, 8], [18, 40, 3], [41, 43, 22]], ![[0, 1], [29, 16, 46], [21, 40, 36], [46, 14, 15], [20, 7, 43], [38, 3, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 12], []]
 b := ![[], [33, 44, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [17, 23, 15, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2716224, -1355245, -174605]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-57792, -28835, -3715]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-59, -30, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-59, -30, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![47, 23, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-59, -30, 1], ![280, 22, -29], ![-8120, -2069, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -23, 53]], ![![-2, -1, 1], ![31, 13, -29], ![-147, -36, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [9, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [12, 52], [0, 1]]
 g := ![![[34, 6], [52], [50, 38], [46], [12, 1]], ![[0, 47], [52], [29, 15], [46], [24, 52]]]
 h' := ![![[12, 52], [49, 18], [27, 30], [14, 12], [51, 29], [0, 1]], ![[0, 1], [0, 35], [16, 23], [52, 41], [28, 24], [12, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [6, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [9, 41, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![849, 482, 44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23, -10, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-24, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-24, 1, 0]] 
 ![![53, 0, 0], ![29, 1, 0], ![7, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-24, 1, 0], ![0, -24, 1], ![280, 81, -23]]]
  hmulB := by decide  
  f := ![![![1201, -50, 0], ![2650, 0, 0]], ![![649, -27, 0], ![1432, 0, 0]], ![![155, -6, 0], ![342, 1, 0]]]
  g := ![![![1, 0, 0], ![-29, 53, 0], ![-7, 0, 53]], ![![-1, 1, 0], ![13, -24, 1], ![-36, 81, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-59, -30, 1]] ![![53, 0, 0], ![-24, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-1272, 53, 0]], ![![-3127, -1590, 53], ![1696, 742, -53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-24, 1, 0]]], ![![![-59, -30, 1]], ![![32, 14, -1]]]]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![12, 1, 0]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![12, 1, 0]] 
 ![![59, 0, 0], ![12, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![12, 1, 0], ![0, 12, 1], ![280, 81, 13]]]
  hmulB := by decide  
  f := ![![![37, 3, 0], ![-177, 0, 0]], ![![-12, -1, 0], ![60, 0, 0]], ![![15, 1, 0], ![-71, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 59, 0], ![-33, 0, 59]], ![![0, 1, 0], ![-3, 12, 1], ![-19, 81, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N0 : Nat.card (O ⧸ I59N0) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N0)

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := prime_ideal_of_norm_prime hp59.out _ NI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![13, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![13, 1, 0]] 
 ![![59, 0, 0], ![13, 1, 0], ![8, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![13, 1, 0], ![0, 13, 1], ![280, 81, 14]]]
  hmulB := by decide  
  f := ![![![417, 32, 0], ![-1888, 0, 0]], ![![91, 7, 0], ![-412, 0, 0]], ![![42, 3, 0], ![-190, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 59, 0], ![-8, 0, 59]], ![![0, 1, 0], ![-3, 13, 1], ![-15, 81, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1

def I59N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![-26, 1, 0]] i)))

def SI59N2: IdealEqSpanCertificate' Table ![![59, 0, 0], ![-26, 1, 0]] 
 ![![59, 0, 0], ![33, 1, 0], ![32, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![-26, 1, 0], ![0, -26, 1], ![280, 81, -25]]]
  hmulB := by decide  
  f := ![![![963, -37, 0], ![2183, 0, 0]], ![![521, -20, 0], ![1181, 0, 0]], ![![532, -20, 0], ![1206, 1, 0]]]
  g := ![![![1, 0, 0], ![-33, 59, 0], ![-32, 0, 59]], ![![-1, 1, 0], ![14, -26, 1], ![-27, 81, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N2 : Nat.card (O ⧸ I59N2) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N2)

lemma isPrimeI59N2 : Ideal.IsPrime I59N2 := prime_ideal_of_norm_prime hp59.out _ NI59N2
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![12, 1, 0]] ![![59, 0, 0], ![13, 1, 0]]
  ![![59, 0, 0], ![-80, -34, 1]] where
 M := ![![![3481, 0, 0], ![767, 59, 0]], ![![708, 59, 0], ![156, 25, 1]]]
 hmul := by decide  
 g := ![![![![59, 0, 0], ![0, 0, 0]], ![![13, 1, 0], ![0, 0, 0]]], ![![![12, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI59N1 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![-80, -34, 1]] ![![59, 0, 0], ![-26, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![-1534, 59, 0]], ![![-4720, -2006, 59], ![2360, 885, -59]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![-26, 1, 0]]], ![![![-80, -34, 1]], ![![40, 15, -1]]]]
 hle2 := by decide  


def PBC59 : ContainsPrimesAboveP 59 ![I59N0, I59N1, I59N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI59N0
    exact isPrimeI59N1
    exact isPrimeI59N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 59 (by decide) (𝕀 ⊙ MulI59N0 ⊙ MulI59N1)
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [54, 10, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [11, 30, 40], [52, 30, 21], [0, 1]]
 g := ![![[19, 6, 58], [44, 34], [45, 27, 22], [24, 29, 4], [1]], ![[2, 15, 27, 59], [54, 58], [5, 52, 45, 32], [57, 6, 14, 17], [41, 18, 1, 11]], ![[51, 5, 0, 17], [51, 13], [21, 30, 53, 23], [48, 21, 22, 55], [7, 43, 18, 50]]]
 h' := ![![[11, 30, 40], [42, 54, 34], [10, 25, 41], [46, 12, 12], [7, 51, 2], [0, 1]], ![[52, 30, 21], [3, 57, 8], [33, 26, 34], [12, 38, 47], [32, 53, 26], [11, 30, 40]], ![[0, 1], [11, 11, 19], [52, 10, 47], [34, 11, 2], [52, 18, 33], [52, 30, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 39], []]
 b := ![[], [42, 19, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [54, 10, 59, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4333684, 1615646, 158234]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71044, 26486, 2594]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-79, -2, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-79, -2, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![55, 65, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-79, -2, 1], ![280, 2, -1], ![-280, 199, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -65, 67]], ![![-2, -1, 1], ![5, 1, -1], ![-5, 2, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [64, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 66], [0, 1]]
 g := ![![[59, 22], [66, 15], [4], [19], [40], [1]], ![[0, 45], [41, 52], [4], [19], [40], [1]]]
 h' := ![![[43, 66], [64, 25], [36, 45], [15, 65], [62, 35], [3, 43], [0, 1]], ![[0, 1], [0, 42], [28, 22], [63, 2], [26, 32], [43, 24], [43, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [15, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [64, 24, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1359, -59, 63]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, -62, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![1, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![1, 1, 0]] 
 ![![67, 0, 0], ![1, 1, 0], ![66, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![1, 1, 0], ![0, 1, 1], ![280, 81, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![67, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![66, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 67, 0], ![-66, 0, 67]], ![![0, 1, 0], ![-1, 1, 1], ![1, 81, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-79, -2, 1]] ![![67, 0, 0], ![1, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![67, 67, 0]], ![![-5293, -134, 67], ![201, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![1, 1, 0]]], ![![![-79, -2, 1]], ![![3, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [8, 0, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 16, 51], [25, 54, 20], [0, 1]]
 g := ![![[51, 34, 48], [18, 28, 58], [48, 50, 29], [55, 9], [43, 1], []], ![[28, 34, 51, 51], [37, 15, 45, 53], [2, 33, 16, 17], [11, 24], [42, 5], [17, 45]], ![[50, 28, 13, 50], [24, 61, 70, 4], [60, 36, 21, 60], [28, 48], [49, 43], [48, 45]]]
 h' := ![![[18, 16, 51], [69, 49, 30], [42, 44, 22], [36, 36, 10], [11, 63, 3], [0, 0, 1], [0, 1]], ![[25, 54, 20], [59, 22, 1], [0, 60, 24], [8, 38, 33], [5, 23, 38], [46, 3, 54], [18, 16, 51]], ![[0, 1], [4, 0, 40], [54, 38, 25], [9, 68, 28], [37, 56, 30], [28, 68, 16], [25, 54, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 54], []]
 b := ![[], [48, 7, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [8, 0, 28, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1332528, 605559, 74053]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18768, 8529, 1043]
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


def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![73, 0, 0], ![3, 1, 0], ![64, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![280, 81, 4]]]
  hmulB := by decide  
  f := ![![![-69, -4, 1]], ![![1, 0, 0]], ![![-72, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-3, 81, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, 1, 0]] 
 ![![73, 0, 0], ![71, 1, 0], ![69, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, 1, 0], ![0, -2, 1], ![280, 81, -1]]]
  hmulB := by decide  
  f := ![![![79, -39, 0], ![2847, 0, 0]], ![![77, -38, 0], ![2775, 0, 0]], ![![75, -37, 0], ![2703, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 73, 0], ![-69, 0, 73]], ![![-1, 1, 0], ![1, -2, 1], ![-74, 81, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![3, 1, 0]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0], ![-79, 1, 1]] where
 M := ![![![219, 73, 0], ![-6, 1, 1]]]
 hmul := by decide  
 g := ![![![![3, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-79, 1, 1]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-146, 73, 0]], ![![-5767, 73, 73], ![438, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-2, 1, 0]]], ![![![-79, 1, 1]], ![![6, 0, 0]]]]
 hle2 := by decide  


def PBC73 : ContainsPrimesAboveP 73 ![I73N0, I73N1, I73N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI73N0
    exact isPrimeI73N1
    exact isPrimeI73N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 73 (by decide) (𝕀 ⊙ MulI73N0 ⊙ MulI73N1)
instance hp79 : Fact (Nat.Prime 79) := {out := by norm_num}

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-39, 6, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-39, 6, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![40, 6, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-39, 6, 1], ![280, 42, 7], ![1960, 847, 49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -6, 79]], ![![-1, 0, 1], ![0, 0, 7], ![0, 7, 49]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [59, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 78], [0, 1]]
 g := ![![[62, 62], [70, 40], [54, 46], [59, 42], [23], [1]], ![[75, 17], [58, 39], [56, 33], [78, 37], [23], [1]]]
 h' := ![![[55, 78], [57, 33], [53, 44], [74, 58], [70, 68], [20, 55], [0, 1]], ![[0, 1], [55, 46], [24, 35], [25, 21], [18, 11], [43, 24], [55, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [78, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [59, 24, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9969, -2076, 444]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-351, -60, 444]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-7, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-7, 1, 0]] 
 ![![79, 0, 0], ![72, 1, 0], ![30, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-7, 1, 0], ![0, -7, 1], ![280, 81, -6]]]
  hmulB := by decide  
  f := ![![![267, -38, 0], ![3002, 0, 0]], ![![246, -35, 0], ![2766, 0, 0]], ![![106, -15, 0], ![1192, 1, 0]]]
  g := ![![![1, 0, 0], ![-72, 79, 0], ![-30, 0, 79]], ![![-1, 1, 0], ![6, -7, 1], ![-68, 81, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-39, 6, 1]] ![![79, 0, 0], ![-7, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-553, 79, 0]], ![![-3081, 474, 79], ![553, 0, 0]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-7, 1, 0]]], ![![![-39, 6, 1]], ![![7, 0, 0]]]]
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


lemma PB178I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB178I1 : PrimesBelowBoundCertificateInterval O 31 79 178 where
  m := 11
  g := ![1, 2, 2, 1, 2, 3, 1, 2, 1, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB178I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0, I59N1, I59N2]
    · exact ![I61N0]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0, I73N1, I73N1]
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
    · exact ![1681, 41]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![59, 59, 59]
    · exact ![226981]
    · exact ![4489, 67]
    · exact ![357911]
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
      exact NI41N1
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
      exact NI59N1
      exact NI59N2
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
  β := ![I41N1, I43N1, I53N1, I59N0, I59N1, I59N2, I67N1, I73N0, I73N1, I79N1]
  Il := ![[], [I41N1], [I43N1], [], [I53N1], [I59N0, I59N1, I59N2], [], [I67N1], [], [I73N0, I73N1, I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
