
import IdealArithmetic.Examples.NF3_1_378695_1.RI3_1_378695_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, -11, -2]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, -11, -2]] 
 ![![37, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![37, -11, -2], ![370, -55, -13], ![2405, -228, -68]]]
  hmulB := by decide  
  f := ![![![776, -292, 33]], ![![-165, 62, -7]], ![![1295, -487, 55]]]
  g := ![![![1, -11, -2], ![10, -55, -13], ![65, -228, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N0 : Nat.card (O ⧸ I37N0) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N0)

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := prime_ideal_of_norm_prime hp37.out _ NI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![572, -45, -15]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![572, -45, -15]] 
 ![![37, 0, 0], ![18, 1, 0], ![9, 0, 1]] where
  M :=![![![572, -45, -15], ![2775, -118, -60], ![11100, 15, -178]]]
  hmulB := by decide  
  f := ![![![-21904, 8235, -930]], ![![-6006, 2258, -255]], ![![-41853, 15735, -1777]]]
  g := ![![![41, -45, -15], ![147, -118, -60], ![336, 15, -178]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, -11, -2]] ![![572, -45, -15]]
  ![![-31561, -397, 461]] where
 M := ![![![-31561, -397, 461]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI37N1 : IdealMulLeCertificate' Table 
  ![![-31561, -397, 461]] ![![572, -45, -15]]
  ![![37, 0, 0]] where
 M := ![![![-14037467, 1474006, 415177]]]
 hmul := by decide  
 g := ![![![![-379391, 39838, 11221]]]]
 hle2 := by decide  


def PBC37 : ContainsPrimesAboveP 37 ![I37N0, I37N1, I37N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI37N0
    exact isPrimeI37N1
    exact isPrimeI37N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 37 (by decide) (𝕀 ⊙ MulI37N0 ⊙ MulI37N1)
instance hp41 : Fact (Nat.Prime 41) := {out := by norm_num}

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![-34, -4, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![-34, -4, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![7, 37, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![-34, -4, 1], ![-185, 12, -3], ![555, -323, 9]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -37, 41]], ![![-1, -1, 1], ![-4, 3, -3], ![12, -16, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [2, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 40], [0, 1]]
 g := ![![[3, 21], [18], [37], [13, 36], [1]], ![[0, 20], [18], [37], [2, 5], [1]]]
 h' := ![![[35, 40], [10, 29], [28, 31], [15, 18], [39, 35], [0, 1]], ![[0, 1], [0, 12], [6, 10], [30, 23], [34, 6], [35, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [32, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [2, 6, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-553, -53, 44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -41, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![3, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![3, 1, 0]] 
 ![![41, 0, 0], ![3, 1, 0], ![32, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![3, 1, 0], ![0, 3, 1], ![-185, 46, 4]]]
  hmulB := by decide  
  f := ![![![37, 12, 0], ![-492, 0, 0]], ![![-3, -1, 0], ![42, 0, 0]], ![![28, 9, 0], ![-372, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 41, 0], ![-32, 0, 41]], ![![0, 1, 0], ![-1, 3, 1], ![-11, 46, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-34, -4, 1]] ![![41, 0, 0], ![3, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![123, 41, 0]], ![![-1394, -164, 41], ![-287, 0, 0]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![3, 1, 0]]], ![![![-34, -4, 1]], ![![-7, 0, 0]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0]] 
 ![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 3 2 5 [1, 9, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 14, 39], [26, 28, 4], [0, 1]]
 g := ![![[10, 22, 35], [30, 8, 40], [27, 13], [32, 16, 1], []], ![[35, 2, 20, 32], [18, 13, 15, 37], [33, 35], [15, 10, 25, 3], [15, 16]], ![[20, 14, 5, 1], [17, 29, 16, 17], [26, 38], [0, 22, 41, 10], [7, 16]]]
 h' := ![![[33, 14, 39], [13, 1, 32], [8, 22, 13], [11, 40, 23], [0, 0, 1], [0, 1]], ![[26, 28, 4], [14, 25, 32], [33, 37, 18], [18, 21, 11], [42, 42, 28], [33, 14, 39]], ![[0, 1], [33, 17, 22], [32, 27, 12], [12, 25, 9], [24, 1, 14], [26, 28, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36], []]
 b := ![[], [25, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 3
  hpos := by decide
  P := [1, 9, 27, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![937228, -504347, 67381]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21796, -11729, 1567]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-9, -17, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-9, -17, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![38, 30, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-9, -17, 1], ![-185, 37, -16], ![2960, -921, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -30, 47]], ![![-1, -1, 1], ![9, 11, -16], ![46, -33, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [39, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 46], [0, 1]]
 g := ![![[30, 32], [23, 25], [14, 24], [17, 25], [1]], ![[2, 15], [7, 22], [40, 23], [1, 22], [1]]]
 h' := ![![[5, 46], [43, 28], [18, 5], [42, 20], [8, 5], [0, 1]], ![[0, 1], [42, 19], [43, 42], [1, 27], [33, 42], [5, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [24, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [39, 42, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1632, -317, 132]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, -91, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![16, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![16, 1, 0]] 
 ![![47, 0, 0], ![16, 1, 0], ![26, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![16, 1, 0], ![0, 16, 1], ![-185, 46, 17]]]
  hmulB := by decide  
  f := ![![![17, 1, 0], ![-47, 0, 0]], ![![-16, -1, 0], ![48, 0, 0]], ![![6, 0, 0], ![-16, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 47, 0], ![-26, 0, 47]], ![![0, 1, 0], ![-6, 16, 1], ![-29, 46, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-9, -17, 1]] ![![47, 0, 0], ![16, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![752, 47, 0]], ![![-423, -799, 47], ![-329, -235, 0]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![16, 1, 0]]], ![![![-9, -17, 1]], ![![-7, -5, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![2, 1, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![2, 1, 0]] 
 ![![53, 0, 0], ![2, 1, 0], ![49, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![2, 1, 0], ![0, 2, 1], ![-185, 46, 3]]]
  hmulB := by decide  
  f := ![![![51, 25, 0], ![-1325, 0, 0]], ![![-2, -1, 0], ![54, 0, 0]], ![![47, 23, 0], ![-1221, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 53, 0], ![-49, 0, 53]], ![![0, 1, 0], ![-1, 2, 1], ![-8, 46, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28, -20, -3]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![28, -20, -3]] 
 ![![53, 0, 0], ![5, 1, 0], ![28, 0, 1]] where
  M :=![![![28, -20, -3], ![555, -110, -23], ![4255, -503, -133]]]
  hmulB := by decide  
  f := ![![![3061, -1151, 130]], ![![-165, 62, -7]], ![![5181, -1948, 220]]]
  g := ![![![4, -20, -3], ![33, -110, -23], ![198, -503, -133]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-8, 1, 0]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-8, 1, 0]] 
 ![![53, 0, 0], ![45, 1, 0], ![42, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-8, 1, 0], ![0, -8, 1], ![-185, 46, -7]]]
  hmulB := by decide  
  f := ![![![193, -24, 0], ![1272, 0, 0]], ![![169, -21, 0], ![1114, 0, 0]], ![![162, -20, 0], ![1068, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 53, 0], ![-42, 0, 53]], ![![-1, 1, 0], ![6, -8, 1], ![-37, 46, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![2, 1, 0]] ![![28, -20, -3]]
  ![![53, 0, 0], ![-43, 7, 1]] where
 M := ![![![1484, -1060, -159]], ![![611, -150, -29]]]
 hmul := by decide  
 g := ![![![![28, -20, -3], ![0, 0, 0]]], ![![![31, -6, -1], ![24, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![-43, 7, 1]] ![![53, 0, 0], ![-8, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-424, 53, 0]], ![![-2279, 371, 53], ![159, -53, 0]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-8, 1, 0]]], ![![![-43, 7, 1]], ![![3, -1, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [1, 11, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 15, 27], [54, 43, 32], [0, 1]]
 g := ![![[34, 25, 36], [1, 43, 36], [0, 20], [30, 8, 46], [1]], ![[46, 35, 25, 25], [17, 39, 52, 16], [6, 27], [25, 15, 31, 36], [35, 17, 13, 36]], ![[33, 45, 22, 39], [30, 45, 24, 24], [46, 53], [56, 56, 54, 34], [44, 9, 42, 23]]]
 h' := ![![[25, 15, 27], [58, 53, 53], [15, 22, 53], [29, 17, 16], [58, 48, 20], [0, 1]], ![[54, 43, 32], [57, 16, 52], [6, 23, 41], [37, 51, 26], [14, 52, 32], [25, 15, 27]], ![[0, 1], [31, 49, 13], [25, 14, 24], [37, 50, 17], [8, 18, 7], [54, 43, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 11], []]
 b := ![[], [54, 13, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [1, 11, 39, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-716083, 339663, -36521]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12137, 5757, -619]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-32, -20, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-32, -20, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![29, 41, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-32, -20, 1], ![-185, 14, -19], ![3515, -1059, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -41, 61]], ![![-1, -1, 1], ![6, 13, -19], ![60, -14, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [47, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 60], [0, 1]]
 g := ![![[9, 13], [16], [20, 57], [6, 46], [4, 1]], ![[0, 48], [16], [4, 4], [7, 15], [8, 60]]]
 h' := ![![[4, 60], [56, 47], [36, 4], [23, 22], [56, 30], [0, 1]], ![[0, 1], [0, 14], [52, 57], [50, 39], [54, 31], [4, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [17, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [47, 57, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-508, -104, -7]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, 3, -7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![19, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![19, 1, 0]] 
 ![![61, 0, 0], ![19, 1, 0], ![5, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![19, 1, 0], ![0, 19, 1], ![-185, 46, 20]]]
  hmulB := by decide  
  f := ![![![476, 25, 0], ![-1525, 0, 0]], ![![152, 8, 0], ![-487, 0, 0]], ![![6, 0, 0], ![-19, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 61, 0], ![-5, 0, 61]], ![![0, 1, 0], ![-6, 19, 1], ![-19, 46, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-32, -20, 1]] ![![61, 0, 0], ![19, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![1159, 61, 0]], ![![-1952, -1220, 61], ![-793, -366, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![19, 1, 0]]], ![![![-32, -20, 1]], ![![-13, -6, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [29, 66, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 29, 20], [35, 37, 47], [0, 1]]
 g := ![![[55, 53, 47], [66, 22, 4], [44, 65], [39, 59], [48, 1], []], ![[53, 41, 38, 34], [16, 42, 53, 2], [65, 36], [9, 47], [52, 29], [59, 65]], ![[4, 14, 4, 33], [36, 44, 21, 23], [53, 6], [47, 1], [34, 37], [32, 65]]]
 h' := ![![[13, 29, 20], [29, 19, 39], [16, 58, 2], [32, 37, 20], [15, 19, 27], [0, 0, 1], [0, 1]], ![[35, 37, 47], [36, 15, 14], [31, 7, 28], [24, 1, 6], [34, 15, 39], [66, 0, 37], [13, 29, 20]], ![[0, 1], [16, 33, 14], [27, 2, 37], [31, 29, 41], [56, 33, 1], [29, 0, 29], [35, 37, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 21], []]
 b := ![[], [40, 3, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [29, 66, 19, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2106480, 302170, 64320]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31440, 4510, 960]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0]] 
 ![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [23, 18, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 11, 53], [33, 59, 18], [0, 1]]
 g := ![![[24, 24, 10], [34, 67, 4], [10, 23, 36], [36, 38], [49, 1], []], ![[4, 32, 44, 51], [3, 62, 70, 69], [30, 63, 3, 34], [54, 32], [39, 2], [2, 40]], ![[45, 3, 62, 36], [50, 7, 24, 27], [30, 30, 29, 32], [22, 5], [47, 50], [37, 40]]]
 h' := ![![[16, 11, 53], [70, 53, 9], [54, 21, 2], [34, 9, 65], [9, 18, 40], [0, 0, 1], [0, 1]], ![[33, 59, 18], [39, 46, 3], [29, 17, 24], [54, 31, 52], [35, 36, 48], [68, 35, 59], [16, 11, 53]], ![[0, 1], [56, 43, 59], [16, 33, 45], [39, 31, 25], [41, 17, 54], [25, 36, 11], [33, 59, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 14], []]
 b := ![[], [30, 27, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [23, 18, 22, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-77674, 27761, -2982]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1094, 391, -42]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-66, -17, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-66, -17, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![7, 56, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-66, -17, 1], ![-185, -20, -16], ![2960, -921, -36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -56, 73]], ![![-1, -1, 1], ![-1, 12, -16], ![44, 15, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [3, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 72], [0, 1]]
 g := ![![[30, 49], [37], [35], [3, 49], [70], [1]], ![[0, 24], [37], [35], [46, 24], [70], [1]]]
 h' := ![![[56, 72], [27, 66], [49, 57], [64, 53], [18, 7], [70, 56], [0, 1]], ![[0, 1], [0, 7], [29, 16], [39, 20], [45, 66], [67, 17], [56, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [6, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [3, 17, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1477, -355, 227]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -179, 227]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![16, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![16, 1, 0]] 
 ![![73, 0, 0], ![16, 1, 0], ![36, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![16, 1, 0], ![0, 16, 1], ![-185, 46, 17]]]
  hmulB := by decide  
  f := ![![![417, 26, 0], ![-1898, 0, 0]], ![![80, 5, 0], ![-364, 0, 0]], ![![196, 12, 0], ![-892, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 73, 0], ![-36, 0, 73]], ![![0, 1, 0], ![-4, 16, 1], ![-21, 46, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-66, -17, 1]] ![![73, 0, 0], ![16, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1168, 73, 0]], ![![-4818, -1241, 73], ![-1241, -292, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![16, 1, 0]]], ![![![-66, -17, 1]], ![![-17, -4, 0]]]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [3, 67, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 42, 10], [61, 36, 69], [0, 1]]
 g := ![![[65, 69, 36], [39, 56, 22], [71, 75, 32], [67, 54, 40], [24, 1], []], ![[49, 66, 76, 18], [24, 70, 16, 8], [52, 43, 30, 13], [20, 7, 60, 40], [50, 32], [1, 21]], ![[11, 7, 74, 35], [51, 33, 5, 6], [5, 41, 42, 28], [2, 54, 27, 56], [66, 26], [21, 21]]]
 h' := ![![[42, 42, 10], [41, 7, 73], [24, 27, 41], [36, 59, 43], [7, 48, 35], [0, 0, 1], [0, 1]], ![[61, 36, 69], [39, 51, 12], [47, 69, 8], [27, 72, 5], [63, 76, 2], [23, 1, 36], [42, 42, 10]], ![[0, 1], [8, 21, 73], [48, 62, 30], [6, 27, 31], [62, 34, 42], [24, 78, 42], [61, 36, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 51], []]
 b := ![[], [67, 43, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [3, 67, 55, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1660185, -619202, 69046]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21015, -7838, 874]
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



lemma PB175I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB175I1 : PrimesBelowBoundCertificateInterval O 31 79 175 where
  m := 11
  g := ![3, 2, 1, 2, 3, 1, 2, 1, 1, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB175I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0]
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
    · exact ![37, 37, 37]
    · exact ![1681, 41]
    · exact ![79507]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![357911]
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
      exact NI37N1
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
      exact NI41N0
      exact NI41N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
    · dsimp ; intro j
      fin_cases j
      exact NI73N0
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I37N0, I37N1, I41N1, I47N1, I53N0, I53N1, I53N2, I61N1, I73N1]
  Il := ![[I37N0, I37N1, I37N1], [I41N1], [], [I47N1], [I53N0, I53N1, I53N2], [], [I61N1], [], [], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
