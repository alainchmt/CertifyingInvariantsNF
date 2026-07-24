
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![33, -5, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![33, -5, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![33, 32, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![33, -5, 1], ![56, -4, -14], ![-207, 213, -13]]]
  hmulB := by decide  
  f := ![![![-32, 5, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -32, 37]], ![![0, -1, 1], ![14, 12, -14], ![6, 17, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [30, 10, 1] where
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
 g := ![![[25, 21], [36], [6, 12], [26], [1]], ![[0, 16], [36], [34, 25], [26], [1]]]
 h' := ![![[27, 36], [18, 24], [5, 31], [9, 7], [7, 27], [0, 1]], ![[0, 1], [0, 13], [28, 6], [13, 30], [33, 10], [27, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [19, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [30, 10, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![473, 27, -405]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![374, 351, -405]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![-1, 13, 3], ![51, -42, 15]]]
  hmulB := by decide  
  f := ![![![-239, 3120, 720], ![0, -8880, 0]], ![![-90, 1170, 270], ![1, -3330, 0]], ![![-87, 1096, 253], ![8, -3120, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-13, 0, 37]], ![![0, 1, 0], ![-6, 13, 3], ![12, -42, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![33, -5, 1]] ![![37, 0, 0], ![14, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![518, 37, 0]], ![![1221, -185, 37], ![518, -74, 0]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![14, 1, 0]]], ![![![33, -5, 1]], ![![14, -2, 0]]]]
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


def P41P0 : CertificateIrreducibleZModOfList' 41 3 2 5 [7, 14, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 6, 38], [8, 34, 3], [0, 1]]
 g := ![![[27, 7, 1], [20, 31], [35, 10], [29, 24, 1], []], ![[10, 0, 34, 29], [14, 10], [9, 39], [19, 17, 33, 17], [16, 9]], ![[29, 12, 8, 3], [21, 16], [32, 32], [33, 13, 20, 26], [10, 9]]]
 h' := ![![[16, 6, 38], [8, 12, 1], [5, 14, 21], [2, 0, 25], [0, 0, 1], [0, 1]], ![[8, 34, 3], [16, 18, 39], [14, 16, 16], [35, 3, 30], [21, 28, 34], [16, 6, 38]], ![[0, 1], [16, 11, 1], [32, 11, 4], [16, 38, 27], [35, 13, 6], [8, 34, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25, 14], []]
 b := ![[], [25, 18, 32], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 3
  hpos := by decide
  P := [7, 14, 17, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1109337, -1748937, 820984]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27057, -42657, 20024]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![16, 13, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![16, 13, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![16, 13, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![16, 13, 1], ![38, -39, 40], ![711, -543, -12]]]
  hmulB := by decide  
  f := ![![![-15, -13, -1], ![43, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -13, 43]], ![![0, 0, 1], ![-14, -13, 40], ![21, -9, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [37, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 42], [0, 1]]
 g := ![![[13, 9], [6, 15], [25], [37, 21], [1]], ![[27, 34], [15, 28], [25], [41, 22], [1]]]
 h' := ![![[35, 42], [36, 40], [27, 31], [7, 38], [6, 35], [0, 1]], ![[0, 1], [17, 3], [37, 12], [4, 5], [27, 8], [35, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [39, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [37, 8, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201846, 24739, -184975]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73522, 56498, -184975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![3, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![3, 1, 0]] 
 ![![43, 0, 0], ![3, 1, 0], ![12, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![3, 1, 0], ![-1, 2, 3], ![51, -42, 4]]]
  hmulB := by decide  
  f := ![![![-724, 1450, 2175], ![0, -31175, 0]], ![![-50, 100, 150], ![1, -2150, 0]], ![![-204, 404, 607], ![28, -8700, 0]]]
  g := ![![![1, 0, 0], ![-3, 43, 0], ![-12, 0, 43]], ![![0, 1, 0], ![-1, 2, 3], ![3, -42, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![16, 13, 1]] ![![43, 0, 0], ![3, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![129, 43, 0]], ![![688, 559, 43], ![86, 0, 43]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![3, 1, 0]]], ![![![16, 13, 1]], ![![2, 0, 1]]]]
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


def P47P0 : CertificateIrreducibleZModOfList' 47 3 2 5 [43, 14, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 40, 34], [30, 6, 13], [0, 1]]
 g := ![![[8, 32, 36], [5, 44, 34], [5, 27, 4], [23, 15, 1], []], ![[6, 11, 2, 28], [35, 32, 4, 6], [8, 1, 13, 16], [10, 24, 14, 2], [38, 28]], ![[8, 38, 1, 23], [14, 15, 43, 35], [23, 8, 17, 33], [18, 25, 17, 26], [12, 28]]]
 h' := ![![[32, 40, 34], [20, 36, 6], [20, 42, 9], [45, 20, 45], [0, 0, 1], [0, 1]], ![[30, 6, 13], [3, 39, 38], [10, 25, 25], [25, 45, 10], [1, 25, 6], [32, 40, 34]], ![[0, 1], [20, 19, 3], [36, 27, 13], [18, 29, 39], [8, 22, 40], [30, 6, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 8], []]
 b := ![[], [4, 5, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 3
  hpos := by decide
  P := [43, 14, 32, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-712896, 1575252, -973464]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15168, 33516, -20712]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![43, 18, 1]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0], ![43, 18, 1]] 
 ![![53, 0, 0], ![0, 53, 0], ![43, 18, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![43, 18, 1], ![33, -17, 55], ![966, -753, 20]]]
  hmulB := by decide  
  f := ![![![-42, -18, -1], ![53, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -18, 53]], ![![0, 0, 1], ![-44, -19, 55], ![2, -21, 20]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 2 2 5 [22, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 52], [0, 1]]
 g := ![![[22, 11], [13], [24, 29], [40], [46, 1]], ![[51, 42], [13], [33, 24], [40], [39, 52]]]
 h' := ![![[46, 52], [36, 8], [2, 38], [46, 33], [48, 27], [0, 1]], ![[0, 1], [33, 45], [1, 15], [27, 20], [18, 26], [46, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [26, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 2
  hpos := by decide
  P := [22, 7, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![462, 27, -396]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![330, 135, -396]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 2809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0], ![-2, 1, 0]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![53, 0, 0], ![-2, 1, 0]] 
 ![![53, 0, 0], ![51, 1, 0], ![33, 0, 1]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]], ![![-2, 1, 0], ![-1, -3, 3], ![51, -42, -1]]]
  hmulB := by decide  
  f := ![![![-779, -2340, 2340], ![0, -41340, 0]], ![![-749, -2250, 2250], ![1, -39750, 0]], ![![-485, -1457, 1457], ![1, -25740, 0]]]
  g := ![![![1, 0, 0], ![-51, 53, 0], ![-33, 0, 53]], ![![-1, 1, 0], ![1, -3, 3], ![42, -42, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![53, 0, 0], ![43, 18, 1]] ![![53, 0, 0], ![-2, 1, 0]]
  ![![53, 0, 0]] where
 M := ![![![2809, 0, 0], ![-106, 53, 0]], ![![2279, 954, 53], ![-53, -53, 53]]]
 hmul := by decide  
 g := ![![![![53, 0, 0]], ![![-2, 1, 0]]], ![![![43, 18, 1]], ![![-1, -1, 1]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [44, 57, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 33, 27], [6, 25, 32], [0, 1]]
 g := ![![[52, 54, 27], [51, 22, 15], [15, 4], [16, 32, 7], [1]], ![[44, 48, 26, 25], [56, 53, 5, 48], [38, 49], [10, 52, 46, 49], [52, 56, 49, 36]], ![[3, 30, 46, 47], [13, 26, 44, 42], [11, 22], [58, 36, 29, 44], [18, 4, 6, 23]]]
 h' := ![![[13, 33, 27], [57, 44, 33], [5, 27, 29], [4, 29, 2], [15, 2, 19], [0, 1]], ![[6, 25, 32], [24, 27, 7], [21, 41, 38], [10, 50, 7], [27, 34, 57], [13, 33, 27]], ![[0, 1], [50, 47, 19], [54, 50, 51], [40, 39, 50], [14, 23, 42], [6, 25, 32]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 11], []]
 b := ![[], [9, 12, 28], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [44, 57, 40, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-377482, 739860, -385860]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6398, 12540, -6540]
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


def P61P0 : CertificateIrreducibleZModOfList' 61 3 2 5 [10, 39, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 33, 59], [46, 27, 2], [0, 1]]
 g := ![![[26, 52, 1], [6, 22], [57, 60, 12], [34, 16, 46], [1]], ![[50, 17, 50, 11], [32, 19], [40, 19, 60, 8], [39, 26, 39, 6], [48, 35, 34, 53]], ![[6, 56, 25, 11], [28, 36], [47, 15, 4, 11], [46, 33, 46, 18], [36, 1, 15, 8]]]
 h' := ![![[45, 33, 59], [15, 50, 60], [40, 49, 12], [26, 17, 45], [51, 22, 30], [0, 1]], ![[46, 27, 2], [59, 21, 56], [47, 59, 43], [21, 56, 22], [60, 3, 34], [45, 33, 59]], ![[0, 1], [39, 51, 6], [21, 14, 6], [16, 49, 55], [47, 36, 58], [46, 27, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 45], []]
 b := ![[], [57, 57, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 3
  hpos := by decide
  P := [10, 39, 31, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-323727, 384544, -115168]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5307, 6304, -1888]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![64, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![-1, -29, 3], ![51, -42, -27]]]
  hmulB := by decide  
  f := ![![![-2694, -78155, 8085], ![0, -180565, 0]], ![![-1567, -45472, 4704], ![1, -105056, 0]], ![![-2560, -74656, 7723], ![32, -172480, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-64, 0, 67]], ![![-1, 1, 0], ![14, -29, 3], ![51, -42, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-22, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-22, 1, 0]] 
 ![![67, 0, 0], ![45, 1, 0], ![32, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-22, 1, 0], ![-1, -23, 3], ![51, -42, -21]]]
  hmulB := by decide  
  f := ![![![194, 3932, -513], ![67, 11457, 0]], ![![137, 2621, -342], ![68, 7638, 0]], ![![92, 1878, -245], ![30, 5472, 0]]]
  g := ![![![1, 0, 0], ![-45, 67, 0], ![-32, 0, 67]], ![![-1, 1, 0], ![14, -23, 3], ![39, -42, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-17, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-17, 1, 0]] 
 ![![67, 0, 0], ![50, 1, 0], ![54, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-17, 1, 0], ![-1, -18, 3], ![51, -42, -16]]]
  hmulB := by decide  
  f := ![![![-188, -3402, 567], ![0, -12663, 0]], ![![-140, -2538, 423], ![1, -9447, 0]], ![![-150, -2742, 457], ![6, -10206, 0]]]
  g := ![![![1, 0, 0], ![-50, 67, 0], ![-54, 0, 67]], ![![-1, 1, 0], ![11, -18, 3], ![45, -42, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-28, 1, 0]] ![![67, 0, 0], ![-22, 1, 0]]
  ![![67, 0, 0], ![4, -17, 1]] where
 M := ![![![4489, 0, 0], ![-1474, 67, 0]], ![![-1876, 67, 0], ![615, -51, 3]]]
 hmul := by decide  
 g := ![![![![63, 17, -1], ![67, 0, 0]], ![![-22, 1, 0], ![0, 0, 0]]], ![![![-28, 1, 0], ![0, 0, 0]], ![![9, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![4, -17, 1]] ![![67, 0, 0], ![-17, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-1139, 67, 0]], ![![268, -1139, 67], ![0, 268, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-17, 1, 0]]], ![![![4, -17, 1]], ![![0, 4, -1]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![10, 1, 0]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![71, 0, 0], ![10, 1, 0]] 
 ![![71, 0, 0], ![10, 1, 0], ![17, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![10, 1, 0], ![-1, 9, 3], ![51, -42, 11]]]
  hmulB := by decide  
  f := ![![![2231, -20161, -6720], ![71, 159040, 0]], ![![305, -2836, -945], ![72, 22365, 0]], ![![527, -4828, -1609], ![68, 38080, 0]]]
  g := ![![![1, 0, 0], ![-10, 71, 0], ![-17, 0, 71]], ![![0, 1, 0], ![-2, 9, 3], ![4, -42, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-20, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-20, 1, 0]] 
 ![![71, 0, 0], ![51, 1, 0], ![49, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-20, 1, 0], ![-1, -21, 3], ![51, -42, -19]]]
  hmulB := by decide  
  f := ![![![-155, -3276, 468], ![0, -11076, 0]], ![![-111, -2352, 336], ![1, -7952, 0]], ![![-105, -2261, 323], ![7, -7644, 0]]]
  g := ![![![1, 0, 0], ![-51, 71, 0], ![-49, 0, 71]], ![![-1, 1, 0], ![13, -21, 3], ![44, -42, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![10, 1, 0]] ![![71, 0, 0], ![10, 1, 0]]
  ![![71, 0, 0], ![33, 30, 1]] where
 M := ![![![5041, 0, 0], ![710, 71, 0]], ![![710, 71, 0], ![99, 19, 3]]]
 hmul := by decide  
 g := ![![![![38, -30, -1], ![71, 0, 0]], ![![-23, -29, -1], ![71, 0, 0]]], ![![![-23, -29, -1], ![71, 0, 0]], ![![0, -1, 0], ![3, 0, 0]]]]
 hle2 := by decide  
def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![33, 30, 1]] ![![71, 0, 0], ![-20, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-1420, 71, 0]], ![![2343, 2130, 71], ![-639, -639, 71]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-20, 1, 0]]], ![![![33, 30, 1]], ![![-9, -9, 1]]]]
 hle2 := by decide  


def PBC71 : ContainsPrimesAboveP 71 ![I71N0, I71N0, I71N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI71N0
    exact isPrimeI71N0
    exact isPrimeI71N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 71 (by decide) (𝕀 ⊙ MulI71N0 ⊙ MulI71N1)
instance hp73 : Fact (Nat.Prime 73) := {out := by norm_num}

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-32, 1, 0]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-32, 1, 0]] 
 ![![73, 0, 0], ![41, 1, 0], ![37, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-32, 1, 0], ![-1, -33, 3], ![51, -42, -31]]]
  hmulB := by decide  
  f := ![![![-3989, -131670, 11970], ![0, -291270, 0]], ![![-2239, -73920, 6720], ![1, -163520, 0]], ![![-2017, -66737, 6067], ![11, -147630, 0]]]
  g := ![![![1, 0, 0], ![-41, 73, 0], ![-37, 0, 73]], ![![-1, 1, 0], ![17, -33, 3], ![40, -42, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N0 : Nat.card (O ⧸ I73N0) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N0)

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := prime_ideal_of_norm_prime hp73.out _ NI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-21, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-21, 1, 0]] 
 ![![73, 0, 0], ![52, 1, 0], ![16, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-21, 1, 0], ![-1, -22, 3], ![51, -42, -20]]]
  hmulB := by decide  
  f := ![![![-329, -7260, 990], ![0, -24090, 0]], ![![-234, -5170, 705], ![1, -17155, 0]], ![![-56, -1592, 217], ![56, -5280, 0]]]
  g := ![![![1, 0, 0], ![-52, 73, 0], ![-16, 0, 73]], ![![-1, 1, 0], ![15, -22, 3], ![35, -42, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1

def I73N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-20, 1, 0]] i)))

def SI73N2: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-20, 1, 0]] 
 ![![73, 0, 0], ![53, 1, 0], ![30, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-20, 1, 0], ![-1, -21, 3], ![51, -42, -19]]]
  hmulB := by decide  
  f := ![![![-3533, -74214, 10602], ![0, -257982, 0]], ![![-2564, -53865, 7695], ![1, -187245, 0]], ![![-1450, -30499, 4357], ![7, -106020, 0]]]
  g := ![![![1, 0, 0], ![-53, 73, 0], ![-30, 0, 73]], ![![-1, 1, 0], ![14, -21, 3], ![39, -42, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N2 : Nat.card (O ⧸ I73N2) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N2)

lemma isPrimeI73N2 : Ideal.IsPrime I73N2 := prime_ideal_of_norm_prime hp73.out _ NI73N2
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-32, 1, 0]] ![![73, 0, 0], ![-21, 1, 0]]
  ![![73, 0, 0], ![29, -18, 1]] where
 M := ![![![5329, 0, 0], ![-1533, 73, 0]], ![![-2336, 73, 0], ![671, -54, 3]]]
 hmul := by decide  
 g := ![![![![44, 18, -1], ![73, 0, 0]], ![![-21, 1, 0], ![0, 0, 0]]], ![![![-32, 1, 0], ![0, 0, 0]], ![![-21, 18, -1], ![76, 0, 0]]]]
 hle2 := by decide  

def MulI73N1 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![29, -18, 1]] ![![73, 0, 0], ![-20, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-1460, 73, 0]], ![![2117, -1314, 73], ![-511, 365, -73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-20, 1, 0]]], ![![![29, -18, 1]], ![![-7, 5, -1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![30, -18, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![30, -18, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![30, 61, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![30, -18, 1], ![69, 6, -53], ![-870, 759, -29]]]
  hmulB := by decide  
  f := ![![![-29, 18, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -61, 79]], ![![0, -1, 1], ![21, 41, -53], ![0, 32, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [43, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 78], [0, 1]]
 g := ![![[75, 55], [21, 50], [32, 45], [65, 20], [38], [1]], ![[55, 24], [10, 29], [30, 34], [29, 59], [38], [1]]]
 h' := ![![[14, 78], [45, 23], [46, 45], [49, 60], [57, 39], [36, 14], [0, 1]], ![[0, 1], [51, 56], [44, 34], [20, 19], [50, 40], [74, 65], [14, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [73, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [43, 65, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1032, 550, -1119]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![438, 871, -1119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-26, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-26, 1, 0]] 
 ![![79, 0, 0], ![53, 1, 0], ![29, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-26, 1, 0], ![-1, -27, 3], ![51, -42, -25]]]
  hmulB := by decide  
  f := ![![![195, 4535, -504], ![79, 13272, 0]], ![![139, 3023, -336], ![80, 8848, 0]], ![![65, 1665, -185], ![9, 4872, 0]]]
  g := ![![![1, 0, 0], ![-53, 79, 0], ![-29, 0, 79]], ![![-1, 1, 0], ![17, -27, 3], ![38, -42, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![30, -18, 1]] ![![79, 0, 0], ![-26, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-2054, 79, 0]], ![![2370, -1422, 79], ![-711, 474, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-26, 1, 0]]], ![![![30, -18, 1]], ![![-9, 6, -1]]]]
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


lemma PB278I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB278I1 : PrimesBelowBoundCertificateInterval O 31 79 278 where
  m := 11
  g := ![2, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB278I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0]
    · exact ![I43N0, I43N1]
    · exact ![I47N0]
    · exact ![I53N0, I53N1]
    · exact ![I59N0]
    · exact ![I61N0]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N0, I71N1]
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
    · exact ![68921]
    · exact ![1849, 43]
    · exact ![103823]
    · exact ![2809, 53]
    · exact ![205379]
    · exact ![226981]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
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
      exact NI67N1
      exact NI67N2
    · dsimp ; intro j
      fin_cases j
      exact NI71N0
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
  β := ![I37N1, I43N1, I53N1, I67N0, I67N1, I67N2, I71N0, I71N1, I73N0, I73N1, I73N2, I79N1]
  Il := ![[I37N1], [], [I43N1], [], [I53N1], [], [], [I67N0, I67N1, I67N2], [I71N0, I71N0, I71N1], [I73N0, I73N1, I73N2], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
