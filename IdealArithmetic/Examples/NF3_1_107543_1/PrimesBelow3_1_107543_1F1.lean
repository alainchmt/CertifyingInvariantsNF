
import IdealArithmetic.Examples.NF3_1_107543_1.RI3_1_107543_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [36, 33, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 35, 1], [3, 1, 36], [0, 1]]
 g := ![![[35, 13, 4], [21, 26], [25, 1, 25], [1, 1], []], ![[35, 24, 6, 25], [17, 28], [28, 35, 29, 26], [32, 1], [34, 1]], ![[12, 29, 6, 28], [22, 27], [19, 19, 8, 34], [29, 4], [36, 1]]]
 h' := ![![[35, 35, 1], [17, 30, 2], [25, 28, 27], [1, 5, 5], [0, 0, 1], [0, 1]], ![[3, 1, 36], [33, 8, 32], [33, 11, 18], [33, 12, 10], [1, 34, 1], [35, 35, 1]], ![[0, 1], [12, 36, 3], [29, 35, 29], [19, 20, 22], [8, 3, 35], [3, 1, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 31], []]
 b := ![[], [16, 8, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [36, 33, 36, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1113589, -224590, -62197]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30097, -6070, -1681]
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


def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16, 4, 3]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![16, 4, 3]] 
 ![![41, 0, 0], ![7, 1, 0], ![37, 0, 1]] where
  M :=![![![16, 4, 3], ![-177, -20, 40], ![-413, -71, 20]]]
  hmulB := by decide  
  f := ![![![2440, -293, 220]], ![![100, -12, 9]], ![![2307, -277, 208]]]
  g := ![![![-3, 4, 3], ![-37, -20, 40], ![-16, -71, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-39, -7, 1]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-39, -7, 1]] 
 ![![41, 0, 0], ![26, 1, 0], ![20, 0, 1]] where
  M :=![![![-39, -7, 1], ![-59, -26, -45], ![354, 43, -71]]]
  hmulB := by decide  
  f := ![![![3781, -454, 341]], ![![1907, -229, 172]], ![![2007, -241, 181]]]
  g := ![![![3, -7, 1], ![37, -26, -45], ![16, 43, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![16, 4, 3]] ![![16, 4, 3]]
  ![![-1691, -229, 268]] where
 M := ![![![-1691, -229, 268]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-1691, -229, 268]] ![![-39, -7, 1]]
  ![![41, 0, 0]] where
 M := ![![![174332, 29315, -10414]]]
 hmul := by decide  
 g := ![![![![4252, 715, -254]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![43, 0, 0], ![5, 1, 0], ![17, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 2, 7], ![-59, -8, 9]]]
  hmulB := by decide  
  f := ![![![-74, 9, -7]], ![![1, 0, 0]], ![![-32, 4, -3]]]
  g := ![![![0, 1, 0], ![-3, 2, 7], ![-4, -8, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-233, 28, -21]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![-233, 28, -21]] 
 ![![43, 0, 0], ![32, 1, 0], ![21, 0, 1]] where
  M :=![![![-233, 28, -21], ![1239, -149, 112], ![-413, 49, -37]]]
  hmulB := by decide  
  f := ![![![-25, -7, -7]], ![![-9, -4, -7]], ![![7, 0, -4]]]
  g := ![![![-16, 28, -21], ![85, -149, 112], ![-28, 49, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![5, 1, 0]] ![![5, 1, 0]]
  ![![25, 7, 7]] where
 M := ![![![25, 7, 7]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![25, 7, 7]] ![![-233, 28, -21]]
  ![![43, 0, 0]] where
 M := ![![![-43, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC43 : ContainsPrimesAboveP 43 ![I43N0, I43N0, I43N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI43N0
    exact isPrimeI43N0
    exact isPrimeI43N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 43 (by decide) (𝕀 ⊙ MulI43N0 ⊙ MulI43N1)
instance hp47 : Fact (Nat.Prime 47) := {out := by norm_num}

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-112, 13, -10]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![-112, 13, -10]] 
 ![![47, 0, 0], ![0, 47, 0], ![30, 41, 1]] where
  M :=![![![-112, 13, -10], ![590, -71, 51], ![-177, 26, -20]]]
  hmulB := by decide  
  f := ![![![-2, 0, 1]], ![![-59, -10, 4]], ![![-54, -9, 4]]]
  g := ![![![4, 9, -10], ![-20, -46, 51], ![9, 18, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [28, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 46], [0, 1]]
 g := ![![[31, 42], [6, 14], [25, 17], [31, 14], [1]], ![[0, 5], [27, 33], [27, 30], [5, 33], [1]]]
 h' := ![![[25, 46], [20, 18], [5, 22], [25, 39], [19, 25], [0, 1]], ![[0, 1], [0, 29], [38, 25], [13, 8], [33, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [29, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [28, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-642, -868, -529]
  a := ![-1, -5, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![324, 443, -529]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 0, 1]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![-2, 0, 1]] 
 ![![47, 0, 0], ![38, 1, 0], ![45, 0, 1]] where
  M :=![![![-2, 0, 1], ![-59, -10, 4], ![-59, -13, -6]]]
  hmulB := by decide  
  f := ![![![-112, 13, -10]], ![![-78, 9, -7]], ![![-111, 13, -10]]]
  g := ![![![-1, 0, 1], ![3, -10, 4], ![15, -13, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![-112, 13, -10]] ![![-2, 0, 1]]
  ![![47, 0, 0]] where
 M := ![![![47, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [10, 40, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 32, 15], [6, 20, 38], [0, 1]]
 g := ![![[12, 17, 52], [27, 7], [2, 36, 7], [22, 11], [1]], ![[31, 32, 48, 10], [24, 43], [32, 18, 23, 28], [22, 6], [39, 3, 6, 36]], ![[17, 17, 14, 11], [15, 38], [7, 26, 23, 36], [12, 40], [47, 40, 8, 17]]]
 h' := ![![[39, 32, 15], [24, 24, 30], [33, 21, 31], [39, 22, 31], [43, 13, 45], [0, 1]], ![[6, 20, 38], [41, 32, 6], [49, 21, 34], [41, 0, 49], [46, 1, 35], [39, 32, 15]], ![[0, 1], [24, 50, 17], [42, 11, 41], [1, 31, 26], [11, 39, 26], [6, 20, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 41], []]
 b := ![[], [25, 7, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [10, 40, 8, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-236115, 14787, -18285]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4455, 279, -345]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI53N0 B_one_repr
lemma NI53N0 : Nat.card (O ⧸ I53N0) = 148877 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI53N0

def PBC53 : ContainsPrimesAboveP 53 ![I53N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI53N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![53, 0, 0]]) timesTableT_eq_Table B_one_repr 53 (by decide) 𝕀

instance hp59 : Fact (Nat.Prime 59) := {out := by norm_num}

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1109, 133, -100]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-1109, 133, -100]] 
 ![![59, 0, 0], ![0, 59, 0], ![40, 50, 1]] where
  M :=![![![-1109, 133, -100], ![5900, -708, 531], ![-1947, 236, -177]]]
  hmulB := by decide  
  f := ![![![0, 1, 3]], ![![-177, -27, 19]], ![![-154, -23, 18]]]
  g := ![![![49, 87, -100], ![-260, -462, 531], ![87, 154, -177]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [52, 35, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [24, 58], [0, 1]]
 g := ![![[54, 17], [0, 51], [3], [4, 49], [24, 1]], ![[49, 42], [44, 8], [3], [0, 10], [48, 58]]]
 h' := ![![[24, 58], [0, 31], [38, 46], [28, 48], [50, 52], [0, 1]], ![[0, 1], [36, 28], [21, 13], [0, 11], [0, 7], [24, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [27, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [52, 35, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1800, -1424, -2169]
  a := ![1, 7, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1440, 1814, -2169]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 3]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![0, 1, 3]] 
 ![![59, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 3], ![-177, -27, 19], ![-236, -47, -8]]]
  hmulB := by decide  
  f := ![![![-1109, 133, -100]], ![![100, -12, 9]], ![![-33, 4, -3]]]
  g := ![![![0, 1, 3], ![-3, -27, 19], ![-4, -47, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-1109, 133, -100]] ![![0, 1, 3]]
  ![![59, 0, 0]] where
 M := ![![![59, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-23, -3, 4]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![-23, -3, 4]] 
 ![![61, 0, 0], ![9, 1, 0], ![1, 0, 1]] where
  M :=![![![-23, -3, 4], ![-236, -46, -5], ![-59, -28, -51]]]
  hmulB := by decide  
  f := ![![![2206, -265, 199]], ![![133, -16, 12]], ![![100, -12, 9]]]
  g := ![![![0, -3, 4], ![3, -46, -5], ![4, -28, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![55, 11, 2]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![55, 11, 2]] 
 ![![61, 0, 0], ![42, 1, 0], ![10, 0, 1]] where
  M :=![![![55, 11, 2], ![-118, 6, 85], ![-767, -114, 91]]]
  hmulB := by decide  
  f := ![![![10236, -1229, 923]], ![![6155, -739, 555]], ![![1974, -237, 178]]]
  g := ![![![-7, 11, 2], ![-20, 6, 85], ![51, -114, 91]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![-23, -3, 4]] ![![-23, -3, 4]]
  ![![1001, 95, -281]] where
 M := ![![![1001, 95, -281]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI61N1 : IdealMulLeCertificate' Table 
  ![![1001, 95, -281]] ![![55, 11, 2]]
  ![![61, 0, 0]] where
 M := ![![![259372, 43615, -15494]]]
 hmul := by decide  
 g := ![![![![4252, 715, -254]]]]
 hle2 := by decide  


def PBC61 : ContainsPrimesAboveP 61 ![I61N0, I61N0, I61N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI61N0
    exact isPrimeI61N0
    exact isPrimeI61N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 61 (by decide) (𝕀 ⊙ MulI61N0 ⊙ MulI61N1)
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [28, 57, 52, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 49, 46], [14, 17, 21], [0, 1]]
 g := ![![[55, 33, 59], [3, 24, 16], [37, 10], [42, 17], [15, 1], []], ![[61, 19, 23, 53], [29, 15, 36, 3], [7, 49], [9, 6], [24, 21], [1, 39]], ![[31, 58, 15, 26], [9, 26, 63, 14], [16, 25], [10, 49], [55, 56], [26, 39]]]
 h' := ![![[1, 49, 46], [50, 53, 40], [62, 40, 4], [19, 41, 55], [49, 55, 34], [0, 0, 1], [0, 1]], ![[14, 17, 21], [28, 20, 36], [61, 34, 32], [49, 15, 7], [57, 59, 26], [40, 21, 17], [1, 49, 46]], ![[0, 1], [14, 61, 58], [35, 60, 31], [9, 11, 5], [17, 20, 7], [4, 46, 49], [14, 17, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 42], []]
 b := ![[], [31, 34, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [28, 57, 52, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1136253, -240262, -76581]
  a := ![0, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16959, -3586, -1143]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, -5, 10]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![-44, -5, 10]] 
 ![![71, 0, 0], ![0, 71, 0], ![24, 35, 1]] where
  M :=![![![-44, -5, 10], ![-590, -109, 5], ![-295, -90, -104]]]
  hmulB := by decide  
  f := ![![![166, -20, 15]], ![![-885, 106, -80]], ![![-376, 45, -34]]]
  g := ![![![-4, -5, 10], ![-10, -4, 5], ![31, 50, -104]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [45, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 70], [0, 1]]
 g := ![![[55, 30], [56, 37], [10, 19], [60], [29], [1]], ![[0, 41], [0, 34], [58, 52], [60], [29], [1]]]
 h' := ![![[10, 70], [36, 39], [47, 45], [27, 44], [10, 29], [26, 10], [0, 1]], ![[0, 1], [0, 32], [0, 26], [41, 27], [16, 42], [55, 61], [10, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [62, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [45, 61, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-120253, -75966, -56879]
  a := ![1, -41, 102]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17533, 26969, -56879]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-166, 20, -15]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![-166, 20, -15]] 
 ![![71, 0, 0], ![35, 1, 0], ![53, 0, 1]] where
  M :=![![![-166, 20, -15], ![885, -106, 80], ![-295, 35, -26]]]
  hmulB := by decide  
  f := ![![![44, 5, -10]], ![![30, 4, -5]], ![![37, 5, -6]]]
  g := ![![![-1, 20, -15], ![5, -106, 80], ![-2, 35, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![-44, -5, 10]] ![![-166, 20, -15]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67879, -8150, 6121]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![67879, -8150, 6121]] 
 ![![73, 0, 0], ![0, 73, 0], ![1, 64, 1]] where
  M :=![![![67879, -8150, 6121], ![-361139, 43361, -32566], ![119711, -14373, 10795]]]
  hmulB := by decide  
  f := ![![![149, 29, 3]], ![![-177, 38, 215]], ![![-179, 30, 192]]]
  g := ![![![846, -5478, 6121], ![-4501, 29145, -32566], ![1492, -9661, 10795]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [17, 39, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 72], [0, 1]]
 g := ![![[71, 32], [61], [67], [64, 12], [61], [1]], ![[64, 41], [61], [67], [34, 61], [61], [1]]]
 h' := ![![[34, 72], [10, 55], [5, 39], [7, 33], [55, 42], [56, 34], [0, 1]], ![[0, 1], [55, 18], [17, 34], [34, 40], [23, 31], [44, 39], [34, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [16, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [17, 39, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-965, -586, -89]
  a := ![-1, -3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, 70, -89]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-149, -29, -3]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![-149, -29, -3]] 
 ![![73, 0, 0], ![59, 1, 0], ![39, 0, 1]] where
  M :=![![![-149, -29, -3], ![177, -38, -215], ![1888, 271, -253]]]
  hmulB := by decide  
  f := ![![![-67879, 8150, -6121]], ![![-49914, 5993, -4501]], ![![-37904, 4551, -3418]]]
  g := ![![![23, -29, -3], ![148, -38, -215], ![-58, 271, -253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![67879, -8150, 6121]] ![![-149, -29, -3]]
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


def P79P0 : CertificateIrreducibleZModOfList' 79 3 2 6 [53, 70, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 28, 66], [33, 50, 13], [0, 1]]
 g := ![![[17, 15, 52], [37, 62, 55], [28, 8, 23], [48, 10, 21], [1, 1], []], ![[1, 1, 75, 71], [65, 43, 31, 71], [55, 45, 7, 17], [17, 1, 43, 61], [76, 51], [73, 11]], ![[26, 70, 3, 40], [30, 8, 51, 19], [27, 39, 78, 11], [6, 72, 30, 62], [59, 73], [47, 11]]]
 h' := ![![[47, 28, 66], [14, 22, 62], [17, 5, 56], [63, 25, 55], [26, 35, 10], [0, 0, 1], [0, 1]], ![[33, 50, 13], [38, 39, 49], [38, 75, 49], [77, 62, 55], [2, 74, 45], [78, 20, 50], [47, 28, 66]], ![[0, 1], [5, 18, 47], [38, 78, 53], [13, 71, 48], [38, 49, 24], [20, 59, 28], [33, 50, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 51], []]
 b := ![[], [41, 16, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 3
  hpos := by decide
  P := [53, 70, 78, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3923140, 553790, -45267]
  a := ![0, -8, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49660, 7010, -573]
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



lemma PB93I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB93I1 : PrimesBelowBoundCertificateInterval O 31 79 93 where
  m := 11
  g := ![1, 3, 3, 2, 1, 2, 3, 1, 2, 2, 1]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB93I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N0, I41N1]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![61, 61, 61]
    · exact ![300763]
    · exact ![5041, 71]
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
      exact NI41N0
      exact NI41N1
    · dsimp ; intro j
      fin_cases j
      exact NI43N0
      exact NI43N0
      exact NI43N1
    · dsimp ; intro j
      fin_cases j
      exact NI47N0
      exact NI47N1
    · dsimp ; intro j
      fin_cases j
      exact NI53N0
    · dsimp ; intro j
      fin_cases j
      exact NI59N0
      exact NI59N1
    · dsimp ; intro j
      fin_cases j
      exact NI61N0
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
      exact NI73N1
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
  β := ![I41N0, I41N1, I43N0, I43N1, I47N1, I59N1, I61N0, I61N1, I71N1, I73N1]
  Il := ![[], [I41N0, I41N0, I41N1], [I43N0, I43N0, I43N1], [I47N1], [], [I59N1], [I61N0, I61N0, I61N1], [], [I71N1], [I73N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
