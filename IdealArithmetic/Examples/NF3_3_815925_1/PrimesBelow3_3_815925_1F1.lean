
import IdealArithmetic.Examples.NF3_3_815925_1.RI3_3_815925_1
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [35, 18, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 15, 23], [27, 21, 14], [0, 1]]
 g := ![![[4, 27, 10], [25, 16], [15, 24, 11], [35, 1], []], ![[33, 16, 17, 14], [34, 33], [10, 31, 1, 19], [26, 34], [2, 11]], ![[2, 0, 18, 13], [22, 34], [26, 13, 5, 29], [22, 3], [11, 11]]]
 h' := ![![[8, 15, 23], [25, 24, 11], [30, 16, 33], [33, 1, 23], [0, 0, 1], [0, 1]], ![[27, 21, 14], [3, 34, 6], [34, 2, 25], [14, 33, 25], [31, 4, 21], [8, 15, 23]], ![[0, 1], [17, 16, 20], [11, 19, 16], [17, 3, 26], [11, 33, 15], [27, 21, 14]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 17], []]
 b := ![[], [28, 5, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [35, 18, 2, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-81992, -94313, -301698]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2216, -2549, -8154]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-680, -9, 19]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![-680, -9, 19]] 
 ![![41, 0, 0], ![9, 1, 0], ![3, 0, 1]] where
  M :=![![![-680, -9, 19], ![-246, 13, 2], ![279, -39, 5]]]
  hmulB := by decide  
  f := ![![![143, -696, -265]], ![![75, -365, -139]], ![![156, -759, -289]]]
  g := ![![![-16, -9, 19], ![-9, 13, 2], ![15, -39, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 9, 3]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![-2, 9, 3]] 
 ![![41, 0, 0], ![35, 1, 0], ![31, 0, 1]] where
  M :=![![![-2, 9, 3], ![-18, 97, 42], ![-81, 369, 127]]]
  hmulB := by decide  
  f := ![![![3179, 36, -87]], ![![2741, 31, -75]], ![![2374, 27, -65]]]
  g := ![![![-10, 9, 3], ![-115, 97, 42], ![-413, 369, 127]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, -3, -1]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![-4, -3, -1]] 
 ![![41, 0, 0], ![37, 1, 0], ![16, 0, 1]] where
  M :=![![![-4, -3, -1], ![6, -37, -14], ![27, -123, -47]]]
  hmulB := by decide  
  f := ![![![-17, 18, -5]], ![![-13, 11, -3]], ![![-13, 21, -6]]]
  g := ![![![3, -3, -1], ![39, -37, -14], ![130, -123, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![-680, -9, 19]] ![![-2, 9, 3]]
  ![![-17, 18, -5]] where
 M := ![![![-17, 18, -5]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![-17, 18, -5]] ![![-4, -3, -1]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 24, 9]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![-5, 24, 9]] 
 ![![43, 0, 0], ![6, 1, 0], ![36, 0, 1]] where
  M :=![![![-5, 24, 9], ![-60, 295, 114], ![-207, 999, 376]]]
  hmulB := by decide  
  f := ![![![-2966, -33, 81]], ![![-438, -5, 12]], ![![-2457, -27, 67]]]
  g := ![![![-11, 24, 9], ![-138, 295, 114], ![-459, 999, 376]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2271, -11050, -4208]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![2271, -11050, -4208]] 
 ![![43, 0, 0], ![18, 1, 0], ![10, 0, 1]] where
  M :=![![![2271, -11050, -4208], ![28396, -138167, -52616], ![94728, -460920, -175525]]]
  hmulB := by decide  
  f := ![![![4045, -110, -64]], ![![1706, -3, -40]], ![![958, -140, 19]]]
  g := ![![![5657, -11050, -4208], ![70734, -138167, -52616], ![235966, -460920, -175525]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![-5, 24, 9]] ![![2271, -11050, -4208]]
  ![![1522701, -7409038, -2821469]] where
 M := ![![![1522701, -7409038, -2821469]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI43N1 : IdealMulLeCertificate' Table 
  ![![1522701, -7409038, -2821469]] ![![2271, -11050, -4208]]
  ![![43, 0, 0]] where
 M := ![![![-474201104509, 2307330198776, 878664763825]]]
 hmul := by decide  
 g := ![![![![-11027932663, 53658841832, 20434064275]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![-8, 22, 1]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![-8, 22, 1]] 
 ![![47, 0, 0], ![0, 47, 0], ![39, 22, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![-8, 22, 1], ![32, 6, 90], ![-255, 807, 73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -22, 47]], ![![-1, 0, 1], ![-74, -42, 90], ![-66, -17, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [21, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 46], [0, 1]]
 g := ![![[34, 9], [39, 24], [19, 32], [25, 34], [1]], ![[0, 38], [11, 23], [13, 15], [1, 13], [1]]]
 h' := ![![[38, 46], [27, 3], [24, 20], [39, 19], [26, 38], [0, 1]], ![[0, 1], [0, 44], [32, 27], [9, 28], [13, 9], [38, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [3, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [21, 9, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1020, -831, 1870]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1530, -893, 1870]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![4, 1, 0]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![47, 0, 0], ![4, 1, 0]] 
 ![![47, 0, 0], ![4, 1, 0], ![21, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![4, 1, 0], ![2, 3, 4], ![-12, 36, 6]]]
  hmulB := by decide  
  f := ![![![-215, -324, -432], ![0, 5076, 0]], ![![-18, -27, -36], ![1, 423, 0]], ![![-97, -145, -193], ![11, 2268, 0]]]
  g := ![![![1, 0, 0], ![-4, 47, 0], ![-21, 0, 47]], ![![0, 1, 0], ![-2, 3, 4], ![-6, 36, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![47, 0, 0], ![-8, 22, 1]] ![![47, 0, 0], ![4, 1, 0]]
  ![![47, 0, 0]] where
 M := ![![![2209, 0, 0], ![188, 47, 0]], ![![-376, 1034, 47], ![0, 94, 94]]]
 hmul := by decide  
 g := ![![![![47, 0, 0]], ![![4, 1, 0]]], ![![![-8, 22, 1]], ![![0, 2, 2]]]]
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


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [44, 27, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 13, 9], [3, 39, 44], [0, 1]]
 g := ![![[14, 8, 43], [46, 16], [5, 40, 36], [7, 52], [1]], ![[44, 5, 21, 6], [1, 43], [11, 37, 30, 15], [28, 6], [40, 29, 51, 40]], ![[33, 38, 18, 16], [30, 52], [10, 11, 15, 4], [23, 38], [3, 37, 24, 13]]]
 h' := ![![[20, 13, 9], [1, 23, 19], [45, 26, 4], [38, 5, 6], [9, 26, 23], [0, 1]], ![[3, 39, 44], [47, 1, 47], [12, 27, 19], [24, 49, 14], [39, 47, 18], [20, 13, 9]], ![[0, 1], [22, 29, 40], [32, 0, 30], [49, 52, 33], [1, 33, 12], [3, 39, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 25], []]
 b := ![[], [49, 47, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [44, 27, 30, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56286530, -307472610, -430203968]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1062010, -5801370, -8117056]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1922, 9351, 3561]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![-1922, 9351, 3561]] 
 ![![59, 0, 0], ![0, 59, 0], ![4, 7, 1]] where
  M :=![![![-1922, 9351, 3561], ![-24030, 116923, 44526], ![-80163, 390051, 148537]]]
  hmulB := by decide  
  f := ![![![-325, 36, -3]], ![![108, -469, 138]], ![![-17, -32, 10]]]
  g := ![![![-274, -264, 3561], ![-3426, -3301, 44526], ![-11429, -11012, 148537]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [52, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 58], [0, 1]]
 g := ![![[56, 21], [26, 12], [15], [34, 45], [38, 1]], ![[28, 38], [10, 47], [15], [33, 14], [17, 58]]]
 h' := ![![[38, 58], [5, 32], [50, 37], [2, 29], [30, 35], [0, 1]], ![[0, 1], [41, 27], [40, 22], [42, 30], [3, 24], [38, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [7, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [52, 21, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1379, -699, 2808]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-167, -345, 2808]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![325, -36, 3]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![325, -36, 3]] 
 ![![59, 0, 0], ![29, 1, 0], ![4, 0, 1]] where
  M :=![![![325, -36, 3], ![-108, 469, -138], ![459, -1251, 364]]]
  hmulB := by decide  
  f := ![![![1922, -9351, -3561]], ![![1352, -6578, -2505]], ![![1489, -7245, -2759]]]
  g := ![![![23, -36, 3], ![-223, 469, -138], ![598, -1251, 364]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![-1922, 9351, 3561]] ![![325, -36, 3]]
  ![![59, 0, 0]] where
 M := ![![![-59, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-9, -13, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-9, -13, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![52, 48, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-9, -13, 1], ![-38, 40, -50], ![165, -453, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -48, 61]], ![![-1, -1, 1], ![42, 40, -50], ![1, -9, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [17, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 60], [0, 1]]
 g := ![![[26, 46], [34], [60, 49], [20, 15], [46, 1]], ![[7, 15], [34], [57, 12], [39, 46], [31, 60]]]
 h' := ![![[46, 60], [16, 30], [17, 41], [26, 54], [11, 25], [0, 1]], ![[0, 1], [54, 31], [12, 20], [9, 7], [2, 36], [46, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [17, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [17, 15, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![451, 116, 1258]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1065, -988, 1258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-11, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-11, 1, 0]] 
 ![![61, 0, 0], ![50, 1, 0], ![59, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-11, 1, 0], ![2, -12, 4], ![-12, 36, -9]]]
  hmulB := by decide  
  f := ![![![-186, 1187, -396], ![61, 6039, 0]], ![![-150, 971, -324], ![62, 4941, 0]], ![![-179, 1148, -383], ![64, 5841, 0]]]
  g := ![![![1, 0, 0], ![-50, 61, 0], ![-59, 0, 61]], ![![-1, 1, 0], ![6, -12, 4], ![-21, 36, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-9, -13, 1]] ![![61, 0, 0], ![-11, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-671, 61, 0]], ![![-549, -793, 61], ![61, 183, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-11, 1, 0]]], ![![![-9, -13, 1]], ![![1, 3, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-7, -9, 1]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-7, -9, 1]] 
 ![![67, 0, 0], ![0, 67, 0], ![60, 58, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-7, -9, 1], ![-30, 38, -34], ![117, -309, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-60, -58, 67]], ![![-1, -1, 1], ![30, 30, -34], ![-9, -15, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P67P0 : CertificateIrreducibleZModOfList' 67 2 2 6 [55, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 66], [0, 1]]
 g := ![![[63, 39], [17, 40], [10], [10], [26], [1]], ![[0, 28], [40, 27], [10], [10], [26], [1]]]
 h' := ![![[19, 66], [3, 21], [25, 24], [21, 12], [54, 12], [12, 19], [0, 1]], ![[0, 1], [0, 46], [12, 43], [48, 55], [14, 55], [38, 48], [19, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [41, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 2
  hpos := by decide
  P := [55, 48, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19270, 24546, 72201]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64370, -62136, 72201]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI67N0 B_one_repr
lemma NI67N0 : Nat.card (O ⧸ I67N0) = 4489 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-33, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-33, 1, 0]] 
 ![![67, 0, 0], ![34, 1, 0], ![55, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-33, 1, 0], ![2, -34, 4], ![-12, 36, -31]]]
  hmulB := by decide  
  f := ![![![-53, 2038, -240], ![134, 4020, 0]], ![![-26, 1019, -120], ![68, 2010, 0]], ![![-44, 1673, -197], ![109, 3300, 0]]]
  g := ![![![1, 0, 0], ![-34, 67, 0], ![-55, 0, 67]], ![![-1, 1, 0], ![14, -34, 4], ![7, 36, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-7, -9, 1]] ![![67, 0, 0], ![-33, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-2211, 67, 0]], ![![-469, -603, 67], ![201, 335, -67]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-33, 1, 0]]], ![![![-7, -9, 1]], ![![3, 5, -1]]]]
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


def P71P0 : CertificateIrreducibleZModOfList' 71 3 2 6 [33, 7, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 12, 32], [8, 58, 39], [0, 1]]
 g := ![![[69, 31, 16], [62, 17, 64], [6, 22, 20], [9, 4], [3, 1], []], ![[18, 37, 25, 10], [56, 36, 63, 25], [31, 17, 46, 12], [27, 15], [0, 27], [6, 30]], ![[28, 42, 41, 23], [24, 29, 66, 51], [34, 10, 42, 17], [57, 32], [35, 2], [70, 30]]]
 h' := ![![[66, 12, 32], [13, 11, 67], [15, 42, 63], [61, 60, 34], [43, 17, 2], [0, 0, 1], [0, 1]], ![[8, 58, 39], [11, 54, 49], [53, 64, 28], [56, 34, 58], [38, 30, 21], [40, 55, 58], [66, 12, 32]], ![[0, 1], [68, 6, 26], [1, 36, 51], [5, 48, 50], [18, 24, 48], [26, 16, 12], [8, 58, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 69], []]
 b := ![[], [4, 52, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 3
  hpos := by decide
  P := [33, 7, 68, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1846, 11147, 5325]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, 157, 75]
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


def P73P0 : CertificateIrreducibleZModOfList' 73 3 2 6 [23, 64, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 72, 29], [60, 0, 44], [0, 1]]
 g := ![![[56, 68, 18], [11, 54], [39, 48], [9, 56, 2], [13, 1], []], ![[32, 15, 71, 47], [26, 6], [20, 4], [41, 34, 10, 21], [], [71, 38]], ![[52, 23, 41, 45], [70, 23], [50, 23], [21, 26, 65, 22], [23, 1], [56, 38]]]
 h' := ![![[26, 72, 29], [57, 44, 23], [50, 71, 45], [12, 10, 62], [66, 21, 32], [0, 0, 1], [0, 1]], ![[60, 0, 44], [68, 71, 35], [3, 8, 15], [68, 8, 71], [64, 66, 25], [65, 5], [26, 72, 29]], ![[0, 1], [28, 31, 15], [18, 67, 13], [0, 55, 13], [47, 59, 16], [49, 68, 72], [60, 0, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 51], []]
 b := ![[], [13, 16, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 3
  hpos := by decide
  P := [23, 64, 60, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![513628, 303826, 1625418]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7036, 4162, 22266]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![35, 1, 0]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![35, 1, 0]] 
 ![![79, 0, 0], ![35, 1, 0], ![19, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![35, 1, 0], ![2, 34, 4], ![-12, 36, 37]]]
  hmulB := by decide  
  f := ![![![3991, 90402, 10640], ![3002, -210140, 0]], ![![1761, 40035, 4712], ![1344, -93062, 0]], ![![951, 21742, 2559], ![742, -50540, 0]]]
  g := ![![![1, 0, 0], ![-35, 79, 0], ![-19, 0, 79]], ![![0, 1, 0], ![-16, 34, 4], ![-25, 36, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N0 : Nat.card (O ⧸ I79N0) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N0)

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := prime_ideal_of_norm_prime hp79.out _ NI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4789, -54, 131]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-4789, -54, 131]] 
 ![![79, 0, 0], ![52, 1, 0], ![9, 0, 1]] where
  M :=![![![-4789, -54, 131], ![-1680, -19, 46], ![1827, 21, -50]]]
  hmulB := by decide  
  f := ![![![-16, 51, 5]], ![![-10, 35, 6]], ![![-9, 30, 4]]]
  g := ![![![-40, -54, 131], ![-14, -19, 46], ![15, 21, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1

def I79N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-9, 1, 0]] i)))

def SI79N2: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-9, 1, 0]] 
 ![![79, 0, 0], ![70, 1, 0], ![57, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-9, 1, 0], ![2, -10, 4], ![-12, 36, -7]]]
  hmulB := by decide  
  f := ![![![5353, -27288, 10920], ![-948, -215670, 0]], ![![4747, -24170, 9672], ![-789, -191022, 0]], ![![3864, -19689, 7879], ![-669, -155610, 0]]]
  g := ![![![1, 0, 0], ![-70, 79, 0], ![-57, 0, 79]], ![![-1, 1, 0], ![6, -10, 4], ![-27, 36, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N2 : Nat.card (O ⧸ I79N2) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N2)

lemma isPrimeI79N2 : Ideal.IsPrime I79N2 := prime_ideal_of_norm_prime hp79.out _ NI79N2
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![35, 1, 0]] ![![-4789, -54, 131]]
  ![![79, 0, 0], ![-58, -18, 1]] where
 M := ![![![-378331, -4266, 10349]], ![![-169295, -1909, 4631]]]
 hmul := by decide  
 g := ![![![![-3107, 468, 102], ![2291, 0, 0]]], ![![![-1411, 203, 46], ![997, 0, 0]]]]
 hle2 := by decide  

def MulI79N1 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![-58, -18, 1]] ![![79, 0, 0], ![-9, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-711, 79, 0]], ![![-4582, -1422, 79], ![474, 158, -79]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-9, 1, 0]]], ![![![-58, -18, 1]], ![![6, 2, -1]]]]
 hle2 := by decide  


def PBC79 : ContainsPrimesAboveP 79 ![I79N0, I79N1, I79N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI79N0
    exact isPrimeI79N1
    exact isPrimeI79N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 79 (by decide) (𝕀 ⊙ MulI79N0 ⊙ MulI79N1)


lemma PB201I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB201I1 : PrimesBelowBoundCertificateInterval O 31 79 201 where
  m := 11
  g := ![1, 3, 3, 2, 1, 2, 2, 2, 1, 1, 3]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB201I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0, I67N1]
    · exact ![I71N0]
    · exact ![I73N0]
    · exact ![I79N0, I79N1, I79N2]
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
    · exact ![3721, 61]
    · exact ![4489, 67]
    · exact ![357911]
    · exact ![389017]
    · exact ![79, 79, 79]
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
      exact NI61N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI79N0
      exact NI79N1
      exact NI79N2
  β := ![I41N0, I41N1, I41N2, I43N0, I43N1, I47N1, I59N1, I61N1, I67N1, I79N0, I79N1, I79N2]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N0, I43N1, I43N1], [I47N1], [], [I59N1], [I61N1], [I67N1], [], [], [I79N0, I79N1, I79N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
