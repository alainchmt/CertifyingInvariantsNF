
import IdealArithmetic.Examples.NF3_1_648324_3.RI3_1_648324_3
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


def P37P0 : CertificateIrreducibleZModOfList' 37 3 2 5 [30, 15, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 11, 29], [27, 25, 8], [0, 1]]
 g := ![![[10, 23, 10], [0, 16], [0, 1, 16], [23, 1], []], ![[22, 11, 1, 17], [33, 21], [20, 20, 5, 23], [27, 33], [1, 27]], ![[28, 32, 30, 32], [20, 7], [20, 18, 31, 23], [3, 10], [22, 27]]]
 h' := ![![[33, 11, 29], [0, 1, 26], [0, 28, 4], [13, 32, 33], [0, 0, 1], [0, 1]], ![[27, 25, 8], [2, 27, 13], [17, 23, 24], [15, 8, 14], [23, 12, 25], [33, 11, 29]], ![[0, 1], [8, 9, 35], [33, 23, 9], [9, 34, 27], [32, 25, 11], [27, 25, 8]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 19], []]
 b := ![[], [18, 7, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 3
  hpos := by decide
  P := [30, 15, 14, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-183150, -50394, -7178]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4950, -1362, -194]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![9, 1, 0]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![9, 1, 0]] 
 ![![41, 0, 0], ![9, 1, 0], ![21, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![9, 1, 0], ![0, 9, 2], ![426, 81, 9]]]
  hmulB := by decide  
  f := ![![![181, 20, 0], ![-820, 0, 0]], ![![27, 3, 0], ![-122, 0, 0]], ![![87, 5, -1], ![-394, 21, 0]]]
  g := ![![![1, 0, 0], ![-9, 41, 0], ![-21, 0, 41]], ![![0, 1, 0], ![-3, 9, 2], ![-12, 81, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N0 : Nat.card (O ⧸ I41N0) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N0)

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := prime_ideal_of_norm_prime hp41.out _ NI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1488511, 55112, -21002]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![1488511, 55112, -21002]] 
 ![![41, 0, 0], ![13, 1, 0], ![18, 0, 1]] where
  M :=![![![1488511, 55112, -21002], ![-8946852, -212651, 110224], ![23477712, -9354, -212651]]]
  hmulB := by decide  
  f := ![![![-46251483097, -11916074620, -1608568786]], ![![-31378526417, -8084256703, -1091305938]], ![![-144116450826, -37129671678, -5012190071]]]
  g := ![![![28051, 55112, -21002], ![-199181, -212651, 110224], ![668952, -9354, -212651]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1

def I41N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![19, 1, 0]] i)))

def SI41N2: IdealEqSpanCertificate' Table ![![41, 0, 0], ![19, 1, 0]] 
 ![![41, 0, 0], ![19, 1, 0], ![4, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![19, 1, 0], ![0, 19, 2], ![426, 81, 19]]]
  hmulB := by decide  
  f := ![![![172, 9, 0], ![-369, 0, 0]], ![![76, 4, 0], ![-163, 0, 0]], ![![14, -9, -1], ![-30, 21, 0]]]
  g := ![![![1, 0, 0], ![-19, 41, 0], ![-4, 0, 41]], ![![0, 1, 0], ![-9, 19, 2], ![-29, 81, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N2 : Nat.card (O ⧸ I41N2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N2)

lemma isPrimeI41N2 : Ideal.IsPrime I41N2 := prime_ideal_of_norm_prime hp41.out _ NI41N2
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![9, 1, 0]] ![![1488511, 55112, -21002]]
  ![![41, 0, 0], ![-44, 11, 1]] where
 M := ![![![61028951, 2259592, -861082]], ![![4449747, 283357, -78794]]]
 hmul := by decide  
 g := ![![![![724671, 246072, -3642], ![-711760, 0, 0]]], ![![![53231, 20736, -665], ![-51529, 0, 0]]]]
 hle2 := by decide  

def MulI41N1 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![-44, 11, 1]] ![![41, 0, 0], ![19, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![779, 41, 0]], ![![-1804, 451, 41], ![-410, 246, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![19, 1, 0]]], ![![![-44, 11, 1]], ![![-10, 6, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-48, 9, 1]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-48, 9, 1]] 
 ![![43, 0, 0], ![0, 43, 0], ![38, 9, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-48, 9, 1], ![426, 33, 18], ![3834, 942, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -9, 43]], ![![-2, 0, 1], ![-6, -3, 18], ![60, 15, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P43P0 : CertificateIrreducibleZModOfList' 43 2 2 5 [40, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 42], [0, 1]]
 g := ![![[40, 14], [13, 11], [35], [34, 38], [1]], ![[0, 29], [0, 32], [35], [36, 5], [1]]]
 h' := ![![[34, 42], [39, 33], [17, 21], [16, 32], [3, 34], [0, 1]], ![[0, 1], [0, 10], [0, 22], [29, 11], [41, 9], [34, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [11, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI43N0 : CertifiedPrimeIdeal' SI43N0 43 where
  n := 2
  hpos := by decide
  P := [40, 9, 1]
  hirr := P43P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5080, 931, 758]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-788, -137, 758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI43N0 B_one_repr
lemma NI43N0 : Nat.card (O ⧸ I43N0) = 1849 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-18, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-18, 1, 0]] 
 ![![43, 0, 0], ![25, 1, 0], ![10, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-18, 1, 0], ![0, -18, 2], ![426, 81, -18]]]
  hmulB := by decide  
  f := ![![![361, -20, 0], ![860, 0, 0]], ![![199, -11, 0], ![474, 0, 0]], ![![94, 4, -1], ![224, 22, 0]]]
  g := ![![![1, 0, 0], ![-25, 43, 0], ![-10, 0, 43]], ![![-1, 1, 0], ![10, -18, 2], ![-33, 81, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-48, 9, 1]] ![![43, 0, 0], ![-18, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-774, 43, 0]], ![![-2064, 387, 43], ![1290, -129, 0]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-18, 1, 0]]], ![![![-48, 9, 1]], ![![30, -3, 0]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1057, 62, -18]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![1057, 62, -18]] 
 ![![47, 0, 0], ![0, 47, 0], ![17, 7, 1]] where
  M :=![![![1057, 62, -18], ![-7668, -401, 124], ![26412, 1188, -401]]]
  hmulB := by decide  
  f := ![![![287, 74, 10]], ![![4260, 1097, 148]], ![![1409, 363, 49]]]
  g := ![![![29, 4, -18], ![-208, -27, 124], ![707, 85, -401]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [14, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 46], [0, 1]]
 g := ![![[8, 37], [21, 9], [24, 17], [30, 42], [1]], ![[0, 10], [0, 38], [0, 30], [26, 5], [1]]]
 h' := ![![[29, 46], [35, 15], [40, 44], [3, 8], [33, 29], [0, 1]], ![[0, 1], [0, 32], [0, 3], [0, 39], [28, 18], [29, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [8, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [14, 18, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2106, -59, 193]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -30, 193]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![287, 74, 10]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![287, 74, 10]] 
 ![![47, 0, 0], ![33, 1, 0], ![43, 0, 1]] where
  M :=![![![287, 74, 10], ![4260, 1097, 148], ![31524, 8124, 1097]]]
  hmulB := by decide  
  f := ![![![1057, 62, -18]], ![![579, 35, -10]], ![![1529, 82, -25]]]
  g := ![![![-55, 74, 10], ![-815, 1097, 148], ![-6037, 8124, 1097]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![1057, 62, -18]] ![![287, 74, 10]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46085, -786, 526]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![-46085, -786, 526]] 
 ![![53, 0, 0], ![12, 1, 0], ![34, 0, 1]] where
  M :=![![![-46085, -786, 526], ![224076, -3479, -1572], ![-334836, 48372, -3479]]]
  hmulB := by decide  
  f := ![![![-88144225, -22709178, -3065546]], ![![-44597232, -11489879, -1551036]], ![![-239075726, -61594656, -8314755]]]
  g := ![![![-1029, -786, 526], ![6024, -3479, -1572], ![-15038, 48372, -3479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N0 : Nat.card (O ⧸ I53N0) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N0)

lemma isPrimeI53N0 : Ideal.IsPrime I53N0 := prime_ideal_of_norm_prime hp53.out _ NI53N0

def I53N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-176027, -45351, -6122]] i)))

def SI53N1: IdealEqSpanCertificate' Table ![![-176027, -45351, -6122]] 
 ![![53, 0, 0], ![46, 1, 0], ![2, 0, 1]] where
  M :=![![![-176027, -45351, -6122], ![-2607972, -671909, -90702], ![-19319526, -4977417, -671909]]]
  hmulB := by decide  
  f := ![![![-27547, -1815, 496]], ![![-19922, -1337, 362]], ![![-15628, -849, 257]]]
  g := ![![![36271, -45351, -6122], ![537382, -671909, -90702], ![3980858, -4977417, -671909]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N1 : Nat.card (O ⧸ I53N1) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N1)

lemma isPrimeI53N1 : Ideal.IsPrime I53N1 := prime_ideal_of_norm_prime hp53.out _ NI53N1

def I53N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 15, 2]] i)))

def SI53N2: IdealEqSpanCertificate' Table ![![59, 15, 2]] 
 ![![53, 0, 0], ![48, 1, 0], ![14, 0, 1]] where
  M :=![![![59, 15, 2], ![852, 221, 30], ![6390, 1641, 221]]]
  hmulB := by decide  
  f := ![![![-389, -33, 8]], ![![-288, -25, 6]], ![![-368, -27, 7]]]
  g := ![![![-13, 15, 2], ![-192, 221, 30], ![-1424, 1641, 221]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI53N2 : Nat.card (O ⧸ I53N2) = 53 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI53N2)

lemma isPrimeI53N2 : Ideal.IsPrime I53N2 := prime_ideal_of_norm_prime hp53.out _ NI53N2
def MulI53N0 : IdealMulLeCertificate' Table 
  ![![-46085, -786, 526]] ![![-176027, -45351, -6122]]
  ![![-389, -33, 8]] where
 M := ![![![-389, -33, 8]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI53N1 : IdealMulLeCertificate' Table 
  ![![-389, -33, 8]] ![![59, 15, 2]]
  ![![53, 0, 0]] where
 M := ![![![53, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P59P0 : CertificateIrreducibleZModOfList' 59 3 2 5 [30, 38, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 1, 33], [12, 57, 26], [0, 1]]
 g := ![![[46, 52, 17], [16, 24, 9], [53, 48], [1, 36, 3], [1]], ![[23, 58, 56, 23], [30, 0, 18, 47], [36, 35], [55, 2, 37, 24], [16, 26, 15, 6]], ![[56, 42, 18, 45], [37, 58, 45, 1], [18, 7], [29, 29, 18, 3], [30, 31, 22, 53]]]
 h' := ![![[36, 1, 33], [51, 58, 28], [18, 9, 56], [29, 18, 44], [29, 21, 48], [0, 1]], ![[12, 57, 26], [7, 34, 29], [31, 20, 8], [7, 14, 34], [38, 22, 7], [36, 1, 33]], ![[0, 1], [9, 26, 2], [7, 30, 54], [4, 27, 40], [2, 16, 4], [12, 57, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 18], []]
 b := ![[], [55, 46, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 3
  hpos := by decide
  P := [30, 38, 11, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1553116, -738090, -157058]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26324, -12510, -2662]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![61, 0, 0], ![7, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 2], ![426, 81, 7]]]
  hmulB := by decide  
  f := ![![![-113, -7, 2]], ![![1, 0, 0]], ![![-60, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 7, 2], ![-3, 81, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N0 : Nat.card (O ⧸ I61N0) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N0)

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := prime_ideal_of_norm_prime hp61.out _ NI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![20, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![20, 1, 0]] 
 ![![61, 0, 0], ![20, 1, 0], ![44, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![20, 1, 0], ![0, 20, 2], ![426, 81, 20]]]
  hmulB := by decide  
  f := ![![![481, 24, 0], ![-1464, 0, 0]], ![![140, 7, 0], ![-426, 0, 0]], ![![364, 8, -1], ![-1108, 31, 0]]]
  g := ![![![1, 0, 0], ![-20, 61, 0], ![-44, 0, 61]], ![![0, 1, 0], ![-8, 20, 2], ![-34, 81, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1

def I61N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-27, 1, 0]] i)))

def SI61N2: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-27, 1, 0]] 
 ![![61, 0, 0], ![34, 1, 0], ![32, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-27, 1, 0], ![0, -27, 2], ![426, 81, -27]]]
  hmulB := by decide  
  f := ![![![1567, -58, 0], ![3538, 0, 0]], ![![892, -33, 0], ![2014, 0, 0]], ![![830, -17, -1], ![1874, 31, 0]]]
  g := ![![![1, 0, 0], ![-34, 61, 0], ![-32, 0, 61]], ![![-1, 1, 0], ![14, -27, 2], ![-24, 81, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N2 : Nat.card (O ⧸ I61N2) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N2)

lemma isPrimeI61N2 : Ideal.IsPrime I61N2 := prime_ideal_of_norm_prime hp61.out _ NI61N2
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![7, 1, 0]] ![![61, 0, 0], ![20, 1, 0]]
  ![![61, 0, 0], ![-52, -17, 1]] where
 M := ![![![427, 61, 0], ![140, 27, 2]]]
 hmul := by decide  
 g := ![![![![7, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI61N1 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![-52, -17, 1]] ![![61, 0, 0], ![-27, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1647, 61, 0]], ![![-3172, -1037, 61], ![1830, 488, -61]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-27, 1, 0]]], ![![![-52, -17, 1]], ![![30, 8, -1]]]]
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

def I67N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5923, -1526, -206]] i)))

def SI67N0: IdealEqSpanCertificate' Table ![![-5923, -1526, -206]] 
 ![![67, 0, 0], ![2, 1, 0], ![65, 0, 1]] where
  M :=![![![-5923, -1526, -206], ![-87756, -22609, -3052], ![-650076, -167484, -22609]]]
  hmulB := by decide  
  f := ![![![-5713, -370, 102]], ![![478, 27, -8]], ![![-7895, -482, 137]]]
  g := ![![![157, -1526, -206], ![2326, -22609, -3052], ![17231, -167484, -22609]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N0 : Nat.card (O ⧸ I67N0) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N0)

lemma isPrimeI67N0 : Ideal.IsPrime I67N0 := prime_ideal_of_norm_prime hp67.out _ NI67N0

def I67N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![4, 1, 0]] i)))

def SI67N1: IdealEqSpanCertificate' Table ![![67, 0, 0], ![4, 1, 0]] 
 ![![67, 0, 0], ![4, 1, 0], ![59, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![4, 1, 0], ![0, 4, 2], ![426, 81, 4]]]
  hmulB := by decide  
  f := ![![![61, 15, 0], ![-1005, 0, 0]], ![![-4, -1, 0], ![68, 0, 0]], ![![53, 11, -1], ![-873, 34, 0]]]
  g := ![![![1, 0, 0], ![-4, 67, 0], ![-59, 0, 67]], ![![0, 1, 0], ![-2, 4, 2], ![-2, 81, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N1 : Nat.card (O ⧸ I67N1) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N1)

lemma isPrimeI67N1 : Ideal.IsPrime I67N1 := prime_ideal_of_norm_prime hp67.out _ NI67N1

def I67N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-6, 1, 0]] i)))

def SI67N2: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-6, 1, 0]] 
 ![![67, 0, 0], ![61, 1, 0], ![49, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-6, 1, 0], ![0, -6, 2], ![426, 81, -6]]]
  hmulB := by decide  
  f := ![![![349, -58, 0], ![3886, 0, 0]], ![![319, -53, 0], ![3552, 0, 0]], ![![259, -40, -1], ![2884, 34, 0]]]
  g := ![![![1, 0, 0], ![-61, 67, 0], ![-49, 0, 67]], ![![-1, 1, 0], ![4, -6, 2], ![-63, 81, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI67N2 : Nat.card (O ⧸ I67N2) = 67 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI67N2)

lemma isPrimeI67N2 : Ideal.IsPrime I67N2 := prime_ideal_of_norm_prime hp67.out _ NI67N2
def MulI67N0 : IdealMulLeCertificate' Table 
  ![![-5923, -1526, -206]] ![![67, 0, 0], ![4, 1, 0]]
  ![![67, 0, 0], ![-63, 3, 1]] where
 M := ![![![-396841, -102242, -13802], ![-111448, -28713, -3876]]]
 hmul := by decide  
 g := ![![![![-3151, -1658, -250], ![2948, 0, 0]], ![![-835, -468, -71], ![881, 0, 0]]]]
 hle2 := by decide  

def MulI67N1 : IdealMulLeCertificate' Table 
  ![![67, 0, 0], ![-63, 3, 1]] ![![67, 0, 0], ![-6, 1, 0]]
  ![![67, 0, 0]] where
 M := ![![![4489, 0, 0], ![-402, 67, 0]], ![![-4221, 201, 67], ![804, 0, 0]]]
 hmul := by decide  
 g := ![![![![67, 0, 0]], ![![-6, 1, 0]]], ![![![-63, 3, 1]], ![![12, 0, 0]]]]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1633, -3666, 480]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![1633, -3666, 480]] 
 ![![71, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![1633, -3666, 480], ![204480, 40513, -7332], ![-1561716, -194706, 40513]]]
  hmulB := by decide  
  f := ![![![-213718777, -55061778, -7432872]], ![![-44597232, -11489879, -1551036]], ![![-330370668, -85115574, -11489879]]]
  g := ![![![23, -3666, 480], ![2880, 40513, -7332], ![-21996, -194706, 40513]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N0 : Nat.card (O ⧸ I71N0) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N0)

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := prime_ideal_of_norm_prime hp71.out _ NI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![34, 1, 0]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![71, 0, 0], ![34, 1, 0]] 
 ![![71, 0, 0], ![34, 1, 0], ![61, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![34, 1, 0], ![0, 34, 2], ![426, 81, 34]]]
  hmulB := by decide  
  f := ![![![579, 17, 0], ![-1207, 0, 0]], ![![238, 7, 0], ![-496, 0, 0]], ![![485, -3, -1], ![-1011, 36, 0]]]
  g := ![![![1, 0, 0], ![-34, 71, 0], ![-61, 0, 71]], ![![0, 1, 0], ![-18, 34, 2], ![-62, 81, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1

def I71N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0], ![-34, 1, 0]] i)))

def SI71N2: IdealEqSpanCertificate' Table ![![71, 0, 0], ![-34, 1, 0]] 
 ![![71, 0, 0], ![37, 1, 0], ![61, 0, 1]] where
  M :=![![![71, 0, 0], ![0, 71, 0], ![0, 0, 71]], ![![-34, 1, 0], ![0, -34, 2], ![426, 81, -34]]]
  hmulB := by decide  
  f := ![![![1259, -37, 0], ![2627, 0, 0]], ![![681, -20, 0], ![1421, 0, 0]], ![![1029, -13, -1], ![2147, 36, 0]]]
  g := ![![![1, 0, 0], ![-37, 71, 0], ![-61, 0, 71]], ![![-1, 1, 0], ![16, -34, 2], ![-7, 81, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N2 : Nat.card (O ⧸ I71N2) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N2)

lemma isPrimeI71N2 : Ideal.IsPrime I71N2 := prime_ideal_of_norm_prime hp71.out _ NI71N2
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![1633, -3666, 480]] ![![71, 0, 0], ![34, 1, 0]]
  ![![71, 0, 0], ![-71, 17, 1]] where
 M := ![![![115943, -260286, 34080], ![260002, -84131, 8988]]]
 hmul := by decide  
 g := ![![![![426, -3377, 497], ![-1207, 0, 0]], ![![1787, -736, 153], ![-1875, 0, 0]]]]
 hle2 := by decide  

def MulI71N1 : IdealMulLeCertificate' Table 
  ![![71, 0, 0], ![-71, 17, 1]] ![![71, 0, 0], ![-34, 1, 0]]
  ![![71, 0, 0]] where
 M := ![![![5041, 0, 0], ![-2414, 71, 0]], ![![-5041, 1207, 71], ![2840, -568, 0]]]
 hmul := by decide  
 g := ![![![![71, 0, 0]], ![![-34, 1, 0]]], ![![![-71, 17, 1]], ![![40, -8, 0]]]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-79, 1, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-79, 1, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![67, 1, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-79, 1, 1], ![426, 2, 2], ![426, 294, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -1, 73]], ![![-2, 0, 1], ![4, 0, 2], ![4, 4, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [70, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 72], [0, 1]]
 g := ![![[17, 24], [24], [23], [5, 65], [46], [1]], ![[0, 49], [24], [23], [35, 8], [46], [1]]]
 h' := ![![[51, 72], [3, 30], [2, 30], [15, 13], [1, 24], [3, 51], [0, 1]], ![[0, 1], [0, 43], [72, 43], [21, 60], [57, 49], [49, 22], [51, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [55, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [70, 22, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16281, 3747, 827]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-536, 40, 827]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![-2, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![-2, 1, 0]] 
 ![![73, 0, 0], ![71, 1, 0], ![71, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![-2, 1, 0], ![0, -2, 2], ![426, 81, -2]]]
  hmulB := by decide  
  f := ![![![79, -39, 0], ![2847, 0, 0]], ![![77, -38, 0], ![2775, 0, 0]], ![![77, -37, -1], ![2775, 37, 0]]]
  g := ![![![1, 0, 0], ![-71, 73, 0], ![-71, 0, 73]], ![![-1, 1, 0], ![0, -2, 2], ![-71, 81, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![-79, 1, 1]] ![![73, 0, 0], ![-2, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![-146, 73, 0]], ![![-5767, 73, 73], ![584, 0, 0]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![-2, 1, 0]]], ![![![-79, 1, 1]], ![![8, 0, 0]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![809023223, 65204596, -16173362]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![809023223, 65204596, -16173362]] 
 ![![79, 0, 0], ![0, 79, 0], ![7, 53, 1]] where
  M :=![![![809023223, 65204596, -16173362], ![-6889852212, -501019099, 130409192], ![27777157896, 1836646170, -501019099]]]
  hmulB := by decide  
  f := ![![![-145627779027559, -37519045129816, -5064752177286]], ![![-2157584427523836, -555872705387725, -75038090259632]], ![![-1662714966294403, -428376222414369, -57827148789737]]]
  g := ![![![11673883, 11675858, -16173362], ![-98768564, -93831725, 130409192], ![396003691, 359375423, -501019099]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [29, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 78], [0, 1]]
 g := ![![[49, 65], [59, 40], [37, 11], [30, 10], [1], [1]], ![[35, 14], [20, 39], [48, 68], [40, 69], [1], [1]]]
 h' := ![![[1, 78], [27, 67], [33, 35], [78, 66], [22, 22], [50, 1], [0, 1]], ![[0, 1], [15, 12], [68, 44], [65, 13], [44, 57], [51, 78], [1, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [68, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [29, 78, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2604, -45, 23]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -16, 23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-81593369, -7950338, 1816654]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![-81593369, -7950338, 1816654]] 
 ![![79, 0, 0], ![52, 1, 0], ![70, 0, 1]] where
  M :=![![![-81593369, -7950338, 1816654], ![773894604, 65555605, -15900676], ![-3386843988, -257030076, 65555605]]]
  hmulB := by decide  
  f := ![![![210585386184649, 54254501858786, 7323896582818]], ![![178106582606104, 45886773494301, 6194324380052]], ![![479156896516054, 123448351301480, 16664478103673]]]
  g := ![![![2590613, -7950338, 1816654], ![-19265184, 65555605, -15900676], ![68225666, -257030076, 65555605]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![809023223, 65204596, -16173362]] ![![-81593369, -7950338, 1816654]]
  ![![79, 0, 0]] where
 M := ![![![39227208492039353, 1999559130896718, -627336411345064]]]
 hmul := by decide  
 g := ![![![![496546942937207, 25310875074642, -7940967232216]]]]
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


lemma PB228I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB228I1 : PrimesBelowBoundCertificateInterval O 31 79 228 where
  m := 11
  g := ![1, 3, 2, 2, 3, 1, 3, 3, 3, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB228I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0]
    · exact ![I41N0, I41N1, I41N2]
    · exact ![I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0, I53N1, I53N2]
    · exact ![I59N0]
    · exact ![I61N0, I61N1, I61N2]
    · exact ![I67N0, I67N1, I67N2]
    · exact ![I71N0, I71N1, I71N2]
    · exact ![I73N0, I73N1]
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
    · exact ![41, 41, 41]
    · exact ![1849, 43]
    · exact ![2209, 47]
    · exact ![53, 53, 53]
    · exact ![205379]
    · exact ![61, 61, 61]
    · exact ![67, 67, 67]
    · exact ![71, 71, 71]
    · exact ![5329, 73]
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
      exact NI41N2
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
      exact NI61N2
    · dsimp ; intro j
      fin_cases j
      exact NI67N0
      exact NI67N1
      exact NI67N2
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
      exact NI79N1
  β := ![I41N0, I41N1, I41N2, I43N1, I47N1, I53N0, I53N1, I53N2, I61N0, I61N1, I61N2, I67N0, I67N1, I67N2, I71N0, I71N1, I71N2, I73N1, I79N1]
  Il := ![[], [I41N0, I41N1, I41N2], [I43N1], [I47N1], [I53N0, I53N1, I53N2], [], [I61N0, I61N1, I61N2], [I67N0, I67N1, I67N2], [I71N0, I71N1, I71N2], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
