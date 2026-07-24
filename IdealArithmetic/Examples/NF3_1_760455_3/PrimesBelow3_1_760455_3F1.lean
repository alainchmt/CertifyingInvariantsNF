
import IdealArithmetic.Examples.NF3_1_760455_3.RI3_1_760455_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp37 : Fact (Nat.Prime 37) := {out := by norm_num}

def I37N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![15, -12, 1]] i)))

def SI37N0: IdealEqSpanCertificate' Table ![![37, 0, 0], ![15, -12, 1]] 
 ![![37, 0, 0], ![0, 37, 0], ![15, 25, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![15, -12, 1], ![13, -3, -83], ![-442, 361, -27]]]
  hmulB := by decide  
  f := ![![![-14, 12, -1], ![37, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -25, 37]], ![![0, -1, 1], ![34, 56, -83], ![-1, 28, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P37P0 : CertificateIrreducibleZModOfList' 37 2 2 5 [21, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 36], [0, 1]]
 g := ![![[35, 30], [28], [11, 10], [25], [1]], ![[0, 7], [28], [24, 27], [25], [1]]]
 h' := ![![[5, 36], [11, 20], [28, 19], [27, 26], [16, 5], [0, 1]], ![[0, 1], [0, 17], [12, 18], [9, 11], [4, 32], [5, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [25, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI37N0 : CertifiedPrimeIdeal' SI37N0 37 where
  n := 2
  hpos := by decide
  P := [21, 32, 1]
  hirr := P37P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![59, 49, -1666]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![677, 1127, -1666]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI37N0 : Ideal.IsPrime I37N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI37N0 B_one_repr
lemma NI37N0 : Nat.card (O ⧸ I37N0) = 1369 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI37N0

def I37N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![9, 1, 0]] i)))

def SI37N1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![9, 1, 0]] 
 ![![37, 0, 0], ![9, 1, 0], ![27, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![9, 1, 0], ![2, 8, 7], ![37, -30, 10]]]
  hmulB := by decide  
  f := ![![![418, 1843, 1617], ![185, -8547, 0]], ![![103, 447, 392], ![38, -2072, 0]], ![![306, 1345, 1180], ![131, -6237, 0]]]
  g := ![![![1, 0, 0], ![-9, 37, 0], ![-27, 0, 37]], ![![0, 1, 0], ![-7, 8, 7], ![1, -30, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI37N1 : Nat.card (O ⧸ I37N1) = 37 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI37N1)

lemma isPrimeI37N1 : Ideal.IsPrime I37N1 := prime_ideal_of_norm_prime hp37.out _ NI37N1
def MulI37N0 : IdealMulLeCertificate' Table 
  ![![37, 0, 0], ![15, -12, 1]] ![![37, 0, 0], ![9, 1, 0]]
  ![![37, 0, 0]] where
 M := ![![![1369, 0, 0], ![333, 37, 0]], ![![555, -444, 37], ![148, -111, -74]]]
 hmul := by decide  
 g := ![![![![37, 0, 0]], ![![9, 1, 0]]], ![![![15, -12, 1]], ![![4, -3, -2]]]]
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

def I41N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![27, 4, 1]] i)))

def SI41N0: IdealEqSpanCertificate' Table ![![41, 0, 0], ![27, 4, 1]] 
 ![![41, 0, 0], ![0, 41, 0], ![27, 4, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![27, 4, 1], ![45, -7, 29], ![150, -119, 1]]]
  hmulB := by decide  
  f := ![![![-26, -4, -1], ![41, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -4, 41]], ![![0, 0, 1], ![-18, -3, 29], ![3, -3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P41P0 : CertificateIrreducibleZModOfList' 41 2 2 5 [3, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 40], [0, 1]]
 g := ![![[], [], [40], [], [1]], ![[], [], [40], [], [1]]]
 h' := ![![[0, 40], [9], [3], [0, 9], [38], [0, 1]], ![[0, 1], [9], [3], [0, 32], [38], [0, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [0, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI41N0 : CertifiedPrimeIdeal' SI41N0 41 where
  n := 2
  hpos := by decide
  P := [3, 0, 1]
  hirr := P41P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5934, 5649, -9545]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6141, 1069, -9545]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI41N0 : Ideal.IsPrime I41N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI41N0 B_one_repr
lemma NI41N0 : Nat.card (O ⧸ I41N0) = 1681 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI41N0

def I41N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![12, 1, 0]] i)))

def SI41N1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![12, 1, 0]] 
 ![![41, 0, 0], ![12, 1, 0], ![40, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![12, 1, 0], ![2, 11, 7], ![37, -30, 13]]]
  hmulB := by decide  
  f := ![![![-431, -2636, -1680], ![-164, 9840, 0]], ![![-128, -769, -490], ![-40, 2870, 0]], ![![-424, -2572, -1639], ![-148, 9600, 0]]]
  g := ![![![1, 0, 0], ![-12, 41, 0], ![-40, 0, 41]], ![![0, 1, 0], ![-10, 11, 7], ![-3, -30, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI41N1 : Nat.card (O ⧸ I41N1) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI41N1)

lemma isPrimeI41N1 : Ideal.IsPrime I41N1 := prime_ideal_of_norm_prime hp41.out _ NI41N1
def MulI41N0 : IdealMulLeCertificate' Table 
  ![![41, 0, 0], ![27, 4, 1]] ![![41, 0, 0], ![12, 1, 0]]
  ![![41, 0, 0]] where
 M := ![![![1681, 0, 0], ![492, 41, 0]], ![![1107, 164, 41], ![369, 41, 41]]]
 hmul := by decide  
 g := ![![![![41, 0, 0]], ![![12, 1, 0]]], ![![![27, 4, 1]], ![![9, 1, 1]]]]
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

def I43N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-19, 1, 0]] i)))

def SI43N0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-19, 1, 0]] 
 ![![43, 0, 0], ![24, 1, 0], ![32, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-19, 1, 0], ![2, -20, 7], ![37, -30, -18]]]
  hmulB := by decide  
  f := ![![![-210, 3055, -1071], ![215, 6579, 0]], ![![-112, 1697, -595], ![130, 3655, 0]], ![![-166, 2274, -797], ![138, 4896, 0]]]
  g := ![![![1, 0, 0], ![-24, 43, 0], ![-32, 0, 43]], ![![-1, 1, 0], ![6, -20, 7], ![31, -30, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N0 : Nat.card (O ⧸ I43N0) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N0)

lemma isPrimeI43N0 : Ideal.IsPrime I43N0 := prime_ideal_of_norm_prime hp43.out _ NI43N0

def I43N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-5, 1, 0]] i)))

def SI43N1: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-5, 1, 0]] 
 ![![43, 0, 0], ![38, 1, 0], ![39, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-5, 1, 0], ![2, -6, 7], ![37, -30, -4]]]
  hmulB := by decide  
  f := ![![![-460, 1425, -1666], ![129, 10234, 0]], ![![-409, 1258, -1470], ![87, 9030, 0]], ![![-420, 1293, -1511], ![93, 9282, 0]]]
  g := ![![![1, 0, 0], ![-38, 43, 0], ![-39, 0, 43]], ![![-1, 1, 0], ![-1, -6, 7], ![31, -30, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI43N1 : Nat.card (O ⧸ I43N1) = 43 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI43N1)

lemma isPrimeI43N1 : Ideal.IsPrime I43N1 := prime_ideal_of_norm_prime hp43.out _ NI43N1
def MulI43N0 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![-19, 1, 0]] ![![43, 0, 0], ![-19, 1, 0]]
  ![![43, 0, 0], ![15, 19, 1]] where
 M := ![![![1849, 0, 0], ![-817, 43, 0]], ![![-817, 43, 0], ![363, -39, 7]]]
 hmul := by decide  
 g := ![![![![28, -19, -1], ![43, 0, 0]], ![![-19, 1, 0], ![0, 0, 0]]], ![![![-19, 1, 0], ![0, 0, 0]], ![![6, -4, 0], ![7, 0, 0]]]]
 hle2 := by decide  
def MulI43N1 : IdealMulLeCertificate' Table 
  ![![43, 0, 0], ![15, 19, 1]] ![![43, 0, 0], ![-5, 1, 0]]
  ![![43, 0, 0]] where
 M := ![![![1849, 0, 0], ![-215, 43, 0]], ![![645, 817, 43], ![0, -129, 129]]]
 hmul := by decide  
 g := ![![![![43, 0, 0]], ![![-5, 1, 0]]], ![![![15, 19, 1]], ![![0, -3, 3]]]]
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

def I47N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![39795, -32069, -2514]] i)))

def SI47N0: IdealEqSpanCertificate' Table ![![39795, -32069, -2514]] 
 ![![47, 0, 0], ![0, 47, 0], ![19, 17, 1]] where
  M :=![![![39795, -32069, -2514], ![-157156, 147284, -226997], ![-1191581, 959556, 83146]]]
  hmulB := by decide  
  f := ![![![-4894944868, -5406070, -162762527]], ![![-6033025639, -6662988, -200605017]], ![![-4172147617, -4607799, -138728690]]]
  g := ![![![1863, 227, -2514], ![88421, 85239, -226997], ![-58965, -9658, 83146]]]
  hle1 := by decide   
  hle2 := by decide  


def P47P0 : CertificateIrreducibleZModOfList' 47 2 2 5 [36, 22, 1] where
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
 g := ![![[45, 17], [31, 42], [11, 24], [7, 14], [1]], ![[0, 30], [0, 5], [0, 23], [28, 33], [1]]]
 h' := ![![[25, 46], [12, 39], [27, 29], [30, 27], [11, 25], [0, 1]], ![[0, 1], [0, 8], [0, 18], [0, 20], [25, 22], [25, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [45, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI47N0 : CertifiedPrimeIdeal' SI47N0 47 where
  n := 2
  hpos := by decide
  P := [36, 22, 1]
  hirr := P47P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52698, 63257, -1166908]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![472850, 423419, -1166908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI47N0 : Ideal.IsPrime I47N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI47N0 B_one_repr
lemma NI47N0 : Nat.card (O ⧸ I47N0) = 2209 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI47N0

def I47N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4894944868, 5406070, 162762527]] i)))

def SI47N1: IdealEqSpanCertificate' Table ![![4894944868, 5406070, 162762527]] 
 ![![47, 0, 0], ![21, 1, 0], ![41, 0, 1]] where
  M :=![![![4894944868, 5406070, 162762527], ![6033025639, 6662988, 200605017], ![525549644, 580427, 17475128]]]
  hmulB := by decide  
  f := ![![![-39795, 32069, 2514]], ![![-14437, 11195, 5953]], ![![-9362, 7559, 424]]]
  g := ![![![-40252047, 5406070, 162762527], ![-49610698, 6662988, 200605017], ![-4321693, 580427, 17475128]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI47N1 : Nat.card (O ⧸ I47N1) = 47 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI47N1)

lemma isPrimeI47N1 : Ideal.IsPrime I47N1 := prime_ideal_of_norm_prime hp47.out _ NI47N1
def MulI47N0 : IdealMulLeCertificate' Table 
  ![![39795, -32069, -2514]] ![![4894944868, 5406070, 162762527]]
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

def I53N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![53, 0, 0]] i)))

def SI53N0: IdealEqSpanCertificate' Table ![![53, 0, 0]] 
 ![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]] where
  M :=![![![53, 0, 0], ![0, 53, 0], ![0, 0, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P53P0 : CertificateIrreducibleZModOfList' 53 3 2 5 [33, 51, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 34, 13], [9, 18, 40], [0, 1]]
 g := ![![[21, 34, 10], [3, 46], [27, 38, 42], [39, 25], [1]], ![[31, 7, 38, 4], [48, 36], [51, 29, 5, 44], [41, 47], [35, 44, 27, 24]], ![[22, 6, 50, 10], [4, 6], [47, 38, 0, 24], [46, 13], [21, 21, 49, 29]]]
 h' := ![![[49, 34, 13], [1, 32, 13], [10, 3, 24], [14, 22, 25], [20, 2, 5], [0, 1]], ![[9, 18, 40], [22, 3, 14], [4, 11, 47], [25, 15, 47], [0, 38, 10], [49, 34, 13]], ![[0, 1], [40, 18, 26], [38, 39, 35], [43, 16, 34], [36, 13, 38], [9, 18, 40]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 15], []]
 b := ![[], [49, 44, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI53N0 : CertifiedPrimeIdeal' SI53N0 53 where
  n := 3
  hpos := by decide
  P := [33, 51, 48, 1]
  hirr := P53P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4289979, 3959100, -5490588]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80943, 74700, -103596]
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

def I59N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![17, -20, 1]] i)))

def SI59N0: IdealEqSpanCertificate' Table ![![59, 0, 0], ![17, -20, 1]] 
 ![![59, 0, 0], ![0, 59, 0], ![17, 39, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![17, -20, 1], ![-3, 7, -139], ![-738, 601, -33]]]
  hmulB := by decide  
  f := ![![![-16, 20, -1], ![59, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -39, 59]], ![![0, -1, 1], ![40, 92, -139], ![-3, 32, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P59P0 : CertificateIrreducibleZModOfList' 59 2 2 5 [38, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 58], [0, 1]]
 g := ![![[6, 22], [47, 29], [3], [43, 27], [8, 1]], ![[5, 37], [43, 30], [3], [23, 32], [16, 58]]]
 h' := ![![[8, 58], [43, 9], [33, 41], [18, 48], [50, 26], [0, 1]], ![[0, 1], [56, 50], [7, 18], [48, 11], [22, 33], [8, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [16, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI59N0 : CertifiedPrimeIdeal' SI59N0 59 where
  n := 2
  hpos := by decide
  P := [38, 51, 1]
  hirr := P59P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38, 49, -1799]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![519, 1190, -1799]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI59N0 : Ideal.IsPrime I59N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI59N0 B_one_repr
lemma NI59N0 : Nat.card (O ⧸ I59N0) = 3481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI59N0

def I59N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![59, 0, 0], ![21, 1, 0]] i)))

def SI59N1: IdealEqSpanCertificate' Table ![![59, 0, 0], ![21, 1, 0]] 
 ![![59, 0, 0], ![21, 1, 0], ![33, 0, 1]] where
  M :=![![![59, 0, 0], ![0, 59, 0], ![0, 0, 59]], ![![21, 1, 0], ![2, 20, 7], ![37, -30, 22]]]
  hmulB := by decide  
  f := ![![![1189, 14388, 5040], ![708, -42480, 0]], ![![407, 5115, 1792], ![296, -15104, 0]], ![![654, 8047, 2819], ![427, -23760, 0]]]
  g := ![![![1, 0, 0], ![-21, 59, 0], ![-33, 0, 59]], ![![0, 1, 0], ![-11, 20, 7], ![-1, -30, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI59N1 : Nat.card (O ⧸ I59N1) = 59 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI59N1)

lemma isPrimeI59N1 : Ideal.IsPrime I59N1 := prime_ideal_of_norm_prime hp59.out _ NI59N1
def MulI59N0 : IdealMulLeCertificate' Table 
  ![![59, 0, 0], ![17, -20, 1]] ![![59, 0, 0], ![21, 1, 0]]
  ![![59, 0, 0]] where
 M := ![![![3481, 0, 0], ![1239, 59, 0]], ![![1003, -1180, 59], ![354, -413, -118]]]
 hmul := by decide  
 g := ![![![![59, 0, 0]], ![![21, 1, 0]]], ![![![17, -20, 1]], ![![6, -7, -2]]]]
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

def I61N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![38, 3, 1]] i)))

def SI61N0: IdealEqSpanCertificate' Table ![![61, 0, 0], ![38, 3, 1]] 
 ![![61, 0, 0], ![0, 61, 0], ![38, 3, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![38, 3, 1], ![43, 5, 22], ![113, -89, 11]]]
  hmulB := by decide  
  f := ![![![-37, -3, -1], ![61, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -3, 61]], ![![0, 0, 1], ![-13, -1, 22], ![-5, -2, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P61P0 : CertificateIrreducibleZModOfList' 61 2 2 5 [36, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 60], [0, 1]]
 g := ![![[17, 39], [1], [34, 49], [54, 48], [59, 1]], ![[0, 22], [1], [58, 12], [19, 13], [57, 60]]]
 h' := ![![[59, 60], [41, 51], [57, 1], [8, 54], [11, 29], [0, 1]], ![[0, 1], [0, 10], [55, 60], [22, 7], [14, 32], [59, 60]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [34, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI61N0 : CertifiedPrimeIdeal' SI61N0 61 where
  n := 2
  hpos := by decide
  P := [36, 2, 1]
  hirr := P61P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14219, -10880, -292]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![415, -164, -292]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI61N0 : Ideal.IsPrime I61N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI61N0 B_one_repr
lemma NI61N0 : Nat.card (O ⧸ I61N0) = 3721 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI61N0

def I61N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0], ![-22, 1, 0]] i)))

def SI61N1: IdealEqSpanCertificate' Table ![![61, 0, 0], ![-22, 1, 0]] 
 ![![61, 0, 0], ![39, 1, 0], ![50, 0, 1]] where
  M :=![![![61, 0, 0], ![0, 61, 0], ![0, 0, 61]], ![![-22, 1, 0], ![2, -23, 7], ![37, -30, -21]]]
  hmulB := by decide  
  f := ![![![3107, -43027, 13104], ![-1769, -114192, 0]], ![![1975, -27489, 8372], ![-1158, -72956, 0]], ![![2546, -35268, 10741], ![-1452, -93600, 0]]]
  g := ![![![1, 0, 0], ![-39, 61, 0], ![-50, 0, 61]], ![![-1, 1, 0], ![9, -23, 7], ![37, -30, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI61N1 : Nat.card (O ⧸ I61N1) = 61 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI61N1)

lemma isPrimeI61N1 : Ideal.IsPrime I61N1 := prime_ideal_of_norm_prime hp61.out _ NI61N1
def MulI61N0 : IdealMulLeCertificate' Table 
  ![![61, 0, 0], ![38, 3, 1]] ![![61, 0, 0], ![-22, 1, 0]]
  ![![61, 0, 0]] where
 M := ![![![3721, 0, 0], ![-1342, 61, 0]], ![![2318, 183, 61], ![-793, -61, 0]]]
 hmul := by decide  
 g := ![![![![61, 0, 0]], ![![-22, 1, 0]]], ![![![38, 3, 1]], ![![-13, -1, 0]]]]
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


def P67P0 : CertificateIrreducibleZModOfList' 67 3 2 6 [16, 24, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 56, 63], [42, 10, 4], [0, 1]]
 g := ![![[62, 26, 49], [44, 0, 19], [45, 49], [15, 62], [55, 1], []], ![[42, 5, 57, 30], [10, 1, 45, 45], [44, 16], [23, 15], [25, 33], [30, 16]], ![[53, 5, 55, 24], [54, 35, 65, 47], [29, 54], [24, 23], [63, 54], [22, 16]]]
 h' := ![![[13, 56, 63], [33, 63, 7], [39, 58, 32], [42, 50, 7], [58, 4, 53], [0, 0, 1], [0, 1]], ![[42, 10, 4], [15, 54, 19], [20, 49, 21], [56, 63, 4], [42, 3, 45], [24, 11, 10], [13, 56, 63]], ![[0, 1], [34, 17, 41], [22, 27, 14], [33, 21, 56], [22, 60, 36], [5, 56, 56], [42, 10, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 14], []]
 b := ![[], [47, 45, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI67N0 : CertifiedPrimeIdeal' SI67N0 67 where
  n := 3
  hpos := by decide
  P := [16, 24, 12, 1]
  hirr := P67P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1287271, 1117560, -838974]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19213, 16680, -12522]
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

def I71N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65201, 72, 2168]] i)))

def SI71N0: IdealEqSpanCertificate' Table ![![65201, 72, 2168]] 
 ![![71, 0, 0], ![0, 71, 0], ![66, 43, 1]] where
  M :=![![![65201, 72, 2168], ![80360, 89, 2672], ![7000, 8, 233]]]
  hmulB := by decide  
  f := ![![![-9, 8, -8]], ![![-280, 223, 48]], ![![-174, 139, 25]]]
  g := ![![![-1097, -1312, 2168], ![-1352, -1617, 2672], ![-118, -141, 233]]]
  hle1 := by decide   
  hle2 := by decide  


def P71P0 : CertificateIrreducibleZModOfList' 71 2 2 6 [26, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 70], [0, 1]]
 g := ![![[52, 29], [31, 37], [], [27], [9], [1]], ![[36, 42], [62, 34], [], [27], [9], [1]]]
 h' := ![![[68, 70], [46, 10], [0, 45], [51], [16, 58], [45, 68], [0, 1]], ![[0, 1], [16, 61], [7, 26], [51], [55, 13], [54, 3], [68, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [9, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI71N0 : CertifiedPrimeIdeal' SI71N0 71 where
  n := 2
  hpos := by decide
  P := [26, 3, 1]
  hirr := P71P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-588, 1024, -5747]
  a := ![4, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5334, 3495, -5747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI71N0 : Ideal.IsPrime I71N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI71N0 B_one_repr
lemma NI71N0 : Nat.card (O ⧸ I71N0) = 5041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI71N0

def I71N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -8, 8]] i)))

def SI71N1: IdealEqSpanCertificate' Table ![![9, -8, 8]] 
 ![![71, 0, 0], ![53, 1, 0], ![63, 0, 1]] where
  M :=![![![9, -8, 8], ![280, -223, -48], ![-280, 248, -239]]]
  hmulB := by decide  
  f := ![![![-65201, -72, -2168]], ![![-49803, -55, -1656]], ![![-57953, -64, -1927]]]
  g := ![![![-1, -8, 8], ![213, -223, -48], ![23, 248, -239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI71N1 : Nat.card (O ⧸ I71N1) = 71 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI71N1)

lemma isPrimeI71N1 : Ideal.IsPrime I71N1 := prime_ideal_of_norm_prime hp71.out _ NI71N1
def MulI71N0 : IdealMulLeCertificate' Table 
  ![![65201, 72, 2168]] ![![9, -8, 8]]
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

def I73N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![56, 8, 1]] i)))

def SI73N0: IdealEqSpanCertificate' Table ![![73, 0, 0], ![56, 8, 1]] 
 ![![73, 0, 0], ![0, 73, 0], ![56, 8, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![56, 8, 1], ![53, 18, 57], ![298, -239, 34]]]
  hmulB := by decide  
  f := ![![![-55, -8, -1], ![73, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -8, 73]], ![![0, 0, 1], ![-43, -6, 57], ![-22, -7, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P73P0 : CertificateIrreducibleZModOfList' 73 2 2 6 [13, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 72], [0, 1]]
 g := ![![[72, 65], [36], [54], [56, 61], [23], [1]], ![[41, 8], [36], [54], [46, 12], [23], [1]]]
 h' := ![![[13, 72], [45, 49], [32, 6], [2, 45], [16, 34], [60, 13], [0, 1]], ![[0, 1], [25, 24], [37, 67], [3, 28], [20, 39], [10, 60], [13, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [65, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI73N0 : CertifiedPrimeIdeal' SI73N0 73 where
  n := 2
  hpos := by decide
  P := [13, 60, 1]
  hirr := P73P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![188, 225, -7500]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5756, 825, -7500]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI73N0 : Ideal.IsPrime I73N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI73N0 B_one_repr
lemma NI73N0 : Nat.card (O ⧸ I73N0) = 5329 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI73N0

def I73N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 0, 0], ![16, 1, 0]] i)))

def SI73N1: IdealEqSpanCertificate' Table ![![73, 0, 0], ![16, 1, 0]] 
 ![![73, 0, 0], ![16, 1, 0], ![39, 0, 1]] where
  M :=![![![73, 0, 0], ![0, 73, 0], ![0, 0, 73]], ![![16, 1, 0], ![2, 15, 7], ![37, -30, 17]]]
  hmulB := by decide  
  f := ![![![-191, -1440, -672], ![0, 7008, 0]], ![![-42, -315, -147], ![1, 1533, 0]], ![![-97, -769, -359], ![-23, 3744, 0]]]
  g := ![![![1, 0, 0], ![-16, 73, 0], ![-39, 0, 73]], ![![0, 1, 0], ![-7, 15, 7], ![-2, -30, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI73N1 : Nat.card (O ⧸ I73N1) = 73 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI73N1)

lemma isPrimeI73N1 : Ideal.IsPrime I73N1 := prime_ideal_of_norm_prime hp73.out _ NI73N1
def MulI73N0 : IdealMulLeCertificate' Table 
  ![![73, 0, 0], ![56, 8, 1]] ![![73, 0, 0], ![16, 1, 0]]
  ![![73, 0, 0]] where
 M := ![![![5329, 0, 0], ![1168, 73, 0]], ![![4088, 584, 73], ![949, 146, 73]]]
 hmul := by decide  
 g := ![![![![73, 0, 0]], ![![16, 1, 0]]], ![![![56, 8, 1]], ![![13, 2, 1]]]]
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

def I79N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![59, -31, 1]] i)))

def SI79N0: IdealEqSpanCertificate' Table ![![79, 0, 0], ![59, -31, 1]] 
 ![![79, 0, 0], ![0, 79, 0], ![59, 48, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![59, -31, 1], ![-25, 60, -216], ![-1145, 931, -2]]]
  hmulB := by decide  
  f := ![![![-58, 31, -1], ![79, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-59, -48, 79]], ![![0, -1, 1], ![161, 132, -216], ![-13, 13, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P79P0 : CertificateIrreducibleZModOfList' 79 2 2 6 [29, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 78], [0, 1]]
 g := ![![[20, 9], [28, 23], [60, 23], [78, 44], [18], [1]], ![[14, 70], [39, 56], [71, 56], [75, 35], [18], [1]]]
 h' := ![![[52, 78], [57, 3], [77, 55], [29, 24], [3, 53], [50, 52], [0, 1]], ![[0, 1], [55, 76], [14, 24], [13, 55], [73, 26], [68, 27], [52, 78]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [43, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI79N0 : CertifiedPrimeIdeal' SI79N0 79 where
  n := 2
  hpos := by decide
  P := [29, 27, 1]
  hirr := P79P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16445, 14188, -10692]
  a := ![6, -12, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7777, 6676, -10692]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI79N0 : Ideal.IsPrime I79N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI79N0 B_one_repr
lemma NI79N0 : Nat.card (O ⧸ I79N0) = 6241 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI79N0

def I79N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![79, 0, 0], ![-21, 1, 0]] i)))

def SI79N1: IdealEqSpanCertificate' Table ![![79, 0, 0], ![-21, 1, 0]] 
 ![![79, 0, 0], ![58, 1, 0], ![2, 0, 1]] where
  M :=![![![79, 0, 0], ![0, 79, 0], ![0, 0, 79]], ![![-21, 1, 0], ![2, -22, 7], ![37, -30, -20]]]
  hmulB := by decide  
  f := ![![![-1013, 12534, -3990], ![474, 45030, 0]], ![![-751, 9192, -2926], ![317, 33022, 0]], ![![-19, 317, -101], ![37, 1140, 0]]]
  g := ![![![1, 0, 0], ![-58, 79, 0], ![-2, 0, 79]], ![![-1, 1, 0], ![16, -22, 7], ![23, -30, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI79N1 : Nat.card (O ⧸ I79N1) = 79 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI79N1)

lemma isPrimeI79N1 : Ideal.IsPrime I79N1 := prime_ideal_of_norm_prime hp79.out _ NI79N1
def MulI79N0 : IdealMulLeCertificate' Table 
  ![![79, 0, 0], ![59, -31, 1]] ![![79, 0, 0], ![-21, 1, 0]]
  ![![79, 0, 0]] where
 M := ![![![6241, 0, 0], ![-1659, 79, 0]], ![![4661, -2449, 79], ![-1264, 711, -237]]]
 hmul := by decide  
 g := ![![![![79, 0, 0]], ![![-21, 1, 0]]], ![![![59, -31, 1]], ![![-16, 9, -3]]]]
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


lemma PB247I1_primes (p : ℕ) :
  p ∈ Set.range ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79] ↔ Nat.Prime p ∧ 31 < p ∧ p ≤ 79 := by
  rw [← List.mem_ofFn']
  convert primes_range 31 79 (by omega)

def PB247I1 : PrimesBelowBoundCertificateInterval O 31 79 247 where
  m := 11
  g := ![2, 2, 3, 2, 1, 2, 2, 1, 2, 2, 2]
  P := ![37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79]
  hP := PB247I1_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I37N0, I37N1]
    · exact ![I41N0, I41N1]
    · exact ![I43N0, I43N0, I43N1]
    · exact ![I47N0, I47N1]
    · exact ![I53N0]
    · exact ![I59N0, I59N1]
    · exact ![I61N0, I61N1]
    · exact ![I67N0]
    · exact ![I71N0, I71N1]
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
    · exact ![1369, 37]
    · exact ![1681, 41]
    · exact ![43, 43, 43]
    · exact ![2209, 47]
    · exact ![148877]
    · exact ![3481, 59]
    · exact ![3721, 61]
    · exact ![300763]
    · exact ![5041, 71]
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
      exact NI37N1
    · dsimp ; intro j
      fin_cases j
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
      exact NI79N1
  β := ![I37N1, I41N1, I43N0, I43N1, I47N1, I59N1, I61N1, I71N1, I73N1, I79N1]
  Il := ![[I37N1], [I41N1], [I43N0, I43N0, I43N1], [I47N1], [], [I59N1], [I61N1], [], [I71N1], [I73N1], [I79N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
