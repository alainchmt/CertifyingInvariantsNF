
import IdealArithmetic.Examples.NF3_1_466796_1.RI3_1_466796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-128, 27, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-128, 27, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![38, 27, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-128, 27, 1], ![-679, 9, 28], ![-19012, 3157, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -27, 83]], ![![-2, 0, 1], ![-21, -9, 28], ![-246, 26, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [41, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 82], [0, 1]]
 g := ![![[76, 81], [20, 65], [41], [27], [47, 33], [1]], ![[0, 2], [0, 18], [41], [27], [56, 50], [1]]]
 h' := ![![[38, 82], [10, 74], [30, 56], [47, 37], [65, 39], [42, 38], [0, 1]], ![[0, 1], [0, 9], [0, 27], [42, 46], [53, 44], [75, 45], [38, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [58, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [41, 45, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1996, -313, 96]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -35, 96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-28, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-28, 1, 0]] 
 ![![83, 0, 0], ![55, 1, 0], ![46, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-28, 1, 0], ![0, -28, 1], ![-679, 137, -27]]]
  hmulB := by decide  
  f := ![![![141, -5, 0], ![415, 0, 0]], ![![113, -4, 0], ![333, 0, 0]], ![![122, -4, 0], ![360, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 83, 0], ![-46, 0, 83]], ![![-1, 1, 0], ![18, -28, 1], ![-84, 137, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-128, 27, 1]] ![![83, 0, 0], ![-28, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2324, 83, 0]], ![![-10624, 2241, 83], ![2905, -747, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-28, 1, 0]]], ![![![-128, 27, 1]], ![![35, -9, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-96, 6, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-96, 6, 1]] 
 ![![89, 0, 0], ![7, 1, 0], ![40, 0, 1]] where
  M :=![![![-96, 6, 1], ![-679, 41, 7], ![-4753, 280, 48]]]
  hmulB := by decide  
  f := ![![![-8, 8, -1]], ![![7, -1, 0]], ![![-57, 22, -2]]]
  g := ![![![-2, 6, 1], ![-14, 41, 7], ![-97, 280, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![35, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![35, 1, 0]] 
 ![![89, 0, 0], ![35, 1, 0], ![21, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![35, 1, 0], ![0, 35, 1], ![-679, 137, 36]]]
  hmulB := by decide  
  f := ![![![701, 20, 0], ![-1780, 0, 0]], ![![245, 7, 0], ![-622, 0, 0]], ![![119, 3, 0], ![-302, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 89, 0], ![-21, 0, 89]], ![![0, 1, 0], ![-14, 35, 1], ![-70, 137, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-43, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-43, 1, 0]] 
 ![![89, 0, 0], ![46, 1, 0], ![20, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-43, 1, 0], ![0, -43, 1], ![-679, 137, -42]]]
  hmulB := by decide  
  f := ![![![1936, -45, 0], ![4005, 0, 0]], ![![990, -23, 0], ![2048, 0, 0]], ![![494, -11, 0], ![1022, 1, 0]]]
  g := ![![![1, 0, 0], ![-46, 89, 0], ![-20, 0, 89]], ![![-1, 1, 0], ![22, -43, 1], ![-69, 137, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-96, 6, 1]] ![![89, 0, 0], ![35, 1, 0]]
  ![![89, 0, 0], ![-111, 42, 1]] where
 M := ![![![-8544, 534, 89], ![-4039, 251, 42]]]
 hmul := by decide  
 g := ![![![![15, -36, 0], ![89, 0, 0]], ![![7, -17, 0], ![42, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-111, 42, 1]] ![![89, 0, 0], ![-43, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3827, 89, 0]], ![![-9879, 3738, 89], ![4094, -1780, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-43, 1, 0]]], ![![![-111, 42, 1]], ![![46, -20, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![0, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![0, 1, 0]] 
 ![![97, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![0, 1, 0], ![0, 0, 1], ![-679, 137, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![0, 1, 0], ![0, 0, 1], ![-7, 137, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![44, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![44, 1, 0]] 
 ![![97, 0, 0], ![44, 1, 0], ![4, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![44, 1, 0], ![0, 44, 1], ![-679, 137, 45]]]
  hmulB := by decide  
  f := ![![![1233, 28, 0], ![-2716, 0, 0]], ![![572, 13, 0], ![-1260, 0, 0]], ![![20, 0, 0], ![-44, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 97, 0], ![-4, 0, 97]], ![![0, 1, 0], ![-20, 44, 1], ![-71, 137, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-45, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-45, 1, 0]] 
 ![![97, 0, 0], ![52, 1, 0], ![12, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-45, 1, 0], ![0, -45, 1], ![-679, 137, -44]]]
  hmulB := by decide  
  f := ![![![3826, -85, 0], ![8245, 0, 0]], ![![2116, -47, 0], ![4560, 0, 0]], ![![516, -11, 0], ![1112, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 97, 0], ![-12, 0, 97]], ![![-1, 1, 0], ![24, -45, 1], ![-75, 137, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![0, 1, 0]] ![![97, 0, 0], ![44, 1, 0]]
  ![![97, 0, 0], ![-97, 44, 1]] where
 M := ![![![9409, 0, 0], ![4268, 97, 0]], ![![0, 97, 0], ![0, 44, 1]]]
 hmul := by decide  
 g := ![![![![97, 0, 0], ![0, 0, 0]], ![![44, 1, 0], ![0, 0, 0]]], ![![![97, -43, -1], ![97, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-97, 44, 1]] ![![97, 0, 0], ![-45, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-4365, 97, 0]], ![![-9409, 4268, 97], ![3686, -1940, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-45, 1, 0]]], ![![![-97, 44, 1]], ![![38, -20, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-89, 35, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-89, 35, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![12, 35, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-89, 35, 1], ![-679, 48, 36], ![-24444, 4253, 84]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-12, -35, 101]], ![![-1, 0, 1], ![-11, -12, 36], ![-252, 13, 84]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [91, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [35, 100], [0, 1]]
 g := ![![[54, 52], [6], [5, 21], [77], [24], [35, 1]], ![[56, 49], [6], [33, 80], [77], [24], [70, 100]]]
 h' := ![![[35, 100], [35, 70], [50, 39], [82, 83], [25, 73], [47, 23], [0, 1]], ![[0, 1], [61, 31], [1, 62], [58, 18], [55, 28], [44, 78], [35, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [14, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [91, 66, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2063, -6650, 1426]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-149, -560, 1426]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-36, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-36, 1, 0]] 
 ![![101, 0, 0], ![65, 1, 0], ![17, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-36, 1, 0], ![0, -36, 1], ![-679, 137, -35]]]
  hmulB := by decide  
  f := ![![![3421, -95, 0], ![9595, 0, 0]], ![![2233, -62, 0], ![6263, 0, 0]], ![![625, -17, 0], ![1753, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 101, 0], ![-17, 0, 101]], ![![-1, 1, 0], ![23, -36, 1], ![-89, 137, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-89, 35, 1]] ![![101, 0, 0], ![-36, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3636, 101, 0]], ![![-8989, 3535, 101], ![2525, -1212, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-36, 1, 0]]], ![![![-89, 35, 1]], ![![25, -12, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![34, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![34, 1, 0]] 
 ![![103, 0, 0], ![34, 1, 0], ![80, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![34, 1, 0], ![0, 34, 1], ![-679, 137, 35]]]
  hmulB := by decide  
  f := ![![![1429, 42, 0], ![-4326, 0, 0]], ![![442, 13, 0], ![-1338, 0, 0]], ![![1100, 32, 0], ![-3330, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 103, 0], ![-80, 0, 103]], ![![0, 1, 0], ![-12, 34, 1], ![-79, 137, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![34, 1, 0]] ![![103, 0, 0], ![34, 1, 0]]
  ![![103, 0, 0], ![-80, -35, 1]] where
 M := ![![![10609, 0, 0], ![3502, 103, 0]], ![![3502, 103, 0], ![1156, 68, 1]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![34, 1, 0], ![0, 0, 0]]], ![![![34, 1, 0], ![0, 0, 0]], ![![12, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-80, -35, 1]] ![![103, 0, 0], ![34, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3502, 103, 0]], ![![-8240, -3605, 103], ![-3399, -1133, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![34, 1, 0]]], ![![![-80, -35, 1]], ![![-33, -11, 0]]]]
 hle2 := by decide  

def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N0, I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N0
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-129, 25, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-129, 25, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![85, 25, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-129, 25, 1], ![-679, 8, 26], ![-17654, 2883, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -25, 107]], ![![-2, 0, 1], ![-27, -6, 26], ![-192, 19, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [60, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 106], [0, 1]]
 g := ![![[3, 9], [91, 49], [29], [31, 30], [34], [34, 1]], ![[95, 98], [45, 58], [29], [88, 77], [34], [68, 106]]]
 h' := ![![[34, 106], [104, 104], [48, 7], [66, 55], [42, 43], [100, 26], [0, 1]], ![[0, 1], [2, 3], [72, 100], [10, 52], [6, 64], [21, 81], [34, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [104, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [60, 73, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![163, -871, 192]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-151, -53, 192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-26, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-26, 1, 0]] 
 ![![107, 0, 0], ![81, 1, 0], ![73, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-26, 1, 0], ![0, -26, 1], ![-679, 137, -25]]]
  hmulB := by decide  
  f := ![![![2133, -82, 0], ![8774, 0, 0]], ![![1639, -63, 0], ![6742, 0, 0]], ![![1463, -56, 0], ![6018, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 107, 0], ![-73, 0, 107]], ![![-1, 1, 0], ![19, -26, 1], ![-93, 137, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-129, 25, 1]] ![![107, 0, 0], ![-26, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2782, 107, 0]], ![![-13803, 2675, 107], ![2675, -642, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-26, 1, 0]]], ![![![-129, 25, 1]], ![![25, -6, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-65, -9, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-65, -9, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![44, 100, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-65, -9, 1], ![-679, 72, -8], ![5432, -1775, 64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -100, 109]], ![![-1, -1, 1], ![-3, 8, -8], ![24, -75, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [70, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 108], [0, 1]]
 g := ![![[12, 3], [31], [72, 94], [95, 21], [75], [32, 1]], ![[108, 106], [31], [28, 15], [4, 88], [75], [64, 108]]]
 h' := ![![[32, 108], [32, 60], [83, 85], [108, 51], [94, 81], [49, 82], [0, 1]], ![[0, 1], [99, 49], [78, 24], [105, 58], [70, 28], [57, 27], [32, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [27, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [70, 77, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1889, -5621, 1000]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-421, -969, 1000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![8, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![8, 1, 0]] 
 ![![109, 0, 0], ![8, 1, 0], ![45, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![8, 1, 0], ![0, 8, 1], ![-679, 137, 9]]]
  hmulB := by decide  
  f := ![![![297, 37, 0], ![-4033, 0, 0]], ![![8, 1, 0], ![-108, 0, 0]], ![![121, 15, 0], ![-1643, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 109, 0], ![-45, 0, 109]], ![![0, 1, 0], ![-1, 8, 1], ![-20, 137, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-65, -9, 1]] ![![109, 0, 0], ![8, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![872, 109, 0]], ![![-7085, -981, 109], ![-1199, 0, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![8, 1, 0]]], ![![![-65, -9, 1]], ![![-11, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [23, 81, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 72, 51], [55, 40, 62], [0, 1]]
 g := ![![[93, 18, 85], [0, 32], [109, 49], [90, 87], [5, 55, 14], [1]], ![[80, 30, 44, 36], [40, 4], [20, 8], [68, 85], [88, 87, 67, 64], [18, 95, 78, 102]], ![[109, 19, 64, 85], [28, 11], [80, 16], [37, 1], [97, 50, 28, 30], [26, 94, 29, 11]]]
 h' := ![![[8, 72, 51], [83, 87, 57], [99, 15, 91], [81, 19, 106], [111, 102, 55], [90, 32, 63], [0, 1]], ![[55, 40, 62], [108, 3, 50], [24, 53, 111], [22, 91, 11], [2, 24, 57], [98, 11, 84], [8, 72, 51]], ![[0, 1], [41, 23, 6], [81, 45, 24], [0, 3, 109], [88, 100, 1], [6, 70, 79], [55, 40, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 92], []]
 b := ![[], [57, 33, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [23, 81, 50, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-92321, 82377, -10057]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-817, 729, -89]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-48, -53, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-48, -53, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![79, 74, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-48, -53, 1], ![-679, 89, -52], ![35308, -7803, 37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -74, 127]], ![![-1, -1, 1], ![27, 31, -52], ![255, -83, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [116, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 126], [0, 1]]
 g := ![![[21, 68], [111, 52], [24, 36], [109, 104], [7, 8], [104, 1]], ![[108, 59], [58, 75], [85, 91], [3, 23], [77, 119], [81, 126]]]
 h' := ![![[104, 126], [78, 24], [10, 59], [56, 121], [77, 55], [1, 32], [0, 1]], ![[0, 1], [34, 103], [50, 68], [67, 6], [82, 72], [27, 95], [104, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [27, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [116, 23, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26341, 5139, 562]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-557, -287, 562]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![52, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![52, 1, 0]] 
 ![![127, 0, 0], ![52, 1, 0], ![90, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![52, 1, 0], ![0, 52, 1], ![-679, 137, 53]]]
  hmulB := by decide  
  f := ![![![937, 18, 0], ![-2286, 0, 0]], ![![364, 7, 0], ![-888, 0, 0]], ![![646, 12, 0], ![-1576, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 127, 0], ![-90, 0, 127]], ![![0, 1, 0], ![-22, 52, 1], ![-99, 137, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-48, -53, 1]] ![![127, 0, 0], ![52, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![6604, 127, 0]], ![![-6096, -6731, 127], ![-3175, -2667, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![52, 1, 0]]], ![![![-48, -53, 1]], ![![-25, -21, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-142, 25, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-142, 25, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![120, 25, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-142, 25, 1], ![-679, -5, 26], ![-17654, 2883, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -25, 131]], ![![-2, 0, 1], ![-29, -5, 26], ![-154, 18, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [51, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 130], [0, 1]]
 g := ![![[63, 74], [20, 99], [48], [117], [9], [45], [1]], ![[66, 57], [1, 32], [48], [117], [9], [45], [1]]]
 h' := ![![[62, 130], [28, 104], [101, 19], [45, 21], [36, 36], [44, 3], [80, 62], [0, 1]], ![[0, 1], [57, 27], [100, 112], [37, 110], [41, 95], [99, 128], [125, 69], [62, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [82, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [51, 69, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3378, -1163, 74]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42, -23, 74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-26, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-26, 1, 0]] 
 ![![131, 0, 0], ![105, 1, 0], ![110, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-26, 1, 0], ![0, -26, 1], ![-679, 137, -25]]]
  hmulB := by decide  
  f := ![![![3329, -128, 0], ![16768, 0, 0]], ![![2679, -103, 0], ![13494, 0, 0]], ![![2814, -108, 0], ![14174, 1, 0]]]
  g := ![![![1, 0, 0], ![-105, 131, 0], ![-110, 0, 131]], ![![-1, 1, 0], ![20, -26, 1], ![-94, 137, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-142, 25, 1]] ![![131, 0, 0], ![-26, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3406, 131, 0]], ![![-18602, 3275, 131], ![3013, -655, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-26, 1, 0]]], ![![![-142, 25, 1]], ![![23, -5, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![28, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![28, 1, 0]] 
 ![![137, 0, 0], ![28, 1, 0], ![38, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![28, 1, 0], ![0, 28, 1], ![-679, 137, 29]]]
  hmulB := by decide  
  f := ![![![1877, 67, 0], ![-9179, 0, 0]], ![![364, 13, 0], ![-1780, 0, 0]], ![![510, 18, 0], ![-2494, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 137, 0], ![-38, 0, 137]], ![![0, 1, 0], ![-6, 28, 1], ![-41, 137, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![47, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![47, 1, 0]] 
 ![![137, 0, 0], ![47, 1, 0], ![120, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![47, 1, 0], ![0, 47, 1], ![-679, 137, 48]]]
  hmulB := by decide  
  f := ![![![1364, 29, 0], ![-3973, 0, 0]], ![![470, 10, 0], ![-1369, 0, 0]], ![![1192, 25, 0], ![-3472, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 137, 0], ![-120, 0, 137]], ![![0, 1, 0], ![-17, 47, 1], ![-94, 137, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -2, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![15, -2, 0]] 
 ![![137, 0, 0], ![61, 1, 0], ![115, 0, 1]] where
  M :=![![![15, -2, 0], ![0, 15, -2], ![1358, -274, 13]]]
  hmulB := by decide  
  f := ![![![-353, 26, 4]], ![![-177, 13, 2]], ![![-445, 32, 5]]]
  g := ![![![1, -2, 0], ![-5, 15, -2], ![121, -274, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![28, 1, 0]] ![![137, 0, 0], ![47, 1, 0]]
  ![![-353, 26, 4]] where
 M := ![![![18769, 0, 0], ![6439, 137, 0]], ![![3836, 137, 0], ![1316, 75, 1]]]
 hmul := by decide  
 g := ![![![![2055, -274, 0]], ![![705, -79, -2]]], ![![![420, -41, -2]], ![![154, -13, -1]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-353, 26, 4]] ![![15, -2, 0]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB194I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB194I2 : PrimesBelowBoundCertificateInterval O 79 137 194 where
  m := 11
  g := ![2, 3, 3, 2, 3, 2, 2, 1, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB194I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N0, I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![97, 97, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N0
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N0, I89N1, I89N2, I97N0, I97N1, I97N2, I101N1, I103N0, I107N1, I109N1, I127N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [I97N0, I97N1, I97N2], [I101N1], [I103N0, I103N0, I103N0], [I107N1], [I109N1], [], [I127N1], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
