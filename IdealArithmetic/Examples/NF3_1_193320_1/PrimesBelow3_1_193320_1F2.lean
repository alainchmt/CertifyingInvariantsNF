
import IdealArithmetic.Examples.NF3_1_193320_1.RI3_1_193320_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [27, 61, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 46, 29], [6, 36, 54], [0, 1]]
 g := ![![[69, 14, 41], [30, 65, 36], [17, 23], [60, 12], [70, 52, 1], []], ![[14, 32, 20, 61], [9, 58, 5, 48], [15, 37], [25, 40], [82, 77, 44, 68], [3, 11]], ![[5, 63, 20, 18], [3, 53, 68, 57], [71, 61], [68, 81], [22, 25, 27, 56], [61, 11]]]
 h' := ![![[46, 46, 29], [20, 14, 37], [69, 50, 6], [69, 22, 43], [19, 53, 26], [0, 0, 1], [0, 1]], ![[6, 36, 54], [14, 28, 78], [54, 78, 6], [25, 0, 28], [6, 58, 66], [43, 17, 36], [46, 46, 29]], ![[0, 1], [8, 41, 51], [82, 38, 71], [67, 61, 12], [34, 55, 74], [49, 66, 46], [6, 36, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51], []]
 b := ![[], [17, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [27, 61, 31, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-55029, -22327, -2241]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-663, -269, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![65749, 27591, 3123]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![65749, 27591, 3123]] 
 ![![89, 0, 0], ![0, 89, 0], ![64, 78, 1]] where
  M :=![![![65749, 27591, 3123], ![580878, 243760, 27591], ![5131926, 2153565, 243760]]]
  hmulB := by decide  
  f := ![![![-835, 15, 9]], ![![1674, -322, 15]], ![![898, -243, 16]]]
  g := ![![![-1507, -2427, 3123], ![-13314, -21442, 27591], ![-117626, -189435, 243760]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [10, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 88], [0, 1]]
 g := ![![[49, 9], [71], [71], [37, 4], [21, 67], [1]], ![[0, 80], [71], [71], [35, 85], [32, 22], [1]]]
 h' := ![![[44, 88], [46, 3], [20, 31], [75, 31], [57, 87], [79, 44], [0, 1]], ![[0, 1], [0, 86], [49, 58], [15, 58], [58, 2], [57, 45], [44, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [28, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [10, 45, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2266, 904, 646]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-490, -556, 646]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![835, -15, -9]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![835, -15, -9]] 
 ![![89, 0, 0], ![11, 1, 0], ![57, 0, 1]] where
  M :=![![![835, -15, -9], ![-1674, 322, -15], ![-2790, -2529, 322]]]
  hmulB := by decide  
  f := ![![![-65749, -27591, -3123]], ![![-14653, -6149, -696]], ![![-99771, -41868, -4739]]]
  g := ![![![17, -15, -9], ![-49, 322, -15], ![75, -2529, 322]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![65749, 27591, 3123]] ![![835, -15, -9]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-48, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-48, 1, 0]] 
 ![![97, 0, 0], ![49, 1, 0], ![24, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-48, 1, 0], ![0, -48, 1], ![186, 57, -48]]]
  hmulB := by decide  
  f := ![![![4657, -97, 0], ![9409, 0, 0]], ![![2401, -50, 0], ![4851, 0, 0]], ![![1176, -24, 0], ![2376, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 97, 0], ![-24, 0, 97]], ![![-1, 1, 0], ![24, -48, 1], ![-15, 57, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-26, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-26, 1, 0]] 
 ![![97, 0, 0], ![71, 1, 0], ![3, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-26, 1, 0], ![0, -26, 1], ![186, 57, -26]]]
  hmulB := by decide  
  f := ![![![1769, -68, 0], ![6596, 0, 0]], ![![1327, -51, 0], ![4948, 0, 0]], ![![59, -2, 0], ![220, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 97, 0], ![-3, 0, 97]], ![![-1, 1, 0], ![19, -26, 1], ![-39, 57, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-23, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-23, 1, 0]] 
 ![![97, 0, 0], ![74, 1, 0], ![53, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-23, 1, 0], ![0, -23, 1], ![186, 57, -23]]]
  hmulB := by decide  
  f := ![![![1151, -50, 0], ![4850, 0, 0]], ![![852, -37, 0], ![3590, 0, 0]], ![![627, -27, 0], ![2642, 1, 0]]]
  g := ![![![1, 0, 0], ![-74, 97, 0], ![-53, 0, 97]], ![![-1, 1, 0], ![17, -23, 1], ![-29, 57, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-48, 1, 0]] ![![97, 0, 0], ![-26, 1, 0]]
  ![![97, 0, 0], ![-13, 23, 1]] where
 M := ![![![9409, 0, 0], ![-2522, 97, 0]], ![![-4656, 97, 0], ![1248, -74, 1]]]
 hmul := by decide  
 g := ![![![![97, 0, 0], ![0, 0, 0]], ![![-13, -22, -1], ![97, 0, 0]]], ![![![-35, -22, -1], ![97, 0, 0]], ![![13, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-13, 23, 1]] ![![97, 0, 0], ![-23, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2231, 97, 0]], ![![-1261, 2231, 97], ![485, -485, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-23, 1, 0]]], ![![![-13, 23, 1]], ![![5, -5, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-42, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-42, 1, 0]] 
 ![![101, 0, 0], ![59, 1, 0], ![54, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-42, 1, 0], ![0, -42, 1], ![186, 57, -42]]]
  hmulB := by decide  
  f := ![![![4075, -97, 0], ![9797, 0, 0]], ![![2437, -58, 0], ![5859, 0, 0]], ![![2202, -52, 0], ![5294, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 101, 0], ![-54, 0, 101]], ![![-1, 1, 0], ![24, -42, 1], ![-9, 57, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-38, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-38, 1, 0]] 
 ![![101, 0, 0], ![63, 1, 0], ![71, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-38, 1, 0], ![0, -38, 1], ![186, 57, -38]]]
  hmulB := by decide  
  f := ![![![533, -14, 0], ![1414, 0, 0]], ![![343, -9, 0], ![910, 0, 0]], ![![395, -10, 0], ![1048, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 101, 0], ![-71, 0, 101]], ![![-1, 1, 0], ![23, -38, 1], ![-7, 57, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77981, 32724, 3704]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![77981, 32724, 3704]] 
 ![![101, 0, 0], ![80, 1, 0], ![64, 0, 1]] where
  M :=![![![77981, 32724, 3704], ![688944, 289109, 32724], ![6086664, 2554212, 289109]]]
  hmulB := by decide  
  f := ![![![-19607, -1668, 440]], ![![-14720, -1267, 332]], ![![-15496, -1188, 333]]]
  g := ![![![-27495, 32724, 3704], ![-242912, 289109, 32724], ![-2146072, 2554212, 289109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-42, 1, 0]] ![![101, 0, 0], ![-38, 1, 0]]
  ![![19607, 1668, -440]] where
 M := ![![![10201, 0, 0], ![-3838, 101, 0]], ![![-4242, 101, 0], ![1596, -80, 1]]]
 hmul := by decide  
 g := ![![![![-7876081, -3305124, -374104]], ![![2274334, 954403, 108028]]], ![![![2586258, 1085299, 122844]], ![![-746820, -313396, -35473]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![19607, 1668, -440]] ![![77981, 32724, 3704]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1, I101N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
    exact isPrimeI101N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0 ⊙ MulI101N1)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![11, 45, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![11, 45, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![11, 45, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![11, 45, 1], ![186, 68, 45], ![8370, 2751, 68]]]
  hmulB := by decide  
  f := ![![![-10, -45, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -45, 103]], ![![0, 0, 1], ![-3, -19, 45], ![74, -3, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [41, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 102], [0, 1]]
 g := ![![[38, 98], [14, 9], [92, 15], [19], [7], [90, 1]], ![[0, 5], [0, 94], [0, 88], [19], [7], [77, 102]]]
 h' := ![![[90, 102], [44, 43], [39, 3], [75, 85], [37, 88], [18, 25], [0, 1]], ![[0, 1], [0, 60], [0, 100], [0, 18], [26, 15], [2, 78], [90, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [18, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [41, 13, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2933, -43, 173]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, -76, 173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-45, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-45, 1, 0]] 
 ![![103, 0, 0], ![58, 1, 0], ![35, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-45, 1, 0], ![0, -45, 1], ![186, 57, -45]]]
  hmulB := by decide  
  f := ![![![4366, -97, 0], ![9991, 0, 0]], ![![2476, -55, 0], ![5666, 0, 0]], ![![1550, -34, 0], ![3547, 1, 0]]]
  g := ![![![1, 0, 0], ![-58, 103, 0], ![-35, 0, 103]], ![![-1, 1, 0], ![25, -45, 1], ![-15, 57, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![11, 45, 1]] ![![103, 0, 0], ![-45, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4635, 103, 0]], ![![1133, 4635, 103], ![-309, -1957, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-45, 1, 0]]], ![![![11, 45, 1]], ![![-3, -19, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [69, 3, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [48, 67, 80], [41, 39, 27], [0, 1]]
 g := ![![[97, 81, 34], [25, 92, 62], [28, 105], [86, 86, 89], [54, 3], [1]], ![[16, 44, 24, 98], [104, 90, 95, 26], [16, 85], [17, 103, 70, 5], [46, 13], [47, 14, 63, 5]], ![[56, 76, 20, 42], [16, 76, 46, 53], [1, 36], [69, 79, 84, 69], [74, 9], [46, 7, 104, 102]]]
 h' := ![![[48, 67, 80], [94, 73, 26], [41, 77, 94], [58, 62, 31], [72, 45, 14], [38, 104, 89], [0, 1]], ![[41, 39, 27], [28, 101, 6], [65, 64, 89], [45, 89, 70], [71, 16, 80], [28, 78, 21], [48, 67, 80]], ![[0, 1], [52, 40, 75], [61, 73, 31], [39, 63, 6], [77, 46, 13], [49, 32, 104], [41, 39, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 58], []]
 b := ![[], [79, 80, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [69, 3, 18, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-670997, -458388, -72546]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6271, -4284, -678]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀

instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [91, 18, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 0, 63], [20, 108, 46], [0, 1]]
 g := ![![[41, 100, 35], [38, 29], [42, 45, 45], [77, 31, 97], [55, 25], [1]], ![[57, 37, 51, 5], [60, 81], [55, 3, 53, 28], [86, 34, 88, 16], [24, 104], [53, 11, 104, 1]], ![[52, 48, 68, 71], [41, 27], [16, 71, 3, 31], [80, 73, 101, 97], [8, 83], [90, 18, 88, 108]]]
 h' := ![![[84, 0, 63], [79, 16, 12], [102, 34, 62], [78, 80, 63], [6, 11, 73], [18, 91, 104], [0, 1]], ![[20, 108, 46], [108, 5, 15], [106, 44, 9], [85, 108, 72], [79, 94, 75], [44, 7, 70], [84, 0, 63]], ![[0, 1], [56, 88, 82], [9, 31, 38], [68, 30, 83], [56, 4, 70], [28, 11, 44], [20, 108, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 68], []]
 b := ![[], [74, 31, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [91, 18, 5, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-64637, -30084, -3706]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-593, -276, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-42, 44, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-42, 44, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![71, 44, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-42, 44, 1], ![186, 15, 44], ![8184, 2694, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -44, 113]], ![![-1, 0, 1], ![-26, -17, 44], ![63, 18, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [73, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 112], [0, 1]]
 g := ![![[24, 72], [112], [69], [25], [13, 31], [56, 1]], ![[101, 41], [112], [69], [25], [54, 82], [112, 112]]]
 h' := ![![[56, 112], [42, 33], [46, 98], [87, 42], [68, 108], [93, 12], [0, 1]], ![[0, 1], [82, 80], [110, 15], [66, 71], [14, 5], [87, 101], [56, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [110, 101]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [73, 57, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7199, 3473, 477]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-236, -155, 477]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-44, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-44, 1, 0]] 
 ![![113, 0, 0], ![69, 1, 0], ![98, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-44, 1, 0], ![0, -44, 1], ![186, 57, -44]]]
  hmulB := by decide  
  f := ![![![1321, -30, 0], ![3390, 0, 0]], ![![837, -19, 0], ![2148, 0, 0]], ![![1162, -26, 0], ![2982, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 113, 0], ![-98, 0, 113]], ![![-1, 1, 0], ![26, -44, 1], ![5, 57, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-42, 44, 1]] ![![113, 0, 0], ![-44, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-4972, 113, 0]], ![![-4746, 4972, 113], ![2034, -1921, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-44, 1, 0]]], ![![![-42, 44, 1]], ![![18, -17, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)


lemma PB125I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 124 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 124 (by omega)

def PB125I2 : PrimesBelowBoundCertificateInterval O 79 124 125 where
  m := 8
  g := ![1, 2, 3, 3, 2, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB125I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![97, 97, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![12769, 113]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
      exact NI97N2
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
  β := ![I89N1, I97N0, I97N1, I97N2, I101N0, I101N1, I101N2, I103N1, I113N1]
  Il := ![[], [I89N1], [I97N0, I97N1, I97N2], [I101N0, I101N1, I101N2], [I103N1], [], [], [I113N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
