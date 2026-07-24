
import IdealArithmetic.Examples.NF3_1_190291_3.RI3_1_190291_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![13, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![13, 1, 0]] 
 ![![83, 0, 0], ![13, 1, 0], ![80, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![13, 1, 0], ![0, 13, 1], ![259, 74, 13]]]
  hmulB := by decide  
  f := ![![![365, 28, 0], ![-2324, 0, 0]], ![![39, 3, 0], ![-248, 0, 0]], ![![354, 27, 0], ![-2254, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 83, 0], ![-80, 0, 83]], ![![0, 1, 0], ![-3, 13, 1], ![-21, 74, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-12, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-12, 1, 0]] 
 ![![83, 0, 0], ![71, 1, 0], ![22, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-12, 1, 0], ![0, -12, 1], ![259, 74, -12]]]
  hmulB := by decide  
  f := ![![![109, -9, 0], ![747, 0, 0]], ![![97, -8, 0], ![665, 0, 0]], ![![50, -4, 0], ![344, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 83, 0], ![-22, 0, 83]], ![![-1, 1, 0], ![10, -12, 1], ![-57, 74, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-1, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-1, 1, 0]] 
 ![![83, 0, 0], ![82, 1, 0], ![82, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-1, 1, 0], ![0, -1, 1], ![259, 74, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![249, 0, 0]], ![![2, -1, 0], ![84, 0, 0]], ![![2, -1, 0], ![84, 1, 0]]]
  g := ![![![1, 0, 0], ![-82, 83, 0], ![-82, 0, 83]], ![![-1, 1, 0], ![0, -1, 1], ![-69, 74, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![13, 1, 0]] ![![83, 0, 0], ![-12, 1, 0]]
  ![![83, 0, 0], ![-73, 1, 1]] where
 M := ![![![6889, 0, 0], ![-996, 83, 0]], ![![1079, 83, 0], ![-156, 1, 1]]]
 hmul := by decide  
 g := ![![![![83, 0, 0], ![0, 0, 0]], ![![61, 0, -1], ![83, 0, 0]]], ![![![13, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-73, 1, 1]] ![![83, 0, 0], ![-1, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-83, 83, 0]], ![![-6059, 83, 83], ![332, 0, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-1, 1, 0]]], ![![![-73, 1, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [25, 86, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 70, 51], [13, 18, 38], [0, 1]]
 g := ![![[10, 38, 85], [37, 80], [3, 78], [29, 83, 11], [13, 30, 1], []], ![[42, 59, 85, 83], [26, 84], [3, 42], [5, 81, 55, 58], [74, 14, 87, 59], [86, 20]], ![[28, 5, 71, 33], [1, 11], [44, 64], [13, 10, 17, 56], [39, 52, 45, 12], [10, 20]]]
 h' := ![![[17, 70, 51], [79, 81, 68], [5, 19, 76], [76, 41, 16], [31, 1, 10], [0, 0, 1], [0, 1]], ![[13, 18, 38], [42, 21, 15], [46, 58, 23], [11, 54, 65], [39, 1, 53], [8, 2, 18], [17, 70, 51]], ![[0, 1], [74, 76, 6], [59, 12, 79], [25, 83, 8], [35, 87, 26], [8, 87, 70], [13, 18, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7, 32], []]
 b := ![[], [84, 53, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [25, 86, 59, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-94251, -31684, -2136]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1059, -356, -24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-50, -11, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-50, -11, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![47, 86, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-50, -11, 1], ![259, 24, -11], ![-2849, -555, 24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -86, 97]], ![![-1, -1, 1], ![8, 10, -11], ![-41, -27, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [31, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 96], [0, 1]]
 g := ![![[67, 72], [11], [89], [85], [95], [57, 1]], ![[0, 25], [11], [89], [85], [95], [17, 96]]]
 h' := ![![[57, 96], [35, 13], [52, 37], [17, 63], [18, 45], [76, 17], [0, 1]], ![[0, 1], [0, 84], [27, 60], [19, 34], [61, 52], [75, 80], [57, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [72, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [31, 40, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3116, 1367, 784]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-412, -681, 784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![11, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![11, 1, 0]] 
 ![![97, 0, 0], ![11, 1, 0], ![73, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![11, 1, 0], ![0, 11, 1], ![259, 74, 11]]]
  hmulB := by decide  
  f := ![![![496, 45, 0], ![-4365, 0, 0]], ![![44, 4, 0], ![-387, 0, 0]], ![![376, 34, 0], ![-3309, 1, 0]]]
  g := ![![![1, 0, 0], ![-11, 97, 0], ![-73, 0, 97]], ![![0, 1, 0], ![-2, 11, 1], ![-14, 74, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-50, -11, 1]] ![![97, 0, 0], ![11, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![1067, 97, 0]], ![![-4850, -1067, 97], ![-291, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![11, 1, 0]]], ![![![-50, -11, 1]], ![![-3, -1, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-91, 36, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-91, 36, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![10, 36, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-91, 36, 1], ![259, -17, 36], ![9324, 2923, -17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -36, 101]], ![![-1, 0, 1], ![-1, -13, 36], ![94, 35, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [58, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 100], [0, 1]]
 g := ![![[91, 54], [76], [98, 20], [22], [43], [75, 1]], ![[0, 47], [76], [83, 81], [22], [43], [49, 100]]]
 h' := ![![[75, 100], [12, 16], [73, 51], [74, 11], [80, 27], [94, 12], [0, 1]], ![[0, 1], [0, 85], [60, 50], [91, 90], [85, 74], [85, 89], [75, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [65, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [58, 26, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1972, 9, 177]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -63, 177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-36, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-36, 1, 0]] 
 ![![101, 0, 0], ![65, 1, 0], ![17, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-36, 1, 0], ![0, -36, 1], ![259, 74, -36]]]
  hmulB := by decide  
  f := ![![![3421, -95, 0], ![9595, 0, 0]], ![![2233, -62, 0], ![6263, 0, 0]], ![![625, -17, 0], ![1753, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 101, 0], ![-17, 0, 101]], ![![-1, 1, 0], ![23, -36, 1], ![-39, 74, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-91, 36, 1]] ![![101, 0, 0], ![-36, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3636, 101, 0]], ![![-9191, 3636, 101], ![3535, -1313, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-36, 1, 0]]], ![![![-91, 36, 1]], ![![35, -13, 0]]]]
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
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-94, -17, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-94, -17, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![9, 86, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-94, -17, 1], ![259, -20, -17], ![-4403, -999, -20]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -86, 103]], ![![-1, -1, 1], ![4, 14, -17], ![-41, 7, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [102, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 102], [0, 1]]
 g := ![![[30, 66], [75, 72], [72, 7], [58], [58], [30, 1]], ![[53, 37], [72, 31], [76, 96], [58], [58], [60, 102]]]
 h' := ![![[30, 102], [75, 90], [72, 22], [92, 25], [31, 77], [30, 77], [0, 1]], ![[0, 1], [97, 13], [11, 81], [18, 78], [75, 26], [74, 26], [30, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [39, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [102, 73, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1378, 1962, 442]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-52, -350, 442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![17, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![17, 1, 0]] 
 ![![103, 0, 0], ![17, 1, 0], ![20, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![17, 1, 0], ![0, 17, 1], ![259, 74, 17]]]
  hmulB := by decide  
  f := ![![![1140, 67, 0], ![-6901, 0, 0]], ![![170, 10, 0], ![-1029, 0, 0]], ![![190, 11, 0], ![-1150, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 103, 0], ![-20, 0, 103]], ![![0, 1, 0], ![-3, 17, 1], ![-13, 74, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-94, -17, 1]] ![![103, 0, 0], ![17, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![1751, 103, 0]], ![![-9682, -1751, 103], ![-1339, -309, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![17, 1, 0]]], ![![![-94, -17, 1]], ![![-13, -3, 0]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [24, 24, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 35, 12], [70, 71, 95], [0, 1]]
 g := ![![[18, 11, 19], [63, 81, 33], [92, 90], [55, 27, 76], [29, 76], [1]], ![[59, 85, 95, 35], [76, 84, 3, 75], [23, 3], [22, 32, 79, 47], [100, 14], [30, 14, 19, 16]], ![[99, 20, 5, 84], [83, 100, 102, 21], [57, 49], [50, 27, 38, 95], [74, 44], [19, 105, 84, 91]]]
 h' := ![![[103, 35, 12], [93, 1, 74], [51, 77, 51], [71, 20, 25], [94, 23, 66], [83, 83, 66], [0, 1]], ![[70, 71, 95], [89, 52, 23], [64, 91, 51], [98, 97, 89], [2, 22, 40], [72, 89, 11], [103, 35, 12]], ![[0, 1], [95, 54, 10], [21, 46, 5], [31, 97, 100], [21, 62, 1], [37, 42, 30], [70, 71, 95]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 28], []]
 b := ![[], [4, 19, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [24, 24, 41, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-103576, -38948, -3424]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-968, -364, -32]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-103, 25, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-103, 25, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![6, 25, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-103, 25, 1], ![259, -29, 25], ![6475, 2109, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -25, 109]], ![![-1, 0, 1], ![1, -6, 25], ![61, 26, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [36, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 108], [0, 1]]
 g := ![![[93, 106], [22], [97, 36], [45, 105], [84], [31, 1]], ![[0, 3], [22], [14, 73], [30, 4], [84], [62, 108]]]
 h' := ![![[31, 108], [96, 18], [105, 83], [15, 6], [50, 66], [83, 53], [0, 1]], ![[0, 1], [0, 91], [62, 26], [92, 103], [25, 43], [91, 56], [31, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [47, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [36, 78, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9957, 4591, 515]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![63, -76, 515]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-25, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-25, 1, 0]] 
 ![![109, 0, 0], ![84, 1, 0], ![29, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-25, 1, 0], ![0, -25, 1], ![259, 74, -25]]]
  hmulB := by decide  
  f := ![![![1501, -60, 0], ![6540, 0, 0]], ![![1176, -47, 0], ![5124, 0, 0]], ![![431, -17, 0], ![1878, 1, 0]]]
  g := ![![![1, 0, 0], ![-84, 109, 0], ![-29, 0, 109]], ![![-1, 1, 0], ![19, -25, 1], ![-48, 74, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-103, 25, 1]] ![![109, 0, 0], ![-25, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2725, 109, 0]], ![![-11227, 2725, 109], ![2834, -654, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-25, 1, 0]]], ![![![-103, 25, 1]], ![![26, -6, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![38, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![38, 1, 0]] 
 ![![113, 0, 0], ![38, 1, 0], ![25, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![38, 1, 0], ![0, 38, 1], ![259, 74, 38]]]
  hmulB := by decide  
  f := ![![![39, 1, 0], ![-113, 0, 0]], ![![-38, -1, 0], ![114, 0, 0]], ![![-25, -1, 0], ![75, 1, 0]]]
  g := ![![![1, 0, 0], ![-38, 113, 0], ![-25, 0, 113]], ![![0, 1, 0], ![-13, 38, 1], ![-31, 74, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-30, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-30, 1, 0]] 
 ![![113, 0, 0], ![83, 1, 0], ![4, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-30, 1, 0], ![0, -30, 1], ![259, 74, -30]]]
  hmulB := by decide  
  f := ![![![1891, -63, 0], ![7119, 0, 0]], ![![1441, -48, 0], ![5425, 0, 0]], ![![68, -2, 0], ![256, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 113, 0], ![-4, 0, 113]], ![![-1, 1, 0], ![22, -30, 1], ![-51, 74, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-8, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-8, 1, 0]] 
 ![![113, 0, 0], ![105, 1, 0], ![49, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-8, 1, 0], ![0, -8, 1], ![259, 74, -8]]]
  hmulB := by decide  
  f := ![![![809, -101, 0], ![11413, 0, 0]], ![![753, -94, 0], ![10623, 0, 0]], ![![361, -45, 0], ![5093, 1, 0]]]
  g := ![![![1, 0, 0], ![-105, 113, 0], ![-49, 0, 113]], ![![-1, 1, 0], ![7, -8, 1], ![-63, 74, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![38, 1, 0]] ![![113, 0, 0], ![-30, 1, 0]]
  ![![113, 0, 0], ![-10, 8, 1]] where
 M := ![![![12769, 0, 0], ![-3390, 113, 0]], ![![4294, 113, 0], ![-1140, 8, 1]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![-20, -7, -1], ![113, 0, 0]]], ![![![38, 1, 0], ![0, 0, 0]], ![![-10, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-10, 8, 1]] ![![113, 0, 0], ![-8, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-904, 113, 0]], ![![-1130, 904, 113], ![339, 0, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-8, 1, 0]]], ![![![-10, 8, 1]], ![![3, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)


lemma PB124I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 123 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 123 (by omega)

def PB124I2 : PrimesBelowBoundCertificateInterval O 79 123 124 where
  m := 8
  g := ![3, 1, 2, 2, 2, 1, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB124I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![1225043]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
  β := ![I83N0, I83N1, I83N2, I97N1, I101N1, I103N1, I109N1, I113N0, I113N1, I113N2]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N1], [I103N1], [], [I109N1], [I113N0, I113N1, I113N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
