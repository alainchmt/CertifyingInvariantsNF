
import IdealArithmetic.Examples.NF3_1_542700_2.RI3_1_542700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, -1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![43, 0, -1]] 
 ![![83, 0, 0], ![3, 1, 0], ![40, 0, 1]] where
  M :=![![![43, 0, -1], ![-210, 13, 0], ![0, -35, 13]]]
  hmulB := by decide  
  f := ![![![-169, -35, -13]], ![![-39, -8, -3]], ![![-170, -35, -13]]]
  g := ![![![1, 0, -1], ![-3, 13, 0], ![-5, -35, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![8, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![8, 1, 0]] 
 ![![83, 0, 0], ![8, 1, 0], ![17, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![8, 1, 0], ![0, 8, 6], ![210, 30, 8]]]
  hmulB := by decide  
  f := ![![![353, 44, 0], ![-3652, 0, 0]], ![![24, 3, 0], ![-248, 0, 0]], ![![75, 8, -1], ![-776, 14, 0]]]
  g := ![![![1, 0, 0], ![-8, 83, 0], ![-17, 0, 83]], ![![0, 1, 0], ![-2, 8, 6], ![-2, 30, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-11, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-11, 1, 0]] 
 ![![83, 0, 0], ![72, 1, 0], ![49, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-11, 1, 0], ![0, -11, 6], ![210, 30, -11]]]
  hmulB := by decide  
  f := ![![![793, -72, 0], ![5976, 0, 0]], ![![694, -63, 0], ![5230, 0, 0]], ![![483, -42, -1], ![3640, 14, 0]]]
  g := ![![![1, 0, 0], ![-72, 83, 0], ![-49, 0, 83]], ![![-1, 1, 0], ![6, -11, 6], ![-17, 30, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![43, 0, -1]] ![![83, 0, 0], ![8, 1, 0]]
  ![![83, 0, 0], ![4, -12, 1]] where
 M := ![![![3569, 0, -83], ![134, 13, -8]]]
 hmul := by decide  
 g := ![![![![39, 12, -2], ![83, 0, 0]], ![![-2, 11, -1], ![75, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![4, -12, 1]] ![![83, 0, 0], ![-11, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-913, 83, 0]], ![![332, -996, 83], ![166, 166, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-11, 1, 0]]], ![![![4, -12, 1]], ![![2, 2, -1]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [85, 1, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 1, 72], [51, 87, 17], [0, 1]]
 g := ![![[39, 5, 32], [71, 73], [22, 25], [38, 24, 20], [39, 29, 1], []], ![[10, 20, 17, 81], [27, 67], [30, 34], [65, 9, 58, 42], [74, 18, 2, 21], [70, 22]], ![[6, 20, 27, 81], [87, 9], [88, 73], [37, 44, 63, 45], [13, 2, 40, 17], [36, 22]]]
 h' := ![![[67, 1, 72], [51, 46, 78], [52, 18, 47], [63, 8, 84], [67, 77, 38], [0, 0, 1], [0, 1]], ![[51, 87, 17], [69, 65, 41], [53, 42, 45], [72, 49, 52], [82, 68, 39], [52, 63, 87], [67, 1, 72]], ![[0, 1], [59, 67, 59], [45, 29, 86], [7, 32, 42], [80, 33, 12], [75, 26, 1], [51, 87, 17]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 77], []]
 b := ![[], [10, 29, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [85, 1, 60, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2225, 89, 89]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, 1, 1]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-42, -17, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-42, -17, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![55, 80, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-42, -17, 1], ![210, -12, -102], ![-3570, -475, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -80, 97]], ![![-1, -1, 1], ![60, 84, -102], ![-30, 5, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [15, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 96], [0, 1]]
 g := ![![[64, 81], [2], [47], [16], [47], [10, 1]], ![[1, 16], [2], [47], [16], [47], [20, 96]]]
 h' := ![![[10, 96], [63, 88], [44, 14], [78, 12], [67, 93], [44, 85], [0, 1]], ![[0, 1], [70, 9], [87, 83], [4, 85], [27, 4], [21, 12], [10, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [73, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [15, 87, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2591, -215, 549]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-338, -455, 549]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![5, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![5, 1, 0]] 
 ![![97, 0, 0], ![5, 1, 0], ![12, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![5, 1, 0], ![0, 5, 6], ![210, 30, 5]]]
  hmulB := by decide  
  f := ![![![186, 37, 0], ![-3589, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![16, -1, -5], ![-308, 81, 0]]]
  g := ![![![1, 0, 0], ![-5, 97, 0], ![-12, 0, 97]], ![![0, 1, 0], ![-1, 5, 6], ![0, 30, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-42, -17, 1]] ![![97, 0, 0], ![5, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![485, 97, 0]], ![![-4074, -1649, 97], ![0, -97, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![5, 1, 0]]], ![![![-42, -17, 1]], ![![0, -1, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-26, -13, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-26, -13, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![75, 88, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-26, -13, 1], ![210, 4, -78], ![-2730, -355, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -88, 101]], ![![-1, -1, 1], ![60, 68, -78], ![-30, -7, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [85, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 100], [0, 1]]
 g := ![![[6, 82], [64], [68, 95], [87], [65], [96, 1]], ![[0, 19], [64], [98, 6], [87], [65], [91, 100]]]
 h' := ![![[96, 100], [38, 48], [78, 93], [23, 14], [67, 84], [21, 41], [0, 1]], ![[0, 1], [0, 53], [17, 8], [54, 87], [51, 17], [18, 60], [96, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [93, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [85, 5, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3441, -148, 159]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-84, -140, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-23, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-23, 1, 0]] 
 ![![101, 0, 0], ![78, 1, 0], ![97, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-23, 1, 0], ![0, -23, 6], ![210, 30, -23]]]
  hmulB := by decide  
  f := ![![![691, -30, 0], ![3030, 0, 0]], ![![530, -23, 0], ![2324, 0, 0]], ![![665, -25, -1], ![2916, 17, 0]]]
  g := ![![![1, 0, 0], ![-78, 101, 0], ![-97, 0, 101]], ![![-1, 1, 0], ![12, -23, 6], ![1, 30, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-26, -13, 1]] ![![101, 0, 0], ![-23, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2323, 101, 0]], ![![-2626, -1313, 101], ![808, 303, -101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-23, 1, 0]]], ![![![-26, -13, 1]], ![![8, 3, -1]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![43, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![43, 1, 0]] 
 ![![103, 0, 0], ![43, 1, 0], ![18, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![43, 1, 0], ![0, 43, 6], ![210, 30, 43]]]
  hmulB := by decide  
  f := ![![![431, 10, 0], ![-1030, 0, 0]], ![![129, 3, 0], ![-308, 0, 0]], ![![82, -34, -5], ![-196, 86, 0]]]
  g := ![![![1, 0, 0], ![-43, 103, 0], ![-18, 0, 103]], ![![0, 1, 0], ![-19, 43, 6], ![-18, 30, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-33, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-33, 1, 0]] 
 ![![103, 0, 0], ![70, 1, 0], ![76, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-33, 1, 0], ![0, -33, 6], ![210, 30, -33]]]
  hmulB := by decide  
  f := ![![![1222, -37, 0], ![3811, 0, 0]], ![![826, -25, 0], ![2576, 0, 0]], ![![910, 0, -5], ![2838, 86, 0]]]
  g := ![![![1, 0, 0], ![-70, 103, 0], ![-76, 0, 103]], ![![-1, 1, 0], ![18, -33, 6], ![6, 30, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-10, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-10, 1, 0]] 
 ![![103, 0, 0], ![93, 1, 0], ![52, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-10, 1, 0], ![0, -10, 6], ![210, 30, -10]]]
  hmulB := by decide  
  f := ![![![371, -37, 0], ![3811, 0, 0]], ![![321, -32, 0], ![3297, 0, 0]], ![![184, -10, -5], ![1890, 86, 0]]]
  g := ![![![1, 0, 0], ![-93, 103, 0], ![-52, 0, 103]], ![![-1, 1, 0], ![6, -10, 6], ![-20, 30, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![43, 1, 0]] ![![103, 0, 0], ![-33, 1, 0]]
  ![![103, 0, 0], ![21, 36, 1]] where
 M := ![![![10609, 0, 0], ![-3399, 103, 0]], ![![4429, 103, 0], ![-1419, 10, 6]]]
 hmul := by decide  
 g := ![![![![82, -36, -1], ![103, 0, 0]], ![![-33, 1, 0], ![0, 0, 0]]], ![![![22, -35, -1], ![103, 0, 0]], ![![-15, -2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![21, 36, 1]] ![![103, 0, 0], ![-10, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1030, 103, 0]], ![![2163, 3708, 103], ![0, -309, 206]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-10, 1, 0]]], ![![![21, 36, 1]], ![![0, -3, 2]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![18, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![18, 1, 0]] 
 ![![107, 0, 0], ![18, 1, 0], ![53, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![18, 1, 0], ![0, 18, 6], ![210, 30, 18]]]
  hmulB := by decide  
  f := ![![![73, 4, 0], ![-428, 0, 0]], ![![-18, -1, 0], ![108, 0, 0]], ![![19, -2, -1], ![-110, 18, 0]]]
  g := ![![![1, 0, 0], ![-18, 107, 0], ![-53, 0, 107]], ![![0, 1, 0], ![-6, 18, 6], ![-12, 30, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![21, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![21, 1, 0]] 
 ![![107, 0, 0], ![21, 1, 0], ![87, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![21, 1, 0], ![0, 21, 6], ![210, 30, 21]]]
  hmulB := by decide  
  f := ![![![862, 41, 0], ![-4387, 0, 0]], ![![168, 8, 0], ![-855, 0, 0]], ![![684, 29, -1], ![-3481, 18, 0]]]
  g := ![![![1, 0, 0], ![-21, 107, 0], ![-87, 0, 107]], ![![0, 1, 0], ![-9, 21, 6], ![-21, 30, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-39, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-39, 1, 0]] 
 ![![107, 0, 0], ![68, 1, 0], ![14, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-39, 1, 0], ![0, -39, 6], ![210, 30, -39]]]
  hmulB := by decide  
  f := ![![![742, -19, 0], ![2033, 0, 0]], ![![508, -13, 0], ![1392, 0, 0]], ![![100, 4, -1], ![274, 18, 0]]]
  g := ![![![1, 0, 0], ![-68, 107, 0], ![-14, 0, 107]], ![![-1, 1, 0], ![24, -39, 6], ![-12, 30, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![18, 1, 0]] ![![107, 0, 0], ![21, 1, 0]]
  ![![107, 0, 0], ![-44, -47, 1]] where
 M := ![![![11449, 0, 0], ![2247, 107, 0]], ![![1926, 107, 0], ![378, 39, 6]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![6, 3, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-44, -47, 1]] ![![107, 0, 0], ![-39, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4173, 107, 0]], ![![-4708, -5029, 107], ![1926, 1819, -321]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-39, 1, 0]]], ![![![-44, -47, 1]], ![![18, 17, -3]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-19, -42, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-19, -42, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![90, 67, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-19, -42, 1], ![210, 11, -252], ![-8820, -1225, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -67, 109]], ![![-1, -1, 1], ![210, 155, -252], ![-90, -18, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [56, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [107, 108], [0, 1]]
 g := ![![[74, 35], [82], [28, 12], [81, 88], [88], [107, 1]], ![[4, 74], [82], [4, 97], [14, 21], [88], [105, 108]]]
 h' := ![![[107, 108], [6, 12], [67, 55], [42, 11], [95, 57], [3, 57], [0, 1]], ![[0, 1], [91, 97], [66, 54], [20, 98], [90, 52], [107, 52], [107, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [1, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [56, 2, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1201, 139, 264]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-229, -161, 264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![34, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![34, 1, 0]] 
 ![![109, 0, 0], ![34, 1, 0], ![98, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![34, 1, 0], ![0, 34, 6], ![210, 30, 34]]]
  hmulB := by decide  
  f := ![![![1599, 47, 0], ![-5123, 0, 0]], ![![442, 13, 0], ![-1416, 0, 0]], ![![1442, 48, 1], ![-4620, -18, 0]]]
  g := ![![![1, 0, 0], ![-34, 109, 0], ![-98, 0, 109]], ![![0, 1, 0], ![-16, 34, 6], ![-38, 30, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-19, -42, 1]] ![![109, 0, 0], ![34, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3706, 109, 0]], ![![-2071, -4578, 109], ![-436, -1417, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![34, 1, 0]]], ![![![-19, -42, 1]], ![![-4, -13, -2]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![7, 5, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![7, 5, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![7, 5, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![7, 5, 1], ![210, 37, 30], ![1050, 185, 37]]]
  hmulB := by decide  
  f := ![![![-6, -5, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -5, 113]], ![![0, 0, 1], ![0, -1, 30], ![7, 0, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [107, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [7, 112], [0, 1]]
 g := ![![[20, 60], [32], [112], [63], [31, 87], [7, 1]], ![[101, 53], [32], [112], [63], [75, 26], [14, 112]]]
 h' := ![![[7, 112], [105, 25], [79, 91], [57, 98], [73, 17], [42, 55], [0, 1]], ![[0, 1], [54, 88], [38, 22], [65, 15], [79, 96], [88, 58], [7, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [110, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [107, 106, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![527, -11, -70]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 3, -70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-30, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-30, 1, 0]] 
 ![![113, 0, 0], ![83, 1, 0], ![76, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-30, 1, 0], ![0, -30, 6], ![210, 30, -30]]]
  hmulB := by decide  
  f := ![![![1891, -63, 0], ![7119, 0, 0]], ![![1441, -48, 0], ![5425, 0, 0]], ![![1292, -38, -1], ![4864, 19, 0]]]
  g := ![![![1, 0, 0], ![-83, 113, 0], ![-76, 0, 113]], ![![-1, 1, 0], ![18, -30, 6], ![0, 30, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![7, 5, 1]] ![![113, 0, 0], ![-30, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-3390, 113, 0]], ![![791, 565, 113], ![0, -113, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-30, 1, 0]]], ![![![7, 5, 1]], ![![0, -1, 0]]]]
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
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![19, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![19, 1, 0]] 
 ![![127, 0, 0], ![19, 1, 0], ![88, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![19, 1, 0], ![0, 19, 6], ![210, 30, 19]]]
  hmulB := by decide  
  f := ![![![1502, 79, 0], ![-10033, 0, 0]], ![![228, 12, 0], ![-1523, 0, 0]], ![![1062, 40, -5], ![-7094, 106, 0]]]
  g := ![![![1, 0, 0], ![-19, 127, 0], ![-88, 0, 127]], ![![0, 1, 0], ![-7, 19, 6], ![-16, 30, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![30, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![30, 1, 0]] 
 ![![127, 0, 0], ![30, 1, 0], ![104, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![30, 1, 0], ![0, 30, 6], ![210, 30, 30]]]
  hmulB := by decide  
  f := ![![![1561, 52, 0], ![-6604, 0, 0]], ![![330, 11, 0], ![-1396, 0, 0]], ![![1292, 18, -5], ![-5466, 106, 0]]]
  g := ![![![1, 0, 0], ![-30, 127, 0], ![-104, 0, 127]], ![![0, 1, 0], ![-12, 30, 6], ![-30, 30, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-49, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-49, 1, 0]] 
 ![![127, 0, 0], ![78, 1, 0], ![2, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-49, 1, 0], ![0, -49, 6], ![210, 30, -49]]]
  hmulB := by decide  
  f := ![![![4509, -92, 0], ![11684, 0, 0]], ![![2794, -57, 0], ![7240, 0, 0]], ![![142, 38, -5], ![368, 106, 0]]]
  g := ![![![1, 0, 0], ![-78, 127, 0], ![-2, 0, 127]], ![![-1, 1, 0], ![30, -49, 6], ![-16, 30, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![19, 1, 0]] ![![127, 0, 0], ![30, 1, 0]]
  ![![127, 0, 0], ![-32, -13, 1]] where
 M := ![![![16129, 0, 0], ![3810, 127, 0]], ![![2413, 127, 0], ![570, 49, 6]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![30, 1, 0], ![0, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![6, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-32, -13, 1]] ![![127, 0, 0], ![-49, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-6223, 127, 0]], ![![-4064, -1651, 127], ![1778, 635, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-49, 1, 0]]], ![![![-32, -13, 1]], ![![14, 5, -1]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [84, 53, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 12, 34], [15, 118, 97], [0, 1]]
 g := ![![[93, 43, 33], [17, 10, 36], [82, 58], [130, 3], [117, 65], [63, 1], []], ![[1, 127, 80, 44], [116, 125, 128, 113], [24, 33], [86, 12], [70, 9], [79, 38], [22, 108]], ![[63, 114, 43, 42], [62, 44, 74, 37], [11, 13], [126, 27], [74, 27], [113, 13], [90, 108]]]
 h' := ![![[48, 12, 34], [13, 71, 65], [41, 79, 125], [95, 51, 78], [81, 63, 38], [79, 114, 117], [0, 0, 1], [0, 1]], ![[15, 118, 97], [49, 24, 128], [49, 51, 13], [121, 90, 65], [128, 18, 76], [84, 61, 128], [63, 84, 118], [48, 12, 34]], ![[0, 1], [95, 36, 69], [41, 1, 124], [21, 121, 119], [16, 50, 17], [72, 87, 17], [1, 47, 12], [15, 118, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 42], []]
 b := ![[], [0, 39, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [84, 53, 68, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9575576, 1602523, 363918]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![73096, 12233, 2778]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![23, -64, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![23, -64, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![23, 73, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![23, -64, 1], ![210, 53, -384], ![-13440, -1885, 53]]]
  hmulB := by decide  
  f := ![![![-22, 64, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -73, 137]], ![![0, -1, 1], ![66, 205, -384], ![-107, -42, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [24, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 136], [0, 1]]
 g := ![![[38, 7], [122], [74], [79, 93], [34], [17], [1]], ![[93, 130], [122], [74], [66, 44], [34], [17], [1]]]
 h' := ![![[47, 136], [5, 12], [78, 81], [22, 38], [8, 40], [31, 50], [113, 47], [0, 1]], ![[0, 1], [21, 125], [49, 56], [27, 99], [107, 97], [52, 87], [130, 90], [47, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [126, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [24, 90, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1325, 119, -4]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, 3, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-27, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-27, 1, 0]] 
 ![![137, 0, 0], ![110, 1, 0], ![84, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-27, 1, 0], ![0, -27, 6], ![210, 30, -27]]]
  hmulB := by decide  
  f := ![![![2161, -80, 0], ![10960, 0, 0]], ![![1756, -65, 0], ![8906, 0, 0]], ![![1338, -45, -1], ![6786, 23, 0]]]
  g := ![![![1, 0, 0], ![-110, 137, 0], ![-84, 0, 137]], ![![-1, 1, 0], ![18, -27, 6], ![-6, 30, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![23, -64, 1]] ![![137, 0, 0], ![-27, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-3699, 137, 0]], ![![3151, -8768, 137], ![-411, 1781, -411]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-27, 1, 0]]], ![![![23, -64, 1]], ![![-3, 13, -3]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB209I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB209I2 : PrimesBelowBoundCertificateInterval O 79 137 209 where
  m := 11
  g := ![3, 1, 2, 2, 3, 3, 2, 2, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB209I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0]
    · exact ![I137N0, I137N1]
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
    · exact ![83, 83, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
    · exact ![2248091]
    · exact ![18769, 137]
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
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I97N1, I101N1, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I109N1, I113N1, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [], [I97N1], [I101N1], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
