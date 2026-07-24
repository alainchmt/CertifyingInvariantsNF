
import IdealArithmetic.Examples.NF3_1_564300_3.RI3_1_564300_3
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [68, 47, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 73, 29], [61, 9, 54], [0, 1]]
 g := ![![[11, 25, 70], [77, 27, 63], [29, 68], [32, 70], [67, 60, 1], []], ![[13, 6, 80, 33], [66, 15, 22, 49], [55, 81], [42, 16], [19, 36, 48, 25], [80, 11]], ![[40, 35, 21, 18], [51, 57, 54, 47], [15, 11], [17, 77], [32, 36, 32, 5], [55, 11]]]
 h' := ![![[82, 73, 29], [76, 48, 30], [5, 5, 48], [63, 66, 63], [9, 75, 53], [0, 0, 1], [0, 1]], ![[61, 9, 54], [36, 4, 2], [46, 77, 79], [47, 41, 74], [9, 11, 79], [39, 77, 9], [82, 73, 29]], ![[0, 1], [27, 31, 51], [62, 1, 39], [70, 59, 29], [8, 80, 34], [64, 6, 73], [61, 9, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 70], []]
 b := ![[], [52, 49, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [68, 47, 23, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3818, -3569, -1162]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, -43, -14]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [67, 80, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 48, 54], [38, 40, 35], [0, 1]]
 g := ![![[83, 38, 34], [16, 40], [20, 78], [71, 26, 47], [34, 84, 1], []], ![[39, 37, 9, 56], [54, 84], [0, 64], [74, 34, 86, 29], [40, 41, 83, 70], [38, 68]], ![[37, 75, 43, 43], [47, 36], [30, 42], [16, 56, 4, 35], [43, 82, 9, 6], [57, 68]]]
 h' := ![![[46, 48, 54], [45, 2, 52], [82, 73, 60], [49, 15, 73], [36, 18, 74], [0, 0, 1], [0, 1]], ![[38, 40, 35], [27, 9, 52], [68, 49, 23], [54, 69, 81], [16, 59, 16], [15, 24, 40], [46, 48, 54]], ![[0, 1], [64, 78, 74], [86, 56, 6], [82, 5, 24], [33, 12, 88], [28, 65, 48], [38, 40, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 23], []]
 b := ![[], [17, 77, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [67, 80, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51531, -55358, 16999]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![579, -622, 191]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-11, -27, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-11, -27, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![86, 70, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-11, -27, 1], ![30, -41, -135], ![-810, 816, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -70, 97]], ![![-1, -1, 1], ![120, 97, -135], ![28, 38, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [59, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 96], [0, 1]]
 g := ![![[16, 89], [32], [93], [22], [61], [26, 1]], ![[2, 8], [32], [93], [22], [61], [52, 96]]]
 h' := ![![[26, 96], [88, 63], [91, 56], [7, 53], [23, 33], [18, 35], [0, 1]], ![[0, 1], [77, 34], [92, 41], [27, 44], [8, 64], [55, 62], [26, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [49, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [59, 71, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-449, 9, 32]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -23, 32]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![38, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![38, 1, 0]] 
 ![![97, 0, 0], ![38, 1, 0], ![41, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![38, 1, 0], ![0, 38, 5], ![30, -30, 38]]]
  hmulB := by decide  
  f := ![![![723, 19, 0], ![-1843, 0, 0]], ![![266, 7, 0], ![-678, 0, 0]], ![![239, -9, -2], ![-609, 39, 0]]]
  g := ![![![1, 0, 0], ![-38, 97, 0], ![-41, 0, 97]], ![![0, 1, 0], ![-17, 38, 5], ![-4, -30, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-11, -27, 1]] ![![97, 0, 0], ![38, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3686, 97, 0]], ![![-1067, -2619, 97], ![-388, -1067, -97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![38, 1, 0]]], ![![![-11, -27, 1]], ![![-4, -11, -1]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![11, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![11, 1, 0]] 
 ![![101, 0, 0], ![11, 1, 0], ![97, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![11, 1, 0], ![0, 11, 5], ![30, -30, 11]]]
  hmulB := by decide  
  f := ![![![441, 40, 0], ![-4040, 0, 0]], ![![33, 3, 0], ![-302, 0, 0]], ![![439, 31, -4], ![-4022, 81, 0]]]
  g := ![![![1, 0, 0], ![-11, 101, 0], ![-97, 0, 101]], ![![0, 1, 0], ![-6, 11, 5], ![-7, -30, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![24, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![24, 1, 0]] 
 ![![101, 0, 0], ![24, 1, 0], ![6, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![24, 1, 0], ![0, 24, 5], ![30, -30, 24]]]
  hmulB := by decide  
  f := ![![![1201, 50, 0], ![-5050, 0, 0]], ![![264, 11, 0], ![-1110, 0, 0]], ![![30, -18, -4], ![-126, 81, 0]]]
  g := ![![![1, 0, 0], ![-24, 101, 0], ![-6, 0, 101]], ![![0, 1, 0], ![-6, 24, 5], ![6, -30, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-35, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-35, 1, 0]] 
 ![![101, 0, 0], ![66, 1, 0], ![58, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-35, 1, 0], ![0, -35, 5], ![30, -30, -35]]]
  hmulB := by decide  
  f := ![![![1331, -38, 0], ![3838, 0, 0]], ![![876, -25, 0], ![2526, 0, 0]], ![![808, 5, -4], ![2330, 81, 0]]]
  g := ![![![1, 0, 0], ![-66, 101, 0], ![-58, 0, 101]], ![![-1, 1, 0], ![20, -35, 5], ![40, -30, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![11, 1, 0]] ![![101, 0, 0], ![24, 1, 0]]
  ![![101, 0, 0], ![-28, 7, 1]] where
 M := ![![![10201, 0, 0], ![2424, 101, 0]], ![![1111, 101, 0], ![264, 35, 5]]]
 hmul := by decide  
 g := ![![![![101, 0, 0], ![0, 0, 0]], ![![24, 1, 0], ![0, 0, 0]]], ![![![11, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-28, 7, 1]] ![![101, 0, 0], ![-35, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3535, 101, 0]], ![![-2828, 707, 101], ![1010, -303, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-35, 1, 0]]], ![![![-28, 7, 1]], ![![10, -3, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![26, 24, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![26, 24, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![26, 24, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![26, 24, 1], ![30, -4, 120], ![720, -714, -4]]]
  hmulB := by decide  
  f := ![![![-25, -24, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -24, 103]], ![![0, 0, 1], ![-30, -28, 120], ![8, -6, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [70, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 102], [0, 1]]
 g := ![![[14, 60], [44, 72], [26, 52], [59], [13], [50, 1]], ![[27, 43], [39, 31], [51, 51], [59], [13], [100, 102]]]
 h' := ![![[50, 102], [10, 67], [34, 81], [19, 19], [21, 70], [2, 61], [0, 1]], ![[0, 1], [64, 36], [67, 22], [42, 84], [19, 33], [65, 42], [50, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [84, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [70, 53, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-56, 289, -430]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![108, 103, -430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-17, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-17, 1, 0]] 
 ![![103, 0, 0], ![86, 1, 0], ![4, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-17, 1, 0], ![0, -17, 5], ![30, -30, -17]]]
  hmulB := by decide  
  f := ![![![1684, -99, 0], ![10197, 0, 0]], ![![1412, -83, 0], ![8550, 0, 0]], ![![72, 6, -3], ![436, 62, 0]]]
  g := ![![![1, 0, 0], ![-86, 103, 0], ![-4, 0, 103]], ![![-1, 1, 0], ![14, -17, 5], ![26, -30, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![26, 24, 1]] ![![103, 0, 0], ![-17, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1751, 103, 0]], ![![2678, 2472, 103], ![-412, -412, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-17, 1, 0]]], ![![![26, 24, 1]], ![![-4, -4, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-19, -51, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-19, -51, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![88, 56, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-19, -51, 1], ![30, -49, -255], ![-1530, 1536, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -56, 107]], ![![-1, -1, 1], ![210, 133, -255], ![26, 40, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [22, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 106], [0, 1]]
 g := ![![[50, 34], [0, 56], [92], [0, 61], [56], [77, 1]], ![[100, 73], [32, 51], [92], [96, 46], [56], [47, 106]]]
 h' := ![![[77, 106], [0, 26], [9, 22], [0, 78], [55, 75], [18, 22], [0, 1]], ![[0, 1], [76, 81], [98, 85], [14, 29], [52, 32], [0, 85], [77, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [25, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [22, 30, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![82, -84, -55]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 28, -55]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![41, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![41, 1, 0]] 
 ![![107, 0, 0], ![41, 1, 0], ![49, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![41, 1, 0], ![0, 41, 5], ![30, -30, 41]]]
  hmulB := by decide  
  f := ![![![1354, 33, 0], ![-3531, 0, 0]], ![![492, 12, 0], ![-1283, 0, 0]], ![![594, -2, -2], ![-1549, 43, 0]]]
  g := ![![![1, 0, 0], ![-41, 107, 0], ![-49, 0, 107]], ![![0, 1, 0], ![-18, 41, 5], ![-7, -30, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-19, -51, 1]] ![![107, 0, 0], ![41, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4387, 107, 0]], ![![-2033, -5457, 107], ![-749, -2140, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![41, 1, 0]]], ![![![-19, -51, 1]], ![![-7, -20, -2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![37, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![37, 1, 0]] 
 ![![109, 0, 0], ![37, 1, 0], ![75, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![37, 1, 0], ![0, 37, 5], ![30, -30, 37]]]
  hmulB := by decide  
  f := ![![![1407, 38, 0], ![-4142, 0, 0]], ![![481, 13, 0], ![-1416, 0, 0]], ![![943, 18, -1], ![-2776, 22, 0]]]
  g := ![![![1, 0, 0], ![-37, 109, 0], ![-75, 0, 109]], ![![0, 1, 0], ![-16, 37, 5], ![-15, -30, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-34, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-34, 1, 0]] 
 ![![109, 0, 0], ![75, 1, 0], ![74, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-34, 1, 0], ![0, -34, 5], ![30, -30, -34]]]
  hmulB := by decide  
  f := ![![![3435, -101, 0], ![11009, 0, 0]], ![![2381, -70, 0], ![7631, 0, 0]], ![![2342, -62, -1], ![7506, 22, 0]]]
  g := ![![![1, 0, 0], ![-75, 109, 0], ![-74, 0, 109]], ![![-1, 1, 0], ![20, -34, 5], ![44, -30, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-3, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-3, 1, 0]] 
 ![![109, 0, 0], ![106, 1, 0], ![20, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-3, 1, 0], ![0, -3, 5], ![30, -30, -3]]]
  hmulB := by decide  
  f := ![![![226, -75, 0], ![8175, 0, 0]], ![![220, -73, 0], ![7958, 0, 0]], ![![44, -14, -1], ![1592, 22, 0]]]
  g := ![![![1, 0, 0], ![-106, 109, 0], ![-20, 0, 109]], ![![-1, 1, 0], ![2, -3, 5], ![30, -30, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![37, 1, 0]] ![![109, 0, 0], ![-34, 1, 0]]
  ![![109, 0, 0], ![10, -43, 1]] where
 M := ![![![11881, 0, 0], ![-3706, 109, 0]], ![![4033, 109, 0], ![-1258, 3, 5]]]
 hmul := by decide  
 g := ![![![![99, 43, -1], ![109, 0, 0]], ![![-34, 1, 0], ![0, 0, 0]]], ![![![27, 44, -1], ![109, 0, 0]], ![![-12, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![10, -43, 1]] ![![109, 0, 0], ![-3, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-327, 109, 0]], ![![1090, -4687, 109], ![0, 109, -218]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-3, 1, 0]]], ![![![10, -43, 1]], ![![0, 1, -2]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![36, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![36, 1, 0]] 
 ![![113, 0, 0], ![36, 1, 0], ![12, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![36, 1, 0], ![0, 36, 5], ![30, -30, 36]]]
  hmulB := by decide  
  f := ![![![649, 18, 0], ![-2034, 0, 0]], ![![180, 5, 0], ![-564, 0, 0]], ![![60, -20, -3], ![-188, 68, 0]]]
  g := ![![![1, 0, 0], ![-36, 113, 0], ![-12, 0, 113]], ![![0, 1, 0], ![-12, 36, 5], ![6, -30, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-29, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-29, 1, 0]] 
 ![![113, 0, 0], ![84, 1, 0], ![103, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-29, 1, 0], ![0, -29, 5], ![30, -30, -29]]]
  hmulB := by decide  
  f := ![![![1538, -53, 0], ![5989, 0, 0]], ![![1132, -39, 0], ![4408, 0, 0]], ![![1406, -31, -3], ![5475, 68, 0]]]
  g := ![![![1, 0, 0], ![-84, 113, 0], ![-103, 0, 113]], ![![-1, 1, 0], ![17, -29, 5], ![49, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-7, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-7, 1, 0]] 
 ![![113, 0, 0], ![106, 1, 0], ![58, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-7, 1, 0], ![0, -7, 5], ![30, -30, -7]]]
  hmulB := by decide  
  f := ![![![694, -99, 0], ![11187, 0, 0]], ![![652, -93, 0], ![10510, 0, 0]], ![![366, -48, -3], ![5900, 68, 0]]]
  g := ![![![1, 0, 0], ![-106, 113, 0], ![-58, 0, 113]], ![![-1, 1, 0], ![4, -7, 5], ![32, -30, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![36, 1, 0]] ![![113, 0, 0], ![-29, 1, 0]]
  ![![113, 0, 0], ![-28, 24, 1]] where
 M := ![![![12769, 0, 0], ![-3277, 113, 0]], ![![4068, 113, 0], ![-1044, 7, 5]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![-1, -23, -1], ![113, 0, 0]]], ![![![36, 1, 0], ![0, 0, 0]], ![![-8, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-28, 24, 1]] ![![113, 0, 0], ![-7, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-791, 113, 0]], ![![-3164, 2712, 113], ![226, -226, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-7, 1, 0]]], ![![![-28, 24, 1]], ![![2, -2, 1]]]]
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
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![58, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![58, 1, 0]] 
 ![![127, 0, 0], ![58, 1, 0], ![13, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![58, 1, 0], ![0, 58, 5], ![30, -30, 58]]]
  hmulB := by decide  
  f := ![![![1857, 32, 0], ![-4064, 0, 0]], ![![870, 15, 0], ![-1904, 0, 0]], ![![191, -20, -2], ![-418, 51, 0]]]
  g := ![![![1, 0, 0], ![-58, 127, 0], ![-13, 0, 127]], ![![0, 1, 0], ![-27, 58, 5], ![8, -30, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-40, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-40, 1, 0]] 
 ![![127, 0, 0], ![87, 1, 0], ![61, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-40, 1, 0], ![0, -40, 5], ![30, -30, -40]]]
  hmulB := by decide  
  f := ![![![2881, -72, 0], ![9144, 0, 0]], ![![2041, -51, 0], ![6478, 0, 0]], ![![1443, -20, -2], ![4580, 51, 0]]]
  g := ![![![1, 0, 0], ![-87, 127, 0], ![-61, 0, 127]], ![![-1, 1, 0], ![25, -40, 5], ![40, -30, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-18, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-18, 1, 0]] 
 ![![127, 0, 0], ![109, 1, 0], ![113, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-18, 1, 0], ![0, -18, 5], ![30, -30, -18]]]
  hmulB := by decide  
  f := ![![![2197, -122, 0], ![15494, 0, 0]], ![![1891, -105, 0], ![13336, 0, 0]], ![![1967, -102, -2], ![13872, 51, 0]]]
  g := ![![![1, 0, 0], ![-109, 127, 0], ![-113, 0, 127]], ![![-1, 1, 0], ![11, -18, 5], ![42, -30, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![58, 1, 0]] ![![127, 0, 0], ![-40, 1, 0]]
  ![![127, 0, 0], ![44, 29, 1]] where
 M := ![![![16129, 0, 0], ![-5080, 127, 0]], ![![7366, 127, 0], ![-2320, 18, 5]]]
 hmul := by decide  
 g := ![![![![83, -29, -1], ![127, 0, 0]], ![![-40, 1, 0], ![0, 0, 0]]], ![![![14, -28, -1], ![127, 0, 0]], ![![-20, -1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![44, 29, 1]] ![![127, 0, 0], ![-18, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2286, 127, 0]], ![![5588, 3683, 127], ![-762, -508, 127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-18, 1, 0]]], ![![![44, 29, 1]], ![![-6, -4, 1]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [72, 37, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 97, 72], [42, 33, 59], [0, 1]]
 g := ![![[116, 107, 99], [5, 38, 108], [112, 7], [36, 52], [102, 39], [74, 1], []], ![[61, 105, 39, 69], [83, 46, 25, 116], [113, 108], [76, 84], [125, 80], [116, 41], [130, 75]], ![[80, 49, 19, 114], [4, 106, 116, 117], [75, 34], [84, 12], [53, 55], [83, 108], [12, 75]]]
 h' := ![![[32, 97, 72], [33, 41, 19], [92, 90, 97], [77, 75, 20], [7, 3, 107], [43, 72, 68], [0, 0, 1], [0, 1]], ![[42, 33, 59], [30, 120, 42], [30, 43, 118], [31, 71, 34], [130, 54, 79], [109, 123, 92], [48, 59, 33], [32, 97, 72]], ![[0, 1], [122, 101, 70], [127, 129, 47], [5, 116, 77], [17, 74, 76], [77, 67, 102], [114, 72, 97], [42, 33, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 123], []]
 b := ![[], [41, 52, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [72, 37, 57, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1046297, -1010534, -53186]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7987, -7714, -406]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![57, 65, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![57, 65, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![57, 65, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![57, 65, 1], ![30, 27, 325], ![1950, -1944, 27]]]
  hmulB := by decide  
  f := ![![![-56, -65, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -65, 137]], ![![0, 0, 1], ![-135, -154, 325], ![3, -27, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [80, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 136], [0, 1]]
 g := ![![[131, 101], [99], [56], [80, 69], [93], [103], [1]], ![[113, 36], [99], [56], [46, 68], [93], [103], [1]]]
 h' := ![![[69, 136], [37, 52], [55, 109], [39, 59], [14, 53], [78, 40], [57, 69], [0, 1]], ![[0, 1], [63, 85], [41, 28], [0, 78], [109, 84], [98, 97], [23, 68], [69, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [131, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [80, 68, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167, 384, -51]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, 27, -51]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-51, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-51, 1, 0]] 
 ![![137, 0, 0], ![86, 1, 0], ![110, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-51, 1, 0], ![0, -51, 5], ![30, -30, -51]]]
  hmulB := by decide  
  f := ![![![3214, -63, 0], ![8631, 0, 0]], ![![2092, -41, 0], ![5618, 0, 0]], ![![2626, -31, -2], ![7052, 55, 0]]]
  g := ![![![1, 0, 0], ![-86, 137, 0], ![-110, 0, 137]], ![![-1, 1, 0], ![28, -51, 5], ![60, -30, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![57, 65, 1]] ![![137, 0, 0], ![-51, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6987, 137, 0]], ![![7809, 8905, 137], ![-2877, -3288, 274]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-51, 1, 0]]], ![![![57, 65, 1]], ![![-21, -24, 2]]]]
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


lemma PB213I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB213I2 : PrimesBelowBoundCertificateInterval O 79 137 213 where
  m := 11
  g := ![1, 1, 2, 3, 2, 2, 3, 3, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB213I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![571787]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![101, 101, 101]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
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
  β := ![I97N1, I101N0, I101N1, I101N2, I103N1, I107N1, I109N0, I109N1, I109N2, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I137N1]
  Il := ![[], [], [I97N1], [I101N0, I101N1, I101N2], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
