
import IdealArithmetic.Examples.NF3_1_325983_1.RI3_1_325983_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![12, 1, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![12, 1, 0]] 
 ![![83, 0, 0], ![12, 1, 0], ![2, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![12, 1, 0], ![0, 13, 5], ![105, -14, 12]]]
  hmulB := by decide  
  f := ![![![61, 5, 0], ![-415, 0, 0]], ![![-12, -1, 0], ![84, 0, 0]], ![![-2, -8, -3], ![14, 50, 0]]]
  g := ![![![1, 0, 0], ![-12, 83, 0], ![-2, 0, 83]], ![![0, 1, 0], ![-2, 13, 5], ![3, -14, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![22, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![22, 1, 0]] 
 ![![83, 0, 0], ![22, 1, 0], ![15, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![22, 1, 0], ![0, 23, 5], ![105, -14, 22]]]
  hmulB := by decide  
  f := ![![![441, 20, 0], ![-1660, 0, 0]], ![![110, 5, 0], ![-414, 0, 0]], ![![41, -12, -3], ![-154, 50, 0]]]
  g := ![![![1, 0, 0], ![-22, 83, 0], ![-15, 0, 83]], ![![0, 1, 0], ![-7, 23, 5], ![1, -14, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-35, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-35, 1, 0]] 
 ![![83, 0, 0], ![48, 1, 0], ![11, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-35, 1, 0], ![0, -34, 5], ![105, -14, -35]]]
  hmulB := by decide  
  f := ![![![1086, -31, 0], ![2573, 0, 0]], ![![666, -19, 0], ![1578, 0, 0]], ![![192, 15, -3], ![455, 50, 0]]]
  g := ![![![1, 0, 0], ![-48, 83, 0], ![-11, 0, 83]], ![![-1, 1, 0], ![19, -34, 5], ![14, -14, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![12, 1, 0]] ![![83, 0, 0], ![22, 1, 0]]
  ![![83, 0, 0], ![3, 7, 1]] where
 M := ![![![6889, 0, 0], ![1826, 83, 0]], ![![996, 83, 0], ![264, 35, 5]]]
 hmul := by decide  
 g := ![![![![80, -7, -1], ![83, 0, 0]], ![![19, -6, -1], ![83, 0, 0]]], ![![![9, -6, -1], ![83, 0, 0]], ![![3, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![3, 7, 1]] ![![83, 0, 0], ![-35, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2905, 83, 0]], ![![249, 581, 83], ![0, -249, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-35, 1, 0]]], ![![![3, 7, 1]], ![![0, -3, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![49, -25, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![49, -25, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![49, 64, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![49, -25, 1], ![105, 10, -125], ![-2646, 371, 35]]]
  hmulB := by decide  
  f := ![![![-48, 25, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -64, 89]], ![![0, -1, 1], ![70, 90, -125], ![-49, -21, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [14, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 88], [0, 1]]
 g := ![![[22, 16], [80], [9], [0, 16], [45, 79], [1]], ![[78, 73], [80], [9], [56, 73], [10, 10], [1]]]
 h' := ![![[48, 88], [71, 85], [52, 76], [0, 3], [82, 4], [75, 48], [0, 1]], ![[0, 1], [57, 4], [51, 13], [55, 86], [7, 85], [65, 41], [48, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [64, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [14, 41, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2093, 1119, -1483]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![840, 1079, -1483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![36, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![36, 1, 0]] 
 ![![89, 0, 0], ![36, 1, 0], ![54, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![36, 1, 0], ![0, 37, 5], ![105, -14, 36]]]
  hmulB := by decide  
  f := ![![![613, 17, 0], ![-1513, 0, 0]], ![![252, 7, 0], ![-622, 0, 0]], ![![342, 2, -1], ![-844, 18, 0]]]
  g := ![![![1, 0, 0], ![-36, 89, 0], ![-54, 0, 89]], ![![0, 1, 0], ![-18, 37, 5], ![-15, -14, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![49, -25, 1]] ![![89, 0, 0], ![36, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3204, 89, 0]], ![![4361, -2225, 89], ![1869, -890, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![36, 1, 0]]], ![![![49, -25, 1]], ![![21, -10, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![36, 41, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![36, 41, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![36, 41, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![36, 41, 1], ![105, 63, 205], ![4284, -553, 22]]]
  hmulB := by decide  
  f := ![![![-35, -41, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-36, -41, 97]], ![![0, 0, 1], ![-75, -86, 205], ![36, -15, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [67, 71, 1] where
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
 g := ![![[72, 81], [75], [3], [35], [50], [26, 1]], ![[44, 16], [75], [3], [35], [50], [52, 96]]]
 h' := ![![[26, 96], [16, 88], [26, 50], [18, 10], [61, 61], [4, 27], [0, 1]], ![[0, 1], [73, 9], [65, 47], [84, 87], [95, 36], [27, 70], [26, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [11, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [67, 71, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![438, 903, -198]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, 93, -198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-11, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-11, 1, 0]] 
 ![![97, 0, 0], ![86, 1, 0], ![75, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-11, 1, 0], ![0, -10, 5], ![105, -14, -11]]]
  hmulB := by decide  
  f := ![![![672, -61, 0], ![5917, 0, 0]], ![![584, -53, 0], ![5142, 0, 0]], ![![518, -43, -2], ![4561, 39, 0]]]
  g := ![![![1, 0, 0], ![-86, 97, 0], ![-75, 0, 97]], ![![-1, 1, 0], ![5, -10, 5], ![22, -14, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![36, 41, 1]] ![![97, 0, 0], ![-11, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1067, 97, 0]], ![![3492, 3977, 97], ![-291, -388, 194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-11, 1, 0]]], ![![![36, 41, 1]], ![![-3, -4, 2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [39, 33, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 73, 82], [67, 27, 19], [0, 1]]
 g := ![![[37, 22, 58], [39, 20], [5, 76, 22], [9, 36], [46, 30], [1]], ![[68, 4, 37, 92], [54, 78], [91, 39, 78, 71], [79, 54], [33, 56], [68, 29, 15, 9]], ![[85, 35, 21, 22], [49, 30], [3, 19, 66, 36], [28, 80], [12, 70], [54, 68, 13, 92]]]
 h' := ![![[72, 73, 82], [43, 17, 19], [7, 19, 90], [44, 44, 74], [30, 88, 95], [62, 68, 38], [0, 1]], ![[67, 27, 19], [64, 79, 89], [94, 61, 49], [31, 95, 51], [48, 8, 85], [27, 14, 37], [72, 73, 82]], ![[0, 1], [85, 5, 94], [28, 21, 63], [75, 63, 77], [37, 5, 22], [0, 19, 26], [67, 27, 19]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 8], []]
 b := ![[], [37, 71, 27], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [39, 33, 63, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5959, -2121, -2626]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59, -21, -26]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![53, 14, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![53, 14, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![53, 14, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![53, 14, 1], ![105, 53, 70], ![1449, -175, 39]]]
  hmulB := by decide  
  f := ![![![-52, -14, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -14, 103]], ![![0, 0, 1], ![-35, -9, 70], ![-6, -7, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [63, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 102], [0, 1]]
 g := ![![[76, 18], [12, 1], [43, 15], [68], [92], [53, 1]], ![[0, 85], [65, 102], [14, 88], [68], [92], [3, 102]]]
 h' := ![![[53, 102], [68, 92], [72, 102], [101, 85], [70, 58], [60, 68], [0, 1]], ![[0, 1], [0, 11], [19, 1], [74, 18], [54, 45], [59, 35], [53, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [60, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [63, 50, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2193, 1825, -2246]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1177, 323, -2246]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![33, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![33, 1, 0]] 
 ![![103, 0, 0], ![33, 1, 0], ![64, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![33, 1, 0], ![0, 34, 5], ![105, -14, 33]]]
  hmulB := by decide  
  f := ![![![298, 9, 0], ![-927, 0, 0]], ![![66, 2, 0], ![-205, 0, 0]], ![![214, -14, -3], ![-666, 62, 0]]]
  g := ![![![1, 0, 0], ![-33, 103, 0], ![-64, 0, 103]], ![![0, 1, 0], ![-14, 34, 5], ![-15, -14, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![53, 14, 1]] ![![103, 0, 0], ![33, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3399, 103, 0]], ![![5459, 1442, 103], ![1854, 515, 103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![33, 1, 0]]], ![![![53, 14, 1]], ![![18, 5, 1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-10, 30, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-10, 30, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![97, 30, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-10, 30, 1], ![105, 6, 150], ![3129, -399, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -30, 107]], ![![-1, 0, 1], ![-135, -42, 150], ![51, 3, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [80, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 106], [0, 1]]
 g := ![![[52, 64], [88, 36], [52], [100, 92], [3], [13, 1]], ![[28, 43], [21, 71], [52], [12, 15], [3], [26, 106]]]
 h' := ![![[13, 106], [22, 99], [103, 101], [25, 42], [18, 29], [30, 89], [0, 1]], ![[0, 1], [25, 8], [25, 6], [36, 65], [74, 78], [10, 18], [13, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [7, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [80, 94, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2159, 1013, -1960]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1797, 559, -1960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-43, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-43, 1, 0]] 
 ![![107, 0, 0], ![64, 1, 0], ![24, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-43, 1, 0], ![0, -42, 5], ![105, -14, -43]]]
  hmulB := by decide  
  f := ![![![2452, -57, 0], ![6099, 0, 0]], ![![1506, -35, 0], ![3746, 0, 0]], ![![554, 4, -2], ![1378, 43, 0]]]
  g := ![![![1, 0, 0], ![-64, 107, 0], ![-24, 0, 107]], ![![-1, 1, 0], ![24, -42, 5], ![19, -14, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-10, 30, 1]] ![![107, 0, 0], ![-43, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4601, 107, 0]], ![![-1070, 3210, 107], ![535, -1284, 107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-43, 1, 0]]], ![![![-10, 30, 1]], ![![5, -12, 1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![52, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![52, 1, 0]] 
 ![![109, 0, 0], ![52, 1, 0], ![81, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![52, 1, 0], ![0, 53, 5], ![105, -14, 52]]]
  hmulB := by decide  
  f := ![![![1509, 29, 0], ![-3161, 0, 0]], ![![676, 13, 0], ![-1416, 0, 0]], ![![1129, 11, -1], ![-2365, 22, 0]]]
  g := ![![![1, 0, 0], ![-52, 109, 0], ![-81, 0, 109]], ![![0, 1, 0], ![-29, 53, 5], ![-31, -14, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-34, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-34, 1, 0]] 
 ![![109, 0, 0], ![75, 1, 0], ![59, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-34, 1, 0], ![0, -33, 5], ![105, -14, -34]]]
  hmulB := by decide  
  f := ![![![3435, -101, 0], ![11009, 0, 0]], ![![2381, -70, 0], ![7631, 0, 0]], ![![1893, -49, -1], ![6067, 22, 0]]]
  g := ![![![1, 0, 0], ![-75, 109, 0], ![-59, 0, 109]], ![![-1, 1, 0], ![20, -33, 5], ![29, -14, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-19, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-19, 1, 0]] 
 ![![109, 0, 0], ![90, 1, 0], ![106, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-19, 1, 0], ![0, -18, 5], ![105, -14, -19]]]
  hmulB := by decide  
  f := ![![![970, -51, 0], ![5559, 0, 0]], ![![780, -41, 0], ![4470, 0, 0]], ![![944, -46, -1], ![5410, 22, 0]]]
  g := ![![![1, 0, 0], ![-90, 109, 0], ![-106, 0, 109]], ![![-1, 1, 0], ![10, -18, 5], ![31, -14, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![52, 1, 0]] ![![109, 0, 0], ![-34, 1, 0]]
  ![![109, 0, 0], ![17, -18, 1]] where
 M := ![![![11881, 0, 0], ![-3706, 109, 0]], ![![5668, 109, 0], ![-1768, 19, 5]]]
 hmul := by decide  
 g := ![![![![92, 18, -1], ![109, 0, 0]], ![![-34, 1, 0], ![0, 0, 0]]], ![![![35, 19, -1], ![109, 0, 0]], ![![-17, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![17, -18, 1]] ![![109, 0, 0], ![-19, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2071, 109, 0]], ![![1853, -1962, 109], ![-218, 327, -109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-19, 1, 0]]], ![![![17, -18, 1]], ![![-2, 3, -1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-55, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-55, 1, 0]] 
 ![![113, 0, 0], ![58, 1, 0], ![84, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-55, 1, 0], ![0, -54, 5], ![105, -14, -55]]]
  hmulB := by decide  
  f := ![![![4676, -85, 0], ![9605, 0, 0]], ![![2366, -43, 0], ![4860, 0, 0]], ![![3438, -30, -3], ![7062, 68, 0]]]
  g := ![![![1, 0, 0], ![-58, 113, 0], ![-84, 0, 113]], ![![-1, 1, 0], ![24, -54, 5], ![49, -14, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-39, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-39, 1, 0]] 
 ![![113, 0, 0], ![74, 1, 0], ![20, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-39, 1, 0], ![0, -38, 5], ![105, -14, -39]]]
  hmulB := by decide  
  f := ![![![1210, -31, 0], ![3503, 0, 0]], ![![820, -21, 0], ![2374, 0, 0]], ![![268, 16, -3], ![776, 68, 0]]]
  g := ![![![1, 0, 0], ![-74, 113, 0], ![-20, 0, 113]], ![![-1, 1, 0], ![24, -38, 5], ![17, -14, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 1, 1]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![17, 1, 1]] 
 ![![113, 0, 0], ![93, 1, 0], ![37, 0, 1]] where
  M :=![![![17, 1, 1], ![105, 4, 5], ![84, 7, 3]]]
  hmulB := by decide  
  f := ![![![-23, 4, 1]], ![![-18, 3, 1]], ![![-4, 1, 0]]]
  g := ![![![-1, 1, 1], ![-4, 4, 5], ![-6, 7, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-55, 1, 0]] ![![113, 0, 0], ![-39, 1, 0]]
  ![![-23, 4, 1]] where
 M := ![![![12769, 0, 0], ![-4407, 113, 0]], ![![-6215, 113, 0], ![2145, -93, 5]]]
 hmul := by decide  
 g := ![![![![1921, 113, 113]], ![![-558, -35, -34]]], ![![![-830, -51, -50]], ![![240, 16, 15]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-23, 4, 1]] ![![17, 1, 1]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![14, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![14, 1, 0]] 
 ![![127, 0, 0], ![14, 1, 0], ![85, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![14, 1, 0], ![0, 15, 5], ![105, -14, 14]]]
  hmulB := by decide  
  f := ![![![1597, 114, 0], ![-14478, 0, 0]], ![![154, 11, 0], ![-1396, 0, 0]], ![![1051, 69, -2], ![-9528, 51, 0]]]
  g := ![![![1, 0, 0], ![-14, 127, 0], ![-85, 0, 127]], ![![0, 1, 0], ![-5, 15, 5], ![-7, -14, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-13, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-13, 1, 0]] 
 ![![127, 0, 0], ![114, 1, 0], ![45, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-13, 1, 0], ![0, -12, 5], ![105, -14, -13]]]
  hmulB := by decide  
  f := ![![![1197, -92, 0], ![11684, 0, 0]], ![![1080, -83, 0], ![10542, 0, 0]], ![![427, -28, -2], ![4168, 51, 0]]]
  g := ![![![1, 0, 0], ![-114, 127, 0], ![-45, 0, 127]], ![![-1, 1, 0], ![9, -12, 5], ![18, -14, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-2, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-2, 1, 0]] 
 ![![127, 0, 0], ![125, 1, 0], ![25, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-2, 1, 0], ![0, -1, 5], ![105, -14, -2]]]
  hmulB := by decide  
  f := ![![![3, 62, -315], ![127, 8001, 0]], ![![1, 62, -310], ![1, 7874, 0]], ![![1, 12, -62], ![51, 1575, 0]]]
  g := ![![![1, 0, 0], ![-125, 127, 0], ![-25, 0, 127]], ![![-1, 1, 0], ![0, -1, 5], ![15, -14, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![14, 1, 0]] ![![127, 0, 0], ![-13, 1, 0]]
  ![![127, 0, 0], ![-11, -25, 1]] where
 M := ![![![16129, 0, 0], ![-1651, 127, 0]], ![![1778, 127, 0], ![-182, 2, 5]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![-2, 26, -1], ![127, 0, 0]]], ![![![14, 1, 0], ![0, 0, 0]], ![![-1, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-11, -25, 1]] ![![127, 0, 0], ![-2, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-254, 127, 0]], ![![-1397, -3175, 127], ![127, 0, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-2, 1, 0]]], ![![![-11, -25, 1]], ![![1, 0, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![32, -28, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![32, -28, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![32, 103, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![32, -28, 1], ![105, -10, -140], ![-2961, 413, 18]]]
  hmulB := by decide  
  f := ![![![-31, 28, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -103, 131]], ![![0, -1, 1], ![35, 110, -140], ![-27, -11, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [25, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 130], [0, 1]]
 g := ![![[120, 21], [107, 33], [75], [81], [101], [38], [1]], ![[0, 110], [12, 98], [75], [81], [101], [38], [1]]]
 h' := ![![[13, 130], [76, 105], [71, 66], [80, 59], [3, 9], [68, 106], [106, 13], [0, 1]], ![[0, 1], [0, 26], [12, 65], [61, 72], [120, 122], [5, 25], [13, 118], [13, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [116, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [25, 118, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![202563, 95221, -80134]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21121, 63733, -80134]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![9, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![9, 1, 0]] 
 ![![131, 0, 0], ![9, 1, 0], ![113, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![9, 1, 0], ![0, 10, 5], ![105, -14, 9]]]
  hmulB := by decide  
  f := ![![![793, 88, 0], ![-11528, 0, 0]], ![![45, 5, 0], ![-654, 0, 0]], ![![667, 66, -4], ![-9696, 105, 0]]]
  g := ![![![1, 0, 0], ![-9, 131, 0], ![-113, 0, 131]], ![![0, 1, 0], ![-5, 10, 5], ![-6, -14, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![32, -28, 1]] ![![131, 0, 0], ![9, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![1179, 131, 0]], ![![4192, -3668, 131], ![393, -262, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![9, 1, 0]]], ![![![32, -28, 1]], ![![3, -2, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [95, 122, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 41, 26], [49, 95, 111], [0, 1]]
 g := ![![[92, 90, 38], [], [4, 73], [22, 49, 69], [127, 69], [77, 1], []], ![[116, 55, 123, 125], [107, 129], [111, 129], [127, 64, 94, 62], [27, 121], [116, 120], [69, 128]], ![[116, 40, 66, 48], [1, 129], [52, 98], [13, 84, 99, 84], [14, 120], [42, 37], [121, 128]]]
 h' := ![![[28, 41, 26], [118, 83, 77], [23, 112], [102, 0, 22], [30, 60, 84], [83, 101, 53], [0, 0, 1], [0, 1]], ![[49, 95, 111], [37, 76, 20], [8, 71, 35], [2, 28, 35], [8, 76, 87], [92, 86, 126], [120, 76, 95], [28, 41, 26]], ![[0, 1], [44, 115, 40], [31, 91, 102], [54, 109, 80], [109, 1, 103], [84, 87, 95], [85, 61, 41], [49, 95, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 117], []]
 b := ![[], [24, 97, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [95, 122, 60, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![538136, -100421, 47128]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3928, -733, 344]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB162I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB162I2 : PrimesBelowBoundCertificateInterval O 79 137 162 where
  m := 11
  g := ![3, 2, 2, 1, 2, 2, 3, 3, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB162I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
    · exact ![I137N0]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
    · exact ![2571353]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I103N1, I107N1, I109N0, I109N1, I109N2, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I131N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
