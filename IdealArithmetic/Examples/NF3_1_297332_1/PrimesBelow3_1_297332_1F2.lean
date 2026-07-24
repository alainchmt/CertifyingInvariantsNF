
import IdealArithmetic.Examples.NF3_1_297332_1.RI3_1_297332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 5, -2]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![45, 5, -2]] 
 ![![83, 0, 0], ![0, 83, 0], ![19, 39, 1]] where
  M :=![![![45, 5, -2], ![-308, -25, 10], ![770, 21, -25]]]
  hmulB := by decide  
  f := ![![![-5, -1, 0]], ![![0, -5, -2]], ![![-3, -3, -1]]]
  g := ![![![1, 1, -2], ![-6, -5, 10], ![15, 12, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [79, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 82], [0, 1]]
 g := ![![[57, 70], [59, 36], [26], [64], [33, 26], [1]], ![[81, 13], [50, 47], [26], [64], [68, 57], [1]]]
 h' := ![![[62, 82], [70, 53], [22, 77], [1, 21], [49, 8], [4, 62], [0, 1]], ![[0, 1], [36, 30], [65, 6], [58, 62], [47, 75], [30, 21], [62, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [41, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [79, 21, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![387, 126, 16]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1, -6, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![5, 1, 0]] 
 ![![83, 0, 0], ![5, 1, 0], ![29, 0, 1]] where
  M :=![![![5, 1, 0], ![0, 5, 2], ![154, 35, 5]]]
  hmulB := by decide  
  f := ![![![-45, -5, 2]], ![![1, 0, 0]], ![![-25, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 5, 2], ![-2, 35, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![45, 5, -2]] ![![5, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![21, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![21, 1, 0]] 
 ![![89, 0, 0], ![21, 1, 0], ![2, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![21, 1, 0], ![0, 21, 2], ![154, 35, 21]]]
  hmulB := by decide  
  f := ![![![316, 15, 0], ![-1335, 0, 0]], ![![42, 2, 0], ![-177, 0, 0]], ![![-8, -11, -1], ![34, 45, 0]]]
  g := ![![![1, 0, 0], ![-21, 89, 0], ![-2, 0, 89]], ![![0, 1, 0], ![-5, 21, 2], ![-7, 35, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-13, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-13, 1, 0]] 
 ![![89, 0, 0], ![76, 1, 0], ![49, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-13, 1, 0], ![0, -13, 2], ![154, 35, -13]]]
  hmulB := by decide  
  f := ![![![729, -56, 0], ![4984, 0, 0]], ![![612, -47, 0], ![4184, 0, 0]], ![![411, -25, -1], ![2810, 45, 0]]]
  g := ![![![1, 0, 0], ![-76, 89, 0], ![-49, 0, 89]], ![![-1, 1, 0], ![10, -13, 2], ![-21, 35, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-8, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-8, 1, 0]] 
 ![![89, 0, 0], ![81, 1, 0], ![57, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-8, 1, 0], ![0, -8, 2], ![154, 35, -8]]]
  hmulB := by decide  
  f := ![![![641, -80, 0], ![7120, 0, 0]], ![![585, -73, 0], ![6498, 0, 0]], ![![417, -48, -1], ![4632, 45, 0]]]
  g := ![![![1, 0, 0], ![-81, 89, 0], ![-57, 0, 89]], ![![-1, 1, 0], ![6, -8, 2], ![-25, 35, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![21, 1, 0]] ![![89, 0, 0], ![-13, 1, 0]]
  ![![89, 0, 0], ![-3, 4, 1]] where
 M := ![![![7921, 0, 0], ![-1157, 89, 0]], ![![1869, 89, 0], ![-273, 8, 2]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![-10, -3, -1], ![89, 0, 0]]], ![![![21, 1, 0], ![0, 0, 0]], ![![-3, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-3, 4, 1]] ![![89, 0, 0], ![-8, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-712, 89, 0]], ![![-267, 356, 89], ![178, 0, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-8, 1, 0]]], ![![![-3, 4, 1]], ![![2, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [69, 5, 84, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 2, 10], [30, 94, 87], [0, 1]]
 g := ![![[86, 29, 49], [59, 95], [85, 25], [46, 49], [30, 72], [1]], ![[20, 66, 31, 40], [87, 94], [45, 35], [68, 8], [22, 64], [0, 77, 20, 30]], ![[89, 36, 22, 63], [7, 81], [45, 32], [24, 61], [26, 53], [78, 64, 68, 67]]]
 h' := ![![[80, 2, 10], [28, 12, 7], [5, 46, 80], [70, 24, 92], [72, 34, 7], [28, 92, 13], [0, 1]], ![[30, 94, 87], [65, 87, 2], [65, 36, 26], [58, 3, 61], [26, 34, 28], [34, 10, 8], [80, 2, 10]], ![[0, 1], [96, 95, 88], [71, 15, 88], [84, 70, 41], [24, 29, 62], [84, 92, 76], [30, 94, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 14], []]
 b := ![[], [14, 37, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [69, 5, 84, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-122899, 106797, 52962]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1267, 1101, 546]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-20, -19, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-20, -19, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![81, 82, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-20, -19, 1], ![154, 15, -38], ![-2926, -588, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -82, 101]], ![![-1, -1, 1], ![32, 31, -38], ![-41, -18, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [42, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 100], [0, 1]]
 g := ![![[78, 97], [68], [86, 43], [68], [19], [57, 1]], ![[52, 4], [68], [12, 58], [68], [19], [13, 100]]]
 h' := ![![[57, 100], [43, 20], [24, 88], [74, 12], [1, 88], [30, 76], [0, 1]], ![[0, 1], [72, 81], [91, 13], [51, 89], [68, 13], [19, 25], [57, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [13, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [42, 44, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1014, -77, 121]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-87, -99, 121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![38, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![38, 1, 0]] 
 ![![101, 0, 0], ![38, 1, 0], ![86, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![38, 1, 0], ![0, 38, 2], ![154, 35, 38]]]
  hmulB := by decide  
  f := ![![![229, 6, 0], ![-606, 0, 0]], ![![38, 1, 0], ![-100, 0, 0]], ![![198, -14, -1], ![-524, 51, 0]]]
  g := ![![![1, 0, 0], ![-38, 101, 0], ![-86, 0, 101]], ![![0, 1, 0], ![-16, 38, 2], ![-44, 35, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-20, -19, 1]] ![![101, 0, 0], ![38, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![3838, 101, 0]], ![![-2020, -1919, 101], ![-606, -707, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![38, 1, 0]]], ![![![-20, -19, 1]], ![![-6, -7, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [62, 79, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 59, 5], [27, 43, 98], [0, 1]]
 g := ![![[37, 36, 59], [63, 56, 81], [0, 42, 15], [86, 26], [54, 1], [1]], ![[61, 4, 0, 11], [40, 88, 8, 40], [87, 88, 78, 75], [35, 19], [85, 58], [59, 96, 77, 22]], ![[49, 52, 13, 68], [4, 6, 38, 28], [87, 2, 66, 9], [7, 60], [29, 8], [87, 76, 54, 81]]]
 h' := ![![[75, 59, 5], [8, 100, 70], [0, 82, 9], [76, 7, 85], [84, 9, 52], [41, 24, 102], [0, 1]], ![[27, 43, 98], [94, 101, 8], [35, 71, 76], [59, 59, 85], [13, 43, 15], [37, 23, 77], [75, 59, 5]], ![[0, 1], [59, 5, 25], [15, 53, 18], [28, 37, 36], [16, 51, 36], [75, 56, 27], [27, 43, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 84], []]
 b := ![[], [3, 56, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [62, 79, 1, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-177881, -111755, -28531]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1727, -1085, -277]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-7, -11, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-7, -11, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![100, 96, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-7, -11, 1], ![154, 28, -22], ![-1694, -308, 28]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-100, -96, 107]], ![![-1, -1, 1], ![22, 20, -22], ![-42, -28, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [95, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 106], [0, 1]]
 g := ![![[66, 13], [98, 99], [92], [84, 4], [52], [43, 1]], ![[90, 94], [75, 8], [92], [42, 103], [52], [86, 106]]]
 h' := ![![[43, 106], [106, 86], [26, 62], [45, 78], [22, 105], [88, 42], [0, 1]], ![[0, 1], [59, 21], [17, 45], [82, 29], [43, 2], [75, 65], [43, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [76, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [95, 64, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![403, 83, -27]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, 25, -27]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![22, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![22, 1, 0]] 
 ![![107, 0, 0], ![22, 1, 0], ![79, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![22, 1, 0], ![0, 22, 2], ![154, 35, 22]]]
  hmulB := by decide  
  f := ![![![1167, 53, 0], ![-5671, 0, 0]], ![![198, 9, 0], ![-962, 0, 0]], ![![839, 27, -1], ![-4077, 54, 0]]]
  g := ![![![1, 0, 0], ![-22, 107, 0], ![-79, 0, 107]], ![![0, 1, 0], ![-6, 22, 2], ![-22, 35, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-7, -11, 1]] ![![107, 0, 0], ![22, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2354, 107, 0]], ![![-749, -1177, 107], ![0, -214, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![22, 1, 0]]], ![![![-7, -11, 1]], ![![0, -2, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [91, 20, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [18, 70, 100], [55, 38, 9], [0, 1]]
 g := ![![[1, 19, 105], [43, 7], [24, 107, 16], [89, 54, 43], [19, 97], [1]], ![[45, 3, 102, 12], [45, 81], [51, 61, 12, 48], [63, 84, 2, 25], [20, 12], [15, 44, 90, 34]], ![[7, 53, 108, 38], [9, 36], [44, 1, 65, 80], [75, 30, 35, 74], [6, 80], [53, 57, 103, 75]]]
 h' := ![![[18, 70, 100], [27, 23, 66], [105, 28, 15], [76, 99, 4], [12, 101, 77], [18, 89, 73], [0, 1]], ![[55, 38, 9], [72, 23, 12], [104, 108, 100], [52, 56, 24], [37, 41, 55], [107, 80, 11], [18, 70, 100]], ![[0, 1], [82, 63, 31], [62, 82, 103], [34, 63, 81], [86, 76, 86], [14, 49, 25], [55, 38, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 43], []]
 b := ![[], [68, 15, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [91, 20, 36, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2660036, 778805, 115431]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24404, 7145, 1059]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-48, 29, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-48, 29, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![65, 29, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-48, 29, 1], ![154, -13, 58], ![4466, 1092, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -29, 113]], ![![-1, 0, 1], ![-32, -15, 58], ![47, 13, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [13, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 112], [0, 1]]
 g := ![![[46, 87], [28], [81], [60], [46, 91], [80, 1]], ![[0, 26], [28], [81], [60], [94, 22], [47, 112]]]
 h' := ![![[80, 112], [106, 58], [73, 64], [83, 9], [80, 88], [90, 59], [0, 1]], ![[0, 1], [0, 55], [108, 49], [12, 104], [1, 25], [64, 54], [80, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [4, 79]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [13, 33, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-943, -40, 22]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -6, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![55, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![55, 1, 0]] 
 ![![113, 0, 0], ![55, 1, 0], ![13, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![55, 1, 0], ![0, 55, 2], ![154, 35, 55]]]
  hmulB := by decide  
  f := ![![![1486, 27, 0], ![-3051, 0, 0]], ![![660, 12, 0], ![-1355, 0, 0]], ![![96, -26, -1], ![-197, 57, 0]]]
  g := ![![![1, 0, 0], ![-55, 113, 0], ![-13, 0, 113]], ![![0, 1, 0], ![-27, 55, 2], ![-22, 35, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-48, 29, 1]] ![![113, 0, 0], ![55, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![6215, 113, 0]], ![![-5424, 3277, 113], ![-2486, 1582, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![55, 1, 0]]], ![![![-48, 29, 1]], ![![-22, 14, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-18, 31, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-18, 31, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![109, 31, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-18, 31, 1], ![154, 17, 62], ![4774, 1162, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -31, 127]], ![![-1, 0, 1], ![-52, -15, 62], ![23, 5, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [63, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [44, 126], [0, 1]]
 g := ![![[88, 52], [122, 42], [123, 70], [2, 4], [87, 8], [44, 1]], ![[90, 75], [65, 85], [28, 57], [51, 123], [58, 119], [88, 126]]]
 h' := ![![[44, 126], [61, 59], [125, 114], [1, 109], [107, 125], [22, 95], [0, 1]], ![[0, 1], [117, 68], [61, 13], [98, 18], [19, 2], [11, 32], [44, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73]]
 b := ![[], [86, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [63, 83, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![679, 531, 308]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-259, -71, 308]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-62, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-62, 1, 0]] 
 ![![127, 0, 0], ![65, 1, 0], ![110, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-62, 1, 0], ![0, -62, 2], ![154, 35, -62]]]
  hmulB := by decide  
  f := ![![![6697, -108, 0], ![13716, 0, 0]], ![![3411, -55, 0], ![6986, 0, 0]], ![![5782, -62, -1], ![11842, 64, 0]]]
  g := ![![![1, 0, 0], ![-65, 127, 0], ![-110, 0, 127]], ![![-1, 1, 0], ![30, -62, 2], ![37, 35, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-18, 31, 1]] ![![127, 0, 0], ![-62, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-7874, 127, 0]], ![![-2286, 3937, 127], ![1270, -1905, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-62, 1, 0]]], ![![![-18, 31, 1]], ![![10, -15, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![55, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![55, 1, 0]] 
 ![![131, 0, 0], ![55, 1, 0], ![125, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![55, 1, 0], ![0, 55, 2], ![154, 35, 55]]]
  hmulB := by decide  
  f := ![![![2476, 45, 0], ![-5895, 0, 0]], ![![990, 18, 0], ![-2357, 0, 0]], ![![2350, 15, -1], ![-5595, 66, 0]]]
  g := ![![![1, 0, 0], ![-55, 131, 0], ![-125, 0, 131]], ![![0, 1, 0], ![-25, 55, 2], ![-66, 35, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-51, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-51, 1, 0]] 
 ![![131, 0, 0], ![80, 1, 0], ![75, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-51, 1, 0], ![0, -51, 2], ![154, 35, -51]]]
  hmulB := by decide  
  f := ![![![1531, -30, 0], ![3930, 0, 0]], ![![970, -19, 0], ![2490, 0, 0]], ![![903, 8, -1], ![2318, 66, 0]]]
  g := ![![![1, 0, 0], ![-80, 131, 0], ![-75, 0, 131]], ![![-1, 1, 0], ![30, -51, 2], ![9, 35, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-4, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-4, 1, 0]] 
 ![![131, 0, 0], ![127, 1, 0], ![123, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-4, 1, 0], ![0, -4, 2], ![154, 35, -4]]]
  hmulB := by decide  
  f := ![![![141, -35, 0], ![4585, 0, 0]], ![![137, -34, 0], ![4455, 0, 0]], ![![133, -31, -1], ![4325, 66, 0]]]
  g := ![![![1, 0, 0], ![-127, 131, 0], ![-123, 0, 131]], ![![-1, 1, 0], ![2, -4, 2], ![-29, 35, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![55, 1, 0]] ![![131, 0, 0], ![-51, 1, 0]]
  ![![131, 0, 0], ![-27, 2, 1]] where
 M := ![![![17161, 0, 0], ![-6681, 131, 0]], ![![7205, 131, 0], ![-2805, 4, 2]]]
 hmul := by decide  
 g := ![![![![131, 0, 0], ![0, 0, 0]], ![![-24, -1, -1], ![131, 0, 0]]], ![![![55, 1, 0], ![0, 0, 0]], ![![6, -2, -1], ![133, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-27, 2, 1]] ![![131, 0, 0], ![-4, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-524, 131, 0]], ![![-3537, 262, 131], ![262, 0, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-4, 1, 0]]], ![![![-27, 2, 1]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![4, -15, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![4, -15, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![4, 122, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![4, -15, 1], ![154, 39, -30], ![-2310, -448, 39]]]
  hmulB := by decide  
  f := ![![![-3, 15, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -122, 137]], ![![0, -1, 1], ![2, 27, -30], ![-18, -38, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [47, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 136], [0, 1]]
 g := ![![[107, 9], [135], [100], [69, 34], [93], [93], [1]], ![[56, 128], [135], [100], [59, 103], [93], [93], [1]]]
 h' := ![![[40, 136], [72, 3], [65, 86], [45, 127], [91, 87], [30, 97], [90, 40], [0, 1]], ![[0, 1], [55, 134], [80, 51], [56, 10], [9, 50], [74, 40], [46, 97], [40, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [14, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [47, 97, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5915, -2102, 542]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-59, -498, 542]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![30, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![30, 1, 0]] 
 ![![137, 0, 0], ![30, 1, 0], ![98, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![30, 1, 0], ![0, 30, 2], ![154, 35, 30]]]
  hmulB := by decide  
  f := ![![![841, 28, 0], ![-3836, 0, 0]], ![![150, 5, 0], ![-684, 0, 0]], ![![574, 4, -1], ![-2618, 69, 0]]]
  g := ![![![1, 0, 0], ![-30, 137, 0], ![-98, 0, 137]], ![![0, 1, 0], ![-8, 30, 2], ![-28, 35, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![4, -15, 1]] ![![137, 0, 0], ![30, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![4110, 137, 0]], ![![548, -2055, 137], ![274, -411, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![30, 1, 0]]], ![![![4, -15, 1]], ![![2, -3, 0]]]]
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


lemma PB155I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB155I2 : PrimesBelowBoundCertificateInterval O 79 137 155 where
  m := 11
  g := ![2, 3, 1, 2, 1, 2, 1, 2, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB155I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![6889, 83]
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N0, I89N1, I89N2, I101N1, I107N1, I113N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [I89N0, I89N1, I89N2], [], [I101N1], [], [I107N1], [], [I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
