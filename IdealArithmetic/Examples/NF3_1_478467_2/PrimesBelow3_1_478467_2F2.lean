
import IdealArithmetic.Examples.NF3_1_478467_2.RI3_1_478467_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [6, 21, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 69, 19], [25, 13, 64], [0, 1]]
 g := ![![[78, 24, 49], [70, 8, 23], [37, 78], [8, 28], [16, 55, 1], []], ![[34, 51, 71, 67], [24, 64, 43, 42], [25, 26], [47, 27], [26, 51, 78, 57], [67, 29]], ![[71, 11, 42, 48], [19, 41, 46, 44], [47, 9], [40, 61], [5, 58, 60, 11], [22, 29]]]
 h' := ![![[30, 69, 19], [78, 7, 76], [60, 79, 43], [38, 48, 24], [70, 81, 51], [0, 0, 1], [0, 1]], ![[25, 13, 64], [39, 0, 42], [23, 35, 68], [67, 71, 62], [10, 61, 44], [0, 69, 13], [30, 69, 19]], ![[0, 1], [39, 76, 48], [77, 52, 55], [39, 47, 80], [14, 24, 71], [78, 14, 69], [25, 13, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 78], []]
 b := ![[], [57, 20, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [6, 21, 28, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1337130, -401886, -30710]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16110, -4842, -370]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-163, 27, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-163, 27, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![15, 27, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-163, 27, 1], ![939, 17, 27], ![25353, 5799, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -27, 89]], ![![-2, 0, 1], ![6, -8, 27], ![282, 60, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [51, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 88], [0, 1]]
 g := ![![[87, 73], [85], [73], [71, 68], [70, 80], [1]], ![[57, 16], [85], [73], [65, 21], [42, 9], [1]]]
 h' := ![![[13, 88], [30, 42], [87, 21], [28, 47], [79, 54], [38, 13], [0, 1]], ![[0, 1], [42, 47], [4, 68], [16, 42], [69, 35], [29, 76], [13, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [81, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [51, 76, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11292, 6143, 1846]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-438, -491, 1846]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-27, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-27, 1, 0]] 
 ![![89, 0, 0], ![62, 1, 0], ![72, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-27, 1, 0], ![0, -27, 1], ![939, 180, -27]]]
  hmulB := by decide  
  f := ![![![1216, -45, 0], ![4005, 0, 0]], ![![892, -33, 0], ![2938, 0, 0]], ![![1008, -37, 0], ![3320, 1, 0]]]
  g := ![![![1, 0, 0], ![-62, 89, 0], ![-72, 0, 89]], ![![-1, 1, 0], ![18, -27, 1], ![-93, 180, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-163, 27, 1]] ![![89, 0, 0], ![-27, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-2403, 89, 0]], ![![-14507, 2403, 89], ![5340, -712, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-27, 1, 0]]], ![![![-163, 27, 1]], ![![60, -8, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-153, 30, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-153, 30, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![41, 30, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-153, 30, 1], ![939, 27, 30], ![28170, 6339, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -30, 97]], ![![-2, 0, 1], ![-3, -9, 30], ![279, 57, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [16, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 96], [0, 1]]
 g := ![![[61, 91], [85], [31], [31], [12], [91, 1]], ![[0, 6], [85], [31], [31], [12], [85, 96]]]
 h' := ![![[91, 96], [47, 24], [90, 45], [95, 15], [3, 82], [96, 20], [0, 1]], ![[0, 1], [0, 73], [14, 52], [5, 82], [93, 15], [73, 77], [91, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [21, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [16, 6, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1850, 457, 303]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-109, -89, 303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-30, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-30, 1, 0]] 
 ![![97, 0, 0], ![67, 1, 0], ![70, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-30, 1, 0], ![0, -30, 1], ![939, 180, -30]]]
  hmulB := by decide  
  f := ![![![2071, -69, 0], ![6693, 0, 0]], ![![1441, -48, 0], ![4657, 0, 0]], ![![1510, -50, 0], ![4880, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 97, 0], ![-70, 0, 97]], ![![-1, 1, 0], ![20, -30, 1], ![-93, 180, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-153, 30, 1]] ![![97, 0, 0], ![-30, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2910, 97, 0]], ![![-14841, 2910, 97], ![5529, -873, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-30, 1, 0]]], ![![![-153, 30, 1]], ![![57, -9, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [15, 67, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 33, 44], [34, 67, 57], [0, 1]]
 g := ![![[0, 93, 14], [95, 6], [89, 40, 20], [12, 54], [4, 45], [1]], ![[92, 0, 37, 10], [28, 96], [35, 3, 4, 7], [28, 80], [21, 56], [17, 88, 47, 41]], ![[25, 41], [5, 49], [91, 24, 4, 42], [72, 36], [57, 92], [77, 57, 3, 60]]]
 h' := ![![[0, 33, 44], [69, 77, 69], [79, 26, 62], [78, 26, 11], [64, 57, 85], [86, 34, 34], [0, 1]], ![[34, 67, 57], [81, 89, 32], [81, 79, 46], [36, 47, 63], [70, 49, 22], [48, 66, 37], [0, 33, 44]], ![[0, 1], [69, 36], [89, 97, 94], [25, 28, 27], [87, 96, 95], [72, 1, 30], [34, 67, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 95], []]
 b := ![[], [82, 80, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [15, 67, 67, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19636218, -7744377, -738209]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-194418, -76677, -7309]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-150, 37, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-150, 37, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![56, 37, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-150, 37, 1], ![939, 30, 37], ![34743, 7599, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -37, 103]], ![![-2, 0, 1], ![-11, -13, 37], ![321, 63, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [90, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 102], [0, 1]]
 g := ![![[25, 91], [39, 100], [76, 91], [1], [55], [16, 1]], ![[39, 12], [94, 3], [90, 12], [1], [55], [32, 102]]]
 h' := ![![[16, 102], [95, 83], [61, 10], [17, 20], [101, 102], [2, 63], [0, 1]], ![[0, 1], [84, 20], [15, 93], [28, 83], [85, 1], [83, 40], [16, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [87, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [90, 87, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1968, 1212, 94]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -22, 94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-37, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-37, 1, 0]] 
 ![![103, 0, 0], ![66, 1, 0], ![73, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-37, 1, 0], ![0, -37, 1], ![939, 180, -37]]]
  hmulB := by decide  
  f := ![![![2036, -55, 0], ![5665, 0, 0]], ![![1296, -35, 0], ![3606, 0, 0]], ![![1494, -40, 0], ![4157, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 103, 0], ![-73, 0, 103]], ![![-1, 1, 0], ![23, -37, 1], ![-80, 180, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-150, 37, 1]] ![![103, 0, 0], ![-37, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3811, 103, 0]], ![![-15450, 3811, 103], ![6489, -1339, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-37, 1, 0]]], ![![![-150, 37, 1]], ![![63, -13, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![18, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![18, 1, 0]] 
 ![![107, 0, 0], ![18, 1, 0], ![104, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![18, 1, 0], ![0, 18, 1], ![939, 180, 18]]]
  hmulB := by decide  
  f := ![![![73, 4, 0], ![-428, 0, 0]], ![![-18, -1, 0], ![108, 0, 0]], ![![76, 4, 0], ![-446, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 107, 0], ![-104, 0, 107]], ![![0, 1, 0], ![-4, 18, 1], ![-39, 180, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![21, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![21, 1, 0]] 
 ![![107, 0, 0], ![21, 1, 0], ![94, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![21, 1, 0], ![0, 21, 1], ![939, 180, 21]]]
  hmulB := by decide  
  f := ![![![862, 41, 0], ![-4387, 0, 0]], ![![168, 8, 0], ![-855, 0, 0]], ![![740, 35, 0], ![-3766, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 107, 0], ![-94, 0, 107]], ![![0, 1, 0], ![-5, 21, 1], ![-45, 180, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-39, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-39, 1, 0]] 
 ![![107, 0, 0], ![68, 1, 0], ![84, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-39, 1, 0], ![0, -39, 1], ![939, 180, -39]]]
  hmulB := by decide  
  f := ![![![742, -19, 0], ![2033, 0, 0]], ![![508, -13, 0], ![1392, 0, 0]], ![![600, -15, 0], ![1644, 1, 0]]]
  g := ![![![1, 0, 0], ![-68, 107, 0], ![-84, 0, 107]], ![![-1, 1, 0], ![24, -39, 1], ![-75, 180, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![18, 1, 0]] ![![107, 0, 0], ![21, 1, 0]]
  ![![107, 0, 0], ![-157, 39, 1]] where
 M := ![![![11449, 0, 0], ![2247, 107, 0]], ![![1926, 107, 0], ![378, 39, 1]]]
 hmul := by decide  
 g := ![![![![107, 0, 0], ![0, 0, 0]], ![![21, 1, 0], ![0, 0, 0]]], ![![![18, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-157, 39, 1]] ![![107, 0, 0], ![-39, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-4173, 107, 0]], ![![-16799, 4173, 107], ![7062, -1498, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-39, 1, 0]]], ![![![-157, 39, 1]], ![![66, -14, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [61, 76, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 57, 40], [11, 51, 69], [0, 1]]
 g := ![![[80, 82, 80], [11, 7], [49, 102, 45], [8, 44, 60], [91, 97], [1]], ![[19, 62, 9, 8], [36, 83], [88, 87, 28, 54], [48, 87, 98, 85], [81, 25], [106, 41, 77, 17]], ![[40, 62, 80, 69], [5, 102], [8, 25, 67, 17], [19, 75, 95, 96], [60, 89], [44, 2, 28, 92]]]
 h' := ![![[25, 57, 40], [28, 101, 25], [63, 61, 15], [57, 71, 63], [23, 36, 13], [48, 33, 36], [0, 1]], ![[11, 51, 69], [5, 25, 83], [81, 16, 44], [37, 62, 58], [82, 48, 32], [3, 71, 104], [25, 57, 40]], ![[0, 1], [23, 92, 1], [108, 32, 50], [40, 85, 97], [0, 25, 64], [64, 5, 78], [11, 51, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 43], []]
 b := ![[], [56, 52, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [61, 76, 73, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19668505, 5031876, 322204]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![180445, 46164, 2956]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [12, 65, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 19, 57], [57, 93, 56], [0, 1]]
 g := ![![[35, 108, 88], [103, 28], [17, 57], [], [65, 31, 11], [1]], ![[57, 12, 82, 57], [14, 109], [63, 1], [49, 77], [72, 96, 102, 109], [8, 19, 96, 99]], ![[79, 37, 16, 87], [97, 26], [11, 109], [18, 77], [95, 66, 9, 60], [39, 92, 101, 14]]]
 h' := ![![[32, 19, 57], [58, 53, 38], [86, 99, 49], [8, 5, 82], [11, 67], [101, 48, 89], [0, 1]], ![[57, 93, 56], [47, 75, 1], [21, 25, 30], [41, 100, 1], [8, 30, 90], [15, 103, 52], [32, 19, 57]], ![[0, 1], [38, 98, 74], [80, 102, 34], [41, 8, 30], [101, 16, 23], [83, 75, 85], [57, 93, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 91], []]
 b := ![[], [88, 73, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [12, 65, 24, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![546468, -69834, -24860]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4836, -618, -220]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [75, 88, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 47, 9], [14, 79, 118], [0, 1]]
 g := ![![[38, 118, 15], [100, 71, 124], [70, 82, 17], [48, 37, 60], [29, 106, 113], [1]], ![[108, 97, 110, 36], [98, 97, 115, 26], [74, 18, 78, 49], [16, 107, 7, 31], [77, 89, 104, 121], [49, 122, 107, 94]], ![[42, 86, 67, 80], [83, 82, 91, 86], [80, 64, 0, 48], [113, 52, 87, 108], [35, 26, 86, 27], [73, 107, 31, 33]]]
 h' := ![![[71, 47, 9], [120, 43, 53], [84, 40, 39], [83, 115, 115], [111, 76, 21], [52, 39, 85], [0, 1]], ![[14, 79, 118], [63, 61, 2], [70, 16, 12], [31, 117, 87], [43, 126, 57], [33, 89, 81], [71, 47, 9]], ![[0, 1], [112, 23, 72], [25, 71, 76], [125, 22, 52], [109, 52, 49], [63, 126, 88], [14, 79, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 123], []]
 b := ![[], [113, 56, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [75, 88, 42, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9240774, 3287014, 302006]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![72762, 25882, 2378]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-73, 32, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-73, 32, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![58, 32, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-73, 32, 1], ![939, 107, 32], ![30048, 6699, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -32, 131]], ![![-1, 0, 1], ![-7, -7, 32], ![182, 25, 107]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [130, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 130], [0, 1]]
 g := ![![[44, 46], [84, 77], [38], [49], [81], [102], [1]], ![[103, 85], [66, 54], [38], [49], [81], [102], [1]]]
 h' := ![![[44, 130], [84, 35], [42, 48], [2, 118], [79, 7], [103, 122], [1, 44], [0, 1]], ![[0, 1], [52, 96], [58, 83], [85, 13], [125, 124], [100, 9], [103, 87], [44, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [124, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [130, 87, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37252, -4354, 1002]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-728, -278, 1002]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-32, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-32, 1, 0]] 
 ![![131, 0, 0], ![99, 1, 0], ![24, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-32, 1, 0], ![0, -32, 1], ![939, 180, -32]]]
  hmulB := by decide  
  f := ![![![3201, -100, 0], ![13100, 0, 0]], ![![2465, -77, 0], ![10088, 0, 0]], ![![648, -20, 0], ![2652, 1, 0]]]
  g := ![![![1, 0, 0], ![-99, 131, 0], ![-24, 0, 131]], ![![-1, 1, 0], ![24, -32, 1], ![-123, 180, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-73, 32, 1]] ![![131, 0, 0], ![-32, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-4192, 131, 0]], ![![-9563, 4192, 131], ![3275, -917, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-32, 1, 0]]], ![![![-73, 32, 1]], ![![25, -7, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [56, 105, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 21, 52], [134, 115, 85], [0, 1]]
 g := ![![[76, 42, 119], [13, 36], [96, 17], [23, 51, 126], [36, 14], [125, 1], []], ![[49, 105, 133, 23], [98, 22], [32, 30], [59, 34, 100, 127], [14, 136], [127, 73], [13, 101]], ![[90, 83, 30, 45], [78, 105], [35, 103], [17, 40, 74, 35], [121, 4], [93, 30], [117, 101]]]
 h' := ![![[128, 21, 52], [30, 123, 16], [115, 20, 131], [82, 44, 47], [71, 26, 117], [124, 108, 39], [0, 0, 1], [0, 1]], ![[134, 115, 85], [79, 101, 16], [118, 15, 76], [102, 55, 21], [36, 18, 11], [86, 37, 100], [38, 136, 115], [128, 21, 52]], ![[0, 1], [52, 50, 105], [131, 102, 67], [131, 38, 69], [18, 93, 9], [128, 129, 135], [33, 1, 21], [134, 115, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 75], []]
 b := ![[], [81, 11, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [56, 105, 12, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![283590, 272082, 40278]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2070, 1986, 294]
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



lemma PB196I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB196I2 : PrimesBelowBoundCertificateInterval O 79 137 196 where
  m := 11
  g := ![1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB196I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0]
    · exact ![I127N0]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![1442897]
    · exact ![2048383]
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
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I89N1, I97N1, I103N1, I107N0, I107N1, I107N2, I131N1]
  Il := ![[], [I89N1], [I97N1], [], [I103N1], [I107N0, I107N1, I107N2], [], [], [], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
