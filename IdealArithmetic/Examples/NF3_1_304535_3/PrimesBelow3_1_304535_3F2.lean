
import IdealArithmetic.Examples.NF3_1_304535_3.RI3_1_304535_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -1, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2, -1, 1]] 
 ![![83, 0, 0], ![11, 1, 0], ![9, 0, 1]] where
  M :=![![![-2, -1, 1], ![105, -9, -5], ![-105, 28, -9]]]
  hmulB := by decide  
  f := ![![![221, 19, 14]], ![![47, 4, 3]], ![![48, 4, 3]]]
  g := ![![![0, -1, 1], ![3, -9, -5], ![-4, 28, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![24, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![24, 1, 0]] 
 ![![83, 0, 0], ![24, 1, 0], ![1, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![24, 1, 0], ![0, 24, 5], ![105, -7, 24]]]
  hmulB := by decide  
  f := ![![![745, 31, 0], ![-2573, 0, 0]], ![![216, 9, 0], ![-746, 0, 0]], ![![-13, -15, -3], ![45, 50, 0]]]
  g := ![![![1, 0, 0], ![-24, 83, 0], ![-1, 0, 83]], ![![0, 1, 0], ![-7, 24, 5], ![3, -7, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-35, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-35, 1, 0]] 
 ![![83, 0, 0], ![48, 1, 0], ![4, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-35, 1, 0], ![0, -35, 5], ![105, -7, -35]]]
  hmulB := by decide  
  f := ![![![1086, -31, 0], ![2573, 0, 0]], ![![666, -19, 0], ![1578, 0, 0]], ![![108, 18, -3], ![256, 50, 0]]]
  g := ![![![1, 0, 0], ![-48, 83, 0], ![-4, 0, 83]], ![![-1, 1, 0], ![20, -35, 5], ![7, -7, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2, -1, 1]] ![![83, 0, 0], ![24, 1, 0]]
  ![![83, 0, 0], ![3, 7, 1]] where
 M := ![![![-166, -83, 83], ![57, -33, 19]]]
 hmul := by decide  
 g := ![![![![-2, -1, 1], ![0, 0, 0]], ![![0, -2, 0], ![19, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![2, -34, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![2, -34, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![2, 55, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![2, -34, 1], ![105, -5, -170], ![-3570, 259, -5]]]
  hmulB := by decide  
  f := ![![![-1, 34, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -55, 89]], ![![0, -1, 1], ![5, 105, -170], ![-40, 6, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [87, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 88], [0, 1]]
 g := ![![[53, 44], [42], [53], [11, 9], [86, 22], [1]], ![[0, 45], [42], [53], [75, 80], [15, 67], [1]]]
 h' := ![![[17, 88], [16, 20], [56, 24], [22, 63], [83, 86], [2, 17], [0, 1]], ![[0, 1], [0, 69], [19, 65], [25, 26], [32, 3], [24, 72], [17, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [51, 83]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [87, 72, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297, -65, -74]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 45, -74]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-8, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-8, 1, 0]] 
 ![![89, 0, 0], ![81, 1, 0], ![5, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-8, 1, 0], ![0, -8, 5], ![105, -7, -8]]]
  hmulB := by decide  
  f := ![![![641, -80, 0], ![7120, 0, 0]], ![![585, -73, 0], ![6498, 0, 0]], ![![45, -4, -1], ![500, 18, 0]]]
  g := ![![![1, 0, 0], ![-81, 89, 0], ![-5, 0, 89]], ![![-1, 1, 0], ![7, -8, 5], ![8, -7, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![2, -34, 1]] ![![89, 0, 0], ![-8, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-712, 89, 0]], ![![178, -3026, 89], ![89, 267, -178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-8, 1, 0]]], ![![![2, -34, 1]], ![![1, 3, -2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![28, 25, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![28, 25, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![28, 25, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![28, 25, 1], ![105, 21, 125], ![2625, -154, 21]]]
  hmulB := by decide  
  f := ![![![-27, -25, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -25, 97]], ![![0, 0, 1], ![-35, -32, 125], ![21, -7, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [51, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 96], [0, 1]]
 g := ![![[1, 64], [95], [91], [66], [8], [46, 1]], ![[35, 33], [95], [91], [66], [8], [92, 96]]]
 h' := ![![[46, 96], [93, 89], [31, 17], [4, 73], [13, 39], [79, 28], [0, 1]], ![[0, 1], [16, 8], [37, 80], [64, 24], [61, 58], [9, 69], [46, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14]]
 b := ![[], [33, 7]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [51, 51, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1259, 175, 104]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43, -25, 104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-28, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-28, 1, 0]] 
 ![![97, 0, 0], ![69, 1, 0], ![76, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-28, 1, 0], ![0, -28, 5], ![105, -7, -28]]]
  hmulB := by decide  
  f := ![![![1849, -66, 0], ![6402, 0, 0]], ![![1317, -47, 0], ![4560, 0, 0]], ![![1436, -40, -2], ![4972, 39, 0]]]
  g := ![![![1, 0, 0], ![-69, 97, 0], ![-76, 0, 97]], ![![-1, 1, 0], ![16, -28, 5], ![28, -7, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![28, 25, 1]] ![![97, 0, 0], ![-28, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2716, 97, 0]], ![![2716, 2425, 97], ![-679, -679, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-28, 1, 0]]], ![![![28, 25, 1]], ![![-7, -7, 1]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [92, 88, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 43, 49], [59, 57, 52], [0, 1]]
 g := ![![[41, 91, 64], [41, 1], [65, 100, 68], [38, 77], [5, 71], [1]], ![[1, 87, 18, 45], [11, 58], [62, 14, 24, 33], [76, 68], [100, 23], [20, 70, 83, 85]], ![[42, 36, 14, 81], [98, 97], [83, 31, 66, 95], [32, 23], [5, 81], [29, 69, 87, 16]]]
 h' := ![![[66, 43, 49], [2, 84, 93], [80, 59, 1], [58, 11, 13], [25, 29, 28], [9, 13, 24], [0, 1]], ![[59, 57, 52], [35, 81, 24], [80, 62, 19], [56, 12, 68], [68, 21, 88], [28, 42, 86], [66, 43, 49]], ![[0, 1], [98, 37, 85], [78, 81, 81], [70, 78, 20], [61, 51, 86], [4, 46, 92], [59, 57, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80, 90], []]
 b := ![[], [40, 24, 60], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [92, 88, 77, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![67973, -1414, -1919]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![673, -14, -19]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [49, 66, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 36, 76], [13, 66, 27], [0, 1]]
 g := ![![[54, 7, 15], [74, 95, 29], [88, 64, 59], [62, 60], [4, 68], [1]], ![[46, 56, 0, 36], [57, 43, 84, 18], [48, 49, 92, 52], [10, 64], [1, 93], [48, 57, 2, 93]], ![[64, 20, 55, 51], [69, 92, 48, 89], [55, 38, 91, 74], [59, 63], [76, 82], [5, 88, 77, 10]]]
 h' := ![![[32, 36, 76], [82, 30, 85], [14, 19, 82], [65, 97, 70], [42, 91, 67], [54, 37, 45], [0, 1]], ![[13, 66, 27], [21, 54, 62], [66, 2, 58], [44, 66, 44], [88, 91, 8], [31, 86, 14], [32, 36, 76]], ![[0, 1], [70, 19, 59], [101, 82, 66], [74, 43, 92], [9, 24, 28], [98, 83, 44], [13, 66, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 70], []]
 b := ![[], [7, 34, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [49, 66, 58, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-117111, 22557, -2266]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1137, 219, -22]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![53, -42, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![53, -42, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![53, 65, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![53, -42, 1], ![105, 46, -210], ![-4410, 315, 46]]]
  hmulB := by decide  
  f := ![![![-52, 42, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -65, 107]], ![![0, -1, 1], ![105, 128, -210], ![-64, -25, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [80, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 106], [0, 1]]
 g := ![![[42, 41], [88, 34], [69], [75, 102], [39], [64, 1]], ![[98, 66], [17, 73], [69], [76, 5], [39], [21, 106]]]
 h' := ![![[64, 106], [22, 24], [1, 26], [99, 47], [25, 40], [16, 57], [0, 1]], ![[0, 1], [60, 83], [60, 81], [4, 60], [17, 67], [26, 50], [64, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [78, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [80, 43, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![290, -36, -45]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 27, -45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-4, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-4, 1, 0]] 
 ![![107, 0, 0], ![103, 1, 0], ![61, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-4, 1, 0], ![0, -4, 5], ![105, -7, -4]]]
  hmulB := by decide  
  f := ![![![117, -29, 0], ![3103, 0, 0]], ![![113, -28, 0], ![2997, 0, 0]], ![![67, -15, -2], ![1777, 43, 0]]]
  g := ![![![1, 0, 0], ![-103, 107, 0], ![-61, 0, 107]], ![![-1, 1, 0], ![1, -4, 5], ![10, -7, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![53, -42, 1]] ![![107, 0, 0], ![-4, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-428, 107, 0]], ![![5671, -4494, 107], ![-107, 214, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-4, 1, 0]]], ![![![53, -42, 1]], ![![-1, 2, -2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-22, 4, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-22, 4, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![87, 4, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-22, 4, 1], ![105, -29, 20], ![420, -7, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -4, 109]], ![![-1, 0, 1], ![-15, -1, 20], ![27, 1, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [53, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 108], [0, 1]]
 g := ![![[85, 35], [84], [57, 80], [96, 1], [83], [73, 1]], ![[24, 74], [84], [11, 29], [60, 108], [83], [37, 108]]]
 h' := ![![[73, 108], [106, 12], [31, 56], [35, 84], [43, 108], [55, 44], [0, 1]], ![[0, 1], [1, 97], [86, 53], [63, 25], [79, 1], [106, 65], [73, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [6, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [53, 36, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4080, 477, 1836]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1428, -63, 1836]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-20, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-20, 1, 0]] 
 ![![109, 0, 0], ![89, 1, 0], ![29, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-20, 1, 0], ![0, -20, 5], ![105, -7, -20]]]
  hmulB := by decide  
  f := ![![![1401, -70, 0], ![7630, 0, 0]], ![![1141, -57, 0], ![6214, 0, 0]], ![![401, -16, -1], ![2184, 22, 0]]]
  g := ![![![1, 0, 0], ![-89, 109, 0], ![-29, 0, 109]], ![![-1, 1, 0], ![15, -20, 5], ![12, -7, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-22, 4, 1]] ![![109, 0, 0], ![-20, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2180, 109, 0]], ![![-2398, 436, 109], ![545, -109, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-20, 1, 0]]], ![![![-22, 4, 1]], ![![5, -1, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![34, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![34, 1, 0]] 
 ![![113, 0, 0], ![34, 1, 0], ![40, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![34, 1, 0], ![0, 34, 5], ![105, -7, 34]]]
  hmulB := by decide  
  f := ![![![273, 8, 0], ![-904, 0, 0]], ![![34, 1, 0], ![-112, 0, 0]], ![![84, -18, -3], ![-278, 68, 0]]]
  g := ![![![1, 0, 0], ![-34, 113, 0], ![-40, 0, 113]], ![![0, 1, 0], ![-12, 34, 5], ![-9, -7, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![45, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![45, 1, 0]] 
 ![![113, 0, 0], ![45, 1, 0], ![47, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![45, 1, 0], ![0, 45, 5], ![105, -7, 45]]]
  hmulB := by decide  
  f := ![![![1621, 36, 0], ![-4068, 0, 0]], ![![585, 13, 0], ![-1468, 0, 0]], ![![679, -12, -3], ![-1704, 68, 0]]]
  g := ![![![1, 0, 0], ![-45, 113, 0], ![-47, 0, 113]], ![![0, 1, 0], ![-20, 45, 5], ![-15, -7, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![34, 1, 0]] ![![113, 0, 0], ![34, 1, 0]]
  ![![113, 0, 0], ![-40, -9, 1]] where
 M := ![![![12769, 0, 0], ![3842, 113, 0]], ![![3842, 113, 0], ![1156, 68, 5]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![34, 1, 0], ![0, 0, 0]]], ![![![34, 1, 0], ![0, 0, 0]], ![![12, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-40, -9, 1]] ![![113, 0, 0], ![45, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![5085, 113, 0]], ![![-4520, -1017, 113], ![-1695, -452, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![45, 1, 0]]], ![![![-40, -9, 1]], ![![-15, -4, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![30, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![30, 1, 0]] 
 ![![127, 0, 0], ![30, 1, 0], ![74, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![30, 1, 0], ![0, 30, 5], ![105, -7, 30]]]
  hmulB := by decide  
  f := ![![![1561, 52, 0], ![-6604, 0, 0]], ![![330, 11, 0], ![-1396, 0, 0]], ![![902, 18, -2], ![-3816, 51, 0]]]
  g := ![![![1, 0, 0], ![-30, 127, 0], ![-74, 0, 127]], ![![0, 1, 0], ![-10, 30, 5], ![-15, -7, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![142, 12, 9]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![142, 12, 9]] 
 ![![127, 0, 0], ![44, 1, 0], ![70, 0, 1]] where
  M :=![![![142, 12, 9], ![945, 79, 60], ![1260, 105, 79]]]
  hmulB := by decide  
  f := ![![![-59, -3, 9]], ![![-13, -2, 3]], ![![-35, 0, 4]]]
  g := ![![![-8, 12, 9], ![-53, 79, 60], ![-70, 105, 79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![53, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![53, 1, 0]] 
 ![![127, 0, 0], ![53, 1, 0], ![124, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![53, 1, 0], ![0, 53, 5], ![105, -7, 53]]]
  hmulB := by decide  
  f := ![![![531, 10, 0], ![-1270, 0, 0]], ![![159, 3, 0], ![-380, 0, 0]], ![![546, -11, -2], ![-1306, 51, 0]]]
  g := ![![![1, 0, 0], ![-53, 127, 0], ![-124, 0, 127]], ![![0, 1, 0], ![-27, 53, 5], ![-48, -7, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![30, 1, 0]] ![![142, 12, 9]]
  ![![127, 0, 0], ![10, -36, 1]] where
 M := ![![![18034, 1524, 1143]], ![![5205, 439, 330]]]
 hmul := by decide  
 g := ![![![![132, 48, 8], ![127, 0, 0]]], ![![![35, 25, 2], ![76, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![10, -36, 1]] ![![127, 0, 0], ![53, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![6731, 127, 0]], ![![1270, -4572, 127], ![635, -1905, -127]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![53, 1, 0]]], ![![![10, -36, 1]], ![![5, -15, -1]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![35, 53, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![35, 53, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![35, 53, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![35, 53, 1], ![105, 28, 265], ![5565, -350, 28]]]
  hmulB := by decide  
  f := ![![![-34, -53, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -53, 131]], ![![0, 0, 1], ![-70, -107, 265], ![35, -14, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [70, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 130], [0, 1]]
 g := ![![[95, 53], [20, 7], [91], [49], [59], [44], [1]], ![[35, 78], [106, 124], [91], [49], [59], [44], [1]]]
 h' := ![![[31, 130], [41, 61], [113, 111], [123, 22], [127, 7], [117, 37], [61, 31], [0, 1]], ![[0, 1], [98, 70], [17, 20], [19, 109], [82, 124], [85, 94], [105, 100], [31, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [107, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [70, 100, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-659, 357, -60]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 27, -60]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-3, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-3, 1, 0]] 
 ![![131, 0, 0], ![128, 1, 0], ![103, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-3, 1, 0], ![0, -3, 5], ![105, -7, -3]]]
  hmulB := by decide  
  f := ![![![139, -46, 0], ![6026, 0, 0]], ![![136, -45, 0], ![5896, 0, 0]], ![![113, -35, -4], ![4900, 105, 0]]]
  g := ![![![1, 0, 0], ![-128, 131, 0], ![-103, 0, 131]], ![![-1, 1, 0], ![-1, -3, 5], ![10, -7, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![35, 53, 1]] ![![131, 0, 0], ![-3, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-393, 131, 0]], ![![4585, 6943, 131], ![0, -131, 262]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-3, 1, 0]]], ![![![35, 53, 1]], ![![0, -1, 2]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![18, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![18, 1, 0]] 
 ![![137, 0, 0], ![18, 1, 0], ![127, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![18, 1, 0], ![0, 18, 5], ![105, -7, 18]]]
  hmulB := by decide  
  f := ![![![1423, 79, 0], ![-10823, 0, 0]], ![![162, 9, 0], ![-1232, 0, 0]], ![![1337, 67, -2], ![-10169, 55, 0]]]
  g := ![![![1, 0, 0], ![-18, 137, 0], ![-127, 0, 137]], ![![0, 1, 0], ![-7, 18, 5], ![-15, -7, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![54, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![54, 1, 0]] 
 ![![137, 0, 0], ![54, 1, 0], ![47, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![54, 1, 0], ![0, 54, 5], ![105, -7, 54]]]
  hmulB := by decide  
  f := ![![![1459, 27, 0], ![-3699, 0, 0]], ![![486, 9, 0], ![-1232, 0, 0]], ![![469, -13, -2], ![-1189, 55, 0]]]
  g := ![![![1, 0, 0], ![-54, 137, 0], ![-47, 0, 137]], ![![0, 1, 0], ![-23, 54, 5], ![-15, -7, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![65, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![65, 1, 0]] 
 ![![137, 0, 0], ![65, 1, 0], ![114, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![65, 1, 0], ![0, 65, 5], ![105, -7, 65]]]
  hmulB := by decide  
  f := ![![![2731, 42, 0], ![-5754, 0, 0]], ![![1235, 19, 0], ![-2602, 0, 0]], ![![2282, 9, -2], ![-4808, 55, 0]]]
  g := ![![![1, 0, 0], ![-65, 137, 0], ![-114, 0, 137]], ![![0, 1, 0], ![-35, 65, 5], ![-50, -7, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![18, 1, 0]] ![![137, 0, 0], ![54, 1, 0]]
  ![![137, 0, 0], ![30, -13, 1]] where
 M := ![![![18769, 0, 0], ![7398, 137, 0]], ![![2466, 137, 0], ![972, 72, 5]]]
 hmul := by decide  
 g := ![![![![107, 13, -1], ![137, 0, 0]], ![![24, 14, -1], ![137, 0, 0]]], ![![![-12, 14, -1], ![137, 0, 0]], ![![6, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![30, -13, 1]] ![![137, 0, 0], ![65, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8905, 137, 0]], ![![4110, -1781, 137], ![2055, -822, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![65, 1, 0]]], ![![![30, -13, 1]], ![![15, -6, 0]]]]
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


lemma PB157I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB157I2 : PrimesBelowBoundCertificateInterval O 79 137 157 where
  m := 11
  g := ![3, 2, 2, 1, 1, 2, 2, 3, 3, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB157I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![113, 113, 113]
    · exact ![127, 127, 127]
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
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I107N1, I109N1, I113N0, I113N1, I127N0, I127N1, I127N2, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [], [], [I107N1], [I109N1], [I113N0, I113N0, I113N1], [I127N0, I127N1, I127N2], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
