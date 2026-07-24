
import IdealArithmetic.Examples.NF3_1_378695_1.RI3_1_378695_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-19289, 7252, -819]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-19289, 7252, -819]] 
 ![![83, 0, 0], ![0, 83, 0], ![80, 33, 1]] where
  M :=![![![-19289, 7252, -819], ![151515, -56963, 6433], ![-1190105, 447433, -50530]]]
  hmulB := by decide  
  f := ![![![-47, 49, 7]], ![![-1295, 275, 56]], ![![-685, 172, 33]]]
  g := ![![![557, 413, -819], ![-4375, -3244, 6433], ![34365, 25481, -50530]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [22, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 82], [0, 1]]
 g := ![![[3, 27], [20, 68], [75], [44], [15, 40], [1]], ![[47, 56], [14, 15], [75], [44], [31, 43], [1]]]
 h' := ![![[17, 82], [58, 39], [38, 20], [32, 18], [2, 25], [61, 17], [0, 1]], ![[0, 1], [57, 44], [46, 63], [6, 65], [12, 58], [18, 66], [17, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [74, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [22, 66, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-533, -113, -16]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, 5, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, -49, -7]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![47, -49, -7]] 
 ![![83, 0, 0], ![49, 1, 0], ![6, 0, 1]] where
  M :=![![![47, -49, -7], ![1295, -275, -56], ![10360, -1281, -331]]]
  hmulB := by decide  
  f := ![![![19289, -7252, 819]], ![![9562, -3595, 406]], ![![15733, -5915, 668]]]
  g := ![![![30, -49, -7], ![182, -275, -56], ![905, -1281, -331]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-19289, 7252, -819]] ![![47, -49, -7]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107211, -40307, 4552]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![107211, -40307, 4552]] 
 ![![89, 0, 0], ![47, 1, 0], ![16, 0, 1]] where
  M :=![![![107211, -40307, 4552], ![-842120, 316603, -35755], ![6614675, -2486850, 280848]]]
  hmulB := by decide  
  f := ![![![-2406, -864, -71]], ![![-1123, -520, -48]], ![![1511, -491, -87]]]
  g := ![![![21672, -40307, 4552], ![-170229, 316603, -35755], ![1337113, -2486850, 280848]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-6, 1, 0]] 
 ![![89, 0, 0], ![83, 1, 0], ![53, 0, 1]] where
  M :=![![![-6, 1, 0], ![0, -6, 1], ![-185, 46, -5]]]
  hmulB := by decide  
  f := ![![![16, -5, -1]], ![![17, -5, -1]], ![![22, -4, -1]]]
  g := ![![![-1, 1, 0], ![5, -6, 1], ![-42, 46, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![107211, -40307, 4552]] ![![107211, -40307, 4552]]
  ![![75547529961, -28402812098, 3207621353]] where
 M := ![![![75547529961, -28402812098, 3207621353]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI89N1 : IdealMulLeCertificate' Table 
  ![![75547529961, -28402812098, 3207621353]] ![![-6, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![-1046695130071, 393514984787, -44440918863]]]
 hmul := by decide  
 g := ![![![![-11760619439, 4421516683, -499336167]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-44, 1, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-44, 1, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![53, 1, 1]] where
  M :=![![![-44, 1, 1], ![-185, 2, 2], ![-370, -93, 4]]]
  hmulB := by decide  
  f := ![![![2, -1, 0]], ![![0, 2, -1]], ![![3, -1, 0]]]
  g := ![![![-1, 0, 1], ![-3, 0, 2], ![-6, -1, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [32, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [73, 96], [0, 1]]
 g := ![![[25, 94], [64], [95], [1], [86], [73, 1]], ![[0, 3], [64], [95], [1], [86], [49, 96]]]
 h' := ![![[73, 96], [55, 71], [58, 8], [73, 17], [28, 96], [89, 59], [0, 1]], ![[0, 1], [0, 26], [60, 89], [53, 80], [52, 1], [31, 38], [73, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [19, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [32, 24, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![564, -1847, 481]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-257, -24, 481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![97, 0, 0], ![95, 1, 0], ![93, 0, 1]] where
  M :=![![![-2, 1, 0], ![0, -2, 1], ![-185, 46, -1]]]
  hmulB := by decide  
  f := ![![![44, -1, -1]], ![![45, -1, -1]], ![![46, 0, -1]]]
  g := ![![![-1, 1, 0], ![1, -2, 1], ![-46, 46, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-44, 1, 1]] ![![-2, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-70, -20, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-70, -20, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![31, 81, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-70, -20, 1], ![-185, -24, -19], ![3515, -1059, -43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-31, -81, 101]], ![![-1, -1, 1], ![4, 15, -19], ![48, 24, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [75, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 100], [0, 1]]
 g := ![![[45, 58], [14], [61, 17], [5], [77], [59, 1]], ![[33, 43], [14], [54, 84], [5], [77], [17, 100]]]
 h' := ![![[59, 100], [52, 19], [71, 69], [13, 57], [40, 45], [19, 73], [0, 1]], ![[0, 1], [62, 82], [1, 32], [43, 44], [69, 56], [84, 28], [59, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [84, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [75, 42, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1668, -317, 132]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -109, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![19, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![19, 1, 0]] 
 ![![101, 0, 0], ![19, 1, 0], ![43, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![19, 1, 0], ![0, 19, 1], ![-185, 46, 20]]]
  hmulB := by decide  
  f := ![![![267, 14, 0], ![-1414, 0, 0]], ![![19, 1, 0], ![-100, 0, 0]], ![![99, 5, 0], ![-524, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 101, 0], ![-43, 0, 101]], ![![0, 1, 0], ![-4, 19, 1], ![-19, 46, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-70, -20, 1]] ![![101, 0, 0], ![19, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1919, 101, 0]], ![![-7070, -2020, 101], ![-1515, -404, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![19, 1, 0]]], ![![![-70, -20, 1]], ![![-15, -4, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [16, 60, 69, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 36, 98], [43, 66, 5], [0, 1]]
 g := ![![[7, 69, 64], [14, 84, 34], [11, 41, 52], [45, 23], [101, 23], [1]], ![[43, 27, 1, 79], [16, 3, 74, 26], [34, 35, 92, 23], [91, 79], [80, 34], [39, 90, 98, 81]], ![[87, 21, 32, 87], [87, 90, 47, 47], [13, 89, 52, 70], [0, 25], [90, 9], [96, 78, 33, 22]]]
 h' := ![![[94, 36, 98], [85, 55, 8], [30, 99, 31], [30, 44, 19], [82, 24, 34], [87, 43, 34], [0, 1]], ![[43, 66, 5], [39, 34, 47], [42, 66, 6], [18, 78, 4], [49, 61, 64], [89, 24, 72], [94, 36, 98]], ![[0, 1], [92, 14, 48], [68, 41, 66], [4, 84, 80], [2, 18, 5], [0, 36, 100], [43, 66, 5]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 54], []]
 b := ![[], [29, 49, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [16, 60, 69, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-732639, 293962, -24308]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7113, 2854, -236]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [100, 60, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 105, 57], [75, 1, 50], [0, 1]]
 g := ![![[37, 66, 81], [11, 58, 99], [102, 90], [71, 4, 9], [102, 62], [1]], ![[52, 2, 99, 36], [63, 9, 96, 79], [13, 101], [92, 93, 53, 41], [14, 75], [23, 77, 96, 83]], ![[41, 38, 8, 103], [72, 94], [38, 57], [15, 89, 57, 45], [3, 44], [29, 8, 1, 24]]]
 h' := ![![[45, 105, 57], [77, 70, 9], [18, 41, 62], [69, 30, 25], [14, 1, 104], [7, 47, 13], [0, 1]], ![[75, 1, 50], [81, 51, 40], [45, 33, 45], [75, 102, 23], [2, 77, 54], [15, 63, 17], [45, 105, 57]], ![[0, 1], [33, 93, 58], [31, 33], [73, 82, 59], [106, 29, 56], [70, 104, 77], [75, 1, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95, 78], []]
 b := ![[], [79, 12, 100], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [100, 60, 94, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42265, 2889, 2889]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-395, 27, 27]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71529, 26892, -3037]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![-71529, 26892, -3037]] 
 ![![109, 0, 0], ![15, 1, 0], ![102, 0, 1]] where
  M :=![![![-71529, 26892, -3037], ![561845, -211231, 23855], ![-4413175, 1659175, -187376]]]
  hmulB := by decide  
  f := ![![![-231, -917, -113]], ![![160, -176, -25]], ![![1532, -1101, -165]]]
  g := ![![![-1515, 26892, -3037], ![11900, -211231, 23855], ![-93472, 1659175, -187376]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![44, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![44, 1, 0]] 
 ![![109, 0, 0], ![44, 1, 0], ![26, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![44, 1, 0], ![0, 44, 1], ![-185, 46, 45]]]
  hmulB := by decide  
  f := ![![![1541, 35, 0], ![-3815, 0, 0]], ![![572, 13, 0], ![-1416, 0, 0]], ![![370, 8, 0], ![-916, 1, 0]]]
  g := ![![![1, 0, 0], ![-44, 109, 0], ![-26, 0, 109]], ![![0, 1, 0], ![-18, 44, 1], ![-31, 46, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![49, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![49, 1, 0]] 
 ![![109, 0, 0], ![49, 1, 0], ![106, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![49, 1, 0], ![0, 49, 1], ![-185, 46, 50]]]
  hmulB := by decide  
  f := ![![![1618, 33, 0], ![-3597, 0, 0]], ![![686, 14, 0], ![-1525, 0, 0]], ![![1640, 33, 0], ![-3646, 1, 0]]]
  g := ![![![1, 0, 0], ![-49, 109, 0], ![-106, 0, 109]], ![![0, 1, 0], ![-23, 49, 1], ![-71, 46, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![-71529, 26892, -3037]] ![![109, 0, 0], ![44, 1, 0]]
  ![![109, 0, 0], ![6, -50, 1]] where
 M := ![![![-7796661, 2931228, -331033], ![-2585431, 972017, -109773]]]
 hmul := by decide  
 g := ![![![![-70791, 20742, -2914], ![-13407, 0, 0]], ![![-23479, 6913, -967], ![-4370, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![6, -50, 1]] ![![109, 0, 0], ![49, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5341, 109, 0]], ![![654, -5450, 109], ![109, -2398, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![49, 1, 0]]], ![![![6, -50, 1]], ![![1, -22, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [109, 72, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 57, 44], [20, 55, 69], [0, 1]]
 g := ![![[52, 109, 11], [52, 41], [39, 109], [27, 91], [58, 59, 4], [1]], ![[74, 45, 37, 62], [94, 62], [30, 9], [5, 18], [110, 74, 63, 9], [59, 40, 43, 95]], ![[74, 29, 80, 53], [82, 16], [25, 51], [87, 22], [85, 61, 97, 30], [86, 35, 25, 18]]]
 h' := ![![[95, 57, 44], [38, 90, 89], [100, 24, 70], [31, 35, 83], [6, 31, 54], [4, 41, 2], [0, 1]], ![[20, 55, 69], [36, 10, 41], [15, 67, 47], [11, 2, 3], [45, 66, 40], [54, 14, 106], [95, 57, 44]], ![[0, 1], [77, 13, 96], [38, 22, 109], [27, 76, 27], [40, 16, 19], [95, 58, 5], [20, 55, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 57], []]
 b := ![[], [88, 7, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [109, 72, 111, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2770082, 453808, 105542]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24514, 4016, 934]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, 13, 3]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-83, 13, 3]] 
 ![![127, 0, 0], ![61, 1, 0], ![89, 0, 1]] where
  M :=![![![-83, 13, 3], ![-555, 55, 16], ![-2960, 181, 71]]]
  hmulB := by decide  
  f := ![![![-1009, 380, -43]], ![![-422, 159, -18]], ![![-1198, 451, -51]]]
  g := ![![![-9, 13, 3], ![-42, 55, 16], ![-160, 181, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-51, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-51, 1, 0]] 
 ![![127, 0, 0], ![76, 1, 0], ![66, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-51, 1, 0], ![0, -51, 1], ![-185, 46, -50]]]
  hmulB := by decide  
  f := ![![![460, -9, 0], ![1143, 0, 0]], ![![256, -5, 0], ![636, 0, 0]], ![![276, -5, 0], ![686, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 127, 0], ![-66, 0, 127]], ![![-1, 1, 0], ![30, -51, 1], ![-3, 46, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-11, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-11, 1, 0]] 
 ![![127, 0, 0], ![116, 1, 0], ![6, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-11, 1, 0], ![0, -11, 1], ![-185, 46, -10]]]
  hmulB := by decide  
  f := ![![![1189, -108, 0], ![13716, 0, 0]], ![![1090, -99, 0], ![12574, 0, 0]], ![![56, -5, 0], ![646, 1, 0]]]
  g := ![![![1, 0, 0], ![-116, 127, 0], ![-6, 0, 127]], ![![-1, 1, 0], ![10, -11, 1], ![-43, 46, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-83, 13, 3]] ![![127, 0, 0], ![-51, 1, 0]]
  ![![127, 0, 0], ![-63, 10, 1]] where
 M := ![![![-10541, 1651, 381], ![3678, -608, -137]]]
 hmul := by decide  
 g := ![![![![-20, 3, 2], ![127, 0, 0]], ![![24, -4, -1], ![-10, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-63, 10, 1]] ![![127, 0, 0], ![-11, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-1397, 127, 0]], ![![-8001, 1270, 127], ![508, -127, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-11, 1, 0]]], ![![![-63, 10, 1]], ![![4, -1, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-504424, 189643, -21417]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-504424, 189643, -21417]] 
 ![![131, 0, 0], ![0, 131, 0], ![38, 101, 1]] where
  M :=![![![-504424, 189643, -21417], ![3962145, -1489606, 168226], ![-31121810, 11700541, -1321380]]]
  hmulB := by decide  
  f := ![![![-2794, 147, 64]], ![![-11840, 150, 211]], ![![-10237, 142, 184]]]
  g := ![![![2362, 17960, -21417], ![-18553, -141072, 168226], ![145730, 1108091, -1321380]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [18, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 130], [0, 1]]
 g := ![![[70, 81], [98, 4], [12], [53], [63], [11], [1]], ![[59, 50], [36, 127], [12], [53], [63], [11], [1]]]
 h' := ![![[50, 130], [70, 9], [40, 2], [16, 55], [70, 61], [126, 60], [113, 50], [0, 1]], ![[0, 1], [127, 122], [9, 129], [15, 76], [107, 70], [113, 71], [124, 81], [50, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [113, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [18, 81, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![863, -178, -29]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15, 21, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2794, -147, -64]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![2794, -147, -64]] 
 ![![131, 0, 0], ![29, 1, 0], ![76, 0, 1]] where
  M :=![![![2794, -147, -64], ![11840, -150, -211], ![39035, 2134, -361]]]
  hmulB := by decide  
  f := ![![![504424, -189643, 21417]], ![![81421, -30611, 3457]], ![![530214, -199339, 22512]]]
  g := ![![![91, -147, -64], ![246, -150, -211], ![35, 2134, -361]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-504424, 189643, -21417]] ![![2794, -147, -64]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-28, -58, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-28, -58, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![109, 79, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-28, -58, 1], ![-185, 18, -57], ![10545, -2807, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -79, 137]], ![![-1, -1, 1], ![44, 33, -57], ![108, 2, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [134, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 136], [0, 1]]
 g := ![![[16, 38], [14], [76], [52, 107], [17], [112], [1]], ![[59, 99], [14], [76], [119, 30], [17], [112], [1]]]
 h' := ![![[48, 136], [79, 77], [41, 98], [19, 58], [23, 92], [71, 47], [3, 48], [0, 1]], ![[0, 1], [76, 60], [87, 39], [63, 79], [55, 45], [135, 90], [115, 89], [48, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [49, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [134, 89, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1346, -283, 371]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-305, -216, 371]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![57, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![57, 1, 0]] 
 ![![137, 0, 0], ![57, 1, 0], ![39, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![57, 1, 0], ![0, 57, 1], ![-185, 46, 58]]]
  hmulB := by decide  
  f := ![![![2452, 43, 0], ![-5891, 0, 0]], ![![1026, 18, 0], ![-2465, 0, 0]], ![![708, 12, 0], ![-1701, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 137, 0], ![-39, 0, 137]], ![![0, 1, 0], ![-24, 57, 1], ![-37, 46, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-28, -58, 1]] ![![137, 0, 0], ![57, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7809, 137, 0]], ![![-3836, -7946, 137], ![-1781, -3288, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![57, 1, 0]]], ![![![-28, -58, 1]], ![![-13, -24, 0]]]]
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


lemma PB175I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB175I2 : PrimesBelowBoundCertificateInterval O 79 137 175 where
  m := 11
  g := ![2, 3, 2, 2, 1, 1, 3, 1, 3, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB175I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1, I127N2]
    · exact ![I131N0, I131N1]
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
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![127, 127, 127]
    · exact ![17161, 131]
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
      exact NI89N0
      exact NI89N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
  β := ![I83N1, I89N0, I89N1, I97N1, I101N1, I109N0, I109N1, I109N2, I127N0, I127N1, I127N2, I131N1, I137N1]
  Il := ![[I83N1], [I89N0, I89N0, I89N1], [I97N1], [I101N1], [], [], [I109N0, I109N1, I109N2], [], [I127N0, I127N1, I127N2], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
