
import IdealArithmetic.Examples.NF3_1_662796_4.RI3_1_662796_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-102, -26, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-102, -26, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![64, 57, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-102, -26, 1], ![494, 12, -26], ![-12844, -2470, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -57, 83]], ![![-2, -1, 1], ![26, 18, -26], ![-164, -38, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [14, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 82], [0, 1]]
 g := ![![[41, 41], [81, 70], [51], [21], [64, 49], [1]], ![[79, 42], [73, 13], [51], [21], [75, 34], [1]]]
 h' := ![![[7, 82], [28, 46], [58, 53], [78, 47], [17, 41], [69, 7], [0, 1]], ![[0, 1], [18, 37], [14, 30], [75, 36], [55, 42], [35, 76], [7, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [82, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [14, 76, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1002, 646, 39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -19, 39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![26, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![26, 1, 0]] 
 ![![83, 0, 0], ![26, 1, 0], ![71, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![26, 1, 0], ![0, 26, 1], ![494, 114, 26]]]
  hmulB := by decide  
  f := ![![![365, 14, 0], ![-1162, 0, 0]], ![![78, 3, 0], ![-248, 0, 0]], ![![269, 10, 0], ![-856, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 83, 0], ![-71, 0, 83]], ![![0, 1, 0], ![-9, 26, 1], ![-52, 114, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-102, -26, 1]] ![![83, 0, 0], ![26, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![2158, 83, 0]], ![![-8466, -2158, 83], ![-2158, -664, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![26, 1, 0]]], ![![![-102, -26, 1]], ![![-26, -8, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-106, -50, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-106, -50, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![72, 39, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-106, -50, 1], ![494, 8, -50], ![-24700, -5206, 8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -39, 89]], ![![-2, -1, 1], ![46, 22, -50], ![-284, -62, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [43, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 88], [0, 1]]
 g := ![![[16, 81], [39], [49], [38, 2], [12, 42], [1]], ![[2, 8], [39], [49], [86, 87], [41, 47], [1]]]
 h' := ![![[24, 88], [61, 9], [74, 22], [57, 82], [18, 64], [46, 24], [0, 1]], ![[0, 1], [10, 80], [68, 67], [67, 7], [41, 25], [88, 65], [24, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [45, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [43, 65, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5949, 2952, 1219]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1053, -501, 1219]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-39, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-39, 1, 0]] 
 ![![89, 0, 0], ![50, 1, 0], ![81, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-39, 1, 0], ![0, -39, 1], ![494, 114, -39]]]
  hmulB := by decide  
  f := ![![![1015, -26, 0], ![2314, 0, 0]], ![![586, -15, 0], ![1336, 0, 0]], ![![915, -23, 0], ![2086, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 89, 0], ![-81, 0, 89]], ![![-1, 1, 0], ![21, -39, 1], ![-23, 114, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-106, -50, 1]] ![![89, 0, 0], ![-39, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-3471, 89, 0]], ![![-9434, -4450, 89], ![4628, 1958, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-39, 1, 0]]], ![![![-106, -50, 1]], ![![52, 22, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-87, 30, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-87, 30, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![10, 30, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-87, 30, 1], ![494, 27, 30], ![14820, 3914, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -30, 97]], ![![-1, 0, 1], ![2, -9, 30], ![150, 32, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [84, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 96], [0, 1]]
 g := ![![[47, 24], [43], [64], [44], [70], [29, 1]], ![[64, 73], [43], [64], [44], [70], [58, 96]]]
 h' := ![![[29, 96], [78, 86], [2, 25], [25, 8], [61, 23], [86, 78], [0, 1]], ![[0, 1], [50, 11], [48, 72], [63, 89], [49, 74], [20, 19], [29, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [16, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [84, 68, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1160, 206, 175]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -52, 175]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-30, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-30, 1, 0]] 
 ![![97, 0, 0], ![67, 1, 0], ![70, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-30, 1, 0], ![0, -30, 1], ![494, 114, -30]]]
  hmulB := by decide  
  f := ![![![2071, -69, 0], ![6693, 0, 0]], ![![1441, -48, 0], ![4657, 0, 0]], ![![1510, -50, 0], ![4880, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 97, 0], ![-70, 0, 97]], ![![-1, 1, 0], ![20, -30, 1], ![-52, 114, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-87, 30, 1]] ![![97, 0, 0], ![-30, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2910, 97, 0]], ![![-8439, 2910, 97], ![3104, -873, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-30, 1, 0]]], ![![![-87, 30, 1]], ![![32, -9, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-49, -41, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-49, -41, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![52, 60, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-49, -41, 1], ![494, 65, -41], ![-20254, -4180, 65]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -60, 101]], ![![-1, -1, 1], ![26, 25, -41], ![-234, -80, 65]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [72, 42, 1] where
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
 g := ![![[9, 68], [84], [30, 1], [49], [19], [59, 1]], ![[82, 33], [84], [89, 100], [49], [19], [17, 100]]]
 h' := ![![[59, 100], [18, 88], [62, 65], [65, 100], [82, 7], [95, 76], [0, 1]], ![[0, 1], [59, 13], [59, 36], [6, 1], [91, 94], [34, 25], [59, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [71, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [72, 42, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2849, 3806, 895]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-489, -494, 895]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![41, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![41, 1, 0]] 
 ![![101, 0, 0], ![41, 1, 0], ![36, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![41, 1, 0], ![0, 41, 1], ![494, 114, 41]]]
  hmulB := by decide  
  f := ![![![1436, 35, 0], ![-3535, 0, 0]], ![![574, 14, 0], ![-1413, 0, 0]], ![![468, 11, 0], ![-1152, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 101, 0], ![-36, 0, 101]], ![![0, 1, 0], ![-17, 41, 1], ![-56, 114, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-49, -41, 1]] ![![101, 0, 0], ![41, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![4141, 101, 0]], ![![-4949, -4141, 101], ![-1515, -1616, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![41, 1, 0]]], ![![![-49, -41, 1]], ![![-15, -16, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [33, 70, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 76, 51], [23, 26, 52], [0, 1]]
 g := ![![[95, 39, 13], [33, 34, 34], [26, 91, 9], [49, 29], [54, 72], [1]], ![[57, 34, 47, 75], [43, 56, 67, 78], [95, 70, 13, 94], [47, 7], [94, 72], [25, 39, 34, 90]], ![[61, 64, 15, 8], [40, 90, 40, 61], [24, 102, 32, 98], [49, 16], [90, 82], [33, 36, 94, 13]]]
 h' := ![![[58, 76, 51], [44, 93, 61], [69, 99, 31], [94, 31, 3], [28, 9, 21], [70, 33, 81], [0, 1]], ![[23, 26, 52], [39, 31, 46], [87, 22, 87], [19, 85, 11], [5, 31, 78], [29, 4, 81], [58, 76, 51]], ![[0, 1], [35, 82, 99], [91, 85, 88], [4, 90, 89], [73, 63, 4], [57, 66, 44], [23, 26, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 35], []]
 b := ![[], [74, 91, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [33, 70, 22, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-391709, -137402, -12360]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3803, -1334, -120]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [77, 104, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 99, 98], [44, 7, 9], [0, 1]]
 g := ![![[74, 71, 57], [67, 100, 30], [36, 61], [64, 104, 27], [93, 75], [1]], ![[92, 106, 103, 7], [63, 64, 75, 26], [43, 37], [53, 11, 63, 67], [31, 11], [14, 27, 1, 20]], ![[70, 42, 56, 69], [80, 70, 101, 105], [11, 10], [78, 69, 71, 19], [58, 4], [60, 103, 77, 87]]]
 h' := ![![[80, 99, 98], [84, 74, 59], [46, 45, 43], [101, 24, 75], [52, 34, 53], [30, 3, 17], [0, 1]], ![[44, 7, 9], [59, 67, 68], [35, 55, 3], [55, 69, 95], [83, 28, 65], [104, 48, 92], [80, 99, 98]], ![[0, 1], [47, 73, 87], [25, 7, 61], [103, 14, 44], [77, 45, 96], [100, 56, 105], [44, 7, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 41], []]
 b := ![[], [101, 68, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [77, 104, 90, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8588462, 2624603, 209078]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![80266, 24529, 1954]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-27, 14, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-27, 14, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![82, 14, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-27, 14, 1], ![494, 87, 14], ![6916, 2090, 87]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -14, 109]], ![![-1, 0, 1], ![-6, -1, 14], ![-2, 8, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [81, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 108], [0, 1]]
 g := ![![[44, 35], [88], [29, 81], [103, 94], [75], [33, 1]], ![[0, 74], [88], [86, 28], [44, 15], [75], [66, 108]]]
 h' := ![![[33, 108], [69, 97], [49, 57], [50, 100], [8, 51], [52, 27], [0, 1]], ![[0, 1], [0, 12], [77, 52], [80, 9], [56, 58], [71, 82], [33, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [71, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [81, 76, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2958, 32, 49]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -6, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-14, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-14, 1, 0]] 
 ![![109, 0, 0], ![95, 1, 0], ![22, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-14, 1, 0], ![0, -14, 1], ![494, 114, -14]]]
  hmulB := by decide  
  f := ![![![659, -47, 0], ![5123, 0, 0]], ![![561, -40, 0], ![4361, 0, 0]], ![![142, -10, 0], ![1104, 1, 0]]]
  g := ![![![1, 0, 0], ![-95, 109, 0], ![-22, 0, 109]], ![![-1, 1, 0], ![12, -14, 1], ![-92, 114, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-27, 14, 1]] ![![109, 0, 0], ![-14, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1526, 109, 0]], ![![-2943, 1526, 109], ![872, -109, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-14, 1, 0]]], ![![![-27, 14, 1]], ![![8, -1, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![56, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![56, 1, 0]] 
 ![![113, 0, 0], ![56, 1, 0], ![28, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![56, 1, 0], ![0, 56, 1], ![494, 114, 56]]]
  hmulB := by decide  
  f := ![![![1289, 23, 0], ![-2599, 0, 0]], ![![616, 11, 0], ![-1242, 0, 0]], ![![252, 4, 0], ![-508, 1, 0]]]
  g := ![![![1, 0, 0], ![-56, 113, 0], ![-28, 0, 113]], ![![0, 1, 0], ![-28, 56, 1], ![-66, 114, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-47, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-47, 1, 0]] 
 ![![113, 0, 0], ![66, 1, 0], ![51, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-47, 1, 0], ![0, -47, 1], ![494, 114, -47]]]
  hmulB := by decide  
  f := ![![![5124, -109, 0], ![12317, 0, 0]], ![![3056, -65, 0], ![7346, 0, 0]], ![![2370, -50, 0], ![5697, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 113, 0], ![-51, 0, 113]], ![![-1, 1, 0], ![27, -47, 1], ![-41, 114, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37, -12, -1]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-37, -12, -1]] 
 ![![113, 0, 0], ![104, 1, 0], ![32, 0, 1]] where
  M :=![![![-37, -12, -1], ![-494, -151, -12], ![-5928, -1862, -151]]]
  hmulB := by decide  
  f := ![![![-457, -50, 7]], ![![-390, -43, 6]], ![![-348, -34, 5]]]
  g := ![![![11, -12, -1], ![138, -151, -12], ![1704, -1862, -151]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![56, 1, 0]] ![![113, 0, 0], ![-47, 1, 0]]
  ![![457, 50, -7]] where
 M := ![![![12769, 0, 0], ![-5311, 113, 0]], ![![6328, 113, 0], ![-2632, 9, 1]]]
 hmul := by decide  
 g := ![![![![4181, 1356, 113]], ![![-1245, -413, -35]]], ![![![2566, 823, 68]], ![![-770, -251, -21]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![457, 50, -7]] ![![-37, -12, -1]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![1, 1, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![1, 1, 0]] 
 ![![127, 0, 0], ![1, 1, 0], ![126, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![1, 1, 0], ![0, 1, 1], ![494, 114, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![127, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![126, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 127, 0], ![-126, 0, 127]], ![![0, 1, 0], ![-1, 1, 1], ![2, 114, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![15, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![15, 1, 0]] 
 ![![127, 0, 0], ![15, 1, 0], ![29, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![15, 1, 0], ![0, 15, 1], ![494, 114, 15]]]
  hmulB := by decide  
  f := ![![![226, 15, 0], ![-1905, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![32, 2, 0], ![-269, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 127, 0], ![-29, 0, 127]], ![![0, 1, 0], ![-2, 15, 1], ![-13, 114, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-16, 1, 0]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-16, 1, 0]] 
 ![![127, 0, 0], ![111, 1, 0], ![125, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-16, 1, 0], ![0, -16, 1], ![494, 114, -16]]]
  hmulB := by decide  
  f := ![![![161, -10, 0], ![1270, 0, 0]], ![![145, -9, 0], ![1144, 0, 0]], ![![163, -10, 0], ![1286, 1, 0]]]
  g := ![![![1, 0, 0], ![-111, 127, 0], ![-125, 0, 127]], ![![-1, 1, 0], ![13, -16, 1], ![-80, 114, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![1, 1, 0]] ![![127, 0, 0], ![15, 1, 0]]
  ![![127, 0, 0], ![-112, 16, 1]] where
 M := ![![![16129, 0, 0], ![1905, 127, 0]], ![![127, 127, 0], ![15, 16, 1]]]
 hmul := by decide  
 g := ![![![![127, 0, 0], ![0, 0, 0]], ![![15, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-112, 16, 1]] ![![127, 0, 0], ![-16, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-2032, 127, 0]], ![![-14224, 2032, 127], ![2286, -254, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-16, 1, 0]]], ![![![-112, 16, 1]], ![![18, -2, 0]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [110, 43, 68, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 18, 118], [56, 112, 13], [0, 1]]
 g := ![![[44, 62, 25], [10, 104, 3], [25, 44], [27, 77], [111, 16], [63, 1], []], ![[87, 0, 8, 116], [79, 100, 77, 50], [111, 36], [128, 117], [91, 15], [75, 99], [92, 38]], ![[55, 71, 97, 27], [127, 0, 118, 34], [53, 59], [73, 113], [46, 80], [54, 62], [66, 38]]]
 h' := ![![[7, 18, 118], [79, 112, 126], [42, 73, 38], [33, 55, 31], [11, 83, 83], [13, 63, 127], [0, 0, 1], [0, 1]], ![[56, 112, 13], [128, 40, 80], [113, 9, 32], [128, 115, 6], [86, 26, 95], [128, 51, 43], [16, 107, 112], [7, 18, 118]], ![[0, 1], [116, 110, 56], [33, 49, 61], [112, 92, 94], [85, 22, 84], [125, 17, 92], [68, 24, 18], [56, 112, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 40], []]
 b := ![[], [100, 63, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [110, 43, 68, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2763052, 1225505, 141742]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![21092, 9355, 1082]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-110, -2, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-110, -2, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![27, 135, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-110, -2, 1], ![494, 4, -2], ![-988, 266, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -135, 137]], ![![-1, -1, 1], ![4, 2, -2], ![-8, -2, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [53, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 136], [0, 1]]
 g := ![![[103, 112], [87], [112], [7, 72], [112], [30], [1]], ![[126, 25], [87], [112], [12, 65], [112], [30], [1]]]
 h' := ![![[21, 136], [22, 89], [48, 19], [40, 89], [14, 49], [123, 48], [84, 21], [0, 1]], ![[0, 1], [110, 48], [36, 118], [128, 48], [84, 88], [35, 89], [114, 116], [21, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [100, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [53, 116, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19471, -3784, 796]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -812, 796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![2, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![2, 1, 0]] 
 ![![137, 0, 0], ![2, 1, 0], ![133, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![2, 1, 0], ![0, 2, 1], ![494, 114, 2]]]
  hmulB := by decide  
  f := ![![![135, 67, 0], ![-9179, 0, 0]], ![![-2, -1, 0], ![138, 0, 0]], ![![131, 65, 0], ![-8907, 1, 0]]]
  g := ![![![1, 0, 0], ![-2, 137, 0], ![-133, 0, 137]], ![![0, 1, 0], ![-1, 2, 1], ![0, 114, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-110, -2, 1]] ![![137, 0, 0], ![2, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![274, 137, 0]], ![![-15070, -274, 137], ![274, 0, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![2, 1, 0]]], ![![![-110, -2, 1]], ![![2, 0, 0]]]]
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


lemma PB231I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB231I2 : PrimesBelowBoundCertificateInterval O 79 137 231 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 2, 3, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB231I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
    · exact ![I109N0, I109N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![11881, 109]
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
      exact NI83N1
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
  β := ![I83N1, I89N1, I97N1, I101N1, I109N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [], [], [I109N1], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
