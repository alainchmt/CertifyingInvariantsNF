
import IdealArithmetic.Examples.NF3_1_648324_3.RI3_1_648324_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-66, -7, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-66, -7, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![17, 76, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-66, -7, 1], ![426, 15, -14], ![-2982, -354, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -76, 83]], ![![-1, -1, 1], ![8, 13, -14], ![-39, -18, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [63, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 82], [0, 1]]
 g := ![![[21, 29], [67, 64], [31], [63], [76, 25], [1]], ![[0, 54], [55, 19], [31], [63], [35, 58], [1]]]
 h' := ![![[5, 82], [12, 64], [21, 75], [27, 60], [26, 35], [20, 5], [0, 1]], ![[0, 1], [0, 19], [64, 8], [78, 23], [35, 48], [45, 78], [5, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [4, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [63, 78, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![915, 297, 5]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, -1, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![14, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![14, 1, 0]] 
 ![![83, 0, 0], ![14, 1, 0], ![68, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![14, 1, 0], ![0, 14, 2], ![426, 81, 14]]]
  hmulB := by decide  
  f := ![![![57, 4, 0], ![-332, 0, 0]], ![![-14, -1, 0], ![84, 0, 0]], ![![44, -4, -1], ![-256, 42, 0]]]
  g := ![![![1, 0, 0], ![-14, 83, 0], ![-68, 0, 83]], ![![0, 1, 0], ![-4, 14, 2], ![-20, 81, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-66, -7, 1]] ![![83, 0, 0], ![14, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![1162, 83, 0]], ![![-5478, -581, 83], ![-498, -83, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![14, 1, 0]]], ![![![-66, -7, 1]], ![![-6, -1, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1409626897, 363171474, 49025062]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![1409626897, 363171474, 49025062]] 
 ![![89, 0, 0], ![0, 89, 0], ![80, 6, 1]] where
  M :=![![![1409626897, 363171474, 49025062], ![20884676412, 5380656919, 726342948], ![154711047924, 39859227600, 5380656919]]]
  hmulB := by decide  
  f := ![![![-49351, 6546, -434]], ![![-184884, -84505, 13092]], ![![-25492, 5106, -457]]]
  g := ![![![-28228967, 775518, 49025062], ![-418233252, 11489879, 726342948], ![-3098219164, 85115574, 5380656919]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [72, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 88], [0, 1]]
 g := ![![[80, 68], [85], [80], [21, 8], [10, 2], [1]], ![[0, 21], [85], [80], [43, 81], [60, 87], [1]]]
 h' := ![![[25, 88], [74, 54], [26, 68], [1, 13], [81, 39], [17, 25], [0, 1]], ![[0, 1], [0, 35], [35, 21], [59, 76], [77, 50], [19, 64], [25, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [83, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [72, 64, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5103, 821, 923]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-887, -53, 923]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![49351, -6546, 434]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![49351, -6546, 434]] 
 ![![89, 0, 0], ![77, 1, 0], ![17, 0, 1]] where
  M :=![![![49351, -6546, 434], ![184884, 84505, -13092], ![-2788596, -437784, 84505]]]
  hmulB := by decide  
  f := ![![![-1409626897, -363171474, -49025062]], ![![-1454224129, -374661353, -50576098]], ![![-2007580957, -517226322, -69821157]]]
  g := ![![![6135, -6546, 434], ![-68533, 84505, -13092], ![331283, -437784, 84505]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![1409626897, 363171474, 49025062]] ![![49351, -6546, 434]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [86, 58, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 12, 67], [73, 84, 30], [0, 1]]
 g := ![![[67, 31, 70], [74, 44], [88, 18], [7, 66], [52, 89], [1]], ![[72, 35, 31, 80], [], [48, 6], [68, 48], [74, 11], [84, 64, 10, 63]], ![[94, 51, 19, 76], [64, 44], [4, 47], [96, 33], [68, 94], [79, 52, 6, 34]]]
 h' := ![![[58, 12, 67], [29, 95, 78], [31, 52, 74], [79, 94, 55], [14, 82, 39], [11, 39, 34], [0, 1]], ![[73, 84, 30], [54, 35, 16], [32, 93], [38, 74, 54], [39, 92, 40], [96, 51, 37], [58, 12, 67]], ![[0, 1], [61, 64, 3], [91, 49, 23], [85, 26, 85], [75, 20, 18], [43, 7, 26], [73, 84, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 50], []]
 b := ![[], [45, 61, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [86, 58, 63, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![115818, -18236, -20758]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1194, -188, -214]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![47, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![47, 1, 0]] 
 ![![101, 0, 0], ![47, 1, 0], ![57, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![47, 1, 0], ![0, 47, 2], ![426, 81, 47]]]
  hmulB := by decide  
  f := ![![![1270, 27, 0], ![-2727, 0, 0]], ![![564, 12, 0], ![-1211, 0, 0]], ![![740, -8, -1], ![-1589, 51, 0]]]
  g := ![![![1, 0, 0], ![-47, 101, 0], ![-57, 0, 101]], ![![0, 1, 0], ![-23, 47, 2], ![-60, 81, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-28, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-28, 1, 0]] 
 ![![101, 0, 0], ![73, 1, 0], ![12, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-28, 1, 0], ![0, -28, 2], ![426, 81, -28]]]
  hmulB := by decide  
  f := ![![![2549, -91, 0], ![9191, 0, 0]], ![![1849, -66, 0], ![6667, 0, 0]], ![![340, 2, -1], ![1226, 51, 0]]]
  g := ![![![1, 0, 0], ![-73, 101, 0], ![-12, 0, 101]], ![![-1, 1, 0], ![20, -28, 2], ![-51, 81, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2953, 97, -40]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![2953, 97, -40]] 
 ![![101, 0, 0], ![82, 1, 0], ![72, 0, 1]] where
  M :=![![![2953, 97, -40], ![-17040, -287, 194], ![41322, -663, -287]]]
  hmulB := by decide  
  f := ![![![-210991, -54359, -7338]], ![![-202250, -52107, -7034]], ![![-379686, -97821, -13205]]]
  g := ![![![-21, 97, -40], ![-74, -287, 194], ![1152, -663, -287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![47, 1, 0]] ![![101, 0, 0], ![-28, 1, 0]]
  ![![-210991, -54359, -7338]] where
 M := ![![![10201, 0, 0], ![-2828, 101, 0]], ![![4747, 101, 0], ![-1316, 19, 2]]]
 hmul := by decide  
 g := ![![![![298253, 9797, -4040]], ![![-99724, -3003, 1314]]], ![![![121751, 4272, -1686]], ![![-40864, -1331, 552]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![-210991, -54359, -7338]] ![![2953, 97, -40]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [28, 55, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 68, 77], [1, 34, 26], [0, 1]]
 g := ![![[32, 73, 91], [58, 41, 98], [57, 31, 34], [87, 49], [99, 97], [1]], ![[32, 32, 54, 65], [77, 99, 12, 62], [25, 53, 33, 53], [63, 63], [99, 56], [63, 77, 38, 37]], ![[15, 94, 3, 2], [85, 93, 41, 13], [92, 73, 68, 91], [18, 29], [54, 7], [36, 0, 97, 66]]]
 h' := ![![[31, 68, 77], [24, 14, 20], [52, 73, 43], [70, 71, 31], [72, 69, 96], [75, 48, 32], [0, 1]], ![[1, 34, 26], [3, 30, 7], [75, 5, 79], [98, 72, 32], [27, 81, 28], [11, 79, 46], [31, 68, 77]], ![[0, 1], [27, 59, 76], [55, 25, 84], [57, 63, 40], [47, 56, 82], [23, 79, 25], [1, 34, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 82], []]
 b := ![[], [43, 56, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [28, 55, 71, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1706401, -652093, -113609]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16567, -6331, -1103]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-93, -23, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-93, -23, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![14, 84, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-93, -23, 1], ![426, -12, -46], ![-9798, -1650, -12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -84, 107]], ![![-1, -1, 1], ![10, 36, -46], ![-90, -6, -12]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [12, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 106], [0, 1]]
 g := ![![[54, 9], [52, 81], [52], [], [41], [101, 1]], ![[0, 98], [101, 26], [52], [], [41], [95, 106]]]
 h' := ![![[101, 106], [18, 3], [18, 9], [0, 42], [91], [72, 24], [0, 1]], ![[0, 1], [0, 104], [71, 98], [69, 65], [91], [35, 83], [101, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [54, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [12, 6, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![864, 369, 77]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -57, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![46, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![46, 1, 0]] 
 ![![107, 0, 0], ![46, 1, 0], ![12, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![46, 1, 0], ![0, 46, 2], ![426, 81, 46]]]
  hmulB := by decide  
  f := ![![![231, 5, 0], ![-535, 0, 0]], ![![46, 1, 0], ![-106, 0, 0]], ![![-36, -24, -1], ![84, 54, 0]]]
  g := ![![![1, 0, 0], ![-46, 107, 0], ![-12, 0, 107]], ![![0, 1, 0], ![-20, 46, 2], ![-36, 81, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-93, -23, 1]] ![![107, 0, 0], ![46, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4922, 107, 0]], ![![-9951, -2461, 107], ![-3852, -1070, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![46, 1, 0]]], ![![![-93, -23, 1]], ![![-36, -10, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-34, 29, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-34, 29, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![75, 29, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-34, 29, 1], ![426, 47, 58], ![12354, 2562, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -29, 109]], ![![-1, 0, 1], ![-36, -15, 58], ![81, 11, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [10, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [105, 108], [0, 1]]
 g := ![![[44, 29], [100], [47, 48], [87, 81], [36], [105, 1]], ![[37, 80], [100], [73, 61], [90, 28], [36], [101, 108]]]
 h' := ![![[105, 108], [47, 62], [75, 99], [2, 87], [41, 9], [40, 6], [0, 1]], ![[0, 1], [17, 47], [6, 10], [90, 22], [5, 100], [16, 103], [105, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [91, 100]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [10, 4, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16203, 3405, 809]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-408, -184, 809]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![51, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![51, 1, 0]] 
 ![![109, 0, 0], ![51, 1, 0], ![62, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![51, 1, 0], ![0, 51, 2], ![426, 81, 51]]]
  hmulB := by decide  
  f := ![![![1735, 34, 0], ![-3706, 0, 0]], ![![765, 15, 0], ![-1634, 0, 0]], ![![956, -7, -1], ![-2042, 55, 0]]]
  g := ![![![1, 0, 0], ![-51, 109, 0], ![-62, 0, 109]], ![![0, 1, 0], ![-25, 51, 2], ![-63, 81, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-34, 29, 1]] ![![109, 0, 0], ![51, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5559, 109, 0]], ![![-3706, 3161, 109], ![-1308, 1526, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![51, 1, 0]]], ![![![-34, 29, 1]], ![![-12, 14, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-70, 47, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-70, 47, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![43, 47, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-70, 47, 1], ![426, 11, 94], ![20022, 4020, 11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -47, 113]], ![![-1, 0, 1], ![-32, -39, 94], ![173, 31, 11]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [41, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 112], [0, 1]]
 g := ![![[74, 102], [77], [16], [52], [47, 32], [17, 1]], ![[0, 11], [77], [16], [52], [26, 81], [34, 112]]]
 h' := ![![[17, 112], [18, 92], [24, 90], [51, 109], [107, 74], [94, 22], [0, 1]], ![[0, 1], [0, 21], [85, 23], [96, 4], [9, 39], [16, 91], [17, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [105, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [41, 96, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2610, 9, 5]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25, -2, 5]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![19, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![19, 1, 0]] 
 ![![113, 0, 0], ![19, 1, 0], ![102, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![19, 1, 0], ![0, 19, 2], ![426, 81, 19]]]
  hmulB := by decide  
  f := ![![![77, 4, 0], ![-452, 0, 0]], ![![-19, -1, 0], ![114, 0, 0]], ![![88, -5, -1], ![-518, 57, 0]]]
  g := ![![![1, 0, 0], ![-19, 113, 0], ![-102, 0, 113]], ![![0, 1, 0], ![-5, 19, 2], ![-27, 81, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-70, 47, 1]] ![![113, 0, 0], ![19, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![2147, 113, 0]], ![![-7910, 5311, 113], ![-904, 904, 113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![19, 1, 0]]], ![![![-70, 47, 1]], ![![-8, 8, 1]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [40, 31, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 88, 26], [45, 38, 101], [0, 1]]
 g := ![![[47, 54, 69], [12, 4, 73], [122, 26, 31], [31, 87, 99], [51, 78, 74], [1]], ![[46, 56, 37, 52], [67, 86, 89, 4], [98, 57, 117, 98], [41, 124, 88, 64], [99, 101, 25, 62], [123, 36, 100, 50]], ![[60, 87, 108, 95], [48, 49, 96, 77], [110, 72, 9, 90], [20, 90, 19, 5], [92, 17, 77, 12], [41, 1, 31, 77]]]
 h' := ![![[25, 88, 26], [28, 98, 113], [73, 15, 33], [30, 68, 44], [119, 74, 37], [87, 96, 70], [0, 1]], ![[45, 38, 101], [47, 5, 111], [55, 19, 120], [63, 16, 11], [39, 108, 28], [37, 108, 76], [25, 88, 26]], ![[0, 1], [97, 24, 30], [13, 93, 101], [78, 43, 72], [108, 72, 62], [77, 50, 108], [45, 38, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 118], []]
 b := ![[], [3, 6, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [40, 31, 57, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1237996, 424561, 77216]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9748, 3343, 608]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-11, -67, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-11, -67, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![120, 64, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-11, -67, 1], ![426, 70, -134], ![-28542, -5214, 70]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -64, 131]], ![![-1, -1, 1], ![126, 66, -134], ![-282, -74, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [42, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 130], [0, 1]]
 g := ![![[121, 25], [103, 113], [7], [60], [64], [74], [1]], ![[10, 106], [10, 18], [7], [60], [64], [74], [1]]]
 h' := ![![[27, 130], [128, 5], [108, 47], [128, 111], [40, 45], [97, 123], [89, 27], [0, 1]], ![[0, 1], [1, 126], [67, 84], [112, 20], [76, 86], [12, 8], [32, 104], [27, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [68, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [42, 104, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16786, -3468, 740]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-806, -388, 740]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![3, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![3, 1, 0]] 
 ![![131, 0, 0], ![3, 1, 0], ![61, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![3, 1, 0], ![0, 3, 2], ![426, 81, 3]]]
  hmulB := by decide  
  f := ![![![127, 42, 0], ![-5502, 0, 0]], ![![-3, -1, 0], ![132, 0, 0]], ![![59, 18, -1], ![-2556, 66, 0]]]
  g := ![![![1, 0, 0], ![-3, 131, 0], ![-61, 0, 131]], ![![0, 1, 0], ![-1, 3, 2], ![0, 81, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-11, -67, 1]] ![![131, 0, 0], ![3, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![393, 131, 0]], ![![-1441, -8777, 131], ![393, -131, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![3, 1, 0]]], ![![![-11, -67, 1]], ![![3, -1, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-88, -32, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-88, -32, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![49, 105, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-88, -32, 1], ![426, -7, -64], ![-13632, -2379, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-49, -105, 137]], ![![-1, -1, 1], ![26, 49, -64], ![-97, -12, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [75, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 136], [0, 1]]
 g := ![![[22, 68], [50], [73], [35, 129], [1], [36], [1]], ![[25, 69], [50], [73], [83, 8], [1], [36], [1]]]
 h' := ![![[131, 136], [5, 43], [78, 119], [115, 115], [37, 35], [48, 136], [62, 131], [0, 1]], ![[0, 1], [21, 94], [49, 18], [110, 22], [101, 102], [54, 1], [98, 6], [131, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [109, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [75, 6, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-530, 19, 115]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45, -88, 115]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![64, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![64, 1, 0]] 
 ![![137, 0, 0], ![64, 1, 0], ![7, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![64, 1, 0], ![0, 64, 2], ![426, 81, 64]]]
  hmulB := by decide  
  f := ![![![833, 13, 0], ![-1781, 0, 0]], ![![320, 5, 0], ![-684, 0, 0]], ![![-49, -33, -1], ![105, 69, 0]]]
  g := ![![![1, 0, 0], ![-64, 137, 0], ![-7, 0, 137]], ![![0, 1, 0], ![-30, 64, 2], ![-38, 81, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-88, -32, 1]] ![![137, 0, 0], ![64, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8768, 137, 0]], ![![-12056, -4384, 137], ![-5206, -2055, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![64, 1, 0]]], ![![![-88, -32, 1]], ![![-38, -15, 0]]]]
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


lemma PB228I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB228I2 : PrimesBelowBoundCertificateInterval O 79 137 228 where
  m := 11
  g := ![2, 2, 1, 3, 1, 2, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB228I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
      exact NI101N2
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
      exact NI113N1
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
      exact NI137N1
  β := ![I83N1, I89N1, I101N0, I101N1, I101N2, I107N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N0, I101N1, I101N2], [], [I107N1], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
