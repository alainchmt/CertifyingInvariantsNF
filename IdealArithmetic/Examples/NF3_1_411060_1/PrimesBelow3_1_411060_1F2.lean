
import IdealArithmetic.Examples.NF3_1_411060_1.RI3_1_411060_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![20, -31, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![20, -31, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![20, 52, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![20, -31, 1], ![114, 64, -152], ![-3420, 570, -88]]]
  hmulB := by decide  
  f := ![![![-19, 31, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -52, 83]], ![![0, -1, 1], ![38, 96, -152], ![-20, 62, -88]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [39, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 82], [0, 1]]
 g := ![![[74, 81], [32, 78], [48], [63], [65, 29], [1]], ![[36, 2], [20, 5], [48], [63], [35, 54], [1]]]
 h' := ![![[19, 82], [80, 9], [77, 24], [66, 31], [38, 48], [44, 19], [0, 1]], ![[0, 1], [2, 74], [35, 59], [74, 52], [37, 35], [73, 64], [19, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [9, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [39, 64, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1863, 1806, -1571]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![401, 1006, -1571]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-14, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-14, 1, 0]] 
 ![![83, 0, 0], ![69, 1, 0], ![5, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-14, 1, 0], ![0, -16, 5], ![114, -18, -11]]]
  hmulB := by decide  
  f := ![![![225, -16, 0], ![1328, 0, 0]], ![![183, -13, 0], ![1080, 0, 0]], ![![23, 8, -3], ![136, 50, 0]]]
  g := ![![![1, 0, 0], ![-69, 83, 0], ![-5, 0, 83]], ![![-1, 1, 0], ![13, -16, 5], ![17, -18, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![20, -31, 1]] ![![83, 0, 0], ![-14, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1162, 83, 0]], ![![1660, -2573, 83], ![-166, 498, -166]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-14, 1, 0]]], ![![![20, -31, 1]], ![![-2, 6, -2]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-409447, 66075, 7379]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-409447, 66075, 7379]] 
 ![![89, 0, 0], ![0, 89, 0], ![17, 51, 1]] where
  M :=![![![-409447, 66075, 7379], ![841206, -674419, 352512], ![8373756, -1100802, -321907]]]
  hmulB := by decide  
  f := ![![![-6799394513, -147721203, -317626609]], ![![-36209433426, -786673145, -1691485842]], ![![-22644050135, -491956500, -1057793138]]]
  g := ![![![-6010, -3486, 7379], ![-57882, -209579, 352512], ![155575, 172095, -321907]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [33, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 88], [0, 1]]
 g := ![![[4, 34], [64], [18], [66, 4], [49, 69], [1]], ![[55, 55], [64], [18], [72, 85], [19, 20], [1]]]
 h' := ![![[46, 88], [15, 37], [13, 8], [47, 14], [74, 87], [56, 46], [0, 1]], ![[0, 1], [26, 52], [25, 81], [68, 75], [71, 2], [36, 43], [46, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [36, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [33, 43, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1017, 2072, -982]
  a := ![-1, -4, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![199, 586, -982]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6799394513, -147721203, -317626609]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-6799394513, -147721203, -317626609]] 
 ![![89, 0, 0], ![9, 1, 0], ![23, 0, 1]] where
  M :=![![![-6799394513, -147721203, -317626609], ![-36209433426, -786673145, -1691485842], ![-53049650568, -1152537654, -2478158987]]]
  hmulB := by decide  
  f := ![![![-409447, 66075, 7379]], ![![-31953, -896, 4707]], ![![-11725, 4707, -1710]]]
  g := ![![![20623689, -147721203, -317626609], ![109829205, -786673145, -1691485842], ![160908371, -1152537654, -2478158987]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-409447, 66075, 7379]] ![![-6799394513, -147721203, -317626609]]
  ![![89, 0, 0]] where
 M := ![![![89, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![24, 44, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![24, 44, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![24, 44, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![24, 44, 1], ![114, -82, 223], ![5130, -780, 141]]]
  hmulB := by decide  
  f := ![![![-23, -44, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -44, 97]], ![![0, 0, 1], ![-54, -102, 223], ![18, -72, 141]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [84, 2, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [95, 96], [0, 1]]
 g := ![![[67, 89], [3], [95], [49], [95], [95, 1]], ![[83, 8], [3], [95], [49], [95], [93, 96]]]
 h' := ![![[95, 96], [72, 63], [18, 10], [23, 17], [68, 90], [71, 17], [0, 1]], ![[0, 1], [43, 34], [95, 87], [86, 80], [82, 7], [37, 80], [95, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90]]
 b := ![[], [45, 45]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [84, 2, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4052, -8, 185]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -84, 185]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-29, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-29, 1, 0]] 
 ![![97, 0, 0], ![68, 1, 0], ![53, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-29, 1, 0], ![0, -31, 5], ![114, -18, -26]]]
  hmulB := by decide  
  f := ![![![2698, -93, 0], ![9021, 0, 0]], ![![1886, -65, 0], ![6306, 0, 0]], ![![1464, -38, -2], ![4895, 39, 0]]]
  g := ![![![1, 0, 0], ![-68, 97, 0], ![-53, 0, 97]], ![![-1, 1, 0], ![19, -31, 5], ![28, -18, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![24, 44, 1]] ![![97, 0, 0], ![-29, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2813, 97, 0]], ![![2328, 4268, 97], ![-582, -1358, 194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-29, 1, 0]]], ![![![24, 44, 1]], ![![-6, -14, 2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![11, 18, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![11, 18, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![11, 18, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![11, 18, 1], ![114, -43, 93], ![2166, -312, 50]]]
  hmulB := by decide  
  f := ![![![-10, -18, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -18, 101]], ![![0, 0, 1], ![-9, -17, 93], ![16, -12, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [91, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 100], [0, 1]]
 g := ![![[74, 100], [31], [49, 68], [56], [43], [33, 1]], ![[41, 1], [31], [71, 33], [56], [43], [66, 100]]]
 h' := ![![[33, 100], [30, 91], [86, 58], [36, 13], [48, 64], [27, 89], [0, 1]], ![[0, 1], [3, 10], [81, 43], [61, 88], [39, 37], [35, 12], [33, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [86, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [91, 68, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2896, 4188, -3235]
  a := ![1, 5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![381, 618, -3235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![8, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![8, 1, 0]] 
 ![![101, 0, 0], ![8, 1, 0], ![51, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![8, 1, 0], ![0, 6, 5], ![114, -18, 11]]]
  hmulB := by decide  
  f := ![![![289, 36, 0], ![-3636, 0, 0]], ![![8, 1, 0], ![-100, 0, 0]], ![![135, 12, -4], ![-1698, 81, 0]]]
  g := ![![![1, 0, 0], ![-8, 101, 0], ![-51, 0, 101]], ![![0, 1, 0], ![-3, 6, 5], ![-3, -18, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![11, 18, 1]] ![![101, 0, 0], ![8, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![808, 101, 0]], ![![1111, 1818, 101], ![202, 101, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![8, 1, 0]]], ![![![11, 18, 1]], ![![2, 1, 1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [72, 2, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 86, 80], [38, 16, 23], [0, 1]]
 g := ![![[24, 50, 100], [5, 91, 100], [26, 17, 60], [18, 30], [34, 13], [1]], ![[9, 68, 12, 65], [0, 35, 53, 70], [30, 81, 97, 22], [87, 93], [78, 64], [9, 55, 38, 90]], ![[97, 81, 98, 61], [92, 32, 48, 100], [20, 22, 38, 9], [16, 14], [89, 28], [77, 37, 23, 13]]]
 h' := ![![[23, 86, 80], [52, 45, 93], [85, 24, 10], [8, 32, 67], [58, 5, 66], [31, 101, 61], [0, 1]], ![[38, 16, 23], [32, 3, 41], [44, 60, 20], [36, 99, 27], [29, 58, 14], [86, 46, 95], [23, 86, 80]], ![[0, 1], [49, 55, 72], [32, 19, 73], [63, 75, 9], [59, 40, 23], [94, 59, 50], [38, 16, 23]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 54], []]
 b := ![[], [60, 76, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [72, 2, 42, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-791658, 454848, -210223]
  a := ![0, 3, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7686, 4416, -2041]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [55, 3, 31, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 49, 70], [71, 57, 37], [0, 1]]
 g := ![![[68, 51, 90], [80, 24, 81], [4, 35], [80, 72, 75], [34, 105], [1]], ![[72, 39, 35, 74], [57, 77, 60, 96], [70, 37], [91, 59, 75, 18], [100, 33], [69, 8, 101, 65]], ![[10, 58, 17, 44], [37, 2, 96, 42], [72, 42], [22, 25, 105, 16], [51, 90], [36, 67, 72, 42]]]
 h' := ![![[5, 49, 70], [94, 78, 82], [56, 91, 98], [94, 29, 28], [85, 17, 17], [52, 104, 76], [0, 1]], ![[71, 57, 37], [97, 104, 76], [25, 86, 79], [39, 34, 95], [18, 10, 19], [75, 32, 56], [5, 49, 70]], ![[0, 1], [13, 32, 56], [13, 37, 37], [96, 44, 91], [24, 80, 71], [49, 78, 82], [71, 57, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 67], []]
 b := ![[], [69, 65, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [55, 3, 31, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![360186396, -169758282, 76903147]
  a := ![1, -21, 62]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3366228, -1586526, 718721]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [69, 35, 27, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [42, 99, 68], [40, 9, 41], [0, 1]]
 g := ![![[61, 70, 87], [90, 64], [101, 37, 102], [26, 56, 31], [83, 75], [1]], ![[23, 29, 5, 76], [41, 25], [14, 84, 31, 37], [22, 84, 0, 17], [58, 49], [15, 6, 56, 76]], ![[73, 0, 103, 23], [73, 60], [71, 38, 30, 85], [100, 15, 39, 58], [65, 66], [103, 55, 24, 33]]]
 h' := ![![[42, 99, 68], [52, 81, 95], [7, 9, 101], [59, 29, 50], [15, 20, 85], [40, 74, 82], [0, 1]], ![[40, 9, 41], [21, 7, 41], [105, 81, 104], [84, 31, 24], [15, 95, 54], [23, 96, 102], [42, 99, 68]], ![[0, 1], [6, 21, 82], [62, 19, 13], [46, 49, 35], [9, 103, 79], [104, 48, 34], [40, 9, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64, 52], []]
 b := ![[], [48, 97, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [69, 35, 27, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![85674, -33354, 16023]
  a := ![-1, -1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![786, -306, 147]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10901710905659702693123363188077157, 236846655487222596484000881909117, 509262032176930795577274203087847]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![10901710905659702693123363188077157, 236846655487222596484000881909117, 509262032176930795577274203087847]] 
 ![![113, 0, 0], ![0, 113, 0], ![50, 55, 1]] where
  M :=![![![10901710905659702693123363188077157, 236846655487222596484000881909117, 509262032176930795577274203087847], ![58055871668170110695809259152014558, 1261301015500503179764425768677677, 2712019373966905369151827018809126], ![85056390393713486694985359689653896, 1847904587353162810215274562690058, 3973320389467408548916252787486803]]]
  hmulB := by decide  
  f := ![![![28892063780516171, 1456453162164975, -4697220077492829]], ![![-535483088834182506, 110529118851057143, -6809394421653612]], ![![-251118709072580572, 53710985814756709, -4474849315364483]]]
  g := ![![![-128861864629972009608321654569161, -245774912515433373099699825556836, 509262032176930795577274203087847], ![-686239796727213785502496387508334, -1308847473917515859500761595272781, 2712019373966905369151827018809126], ![-1005394947607583546467498050306958, -1917563865781896525488306449106939, 3973320389467408548916252787486803]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [40, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 112], [0, 1]]
 g := ![![[75, 85], [4], [98], [97], [85, 88], [51, 1]], ![[3, 28], [4], [98], [97], [53, 25], [102, 112]]]
 h' := ![![[51, 112], [79, 56], [37, 111], [62, 18], [103, 60], [107, 75], [0, 1]], ![[0, 1], [110, 57], [48, 2], [76, 95], [112, 53], [90, 38], [51, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [29, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [40, 62, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4486, 4008, -1994]
  a := ![0, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![922, 1006, -1994]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![28892063780516171, 1456453162164975, -4697220077492829]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![28892063780516171, 1456453162164975, -4697220077492829]] 
 ![![113, 0, 0], ![61, 1, 0], ![26, 0, 1]] where
  M :=![![![28892063780516171, 1456453162164975, -4697220077492829], ![-535483088834182506, 110529118851057143, -6809394421653612], ![-369447428347375356, -82582797848883498, 103719724429403531]]]
  hmulB := by decide  
  f := ![![![10901710905659702693123363188077157, 236846655487222596484000881909117, 509262032176930795577274203087847]], ![![6398763158525769690056056757740895, 139017230090452049250340527125078, 298911533953625521233323481479361]], ![![3261069680892617316072502677696106, 70848828584256197511498207896700, 152337462177589462247127274936025]]]
  g := ![![![550231353126250, 1456453162164975, -4697220077492829], ![-62838186582174109, 110529118851057143, -6809394421653612], ![17445932790000232, -82582797848883498, 103719724429403531]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![10901710905659702693123363188077157, 236846655487222596484000881909117, 509262032176930795577274203087847]] ![![28892063780516171, 1456453162164975, -4697220077492829]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11539589325315496648332597811, -250704972921095831282740896, -539059855939352516288750074]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-11539589325315496648332597811, -250704972921095831282740896, -539059855939352516288750074]] 
 ![![127, 0, 0], ![0, 127, 0], ![119, 41, 1]] where
  M :=![![![-11539589325315496648332597811, -250704972921095831282740896, -539059855939352516288750074], ![-61452823577086186856917508436, -1335101972564959692569614687, -2870704432423536705279954702], ![-90033190490091111623149970580, -1956028758692505232375664760, -4205806404988496397849569389]]]
  hmulB := by decide  
  f := ![![![-44034241435549, 11656897723152, -2312616221702]], ![![-263638249274028, -25720944891217, 51346639950654]], ![![-117984211495277, 748319171953, 14611311831919]]]
  g := ![![![414240421507617738504162685, 172053142681829585327212694, -539059855939352516288750074], ![2205992156545784890325961426, 916250234305512167117389985, -2870704432423536705279954702], ![3231950958295590234023218793, 1342378219258549977003595907, -4205806404988496397849569389]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [32, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [25, 126], [0, 1]]
 g := ![![[27, 4], [54, 8], [102, 1], [100, 31], [48, 113], [25, 1]], ![[0, 123], [0, 119], [0, 126], [113, 96], [79, 14], [50, 126]]]
 h' := ![![[25, 126], [50, 125], [38, 95], [102, 1], [115, 44], [89, 85], [0, 1]], ![[0, 1], [0, 2], [0, 32], [0, 126], [72, 83], [55, 42], [25, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [67, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [32, 102, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18480, 9684, -8660]
  a := ![2, 6, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8260, 2872, -8660]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![44034241435549, -11656897723152, 2312616221702]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![44034241435549, -11656897723152, 2312616221702]] 
 ![![127, 0, 0], ![46, 1, 0], ![27, 0, 1]] where
  M :=![![![44034241435549, -11656897723152, 2312616221702], ![263638249274028, 25720944891217, -51346639950654], ![-1065248091165300, 237575553677160, -25625695059437]]]
  hmulB := by decide  
  f := ![![![11539589325315496648332597811, 250704972921095831282740896, 539059855939352516288750074]], ![![4663574271981094745513519746, 101319139582168251429729889, 217853998469557105941436678]], ![![3162221277744956859276615051, 68701283681591280921335976, 147719862325598538091699381]]]
  g := ![![![4077251170981, -11656897723152, 2312616221702], ![3675858763352, 25720944891217, -51346639950654], ![-88990785777243, 237575553677160, -25625695059437]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-11539589325315496648332597811, -250704972921095831282740896, -539059855939352516288750074]] ![![44034241435549, -11656897723152, 2312616221702]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![22, -21, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![22, -21, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![22, 110, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![22, -21, 1], ![114, 46, -102], ![-2280, 390, -56]]]
  hmulB := by decide  
  f := ![![![-21, 21, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -110, 131]], ![![0, -1, 1], ![18, 86, -102], ![-8, 50, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [69, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 130], [0, 1]]
 g := ![![[65, 89], [75, 28], [35], [123], [107], [44], [1]], ![[57, 42], [124, 103], [35], [123], [107], [44], [1]]]
 h' := ![![[100, 130], [65, 58], [75, 91], [130, 67], [44, 56], [22, 32], [62, 100], [0, 1]], ![[0, 1], [101, 73], [5, 40], [18, 64], [11, 75], [78, 99], [106, 31], [100, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [47, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [69, 31, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![641, 61, 47]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -39, 47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-29, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-29, 1, 0]] 
 ![![131, 0, 0], ![102, 1, 0], ![56, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-29, 1, 0], ![0, -31, 5], ![114, -18, -26]]]
  hmulB := by decide  
  f := ![![![3655, -126, 0], ![16506, 0, 0]], ![![2872, -99, 0], ![12970, 0, 0]], ![![1562, -29, -4], ![7054, 105, 0]]]
  g := ![![![1, 0, 0], ![-102, 131, 0], ![-56, 0, 131]], ![![-1, 1, 0], ![22, -31, 5], ![26, -18, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![22, -21, 1]] ![![131, 0, 0], ![-29, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-3799, 131, 0]], ![![2882, -2751, 131], ![-524, 655, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-29, 1, 0]]], ![![![22, -21, 1]], ![![-4, 5, -1]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [74, 82, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 4, 133], [74, 132, 4], [0, 1]]
 g := ![![[134, 76, 103], [61, 8], [2, 32], [47, 41, 34], [103, 81], [22, 1], []], ![[88, 104, 57, 107], [62, 60], [64, 68], [56, 113, 46, 18], [128, 73], [18, 25], [46, 16]], ![[44, 45, 29, 126], [67, 37], [3, 122], [52, 42, 82, 69], [86, 32], [36, 16], [38, 16]]]
 h' := ![![[85, 4, 133], [83, 135, 68], [58, 86, 75], [84, 27, 124], [32, 129, 87], [16, 40, 128], [0, 0, 1], [0, 1]], ![[74, 132, 4], [126, 75, 79], [78, 87, 103], [108, 74, 94], [102, 48, 8], [126, 10, 22], [122, 108, 132], [85, 4, 133]], ![[0, 1], [110, 64, 127], [37, 101, 96], [56, 36, 56], [89, 97, 42], [98, 87, 124], [61, 29, 4], [74, 132, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 12], []]
 b := ![[], [104, 42, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [74, 82, 115, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6576274, 4459350, -2182410]
  a := ![1, 6, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48002, 32550, -15930]
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



lemma PB182I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB182I2 : PrimesBelowBoundCertificateInterval O 79 137 182 where
  m := 11
  g := ![2, 2, 2, 2, 1, 1, 1, 2, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB182I2_primes
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
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![16129, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I97N1, I101N1, I113N1, I127N1, I131N1]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [], [], [], [I113N1], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
