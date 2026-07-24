
import IdealArithmetic.Examples.NF3_1_252563_1.RI3_1_252563_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![41, 13, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![41, 13, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![41, 13, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![41, 13, 1], ![35, 3, 13], ![455, -459, 3]]]
  hmulB := by decide  
  f := ![![![-40, -13, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -13, 83]], ![![0, 0, 1], ![-6, -2, 13], ![4, -6, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [27, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 82], [0, 1]]
 g := ![![[55, 40], [61, 48], [38], [75], [77, 81], [1]], ![[0, 43], [78, 35], [38], [75], [59, 2], [1]]]
 h' := ![![[9, 82], [13, 17], [10, 52], [66, 72], [79, 65], [56, 9], [0, 1]], ![[0, 1], [0, 66], [63, 31], [50, 11], [0, 18], [54, 74], [9, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [55, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [27, 74, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![97, -115, -111]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![56, 16, -111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-13, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-13, 1, 0]] 
 ![![83, 0, 0], ![70, 1, 0], ![80, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-13, 1, 0], ![0, -13, 1], ![35, -38, -13]]]
  hmulB := by decide  
  f := ![![![521, -40, 0], ![3320, 0, 0]], ![![430, -33, 0], ![2740, 0, 0]], ![![484, -37, 0], ![3084, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 83, 0], ![-80, 0, 83]], ![![-1, 1, 0], ![10, -13, 1], ![45, -38, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![41, 13, 1]] ![![83, 0, 0], ![-13, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1079, 83, 0]], ![![3403, 1079, 83], ![-498, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-13, 1, 0]]], ![![![41, 13, 1]], ![![-6, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![21, -28, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![21, -28, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![21, 61, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![21, -28, 1], ![35, -17, -28], ![-980, 1099, -17]]]
  hmulB := by decide  
  f := ![![![-20, 28, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -61, 89]], ![![0, -1, 1], ![7, 19, -28], ![-7, 24, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [47, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 88], [0, 1]]
 g := ![![[5, 36], [20], [16], [86, 2], [34, 45], [1]], ![[0, 53], [20], [16], [61, 87], [50, 44], [1]]]
 h' := ![![[32, 88], [75, 6], [83, 38], [52, 4], [4, 25], [42, 32], [0, 1]], ![[0, 1], [0, 83], [53, 51], [2, 85], [3, 64], [87, 57], [32, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [6, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [47, 57, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-429, 661, -173]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36, 126, -173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![28, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![28, 1, 0]] 
 ![![89, 0, 0], ![28, 1, 0], ![17, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![28, 1, 0], ![0, 28, 1], ![35, -38, 28]]]
  hmulB := by decide  
  f := ![![![757, 27, 0], ![-2403, 0, 0]], ![![196, 7, 0], ![-622, 0, 0]], ![![93, 3, 0], ![-295, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 89, 0], ![-17, 0, 89]], ![![0, 1, 0], ![-9, 28, 1], ![7, -38, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![21, -28, 1]] ![![89, 0, 0], ![28, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2492, 89, 0]], ![![1869, -2492, 89], ![623, -801, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![28, 1, 0]]], ![![![21, -28, 1]], ![![7, -9, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [90, 73, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 30, 46], [87, 66, 51], [0, 1]]
 g := ![![[68, 35, 49], [93, 95], [19, 12], [60, 54], [86, 70], [1]], ![[71, 6, 3, 55], [63, 53], [53, 24], [52, 43], [27, 93], [31, 34, 47, 45]], ![[75, 79, 10, 15], [48, 86], [30, 81], [94, 48], [84, 43], [82, 84, 7, 52]]]
 h' := ![![[88, 30, 46], [44, 69, 7], [84, 64, 80], [40, 28, 20], [69, 77, 65], [7, 24, 78], [0, 1]], ![[87, 66, 51], [86, 79, 47], [18, 90, 76], [61, 43, 86], [45, 35, 72], [70, 27, 44], [88, 30, 46]], ![[0, 1], [2, 46, 43], [32, 40, 38], [4, 26, 88], [92, 82, 57], [59, 46, 72], [87, 66, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 23], []]
 b := ![[], [13, 32, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [90, 73, 19, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-181972, -2425, -4753]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1876, -25, -49]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-16, 42, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-16, 42, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![85, 42, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-16, 42, 1], ![35, -54, 42], ![1470, -1561, -54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -42, 101]], ![![-1, 0, 1], ![-35, -18, 42], ![60, 7, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [95, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 100], [0, 1]]
 g := ![![[38, 84], [33], [25, 97], [45], [19], [26, 1]], ![[0, 17], [33], [22, 4], [45], [19], [52, 100]]]
 h' := ![![[26, 100], [74, 36], [49, 72], [31, 20], [8, 67], [55, 76], [0, 1]], ![[0, 1], [0, 65], [2, 29], [46, 81], [33, 34], [11, 25], [26, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [54, 58]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [95, 75, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-39, 620, -572]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![481, 244, -572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-42, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-42, 1, 0]] 
 ![![101, 0, 0], ![59, 1, 0], ![54, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-42, 1, 0], ![0, -42, 1], ![35, -38, -42]]]
  hmulB := by decide  
  f := ![![![4075, -97, 0], ![9797, 0, 0]], ![![2437, -58, 0], ![5859, 0, 0]], ![![2202, -52, 0], ![5294, 1, 0]]]
  g := ![![![1, 0, 0], ![-59, 101, 0], ![-54, 0, 101]], ![![-1, 1, 0], ![24, -42, 1], ![45, -38, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-16, 42, 1]] ![![101, 0, 0], ![-42, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4242, 101, 0]], ![![-1616, 4242, 101], ![707, -1818, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-42, 1, 0]]], ![![![-16, 42, 1]], ![![7, -18, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![67, -21, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![67, -21, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![67, 82, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![67, -21, 1], ![35, 29, -21], ![-735, 833, 29]]]
  hmulB := by decide  
  f := ![![![-66, 21, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -82, 103]], ![![0, -1, 1], ![14, 17, -21], ![-26, -15, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [92, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 102], [0, 1]]
 g := ![![[17, 28], [26, 61], [4, 49], [52], [55], [84, 1]], ![[0, 75], [0, 42], [0, 54], [52], [55], [65, 102]]]
 h' := ![![[84, 102], [80, 53], [44, 24], [73, 96], [99, 19], [100, 63], [0, 1]], ![[0, 1], [0, 50], [0, 79], [0, 7], [47, 84], [36, 40], [84, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [91, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [92, 19, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![162, -60, -56]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38, 44, -56]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![21, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![21, 1, 0]] 
 ![![103, 0, 0], ![21, 1, 0], ![74, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![21, 1, 0], ![0, 21, 1], ![35, -38, 21]]]
  hmulB := by decide  
  f := ![![![883, 42, 0], ![-4326, 0, 0]], ![![147, 7, 0], ![-720, 0, 0]], ![![614, 29, 0], ![-3008, 1, 0]]]
  g := ![![![1, 0, 0], ![-21, 103, 0], ![-74, 0, 103]], ![![0, 1, 0], ![-5, 21, 1], ![-7, -38, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![67, -21, 1]] ![![103, 0, 0], ![21, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![2163, 103, 0]], ![![6901, -2163, 103], ![1442, -412, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![21, 1, 0]]], ![![![67, -21, 1]], ![![14, -4, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-43, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-43, 1, 0]] 
 ![![107, 0, 0], ![64, 1, 0], ![77, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-43, 1, 0], ![0, -43, 1], ![35, -38, -43]]]
  hmulB := by decide  
  f := ![![![388, -9, 0], ![963, 0, 0]], ![![216, -5, 0], ![536, 0, 0]], ![![276, -6, 0], ![685, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 107, 0], ![-77, 0, 107]], ![![-1, 1, 0], ![25, -43, 1], ![54, -38, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-42, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-42, 1, 0]] 
 ![![107, 0, 0], ![65, 1, 0], ![55, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-42, 1, 0], ![0, -42, 1], ![35, -38, -42]]]
  hmulB := by decide  
  f := ![![![3991, -95, 0], ![10165, 0, 0]], ![![2437, -58, 0], ![6207, 0, 0]], ![![2075, -49, 0], ![5285, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 107, 0], ![-55, 0, 107]], ![![-1, 1, 0], ![25, -42, 1], ![45, -38, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![207022731212, 4809810760, 5333827787]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![207022731212, 4809810760, 5333827787]] 
 ![![107, 0, 0], ![85, 1, 0], ![51, 0, 1]] where
  M :=![![![207022731212, 4809810760, 5333827787], ![186683972545, 4337275306, 4809810760], ![168343376600, 3911163665, 4337275306]]]
  hmulB := by decide  
  f := ![![![-641764, 666795, 49778]], ![![-493530, 506021, 45775]], ![![-87777, 97295, 50]]]
  g := ![![![-4428377575, 4809810760, 5333827787], ![-3993315675, 4337275306, 4809810760], ![-3600996033, 3911163665, 4337275306]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-43, 1, 0]] ![![107, 0, 0], ![-42, 1, 0]]
  ![![-641764, 666795, 49778]] where
 M := ![![![11449, 0, 0], ![-4494, 107, 0]], ![![-4601, 107, 0], ![1806, -85, 1]]]
 hmul := by decide  
 g := ![![![![22151432239684, 514649751320, 570719573209]], ![![-8508270738359, -197674776614, -219210956294]]], ![![![-8715293469571, -202484587374, -224544784081]], ![![3347507086721, 77773467245, 86246694804]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![-641764, 666795, 49778]] ![![207022731212, 4809810760, 5333827787]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![13, 53, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![13, 53, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![13, 53, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![13, 53, 1], ![35, -25, 53], ![1855, -1979, -25]]]
  hmulB := by decide  
  f := ![![![-12, -53, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -53, 109]], ![![0, 0, 1], ![-6, -26, 53], ![20, -6, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [88, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [34, 108], [0, 1]]
 g := ![![[12, 83], [38], [33, 48], [58, 75], [48], [34, 1]], ![[0, 26], [38], [30, 61], [101, 34], [48], [68, 108]]]
 h' := ![![[34, 108], [30, 44], [39, 93], [19, 87], [30, 82], [60, 87], [0, 1]], ![[0, 1], [0, 65], [40, 16], [34, 22], [93, 27], [75, 22], [34, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [54, 93]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [88, 75, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1494, 54, 400]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -194, 400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-53, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-53, 1, 0]] 
 ![![109, 0, 0], ![56, 1, 0], ![25, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-53, 1, 0], ![0, -53, 1], ![35, -38, -53]]]
  hmulB := by decide  
  f := ![![![4877, -92, 0], ![10028, 0, 0]], ![![2492, -47, 0], ![5124, 0, 0]], ![![1139, -21, 0], ![2342, 1, 0]]]
  g := ![![![1, 0, 0], ![-56, 109, 0], ![-25, 0, 109]], ![![-1, 1, 0], ![27, -53, 1], ![32, -38, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![13, 53, 1]] ![![109, 0, 0], ![-53, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-5777, 109, 0]], ![![1417, 5777, 109], ![-654, -2834, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-53, 1, 0]]], ![![![13, 53, 1]], ![![-6, -26, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [11, 31, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 45, 38], [59, 67, 75], [0, 1]]
 g := ![![[9, 41, 7], [1, 102], [110, 105], [10, 18], [39, 65, 18], [1]], ![[33, 39, 64, 47], [83, 105], [18, 52], [8, 16], [53, 82, 110, 10], [82, 69, 47, 67]], ![[67, 54, 98, 92], [22, 18], [65, 32], [99, 15], [58, 6, 23, 47], [15, 66, 28, 46]]]
 h' := ![![[14, 45, 38], [53, 25, 81], [105, 110, 92], [80, 61, 52], [23, 5, 73], [102, 82, 73], [0, 1]], ![[59, 67, 75], [63, 44, 49], [80, 49, 61], [74, 24, 39], [7, 32, 109], [34, 107, 97], [14, 45, 38]], ![[0, 1], [112, 44, 96], [44, 67, 73], [104, 28, 22], [17, 76, 44], [6, 37, 56], [59, 67, 75]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 11], []]
 b := ![[], [60, 70, 80], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [11, 31, 40, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20001, 23278, -1130]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-177, 206, -10]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-153, -2, -4]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-153, -2, -4]] 
 ![![127, 0, 0], ![0, 127, 0], ![70, 64, 1]] where
  M :=![![![-153, -2, -4], ![-140, -1, -2], ![-70, -64, -1]]]
  hmulB := by decide  
  f := ![![![1, -2, 0]], ![![0, 1, -2]], ![![0, 0, -1]]]
  g := ![![![1, 2, -4], ![0, 1, -2], ![0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [85, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 126], [0, 1]]
 g := ![![[113, 17], [73, 17], [59, 15], [56, 37], [40, 82], [47, 1]], ![[23, 110], [110, 110], [2, 112], [17, 90], [84, 45], [94, 126]]]
 h' := ![![[47, 126], [18, 115], [65, 12], [66, 74], [29, 52], [69, 92], [0, 1]], ![[0, 1], [89, 12], [121, 115], [115, 53], [60, 75], [75, 35], [47, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [113]]
 b := ![[], [101, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [85, 80, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1151, 820, 116]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73, -52, 116]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -2, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1, -2, 0]] 
 ![![127, 0, 0], ![63, 1, 0], ![95, 0, 1]] where
  M :=![![![1, -2, 0], ![0, 1, -2], ![-70, 76, 1]]]
  hmulB := by decide  
  f := ![![![-153, -2, -4]], ![![-77, -1, -2]], ![![-115, -2, -3]]]
  g := ![![![1, -2, 0], ![1, 1, -2], ![-39, 76, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-153, -2, -4]] ![![1, -2, 0]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [112, 118, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 83, 33], [105, 47, 98], [0, 1]]
 g := ![![[27, 15, 121], [23, 66, 129], [36, 113], [112, 7], [127, 75], [94, 1], []], ![[69, 106, 129, 101], [63, 127, 67, 100], [59, 89], [102, 109], [72, 75], [128, 113], [31, 41]], ![[35, 94, 37, 85], [40, 81, 11, 79], [13, 121], [42, 48], [], [41, 77], [97, 41]]]
 h' := ![![[120, 83, 33], [44, 34, 120], [70, 75, 103], [33, 29, 84], [1, 6, 20], [83, 62, 72], [0, 0, 1], [0, 1]], ![[105, 47, 98], [113, 81, 81], [63, 22, 111], [11, 56, 58], [118, 63, 90], [86, 43, 59], [55, 11, 47], [120, 83, 33]], ![[0, 1], [9, 16, 61], [31, 34, 48], [96, 46, 120], [52, 62, 21], [107, 26], [30, 120, 83], [105, 47, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 57], []]
 b := ![[], [118, 39, 34], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [112, 118, 37, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9956, 0, 0]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![76, 0, 0]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [89, 6, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 103, 52], [84, 33, 85], [0, 1]]
 g := ![![[37, 104, 93], [136, 44], [100, 107], [84, 86, 101], [30, 105], [79, 1], []], ![[51, 94, 95, 46], [106, 28], [116, 37], [82, 26, 2, 83], [127, 118], [103, 130], [59, 101]], ![[65, 19, 21, 47], [113, 135], [67, 16], [28, 18, 49, 113], [116, 18], [131, 60], [26, 101]]]
 h' := ![![[132, 103, 52], [111, 79, 40], [61, 72, 110], [59, 134, 45], [88, 15, 52], [93, 122, 70], [0, 0, 1], [0, 1]], ![[84, 33, 85], [12, 107, 85], [104, 61, 113], [133, 76, 96], [69, 11, 30], [1, 89, 23], [117, 39, 33], [132, 103, 52]], ![[0, 1], [106, 88, 12], [5, 4, 51], [25, 64, 133], [99, 111, 55], [55, 63, 44], [84, 98, 103], [84, 33, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 28], []]
 b := ![[], [18, 79, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [89, 6, 58, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29729, -30825, -1507]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![217, -225, -11]
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



lemma PB143I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB143I2 : PrimesBelowBoundCertificateInterval O 79 137 143 where
  m := 11
  g := ![2, 2, 1, 2, 2, 3, 2, 1, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB143I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
      exact NI101N1
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N1, I127N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
