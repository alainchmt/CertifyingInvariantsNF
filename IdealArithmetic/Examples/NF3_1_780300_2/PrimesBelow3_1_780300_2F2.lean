
import IdealArithmetic.Examples.NF3_1_780300_2.RI3_1_780300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![2, 1, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![2, 1, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![2, 1, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![2, 1, 1], ![170, 2, 2], ![170, 85, 2]]]
  hmulB := by decide  
  f := ![![![-1, -1, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -1, 83]], ![![0, 0, 1], ![2, 0, 2], ![2, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [79, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 82], [0, 1]]
 g := ![![[82, 31], [76, 81], [81], [77], [70, 16], [1]], ![[41, 52], [1, 2], [81], [77], [6, 67], [1]]]
 h' := ![![[79, 82], [55, 23], [70, 74], [24, 74], [31, 49], [4, 79], [0, 1]], ![[0, 1], [46, 60], [23, 9], [60, 9], [1, 34], [20, 4], [79, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [31, 57]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [79, 4, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1964, 761, 14]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, 9, 14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-2, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-2, 1, 0]] 
 ![![83, 0, 0], ![81, 1, 0], ![81, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-2, 1, 0], ![0, -2, 2], ![170, 0, -2]]]
  hmulB := by decide  
  f := ![![![89, -44, 0], ![3652, 0, 0]], ![![87, -43, 0], ![3570, 0, 0]], ![![87, -42, -1], ![3570, 42, 0]]]
  g := ![![![1, 0, 0], ![-81, 83, 0], ![-81, 0, 83]], ![![-1, 1, 0], ![0, -2, 2], ![4, 0, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![2, 1, 1]] ![![83, 0, 0], ![-2, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-166, 83, 0]], ![![166, 83, 83], ![166, 0, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-2, 1, 0]]], ![![![2, 1, 1]], ![![2, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-22, -16, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-22, -16, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![67, 73, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-22, -16, 1], ![170, -22, -32], ![-2720, 85, -22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-67, -73, 89]], ![![-1, -1, 1], ![26, 26, -32], ![-14, 19, -22]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [61, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 88], [0, 1]]
 g := ![![[53, 47], [8], [68], [18, 79], [64, 40], [1]], ![[25, 42], [8], [68], [41, 10], [61, 49], [1]]]
 h' := ![![[60, 88], [24, 74], [45, 39], [59, 54], [12, 48], [28, 60], [0, 1]], ![[0, 1], [14, 15], [71, 50], [6, 35], [44, 41], [68, 29], [60, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [73, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [61, 29, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1961, -14, 101]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -83, 101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![32, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![32, 1, 0]] 
 ![![89, 0, 0], ![32, 1, 0], ![22, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![32, 1, 0], ![0, 32, 2], ![170, 0, 32]]]
  hmulB := by decide  
  f := ![![![1089, 34, 0], ![-3026, 0, 0]], ![![352, 11, 0], ![-978, 0, 0]], ![![262, -8, -1], ![-728, 45, 0]]]
  g := ![![![1, 0, 0], ![-32, 89, 0], ![-22, 0, 89]], ![![0, 1, 0], ![-12, 32, 2], ![-6, 0, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-22, -16, 1]] ![![89, 0, 0], ![32, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2848, 89, 0]], ![![-1958, -1424, 89], ![-534, -534, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![32, 1, 0]]], ![![![-22, -16, 1]], ![![-6, -6, 0]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [85, 78, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 54, 10], [51, 42, 87], [0, 1]]
 g := ![![[93, 3, 61], [71, 16], [32, 3], [82, 48], [44, 9], [1]], ![[16, 91, 75, 77], [67, 50], [64, 25], [80, 1], [74, 43], [83, 9, 91, 30]], ![[59, 28, 63, 23], [82, 88], [49, 25], [30, 66], [37, 8], [13, 19, 94, 67]]]
 h' := ![![[49, 54, 10], [26, 58, 62], [85, 82, 93], [63, 91, 87], [90, 42, 57], [12, 19, 3], [0, 1]], ![[51, 42, 87], [94, 96, 80], [39, 68, 70], [85, 28, 5], [17, 87, 1], [14, 28, 25], [49, 54, 10]], ![[0, 1], [39, 40, 52], [92, 44, 31], [38, 75, 5], [58, 65, 39], [14, 50, 69], [51, 42, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 63], []]
 b := ![[], [87, 31, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [85, 78, 94, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-488492, 72944, 3977]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5036, 752, 41]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![8, -2, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![8, -2, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![8, 99, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![8, -2, 1], ![170, 8, -4], ![-340, 85, 8]]]
  hmulB := by decide  
  f := ![![![-7, 2, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -99, 101]], ![![0, -1, 1], ![2, 4, -4], ![-4, -7, 8]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [11, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [4, 100], [0, 1]]
 g := ![![[18, 17], [33], [28, 19], [56], [25], [4, 1]], ![[86, 84], [33], [3, 82], [56], [25], [8, 100]]]
 h' := ![![[4, 100], [66, 44], [96, 29], [96, 25], [45, 64], [57, 5], [0, 1]], ![[0, 1], [40, 57], [10, 72], [95, 76], [99, 37], [77, 96], [4, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [72, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [11, 97, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![351, -12, -95]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 93, -95]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![4, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![4, 1, 0]] 
 ![![101, 0, 0], ![4, 1, 0], ![93, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![4, 1, 0], ![0, 4, 2], ![170, 0, 4]]]
  hmulB := by decide  
  f := ![![![281, 70, 0], ![-7070, 0, 0]], ![![4, 1, 0], ![-100, 0, 0]], ![![257, 62, -1], ![-6466, 51, 0]]]
  g := ![![![1, 0, 0], ![-4, 101, 0], ![-93, 0, 101]], ![![0, 1, 0], ![-2, 4, 2], ![-2, 0, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![8, -2, 1]] ![![101, 0, 0], ![4, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![404, 101, 0]], ![![808, -202, 101], ![202, 0, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![4, 1, 0]]], ![![![8, -2, 1]], ![![2, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![17, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![17, 1, 0]] 
 ![![103, 0, 0], ![17, 1, 0], ![10, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![17, 1, 0], ![0, 17, 2], ![170, 0, 17]]]
  hmulB := by decide  
  f := ![![![1140, 67, 0], ![-6901, 0, 0]], ![![170, 10, 0], ![-1029, 0, 0]], ![![78, -4, -1], ![-472, 52, 0]]]
  g := ![![![1, 0, 0], ![-17, 103, 0], ![-10, 0, 103]], ![![0, 1, 0], ![-3, 17, 2], ![0, 0, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![25, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![25, 1, 0]] 
 ![![103, 0, 0], ![25, 1, 0], ![48, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![25, 1, 0], ![0, 25, 2], ![170, 0, 25]]]
  hmulB := by decide  
  f := ![![![676, 27, 0], ![-2781, 0, 0]], ![![150, 6, 0], ![-617, 0, 0]], ![![316, 0, -1], ![-1300, 52, 0]]]
  g := ![![![1, 0, 0], ![-25, 103, 0], ![-48, 0, 103]], ![![0, 1, 0], ![-7, 25, 2], ![-10, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-42, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-42, 1, 0]] 
 ![![103, 0, 0], ![61, 1, 0], ![45, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-42, 1, 0], ![0, -42, 2], ![170, 0, -42]]]
  hmulB := by decide  
  f := ![![![1723, -41, 0], ![4223, 0, 0]], ![![1093, -26, 0], ![2679, 0, 0]], ![![765, 3, -1], ![1875, 52, 0]]]
  g := ![![![1, 0, 0], ![-61, 103, 0], ![-45, 0, 103]], ![![-1, 1, 0], ![24, -42, 2], ![20, 0, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![17, 1, 0]] ![![103, 0, 0], ![25, 1, 0]]
  ![![103, 0, 0], ![-45, 21, 1]] where
 M := ![![![10609, 0, 0], ![2575, 103, 0]], ![![1751, 103, 0], ![425, 42, 2]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-45, 21, 1]] ![![103, 0, 0], ![-42, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4326, 103, 0]], ![![-4635, 2163, 103], ![2060, -927, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-42, 1, 0]]], ![![![-45, 21, 1]], ![![20, -9, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-27, -19, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-27, -19, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![80, 88, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-27, -19, 1], ![170, -27, -38], ![-3230, 85, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-80, -88, 107]], ![![-1, -1, 1], ![30, 31, -38], ![-10, 23, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [48, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 106], [0, 1]]
 g := ![![[49, 29], [20, 89], [12], [59, 11], [10], [2, 1]], ![[0, 78], [91, 18], [12], [81, 96], [10], [4, 106]]]
 h' := ![![[2, 106], [3, 52], [105, 93], [57, 71], [69, 15], [11, 63], [0, 1]], ![[0, 1], [0, 55], [77, 14], [92, 36], [99, 92], [30, 44], [2, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41]]
 b := ![[], [33, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [48, 105, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6614, 2118, 829]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-558, -662, 829]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![38, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![38, 1, 0]] 
 ![![107, 0, 0], ![38, 1, 0], ![27, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![38, 1, 0], ![0, 38, 2], ![170, 0, 38]]]
  hmulB := by decide  
  f := ![![![951, 25, 0], ![-2675, 0, 0]], ![![342, 9, 0], ![-962, 0, 0]], ![![235, -13, -1], ![-661, 54, 0]]]
  g := ![![![1, 0, 0], ![-38, 107, 0], ![-27, 0, 107]], ![![0, 1, 0], ![-14, 38, 2], ![-8, 0, 38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-27, -19, 1]] ![![107, 0, 0], ![38, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4066, 107, 0]], ![![-2889, -2033, 107], ![-856, -749, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![38, 1, 0]]], ![![![-27, -19, 1]], ![![-8, -7, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [43, 7, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 81, 89], [23, 27, 20], [0, 1]]
 g := ![![[102, 55, 35], [77, 21], [103, 61, 7], [102, 78, 34], [15, 9], [1]], ![[99, 53, 20, 15], [19, 88], [31, 22, 40, 108], [50, 30, 52, 63], [60, 102], [7, 20, 101, 66]], ![[56, 36, 64, 100], [48, 78], [63, 45, 35, 80], [45, 5, 96, 108], [67, 84], [23, 59, 7, 43]]]
 h' := ![![[83, 81, 89], [33, 66, 97], [40, 57, 28], [83, 99, 94], [5, 1, 90], [66, 102, 106], [0, 1]], ![[23, 27, 20], [46, 74, 100], [10, 96, 52], [79, 12, 13], [37, 54, 12], [108, 77, 59], [83, 81, 89]], ![[0, 1], [100, 78, 21], [86, 65, 29], [83, 107, 2], [65, 54, 7], [60, 39, 53], [23, 27, 20]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27, 108], []]
 b := ![[], [53, 1, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [43, 7, 3, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5232, -4578, 1526]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-48, -42, 14]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-111, 2, 4]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-111, 2, 4]] 
 ![![113, 0, 0], ![0, 113, 0], ![57, 57, 1]] where
  M :=![![![-111, 2, 4], ![680, -111, 4], ![340, 340, -111]]]
  hmulB := by decide  
  f := ![![![97, 14, 4]], ![![680, 97, 28]], ![![413, 59, 17]]]
  g := ![![![-3, -2, 4], ![4, -3, 4], ![59, 59, -111]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [20, 100, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 112], [0, 1]]
 g := ![![[5, 111], [88], [9], [87], [49, 53], [13, 1]], ![[92, 2], [88], [9], [87], [60, 60], [26, 112]]]
 h' := ![![[13, 112], [32, 87], [53, 38], [81, 3], [37, 55], [79, 36], [0, 1]], ![[0, 1], [33, 26], [95, 75], [7, 110], [74, 58], [95, 77], [13, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [23, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [20, 100, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6576, -700, 408]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-264, -212, 408]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 14, 4]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![97, 14, 4]] 
 ![![113, 0, 0], ![112, 1, 0], ![56, 0, 1]] where
  M :=![![![97, 14, 4], ![680, 97, 28], ![2380, 340, 97]]]
  hmulB := by decide  
  f := ![![![-111, 2, 4]], ![![-104, 1, 4]], ![![-52, 4, 1]]]
  g := ![![![-15, 14, 4], ![-104, 97, 28], ![-364, 340, 97]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-111, 2, 4]] ![![97, 14, 4]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [50, 1, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 67, 74], [54, 59, 53], [0, 1]]
 g := ![![[13, 44, 52], [18, 39, 124], [82, 33, 68], [59, 30, 47], [56, 59, 124], [1]], ![[24, 120, 80, 41], [95, 30, 111, 19], [51, 101, 107, 73], [66, 61, 43, 103], [109, 22, 26, 38], [90, 64, 77, 94]], ![[14, 39, 90, 51], [114, 89, 105, 56], [50, 70, 19, 93], [75, 4, 96, 29], [126, 88, 55, 118], [80, 65, 5, 33]]]
 h' := ![![[112, 67, 74], [116, 90, 68], [91, 125, 88], [98, 1, 24], [121, 2, 89], [77, 126, 39], [0, 1]], ![[54, 59, 53], [79, 13, 4], [87, 28, 91], [16, 65, 93], [123, 116, 65], [126, 25, 68], [112, 67, 74]], ![[0, 1], [21, 24, 55], [85, 101, 75], [99, 61, 10], [6, 9, 100], [48, 103, 20], [54, 59, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 117], []]
 b := ![[], [5, 67, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [50, 1, 88, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11938, 8509, 2540]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, 67, 20]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-21, -29, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-21, -29, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![110, 102, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-21, -29, 1], ![170, -21, -58], ![-4930, 85, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-110, -102, 131]], ![![-1, -1, 1], ![50, 45, -58], ![-20, 17, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [16, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 130], [0, 1]]
 g := ![![[73, 41], [80, 65], [60], [75], [45], [121], [1]], ![[0, 90], [9, 66], [60], [75], [45], [121], [1]]]
 h' := ![![[11, 130], [30, 33], [18, 117], [42, 45], [71, 72], [23, 62], [115, 11], [0, 1]], ![[0, 1], [0, 98], [126, 14], [13, 86], [77, 59], [50, 69], [105, 120], [11, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [122, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [16, 120, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1497, -403, -90]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![87, 67, -90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![58, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![58, 1, 0]] 
 ![![131, 0, 0], ![58, 1, 0], ![21, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![58, 1, 0], ![0, 58, 2], ![170, 0, 58]]]
  hmulB := by decide  
  f := ![![![2263, 39, 0], ![-5109, 0, 0]], ![![986, 17, 0], ![-2226, 0, 0]], ![![361, -23, -1], ![-815, 66, 0]]]
  g := ![![![1, 0, 0], ![-58, 131, 0], ![-21, 0, 131]], ![![0, 1, 0], ![-26, 58, 2], ![-8, 0, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-21, -29, 1]] ![![131, 0, 0], ![58, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![7598, 131, 0]], ![![-2751, -3799, 131], ![-1048, -1703, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![58, 1, 0]]], ![![![-21, -29, 1]], ![![-8, -13, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-38, 23, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-38, 23, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![99, 23, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-38, 23, 1], ![170, -38, 46], ![3910, 85, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -23, 137]], ![![-1, 0, 1], ![-32, -8, 46], ![56, 7, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [18, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 136], [0, 1]]
 g := ![![[5, 99], [14], [11], [63, 63], [109], [17], [1]], ![[0, 38], [14], [11], [10, 74], [109], [17], [1]]]
 h' := ![![[47, 136], [54, 28], [13, 39], [99, 82], [6, 101], [18, 66], [119, 47], [0, 1]], ![[0, 1], [0, 109], [65, 98], [117, 55], [95, 36], [106, 71], [136, 90], [47, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [39, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [18, 90, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-583, 169, -82]
  a := ![-3, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55, 15, -82]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-46, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-46, 1, 0]] 
 ![![137, 0, 0], ![91, 1, 0], ![38, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-46, 1, 0], ![0, -46, 2], ![170, 0, -46]]]
  hmulB := by decide  
  f := ![![![231, -5, 0], ![685, 0, 0]], ![![185, -4, 0], ![549, 0, 0]], ![![146, 20, -1], ![434, 69, 0]]]
  g := ![![![1, 0, 0], ![-91, 137, 0], ![-38, 0, 137]], ![![-1, 1, 0], ![30, -46, 2], ![14, 0, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-38, 23, 1]] ![![137, 0, 0], ![-46, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6302, 137, 0]], ![![-5206, 3151, 137], ![1918, -1096, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-46, 1, 0]]], ![![![-38, 23, 1]], ![![14, -8, 0]]]]
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


lemma PB250I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB250I2 : PrimesBelowBoundCertificateInterval O 79 137 250 where
  m := 11
  g := ![2, 2, 1, 2, 3, 2, 1, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB250I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
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
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![1295029]
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
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I101N1, I103N0, I103N1, I103N2, I107N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N1], [], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
