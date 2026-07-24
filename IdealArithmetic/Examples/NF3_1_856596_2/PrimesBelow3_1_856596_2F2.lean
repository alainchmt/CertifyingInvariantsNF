
import IdealArithmetic.Examples.NF3_1_856596_2.RI3_1_856596_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-18, 23, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-18, 23, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![65, 23, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-18, 23, 1], ![315, 54, 273], ![3984, 83, -83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -23, 83]], ![![-1, 0, 1], ![-210, -75, 273], ![113, 24, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [27, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 82], [0, 1]]
 g := ![![[0, 40], [], [], [75], [], [1]], ![[0, 43], [], [], [75], [], [1]]]
 h' := ![![[0, 82], [0, 17], [10], [50], [0, 65], [56], [0, 1]], ![[0, 1], [0, 66], [10], [50], [0, 18], [56], [0, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [0, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [27, 0, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1176, 600, 156]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-108, -36, 156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-24, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-24, 1, 0]] 
 ![![83, 0, 0], ![59, 1, 0], ![0, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-24, 1, 0], ![6, -21, 12], ![177, 3, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![18, 1, -1], ![64, 7, 0]]]
  g := ![![![1, 0, 0], ![-59, 83, 0], ![0, 0, 83]], ![![-1, 1, 0], ![15, -21, 12], ![0, 3, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-18, 23, 1]] ![![83, 0, 0], ![-24, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1992, 83, 0]], ![![-1494, 1909, 83], ![747, -498, 249]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-24, 1, 0]]], ![![![-18, 23, 1]], ![![9, -6, 3]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-38, 12, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-38, 12, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![51, 12, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-38, 12, 1], ![249, 1, 141], ![2037, 50, -70]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -12, 89]], ![![-1, 0, 1], ![-78, -19, 141], ![63, 10, -70]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [31, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 88], [0, 1]]
 g := ![![[42, 10], [55], [8], [88, 22], [71, 21], [1]], ![[16, 79], [55], [8], [13, 67], [52, 68], [1]]]
 h' := ![![[33, 88], [76, 59], [1, 12], [31, 39], [24, 72], [58, 33], [0, 1]], ![[0, 1], [65, 30], [41, 77], [72, 50], [86, 17], [79, 56], [33, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [4, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [31, 56, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2028, 350, 400]
  a := ![2, 0, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-252, -50, 400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![37, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![37, 1, 0]] 
 ![![89, 0, 0], ![37, 1, 0], ![70, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![37, 1, 0], ![6, 40, 12], ![177, 3, 34]]]
  hmulB := by decide  
  f := ![![![11807, 95412, 28644], ![6052, -212443, 0]], ![![4916, 39652, 11904], ![2493, -88288, 0]], ![![9281, 75043, 22529], ![4773, -167090, 0]]]
  g := ![![![1, 0, 0], ![-37, 89, 0], ![-70, 0, 89]], ![![0, 1, 0], ![-26, 40, 12], ![-26, 3, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-38, 12, 1]] ![![89, 0, 0], ![37, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3293, 89, 0]], ![![-3382, 1068, 89], ![-1157, 445, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![37, 1, 0]]], ![![![-38, 12, 1]], ![![-13, 5, 2]]]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [77, 10, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 81, 50], [2, 15, 47], [0, 1]]
 g := ![![[63, 6, 70], [41, 47], [26, 81], [17, 2], [78, 1], [1]], ![[11, 40, 29, 94], [24, 96], [90, 49], [30, 96], [], [48, 49, 53, 64]], ![[63, 38, 29, 93], [93, 89], [94, 4], [21, 35], [12, 1], [88, 42, 13, 33]]]
 h' := ![![[96, 81, 50], [94, 80, 19], [70, 73, 85], [61, 30, 88], [20, 4, 14], [20, 87, 1], [0, 1]], ![[2, 15, 47], [11, 0, 17], [4, 81, 75], [12, 93, 7], [24, 47, 22], [86, 64], [96, 81, 50]], ![[0, 1], [90, 17, 61], [49, 40, 34], [20, 71, 2], [45, 46, 61], [22, 43, 96], [2, 15, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 6], []]
 b := ![[], [84, 10, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [77, 10, 96, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20947507930, -1092582392, -450806530]
  a := ![-129, -64, -194]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-215953690, -11263736, -4647490]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-31, 11, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-31, 11, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![70, 11, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-31, 11, 1], ![243, 5, 129], ![1860, 47, -60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -11, 101]], ![![-1, 0, 1], ![-87, -14, 129], ![60, 7, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [35, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 100], [0, 1]]
 g := ![![[7, 76], [80], [79, 78], [4], [16], [58, 1]], ![[72, 25], [80], [58, 23], [4], [16], [15, 100]]]
 h' := ![![[58, 100], [58, 50], [63, 79], [67, 52], [45, 99], [91, 97], [0, 1]], ![[0, 1], [29, 51], [100, 22], [53, 49], [30, 2], [61, 4], [58, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [18, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [35, 43, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1864, 694, -93]
  a := ![-3, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 17, -93]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-28, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-28, 1, 0]] 
 ![![101, 0, 0], ![73, 1, 0], ![60, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-28, 1, 0], ![6, -25, 12], ![177, 3, -31]]]
  hmulB := by decide  
  f := ![![![4093, -18438, 8856], ![-1212, -74538, 0]], ![![2947, -13316, 6396], ![-908, -53833, 0]], ![![2424, -10953, 5261], ![-747, -44280, 0]]]
  g := ![![![1, 0, 0], ![-73, 101, 0], ![-60, 0, 101]], ![![-1, 1, 0], ![11, -25, 12], ![18, 3, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-31, 11, 1]] ![![101, 0, 0], ![-28, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2828, 101, 0]], ![![-3131, 1111, 101], ![1111, -303, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-28, 1, 0]]], ![![![-31, 11, 1]], ![![11, -3, 1]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [19, 61, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 79, 70], [91, 23, 33], [0, 1]]
 g := ![![[40, 75, 92], [36, 102, 79], [97, 4, 17], [69, 97], [55, 26], [1]], ![[73, 55, 29, 99], [102, 91, 91, 70], [10, 100, 97, 27], [62, 92], [67, 50], [67, 34, 83, 10]], ![[93, 85, 3, 81], [8, 33, 46, 64], [67, 42, 84, 83], [44, 9], [14, 92], [14, 51, 49, 93]]]
 h' := ![![[64, 79, 70], [37, 4, 68], [11, 49, 39], [58, 31, 29], [37, 14, 32], [84, 42, 52], [0, 1]], ![[91, 23, 33], [78, 26, 93], [17, 30, 1], [13, 26, 56], [26, 91, 68], [75, 85, 16], [64, 79, 70]], ![[0, 1], [62, 73, 45], [45, 24, 63], [64, 46, 18], [73, 101, 3], [66, 79, 35], [91, 23, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 6], []]
 b := ![[], [56, 102, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [19, 61, 51, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-563204, -2060, -6180]
  a := ![-3, -2, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5468, -20, -60]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![27, 21, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![27, 21, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![27, 21, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![27, 21, 1], ![303, 93, 249], ![3630, 77, -32]]]
  hmulB := by decide  
  f := ![![![-26, -21, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-27, -21, 107]], ![![0, 0, 1], ![-60, -48, 249], ![42, 7, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [87, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [103, 106], [0, 1]]
 g := ![![[64, 16], [65, 25], [30], [106, 44], [12], [103, 1]], ![[0, 91], [72, 82], [30], [37, 63], [12], [99, 106]]]
 h' := ![![[103, 106], [16, 4], [37, 102], [87, 64], [6, 77], [27, 36], [0, 1]], ![[0, 1], [0, 103], [57, 5], [45, 43], [19, 30], [97, 71], [103, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [49, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [87, 4, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![161709, 36393, 9972]
  a := ![23, 21, 45]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1005, -1617, 9972]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-35, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-35, 1, 0]] 
 ![![107, 0, 0], ![72, 1, 0], ![32, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-35, 1, 0], ![6, -32, 12], ![177, 3, -38]]]
  hmulB := by decide  
  f := ![![![17596, -105537, 39600], ![-6741, -353100, 0]], ![![11851, -70998, 26640], ![-4493, -237540, 0]], ![![5281, -31563, 11843], ![-1959, -105600, 0]]]
  g := ![![![1, 0, 0], ![-72, 107, 0], ![-32, 0, 107]], ![![-1, 1, 0], ![18, -32, 12], ![11, 3, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![27, 21, 1]] ![![107, 0, 0], ![-35, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3745, 107, 0]], ![![2889, 2247, 107], ![-642, -642, 214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-35, 1, 0]]], ![![![27, 21, 1]], ![![-6, -6, 2]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-52, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-52, 1, 0]] 
 ![![109, 0, 0], ![57, 1, 0], ![97, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-52, 1, 0], ![6, -49, 12], ![177, 3, -55]]]
  hmulB := by decide  
  f := ![![![8113, -84042, 20592], ![-4578, -187044, 0]], ![![4239, -43931, 10764], ![-2397, -97773, 0]], ![![7237, -74790, 18325], ![-4038, -166452, 0]]]
  g := ![![![1, 0, 0], ![-57, 109, 0], ![-97, 0, 109]], ![![-1, 1, 0], ![15, -49, 12], ![49, 3, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-32, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-32, 1, 0]] 
 ![![109, 0, 0], ![77, 1, 0], ![14, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-32, 1, 0], ![6, -29, 12], ![177, 3, -35]]]
  hmulB := by decide  
  f := ![![![9649, -51242, 21216], ![-3270, -192712, 0]], ![![6817, -36171, 14976], ![-2288, -136032, 0]], ![![1254, -6582, 2725], ![-370, -24752, 0]]]
  g := ![![![1, 0, 0], ![-77, 109, 0], ![-14, 0, 109]], ![![-1, 1, 0], ![19, -29, 12], ![4, 3, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-25, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-25, 1, 0]] 
 ![![109, 0, 0], ![84, 1, 0], ![100, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-25, 1, 0], ![6, -22, 12], ![177, 3, -28]]]
  hmulB := by decide  
  f := ![![![8651, -33530, 18300], ![-2180, -166225, 0]], ![![6651, -25834, 14100], ![-1743, -128075, 0]], ![![7925, -30761, 16789], ![-2051, -152500, 0]]]
  g := ![![![1, 0, 0], ![-84, 109, 0], ![-100, 0, 109]], ![![-1, 1, 0], ![6, -22, 12], ![25, 3, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-52, 1, 0]] ![![109, 0, 0], ![-32, 1, 0]]
  ![![109, 0, 0], ![12, -34, 1]] where
 M := ![![![11881, 0, 0], ![-3488, 109, 0]], ![![-5668, 109, 0], ![1670, -81, 12]]]
 hmul := by decide  
 g := ![![![![97, 34, -1], ![109, 0, 0]], ![![-32, 1, 0], ![0, 0, 0]]], ![![![-52, 1, 0], ![0, 0, 0]], ![![14, 3, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![12, -34, 1]] ![![109, 0, 0], ![-25, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-2725, 109, 0]], ![![1308, -3706, 109], ![-327, 763, -436]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-25, 1, 0]]], ![![![12, -34, 1]], ![![-3, 7, -4]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [65, 52, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 34, 66], [18, 78, 47], [0, 1]]
 g := ![![[103, 42, 72], [32, 62], [13, 32], [88, 112], [99, 40, 100], [1]], ![[3, 20, 20, 17], [110, 14], [5, 31], [68, 13], [109, 18, 5, 33], [103, 2, 95, 24]], ![[38, 62, 80, 48], [6, 9], [12, 26], [15, 32], [71, 12, 56, 20], [77, 9, 58, 89]]]
 h' := ![![[85, 34, 66], [60, 104, 33], [85, 70, 66], [79, 108, 91], [6, 93, 15], [48, 61, 103], [0, 1]], ![[18, 78, 47], [20, 59, 59], [27, 59, 50], [37, 1, 101], [84, 92, 76], [55, 15, 82], [85, 34, 66]], ![[0, 1], [58, 63, 21], [83, 97, 110], [33, 4, 34], [68, 41, 22], [36, 37, 41], [18, 78, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 49], []]
 b := ![[], [83, 52, 90], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [65, 52, 10, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![904, -565, 565]
  a := ![-1, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -5, 5]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [73, 5, 42, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 22, 11], [84, 104, 116], [0, 1]]
 g := ![![[40, 52, 84], [106, 86, 64], [57, 119, 37], [55, 10, 113], [86, 119, 113], [1]], ![[100, 54, 12, 15], [62, 112, 34, 94], [8, 10, 22, 47], [71, 36, 124, 120], [29, 116, 49, 117], [62, 58, 90, 61]], ![[104, 103, 20, 53], [60, 58, 114, 97], [26, 39, 62, 112], [20, 54, 98, 23], [107, 35, 3, 45], [52, 108, 55, 66]]]
 h' := ![![[1, 22, 11], [9, 61, 46], [30, 33, 119], [49, 115, 52], [72, 22, 85], [54, 122, 85], [0, 1]], ![[84, 104, 116], [48, 30, 121], [111, 21, 39], [106, 64, 69], [92, 53, 65], [47, 94, 22], [1, 22, 11]], ![[0, 1], [114, 36, 87], [25, 73, 96], [10, 75, 6], [9, 52, 104], [9, 38, 20], [84, 104, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 94], []]
 b := ![[], [39, 86, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [73, 5, 42, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2875915, 210566, 63246]
  a := ![5, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22645, 1658, 498]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [50, 102, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 6, 2], [126, 124, 129], [0, 1]]
 g := ![![[55, 24, 94], [110, 63, 107], [120, 11], [96, 75], [16, 60], [127, 1], []], ![[77, 99, 16, 31], [30, 40, 29, 86], [3, 45], [54, 28], [30, 64], [105, 49], [8, 4]], ![[77, 86, 44, 27], [1, 62, 2, 77], [68, 99], [113, 107], [16, 58], [114, 36], [12, 4]]]
 h' := ![![[1, 6, 2], [2, 74, 116], [54, 22, 32], [91, 56, 81], [31, 101, 72], [69, 96, 45], [0, 0, 1], [0, 1]], ![[126, 124, 129], [35, 46, 122], [15, 99, 82], [54, 101, 69], [93, 106, 91], [26, 67, 8], [125, 44, 124], [1, 6, 2]], ![[0, 1], [4, 11, 24], [15, 10, 17], [3, 105, 112], [46, 55, 99], [45, 99, 78], [80, 87, 6], [126, 124, 129]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 112], []]
 b := ![[], [59, 24, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [50, 102, 4, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9739195, -522035, -220080]
  a := ![-10, -5, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-74345, -3985, -1680]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![62688196, -2747404, -1853633]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![62688196, -2747404, -1853633]] 
 ![![137, 0, 0], ![65, 1, 0], ![66, 0, 1]] where
  M :=![![![62688196, -2747404, -1853633], ![-344577465, 48885085, -27407949], ![-325024437, -34193074, 63515876]]]
  hmulB := by decide  
  f := ![![![2167816968764234, 237885182123746, 165915715478201]], ![![1253302888336199, 137531069340245, 95922602519222]], ![![1246327955676927, 136765675790024, 95388770115818]]]
  g := ![![![2654082, -2747404, -1853633], ![-12504988, 48885085, -27407949], ![-16748339, -34193074, 63515876]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4137463, 77070, 238370]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![-4137463, 77070, 238370]] 
 ![![137, 0, 0], ![73, 1, 0], ![109, 0, 1]] where
  M :=![![![-4137463, 77070, 238370], ![42653910, -3191143, 209730], ![-7096800, 3568390, -3415193]]]
  hmulB := by decide  
  f := ![![![-10149970800899, -1113806048810, -776836648010]], ![![-6460808696761, -708976207697, -494483488660]], ![![-9021209485843, -989941536780, -690445940727]]]
  g := ![![![-260919, 77070, 238370], ![1844867, -3191143, 209730], ![763991, 3568390, -3415193]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![567869448733935100121565758, 62315098175281040116319452, 43462371243736386940793397]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![567869448733935100121565758, 62315098175281040116319452, 43462371243736386940793397]] 
 ![![137, 0, 0], ![136, 1, 0], ![92, 0, 1]] where
  M :=![![![567869448733935100121565758, 62315098175281040116319452, 43462371243736386940793397], ![8066730299193026729218347981, 885201856990987381292904305, 617394064372163320573453233], ![7248546078819678436739517465, 795418491938152537520065914, 554773639183037527535780990]]]
  hmulB := by decide  
  f := ![![![363402751761988, -6984252847622, -20697286685769]], ![![333704007147179, -4886863168721, -20704745718093]], ![![248156966056465, -6958146234488, -11697693514810]]]
  g := ![![![-86901620857868860979933374, 62315098175281040116319452, 43462371243736386940793397], ![-1234459680100877975323900255, 885201856990987381292904305, 617394064372163320573453233], ![-1109252143281814008753878087, 795418491938152537520065914, 554773639183037527535780990]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![62688196, -2747404, -1853633]] ![![-4137463, 77070, 238370]]
  ![![-363402751761988, 6984252847622, 20697286685769]] where
 M := ![![![-363402751761988, 6984252847622, 20697286685769]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![-363402751761988, 6984252847622, 20697286685769]] ![![567869448733935100121565758, 62315098175281040116319452, 43462371243736386940793397]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB262I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB262I2 : PrimesBelowBoundCertificateInterval O 79 137 262 where
  m := 11
  g := ![2, 2, 1, 2, 1, 2, 3, 1, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB262I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![2048383]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N1, I101N1, I107N1, I109N0, I109N1, I109N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [], [I101N1], [], [I107N1], [I109N0, I109N1, I109N2], [], [], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
