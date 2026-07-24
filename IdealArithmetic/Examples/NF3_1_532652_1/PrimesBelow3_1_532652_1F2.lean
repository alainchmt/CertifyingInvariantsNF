
import IdealArithmetic.Examples.NF3_1_532652_1.RI3_1_532652_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-238263, -88187, -9318]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-238263, -88187, -9318]] 
 ![![83, 0, 0], ![0, 83, 0], ![59, 66, 1]] where
  M :=![![![-238263, -88187, -9318], ![-2254956, -834615, -88187], ![-21341254, -7898924, -834615]]]
  hmulB := by decide  
  f := ![![![2561, 231, -53]], ![![-12826, -831, 231]], ![![-7705, -473, 136]]]
  g := ![![![3753, 6347, -9318], ![35519, 60069, -88187], ![336157, 568502, -834615]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [61, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 82], [0, 1]]
 g := ![![[82, 49], [7, 29], [4], [25], [4, 69], [1]], ![[0, 34], [33, 54], [4], [25], [63, 14], [1]]]
 h' := ![![[61, 82], [71, 7], [41, 19], [77, 81], [5, 5], [22, 61], [0, 1]], ![[0, 1], [0, 76], [38, 64], [38, 2], [61, 78], [8, 22], [61, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [67, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [61, 22, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![545, 348, 43]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-24, -30, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2561, 231, -53]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![2561, 231, -53]] 
 ![![83, 0, 0], ![17, 1, 0], ![43, 0, 1]] where
  M :=![![![2561, 231, -53], ![-12826, -831, 231], ![55902, 1958, -831]]]
  hmulB := by decide  
  f := ![![![-238263, -88187, -9318]], ![![-75969, -28118, -2971]], ![![-380561, -140855, -14883]]]
  g := ![![![11, 231, -53], ![-104, -831, 231], ![703, 1958, -831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-238263, -88187, -9318]] ![![2561, 231, -53]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 9, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![17, 9, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![17, 9, 1]] where
  M :=![![![17, 9, 1], ![242, 81, 9], ![2178, 818, 81]]]
  hmulB := by decide  
  f := ![![![-9, 1, 0]], ![![0, -9, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 9], ![9, 1, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [47, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 88], [0, 1]]
 g := ![![[44, 36], [47], [18], [9, 10], [11, 85], [1]], ![[0, 53], [47], [18], [66, 79], [6, 4], [1]]]
 h' := ![![[68, 88], [52, 83], [83, 74], [22, 75], [17, 30], [42, 68], [0, 1]], ![[0, 1], [0, 6], [42, 15], [49, 14], [10, 59], [38, 21], [68, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [46, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [47, 21, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2877, 1372, 637]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-154, -49, 637]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![-9, 1, 0]] 
 ![![89, 0, 0], ![80, 1, 0], ![8, 0, 1]] where
  M :=![![![-9, 1, 0], ![0, -9, 1], ![242, 64, -9]]]
  hmulB := by decide  
  f := ![![![17, 9, 1]], ![![18, 9, 1]], ![![26, 10, 1]]]
  g := ![![![-1, 1, 0], ![8, -9, 1], ![-54, 64, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![17, 9, 1]] ![![-9, 1, 0]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [75, 62, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [0, 3, 73], [68, 93, 24], [0, 1]]
 g := ![![[0, 92, 64], [72, 43], [85, 27], [49, 86], [62, 65], [1]], ![[56, 19, 18, 96], [18, 66], [22, 53], [60, 88], [96, 85], [4, 89, 38, 47]], ![[23, 66, 58, 64], [70, 22], [23, 81], [56, 49], [36, 44], [58, 27, 77, 50]]]
 h' := ![![[0, 3, 73], [93, 48, 89], [62, 71, 25], [36, 8, 30], [5, 96, 38], [22, 35, 68], [0, 1]], ![[68, 93, 24], [51, 75, 44], [72, 77, 39], [48, 16, 76], [59, 58, 66], [88, 61, 52], [0, 3, 73]], ![[0, 1], [88, 71, 61], [10, 46, 33], [59, 73, 88], [66, 40, 90], [70, 1, 74], [68, 93, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 35], []]
 b := ![[], [91, 76, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [75, 62, 29, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-80219, -29294, -22795]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-827, -302, -235]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![28, 1, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![28, 1, 0]] 
 ![![101, 0, 0], ![28, 1, 0], ![24, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![28, 1, 0], ![0, 28, 1], ![242, 64, 28]]]
  hmulB := by decide  
  f := ![![![1317, 47, 0], ![-4747, 0, 0]], ![![364, 13, 0], ![-1312, 0, 0]], ![![288, 10, 0], ![-1038, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 101, 0], ![-24, 0, 101]], ![![0, 1, 0], ![-8, 28, 1], ![-22, 64, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N0 : Nat.card (O ⧸ I101N0) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N0)

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := prime_ideal_of_norm_prime hp101.out _ NI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 19, 2]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![51, 19, 2]] 
 ![![101, 0, 0], ![34, 1, 0], ![56, 0, 1]] where
  M :=![![![51, 19, 2], ![484, 179, 19], ![4598, 1700, 179]]]
  hmulB := by decide  
  f := ![![![-259, -1, 3]], ![![-80, -1, 1]], ![![-146, 6, 1]]]
  g := ![![![-7, 19, 2], ![-66, 179, 19], ![-626, 1700, 179]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1

def I101N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![39, 1, 0]] i)))

def SI101N2: IdealEqSpanCertificate' Table ![![101, 0, 0], ![39, 1, 0]] 
 ![![101, 0, 0], ![39, 1, 0], ![95, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![39, 1, 0], ![0, 39, 1], ![242, 64, 39]]]
  hmulB := by decide  
  f := ![![![1366, 35, 0], ![-3535, 0, 0]], ![![468, 12, 0], ![-1211, 0, 0]], ![![1264, 32, 0], ![-3271, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 101, 0], ![-95, 0, 101]], ![![0, 1, 0], ![-16, 39, 1], ![-59, 64, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N2 : Nat.card (O ⧸ I101N2) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N2)

lemma isPrimeI101N2 : Ideal.IsPrime I101N2 := prime_ideal_of_norm_prime hp101.out _ NI101N2
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![28, 1, 0]] ![![51, 19, 2]]
  ![![101, 0, 0], ![-58, -39, 1]] where
 M := ![![![5151, 1919, 202]], ![![1912, 711, 75]]]
 hmul := by decide  
 g := ![![![![51, 19, 2], ![0, 0, 0]]], ![![![62, 36, 0], ![75, 0, 0]]]]
 hle2 := by decide  

def MulI101N1 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-58, -39, 1]] ![![101, 0, 0], ![39, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![3939, 101, 0]], ![![-5858, -3939, 101], ![-2020, -1515, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![39, 1, 0]]], ![![![-58, -39, 1]], ![![-20, -15, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [102, 0, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 16, 2], [37, 86, 101], [0, 1]]
 g := ![![[97, 69, 17], [87, 56, 92], [49, 3, 25], [65, 15], [24, 34], [1]], ![[57, 88, 88, 25], [49, 27, 44, 52], [56, 19, 43, 64], [28, 2], [33, 41], [54, 66, 28, 8]], ![[26, 36, 1, 45], [72, 80, 28, 3], [83, 100, 14, 39], [67, 46], [53, 52], [5, 45, 63, 95]]]
 h' := ![![[97, 16, 2], [87, 88, 29], [49, 37, 68], [72, 67, 5], [25, 34, 85], [1, 0, 31], [0, 1]], ![[37, 86, 101], [81, 76, 95], [21, 65, 51], [69, 29, 49], [12, 14, 65], [44, 43, 91], [97, 16, 2]], ![[0, 1], [99, 42, 82], [34, 1, 87], [56, 7, 49], [68, 55, 56], [85, 60, 84], [37, 86, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 99], []]
 b := ![[], [17, 26, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [102, 0, 72, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1271535, -593177, -61800]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12345, -5759, -600]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![18, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![18, 1, 0]] 
 ![![107, 0, 0], ![18, 1, 0], ![104, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![18, 1, 0], ![0, 18, 1], ![242, 64, 18]]]
  hmulB := by decide  
  f := ![![![73, 4, 0], ![-428, 0, 0]], ![![-18, -1, 0], ![108, 0, 0]], ![![76, 4, 0], ![-446, 1, 0]]]
  g := ![![![1, 0, 0], ![-18, 107, 0], ![-104, 0, 107]], ![![0, 1, 0], ![-4, 18, 1], ![-26, 64, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![75, 11, -2]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![75, 11, -2]] 
 ![![107, 0, 0], ![19, 1, 0], ![67, 0, 1]] where
  M :=![![![75, 11, -2], ![-484, -53, 11], ![2662, 220, -53]]]
  hmulB := by decide  
  f := ![![![-389, -143, -15]], ![![-103, -38, -4]], ![![-567, -209, -22]]]
  g := ![![![0, 11, -2], ![-2, -53, 11], ![19, 220, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-37, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-37, 1, 0]] 
 ![![107, 0, 0], ![70, 1, 0], ![22, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-37, 1, 0], ![0, -37, 1], ![242, 64, -37]]]
  hmulB := by decide  
  f := ![![![3516, -95, 0], ![10165, 0, 0]], ![![2258, -61, 0], ![6528, 0, 0]], ![![716, -19, 0], ![2070, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 107, 0], ![-22, 0, 107]], ![![-1, 1, 0], ![24, -37, 1], ![-32, 64, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![18, 1, 0]] ![![75, 11, -2]]
  ![![107, 0, 0], ![-86, 37, 1]] where
 M := ![![![8025, 1177, -214]], ![![866, 145, -25]]]
 hmul := by decide  
 g := ![![![![75, 11, -2], ![0, 0, 0]]], ![![![74, -27, -1], ![82, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-86, 37, 1]] ![![107, 0, 0], ![-37, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3959, 107, 0]], ![![-9202, 3959, 107], ![3424, -1391, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-37, 1, 0]]], ![![![-86, 37, 1]], ![![32, -13, 0]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [45, 36, 19, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 24, 79], [70, 84, 30], [0, 1]]
 g := ![![[48, 32, 81], [13, 27], [68, 16, 74], [9, 52, 82], [68, 34], [1]], ![[50, 86, 31, 39], [85, 38], [108, 92, 31, 99], [25, 34, 16, 58], [6, 78], [45, 89, 100, 32]], ![[67, 10, 104, 76], [52, 48], [6, 82, 31, 90], [57, 77, 41, 2], [28, 100], [57, 70, 34, 77]]]
 h' := ![![[20, 24, 79], [24, 57, 9], [101, 82, 71], [31, 34, 69], [55, 25, 54], [64, 73, 90], [0, 1]], ![[70, 84, 30], [94, 55, 27], [70, 15, 16], [65, 51, 89], [21, 25, 80], [89, 67, 29], [20, 24, 79]], ![[0, 1], [55, 106, 73], [18, 12, 22], [108, 24, 60], [69, 59, 84], [28, 78, 99], [70, 84, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56, 54], []]
 b := ![[], [43, 28, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [45, 36, 19, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-96029, -37060, -3815]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-881, -340, -35]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![32, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![32, 1, 0]] 
 ![![113, 0, 0], ![32, 1, 0], ![106, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![32, 1, 0], ![0, 32, 1], ![242, 64, 32]]]
  hmulB := by decide  
  f := ![![![1249, 39, 0], ![-4407, 0, 0]], ![![352, 11, 0], ![-1242, 0, 0]], ![![1162, 36, 0], ![-4100, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 113, 0], ![-106, 0, 113]], ![![0, 1, 0], ![-10, 32, 1], ![-46, 64, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![39, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![39, 1, 0]] 
 ![![113, 0, 0], ![39, 1, 0], ![61, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![39, 1, 0], ![0, 39, 1], ![242, 64, 39]]]
  hmulB := by decide  
  f := ![![![898, 23, 0], ![-2599, 0, 0]], ![![312, 8, 0], ![-903, 0, 0]], ![![482, 12, 0], ![-1395, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 113, 0], ![-61, 0, 113]], ![![0, 1, 0], ![-14, 39, 1], ![-41, 64, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![42, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![42, 1, 0]] 
 ![![113, 0, 0], ![42, 1, 0], ![44, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![42, 1, 0], ![0, 42, 1], ![242, 64, 42]]]
  hmulB := by decide  
  f := ![![![1135, 27, 0], ![-3051, 0, 0]], ![![378, 9, 0], ![-1016, 0, 0]], ![![436, 10, 0], ![-1172, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 113, 0], ![-44, 0, 113]], ![![0, 1, 0], ![-16, 42, 1], ![-38, 64, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![32, 1, 0]] ![![113, 0, 0], ![39, 1, 0]]
  ![![113, 0, 0], ![5, -42, 1]] where
 M := ![![![12769, 0, 0], ![4407, 113, 0]], ![![3616, 113, 0], ![1248, 71, 1]]]
 hmul := by decide  
 g := ![![![![108, 42, -1], ![113, 0, 0]], ![![34, 43, -1], ![113, 0, 0]]], ![![![27, 43, -1], ![113, 0, 0]], ![![11, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![5, -42, 1]] ![![113, 0, 0], ![42, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4746, 113, 0]], ![![565, -4746, 113], ![452, -1695, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![42, 1, 0]]], ![![![5, -42, 1]], ![![4, -15, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [42, 96, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [85, 34, 39], [46, 92, 88], [0, 1]]
 g := ![![[1, 22, 60], [56, 113, 11], [54, 96, 98], [115, 60, 9], [83, 58, 16], [1]], ![[34, 38, 19, 7], [10, 86, 65, 123], [69, 19, 33, 48], [95, 124, 65, 93], [35, 84, 17, 77], [24, 2, 115, 10]], ![[46, 53, 95, 17], [56, 87, 120, 94], [59, 81, 2, 19], [100, 62, 105, 68], [62, 14, 65, 35], [122, 53, 21, 117]]]
 h' := ![![[85, 34, 39], [61, 108, 106], [18, 71, 30], [123, 103, 112], [70, 123, 124], [85, 31, 4], [0, 1]], ![[46, 92, 88], [72, 93, 121], [29, 52, 68], [79, 111, 97], [53, 24, 76], [88, 121, 53], [85, 34, 39]], ![[0, 1], [114, 53, 27], [91, 4, 29], [44, 40, 45], [91, 107, 54], [10, 102, 70], [46, 92, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43, 69], []]
 b := ![[], [46, 22, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [42, 96, 123, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3760216, 1308989, 141097]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29608, 10307, 1111]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [45, 62, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 55, 48], [112, 75, 83], [0, 1]]
 g := ![![[84, 88, 44], [13, 120, 99], [128, 46], [38, 48], [78, 45], [0, 1], []], ![[26, 80, 32, 107], [5, 42, 127, 109], [7, 74], [14, 81], [58, 4], [115, 123], [40, 77]], ![[35, 90, 46, 2], [54, 79, 42, 18], [94, 64], [76, 114], [123, 63], [3, 12], [5, 77]]]
 h' := ![![[19, 55, 48], [70, 31, 31], [39, 79, 19], [67, 43, 35], [27, 82, 21], [0, 86, 69], [0, 0, 1], [0, 1]], ![[112, 75, 83], [66, 100, 14], [6, 6, 108], [37, 12, 104], [55, 59, 9], [69, 80, 2], [2, 75, 75], [19, 55, 48]], ![[0, 1], [29, 0, 86], [74, 46, 4], [80, 76, 123], [15, 121, 101], [21, 96, 60], [5, 56, 55], [112, 75, 83]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 31], []]
 b := ![[], [41, 18, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [45, 62, 0, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![91700, 1703, -3930]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![700, 13, -30]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![137, 0, 0], ![7, 1, 0], ![88, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 1], ![242, 64, 7]]]
  hmulB := by decide  
  f := ![![![-15, -7, 1]], ![![1, 0, 0]], ![![-22, -6, 1]]]
  g := ![![![0, 1, 0], ![-1, 7, 1], ![-6, 64, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![32, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![32, 1, 0]] 
 ![![137, 0, 0], ![32, 1, 0], ![72, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![32, 1, 0], ![0, 32, 1], ![242, 64, 32]]]
  hmulB := by decide  
  f := ![![![833, 26, 0], ![-3562, 0, 0]], ![![160, 5, 0], ![-684, 0, 0]], ![![456, 14, 0], ![-1950, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 137, 0], ![-72, 0, 137]], ![![0, 1, 0], ![-8, 32, 1], ![-30, 64, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-39, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-39, 1, 0]] 
 ![![137, 0, 0], ![98, 1, 0], ![123, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-39, 1, 0], ![0, -39, 1], ![242, 64, -39]]]
  hmulB := by decide  
  f := ![![![5227, -134, 0], ![18358, 0, 0]], ![![3784, -97, 0], ![13290, 0, 0]], ![![4731, -121, 0], ![16616, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 137, 0], ![-123, 0, 137]], ![![-1, 1, 0], ![27, -39, 1], ![-9, 64, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![7, 1, 0]] ![![137, 0, 0], ![32, 1, 0]]
  ![![137, 0, 0], ![-50, 39, 1]] where
 M := ![![![959, 137, 0], ![224, 39, 1]]]
 hmul := by decide  
 g := ![![![![7, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-50, 39, 1]] ![![137, 0, 0], ![-39, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-5343, 137, 0]], ![![-6850, 5343, 137], ![2192, -1507, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-39, 1, 0]]], ![![![-50, 39, 1]], ![![16, -11, 0]]]]
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


lemma PB207I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB207I2 : PrimesBelowBoundCertificateInterval O 79 137 207 where
  m := 11
  g := ![2, 2, 1, 3, 1, 3, 1, 3, 1, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB207I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1, I101N2]
    · exact ![I103N0]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![101, 101, 101]
    · exact ![1092727]
    · exact ![107, 107, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
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
      exact NI101N2
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
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
      exact NI113N1
      exact NI113N2
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
  β := ![I83N1, I89N1, I101N0, I101N1, I101N2, I107N0, I107N1, I107N2, I113N0, I113N1, I113N2, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [], [I101N0, I101N1, I101N2], [], [I107N0, I107N1, I107N2], [], [I113N0, I113N1, I113N2], [], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
