
import IdealArithmetic.Examples.NF3_3_582169_2.RI3_3_582169_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [46, 76, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 71, 44], [61, 11, 39], [0, 1]]
 g := ![![[7, 56, 48], [45, 37, 75], [19, 40], [9, 10], [68, 71, 1], []], ![[14, 74, 7, 64], [48, 34, 64, 7], [66, 49], [62, 77], [2, 30, 43, 12], [31, 27]], ![[71, 28, 0, 32], [37, 43, 51, 54], [25, 17], [61, 7], [68, 41, 49, 55], [36, 27]]]
 h' := ![![[10, 71, 44], [5, 45, 31], [42, 27, 65], [13, 22, 17], [26, 32, 50], [0, 0, 1], [0, 1]], ![[61, 11, 39], [19, 2, 80], [27, 36, 77], [18, 60, 76], [31, 27, 49], [2, 63, 11], [10, 71, 44]], ![[0, 1], [33, 36, 55], [43, 20, 24], [23, 1, 73], [67, 24, 67], [73, 20, 71], [61, 11, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 19], []]
 b := ![[], [40, 63, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [46, 76, 12, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-650637, 508873, -56357]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7839, 6131, -679]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![5, 1, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![5, 1, 0]] 
 ![![89, 0, 0], ![5, 1, 0], ![64, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![5, 1, 0], ![0, 5, 1], ![-1639, 254, 6]]]
  hmulB := by decide  
  f := ![![![81, 16, 0], ![-1424, 0, 0]], ![![-5, -1, 0], ![90, 0, 0]], ![![56, 11, 0], ![-984, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 89, 0], ![-64, 0, 89]], ![![0, 1, 0], ![-1, 5, 1], ![-37, 254, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N0 : Nat.card (O ⧸ I89N0) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N0)

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := prime_ideal_of_norm_prime hp89.out _ NI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![9, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![9, 1, 0]] 
 ![![89, 0, 0], ![9, 1, 0], ![8, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![9, 1, 0], ![0, 9, 1], ![-1639, 254, 10]]]
  hmulB := by decide  
  f := ![![![73, 8, 0], ![-712, 0, 0]], ![![-9, -1, 0], ![90, 0, 0]], ![![-8, -1, 0], ![80, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 89, 0], ![-8, 0, 89]], ![![0, 1, 0], ![-1, 9, 1], ![-45, 254, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1

def I89N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-15, 1, 0]] i)))

def SI89N2: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-15, 1, 0]] 
 ![![89, 0, 0], ![74, 1, 0], ![42, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-15, 1, 0], ![0, -15, 1], ![-1639, 254, -14]]]
  hmulB := by decide  
  f := ![![![121, -8, 0], ![712, 0, 0]], ![![106, -7, 0], ![624, 0, 0]], ![![78, -5, 0], ![460, 1, 0]]]
  g := ![![![1, 0, 0], ![-74, 89, 0], ![-42, 0, 89]], ![![-1, 1, 0], ![12, -15, 1], ![-223, 254, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N2 : Nat.card (O ⧸ I89N2) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N2)

lemma isPrimeI89N2 : Ideal.IsPrime I89N2 := prime_ideal_of_norm_prime hp89.out _ NI89N2
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![5, 1, 0]] ![![89, 0, 0], ![9, 1, 0]]
  ![![89, 0, 0], ![-133, 14, 1]] where
 M := ![![![7921, 0, 0], ![801, 89, 0]], ![![445, 89, 0], ![45, 14, 1]]]
 hmul := by decide  
 g := ![![![![89, 0, 0], ![0, 0, 0]], ![![9, 1, 0], ![0, 0, 0]]], ![![![5, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI89N1 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-133, 14, 1]] ![![89, 0, 0], ![-15, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1335, 89, 0]], ![![-11837, 1246, 89], ![356, -89, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-15, 1, 0]]], ![![![-133, 14, 1]], ![![4, -1, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1, I89N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
    exact isPrimeI89N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0 ⊙ MulI89N1)
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [93, 82, 30, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 56, 67], [14, 40, 30], [0, 1]]
 g := ![![[86, 80, 24], [84, 27], [63, 54], [38, 24], [36, 27], [1]], ![[50, 13, 26, 80], [67, 44], [78, 9], [51, 36], [20, 1], [83, 93, 27, 63]], ![[34, 57, 81, 71], [65, 49], [70, 65], [93, 95], [17, 88], [7, 86, 86, 34]]]
 h' := ![![[53, 56, 67], [80, 43, 86], [36, 53, 67], [47, 46, 32], [63, 89, 86], [4, 15, 67], [0, 1]], ![[14, 40, 30], [31, 70, 16], [32, 66, 23], [60, 39, 94], [27, 27, 91], [23, 72, 96], [53, 56, 67]], ![[0, 1], [55, 81, 92], [38, 75, 7], [90, 12, 68], [3, 78, 17], [56, 10, 31], [14, 40, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 59], []]
 b := ![[], [27, 95, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [93, 82, 30, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72661827, -22913922, 1806043]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![749091, -236226, 18619]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [40, 1, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 1, 83], [28, 99, 18], [0, 1]]
 g := ![![[99, 33, 16], [74, 82], [65, 31, 81], [89, 80], [26, 49], [1]], ![[85, 36, 89, 27], [86, 24], [23, 96, 88, 89], [20, 43], [46, 16], [37, 9, 43, 26]], ![[85, 80, 46, 61], [82, 92], [96, 19, 98, 26], [85, 100], [88, 20], [100, 52, 96, 75]]]
 h' := ![![[80, 1, 83], [39, 28, 4], [26, 100, 48], [71, 60, 9], [55, 13, 79], [61, 100, 7], [0, 1]], ![[28, 99, 18], [19, 96, 94], [96, 7, 23], [89, 11, 13], [92, 43, 12], [66, 17, 4], [80, 1, 83]], ![[0, 1], [39, 78, 3], [84, 95, 30], [88, 30, 79], [85, 45, 10], [75, 85, 90], [28, 99, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 51], []]
 b := ![[], [78, 92, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [40, 1, 94, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3140393, 1084538, -91304]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31093, 10738, -904]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![4, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![4, 1, 0]] 
 ![![103, 0, 0], ![4, 1, 0], ![87, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![4, 1, 0], ![0, 4, 1], ![-1639, 254, 5]]]
  hmulB := by decide  
  f := ![![![97, 24, 0], ![-2472, 0, 0]], ![![-4, -1, 0], ![104, 0, 0]], ![![81, 20, 0], ![-2064, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 103, 0], ![-87, 0, 103]], ![![0, 1, 0], ![-1, 4, 1], ![-30, 254, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![13, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![13, 1, 0]] 
 ![![103, 0, 0], ![13, 1, 0], ![37, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![13, 1, 0], ![0, 13, 1], ![-1639, 254, 14]]]
  hmulB := by decide  
  f := ![![![79, 6, 0], ![-618, 0, 0]], ![![-13, -1, 0], ![104, 0, 0]], ![![15, 1, 0], ![-116, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 103, 0], ![-37, 0, 103]], ![![0, 1, 0], ![-2, 13, 1], ![-53, 254, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-18, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-18, 1, 0]] 
 ![![103, 0, 0], ![85, 1, 0], ![88, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-18, 1, 0], ![0, -18, 1], ![-1639, 254, -17]]]
  hmulB := by decide  
  f := ![![![1315, -73, 0], ![7519, 0, 0]], ![![1081, -60, 0], ![6181, 0, 0]], ![![1120, -62, 0], ![6404, 1, 0]]]
  g := ![![![1, 0, 0], ![-85, 103, 0], ![-88, 0, 103]], ![![-1, 1, 0], ![14, -18, 1], ![-211, 254, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![4, 1, 0]] ![![103, 0, 0], ![13, 1, 0]]
  ![![103, 0, 0], ![-154, 17, 1]] where
 M := ![![![10609, 0, 0], ![1339, 103, 0]], ![![412, 103, 0], ![52, 17, 1]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![13, 1, 0], ![0, 0, 0]]], ![![![4, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-154, 17, 1]] ![![103, 0, 0], ![-18, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-1854, 103, 0]], ![![-15862, 1751, 103], ![1133, -206, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-18, 1, 0]]], ![![![-154, 17, 1]], ![![11, -2, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [79, 74, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 73, 105], [20, 33, 2], [0, 1]]
 g := ![![[71, 67, 4], [86, 47, 52], [32, 49], [59, 87, 49], [59, 90], [1]], ![[1, 26, 88, 83], [12, 70, 61, 76], [100, 90], [94, 20, 18, 90], [23, 48], [32, 28, 6, 99]], ![[7, 29, 74, 106], [57, 48, 26, 6], [5, 3], [87, 26, 85, 51], [19, 69], [95, 105, 89, 8]]]
 h' := ![![[62, 73, 105], [54, 92, 105], [2, 26, 65], [47, 86, 100], [82, 2, 7], [28, 33, 82], [0, 1]], ![[20, 33, 2], [13, 29, 71], [60, 36, 60], [91, 47, 25], [37, 64, 13], [79, 88, 72], [62, 73, 105]], ![[0, 1], [51, 93, 38], [18, 45, 89], [78, 81, 89], [99, 41, 87], [67, 93, 60], [20, 33, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 26], []]
 b := ![[], [61, 37, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [79, 74, 25, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61414790, 20359746, -1643092]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-573970, 190278, -15356]
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


def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![36, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![36, 1, 0]] 
 ![![109, 0, 0], ![36, 1, 0], ![12, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![36, 1, 0], ![0, 36, 1], ![-1639, 254, 37]]]
  hmulB := by decide  
  f := ![![![1585, 44, 0], ![-4796, 0, 0]], ![![468, 13, 0], ![-1416, 0, 0]], ![![156, 4, 0], ![-472, 1, 0]]]
  g := ![![![1, 0, 0], ![-36, 109, 0], ![-12, 0, 109]], ![![0, 1, 0], ![-12, 36, 1], ![-103, 254, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![36, 1, 0]] ![![109, 0, 0], ![36, 1, 0]]
  ![![109, 0, 0], ![-121, -37, 1]] where
 M := ![![![11881, 0, 0], ![3924, 109, 0]], ![![3924, 109, 0], ![1296, 72, 1]]]
 hmul := by decide  
 g := ![![![![109, 0, 0], ![0, 0, 0]], ![![36, 1, 0], ![0, 0, 0]]], ![![![36, 1, 0], ![0, 0, 0]], ![![13, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-121, -37, 1]] ![![109, 0, 0], ![36, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![3924, 109, 0]], ![![-13189, -4033, 109], ![-5995, -1199, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![36, 1, 0]]], ![![![-121, -37, 1]], ![![-55, -11, 0]]]]
 hle2 := by decide  

def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N0, I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N0
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-56, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-56, 1, 0]] 
 ![![113, 0, 0], ![57, 1, 0], ![28, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-56, 1, 0], ![0, -56, 1], ![-1639, 254, -55]]]
  hmulB := by decide  
  f := ![![![6329, -113, 0], ![12769, 0, 0]], ![![3249, -58, 0], ![6555, 0, 0]], ![![1596, -28, 0], ![3220, 1, 0]]]
  g := ![![![1, 0, 0], ![-57, 113, 0], ![-28, 0, 113]], ![![-1, 1, 0], ![28, -56, 1], ![-129, 254, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-36, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-36, 1, 0]] 
 ![![113, 0, 0], ![77, 1, 0], ![60, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-36, 1, 0], ![0, -36, 1], ![-1639, 254, -35]]]
  hmulB := by decide  
  f := ![![![1225, -34, 0], ![3842, 0, 0]], ![![829, -23, 0], ![2600, 0, 0]], ![![660, -18, 0], ![2070, 1, 0]]]
  g := ![![![1, 0, 0], ![-77, 113, 0], ![-60, 0, 113]], ![![-1, 1, 0], ![24, -36, 1], ![-169, 254, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-22, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-22, 1, 0]] 
 ![![113, 0, 0], ![91, 1, 0], ![81, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-22, 1, 0], ![0, -22, 1], ![-1639, 254, -21]]]
  hmulB := by decide  
  f := ![![![1013, -46, 0], ![5198, 0, 0]], ![![815, -37, 0], ![4182, 0, 0]], ![![753, -34, 0], ![3864, 1, 0]]]
  g := ![![![1, 0, 0], ![-91, 113, 0], ![-81, 0, 113]], ![![-1, 1, 0], ![17, -22, 1], ![-204, 254, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-56, 1, 0]] ![![113, 0, 0], ![-36, 1, 0]]
  ![![113, 0, 0], ![-131, 21, 1]] where
 M := ![![![12769, 0, 0], ![-4068, 113, 0]], ![![-6328, 113, 0], ![2016, -92, 1]]]
 hmul := by decide  
 g := ![![![![113, 0, 0], ![0, 0, 0]], ![![95, -20, -1], ![113, 0, 0]]], ![![![75, -20, -1], ![113, 0, 0]], ![![19, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-131, 21, 1]] ![![113, 0, 0], ![-22, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-2486, 113, 0]], ![![-14803, 2373, 113], ![1243, -339, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-22, 1, 0]]], ![![![-131, 21, 1]], ![![11, -3, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [41, 67, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 84, 23], [89, 42, 104], [0, 1]]
 g := ![![[27, 32, 22], [126, 37, 117], [34, 89, 81], [79, 58, 64], [55, 6, 4], [1]], ![[77, 77, 34, 118], [104, 88, 105, 59], [97, 82, 83, 125], [120, 49, 29, 46], [24, 85, 41, 54], [94, 63, 8, 102]], ![[43, 57, 90, 107], [120, 112, 90, 84], [100, 94, 28, 79], [12, 63, 15, 87], [104, 90, 43, 87], [79, 87, 56, 25]]]
 h' := ![![[36, 84, 23], [41, 83, 28], [3, 74, 25], [63, 21, 9], [31, 36, 119], [86, 60, 125], [0, 1]], ![[89, 42, 104], [14, 29, 37], [34, 94, 85], [54, 63, 99], [102, 91, 111], [3, 84, 26], [36, 84, 23]], ![[0, 1], [72, 15, 62], [3, 86, 17], [3, 43, 19], [39, 0, 24], [55, 110, 103], [89, 42, 104]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 79], []]
 b := ![[], [91, 51, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [41, 67, 2, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-601472, 517652, -58928]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4736, 4076, -464]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [31, 125, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 69, 51], [111, 61, 80], [0, 1]]
 g := ![![[109, 28, 11], [60, 115, 80], [7, 49], [63, 58], [115, 12], [7, 1], []], ![[92, 11, 25, 37], [23, 74, 45, 104], [1, 121], [121, 38], [78, 65], [6, 53], [93, 112]], ![[13, 39, 117, 114], [66, 98, 77, 108], [44, 16], [69, 28], [121, 109], [2, 45], [64, 112]]]
 h' := ![![[27, 69, 51], [105, 28, 81], [58, 43, 39], [119, 24, 124], [32, 129, 53], [45, 11, 55], [0, 0, 1], [0, 1]], ![[111, 61, 80], [93, 108, 81], [5, 51, 118], [125, 33, 11], [48, 61, 118], [34, 93, 117], [73, 26, 61], [27, 69, 51]], ![[0, 1], [14, 126, 100], [40, 37, 105], [116, 74, 127], [91, 72, 91], [82, 27, 90], [119, 105, 69], [111, 61, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 124], []]
 b := ![[], [30, 117, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [31, 125, 124, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43105419, 4192786, 364049]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-329049, 32006, 2779]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [12, 63, 98, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 1, 48], [28, 135, 89], [0, 1]]
 g := ![![[79, 65, 119], [56, 133], [85, 65], [35, 116, 78], [88, 72], [39, 1], []], ![[109, 10, 82, 51], [106, 126], [11, 101], [128, 66, 101, 35], [10, 61], [122, 4], [80, 112]], ![[51, 128, 105, 92], [22, 39], [42, 126], [132, 92, 5, 108], [15, 120], [22, 1], [39, 112]]]
 h' := ![![[11, 1, 48], [2, 6, 121], [20, 94, 74], [128, 103, 32], [1, 99, 107], [80, 134, 88], [0, 0, 1], [0, 1]], ![[28, 135, 89], [66, 7, 46], [70, 38, 117], [32, 101, 85], [93, 118, 17], [58, 60, 91], [120, 77, 135], [11, 1, 48]], ![[0, 1], [46, 124, 107], [6, 5, 83], [109, 70, 20], [6, 57, 13], [130, 80, 95], [42, 60, 1], [28, 135, 89]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 46], []]
 b := ![[], [83, 136, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [12, 63, 98, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4835004, 1040652, -54389]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35292, 7596, -397]
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



lemma PB170I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB170I2 : PrimesBelowBoundCertificateInterval O 79 137 170 where
  m := 11
  g := ![1, 3, 1, 1, 3, 1, 3, 3, 1, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB170I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1, I89N2]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0, I109N0, I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0]
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
    · exact ![571787]
    · exact ![89, 89, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
    · exact ![2048383]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
      exact NI89N2
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N0
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
  β := ![I89N0, I89N1, I89N2, I103N0, I103N1, I103N2, I109N0, I113N0, I113N1, I113N2]
  Il := ![[], [I89N0, I89N1, I89N2], [], [], [I103N0, I103N1, I103N2], [], [I109N0, I109N0, I109N0], [I113N0, I113N1, I113N2], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
