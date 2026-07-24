
import IdealArithmetic.Examples.NF3_1_331240_2.RI3_1_331240_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107, -8, 11]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-107, -8, 11]] 
 ![![83, 0, 0], ![0, 83, 0], ![28, 37, 1]] where
  M :=![![![-107, -8, 11], ![1210, -67, -22], ![330, 110, -89]]]
  hmulB := by decide  
  f := ![![![101, 6, 11]], ![![1210, 71, 132]], ![![596, 35, 65]]]
  g := ![![![-5, -5, 11], ![22, 9, -22], ![34, 41, -89]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [53, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 82], [0, 1]]
 g := ![![[32, 81], [3, 11], [9], [23], [71, 51], [1]], ![[21, 2], [22, 72], [9], [23], [61, 32], [1]]]
 h' := ![![[47, 82], [7, 9], [6, 54], [63, 3], [55, 40], [30, 47], [0, 1]], ![[0, 1], [15, 74], [54, 29], [38, 80], [26, 43], [81, 36], [47, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [26, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [53, 36, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4453, 3919, 411]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-85, -136, 411]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 6, 11]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![101, 6, 11]] 
 ![![83, 0, 0], ![2, 1, 0], ![76, 0, 1]] where
  M :=![![![101, 6, 11], ![1210, 71, 132], ![1870, 110, 203]]]
  hmulB := by decide  
  f := ![![![-107, -8, 11]], ![![12, -1, 0]], ![![-94, -6, 9]]]
  g := ![![![-9, 6, 11], ![-108, 71, 132], ![-166, 110, 203]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-107, -8, 11]] ![![101, 6, 11]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [53, 53, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 64, 22], [34, 24, 67], [0, 1]]
 g := ![![[26, 9, 22], [19, 2], [40, 25], [22, 12, 36], [28, 80, 1], []], ![[88, 24, 51, 69], [18, 50], [70, 81], [50, 22, 18, 47], [85, 28, 56, 34], [62, 39]], ![[32, 21, 6, 4], [11, 72], [9, 16], [43, 14, 51, 17], [6, 20, 56, 45], [17, 39]]]
 h' := ![![[46, 64, 22], [36, 82, 17], [8, 58, 64], [80, 18, 84], [29, 61, 83], [0, 0, 1], [0, 1]], ![[34, 24, 67], [27, 14, 76], [64, 38, 53], [83, 79, 9], [65, 71, 41], [76, 1, 24], [46, 64, 22]], ![[0, 1], [39, 82, 85], [55, 82, 61], [40, 81, 85], [39, 46, 54], [77, 88, 64], [34, 24, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 13], []]
 b := ![[], [77, 32, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [53, 53, 9, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3871678, 164739, 85351]
  a := ![-1, -7, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43502, 1851, 959]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![4, 24, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![4, 24, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![4, 24, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![4, 24, 1], ![110, -116, 270], ![2750, 10, 154]]]
  hmulB := by decide  
  f := ![![![-3, -24, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -24, 97]], ![![0, 0, 1], ![-10, -68, 270], ![22, -38, 154]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [9, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 96], [0, 1]]
 g := ![![[22, 54], [81], [96], [95], [49], [93, 1]], ![[0, 43], [81], [96], [95], [49], [89, 96]]]
 h' := ![![[93, 96], [31, 32], [88, 88], [51, 75], [79, 17], [36, 7], [0, 1]], ![[0, 1], [0, 65], [27, 9], [42, 22], [11, 80], [8, 90], [93, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [39, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [9, 4, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3849, -89, 259]
  a := ![-64, 1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![29, -65, 259]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![21, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![21, 1, 0]] 
 ![![97, 0, 0], ![21, 1, 0], ![40, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![21, 1, 0], ![0, 16, 11], ![110, 0, 27]]]
  hmulB := by decide  
  f := ![![![526, 25, 0], ![-2425, 0, 0]], ![![84, 4, 0], ![-387, 0, 0]], ![![226, 2, -6], ![-1042, 53, 0]]]
  g := ![![![1, 0, 0], ![-21, 97, 0], ![-40, 0, 97]], ![![0, 1, 0], ![-8, 16, 11], ![-10, 0, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![4, 24, 1]] ![![97, 0, 0], ![21, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![2037, 97, 0]], ![![388, 2328, 97], ![194, 388, 291]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![21, 1, 0]]], ![![![4, 24, 1]], ![![2, 4, 3]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![32, 21, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![32, 21, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![32, 21, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![32, 21, 1], ![110, -73, 237], ![2420, 10, 164]]]
  hmulB := by decide  
  f := ![![![-31, -21, -1], ![101, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -21, 101]], ![![0, 0, 1], ![-74, -50, 237], ![-28, -34, 164]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [87, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [87, 100], [0, 1]]
 g := ![![[100, 36], [71], [67, 24], [64], [64], [87, 1]], ![[0, 65], [71], [34, 77], [64], [64], [73, 100]]]
 h' := ![![[87, 100], [17, 95], [29, 24], [11, 78], [23, 8], [6, 8], [0, 1]], ![[0, 1], [0, 6], [97, 77], [30, 23], [12, 93], [96, 93], [87, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [28, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [87, 14, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5382, 5331, 1235]
  a := ![1, 11, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-338, -204, 1235]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-35, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-35, 1, 0]] 
 ![![101, 0, 0], ![66, 1, 0], ![38, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-35, 1, 0], ![0, -40, 11], ![110, 0, -29]]]
  hmulB := by decide  
  f := ![![![1821, -52, 0], ![5252, 0, 0]], ![![1226, -35, 0], ![3536, 0, 0]], ![![708, -2, -5], ![2042, 46, 0]]]
  g := ![![![1, 0, 0], ![-66, 101, 0], ![-38, 0, 101]], ![![-1, 1, 0], ![22, -40, 11], ![12, 0, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![32, 21, 1]] ![![101, 0, 0], ![-35, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-3535, 101, 0]], ![![3232, 2121, 101], ![-1010, -808, 202]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-35, 1, 0]]], ![![![32, 21, 1]], ![![-10, -8, 2]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [17, 35, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 97, 11], [23, 5, 92], [0, 1]]
 g := ![![[20, 45, 76], [32, 98, 33], [46, 66, 49], [37, 36], [48, 64], [1]], ![[69, 55, 95, 54], [66, 93, 47, 85], [7, 24, 10, 88], [99, 61], [74, 66], [21, 20, 49, 95]], ![[64, 31, 61, 8], [74, 10, 52, 15], [49, 79, 64, 56], [92, 15], [95, 29], [58, 34, 0, 8]]]
 h' := ![![[72, 97, 11], [74, 8, 73], [42, 22, 41], [30, 18, 7], [91, 70, 6], [86, 68, 95], [0, 1]], ![[23, 5, 92], [83, 74, 41], [1, 24, 35], [6, 97, 27], [12, 50, 79], [31, 64, 90], [72, 97, 11]], ![[0, 1], [78, 21, 92], [73, 57, 27], [74, 91, 69], [89, 86, 18], [57, 74, 21], [23, 5, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 50], []]
 b := ![[], [20, 79, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [17, 35, 8, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9242293, -319300, -229793]
  a := ![0, 9, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-89731, -3100, -2231]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-8, -48, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-8, -48, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![99, 59, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-8, -48, 1], ![110, 232, -522], ![-5170, 10, -290]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -59, 107]], ![![-1, -1, 1], ![484, 290, -522], ![220, 160, -290]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [11, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 106], [0, 1]]
 g := ![![[43, 39], [10, 86], [39], [1, 76], [40], [62, 1]], ![[0, 68], [99, 21], [39], [5, 31], [40], [17, 106]]]
 h' := ![![[62, 106], [104, 57], [13, 34], [96, 50], [90, 41], [67, 88], [0, 1]], ![[0, 1], [0, 50], [88, 73], [93, 57], [64, 66], [66, 19], [62, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [77, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [11, 45, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![400457, 294628, 102565]
  a := ![1, -81, 182]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-91154, -53801, 102565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-13, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-13, 1, 0]] 
 ![![107, 0, 0], ![94, 1, 0], ![76, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-13, 1, 0], ![0, -18, 11], ![110, 0, -7]]]
  hmulB := by decide  
  f := ![![![456, -35, 0], ![3745, 0, 0]], ![![404, -31, 0], ![3318, 0, 0]], ![![320, -18, -4], ![2628, 39, 0]]]
  g := ![![![1, 0, 0], ![-94, 107, 0], ![-76, 0, 107]], ![![-1, 1, 0], ![8, -18, 11], ![6, 0, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-8, -48, 1]] ![![107, 0, 0], ![-13, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-1391, 107, 0]], ![![-856, -5136, 107], ![214, 856, -535]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-13, 1, 0]]], ![![![-8, -48, 1]], ![![2, 8, -5]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![29, 8, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![29, 8, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![29, 8, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![29, 8, 1], ![110, -11, 94], ![990, 10, 83]]]
  hmulB := by decide  
  f := ![![![-28, -8, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -8, 109]], ![![0, 0, 1], ![-24, -7, 94], ![-13, -6, 83]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [85, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [71, 108], [0, 1]]
 g := ![![[62, 106], [31], [65, 48], [78, 48], [94], [71, 1]], ![[67, 3], [31], [94, 61], [107, 61], [94], [33, 108]]]
 h' := ![![[71, 108], [47, 18], [34, 24], [19, 87], [41, 87], [69, 51], [0, 1]], ![[0, 1], [17, 91], [103, 85], [92, 22], [5, 22], [93, 58], [71, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [44, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [85, 38, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3568, 2063, 1307]
  a := ![-1, -7, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-315, -77, 1307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![15, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![15, 1, 0]] 
 ![![109, 0, 0], ![15, 1, 0], ![26, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![15, 1, 0], ![0, 10, 11], ![110, 0, 21]]]
  hmulB := by decide  
  f := ![![![1171, 78, 0], ![-8502, 0, 0]], ![![135, 9, 0], ![-980, 0, 0]], ![![254, 16, -1], ![-1844, 10, 0]]]
  g := ![![![1, 0, 0], ![-15, 109, 0], ![-26, 0, 109]], ![![0, 1, 0], ![-4, 10, 11], ![-4, 0, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![29, 8, 1]] ![![109, 0, 0], ![15, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![1635, 109, 0]], ![![3161, 872, 109], ![545, 109, 109]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![15, 1, 0]]], ![![![29, 8, 1]], ![![5, 1, 1]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![54, 16, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![54, 16, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![54, 16, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![54, 16, 1], ![110, -26, 182], ![1870, 10, 156]]]
  hmulB := by decide  
  f := ![![![-53, -16, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -16, 113]], ![![0, 0, 1], ![-86, -26, 182], ![-58, -22, 156]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [21, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 112], [0, 1]]
 g := ![![[90, 28], [11], [11], [18], [84, 53], [31, 1]], ![[54, 85], [11], [11], [18], [32, 60], [62, 112]]]
 h' := ![![[31, 112], [31, 64], [6, 24], [89, 89], [44, 73], [27, 36], [0, 1]], ![[0, 1], [94, 49], [72, 89], [23, 24], [47, 40], [13, 77], [31, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [70, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [21, 82, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10251, 7482, 5256]
  a := ![0, -14, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2421, -678, 5256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![44, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![44, 1, 0]] 
 ![![113, 0, 0], ![44, 1, 0], ![70, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![44, 1, 0], ![0, 39, 11], ![110, 0, 50]]]
  hmulB := by decide  
  f := ![![![617, 14, 0], ![-1582, 0, 0]], ![![220, 5, 0], ![-564, 0, 0]], ![![390, -16, -7], ![-1000, 72, 0]]]
  g := ![![![1, 0, 0], ![-44, 113, 0], ![-70, 0, 113]], ![![0, 1, 0], ![-22, 39, 11], ![-30, 0, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![54, 16, 1]] ![![113, 0, 0], ![44, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![4972, 113, 0]], ![![6102, 1808, 113], ![2486, 678, 226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![44, 1, 0]]], ![![![54, 16, 1]], ![![22, 6, 2]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [83, 84, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 77, 103], [44, 49, 24], [0, 1]]
 g := ![![[106, 43, 69], [33, 73, 4], [92, 93, 120], [32, 39, 71], [93, 106, 81], [1]], ![[122, 72, 97, 79], [97, 72, 123, 38], [114, 98, 123, 84], [29, 71, 93, 70], [116, 102, 54, 18], [126, 22, 4, 19]], ![[53, 57, 126, 96], [85, 54, 78, 92], [58, 40, 47, 108], [83, 15, 3, 3], [44, 48, 49, 106], [34, 89, 46, 108]]]
 h' := ![![[92, 77, 103], [55, 61, 14], [111, 41, 2], [11, 66, 82], [28, 58, 43], [44, 43, 9], [0, 1]], ![[44, 49, 24], [6, 126, 111], [117, 91, 3], [13, 26, 21], [87, 15, 80], [7, 55, 44], [92, 77, 103]], ![[0, 1], [70, 67, 2], [46, 122, 122], [73, 35, 24], [52, 54, 4], [66, 29, 74], [44, 49, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 22], []]
 b := ![[], [45, 120, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [83, 84, 118, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-359819829, -8224520, -8732520]
  a := ![2, 30, -68]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2833227, -64760, -68760]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![19, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![19, 1, 0]] 
 ![![131, 0, 0], ![19, 1, 0], ![83, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![19, 1, 0], ![0, 14, 11], ![110, 0, 25]]]
  hmulB := by decide  
  f := ![![![1084, 57, 0], ![-7467, 0, 0]], ![![152, 8, 0], ![-1047, 0, 0]], ![![690, 35, -1], ![-4753, 12, 0]]]
  g := ![![![1, 0, 0], ![-19, 131, 0], ![-83, 0, 131]], ![![0, 1, 0], ![-9, 14, 11], ![-15, 0, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![45, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![45, 1, 0]] 
 ![![131, 0, 0], ![45, 1, 0], ![15, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![45, 1, 0], ![0, 40, 11], ![110, 0, 51]]]
  hmulB := by decide  
  f := ![![![2656, 59, 0], ![-7729, 0, 0]], ![![900, 20, 0], ![-2619, 0, 0]], ![![300, 3, -1], ![-873, 12, 0]]]
  g := ![![![1, 0, 0], ![-45, 131, 0], ![-15, 0, 131]], ![![0, 1, 0], ![-15, 40, 11], ![-5, 0, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-65, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-65, 1, 0]] 
 ![![131, 0, 0], ![66, 1, 0], ![27, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-65, 1, 0], ![0, -70, 11], ![110, 0, -59]]]
  hmulB := by decide  
  f := ![![![8516, -131, 0], ![17161, 0, 0]], ![![4356, -67, 0], ![8778, 0, 0]], ![![1782, -21, -1], ![3591, 12, 0]]]
  g := ![![![1, 0, 0], ![-66, 131, 0], ![-27, 0, 131]], ![![-1, 1, 0], ![33, -70, 11], ![13, 0, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![19, 1, 0]] ![![131, 0, 0], ![45, 1, 0]]
  ![![131, 0, 0], ![42, 53, 1]] where
 M := ![![![17161, 0, 0], ![5895, 131, 0]], ![![2489, 131, 0], ![855, 59, 11]]]
 hmul := by decide  
 g := ![![![![89, -53, -1], ![131, 0, 0]], ![![3, -52, -1], ![131, 0, 0]]], ![![![-23, -52, -1], ![131, 0, 0]], ![![3, -4, 0], ![11, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![42, 53, 1]] ![![131, 0, 0], ![-65, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-8515, 131, 0]], ![![5502, 6943, 131], ![-2620, -3668, 524]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-65, 1, 0]]], ![![![42, 53, 1]], ![![-20, -28, 4]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![51, 6, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![51, 6, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![51, 6, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![51, 6, 1], ![110, 21, 72], ![770, 10, 93]]]
  hmulB := by decide  
  f := ![![![-50, -6, -1], ![137, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -6, 137]], ![![0, 0, 1], ![-26, -3, 72], ![-29, -4, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [33, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 136], [0, 1]]
 g := ![![[48, 121], [101], [38], [74, 120], [63], [38], [1]], ![[47, 16], [101], [38], [13, 17], [63], [38], [1]]]
 h' := ![![[60, 136], [4, 126], [7, 85], [24, 77], [75, 42], [109, 101], [104, 60], [0, 1]], ![[0, 1], [29, 11], [38, 52], [123, 60], [129, 95], [4, 36], [5, 77], [60, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [46, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [33, 77, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1203, -68, 217]
  a := ![13, -1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-72, -10, 217]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![65, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![65, 1, 0]] 
 ![![137, 0, 0], ![65, 1, 0], ![44, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![65, 1, 0], ![0, 60, 11], ![110, 0, 71]]]
  hmulB := by decide  
  f := ![![![4551, 70, 0], ![-9590, 0, 0]], ![![2145, 33, 0], ![-4520, 0, 0]], ![![1492, 12, -2], ![-3144, 25, 0]]]
  g := ![![![1, 0, 0], ![-65, 137, 0], ![-44, 0, 137]], ![![0, 1, 0], ![-32, 60, 11], ![-22, 0, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![51, 6, 1]] ![![137, 0, 0], ![65, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8905, 137, 0]], ![![6987, 822, 137], ![3425, 411, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![65, 1, 0]]], ![![![51, 6, 1]], ![![25, 3, 1]]]]
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


lemma PB163I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB163I2 : PrimesBelowBoundCertificateInterval O 79 137 163 where
  m := 11
  g := ![2, 1, 2, 2, 1, 2, 2, 2, 1, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB163I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1, I131N2]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![131, 131, 131]
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
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I97N1, I101N1, I107N1, I109N1, I113N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N1], [], [I97N1], [I101N1], [], [I107N1], [I109N1], [I113N1], [], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
