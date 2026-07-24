
import IdealArithmetic.Examples.NF3_3_662216_1.RI3_3_662216_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11137, -4706, -826]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-11137, -4706, -826]] 
 ![![83, 0, 0], ![0, 83, 0], ![17, 27, 1]] where
  M :=![![![-11137, -4706, -826], ![-137692, -58219, -10238], ![-847700, -358276, -62925]]]
  hmulB := by decide  
  f := ![![![-55411, -2278, 1098]], ![![174500, 7175, -3458]], ![![42439, 1745, -841]]]
  g := ![![![35, 212, -826], ![438, 2629, -10238], ![2675, 16153, -62925]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [4, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 82], [0, 1]]
 g := ![![[35, 21], [59, 10], [7], [7], [21, 12], [1]], ![[0, 62], [70, 73], [7], [7], [1, 71], [1]]]
 h' := ![![[26, 82], [13, 41], [37, 50], [56, 67], [82, 16], [79, 26], [0, 1]], ![[0, 1], [0, 42], [9, 33], [55, 16], [0, 67], [8, 57], [26, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [35, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [4, 57, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1029, 609, 124]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, -33, 124]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-55411, -2278, 1098]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-55411, -2278, 1098]] 
 ![![83, 0, 0], ![28, 1, 0], ![65, 0, 1]] where
  M :=![![![-55411, -2278, 1098], ![174500, 7175, -3458], ![-247076, -10164, 4897]]]
  hmulB := by decide  
  f := ![![![-11137, -4706, -826]], ![![-5416, -2289, -402]], ![![-18935, -8002, -1405]]]
  g := ![![![-759, -2278, 1098], ![2390, 7175, -3458], ![-3383, -10164, 4897]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-11137, -4706, -826]] ![![-55411, -2278, 1098]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-530, -129, 28]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-530, -129, 28]] 
 ![![89, 0, 0], ![0, 89, 0], ![51, 24, 1]] where
  M :=![![![-530, -129, 28], ![4379, 1066, -230], ![-17717, -4301, 937]]]
  hmulB := by decide  
  f := ![![![108, 5, -2]], ![![-317, -6, 8]], ![![-17, 2, 1]]]
  g := ![![![-22, -9, 28], ![181, 74, -230], ![-736, -301, 937]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [18, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 88], [0, 1]]
 g := ![![[39, 5], [45], [5], [7, 40], [17, 11], [1]], ![[0, 84], [45], [5], [51, 49], [38, 78], [1]]]
 h' := ![![[10, 88], [12, 70], [33, 32], [52, 70], [50, 29], [71, 10], [0, 1]], ![[0, 1], [0, 19], [86, 57], [40, 19], [73, 60], [82, 79], [10, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [83, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [18, 79, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311, 1419, 1828]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1051, -477, 1828]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![108, 5, -2]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![108, 5, -2]] 
 ![![89, 0, 0], ![40, 1, 0], ![46, 0, 1]] where
  M :=![![![108, 5, -2], ![-317, -6, 8], ![587, 67, -1]]]
  hmulB := by decide  
  f := ![![![-530, -129, 28]], ![![-189, -46, 10]], ![![-473, -115, 25]]]
  g := ![![![0, 5, -2], ![-5, -6, 8], ![-23, 67, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-530, -129, 28]] ![![108, 5, -2]]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [29, 5, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [39, 42, 49], [3, 54, 48], [0, 1]]
 g := ![![[2, 21, 85], [43, 65], [73, 36], [39, 65], [45, 18], [1]], ![[34, 64, 11, 31], [44, 3], [18, 88], [], [56, 2], [5, 35, 61, 85]], ![[56, 41, 46, 31], [69, 70], [5, 43], [70, 65], [15, 8], [79, 80, 11, 12]]]
 h' := ![![[39, 42, 49], [46, 75, 52], [41, 49, 29], [86, 66, 6], [21, 28, 68], [68, 92, 42], [0, 1]], ![[3, 54, 48], [80, 7, 81], [17, 72, 87], [32, 3, 66], [41, 58], [4, 1, 83], [39, 42, 49]], ![[0, 1], [86, 15, 61], [27, 73, 78], [50, 28, 25], [72, 11, 29], [64, 4, 69], [3, 54, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 14], []]
 b := ![[], [93, 16, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [29, 5, 55, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6773713312, -3593999671, -1028285360]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69832096, -37051543, -10600880]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6248, 2641, 464]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![6248, 2641, 464]] 
 ![![101, 0, 0], ![0, 101, 0], ![57, 76, 1]] where
  M :=![![![6248, 2641, 464], ![77345, 32696, 5746], ![475777, 201113, 35337]]]
  hmulB := by decide  
  f := ![![![-2146, -85, 42]], ![![6677, 248, -128]], ![![3723, 136, -71]]]
  g := ![![![-200, -323, 464], ![-2477, -4000, 5746], ![-15232, -24599, 35337]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [54, 79, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 100], [0, 1]]
 g := ![![[37, 58], [92], [35, 45], [85], [70], [22, 1]], ![[0, 43], [92], [15, 56], [85], [70], [44, 100]]]
 h' := ![![[22, 100], [14, 82], [29, 71], [32, 34], [28, 61], [24, 26], [0, 1]], ![[0, 1], [0, 19], [76, 30], [73, 67], [57, 40], [91, 75], [22, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [34, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [54, 79, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1016, 2230, 1042]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-578, -762, 1042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2146, -85, 42]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-2146, -85, 42]] 
 ![![101, 0, 0], ![49, 1, 0], ![12, 0, 1]] where
  M :=![![![-2146, -85, 42], ![6677, 248, -128], ![-9107, -267, 163]]]
  hmulB := by decide  
  f := ![![![6248, 2641, 464]], ![![3797, 1605, 282]], ![![5453, 2305, 405]]]
  g := ![![![15, -85, 42], ![-39, 248, -128], ![20, -267, 163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![6248, 2641, 464]] ![![-2146, -85, 42]]
  ![![101, 0, 0]] where
 M := ![![![101, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![103, 0, 0], ![2, 1, 0], ![50, 0, 1]] where
  M :=![![![2, 1, 0], ![1, 2, 2], ![161, 57, 3]]]
  hmulB := by decide  
  f := ![![![-108, -3, 2]], ![![1, 0, 0]], ![![-55, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 2], ![-1, 57, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1164, 29, -20]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![1164, 29, -20]] 
 ![![103, 0, 0], ![19, 1, 0], ![26, 0, 1]] where
  M :=![![![1164, 29, -20], ![-3191, 24, 38], ![2489, -527, 53]]]
  hmulB := by decide  
  f := ![![![-21298, -9003, -1582]], ![![-6489, -2743, -482]], ![![-21123, -8929, -1569]]]
  g := ![![![11, 29, -20], ![-45, 24, 38], ![108, -527, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1481, -626, -110]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![-1481, -626, -110]] 
 ![![103, 0, 0], ![81, 1, 0], ![16, 0, 1]] where
  M :=![![![-1481, -626, -110], ![-18336, -7751, -1362], ![-112776, -47672, -8377]]]
  hmulB := by decide  
  f := ![![![-863, 82, -2]], ![![-681, 55, 0]], ![![-8, 56, -9]]]
  g := ![![![495, -626, -110], ![6129, -7751, -1362], ![37696, -47672, -8377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0]] ![![1164, 29, -20]]
  ![![-863, 82, -2]] where
 M := ![![![-863, 82, -2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-863, 82, -2]] ![![-1481, -626, -110]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![221, 90, 14]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![221, 90, 14]] 
 ![![107, 0, 0], ![0, 1, 0], ![54, 0, 1]] where
  M :=![![![221, 90, 14], ![2344, 1019, 194], ![16016, 6656, 1109]]]
  hmulB := by decide  
  f := ![![![-161193, -6626, 3194]], ![![4744, 195, -94]], ![![-88066, -3620, 1745]]]
  g := ![![![-5, 90, 14], ![-76, 1019, 194], ![-410, 6656, 1109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-706, -29, 14]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-706, -29, 14]] 
 ![![107, 0, 0], ![25, 1, 0], ![9, 0, 1]] where
  M :=![![![-706, -29, 14], ![2225, 92, -44], ![-3143, -127, 63]]]
  hmulB := by decide  
  f := ![![![-208, -49, 12]], ![![-31, -7, 2]], ![![-79, -18, 5]]]
  g := ![![![-1, -29, 14], ![3, 92, -44], ![-5, -127, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![296, 13, -6]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![296, 13, -6]] 
 ![![107, 0, 0], ![81, 1, 0], ![37, 0, 1]] where
  M :=![![![296, 13, -6], ![-953, -46, 20], ![1439, 87, -33]]]
  hmulB := by decide  
  f := ![![![222, 93, 16]], ![![193, 81, 14]], ![![233, 98, 17]]]
  g := ![![![-5, 13, -6], ![19, -46, 20], ![-41, 87, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![221, 90, 14]] ![![-706, -29, 14]]
  ![![222, 93, 16]] where
 M := ![![![222, 93, 16]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![222, 93, 16]] ![![296, 13, -6]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2260, 981, 186]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![2260, 981, 186]] 
 ![![109, 0, 0], ![0, 109, 0], ![52, 0, 1]] where
  M :=![![![2260, 981, 186], ![30927, 12862, 2148], ![178215, 76191, 13843]]]
  hmulB := by decide  
  f := ![![![132022, 5427, -2616]], ![![-415749, -17090, 8238]], ![![68383, 2811, -1355]]]
  g := ![![![-68, 9, 186], ![-741, 118, 2148], ![-4969, 699, 13843]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [30, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 108], [0, 1]]
 g := ![![[44, 22], [63], [40, 61], [57, 28], [25], [97, 1]], ![[107, 87], [63], [71, 48], [48, 81], [25], [85, 108]]]
 h' := ![![[97, 108], [73, 26], [108, 45], [34, 37], [12, 30], [33, 5], [0, 1]], ![[0, 1], [88, 83], [4, 64], [26, 72], [88, 79], [82, 104], [97, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [54, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [30, 12, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1100, 654, 214]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-92, 6, 214]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![132022, 5427, -2616]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![132022, 5427, -2616]] 
 ![![109, 0, 0], ![108, 1, 0], ![0, 0, 1]] where
  M :=![![![132022, 5427, -2616], ![-415749, -17090, 8238], ![588603, 24195, -11663]]]
  hmulB := by decide  
  f := ![![![2260, 981, 186]], ![![2523, 1090, 204]], ![![1635, 699, 127]]]
  g := ![![![-4166, 5427, -2616], ![13119, -17090, 8238], ![-18573, 24195, -11663]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![2260, 981, 186]] ![![132022, 5427, -2616]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3445, -140, 68]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-3445, -140, 68]] 
 ![![113, 0, 0], ![18, 1, 0], ![8, 0, 1]] where
  M :=![![![-3445, -140, 68], ![10808, 431, -212], ![-15128, -568, 291]]]
  hmulB := by decide  
  f := ![![![-5005, -2116, -372]], ![![-1346, -569, -100]], ![![-3728, -1576, -277]]]
  g := ![![![-13, -140, 68], ![42, 431, -212], ![-64, -568, 291]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-115, -28, 6]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-115, -28, 6]] 
 ![![113, 0, 0], ![27, 1, 0], ![88, 0, 1]] where
  M :=![![![-115, -28, 6], ![938, 227, -50], ![-3854, -942, 199]]]
  hmulB := by decide  
  f := ![![![-1927, -80, 38]], ![![-407, -17, 8]], ![![-1578, -66, 31]]]
  g := ![![![1, -28, 6], ![-7, 227, -50], ![36, -942, 199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1051, -444, -78]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-1051, -444, -78]] 
 ![![113, 0, 0], ![67, 1, 0], ![16, 0, 1]] where
  M :=![![![-1051, -444, -78], ![-13002, -5497, -966], ![-79986, -33810, -5941]]]
  hmulB := by decide  
  f := ![![![-2783, -624, 138]], ![![-1459, -325, 72]], ![![-1150, -270, 59]]]
  g := ![![![265, -444, -78], ![3281, -5497, -966], ![20180, -33810, -5941]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-3445, -140, 68]] ![![-115, -28, 6]]
  ![![2783, 624, -138]] where
 M := ![![![2783, 624, -138]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![2783, 624, -138]] ![![-1051, -444, -78]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-249812, -10269, 4950]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-249812, -10269, 4950]] 
 ![![127, 0, 0], ![11, 1, 0], ![67, 0, 1]] where
  M :=![![![-249812, -10269, 4950], ![786681, 32338, -15588], ![-1113759, -45783, 22069]]]
  hmulB := by decide  
  f := ![![![1918, 711, 72]], ![![263, 109, 18]], ![![1975, 756, 91]]]
  g := ![![![-3689, -10269, 4950], ![11617, 32338, -15588], ![-16447, -45783, 22069]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![180, 43, -10]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![180, 43, -10]] 
 ![![127, 0, 0], ![14, 1, 0], ![93, 0, 1]] where
  M :=![![![180, 43, -10], ![-1567, -390, 76], ![5833, 1361, -347]]]
  hmulB := by decide  
  f := ![![![31894, 1311, -632]], ![![2725, 112, -54]], ![![24475, 1006, -485]]]
  g := ![![![4, 43, -10], ![-25, -390, 76], ![150, 1361, -347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, -12, -2]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![-29, -12, -2]] 
 ![![127, 0, 0], ![101, 1, 0], ![107, 0, 1]] where
  M :=![![![-29, -12, -2], ![-334, -143, -26], ![-2150, -902, -155]]]
  hmulB := by decide  
  f := ![![![-1287, -56, 26]], ![![-991, -43, 20]], ![![-1133, -50, 23]]]
  g := ![![![11, -12, -2], ![133, -143, -26], ![831, -902, -155]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-249812, -10269, 4950]] ![![180, 43, -10]]
  ![![-1287, -56, 26]] where
 M := ![![![-1287, -56, 26]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![-1287, -56, 26]] ![![-29, -12, -2]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [120, 63, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 23, 51], [7, 107, 80], [0, 1]]
 g := ![![[128, 103, 61], [55, 28, 33], [104, 4], [103, 52], [68, 61], [105, 1], []], ![[100, 126, 65, 6], [78, 119, 76, 90], [8, 125], [58, 13], [69, 15], [124, 52], [89, 112]], ![[130, 72, 101, 11], [96, 27, 91, 84], [65, 65], [1, 117], [114, 20], [40, 5], [60, 112]]]
 h' := ![![[98, 23, 51], [81, 22, 89], [64, 31, 65], [19, 79, 129], [14, 27, 107], [107, 77, 89], [0, 0, 1], [0, 1]], ![[7, 107, 80], [7, 29, 34], [103, 57, 21], [88, 110, 16], [57, 49, 119], [52, 115, 88], [103, 2, 107], [98, 23, 51]], ![[0, 1], [63, 80, 8], [123, 43, 45], [71, 73, 117], [86, 55, 36], [81, 70, 85], [54, 129, 23], [7, 107, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [6, 19], []]
 b := ![[], [125, 17, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [120, 63, 26, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8952802, 3797952, 665742]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![68342, 28992, 5082]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6572, -1597, 346]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-6572, -1597, 346]] 
 ![![137, 0, 0], ![0, 137, 0], ![99, 33, 1]] where
  M :=![![![-6572, -1597, 346], ![54109, 13150, -2848], ![-219403, -53315, 11553]]]
  hmulB := by decide  
  f := ![![![-590, -23, 12]], ![![1909, 94, -34]], ![![16, 6, 1]]]
  g := ![![![-298, -95, 346], ![2453, 782, -2848], ![-9950, -3172, 11553]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [110, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 136], [0, 1]]
 g := ![![[11, 128], [129], [50], [125, 7], [15], [118], [1]], ![[78, 9], [129], [50], [12, 130], [15], [118], [1]]]
 h' := ![![[23, 136], [117, 111], [14, 35], [87, 18], [70, 125], [79, 120], [27, 23], [0, 1]], ![[0, 1], [67, 26], [134, 102], [90, 119], [68, 12], [99, 17], [8, 114], [23, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [88, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [110, 114, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2022, 285, 183]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-147, -42, 183]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![590, 23, -12]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![590, 23, -12]] 
 ![![137, 0, 0], ![70, 1, 0], ![85, 0, 1]] where
  M :=![![![590, 23, -12], ![-1909, -94, 34], ![2395, 3, -71]]]
  hmulB := by decide  
  f := ![![![6572, 1597, -346]], ![![2963, 720, -156]], ![![5679, 1380, -299]]]
  g := ![![![0, 23, -12], ![13, -94, 34], ![60, 3, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-6572, -1597, 346]] ![![590, 23, -12]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB181I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB181I2 : PrimesBelowBoundCertificateInterval O 79 137 181 where
  m := 11
  g := ![2, 2, 1, 2, 3, 3, 2, 3, 3, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB181I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1, I107N2]
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
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![103, 103, 103]
    · exact ![107, 107, 107]
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
      exact NI107N2
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
  β := ![I83N1, I89N1, I101N1, I103N0, I103N1, I103N2, I107N0, I107N1, I107N2, I109N1, I113N0, I113N1, I113N2, I127N0, I127N1, I127N2, I137N1]
  Il := ![[I83N1], [I89N1], [], [I101N1], [I103N0, I103N1, I103N2], [I107N0, I107N1, I107N2], [I109N1], [I113N0, I113N1, I113N2], [I127N0, I127N1, I127N2], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
