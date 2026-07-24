
import IdealArithmetic.Examples.NF3_1_808623_1.RI3_1_808623_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![26, 25, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![26, 25, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![26, 25, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![26, 25, 1], ![127, 87, 123], ![4279, 306, -11]]]
  hmulB := by decide  
  f := ![![![-25, -25, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -25, 83]], ![![0, 0, 1], ![-37, -36, 123], ![55, 7, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [75, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 82], [0, 1]]
 g := ![![[4, 31], [74, 38], [77], [12], [80, 28], [1]], ![[0, 52], [45, 45], [77], [12], [63, 55], [1]]]
 h' := ![![[32, 82], [11, 23], [16, 11], [8, 49], [59, 26], [8, 32], [0, 1]], ![[0, 1], [0, 60], [36, 72], [82, 34], [61, 57], [36, 51], [32, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [78, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [75, 51, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1823, 958, 35]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 1, 35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-40, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-40, 1, 0]] 
 ![![83, 0, 0], ![43, 1, 0], ![11, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-40, 1, 0], ![-2, -38, 5], ![177, 11, -42]]]
  hmulB := by decide  
  f := ![![![-4631, -97901, 12880], ![1079, -213808, 0]], ![![-2387, -50699, 6670], ![582, -110722, 0]], ![![-607, -12975, 1707], ![157, -28336, 0]]]
  g := ![![![1, 0, 0], ![-43, 83, 0], ![-11, 0, 83]], ![![-1, 1, 0], ![19, -38, 5], ![2, 11, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![26, 25, 1]] ![![83, 0, 0], ![-40, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-3320, 83, 0]], ![![2158, 2075, 83], ![-913, -913, 83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-40, 1, 0]]], ![![![26, 25, 1]], ![![-11, -11, 1]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29276, 5337, 1970]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![29276, 5337, 1970]] 
 ![![89, 0, 0], ![0, 89, 0], ![7, 22, 1]] where
  M :=![![![29276, 5337, 1970], ![338016, 61620, 22745], ![657029, 119777, 44212]]]
  hmulB := by decide  
  f := ![![![175, 14, -15]], ![![-2683, 38, 100]], ![![-597, 7, 23]]]
  g := ![![![174, -427, 1970], ![2009, -4930, 22745], ![3905, -9583, 44212]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [35, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 88], [0, 1]]
 g := ![![[79, 4], [67], [10], [40, 80], [26, 36], [1]], ![[55, 85], [67], [10], [5, 9], [77, 53], [1]]]
 h' := ![![[83, 88], [48, 2], [48, 45], [24, 30], [69, 76], [54, 83], [0, 1]], ![[0, 1], [36, 87], [45, 44], [22, 59], [58, 13], [1, 6], [83, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [36, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [35, 6, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12506, 4992, 1748]
  a := ![-5, 2, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-278, -376, 1748]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![175, 14, -15]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![175, 14, -15]] 
 ![![89, 0, 0], ![70, 1, 0], ![24, 0, 1]] where
  M :=![![![175, 14, -15], ![-2683, 38, 100], ![4668, -311, -48]]]
  hmulB := by decide  
  f := ![![![29276, 5337, 1970]], ![![26824, 4890, 1805]], ![![15277, 2785, 1028]]]
  g := ![![![-5, 14, -15], ![-87, 38, 100], ![310, -311, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![29276, 5337, 1970]] ![![175, 14, -15]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![23, 1, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![23, 1, 0]] 
 ![![97, 0, 0], ![23, 1, 0], ![1, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![23, 1, 0], ![-2, 25, 5], ![177, 11, 21]]]
  hmulB := by decide  
  f := ![![![1779, -22802, -4560], ![194, 88464, 0]], ![![409, -5401, -1080], ![98, 20952, 0]], ![![-3, -236, -47], ![92, 912, 0]]]
  g := ![![![1, 0, 0], ![-23, 97, 0], ![-1, 0, 97]], ![![0, 1, 0], ![-6, 25, 5], ![-1, 11, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N0 : Nat.card (O ⧸ I97N0) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N0)

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := prime_ideal_of_norm_prime hp97.out _ NI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![26, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![26, 1, 0]] 
 ![![97, 0, 0], ![26, 1, 0], ![48, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![26, 1, 0], ![-2, 28, 5], ![177, 11, 24]]]
  hmulB := by decide  
  f := ![![![957, -14114, -2520], ![194, 48888, 0]], ![![244, -3781, -675], ![98, 13095, 0]], ![![480, -6984, -1247], ![72, 24192, 0]]]
  g := ![![![1, 0, 0], ![-26, 97, 0], ![-48, 0, 97]], ![![0, 1, 0], ![-10, 28, 5], ![-13, 11, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1

def I97N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![48, 1, 0]] i)))

def SI97N2: IdealEqSpanCertificate' Table ![![97, 0, 0], ![48, 1, 0]] 
 ![![97, 0, 0], ![48, 1, 0], ![24, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![48, 1, 0], ![-2, 50, 5], ![177, 11, 46]]]
  hmulB := by decide  
  f := ![![![13381, -370530, -37050], ![2910, 718770, 0]], ![![6612, -183315, -18330], ![1456, 355602, 0]], ![![3288, -91678, -9167], ![766, 177840, 0]]]
  g := ![![![1, 0, 0], ![-48, 97, 0], ![-24, 0, 97]], ![![0, 1, 0], ![-26, 50, 5], ![-15, 11, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N2 : Nat.card (O ⧸ I97N2) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N2)

lemma isPrimeI97N2 : Ideal.IsPrime I97N2 := prime_ideal_of_norm_prime hp97.out _ NI97N2
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![23, 1, 0]] ![![97, 0, 0], ![26, 1, 0]]
  ![![97, 0, 0], ![-36, -48, 1]] where
 M := ![![![9409, 0, 0], ![2522, 97, 0]], ![![2231, 97, 0], ![596, 51, 5]]]
 hmul := by decide  
 g := ![![![![97, 0, 0], ![0, 0, 0]], ![![26, 1, 0], ![0, 0, 0]]], ![![![23, 1, 0], ![0, 0, 0]], ![![8, 3, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI97N1 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-36, -48, 1]] ![![97, 0, 0], ![48, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![4656, 97, 0]], ![![-3492, -4656, 97], ![-1455, -2425, -194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![48, 1, 0]]], ![![![-36, -48, 1]], ![![-15, -25, -2]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1, I97N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
    exact isPrimeI97N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0 ⊙ MulI97N1)
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [60, 15, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [59, 10, 59], [57, 90, 42], [0, 1]]
 g := ![![[31, 1, 64], [62, 4], [30, 24, 82], [83, 85], [97, 23], [1]], ![[19, 16, 40, 27], [71, 31], [25, 8, 40, 73], [38, 16], [18, 85], [57, 67, 80, 46]], ![[79, 14, 89, 11], [4, 65], [12, 89, 11, 41], [75, 17], [60, 19], [60, 54, 82, 55]]]
 h' := ![![[59, 10, 59], [38, 60, 8], [18, 51, 2], [74, 19, 48], [2, 76, 40], [41, 86, 15], [0, 1]], ![[57, 90, 42], [74, 44, 18], [30, 68, 58], [68, 86, 88], [96, 0, 4], [60, 70, 61], [59, 10, 59]], ![[0, 1], [38, 98, 75], [50, 83, 41], [29, 97, 66], [61, 25, 57], [96, 46, 25], [57, 90, 42]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33, 66], []]
 b := ![[], [88, 60, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [60, 15, 86, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-58323351021, -7930654936, -2086317004]
  a := ![66, -129, -197]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-577458921, -78521336, -20656604]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![5, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![5, 1, 0]] 
 ![![103, 0, 0], ![5, 1, 0], ![75, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![5, 1, 0], ![-2, 7, 5], ![177, 11, 3]]]
  hmulB := by decide  
  f := ![![![1360, -4775, -3410], ![103, 70246, 0]], ![![66, -231, -165], ![1, 3399, 0]], ![![990, -3477, -2483], ![81, 51150, 0]]]
  g := ![![![1, 0, 0], ![-5, 103, 0], ![-75, 0, 103]], ![![0, 1, 0], ![-4, 7, 5], ![-1, 11, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![41, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![41, 1, 0]] 
 ![![103, 0, 0], ![41, 1, 0], ![59, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![41, 1, 0], ![-2, 43, 5], ![177, 11, 39]]]
  hmulB := by decide  
  f := ![![![14264, -328717, -38220], ![2575, 787332, 0]], ![![5674, -130816, -15210], ![1031, 313326, 0]], ![![8179, -188294, -21893], ![1454, 450996, 0]]]
  g := ![![![1, 0, 0], ![-41, 103, 0], ![-59, 0, 103]], ![![0, 1, 0], ![-20, 43, 5], ![-25, 11, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-46, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-46, 1, 0]] 
 ![![103, 0, 0], ![57, 1, 0], ![48, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-46, 1, 0], ![-2, -44, 5], ![177, 11, -48]]]
  hmulB := by decide  
  f := ![![![-5793, -140637, 15980], ![1339, -329188, 0]], ![![-3213, -77799, 8840], ![722, -182104, 0]], ![![-2680, -65540, 7447], ![668, -153408, 0]]]
  g := ![![![1, 0, 0], ![-57, 103, 0], ![-48, 0, 103]], ![![-1, 1, 0], ![22, -44, 5], ![18, 11, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![5, 1, 0]] ![![103, 0, 0], ![41, 1, 0]]
  ![![103, 0, 0], ![20, -11, 1]] where
 M := ![![![10609, 0, 0], ![4223, 103, 0]], ![![515, 103, 0], ![203, 48, 5]]]
 hmul := by decide  
 g := ![![![![83, 11, -1], ![103, 0, 0]], ![![21, 12, -1], ![103, 0, 0]]], ![![![-15, 12, -1], ![103, 0, 0]], ![![1, 1, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![20, -11, 1]] ![![103, 0, 0], ![-46, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4738, 103, 0]], ![![2060, -1133, 103], ![-721, 515, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-46, 1, 0]]], ![![![20, -11, 1]], ![![-7, 5, -1]]]]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [10, 92, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [101, 32, 20], [54, 74, 87], [0, 1]]
 g := ![![[22, 16, 37], [28, 75, 79], [20, 44], [32, 50, 39], [3, 57], [1]], ![[52, 28, 45, 103], [27, 45, 43, 106], [65, 14], [4, 66, 29, 7], [], [82, 28, 71, 82]], ![[51, 99, 58, 1], [38, 35, 32, 16], [69, 40], [22, 23, 88, 105], [8, 57], [4, 31, 13, 25]]]
 h' := ![![[101, 32, 20], [41, 2, 95], [15, 97, 20], [1, 65, 30], [70, 31, 50], [97, 15, 48], [0, 1]], ![[54, 74, 87], [49, 99, 8], [6, 14, 103], [96, 13, 96], [86, 8, 40], [34, 19], [101, 32, 20]], ![[0, 1], [48, 6, 4], [0, 103, 91], [72, 29, 88], [7, 68, 17], [27, 73, 59], [54, 74, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 76], []]
 b := ![[], [63, 81, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [10, 92, 59, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9617481, -1032978, 3210]
  a := ![5, -3, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-89883, -9654, 30]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [13, 4, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 70, 22], [41, 38, 87], [0, 1]]
 g := ![![[79, 12, 108], [55, 73], [36, 4, 106], [107, 25, 26], [24, 25], [1]], ![[59, 68, 95, 1], [29, 100], [45, 27, 29, 97], [14, 108, 3, 28], [66, 3], [100, 29, 4, 75]], ![[20, 87, 23, 49], [6, 28], [74, 47, 32, 63], [61, 82, 55, 45], [2, 83], [27, 39, 70, 34]]]
 h' := ![![[63, 70, 22], [91, 48, 33], [77, 44, 89], [26, 76, 91], [75, 10, 35], [96, 105, 104], [0, 1]], ![[41, 38, 87], [64, 100, 21], [21, 88, 99], [67, 33, 7], [95, 50, 24], [9, 62, 49], [63, 70, 22]], ![[0, 1], [3, 70, 55], [9, 86, 30], [62, 0, 11], [55, 49, 50], [9, 51, 65], [41, 38, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 5], []]
 b := ![[], [102, 46, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [13, 4, 5, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-907316, -119464, -28885]
  a := ![2, -3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8324, -1096, -265]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-47, -28, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-47, -28, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![66, 85, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-47, -28, 1], ![233, -92, -142], ![-5102, -277, 22]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -85, 113]], ![![-1, -1, 1], ![85, 106, -142], ![-58, -19, 22]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [17, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [112, 112], [0, 1]]
 g := ![![[20, 25], [99], [61], [83], [104, 30], [112, 1]], ![[108, 88], [99], [61], [83], [74, 83], [111, 112]]]
 h' := ![![[112, 112], [61, 5], [106, 41], [76, 20], [40, 14], [17, 97], [0, 1]], ![[0, 1], [56, 108], [65, 72], [56, 93], [26, 99], [33, 16], [112, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [27, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [17, 1, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![54757, 6975, 2701]
  a := ![-3, 23, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1093, -1970, 2701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![29, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![29, 1, 0]] 
 ![![113, 0, 0], ![29, 1, 0], ![91, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![29, 1, 0], ![-2, 31, 5], ![177, 11, 27]]]
  hmulB := by decide  
  f := ![![![-2125, 33854, 5460], ![-226, -123396, 0]], ![![-560, 8680, 1400], ![1, -31640, 0]], ![![-1710, 27263, 4397], ![-187, -99372, 0]]]
  g := ![![![1, 0, 0], ![-29, 113, 0], ![-91, 0, 113]], ![![0, 1, 0], ![-12, 31, 5], ![-23, 11, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-47, -28, 1]] ![![113, 0, 0], ![29, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![3277, 113, 0]], ![![-5311, -3164, 113], ![-1130, -904, -113]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![29, 1, 0]]], ![![![-47, -28, 1]], ![![-10, -8, -1]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [22, 19, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 115, 45], [90, 11, 82], [0, 1]]
 g := ![![[99, 107, 68], [101, 26, 11], [107, 38, 15], [62, 114, 113], [92, 121, 88], [1]], ![[109, 122, 69, 10], [90, 118, 117, 57], [100, 58, 17, 67], [106, 72, 80, 110], [92, 61, 108, 40], [73, 121, 112, 66]], ![[63, 95, 120, 68], [96, 80, 97, 37], [119, 49, 99, 79], [39, 21, 31, 38], [7, 20, 72, 103], [3, 63, 36, 61]]]
 h' := ![![[108, 115, 45], [64, 101, 103], [59, 125, 30], [33, 61, 53], [8, 11, 85], [105, 108, 71], [0, 1]], ![[90, 11, 82], [105, 112, 90], [60, 20, 113], [49, 6, 26], [54, 26, 33], [44, 100, 53], [108, 115, 45]], ![[0, 1], [25, 41, 61], [19, 109, 111], [13, 60, 48], [40, 90, 9], [81, 46, 3], [90, 11, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 122], []]
 b := ![[], [101, 30, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [22, 19, 56, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2682113, -256413, 43053]
  a := ![3, -1, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21119, -2019, 339]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![10, -34, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![10, -34, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![10, 97, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![10, -34, 1], ![245, -47, -172], ![-6164, -343, 91]]]
  hmulB := by decide  
  f := ![![![-9, 34, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -97, 131]], ![![0, -1, 1], ![15, 127, -172], ![-54, -70, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [67, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [51, 130], [0, 1]]
 g := ![![[97, 4], [127, 48], [36], [62], [105], [112], [1]], ![[39, 127], [86, 83], [36], [62], [105], [112], [1]]]
 h' := ![![[51, 130], [6, 2], [4, 21], [53, 125], [43, 18], [129, 57], [64, 51], [0, 1]], ![[0, 1], [108, 129], [27, 110], [9, 6], [44, 113], [23, 74], [45, 80], [51, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [108, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [67, 80, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2813, 4610, 1945]
  a := ![-4, 5, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-127, -1405, 1945]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![41, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![41, 1, 0]] 
 ![![131, 0, 0], ![41, 1, 0], ![40, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![41, 1, 0], ![-2, 43, 5], ![177, 11, 39]]]
  hmulB := by decide  
  f := ![![![-223, 4816, 560], ![0, -14672, 0]], ![![-70, 1505, 175], ![1, -4585, 0]], ![![-90, 1470, 171], ![70, -4480, 0]]]
  g := ![![![1, 0, 0], ![-41, 131, 0], ![-40, 0, 131]], ![![0, 1, 0], ![-15, 43, 5], ![-14, 11, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![10, -34, 1]] ![![131, 0, 0], ![41, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![5371, 131, 0]], ![![1310, -4454, 131], ![655, -1441, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![41, 1, 0]]], ![![![10, -34, 1]], ![![5, -11, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![22, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![22, 1, 0]] 
 ![![137, 0, 0], ![22, 1, 0], ![31, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![22, 1, 0], ![-2, 24, 5], ![177, 11, 20]]]
  hmulB := by decide  
  f := ![![![19685, -239123, -49815], ![1507, 1364931, 0]], ![![3154, -38378, -7995], ![275, 219063, 0]], ![![4457, -54108, -11272], ![324, 308853, 0]]]
  g := ![![![1, 0, 0], ![-22, 137, 0], ![-31, 0, 137]], ![![0, 1, 0], ![-5, 24, 5], ![-5, 11, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![56, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![56, 1, 0]] 
 ![![137, 0, 0], ![56, 1, 0], ![35, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![56, 1, 0], ![-2, 58, 5], ![177, 11, 54]]]
  hmulB := by decide  
  f := ![![![18841, -586985, -50600], ![3425, 1386440, 0]], ![![7656, -239899, -20680], ![1508, 566632, 0]], ![![4795, -149960, -12927], ![920, 354200, 0]]]
  g := ![![![1, 0, 0], ![-56, 137, 0], ![-35, 0, 137]], ![![0, 1, 0], ![-25, 58, 5], ![-17, 11, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![59, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![59, 1, 0]] 
 ![![137, 0, 0], ![59, 1, 0], ![47, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![59, 1, 0], ![-2, 61, 5], ![177, 11, 57]]]
  hmulB := by decide  
  f := ![![![230, -8785, -720], ![137, 19728, 0]], ![![65, -3783, -310], ![138, 8494, 0]], ![![69, -3014, -247], ![70, 6768, 0]]]
  g := ![![![1, 0, 0], ![-59, 137, 0], ![-47, 0, 137]], ![![0, 1, 0], ![-28, 61, 5], ![-23, 11, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![22, 1, 0]] ![![137, 0, 0], ![56, 1, 0]]
  ![![137, 0, 0], ![-28, 16, 1]] where
 M := ![![![18769, 0, 0], ![7672, 137, 0]], ![![3014, 137, 0], ![1230, 80, 5]]]
 hmul := by decide  
 g := ![![![![137, 0, 0], ![0, 0, 0]], ![![56, 1, 0], ![0, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![10, 0, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-28, 16, 1]] ![![137, 0, 0], ![59, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![8083, 137, 0]], ![![-3836, 2192, 137], ![-1507, 959, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![59, 1, 0]]], ![![![-28, 16, 1]], ![![-11, 7, 1]]]]
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


lemma PB255I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB255I2 : PrimesBelowBoundCertificateInterval O 79 137 255 where
  m := 11
  g := ![2, 2, 3, 1, 3, 1, 1, 2, 1, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB255I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1, I97N2]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0]
    · exact ![I109N0]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0, I131N1]
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
    · exact ![97, 97, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![1225043]
    · exact ![1295029]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![17161, 131]
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
      exact NI97N1
      exact NI97N2
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
      exact NI137N2
  β := ![I83N1, I89N1, I97N0, I97N1, I97N2, I103N0, I103N1, I103N2, I113N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [I97N0, I97N1, I97N2], [], [I103N0, I103N1, I103N2], [], [], [I113N1], [], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
