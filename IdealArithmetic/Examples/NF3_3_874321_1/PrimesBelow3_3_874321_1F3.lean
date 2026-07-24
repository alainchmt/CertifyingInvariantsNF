
import IdealArithmetic.Examples.NF3_3_874321_1.RI3_3_874321_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 28, 6]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![61, 28, 6]] 
 ![![139, 0, 0], ![43, 1, 0], ![18, 0, 1]] where
  M :=![![![61, 28, 6], ![1062, 413, 84], ![4602, 1866, 385]]]
  hmulB := by decide  
  f := ![![![-2261, -416, 126]], ![![-539, -99, 30]], ![![-876, -162, 49]]]
  g := ![![![-9, 28, 6], ![-131, 413, 84], ![-594, 1866, 385]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![12, 5, 1]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![12, 5, 1]] 
 ![![139, 0, 0], ![105, 1, 0], ![43, 0, 1]] where
  M :=![![![12, 5, 1], ![177, 71, 15], ![826, 329, 66]]]
  hmulB := by decide  
  f := ![![![-249, -1, 4]], ![![-183, -1, 3]], ![![-80, 1, 1]]]
  g := ![![![-4, 5, 1], ![-57, 71, 15], ![-263, 329, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-38, -15, -3]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-38, -15, -3]] 
 ![![139, 0, 0], ![129, 1, 0], ![109, 0, 1]] where
  M :=![![![-38, -15, -3], ![-531, -215, -45], ![-2478, -987, -200]]]
  hmulB := by decide  
  f := ![![![-1415, -39, 30]], ![![-1275, -35, 27]], ![![-1172, -33, 25]]]
  g := ![![![16, -15, -3], ![231, -215, -45], ![1055, -987, -200]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![61, 28, 6]] ![![12, 5, 1]]
  ![![10644, 4267, 877]] where
 M := ![![![10644, 4267, 877]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![10644, 4267, 877]] ![![-38, -15, -3]]
  ![![139, 0, 0]] where
 M := ![![![-4843455, -1942664, -399347]]]
 hmul := by decide  
 g := ![![![![-34845, -13976, -2873]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![710932, 17979, -14718]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![710932, 17979, -14718]] 
 ![![149, 0, 0], ![0, 149, 0], ![119, 3, 1]] where
  M :=![![![710932, 17979, -14718], ![-2605086, -65861, 53937], ![4050645, 102504, -83840]]]
  hmulB := by decide  
  f := ![![![-46792, -8688, 2625]], ![![464625, 86270, -26064]], ![![-39376, -7311, 2209]]]
  g := ![![![16526, 417, -14718], ![-60561, -1528, 53937], ![94145, 2376, -83840]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [93, 106, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 148], [0, 1]]
 g := ![![[46, 49], [4], [60, 63], [118], [76, 121], [61], [1]], ![[67, 100], [4], [87, 86], [118], [64, 28], [61], [1]]]
 h' := ![![[43, 148], [94, 142], [82, 147], [105, 130], [84, 77], [145, 138], [56, 43], [0, 1]], ![[0, 1], [91, 7], [145, 2], [33, 19], [117, 72], [119, 11], [117, 106], [43, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [54, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [93, 106, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2158, 2347, 832]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-650, -1, 832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46792, -8688, 2625]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-46792, -8688, 2625]] 
 ![![149, 0, 0], ![140, 1, 0], ![125, 0, 1]] where
  M :=![![![-46792, -8688, 2625], ![464625, 86270, -26064], ![-1692651, -314277, 94958]]]
  hmulB := by decide  
  f := ![![![710932, 17979, -14718]], ![![650506, 16451, -13467]], ![![623605, 15771, -12910]]]
  g := ![![![5647, -8688, 2625], ![-56075, 86270, -26064], ![204271, -314277, 94958]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![710932, 17979, -14718]] ![![-46792, -8688, 2625]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3797, 705, -213]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![3797, 705, -213]] 
 ![![151, 0, 0], ![71, 1, 0], ![108, 0, 1]] where
  M :=![![![3797, 705, -213], ![-37701, -7000, 2115], ![137352, 25503, -7705]]]
  hmulB := by decide  
  f := ![![![3845, 114, -75]], ![![1720, 53, -33]], ![![2913, 93, -55]]]
  g := ![![![-154, 705, -213], ![1529, -7000, 2115], ![-5571, 25503, -7705]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2221, 816, 135]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![2221, 816, 135]] 
 ![![151, 0, 0], ![104, 1, 0], ![135, 0, 1]] where
  M :=![![![2221, 816, 135], ![23895, 10327, 2448], ![136467, 52029, 9511]]]
  hmulB := by decide  
  f := ![![![-29146895, -737061, 603423]], ![![-19367359, -489758, 400959]], ![![-27158229, -686772, 562252]]]
  g := ![![![-668, 816, 135], ![-9143, 10327, 2448], ![-43434, 52029, 9511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![265, 49, -15]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![265, 49, -15]] 
 ![![151, 0, 0], ![126, 1, 0], ![102, 0, 1]] where
  M :=![![![265, 49, -15], ![-2655, -496, 147], ![9558, 1761, -545]]]
  hmulB := by decide  
  f := ![![![-11453, -290, 237]], ![![-9279, -235, 192]], ![![-8169, -207, 169]]]
  g := ![![![-29, 49, -15], ![297, -496, 147], ![-1038, 1761, -545]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![3797, 705, -213]] ![![2221, 816, 135]]
  ![![-3788359, -703290, 212592]] where
 M := ![![![-3788359, -703290, 212592]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-3788359, -703290, 212592]] ![![265, 49, -15]]
  ![![151, 0, 0]] where
 M := ![![![2895274151, 537576761, -162420885]]]
 hmul := by decide  
 g := ![![![![19174001, 3560111, -1075635]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [66, 99, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 36, 1], [81, 120, 156], [0, 1]]
 g := ![![[24, 99, 143], [81, 156], [111, 149, 1], [151, 47, 17], [85, 61, 36], [67, 1], []], ![[63, 25, 65, 49], [29, 82], [65, 156, 123, 16], [1, 40, 154, 35], [122, 92, 60, 30], [81, 113], [139, 1]], ![[84, 64, 10, 90], [113, 146], [120, 82, 113, 132], [49, 74, 98, 100], [87, 43, 76, 82], [60, 40], [141, 1]]]
 h' := ![![[143, 36, 1], [132, 43, 65], [53, 31, 129], [82, 41, 1], [42, 10, 71], [131, 52, 151], [0, 0, 1], [0, 1]], ![[81, 120, 156], [0, 154, 150], [117, 132, 125], [107, 143, 4], [41, 74, 52], [48, 136, 117], [128, 80, 120], [143, 36, 1]], ![[0, 1], [88, 117, 99], [139, 151, 60], [30, 130, 152], [9, 73, 34], [89, 126, 46], [81, 77, 36], [81, 120, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 65], []]
 b := ![[], [87, 77, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [66, 99, 90, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1650227, 1194142, 490154]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10511, 7606, 3122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [142, 73, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 67, 119], [51, 95, 44], [0, 1]]
 g := ![![[123, 117, 21], [72, 11, 69], [11, 83], [105, 131], [53, 145], [114, 26, 1], []], ![[50, 57, 75, 118], [158, 91, 58, 15], [114, 145], [128, 4], [105, 10], [87, 99, 117, 131], [104, 143]], ![[32, 70, 0, 59], [90, 50, 9, 107], [150, 115], [49, 97], [30, 54], [38, 68, 108, 123], [16, 143]]]
 h' := ![![[138, 67, 119], [45, 25, 99], [117, 145, 45], [7, 48, 88], [128, 148, 72], [112, 48, 109], [0, 0, 1], [0, 1]], ![[51, 95, 44], [85, 70, 155], [158, 139, 14], [32, 105, 54], [142, 6, 2], [120, 135, 93], [38, 48, 95], [138, 67, 119]], ![[0, 1], [150, 68, 72], [149, 42, 104], [111, 10, 21], [68, 9, 89], [116, 143, 124], [3, 115, 67], [51, 95, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 20], []]
 b := ![[], [70, 63, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [142, 73, 137, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![290466, -9617, -652]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1782, -59, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [136, 163, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [30, 145, 39], [50, 21, 128], [0, 1]]
 g := ![![[71, 114, 32], [97, 100, 32], [96, 125, 19], [138, 32], [139, 27], [58, 80, 1], []], ![[82, 108, 73, 161], [115, 137, 40, 35], [15, 69], [58, 124], [30, 64], [3, 48, 84, 165], [58, 18]], ![[118, 95, 44, 56], [110, 95, 18, 100], [63, 148, 71, 94], [92, 61], [112, 61], [68, 43, 76, 162], [136, 18]]]
 h' := ![![[30, 145, 39], [1, 46, 115], [137, 120, 115], [161, 81, 112], [152, 110, 115], [128, 40, 148], [0, 0, 1], [0, 1]], ![[50, 21, 128], [29, 162, 34], [47, 37, 81], [159, 147], [96, 90, 25], [166, 5, 159], [26, 138, 21], [30, 145, 39]], ![[0, 1], [95, 126, 18], [90, 10, 138], [60, 106, 55], [106, 134, 27], [108, 122, 27], [36, 29, 145], [50, 21, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 29], []]
 b := ![[], [5, 135, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [136, 163, 87, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5117214, -2667658, -808781]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30642, -15974, -4843]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [138, 103, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 37, 36], [117, 135, 137], [0, 1]]
 g := ![![[169, 39, 158], [15, 167], [60, 155, 49], [130, 89, 34], [50, 122], [80, 150, 1], []], ![[170, 129, 152, 38], [71, 34], [35, 144, 121, 96], [3, 170, 46, 29], [5, 23], [105, 80, 133, 84], [17, 85]], ![[47, 100, 164, 4], [110, 35], [82, 7, 90, 52], [137, 1, 67, 90], [22, 96], [115, 116, 115, 21], [89, 85]]]
 h' := ![![[33, 37, 36], [63, 107, 136], [24, 46, 72], [52, 141, 7], [6, 136, 42], [32, 124, 45], [0, 0, 1], [0, 1]], ![[117, 135, 137], [106, 143, 68], [133, 99, 131], [58, 85, 139], [140, 17, 13], [151, 18, 159], [127, 33, 135], [33, 37, 36]], ![[0, 1], [140, 96, 142], [142, 28, 143], [102, 120, 27], [103, 20, 118], [5, 31, 142], [23, 140, 37], [117, 135, 137]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 99], []]
 b := ![[], [104, 16, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [138, 103, 23, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2297440, -1190413, -362608]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13280, -6881, -2096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [104, 174, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 96, 148], [82, 82, 31], [0, 1]]
 g := ![![[32, 138, 146], [176, 88, 161], [78, 156], [78, 101], [86, 162, 13], [44, 155, 1], []], ![[9, 72, 125, 113], [8, 79, 161, 164], [170, 68], [164, 56], [72, 154, 155, 78], [113, 19, 69, 91], [161, 66]], ![[78, 19, 56, 93], [128, 173, 31, 101], [163, 48], [45, 19], [11, 44, 21, 49], [48, 161, 158, 12], [99, 66]]]
 h' := ![![[73, 96, 148], [133, 101, 135], [26, 91, 124], [158, 128, 131], [6, 48, 82], [78, 31, 152], [0, 0, 1], [0, 1]], ![[82, 82, 31], [153, 46, 63], [118, 164, 8], [16, 166, 151], [70, 152, 45], [160, 73, 47], [41, 81, 82], [73, 96, 148]], ![[0, 1], [8, 32, 160], [67, 103, 47], [67, 64, 76], [123, 158, 52], [77, 75, 159], [8, 98, 96], [82, 82, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [172, 142], []]
 b := ![[], [86, 161, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [104, 174, 24, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1473587607, 751025825, 225246440]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8232333, 4195675, 1258360]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3193, 81, -66]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![3193, 81, -66]] 
 ![![181, 0, 0], ![0, 181, 0], ![86, 7, 1]] where
  M :=![![![3193, 81, -66], ![-11682, -290, 243], ![18231, 480, -371]]]
  hmulB := by decide  
  f := ![![![-50, -9, 3]], ![![531, 103, -27]], ![![-13, -2, 1]]]
  g := ![![![49, 3, -66], ![-180, -11, 243], ![277, 17, -371]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [78, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 180], [0, 1]]
 g := ![![[141, 60], [148], [60, 101], [178], [170, 80], [37, 39], [1]], ![[6, 121], [148], [59, 80], [178], [171, 101], [85, 142], [1]]]
 h' := ![![[43, 180], [173, 28], [26, 87], [90, 120], [134, 84], [10, 108], [103, 43], [0, 1]], ![[0, 1], [110, 153], [147, 94], [1, 61], [126, 97], [129, 73], [142, 138], [43, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [92, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [78, 138, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1534, 1455, 906]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-422, -27, 906]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50, 9, -3]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![50, 9, -3]] 
 ![![181, 0, 0], ![160, 1, 0], ![41, 0, 1]] where
  M :=![![![50, 9, -3], ![-531, -103, 27], ![1770, 309, -112]]]
  hmulB := by decide  
  f := ![![![-3193, -81, 66]], ![![-2758, -70, 57]], ![![-824, -21, 17]]]
  g := ![![![-7, 9, -3], ![82, -103, 27], ![-238, 309, -112]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![3193, 81, -66]] ![![50, 9, -3]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1209159, 30577, -25033]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![1209159, 30577, -25033]] 
 ![![191, 0, 0], ![0, 191, 0], ![37, 110, 1]] where
  M :=![![![1209159, 30577, -25033], ![-4430841, -112046, 91731], ![6889076, 174211, -142623]]]
  hmulB := by decide  
  f := ![![![1113, 212, -59]], ![![-10443, -1861, 636]], ![![-5584, -989, 344]]]
  g := ![![![11180, 14577, -25033], ![-40968, -53416, 91731], ![63697, 83051, -142623]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [159, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 190], [0, 1]]
 g := ![![[51, 108], [30, 43], [127, 115], [114, 27], [160, 169], [36, 120], [1]], ![[14, 83], [109, 148], [54, 76], [57, 164], [164, 22], [101, 71], [1]]]
 h' := ![![[104, 190], [5, 47], [53, 59], [19, 146], [154, 119], [6, 13], [32, 104], [0, 1]], ![[0, 1], [118, 144], [77, 132], [114, 45], [115, 72], [21, 178], [152, 87], [104, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [99, 134]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [159, 87, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4879, 6638, 4179]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-784, -2372, 4179]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1113, -212, 59]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-1113, -212, 59]] 
 ![![191, 0, 0], ![52, 1, 0], ![100, 0, 1]] where
  M :=![![![-1113, -212, 59], ![10443, 1861, -636], ![-41005, -7967, 2073]]]
  hmulB := by decide  
  f := ![![![-1209159, -30577, 25033]], ![![-305997, -7738, 6335]], ![![-669136, -16921, 13853]]]
  g := ![![![21, -212, 59], ![-119, 1861, -636], ![869, -7967, 2073]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![1209159, 30577, -25033]] ![![-1113, -212, 59]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [179, 53, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 176, 136], [11, 16, 57], [0, 1]]
 g := ![![[153, 171, 16], [164, 124], [110, 1], [22, 67], [190, 50], [81, 128], [1]], ![[109, 185, 174, 11], [73, 187], [19, 2], [84, 126], [144, 175], [57, 150], [134, 189, 189, 87]], ![[152, 2, 122, 125], [149, 75], [167, 107], [102, 46], [164, 67], [152, 161], [154, 151, 100, 106]]]
 h' := ![![[19, 176, 136], [78, 111, 189], [171, 28, 33], [91, 153, 192], [13, 126, 35], [172, 68, 67], [14, 140, 30], [0, 1]], ![[11, 16, 57], [15, 34, 171], [94, 129, 90], [139, 147, 141], [182, 108, 133], [17, 8, 91], [50, 100, 27], [19, 176, 136]], ![[0, 1], [102, 48, 26], [77, 36, 70], [172, 86, 53], [148, 152, 25], [174, 117, 35], [13, 146, 136], [11, 16, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 28], []]
 b := ![[], [130, 11, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [179, 53, 163, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-60398771, -27902396, -7298102]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-312947, -144572, -37814]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB208I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB208I3 : PrimesBelowBoundCertificateInterval O 137 193 208 where
  m := 11
  g := ![3, 2, 3, 1, 1, 1, 1, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB208I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![7189057]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I149N1, I151N0, I151N1, I151N2, I181N1, I191N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N0, I151N1, I151N2], [], [], [], [], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
