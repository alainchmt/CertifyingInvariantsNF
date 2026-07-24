
import IdealArithmetic.Examples.NF3_1_933907_1.RI3_1_933907_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![60, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![60, 1, 0]] 
 ![![139, 0, 0], ![60, 1, 0], ![116, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![60, 1, 0], ![0, 61, 2], ![-754, 117, 60]]]
  hmulB := by decide  
  f := ![![![2701, 45, 0], ![-6255, 0, 0]], ![![1140, 19, 0], ![-2640, 0, 0]], ![![2204, 6, -1], ![-5104, 70, 0]]]
  g := ![![![1, 0, 0], ![-60, 139, 0], ![-116, 0, 139]], ![![0, 1, 0], ![-28, 61, 2], ![-106, 117, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-33, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-33, 1, 0]] 
 ![![139, 0, 0], ![106, 1, 0], ![28, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-33, 1, 0], ![0, -32, 2], ![-754, 117, -33]]]
  hmulB := by decide  
  f := ![![![3004, -91, 0], ![12649, 0, 0]], ![![2344, -71, 0], ![9870, 0, 0]], ![![664, -4, -1], ![2796, 70, 0]]]
  g := ![![![1, 0, 0], ![-106, 139, 0], ![-28, 0, 139]], ![![-1, 1, 0], ![24, -32, 2], ![-88, 117, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-28, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-28, 1, 0]] 
 ![![139, 0, 0], ![111, 1, 0], ![39, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-28, 1, 0], ![0, -27, 2], ![-754, 117, -28]]]
  hmulB := by decide  
  f := ![![![1205, -43, 0], ![5977, 0, 0]], ![![953, -34, 0], ![4727, 0, 0]], ![![353, 1, -1], ![1751, 70, 0]]]
  g := ![![![1, 0, 0], ![-111, 139, 0], ![-39, 0, 139]], ![![-1, 1, 0], ![21, -27, 2], ![-91, 117, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![60, 1, 0]] ![![139, 0, 0], ![-33, 1, 0]]
  ![![139, 0, 0], ![-17, 14, 1]] where
 M := ![![![19321, 0, 0], ![-4587, 139, 0]], ![![8340, 139, 0], ![-1980, 28, 2]]]
 hmul := by decide  
 g := ![![![![139, 0, 0], ![0, 0, 0]], ![![-16, -13, -1], ![139, 0, 0]]], ![![![60, 1, 0], ![0, 0, 0]], ![![-14, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-17, 14, 1]] ![![139, 0, 0], ![-28, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-3892, 139, 0]], ![![-2363, 1946, 139], ![-278, -278, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-28, 1, 0]]], ![![![-17, 14, 1]], ![![-2, -2, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [12, 89, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [138, 148, 112], [52, 0, 37], [0, 1]]
 g := ![![[63, 5, 110], [22, 127], [22, 101, 17], [97, 143], [100, 70, 123], [41, 1], []], ![[9, 59, 132, 116], [56, 120], [136, 68], [143, 96], [36, 75, 82, 64], [], [30, 28]], ![[143, 41, 126, 17], [76, 31], [54, 138, 46, 33], [94, 64], [84, 4, 104, 95], [33, 1], [105, 28]]]
 h' := ![![[138, 148, 112], [147, 102, 40], [34, 79, 53], [92, 0, 49], [141, 33, 21], [104, 64, 102], [0, 0, 1], [0, 1]], ![[52, 0, 37], [44, 36, 100], [57, 7, 57], [3, 102], [123, 32, 120], [54, 124, 16], [59, 145], [138, 148, 112]], ![[0, 1], [35, 11, 9], [65, 63, 39], [73, 47, 100], [146, 84, 8], [81, 110, 31], [103, 4, 148], [52, 0, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 21], []]
 b := ![[], [51, 2, 65], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [12, 89, 108, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4700801, 1449174, -233185]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-31549, 9726, -1565]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-99, -45, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-99, -45, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![52, 106, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-99, -45, 1], ![-754, -27, -90], ![34307, -5642, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -106, 151]], ![![-1, -1, 1], ![26, 63, -90], ![221, -50, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [81, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 150], [0, 1]]
 g := ![![[115, 110], [4, 45], [150, 8], [97], [32, 31], [95], [1]], ![[0, 41], [5, 106], [73, 143], [97], [130, 120], [95], [1]]]
 h' := ![![[47, 150], [129, 84], [81, 14], [16, 59], [126, 90], [74, 22], [70, 47], [0, 1]], ![[0, 1], [0, 67], [135, 137], [71, 92], [128, 61], [51, 129], [14, 104], [47, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [102, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [81, 104, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22, -4993, 2282]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-786, -1635, 2282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-61, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-61, 1, 0]] 
 ![![151, 0, 0], ![90, 1, 0], ![133, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-61, 1, 0], ![0, -60, 2], ![-754, 117, -61]]]
  hmulB := by decide  
  f := ![![![5247, -86, 0], ![12986, 0, 0]], ![![3112, -51, 0], ![7702, 0, 0]], ![![4649, -46, -1], ![11506, 76, 0]]]
  g := ![![![1, 0, 0], ![-90, 151, 0], ![-133, 0, 151]], ![![-1, 1, 0], ![34, -60, 2], ![-21, 117, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-99, -45, 1]] ![![151, 0, 0], ![-61, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-9211, 151, 0]], ![![-14949, -6795, 151], ![5285, 2718, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-61, 1, 0]]], ![![![-99, -45, 1]], ![![35, 18, -1]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [115, 131, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 27, 63], [92, 129, 94], [0, 1]]
 g := ![![[40, 36, 132], [67, 12], [0, 76, 106], [24, 113, 124], [37, 9, 100], [45, 1], []], ![[101, 30, 21, 8], [26, 118], [6, 152, 151, 63], [46, 103, 34, 103], [133, 13, 4, 73], [122, 156], [44, 44]], ![[72, 14, 86, 129], [133, 117], [26, 1, 112, 85], [143, 44, 75, 29], [150, 67, 77, 26], [125, 101], [13, 44]]]
 h' := ![![[110, 27, 63], [145, 48, 17], [0, 12, 13], [66, 131, 48], [141, 120, 76], [6, 113, 10], [0, 0, 1], [0, 1]], ![[92, 129, 94], [133, 65, 36], [53, 103, 78], [88, 52, 1], [137, 64, 94], [97, 55, 88], [132, 140, 129], [110, 27, 63]], ![[0, 1], [103, 44, 104], [13, 42, 66], [131, 131, 108], [117, 130, 144], [22, 146, 59], [61, 17, 27], [92, 129, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 50], []]
 b := ![[], [128, 54, 64], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [115, 131, 112, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-170188, 118378, -21509]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1084, 754, -137]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [116, 92, 28, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 141, 62], [90, 21, 101], [0, 1]]
 g := ![![[105, 78, 100], [81, 9, 1], [135, 156], [106, 60], [90, 155], [40, 135, 1], []], ![[83, 68, 107, 152], [122, 0, 68, 47], [137, 64], [5, 84], [128, 96], [82, 26, 64, 121], [154, 95]], ![[124, 65, 69, 20], [31, 107, 33, 129], [69, 56], [57, 111], [73, 83], [37, 30, 14, 147], [115, 95]]]
 h' := ![![[45, 141, 62], [58, 95, 10], [21, 100, 1], [149, 1, 51], [63, 121, 68], [87, 57, 36], [0, 0, 1], [0, 1]], ![[90, 21, 101], [141, 70, 69], [92, 135, 27], [70, 73, 155], [18, 127, 128], [14, 2, 52], [135, 53, 21], [45, 141, 62]], ![[0, 1], [55, 161, 84], [32, 91, 135], [156, 89, 120], [30, 78, 130], [115, 104, 75], [139, 110, 141], [90, 21, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 77], []]
 b := ![[], [123, 10, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [116, 92, 28, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27976179, 8790427, -1569038]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-171633, 53929, -9626]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![30, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![30, 1, 0]] 
 ![![167, 0, 0], ![30, 1, 0], ![36, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![30, 1, 0], ![0, 31, 2], ![-754, 117, 30]]]
  hmulB := by decide  
  f := ![![![871, 29, 0], ![-4843, 0, 0]], ![![150, 5, 0], ![-834, 0, 0]], ![![168, -10, -1], ![-934, 84, 0]]]
  g := ![![![1, 0, 0], ![-30, 167, 0], ![-36, 0, 167]], ![![0, 1, 0], ![-6, 31, 2], ![-32, 117, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![35, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![35, 1, 0]] 
 ![![167, 0, 0], ![35, 1, 0], ![38, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![35, 1, 0], ![0, 36, 2], ![-754, 117, 35]]]
  hmulB := by decide  
  f := ![![![2556, 73, 0], ![-12191, 0, 0]], ![![490, 14, 0], ![-2337, 0, 0]], ![![564, -2, -1], ![-2690, 84, 0]]]
  g := ![![![1, 0, 0], ![-35, 167, 0], ![-38, 0, 167]], ![![0, 1, 0], ![-8, 36, 2], ![-37, 117, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-66, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-66, 1, 0]] 
 ![![167, 0, 0], ![101, 1, 0], ![26, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-66, 1, 0], ![0, -65, 2], ![-754, 117, -66]]]
  hmulB := by decide  
  f := ![![![8449, -128, 0], ![21376, 0, 0]], ![![5083, -77, 0], ![12860, 0, 0]], ![![1366, 12, -1], ![3456, 84, 0]]]
  g := ![![![1, 0, 0], ![-101, 167, 0], ![-26, 0, 167]], ![![-1, 1, 0], ![39, -65, 2], ![-65, 117, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![30, 1, 0]] ![![167, 0, 0], ![35, 1, 0]]
  ![![167, 0, 0], ![-143, 33, 1]] where
 M := ![![![27889, 0, 0], ![5845, 167, 0]], ![![5010, 167, 0], ![1050, 66, 2]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![35, 1, 0], ![0, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![8, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-143, 33, 1]] ![![167, 0, 0], ![-66, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11022, 167, 0]], ![![-23881, 5511, 167], ![8684, -2171, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-66, 1, 0]]], ![![![-143, 33, 1]], ![![52, -13, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-11, 50, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-11, 50, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![162, 50, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-11, 50, 1], ![-754, 156, 100], ![-37323, 5473, 106]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-162, -50, 173]], ![![-1, 0, 1], ![-98, -28, 100], ![-315, 1, 106]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [122, 13, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [160, 172], [0, 1]]
 g := ![![[149, 78], [149], [111, 22], [17, 13], [24], [110, 169], [1]], ![[0, 95], [149], [171, 151], [21, 160], [24], [162, 4], [1]]]
 h' := ![![[160, 172], [42, 123], [125, 29], [2, 56], [126, 79], [74, 102], [51, 160], [0, 1]], ![[0, 1], [0, 50], [94, 144], [139, 117], [137, 94], [132, 71], [47, 13], [160, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [70, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [122, 13, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5533, -2011, 1022]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-989, -307, 1022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![73, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![73, 1, 0]] 
 ![![173, 0, 0], ![73, 1, 0], ![67, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![73, 1, 0], ![0, 74, 2], ![-754, 117, 73]]]
  hmulB := by decide  
  f := ![![![1315, 18, 0], ![-3114, 0, 0]], ![![511, 7, 0], ![-1210, 0, 0]], ![![527, -30, -1], ![-1248, 87, 0]]]
  g := ![![![1, 0, 0], ![-73, 173, 0], ![-67, 0, 173]], ![![0, 1, 0], ![-32, 74, 2], ![-82, 117, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-11, 50, 1]] ![![173, 0, 0], ![73, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![12629, 173, 0]], ![![-1903, 8650, 173], ![-1557, 3806, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![73, 1, 0]]], ![![![-11, 50, 1]], ![![-9, 22, 1]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-54, -56, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-54, -56, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![125, 123, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-54, -56, 1], ![-754, 7, -112], ![42601, -6929, 63]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -123, 179]], ![![-1, -1, 1], ![74, 77, -112], ![194, -82, 63]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [93, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 178], [0, 1]]
 g := ![![[41, 77], [60, 57], [142], [9], [116, 14], [76, 52], [1]], ![[0, 102], [25, 122], [142], [9], [76, 165], [132, 127], [1]]]
 h' := ![![[125, 178], [148, 16], [12, 86], [35, 121], [131, 3], [92, 67], [86, 125], [0, 1]], ![[0, 1], [0, 163], [22, 93], [124, 58], [148, 176], [54, 112], [138, 54], [125, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [8, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [93, 54, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-466955, -66457, 53573]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-40020, -37184, 53573]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-67, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-67, 1, 0]] 
 ![![179, 0, 0], ![112, 1, 0], ![116, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-67, 1, 0], ![0, -66, 2], ![-754, 117, -67]]]
  hmulB := by decide  
  f := ![![![68, 10031, -304], ![179, 27208, 0]], ![![68, 6269, -190], ![180, 17005, 0]], ![![13, 6501, -197], ![33, 17632, 0]]]
  g := ![![![1, 0, 0], ![-112, 179, 0], ![-116, 0, 179]], ![![-1, 1, 0], ![40, -66, 2], ![-34, 117, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-54, -56, 1]] ![![179, 0, 0], ![-67, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-11993, 179, 0]], ![![-9666, -10024, 179], ![2864, 3759, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-67, 1, 0]]], ![![![-54, -56, 1]], ![![16, 21, -1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-131, 54, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-131, 54, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![50, 54, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-131, 54, 1], ![-754, 40, 108], ![-40339, 5941, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-50, -54, 181]], ![![-1, 0, 1], ![-34, -32, 108], ![-219, 37, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [97, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 180], [0, 1]]
 g := ![![[9, 102], [116], [115, 94], [145], [94, 143], [134, 119], [1]], ![[15, 79], [116], [46, 87], [145], [145, 38], [141, 62], [1]]]
 h' := ![![[32, 180], [115, 37], [67, 109], [152, 53], [113, 67], [34, 163], [84, 32], [0, 1]], ![[0, 1], [32, 144], [116, 72], [38, 128], [85, 114], [1, 18], [22, 149], [32, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [49, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [97, 149, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2690, 389, 272]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-90, -79, 272]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![73, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![73, 1, 0]] 
 ![![181, 0, 0], ![73, 1, 0], ![14, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![73, 1, 0], ![0, 74, 2], ![-754, 117, 73]]]
  hmulB := by decide  
  f := ![![![1607, 22, 0], ![-3982, 0, 0]], ![![657, 9, 0], ![-1628, 0, 0]], ![![88, -36, -1], ![-218, 91, 0]]]
  g := ![![![1, 0, 0], ![-73, 181, 0], ![-14, 0, 181]], ![![0, 1, 0], ![-30, 74, 2], ![-57, 117, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-131, 54, 1]] ![![181, 0, 0], ![73, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![13213, 181, 0]], ![![-23711, 9774, 181], ![-10317, 3982, 181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![73, 1, 0]]], ![![![-131, 54, 1]], ![![-57, 22, 1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-38, 25, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-38, 25, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![153, 25, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-38, 25, 1], ![-754, 104, 50], ![-18473, 2548, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -25, 191]], ![![-1, 0, 1], ![-44, -6, 50], ![-160, 3, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [53, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 190], [0, 1]]
 g := ![![[35, 26], [101, 86], [120, 144], [71, 54], [46, 120], [105, 160], [1]], ![[128, 165], [56, 105], [18, 47], [176, 137], [152, 71], [119, 31], [1]]]
 h' := ![![[55, 190], [186, 44], [134, 116], [57, 12], [45, 93], [165, 104], [138, 55], [0, 1]], ![[0, 1], [123, 147], [20, 75], [144, 179], [3, 98], [155, 87], [107, 136], [55, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [32, 169]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [53, 136, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13142, -5498, 3623]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2971, -503, 3623]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-50, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-50, 1, 0]] 
 ![![191, 0, 0], ![141, 1, 0], ![112, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-50, 1, 0], ![0, -49, 2], ![-754, 117, -50]]]
  hmulB := by decide  
  f := ![![![7751, -155, 0], ![29605, 0, 0]], ![![5701, -114, 0], ![21775, 0, 0]], ![![4532, -66, -1], ![17310, 96, 0]]]
  g := ![![![1, 0, 0], ![-141, 191, 0], ![-112, 0, 191]], ![![-1, 1, 0], ![35, -49, 2], ![-61, 117, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-38, 25, 1]] ![![191, 0, 0], ![-50, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-9550, 191, 0]], ![![-7258, 4775, 191], ![1146, -1146, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-50, 1, 0]]], ![![![-38, 25, 1]], ![![6, -6, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-148, -77, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-148, -77, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![45, 116, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-148, -77, 1], ![-754, -108, -154], ![58435, -9386, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -116, 193]], ![![-1, -1, 1], ![32, 92, -154], ![310, -30, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [52, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 192], [0, 1]]
 g := ![![[136, 131], [162], [169], [134], [2], [139], [69, 1]], ![[104, 62], [162], [169], [134], [2], [139], [138, 192]]]
 h' := ![![[69, 192], [124, 175], [153, 111], [16, 13], [187, 110], [171, 141], [79, 77], [0, 1]], ![[0, 1], [40, 18], [92, 82], [141, 180], [57, 83], [57, 52], [181, 116], [69, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [26, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [52, 124, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-58508, -3300, 3572]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1136, -2164, 3572]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-39, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-39, 1, 0]] 
 ![![193, 0, 0], ![154, 1, 0], ![31, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-39, 1, 0], ![0, -38, 2], ![-754, 117, -39]]]
  hmulB := by decide  
  f := ![![![4798, -123, 0], ![23739, 0, 0]], ![![3862, -99, 0], ![19108, 0, 0]], ![![784, -1, -1], ![3879, 97, 0]]]
  g := ![![![1, 0, 0], ![-154, 193, 0], ![-31, 0, 193]], ![![-1, 1, 0], ![30, -38, 2], ![-91, 117, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-148, -77, 1]] ![![193, 0, 0], ![-39, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-7527, 193, 0]], ![![-28564, -14861, 193], ![5018, 2895, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-39, 1, 0]]], ![![![-148, -77, 1]], ![![26, 15, -1]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB274I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB274I3 : PrimesBelowBoundCertificateInterval O 137 193 274 where
  m := 11
  g := ![3, 1, 2, 1, 1, 3, 2, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB274I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![37249, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
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
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I151N1, I167N0, I167N1, I167N2, I173N1, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [], [I151N1], [], [], [I167N0, I167N1, I167N2], [I173N1], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
