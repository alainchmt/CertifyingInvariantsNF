
import IdealArithmetic.Examples.NF3_1_780300_1.RI3_1_780300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [97, 46, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 95, 94], [129, 43, 45], [0, 1]]
 g := ![![[126, 84, 81], [0, 24, 16], [116, 42], [41, 12, 125], [28, 31], [0, 1], []], ![[93, 117, 111, 72], [20, 20, 113, 111], [30, 81], [91, 26, 49, 114], [58, 20], [13, 42], [68, 79]], ![[22, 97, 23, 20], [83, 26, 59, 29], [112, 44], [52, 73, 80, 6], [68, 67], [23, 129], [117, 79]]]
 h' := ![![[10, 95, 94], [0, 51, 9], [4, 3, 4], [54, 73, 96], [64, 14, 60], [0, 42, 93], [0, 0, 1], [0, 1]], ![[129, 43, 45], [9, 25, 38], [43, 27, 37], [27, 48, 9], [61, 101, 4], [108, 7, 24], [37, 5, 43], [10, 95, 94]], ![[0, 1], [136, 63, 92], [14, 109, 98], [6, 18, 34], [107, 24, 75], [93, 90, 22], [10, 134, 95], [129, 43, 45]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 136], []]
 b := ![[], [84, 20, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [97, 46, 0, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6533, -556, -556]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, -4, -4]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-30, -21, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-30, -21, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![119, 128, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-30, -21, 1], ![170, -30, -105], ![-3570, 34, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -128, 149]], ![![-1, -1, 1], ![85, 90, -105], ![0, 26, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [148, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 148], [0, 1]]
 g := ![![[27, 148], [25], [92, 107], [140], [125, 142], [133], [1]], ![[0, 1], [25], [1, 42], [140], [85, 7], [133], [1]]]
 h' := ![![[27, 148], [145, 105], [92, 5], [120, 133], [125, 17], [134, 69], [1, 27], [0, 1]], ![[0, 1], [0, 44], [78, 144], [135, 16], [137, 132], [60, 80], [134, 122], [27, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [35, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [148, 122, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2013, 66, 380]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-317, -326, 380]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-44, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-44, 1, 0]] 
 ![![149, 0, 0], ![105, 1, 0], ![30, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-44, 1, 0], ![0, -44, 5], ![170, 0, -44]]]
  hmulB := by decide  
  f := ![![![5413, -123, 0], ![18327, 0, 0]], ![![3785, -86, 0], ![12815, 0, 0]], ![![1094, -16, -1], ![3704, 30, 0]]]
  g := ![![![1, 0, 0], ![-105, 149, 0], ![-30, 0, 149]], ![![-1, 1, 0], ![30, -44, 5], ![10, 0, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-30, -21, 1]] ![![149, 0, 0], ![-44, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-6556, 149, 0]], ![![-4470, -3129, 149], ![1490, 894, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-44, 1, 0]]], ![![![-30, -21, 1]], ![![10, 6, -1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [130, 114, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 88, 52], [47, 62, 99], [0, 1]]
 g := ![![[3, 39, 25], [14, 106, 118], [34, 113, 5], [148, 37], [55, 59, 78], [110, 1], []], ![[76, 89, 18, 24], [88, 18, 68, 119], [131, 14, 31, 79], [140, 21], [83, 140, 93, 14], [4, 69], [62, 137]], ![[113, 16, 112, 50], [33, 78, 35, 19], [147, 77, 78, 110], [96, 22], [24, 115, 42, 40], [66, 43], [15, 137]]]
 h' := ![![[63, 88, 52], [143, 46, 5], [110, 36, 119], [28, 88, 55], [98, 14, 108], [45, 14, 57], [0, 0, 1], [0, 1]], ![[47, 62, 99], [102, 28, 135], [108, 55, 39], [121, 66, 134], [72, 17, 25], [129, 100, 34], [137, 102, 62], [63, 88, 52]], ![[0, 1], [127, 77, 11], [7, 60, 144], [138, 148, 113], [38, 120, 18], [64, 37, 60], [108, 49, 88], [47, 62, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131, 69], []]
 b := ![[], [106, 71, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [130, 114, 41, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54964, 1510, -7399]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-364, 10, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-69, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-69, 1, 0]] 
 ![![157, 0, 0], ![88, 1, 0], ![84, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-69, 1, 0], ![0, -69, 5], ![170, 0, -69]]]
  hmulB := by decide  
  f := ![![![6625, -96, 0], ![15072, 0, 0]], ![![3658, -53, 0], ![8322, 0, 0]], ![![3498, -23, -2], ![7958, 63, 0]]]
  g := ![![![1, 0, 0], ![-88, 157, 0], ![-84, 0, 157]], ![![-1, 1, 0], ![36, -69, 5], ![38, 0, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-45, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-45, 1, 0]] 
 ![![157, 0, 0], ![112, 1, 0], ![66, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-45, 1, 0], ![0, -45, 5], ![170, 0, -45]]]
  hmulB := by decide  
  f := ![![![496, -11, 0], ![1727, 0, 0]], ![![406, -9, 0], ![1414, 0, 0]], ![![228, 13, -2], ![794, 63, 0]]]
  g := ![![![1, 0, 0], ![-112, 157, 0], ![-66, 0, 157]], ![![-1, 1, 0], ![30, -45, 5], ![20, 0, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-43, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-43, 1, 0]] 
 ![![157, 0, 0], ![114, 1, 0], ![7, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-43, 1, 0], ![0, -43, 5], ![170, 0, -43]]]
  hmulB := by decide  
  f := ![![![4473, -104, 0], ![16328, 0, 0]], ![![3312, -77, 0], ![12090, 0, 0]], ![![269, 11, -2], ![982, 63, 0]]]
  g := ![![![1, 0, 0], ![-114, 157, 0], ![-7, 0, 157]], ![![-1, 1, 0], ![31, -43, 5], ![3, 0, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-69, 1, 0]] ![![157, 0, 0], ![-45, 1, 0]]
  ![![157, 0, 0], ![-7, 40, 1]] where
 M := ![![![24649, 0, 0], ![-7065, 157, 0]], ![![-10833, 157, 0], ![3105, -114, 5]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![-38, -39, -1], ![157, 0, 0]]], ![![![-62, -39, -1], ![157, 0, 0]], ![![20, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-7, 40, 1]] ![![157, 0, 0], ![-43, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6751, 157, 0]], ![![-1099, 6280, 157], ![471, -1727, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-43, 1, 0]]], ![![![-7, 40, 1]], ![![3, -11, 1]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [133, 66, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 127, 119], [140, 35, 44], [0, 1]]
 g := ![![[153, 23, 25], [147, 153, 96], [112, 55], [132, 83], [111, 6], [106, 3, 1], []], ![[40, 67, 44, 4], [149, 37, 106, 53], [13, 54], [77, 38], [108, 118], [47, 58, 145, 53], [11, 143]], ![[43, 124, 37, 120], [125, 110, 8, 2], [3, 97], [15, 158], [32, 38], [29, 5, 132, 137], [86, 143]]]
 h' := ![![[26, 127, 119], [9, 60, 5], [114, 157, 52], [103, 50, 50], [113, 9, 75], [83, 103, 150], [0, 0, 1], [0, 1]], ![[140, 35, 44], [79, 106, 143], [110, 17, 128], [32, 159, 39], [2, 88, 110], [115, 50, 66], [28, 62, 35], [26, 127, 119]], ![[0, 1], [156, 160, 15], [61, 152, 146], [42, 117, 74], [154, 66, 141], [3, 10, 110], [12, 101, 127], [140, 35, 44]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 90], []]
 b := ![[], [133, 131, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [133, 66, 160, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-321110, 48737, 4238]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1970, 299, 26]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-31, 42, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-31, 42, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![136, 42, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-31, 42, 1], ![170, -31, 210], ![7140, 34, -31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -42, 167]], ![![-1, 0, 1], ![-170, -53, 210], ![68, 8, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [135, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 166], [0, 1]]
 g := ![![[63, 93], [116, 114], [33, 14], [96], [2], [158, 144], [1]], ![[10, 74], [148, 53], [34, 153], [96], [2], [49, 23], [1]]]
 h' := ![![[12, 166], [38, 107], [54, 75], [147, 66], [9, 51], [46, 13], [32, 12], [0, 1]], ![[0, 1], [153, 60], [119, 92], [104, 101], [120, 116], [35, 154], [9, 155], [12, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [86, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [135, 155, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![475, -121, -150]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![125, 37, -150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-43, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-43, 1, 0]] 
 ![![167, 0, 0], ![124, 1, 0], ![31, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-43, 1, 0], ![0, -43, 5], ![170, 0, -43]]]
  hmulB := by decide  
  f := ![![![5204, -121, 0], ![20207, 0, 0]], ![![3914, -91, 0], ![15198, 0, 0]], ![![1000, -6, -2], ![3883, 67, 0]]]
  g := ![![![1, 0, 0], ![-124, 167, 0], ![-31, 0, 167]], ![![-1, 1, 0], ![31, -43, 5], ![9, 0, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-31, 42, 1]] ![![167, 0, 0], ![-43, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-7181, 167, 0]], ![![-5177, 7014, 167], ![1503, -1837, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-43, 1, 0]]], ![![![-31, 42, 1]], ![![9, -11, 1]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![32, -53, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![32, -53, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![32, 120, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![32, -53, 1], ![170, 32, -265], ![-9010, 34, 32]]]
  hmulB := by decide  
  f := ![![![-31, 53, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -120, 173]], ![![0, -1, 1], ![50, 184, -265], ![-58, -22, 32]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [8, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 172], [0, 1]]
 g := ![![[88, 133], [49], [28, 4], [24, 33], [33], [21, 144], [1]], ![[49, 40], [49], [153, 169], [147, 140], [33], [23, 29], [1]]]
 h' := ![![[161, 172], [133, 126], [122, 166], [154, 171], [107, 44], [5, 44], [165, 161], [0, 1]], ![[0, 1], [5, 47], [33, 7], [5, 2], [98, 129], [169, 129], [136, 12], [161, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [142, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [8, 12, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6481, 300, 1819]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-299, -1260, 1819]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-81, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-81, 1, 0]] 
 ![![173, 0, 0], ![92, 1, 0], ![141, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-81, 1, 0], ![0, -81, 5], ![170, 0, -81]]]
  hmulB := by decide  
  f := ![![![6076, -75, 0], ![12975, 0, 0]], ![![3160, -39, 0], ![6748, 0, 0]], ![![4998, -13, -3], ![10673, 104, 0]]]
  g := ![![![1, 0, 0], ![-92, 173, 0], ![-141, 0, 173]], ![![-1, 1, 0], ![39, -81, 5], ![67, 0, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![32, -53, 1]] ![![173, 0, 0], ![-81, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-14013, 173, 0]], ![![5536, -9169, 173], ![-2422, 4325, -346]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-81, 1, 0]]], ![![![32, -53, 1]], ![![-14, 25, -2]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![25, 30, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![25, 30, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![25, 30, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![25, 30, 1], ![170, 25, 150], ![5100, 34, 25]]]
  hmulB := by decide  
  f := ![![![-24, -30, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-25, -30, 179]], ![![0, 0, 1], ![-20, -25, 150], ![25, -4, 25]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [1, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 178], [0, 1]]
 g := ![![[69, 1], [110, 65], [107], [1], [0, 66], [94, 107], [1]], ![[0, 178], [100, 114], [107], [1], [100, 113], [50, 72], [1]]]
 h' := ![![[110, 178], [69, 1], [73, 94], [178, 110], [0, 178], [85, 31], [178, 110], [0, 1]], ![[0, 1], [0, 178], [31, 85], [106, 69], [69, 1], [94, 148], [106, 69], [110, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [154, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [1, 69, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1087, 235, -22]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 5, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![29, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![29, 1, 0]] 
 ![![179, 0, 0], ![29, 1, 0], ![154, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![29, 1, 0], ![0, 29, 5], ![170, 0, 29]]]
  hmulB := by decide  
  f := ![![![3075, 106, 0], ![-18974, 0, 0]], ![![493, 17, 0], ![-3042, 0, 0]], ![![2606, 84, -1], ![-16080, 36, 0]]]
  g := ![![![1, 0, 0], ![-29, 179, 0], ![-154, 0, 179]], ![![0, 1, 0], ![-9, 29, 5], ![-24, 0, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![25, 30, 1]] ![![179, 0, 0], ![29, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![5191, 179, 0]], ![![4475, 5370, 179], ![895, 895, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![29, 1, 0]]], ![![![25, 30, 1]], ![![5, 5, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [151, 66, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 81, 23], [74, 99, 158], [0, 1]]
 g := ![![[82, 159, 48], [180, 99], [139, 143, 4], [16, 75], [48, 177, 176], [115, 0, 1], []], ![[20, 168, 171, 158], [132, 172], [140, 122, 164, 118], [117, 172], [36, 163, 55, 54], [178, 157, 28, 78], [106, 167]], ![[132, 175, 7, 115], [58, 121], [180, 114, 169, 47], [99, 80], [153, 28, 111, 150], [6, 161, 171, 51], [152, 167]]]
 h' := ![![[107, 81, 23], [19, 15, 132], [7, 4, 113], [1, 100, 179], [173, 91, 16], [11, 12, 30], [0, 0, 1], [0, 1]], ![[74, 99, 158], [115, 132, 19], [77, 125, 57], [86, 29, 111], [167, 82, 57], [154, 43, 169], [149, 144, 99], [107, 81, 23]], ![[0, 1], [56, 34, 30], [44, 52, 11], [180, 52, 72], [58, 8, 108], [71, 126, 163], [81, 37, 81], [74, 99, 158]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [163, 83], []]
 b := ![[], [88, 65, 20], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [151, 66, 0, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![47241, 1086, 2172]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![261, 6, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-73, 10, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-73, 10, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![118, 10, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-73, 10, 1], ![170, -73, 50], ![1700, 34, -73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-118, -10, 191]], ![![-1, 0, 1], ![-30, -3, 50], ![54, 4, -73]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [17, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 190], [0, 1]]
 g := ![![[164, 45], [179, 20], [183, 77], [19, 32], [147, 160], [99, 8], [1]], ![[0, 146], [0, 171], [0, 114], [0, 159], [52, 31], [142, 183], [1]]]
 h' := ![![[77, 190], [13, 42], [136, 28], [59, 29], [175, 154], [36, 136], [174, 77], [0, 1]], ![[0, 1], [0, 149], [0, 163], [0, 162], [0, 37], [3, 55], [182, 114], [77, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [21, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [17, 114, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6551, -1044, 736]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-489, -44, 736]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-50, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-50, 1, 0]] 
 ![![191, 0, 0], ![141, 1, 0], ![73, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-50, 1, 0], ![0, -50, 5], ![170, 0, -50]]]
  hmulB := by decide  
  f := ![![![8351, -167, 0], ![31897, 0, 0]], ![![6101, -122, 0], ![23303, 0, 0]], ![![3253, -25, -4], ![12425, 153, 0]]]
  g := ![![![1, 0, 0], ![-141, 191, 0], ![-73, 0, 191]], ![![-1, 1, 0], ![35, -50, 5], ![20, 0, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-73, 10, 1]] ![![191, 0, 0], ![-50, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-9550, 191, 0]], ![![-13943, 1910, 191], ![3820, -573, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-50, 1, 0]]], ![![![-73, 10, 1]], ![![20, -3, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [139, 52, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 178, 60], [186, 14, 133], [0, 1]]
 g := ![![[8, 168, 14], [42, 134], [52, 189], [], [181, 59], [65, 170], [1]], ![[77, 18, 10, 182], [163, 48], [130, 177], [159, 147], [191, 165], [48, 172], [146, 70, 56, 33]], ![[69, 27, 73, 119], [89, 150], [13, 189], [106, 147], [17, 126], [156, 97], [75, 132, 145, 160]]]
 h' := ![![[46, 178, 60], [173, 77, 173], [118, 1, 110], [165, 34, 162], [92, 82], [57, 184, 32], [54, 141, 39], [0, 1]], ![[186, 14, 133], [93, 9, 94], [13, 145, 56], [110, 59, 62], [4, 121, 95], [150, 164, 101], [35, 170, 128], [46, 178, 60]], ![[0, 1], [6, 107, 119], [188, 47, 27], [79, 100, 162], [97, 183, 98], [181, 38, 60], [40, 75, 26], [186, 14, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 27], []]
 b := ![[], [75, 182, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [139, 52, 154, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31652, 2509, 5018]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-164, 13, 26]
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



lemma PB250I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB250I3 : PrimesBelowBoundCertificateInterval O 137 193 250 where
  m := 11
  g := ![1, 2, 1, 3, 1, 2, 2, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB250I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
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
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I157N0, I157N1, I157N2, I167N1, I173N1, I179N1, I191N1]
  Il := ![[], [I149N1], [], [I157N0, I157N1, I157N2], [], [I167N1], [I173N1], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
