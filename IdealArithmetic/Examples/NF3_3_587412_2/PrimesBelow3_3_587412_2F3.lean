
import IdealArithmetic.Examples.NF3_3_587412_2.RI3_3_587412_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![19, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![19, 1, 0]] 
 ![![139, 0, 0], ![19, 1, 0], ![56, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![19, 1, 0], ![0, 19, 1], ![1162, 210, 19]]]
  hmulB := by decide  
  f := ![![![381, 20, 0], ![-2780, 0, 0]], ![![19, 1, 0], ![-138, 0, 0]], ![![136, 7, 0], ![-992, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 139, 0], ![-56, 0, 139]], ![![0, 1, 0], ![-3, 19, 1], ![-28, 210, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![25, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![25, 1, 0]] 
 ![![139, 0, 0], ![25, 1, 0], ![70, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![25, 1, 0], ![0, 25, 1], ![1162, 210, 25]]]
  hmulB := by decide  
  f := ![![![1726, 69, 0], ![-9591, 0, 0]], ![![300, 12, 0], ![-1667, 0, 0]], ![![830, 33, 0], ![-4612, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 139, 0], ![-70, 0, 139]], ![![0, 1, 0], ![-5, 25, 1], ![-42, 210, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-44, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-44, 1, 0]] 
 ![![139, 0, 0], ![95, 1, 0], ![10, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-44, 1, 0], ![0, -44, 1], ![1162, 210, -44]]]
  hmulB := by decide  
  f := ![![![4357, -99, 0], ![13761, 0, 0]], ![![2993, -68, 0], ![9453, 0, 0]], ![![366, -8, 0], ![1156, 1, 0]]]
  g := ![![![1, 0, 0], ![-95, 139, 0], ![-10, 0, 139]], ![![-1, 1, 0], ![30, -44, 1], ![-132, 210, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![19, 1, 0]] ![![139, 0, 0], ![25, 1, 0]]
  ![![139, 0, 0], ![-81, 44, 1]] where
 M := ![![![19321, 0, 0], ![3475, 139, 0]], ![![2641, 139, 0], ![475, 44, 1]]]
 hmul := by decide  
 g := ![![![![139, 0, 0], ![0, 0, 0]], ![![25, 1, 0], ![0, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![4, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-81, 44, 1]] ![![139, 0, 0], ![-44, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-6116, 139, 0]], ![![-11259, 6116, 139], ![4726, -1807, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-44, 1, 0]]], ![![![-81, 44, 1]], ![![34, -13, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [18, 25, 122, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 122, 86], [118, 26, 63], [0, 1]]
 g := ![![[63, 74, 17], [97, 121], [16, 42, 26], [148, 6], [57, 148, 42], [27, 1], []], ![[110, 78, 110, 31], [84, 86], [54, 82, 26, 113], [91, 25], [1, 125, 30, 80], [89, 80], [7, 95]], ![[128, 60, 115, 33], [54, 142], [50, 85, 36, 103], [15, 33], [80, 147, 139, 47], [128, 133], [30, 95]]]
 h' := ![![[58, 122, 86], [142, 121, 100], [10, 117, 138], [9, 68, 131], [17, 114, 30], [110, 52, 108], [0, 0, 1], [0, 1]], ![[118, 26, 63], [31, 143, 43], [84, 27, 91], [54, 113, 16], [65, 31, 5], [147, 14, 128], [109, 49, 26], [58, 122, 86]], ![[0, 1], [49, 34, 6], [96, 5, 69], [8, 117, 2], [24, 4, 114], [11, 83, 62], [123, 100, 122], [118, 26, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [121, 47], []]
 b := ![[], [1, 111, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [18, 25, 122, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1799920, -431057, -22499]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12080, -2893, -151]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [124, 115, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 145, 126], [114, 5, 25], [0, 1]]
 g := ![![[143, 99, 19], [140, 127, 136], [76, 64, 58], [20, 62], [4, 40, 139], [49, 1], []], ![[31, 131, 80, 101], [17, 79, 129, 102], [78, 145, 8, 3], [70, 124], [39, 49, 12, 12], [120, 25], [121, 21]], ![[126, 126, 139, 97], [80, 100, 141, 19], [100, 136, 67, 144], [53, 1], [90, 67, 31, 110], [136, 36], [71, 21]]]
 h' := ![![[86, 145, 126], [5, 82, 87], [89, 59, 102], [124, 94, 80], [108, 104, 106], [115, 130, 21], [0, 0, 1], [0, 1]], ![[114, 5, 25], [48, 87, 46], [2, 2, 92], [95, 109, 13], [35, 45, 44], [111, 146, 26], [93, 116, 5], [86, 145, 126]], ![[0, 1], [30, 133, 18], [123, 90, 108], [108, 99, 58], [145, 2, 1], [136, 26, 104], [115, 35, 145], [114, 5, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 149], []]
 b := ![[], [56, 54, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [124, 115, 102, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21889866, 11621866, 1322760]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![144966, 76966, 8760]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [128, 70, 141, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 67, 100], [48, 89, 57], [0, 1]]
 g := ![![[118, 48, 40], [20, 121], [132, 107, 144], [99, 25, 118], [71, 104, 56], [16, 1], []], ![[73, 49, 35, 111], [55, 86], [58, 16, 14, 27], [67, 114, 67, 14], [86, 146, 114, 42], [55, 71], [72, 109]], ![[70, 105, 119, 124], [31, 19], [27, 77, 46, 47], [123, 54, 0, 130], [50, 23, 38, 138], [5, 93], [115, 109]]]
 h' := ![![[125, 67, 100], [98, 79, 36], [60, 127, 11], [45, 85, 145], [18, 136, 78], [150, 8, 29], [0, 0, 1], [0, 1]], ![[48, 89, 57], [16, 98, 114], [84, 18, 20], [16, 100, 53], [76, 28, 132], [24, 45, 84], [129, 113, 89], [125, 67, 100]], ![[0, 1], [125, 137, 7], [47, 12, 126], [42, 129, 116], [37, 150, 104], [0, 104, 44], [144, 44, 67], [48, 89, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 28], []]
 b := ![[], [43, 109, 6], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [128, 70, 141, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-187458, -402548, -46315]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1194, -2564, -295]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-157, -78, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-157, -78, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![6, 85, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-157, -78, 1], ![1162, 53, -78], ![-90636, -15218, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -85, 163]], ![![-1, -1, 1], ![10, 41, -78], ![-558, -121, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [23, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 162], [0, 1]]
 g := ![![[94, 96], [12, 126], [113], [53], [155], [59, 56], [1]], ![[41, 67], [136, 37], [113], [53], [155], [96, 107], [1]]]
 h' := ![![[120, 162], [50, 52], [83, 17], [143, 90], [59, 85], [110, 127], [140, 120], [0, 1]], ![[0, 1], [96, 111], [4, 146], [22, 73], [153, 78], [28, 36], [33, 43], [120, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [51, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [23, 43, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6905, 9243, 1756]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-107, -859, 1756]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![78, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![78, 1, 0]] 
 ![![163, 0, 0], ![78, 1, 0], ![110, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![78, 1, 0], ![0, 78, 1], ![1162, 210, 78]]]
  hmulB := by decide  
  f := ![![![1483, 19, 0], ![-3097, 0, 0]], ![![702, 9, 0], ![-1466, 0, 0]], ![![974, 12, 0], ![-2034, 1, 0]]]
  g := ![![![1, 0, 0], ![-78, 163, 0], ![-110, 0, 163]], ![![0, 1, 0], ![-38, 78, 1], ![-146, 210, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-157, -78, 1]] ![![163, 0, 0], ![78, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![12714, 163, 0]], ![![-25591, -12714, 163], ![-11084, -6031, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![78, 1, 0]]], ![![![-157, -78, 1]], ![![-68, -37, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-88, -17, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-88, -17, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![79, 150, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-88, -17, 1], ![1162, 122, -17], ![-19754, -2408, 122]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -150, 167]], ![![-1, -1, 1], ![15, 16, -17], ![-176, -124, 122]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [148, 148, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 166], [0, 1]]
 g := ![![[1, 29], [90, 128], [12, 31], [115], [12], [66, 27], [1]], ![[51, 138], [17, 39], [100, 136], [115], [12], [78, 140], [1]]]
 h' := ![![[19, 166], [40, 14], [61, 104], [17, 96], [105, 99], [85, 124], [19, 19], [0, 1]], ![[0, 1], [139, 153], [33, 63], [4, 71], [149, 68], [103, 43], [46, 148], [19, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [138, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [148, 148, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2472, 1434, 63]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -48, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![17, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![17, 1, 0]] 
 ![![167, 0, 0], ![17, 1, 0], ![45, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![17, 1, 0], ![0, 17, 1], ![1162, 210, 17]]]
  hmulB := by decide  
  f := ![![![902, 53, 0], ![-8851, 0, 0]], ![![68, 4, 0], ![-667, 0, 0]], ![![240, 14, 0], ![-2355, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 167, 0], ![-45, 0, 167]], ![![0, 1, 0], ![-2, 17, 1], ![-19, 210, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-88, -17, 1]] ![![167, 0, 0], ![17, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![2839, 167, 0]], ![![-14696, -2839, 167], ![-334, -167, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![17, 1, 0]]], ![![![-88, -17, 1]], ![![-2, -1, 0]]]]
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


lemma PB171I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 170 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 170 (by omega)

def PB171I3 : PrimesBelowBoundCertificateInterval O 137 170 171 where
  m := 6
  g := ![3, 1, 1, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB171I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
  β := ![I139N0, I139N1, I139N2, I163N1, I167N1]
  Il := ![[I139N0, I139N1, I139N2], [], [], [], [I163N1], [I167N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
