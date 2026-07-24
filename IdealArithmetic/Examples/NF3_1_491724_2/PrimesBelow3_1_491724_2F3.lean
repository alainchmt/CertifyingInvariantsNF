
import IdealArithmetic.Examples.NF3_1_491724_2.RI3_1_491724_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1165213, 319197, 22093]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![1165213, 319197, 22093]] 
 ![![139, 0, 0], ![0, 139, 0], ![3, 115, 1]] where
  M :=![![![1165213, 319197, 22093], ![16834866, 4611721, 319197], ![243228114, 66629598, 4611721]]]
  hmulB := by decide  
  f := ![![![20065, 1443, -196]], ![![-149352, -10511, 1443]], ![![-115221, -8120, 1114]]]
  g := ![![![7906, -15982, 22093], ![114225, -230906, 319197], ![1650309, -3336103, 4611721]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [84, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 138], [0, 1]]
 g := ![![[17, 47], [87, 79], [13], [134, 124], [112], [54], [1]], ![[38, 92], [4, 60], [13], [9, 15], [112], [54], [1]]]
 h' := ![![[101, 138], [59, 73], [29, 94], [3, 98], [90, 47], [18, 23], [55, 101], [0, 1]], ![[0, 1], [65, 66], [71, 45], [32, 41], [111, 92], [117, 116], [109, 38], [101, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [79, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [84, 38, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1608, 1036, 119]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![9, -91, 119]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20065, 1443, -196]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![20065, 1443, -196]] 
 ![![139, 0, 0], ![24, 1, 0], ![119, 0, 1]] where
  M :=![![![20065, 1443, -196], ![-149352, -10511, 1443], ![1099566, 75756, -10511]]]
  hmulB := by decide  
  f := ![![![1165213, 319197, 22093]], ![![322302, 88291, 6111]], ![![2747399, 752619, 52092]]]
  g := ![![![63, 1443, -196], ![-495, -10511, 1443], ![3829, 75756, -10511]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![1165213, 319197, 22093]] ![![20065, 1443, -196]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [107, 42, 110, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 7, 146], [21, 141, 3], [0, 1]]
 g := ![![[43, 148, 85], [101, 64], [70, 94, 73], [40, 124], [2, 48, 121], [39, 1], []], ![[126, 18, 30, 111], [23, 113], [122, 47, 146, 147], [110, 107], [85, 139, 132, 23], [106, 64], [11, 9]], ![[52, 26, 5, 131], [121, 80], [34, 44, 71, 38], [128, 119], [91, 21, 61, 66], [6, 49], [5, 9]]]
 h' := ![![[18, 7, 146], [31, 30, 54], [109, 10, 141], [94, 25, 85], [84, 145, 78], [148, 43, 138], [0, 0, 1], [0, 1]], ![[21, 141, 3], [103, 44, 74], [110, 67, 34], [6, 2, 139], [81, 113, 133], [24, 92, 108], [41, 19, 141], [18, 7, 146]], ![[0, 1], [55, 75, 21], [28, 72, 123], [79, 122, 74], [118, 40, 87], [148, 14, 52], [55, 130, 7], [21, 141, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 39], []]
 b := ![[], [144, 106, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [107, 42, 110, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8273970, 5664980, 771671]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![55530, 38020, 5179]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-163, 12, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-163, 12, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![139, 12, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-163, 12, 1], ![762, -7, 12], ![9144, 2634, -7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -12, 151]], ![![-2, 0, 1], ![-6, -1, 12], ![67, 18, -7]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [51, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 150], [0, 1]]
 g := ![![[9, 59], [87, 31], [13, 84], [118], [53, 78], [36], [1]], ![[108, 92], [52, 120], [113, 67], [118], [38, 73], [36], [1]]]
 h' := ![![[145, 150], [93, 19], [92, 22], [96, 101], [15, 32], [10, 94], [100, 145], [0, 1]], ![[0, 1], [130, 132], [111, 129], [94, 50], [125, 119], [50, 57], [136, 6], [145, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [27, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [51, 6, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2239, 328, 279]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-242, -20, 279]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-12, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-12, 1, 0]] 
 ![![151, 0, 0], ![139, 1, 0], ![7, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-12, 1, 0], ![0, -12, 1], ![762, 156, -12]]]
  hmulB := by decide  
  f := ![![![829, -69, 0], ![10419, 0, 0]], ![![769, -64, 0], ![9665, 0, 0]], ![![61, -5, 0], ![767, 1, 0]]]
  g := ![![![1, 0, 0], ![-139, 151, 0], ![-7, 0, 151]], ![![-1, 1, 0], ![11, -12, 1], ![-138, 156, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-163, 12, 1]] ![![151, 0, 0], ![-12, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-1812, 151, 0]], ![![-24613, 1812, 151], ![2718, -151, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-12, 1, 0]]], ![![![-163, 12, 1]], ![![18, -1, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-69, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-69, 1, 0]] 
 ![![157, 0, 0], ![88, 1, 0], ![106, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-69, 1, 0], ![0, -69, 1], ![762, 156, -69]]]
  hmulB := by decide  
  f := ![![![6625, -96, 0], ![15072, 0, 0]], ![![3658, -53, 0], ![8322, 0, 0]], ![![4516, -65, 0], ![10274, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 157, 0], ![-106, 0, 157]], ![![-1, 1, 0], ![38, -69, 1], ![-36, 156, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-44, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-44, 1, 0]] 
 ![![157, 0, 0], ![113, 1, 0], ![105, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-44, 1, 0], ![0, -44, 1], ![762, 156, -44]]]
  hmulB := by decide  
  f := ![![![1629, -37, 0], ![5809, 0, 0]], ![![1145, -26, 0], ![4083, 0, 0]], ![![1113, -25, 0], ![3969, 1, 0]]]
  g := ![![![1, 0, 0], ![-113, 157, 0], ![-105, 0, 157]], ![![-1, 1, 0], ![31, -44, 1], ![-78, 156, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-69, 1, 0]] ![![157, 0, 0], ![-44, 1, 0]]
  ![![157, 0, 0], ![-104, 44, 1]] where
 M := ![![![24649, 0, 0], ![-6908, 157, 0]], ![![-10833, 157, 0], ![3036, -113, 1]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![60, -43, -1], ![157, 0, 0]]], ![![![35, -43, -1], ![157, 0, 0]], ![![20, -1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-104, 44, 1]] ![![157, 0, 0], ![-44, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6908, 157, 0]], ![![-16328, 6908, 157], ![5338, -1884, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-44, 1, 0]]], ![![![-104, 44, 1]], ![![34, -12, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N1
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [3, 58, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 138, 108], [82, 24, 55], [0, 1]]
 g := ![![[121, 71, 90], [140, 101, 15], [17, 140], [112, 38], [129, 1], [11, 45, 1], []], ![[13, 124, 132, 32], [54, 119, 25, 37], [115, 158], [104, 87], [115, 16], [38, 18, 108, 105], [162, 91]], ![[9, 45, 124, 40], [25, 61, 155, 38], [2, 14], [155, 26], [66, 9], [46, 122, 67, 145], [52, 91]]]
 h' := ![![[126, 138, 108], [69, 51, 116], [18, 42, 129], [45, 132, 125], [50, 12, 110], [130, 42, 1], [0, 0, 1], [0, 1]], ![[82, 24, 55], [39, 120, 142], [64, 84, 134], [75, 96, 141], [77, 87, 24], [111, 96, 159], [68, 5, 24], [126, 138, 108]], ![[0, 1], [39, 155, 68], [37, 37, 63], [80, 98, 60], [120, 64, 29], [36, 25, 3], [48, 158, 138], [82, 24, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 117], []]
 b := ![[], [73, 138, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [3, 58, 118, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13020114, -5051859, -468788]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79878, -30993, -2876]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-28, -63, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-28, -63, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![139, 104, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-28, -63, 1], ![762, 128, -63], ![-48006, -9066, 128]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -104, 167]], ![![-1, -1, 1], ![57, 40, -63], ![-394, -134, 128]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [161, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 166], [0, 1]]
 g := ![![[98, 32], [68, 25], [88, 3], [57], [42], [64, 54], [1]], ![[43, 135], [72, 142], [15, 164], [57], [42], [86, 113], [1]]]
 h' := ![![[87, 166], [74, 115], [27, 162], [62, 105], [80, 97], [50, 83], [6, 87], [0, 1]], ![[0, 1], [59, 52], [93, 5], [12, 62], [2, 70], [90, 84], [60, 80], [87, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [136, 137]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [161, 80, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1685, 994, 77]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-54, -42, 77]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![63, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![63, 1, 0]] 
 ![![167, 0, 0], ![63, 1, 0], ![39, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![63, 1, 0], ![0, 63, 1], ![762, 156, 63]]]
  hmulB := by decide  
  f := ![![![3907, 62, 0], ![-10354, 0, 0]], ![![1449, 23, 0], ![-3840, 0, 0]], ![![843, 13, 0], ![-2234, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 167, 0], ![-39, 0, 167]], ![![0, 1, 0], ![-24, 63, 1], ![-69, 156, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-28, -63, 1]] ![![167, 0, 0], ![63, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![10521, 167, 0]], ![![-4676, -10521, 167], ![-1002, -3841, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![63, 1, 0]]], ![![![-28, -63, 1]], ![![-6, -23, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3011, 95, -21]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![3011, 95, -21]] 
 ![![173, 0, 0], ![0, 173, 0], ![112, 152, 1]] where
  M :=![![![3011, 95, -21], ![-16002, -265, 95], ![72390, -1182, -265]]]
  hmulB := by decide  
  f := ![![![-1055, -289, -20]], ![![-15240, -4175, -289]], ![![-15346, -4204, -291]]]
  g := ![![![31, 19, -21], ![-154, -85, 95], ![590, 226, -265]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [17, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 172], [0, 1]]
 g := ![![[157, 139], [139], [9, 24], [58, 52], [149], [36, 113], [1]], ![[78, 34], [139], [136, 149], [16, 121], [149], [151, 60], [1]]]
 h' := ![![[99, 172], [113, 73], [20, 73], [52, 102], [61, 15], [80, 29], [156, 99], [0, 1]], ![[0, 1], [74, 100], [154, 100], [116, 71], [162, 158], [10, 144], [96, 74], [99, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [146]]
 b := ![[], [106, 73]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [17, 74, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29048, 8134, 593]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-216, -474, 593]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1055, -289, -20]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-1055, -289, -20]] 
 ![![173, 0, 0], ![21, 1, 0], ![78, 0, 1]] where
  M :=![![![-1055, -289, -20], ![-15240, -4175, -289], ![-220218, -60324, -4175]]]
  hmulB := by decide  
  f := ![![![3011, 95, -21]], ![![273, 10, -2]], ![![1776, 36, -11]]]
  g := ![![![38, -289, -20], ![549, -4175, -289], ![7932, -60324, -4175]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![3011, 95, -21]] ![![-1055, -289, -20]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [58, 166, 136, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 81, 99], [176, 97, 80], [0, 1]]
 g := ![![[135, 131, 45], [80, 3, 82], [144, 5], [33, 153], [110, 88, 110], [72, 43, 1], []], ![[177, 47, 83, 148], [124, 172, 54, 137], [80, 117], [90, 9], [178, 83, 40, 170], [35, 32, 4, 154], [5, 135]], ![[173, 112, 143, 93], [48, 49, 107, 110], [63, 149], [94, 56], [6, 143, 139, 106], [1, 39, 142, 52], [24, 135]]]
 h' := ![![[46, 81, 99], [14, 14, 89], [143, 165, 145], [34, 145, 30], [64, 165, 42], [120, 53, 17], [0, 0, 1], [0, 1]], ![[176, 97, 80], [103, 127, 174], [65, 21, 149], [87, 28, 81], [37, 40, 3], [127, 46, 94], [36, 45, 97], [46, 81, 99]], ![[0, 1], [37, 38, 95], [130, 172, 64], [174, 6, 68], [16, 153, 134], [78, 80, 68], [49, 134, 81], [176, 97, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 83], []]
 b := ![[], [141, 61, 142], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [58, 166, 136, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98271, -58533, 358]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-549, -327, 2]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![455, 26, -4]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![455, 26, -4]] 
 ![![181, 0, 0], ![0, 181, 0], ![22, 84, 1]] where
  M :=![![![455, 26, -4], ![-3048, -169, 26], ![19812, 1008, -169]]]
  hmulB := by decide  
  f := ![![![-13, -2, 0]], ![![0, -13, -2]], ![![-10, -8, -1]]]
  g := ![![![3, 2, -4], ![-20, -13, 26], ![130, 84, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [72, 178, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 180], [0, 1]]
 g := ![![[98, 3], [4], [85, 29], [29], [2, 168], [138, 9], [1]], ![[107, 178], [4], [172, 152], [29], [144, 13], [165, 172], [1]]]
 h' := ![![[3, 180], [144, 148], [34, 2], [5, 36], [37, 36], [19, 63], [109, 3], [0, 1]], ![[0, 1], [45, 33], [40, 179], [113, 145], [145, 145], [27, 118], [118, 178], [3, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [72, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [72, 178, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3120, 3850, 981]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -434, 981]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 2, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![13, 2, 0]] 
 ![![181, 0, 0], ![97, 1, 0], ![3, 0, 1]] where
  M :=![![![13, 2, 0], ![0, 13, 2], ![1524, 312, 13]]]
  hmulB := by decide  
  f := ![![![-455, -26, 4]], ![![-227, -13, 2]], ![![-117, -6, 1]]]
  g := ![![![-1, 2, 0], ![-7, 13, 2], ![-159, 312, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![455, 26, -4]] ![![13, 2, 0]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-146, -34, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-146, -34, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![45, 157, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-146, -34, 1], ![762, 10, -34], ![-25908, -4542, 10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -157, 191]], ![![-1, -1, 1], ![12, 28, -34], ![-138, -32, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [104, 114, 1] where
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
 g := ![![[137, 90], [31, 12], [109, 51], [129, 133], [123, 18], [71, 8], [1]], ![[0, 101], [0, 179], [25, 140], [56, 58], [172, 173], [114, 183], [1]]]
 h' := ![![[77, 190], [23, 89], [124, 48], [145, 137], [5, 173], [65, 171], [87, 77], [0, 1]], ![[0, 1], [0, 102], [0, 143], [189, 54], [147, 18], [53, 20], [95, 114], [77, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [166, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [104, 114, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30144, -4372, 960]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-384, -812, 960]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![34, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![34, 1, 0]] 
 ![![191, 0, 0], ![34, 1, 0], ![181, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![34, 1, 0], ![0, 34, 1], ![762, 156, 34]]]
  hmulB := by decide  
  f := ![![![3129, 92, 0], ![-17572, 0, 0]], ![![510, 15, 0], ![-2864, 0, 0]], ![![2931, 86, 0], ![-16460, 1, 0]]]
  g := ![![![1, 0, 0], ![-34, 191, 0], ![-181, 0, 191]], ![![0, 1, 0], ![-7, 34, 1], ![-56, 156, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-146, -34, 1]] ![![191, 0, 0], ![34, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![6494, 191, 0]], ![![-27886, -6494, 191], ![-4202, -1146, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![34, 1, 0]]], ![![![-146, -34, 1]], ![![-22, -6, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-139921, -38330, -2653]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-139921, -38330, -2653]] 
 ![![193, 0, 0], ![0, 193, 0], ![134, 167, 1]] where
  M :=![![![-139921, -38330, -2653], ![-2021586, -553789, -38330], ![-29207460, -8001066, -553789]]]
  hmulB := by decide  
  f := ![![![-7237, -496, 69]], ![![52578, 3527, -496]], ![![38512, 2579, -363]]]
  g := ![![![1117, 2097, -2653], ![16138, 30297, -38330], ![233162, 437729, -553789]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [55, 171, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 192], [0, 1]]
 g := ![![[154, 186], [55], [49], [49], [101], [112], [22, 1]], ![[0, 7], [55], [49], [49], [101], [112], [44, 192]]]
 h' := ![![[22, 192], [47, 147], [62, 21], [21, 7], [173, 186], [18, 115], [141, 43], [0, 1]], ![[0, 1], [0, 46], [138, 172], [175, 186], [19, 7], [39, 78], [122, 150], [22, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [177, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [55, 171, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![923, 253, 354]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-241, -305, 354]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7237, -496, 69]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-7237, -496, 69]] 
 ![![193, 0, 0], ![26, 1, 0], ![96, 0, 1]] where
  M :=![![![-7237, -496, 69], ![52578, 3527, -496], ![-377952, -24798, 3527]]]
  hmulB := by decide  
  f := ![![![-139921, -38330, -2653]], ![![-29324, -8033, -556]], ![![-220932, -60522, -4189]]]
  g := ![![![-5, -496, 69], ![44, 3527, -496], ![-372, -24798, 3527]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-139921, -38330, -2653]] ![![-7237, -496, 69]]
  ![![193, 0, 0]] where
 M := ![![![193, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB199I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB199I3 : PrimesBelowBoundCertificateInterval O 137 193 199 where
  m := 11
  g := ![2, 1, 2, 3, 1, 2, 2, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB199I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
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
      exact NI157N1
      exact NI157N1
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
  β := ![I139N1, I151N1, I157N0, I157N1, I167N1, I173N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [I157N0, I157N1, I157N1], [], [I167N1], [I173N1], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
