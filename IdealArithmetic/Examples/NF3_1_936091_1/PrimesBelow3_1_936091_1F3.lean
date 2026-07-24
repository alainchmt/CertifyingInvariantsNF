
import IdealArithmetic.Examples.NF3_1_936091_1.RI3_1_936091_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-67, -23, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-67, -23, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![72, 116, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-67, -23, 1], ![-194, -50, -22], ![4268, -568, -72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -116, 139]], ![![-1, -1, 1], ![10, 18, -22], ![68, 56, -72]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [101, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 138], [0, 1]]
 g := ![![[99, 131], [24, 83], [51], [122, 45], [112], [81], [1]], ![[27, 8], [76, 56], [51], [110, 94], [112], [81], [1]]]
 h' := ![![[9, 138], [78, 100], [30, 120], [49, 32], [2, 103], [74, 23], [38, 9], [0, 1]], ![[0, 1], [5, 39], [137, 19], [59, 107], [95, 36], [3, 116], [119, 130], [9, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [111, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [101, 130, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-481, -273, -109]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53, 89, -109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![22, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![22, 1, 0]] 
 ![![139, 0, 0], ![22, 1, 0], ![72, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![22, 1, 0], ![0, 22, 1], ![-194, 17, 23]]]
  hmulB := by decide  
  f := ![![![375, 17, 0], ![-2363, 0, 0]], ![![22, 1, 0], ![-138, 0, 0]], ![![180, 8, 0], ![-1134, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 139, 0], ![-72, 0, 139]], ![![0, 1, 0], ![-4, 22, 1], ![-16, 17, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-67, -23, 1]] ![![139, 0, 0], ![22, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![3058, 139, 0]], ![![-9313, -3197, 139], ![-1668, -556, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![22, 1, 0]]], ![![![-67, -23, 1]], ![![-12, -4, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [101, 48, 49, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 12, 48], [47, 136, 101], [0, 1]]
 g := ![![[147, 4, 140], [47, 96], [9, 113, 103], [66, 33], [103, 46, 67], [100, 1], []], ![[129, 123, 70, 10], [20, 107], [122, 127, 66, 44], [34, 142], [130, 38, 78, 10], [117, 20], [6, 69]], ![[90, 114, 88, 122], [114, 20], [100, 84, 100, 105], [54, 88], [74, 57, 23, 136], [100, 144], [102, 69]]]
 h' := ![![[53, 12, 48], [97, 26, 132], [134, 8, 120], [23, 136, 111], [27, 76, 114], [32, 16, 118], [0, 0, 1], [0, 1]], ![[47, 136, 101], [82, 141, 128], [145, 76, 16], [103, 49, 19], [109, 148, 80], [84, 73, 128], [117, 124, 136], [53, 12, 48]], ![[0, 1], [32, 131, 38], [85, 65, 13], [6, 113, 19], [29, 74, 104], [6, 60, 52], [102, 25, 12], [47, 136, 101]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 124], []]
 b := ![[], [1, 83, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [101, 48, 49, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1042851, -262389, 14900]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6999, -1761, 100]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-335, -14, 6]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-335, -14, 6]] 
 ![![151, 0, 0], ![0, 151, 0], ![70, 48, 1]] where
  M :=![![![-335, -14, 6], ![-1164, -233, -8], ![1552, -1300, -241]]]
  hmulB := by decide  
  f := ![![![303, -74, 10]], ![![-1940, 473, -64]], ![![-394, 96, -13]]]
  g := ![![![-5, -2, 6], ![-4, 1, -8], ![122, 68, -241]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [125, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 150], [0, 1]]
 g := ![![[61, 29], [104, 94], [80, 38], [17], [150, 62], [38], [1]], ![[0, 122], [0, 57], [99, 113], [17], [30, 89], [38], [1]]]
 h' := ![![[76, 150], [137, 28], [117, 68], [61, 76], [125, 35], [3, 45], [26, 76], [0, 1]], ![[0, 1], [0, 123], [0, 83], [99, 75], [67, 116], [101, 106], [64, 75], [76, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [109, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [125, 75, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-385, -264, 70]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -24, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![303, -74, 10]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![303, -74, 10]] 
 ![![151, 0, 0], ![102, 1, 0], ![15, 0, 1]] where
  M :=![![![303, -74, 10], ![-1940, 473, -64], ![12416, -3028, 409]]]
  hmulB := by decide  
  f := ![![![-335, -14, 6]], ![![-234, -11, 4]], ![![-23, -10, -1]]]
  g := ![![![51, -74, 10], ![-326, 473, -64], ![2087, -3028, 409]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-335, -14, 6]] ![![303, -74, 10]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [103, 94, 101, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 80, 19], [53, 76, 138], [0, 1]]
 g := ![![[96, 38, 12], [55, 121], [154, 61, 9], [140, 29, 122], [115, 131, 27], [56, 1], []], ![[103, 150, 149, 13], [119, 58], [11, 0, 116, 13], [133, 110, 136, 82], [107, 78, 87, 117], [155, 124], [20, 47]], ![[64, 144, 4, 82], [84, 144], [91, 92, 71, 140], [145, 102, 135, 16], [6, 116, 23, 117], [9, 120], [58, 47]]]
 h' := ![![[3, 80, 19], [12, 36, 13], [152, 70, 146], [24, 57, 3], [87, 143, 114], [41, 128, 59], [0, 0, 1], [0, 1]], ![[53, 76, 138], [147, 90, 102], [1, 147, 23], [8, 124, 55], [4, 29, 77], [149, 138, 8], [147, 39, 76], [3, 80, 19]], ![[0, 1], [25, 31, 42], [55, 97, 145], [144, 133, 99], [106, 142, 123], [12, 48, 90], [132, 118, 80], [53, 76, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 5], []]
 b := ![[], [6, 52, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [103, 94, 101, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-985803, -4082, 12246]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6279, -26, 78]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-63, 59, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-63, 59, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![100, 59, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-63, 59, 1], ![-194, -46, 60], ![-11640, 826, 14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-100, -59, 163]], ![![-1, 0, 1], ![-38, -22, 60], ![-80, 0, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [125, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 162], [0, 1]]
 g := ![![[1, 97], [128, 26], [53], [65], [9], [58, 140], [1]], ![[101, 66], [138, 137], [53], [65], [9], [162, 23], [1]]]
 h' := ![![[38, 162], [137, 74], [116, 134], [59, 78], [69, 37], [85, 3], [38, 38], [0, 1]], ![[0, 1], [15, 89], [155, 29], [89, 85], [8, 126], [36, 160], [15, 125], [38, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [66, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [125, 125, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-457, -268, -104]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![61, 36, -104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-60, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-60, 1, 0]] 
 ![![163, 0, 0], ![103, 1, 0], ![149, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-60, 1, 0], ![0, -60, 1], ![-194, 17, -59]]]
  hmulB := by decide  
  f := ![![![9361, -156, 0], ![25428, 0, 0]], ![![5941, -99, 0], ![16138, 0, 0]], ![![8543, -142, 0], ![23206, 1, 0]]]
  g := ![![![1, 0, 0], ![-103, 163, 0], ![-149, 0, 163]], ![![-1, 1, 0], ![37, -60, 1], ![42, 17, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-63, 59, 1]] ![![163, 0, 0], ![-60, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-9780, 163, 0]], ![![-10269, 9617, 163], ![3586, -3586, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-60, 1, 0]]], ![![![-63, 59, 1]], ![![22, -22, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![4, 34, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![4, 34, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![4, 34, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![4, 34, 1], ![-194, 21, 35], ![-6790, 401, 56]]]
  hmulB := by decide  
  f := ![![![-3, -34, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -34, 167]], ![![0, 0, 1], ![-2, -7, 35], ![-42, -9, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [47, 164, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 166], [0, 1]]
 g := ![![[71, 32], [18, 88], [22, 21], [50], [27], [79, 9], [1]], ![[0, 135], [115, 79], [85, 146], [50], [27], [106, 158], [1]]]
 h' := ![![[3, 166], [156, 115], [135, 103], [32, 122], [85, 102], [128, 19], [120, 3], [0, 1]], ![[0, 1], [0, 52], [110, 64], [64, 45], [57, 65], [18, 148], [129, 164], [3, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [125, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [47, 164, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7354, 3623, 583]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-58, -97, 583]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-35, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-35, 1, 0]] 
 ![![167, 0, 0], ![132, 1, 0], ![111, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-35, 1, 0], ![0, -35, 1], ![-194, 17, -34]]]
  hmulB := by decide  
  f := ![![![4236, -121, 0], ![20207, 0, 0]], ![![3396, -97, 0], ![16200, 0, 0]], ![![2808, -80, 0], ![13395, 1, 0]]]
  g := ![![![1, 0, 0], ![-132, 167, 0], ![-111, 0, 167]], ![![-1, 1, 0], ![27, -35, 1], ![8, 17, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![4, 34, 1]] ![![167, 0, 0], ![-35, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-5845, 167, 0]], ![![668, 5678, 167], ![-334, -1169, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-35, 1, 0]]], ![![![4, 34, 1]], ![![-2, -7, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-28, 43, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-28, 43, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![145, 43, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-28, 43, 1], ![-194, -11, 44], ![-8536, 554, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-145, -43, 173]], ![![-1, 0, 1], ![-38, -11, 44], ![-77, -5, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [166, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 172], [0, 1]]
 g := ![![[154, 57], [22], [77, 64], [1, 139], [51], [31, 43], [1]], ![[12, 116], [22], [42, 109], [25, 34], [51], [21, 130], [1]]]
 h' := ![![[40, 172], [35, 24], [20, 117], [7, 8], [44, 100], [44, 33], [7, 40], [0, 1]], ![[0, 1], [130, 149], [29, 56], [154, 165], [65, 73], [153, 140], [50, 133], [40, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [3, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [166, 133, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1004, 114, -110]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![98, 28, -110]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-44, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-44, 1, 0]] 
 ![![173, 0, 0], ![129, 1, 0], ![140, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-44, 1, 0], ![0, -44, 1], ![-194, 17, -43]]]
  hmulB := by decide  
  f := ![![![3477, -79, 0], ![13667, 0, 0]], ![![2553, -58, 0], ![10035, 0, 0]], ![![2828, -64, 0], ![11116, 1, 0]]]
  g := ![![![1, 0, 0], ![-129, 173, 0], ![-140, 0, 173]], ![![-1, 1, 0], ![32, -44, 1], ![21, 17, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-28, 43, 1]] ![![173, 0, 0], ![-44, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-7612, 173, 0]], ![![-4844, 7439, 173], ![1038, -1903, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-44, 1, 0]]], ![![![-28, 43, 1]], ![![6, -11, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![2, 81, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![2, 81, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![2, 81, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![2, 81, 1], ![-194, 19, 82], ![-15908, 1200, 101]]]
  hmulB := by decide  
  f := ![![![-1, -81, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-2, -81, 179]], ![![0, 0, 1], ![-2, -37, 82], ![-90, -39, 101]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [52, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 178], [0, 1]]
 g := ![![[159, 31], [172, 161], [20], [110], [10, 116], [32, 82], [1]], ![[0, 148], [68, 18], [20], [110], [4, 63], [108, 97], [1]]]
 h' := ![![[145, 178], [6, 116], [175, 55], [118, 60], [17, 17], [126, 37], [127, 145], [0, 1]], ![[0, 1], [0, 63], [95, 124], [47, 119], [155, 162], [121, 142], [30, 34], [145, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [23, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [52, 34, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1500, -606, 145]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, -69, 145]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-82, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-82, 1, 0]] 
 ![![179, 0, 0], ![97, 1, 0], ![78, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-82, 1, 0], ![0, -82, 1], ![-194, 17, -81]]]
  hmulB := by decide  
  f := ![![![14023, -171, 0], ![30609, 0, 0]], ![![7709, -94, 0], ![16827, 0, 0]], ![![6106, -74, 0], ![13328, 1, 0]]]
  g := ![![![1, 0, 0], ![-97, 179, 0], ![-78, 0, 179]], ![![-1, 1, 0], ![44, -82, 1], ![25, 17, -81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![2, 81, 1]] ![![179, 0, 0], ![-82, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-14678, 179, 0]], ![![358, 14499, 179], ![-358, -6623, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-82, 1, 0]]], ![![![2, 81, 1]], ![![-2, -37, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-91, 25, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-91, 25, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![90, 25, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-91, 25, 1], ![-194, -74, 26], ![-5044, 248, -48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -25, 181]], ![![-1, 0, 1], ![-14, -4, 26], ![-4, 8, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [175, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 180], [0, 1]]
 g := ![![[70, 108], [42], [72, 87], [177], [63, 3], [147, 106], [1]], ![[180, 73], [42], [50, 94], [177], [56, 178], [141, 75], [1]]]
 h' := ![![[58, 180], [84, 17], [70, 59], [51, 79], [16, 38], [158, 148], [6, 58], [0, 1]], ![[0, 1], [165, 164], [53, 122], [108, 102], [48, 143], [54, 33], [112, 123], [58, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [45, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [175, 123, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7409, -2658, 386]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-151, -68, 386]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-26, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-26, 1, 0]] 
 ![![181, 0, 0], ![155, 1, 0], ![48, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-26, 1, 0], ![0, -26, 1], ![-194, 17, -25]]]
  hmulB := by decide  
  f := ![![![235, -9, 0], ![1629, 0, 0]], ![![209, -8, 0], ![1449, 0, 0]], ![![108, -4, 0], ![750, 1, 0]]]
  g := ![![![1, 0, 0], ![-155, 181, 0], ![-48, 0, 181]], ![![-1, 1, 0], ![22, -26, 1], ![-9, 17, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-91, 25, 1]] ![![181, 0, 0], ![-26, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-4706, 181, 0]], ![![-16471, 4525, 181], ![2172, -724, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-26, 1, 0]]], ![![![-91, 25, 1]], ![![12, -4, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![55, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![55, 1, 0]] 
 ![![191, 0, 0], ![55, 1, 0], ![31, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![55, 1, 0], ![0, 55, 1], ![-194, 17, 56]]]
  hmulB := by decide  
  f := ![![![2861, 52, 0], ![-9932, 0, 0]], ![![825, 15, 0], ![-2864, 0, 0]], ![![401, 7, 0], ![-1392, 1, 0]]]
  g := ![![![1, 0, 0], ![-55, 191, 0], ![-31, 0, 191]], ![![0, 1, 0], ![-16, 55, 1], ![-15, 17, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![80, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![80, 1, 0]] 
 ![![191, 0, 0], ![80, 1, 0], ![94, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![80, 1, 0], ![0, 80, 1], ![-194, 17, 81]]]
  hmulB := by decide  
  f := ![![![5201, 65, 0], ![-12415, 0, 0]], ![![2160, 27, 0], ![-5156, 0, 0]], ![![2594, 32, 0], ![-6192, 1, 0]]]
  g := ![![![1, 0, 0], ![-80, 191, 0], ![-94, 0, 191]], ![![0, 1, 0], ![-34, 80, 1], ![-48, 17, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![55, 1, 0]] ![![191, 0, 0], ![55, 1, 0]]
  ![![191, 0, 0], ![-31, -81, 1]] where
 M := ![![![36481, 0, 0], ![10505, 191, 0]], ![![10505, 191, 0], ![3025, 110, 1]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![55, 1, 0], ![0, 0, 0]]], ![![![55, 1, 0], ![0, 0, 0]], ![![16, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  
def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-31, -81, 1]] ![![191, 0, 0], ![80, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![15280, 191, 0]], ![![-5921, -15471, 191], ![-2674, -6494, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![80, 1, 0]]], ![![![-31, -81, 1]], ![![-14, -34, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-61, 18, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-61, 18, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![132, 18, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-61, 18, 1], ![-194, -44, 19], ![-3686, 129, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-132, -18, 193]], ![![-1, 0, 1], ![-14, -2, 19], ![-2, 3, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [78, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 192], [0, 1]]
 g := ![![[63, 179], [134], [27], [72], [95], [75], [104, 1]], ![[151, 14], [134], [27], [72], [95], [75], [15, 192]]]
 h' := ![![[104, 192], [70, 117], [10, 110], [46, 42], [114, 74], [169, 148], [187, 123], [0, 1]], ![[0, 1], [79, 76], [63, 83], [168, 151], [90, 119], [121, 45], [48, 70], [104, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [86, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [78, 89, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1598, -326, 132]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82, -14, 132]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-19, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-19, 1, 0]] 
 ![![193, 0, 0], ![174, 1, 0], ![25, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-19, 1, 0], ![0, -19, 1], ![-194, 17, -18]]]
  hmulB := by decide  
  f := ![![![1350, -71, 0], ![13703, 0, 0]], ![![1198, -63, 0], ![12160, 0, 0]], ![![192, -10, 0], ![1949, 1, 0]]]
  g := ![![![1, 0, 0], ![-174, 193, 0], ![-25, 0, 193]], ![![-1, 1, 0], ![17, -19, 1], ![-14, 17, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-61, 18, 1]] ![![193, 0, 0], ![-19, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-3667, 193, 0]], ![![-11773, 3474, 193], ![965, -386, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-19, 1, 0]]], ![![![-61, 18, 1]], ![![5, -2, 0]]]]
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
  g := ![2, 1, 2, 1, 2, 2, 2, 2, 2, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB274I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N0, I191N1]
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
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
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
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N1, I163N1, I167N1, I173N1, I179N1, I181N1, I191N0, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [], [I163N1], [I167N1], [I173N1], [I179N1], [I181N1], [I191N0, I191N0, I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
