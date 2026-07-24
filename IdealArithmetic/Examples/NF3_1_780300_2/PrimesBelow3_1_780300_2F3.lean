
import IdealArithmetic.Examples.NF3_1_780300_2.RI3_1_780300_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![6, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![6, 1, 0]] 
 ![![139, 0, 0], ![6, 1, 0], ![121, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![6, 1, 0], ![0, 6, 2], ![170, 0, 6]]]
  hmulB := by decide  
  f := ![![![637, 106, 0], ![-14734, 0, 0]], ![![18, 3, 0], ![-416, 0, 0]], ![![559, 90, -1], ![-12930, 70, 0]]]
  g := ![![![1, 0, 0], ![-6, 139, 0], ![-121, 0, 139]], ![![0, 1, 0], ![-2, 6, 2], ![-4, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![20, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![20, 1, 0]] 
 ![![139, 0, 0], ![20, 1, 0], ![78, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![20, 1, 0], ![0, 20, 2], ![170, 0, 20]]]
  hmulB := by decide  
  f := ![![![101, 5, 0], ![-695, 0, 0]], ![![-20, -1, 0], ![140, 0, 0]], ![![42, -8, -1], ![-288, 70, 0]]]
  g := ![![![1, 0, 0], ![-20, 139, 0], ![-78, 0, 139]], ![![0, 1, 0], ![-4, 20, 2], ![-10, 0, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-26, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-26, 1, 0]] 
 ![![139, 0, 0], ![113, 1, 0], ![79, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-26, 1, 0], ![0, -26, 2], ![170, 0, -26]]]
  hmulB := by decide  
  f := ![![![3355, -129, 0], ![17931, 0, 0]], ![![2757, -106, 0], ![14735, 0, 0]], ![![1927, -61, -1], ![10299, 70, 0]]]
  g := ![![![1, 0, 0], ![-113, 139, 0], ![-79, 0, 139]], ![![-1, 1, 0], ![20, -26, 2], ![16, 0, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![6, 1, 0]] ![![139, 0, 0], ![20, 1, 0]]
  ![![139, 0, 0], ![60, 13, 1]] where
 M := ![![![19321, 0, 0], ![2780, 139, 0]], ![![834, 139, 0], ![120, 26, 2]]]
 hmul := by decide  
 g := ![![![![79, -13, -1], ![139, 0, 0]], ![![-40, -12, -1], ![139, 0, 0]]], ![![![-54, -12, -1], ![139, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![60, 13, 1]] ![![139, 0, 0], ![-26, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-3614, 139, 0]], ![![8340, 1807, 139], ![-1390, -278, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-26, 1, 0]]], ![![![60, 13, 1]], ![![-10, -2, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-72, 34, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-72, 34, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![77, 34, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-72, 34, 1], ![170, -72, 68], ![5780, 85, -72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -34, 149]], ![![-1, 0, 1], ![-34, -16, 68], ![76, 17, -72]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [102, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [145, 148], [0, 1]]
 g := ![![[76, 19], [143], [23, 96], [125], [134, 49], [16], [1]], ![[0, 130], [143], [86, 53], [125], [87, 100], [16], [1]]]
 h' := ![![[145, 148], [119, 67], [38, 128], [25, 29], [40, 42], [130, 7], [47, 145], [0, 1]], ![[0, 1], [0, 82], [122, 21], [58, 120], [21, 107], [102, 142], [63, 4], [145, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [111, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [102, 4, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![442, 81, -2]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 1, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-68, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-68, 1, 0]] 
 ![![149, 0, 0], ![81, 1, 0], ![72, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-68, 1, 0], ![0, -68, 2], ![170, 0, -68]]]
  hmulB := by decide  
  f := ![![![8773, -129, 0], ![19221, 0, 0]], ![![4761, -70, 0], ![10431, 0, 0]], ![![4232, -28, -1], ![9272, 75, 0]]]
  g := ![![![1, 0, 0], ![-81, 149, 0], ![-72, 0, 149]], ![![-1, 1, 0], ![36, -68, 2], ![34, 0, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-72, 34, 1]] ![![149, 0, 0], ![-68, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10132, 149, 0]], ![![-10728, 5066, 149], ![5066, -2384, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-68, 1, 0]]], ![![![-72, 34, 1]], ![![34, -16, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [77, 43, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 58, 90], [46, 92, 61], [0, 1]]
 g := ![![[83, 61, 8], [58, 63, 11], [73, 36, 10], [10, 8], [127, 93, 99], [148, 1], []], ![[129, 35, 33, 128], [24, 124, 79, 36], [135, 105, 103, 37], [48, 19], [118, 131, 65, 59], [95, 8], [32, 97]], ![[100, 141, 36, 65], [65, 26, 73, 27], [29, 134, 74, 107], [28, 29], [47, 90, 123, 129], [78, 42], [61, 97]]]
 h' := ![![[102, 58, 90], [64, 2, 59], [117, 22, 112], [73, 44, 114], [36, 120, 92], [80, 52, 117], [0, 0, 1], [0, 1]], ![[46, 92, 61], [24, 132, 21], [137, 147, 53], [97, 149, 103], [138, 149, 87], [127, 61, 42], [88, 118, 92], [102, 58, 90]], ![[0, 1], [85, 17, 71], [14, 133, 137], [48, 109, 85], [40, 33, 123], [79, 38, 143], [137, 33, 58], [46, 92, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 92], []]
 b := ![[], [19, 73, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [77, 43, 3, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![387466, 6040, -9060]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2566, 40, -60]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [75, 81, 35, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 36, 34], [143, 120, 123], [0, 1]]
 g := ![![[151, 149, 111], [17, 115], [71, 134, 9], [15, 127, 44], [22, 115, 141], [122, 1], []], ![[80, 35, 93, 119], [73, 17], [143, 42, 32, 62], [33, 82, 82, 91], [40, 15, 86, 69], [36, 113], [139, 57]], ![[106, 45, 60, 72], [147, 153], [127, 123, 153, 137], [74, 51, 65, 125], [88, 120, 150, 28], [56, 40], [50, 57]]]
 h' := ![![[136, 36, 34], [150, 81, 116], [13, 104, 30], [131, 56, 154], [77, 7, 63], [113, 91, 45], [0, 0, 1], [0, 1]], ![[143, 120, 123], [64, 12, 32], [63, 102, 71], [19, 88, 131], [37, 77, 105], [140, 11, 16], [64, 67, 120], [136, 36, 34]], ![[0, 1], [133, 64, 9], [110, 108, 56], [118, 13, 29], [116, 73, 146], [148, 55, 96], [57, 90, 36], [143, 120, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 28], []]
 b := ![[], [85, 88, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [75, 81, 35, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-84623, -5966, -7693]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-539, -38, -49]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [13, 66, 160, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 138, 56], [126, 24, 107], [0, 1]]
 g := ![![[22, 144, 136], [96, 81, 136], [78, 1], [112, 64], [95, 39], [106, 3, 1], []], ![[103, 61, 120, 54], [125, 158, 20, 55], [134, 25], [136, 83], [55, 26], [97, 93, 56, 145], [88, 39]], ![[12, 41, 11, 59], [150, 50, 18, 70], [42, 36], [115, 43], [60, 53], [75, 69, 34, 45], [37, 39]]]
 h' := ![![[40, 138, 56], [56, 86, 25], [38, 88, 25], [20, 119, 1], [3, 5, 155], [89, 137, 107], [0, 0, 1], [0, 1]], ![[126, 24, 107], [63, 82, 37], [125, 32, 149], [20, 120, 5], [141, 54, 88], [82, 110, 134], [130, 161, 24], [40, 138, 56]], ![[0, 1], [3, 158, 101], [74, 43, 152], [91, 87, 157], [49, 104, 83], [60, 79, 85], [73, 2, 138], [126, 24, 107]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 16], []]
 b := ![[], [114, 104, 23], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [13, 66, 160, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-555830, 123554, 3749]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3410, 758, 23]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![16, -26, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![16, -26, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![16, 141, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![16, -26, 1], ![170, 16, -52], ![-4420, 85, 16]]]
  hmulB := by decide  
  f := ![![![-15, 26, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -141, 167]], ![![0, -1, 1], ![6, 44, -52], ![-28, -13, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [118, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 166], [0, 1]]
 g := ![![[139, 122], [89, 87], [9, 81], [100], [94], [83, 127], [1]], ![[89, 45], [130, 80], [99, 86], [100], [94], [20, 40], [1]]]
 h' := ![![[131, 166], [19, 150], [107, 33], [88, 158], [71, 10], [59, 125], [49, 131], [0, 1]], ![[0, 1], [130, 17], [88, 134], [78, 9], [45, 157], [68, 42], [9, 36], [131, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [64, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [118, 36, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![458, 49, -34]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 29, -34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![52, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![52, 1, 0]] 
 ![![167, 0, 0], ![52, 1, 0], ![151, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![52, 1, 0], ![0, 52, 2], ![170, 0, 52]]]
  hmulB := by decide  
  f := ![![![3433, 66, 0], ![-11022, 0, 0]], ![![1092, 21, 0], ![-3506, 0, 0]], ![![3129, 34, -1], ![-10046, 84, 0]]]
  g := ![![![1, 0, 0], ![-52, 167, 0], ![-151, 0, 167]], ![![0, 1, 0], ![-18, 52, 2], ![-46, 0, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![16, -26, 1]] ![![167, 0, 0], ![52, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![8684, 167, 0]], ![![2672, -4342, 167], ![1002, -1336, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![52, 1, 0]]], ![![![16, -26, 1]], ![![6, -8, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![68, -42, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![68, -42, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![68, 131, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![68, -42, 1], ![170, 68, -84], ![-7140, 85, 68]]]
  hmulB := by decide  
  f := ![![![-67, 42, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-68, -131, 173]], ![![0, -1, 1], ![34, 64, -84], ![-68, -51, 68]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [119, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 172], [0, 1]]
 g := ![![[86, 16], [150], [23, 51], [80, 126], [167], [64, 37], [1]], ![[0, 157], [150], [30, 122], [138, 47], [167], [103, 136], [1]]]
 h' := ![![[146, 172], [65, 169], [31, 82], [168, 33], [38, 105], [169, 72], [54, 146], [0, 1]], ![[0, 1], [0, 4], [66, 91], [142, 140], [144, 68], [128, 101], [91, 27], [146, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [84, 160]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [119, 27, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6607, 636, 751]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-257, -565, 751]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![84, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![84, 1, 0]] 
 ![![173, 0, 0], ![84, 1, 0], ![105, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![84, 1, 0], ![0, 84, 2], ![170, 0, 84]]]
  hmulB := by decide  
  f := ![![![4201, 50, 0], ![-8650, 0, 0]], ![![2100, 25, 0], ![-4324, 0, 0]], ![![2541, -12, -1], ![-5232, 87, 0]]]
  g := ![![![1, 0, 0], ![-84, 173, 0], ![-105, 0, 173]], ![![0, 1, 0], ![-42, 84, 2], ![-50, 0, 84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![68, -42, 1]] ![![173, 0, 0], ![84, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![14532, 173, 0]], ![![11764, -7266, 173], ![5882, -3460, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![84, 1, 0]]], ![![![68, -42, 1]], ![![34, -20, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-13, 21, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-13, 21, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![166, 21, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-13, 21, 1], ![170, -13, 42], ![3570, 85, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-166, -21, 179]], ![![-1, 0, 1], ![-38, -5, 42], ![32, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [48, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 178], [0, 1]]
 g := ![![[126, 138], [69, 116], [1], [135], [7, 16], [30, 12], [1]], ![[0, 41], [2, 63], [1], [135], [78, 163], [128, 167], [1]]]
 h' := ![![[38, 178], [89, 106], [176, 37], [90, 178], [22, 99], [171, 4], [131, 38], [0, 1]], ![[0, 1], [0, 73], [150, 142], [52, 1], [25, 80], [144, 175], [143, 141], [38, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [141, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [48, 141, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1112, 502, -121]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![106, 17, -121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-42, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-42, 1, 0]] 
 ![![179, 0, 0], ![137, 1, 0], ![13, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-42, 1, 0], ![0, -42, 2], ![170, 0, -42]]]
  hmulB := by decide  
  f := ![![![4243, -101, 0], ![18079, 0, 0]], ![![3277, -78, 0], ![13963, 0, 0]], ![![341, 13, -1], ![1453, 90, 0]]]
  g := ![![![1, 0, 0], ![-137, 179, 0], ![-13, 0, 179]], ![![-1, 1, 0], ![32, -42, 2], ![4, 0, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-13, 21, 1]] ![![179, 0, 0], ![-42, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-7518, 179, 0]], ![![-2327, 3759, 179], ![716, -895, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-42, 1, 0]]], ![![![-13, 21, 1]], ![![4, -5, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![86, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![86, 1, 0]] 
 ![![181, 0, 0], ![86, 1, 0], ![103, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![86, 1, 0], ![0, 86, 2], ![170, 0, 86]]]
  hmulB := by decide  
  f := ![![![2753, 32, 0], ![-5792, 0, 0]], ![![1290, 15, 0], ![-2714, 0, 0]], ![![1483, -26, -1], ![-3120, 91, 0]]]
  g := ![![![1, 0, 0], ![-86, 181, 0], ![-103, 0, 181]], ![![0, 1, 0], ![-42, 86, 2], ![-48, 0, 86]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-51, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-51, 1, 0]] 
 ![![181, 0, 0], ![130, 1, 0], ![57, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-51, 1, 0], ![0, -51, 2], ![170, 0, -51]]]
  hmulB := by decide  
  f := ![![![4846, -95, 0], ![17195, 0, 0]], ![![3520, -69, 0], ![12490, 0, 0]], ![![1512, -4, -1], ![5365, 91, 0]]]
  g := ![![![1, 0, 0], ![-130, 181, 0], ![-57, 0, 181]], ![![-1, 1, 0], ![36, -51, 2], ![17, 0, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-35, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-35, 1, 0]] 
 ![![181, 0, 0], ![146, 1, 0], ![21, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-35, 1, 0], ![0, -35, 2], ![170, 0, -35]]]
  hmulB := by decide  
  f := ![![![5601, -160, 0], ![28960, 0, 0]], ![![4516, -129, 0], ![23350, 0, 0]], ![![651, -1, -1], ![3366, 91, 0]]]
  g := ![![![1, 0, 0], ![-146, 181, 0], ![-21, 0, 181]], ![![-1, 1, 0], ![28, -35, 2], ![5, 0, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![86, 1, 0]] ![![181, 0, 0], ![-51, 1, 0]]
  ![![181, 0, 0], ![-21, -73, 1]] where
 M := ![![![32761, 0, 0], ![-9231, 181, 0]], ![![15566, 181, 0], ![-4386, 35, 2]]]
 hmul := by decide  
 g := ![![![![181, 0, 0], ![0, 0, 0]], ![![-30, 74, -1], ![181, 0, 0]]], ![![![86, 1, 0], ![0, 0, 0]], ![![-3, 74, -1], ![183, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-21, -73, 1]] ![![181, 0, 0], ![-35, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-6335, 181, 0]], ![![-3801, -13213, 181], ![905, 2534, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-35, 1, 0]]], ![![![-21, -73, 1]], ![![5, 14, -1]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![5, 17, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![5, 17, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![5, 17, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![5, 17, 1], ![170, 5, 34], ![2890, 85, 5]]]
  hmulB := by decide  
  f := ![![![-4, -17, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -17, 191]], ![![0, 0, 1], ![0, -3, 34], ![15, 0, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [152, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [147, 190], [0, 1]]
 g := ![![[136, 184], [15, 43], [159, 13], [27, 90], [174, 39], [8, 26], [1]], ![[62, 7], [33, 148], [160, 178], [78, 101], [177, 152], [10, 165], [1]]]
 h' := ![![[147, 190], [12, 152], [89, 59], [98, 108], [101, 102], [121, 82], [39, 147], [0, 1]], ![[0, 1], [9, 39], [167, 132], [121, 83], [6, 89], [142, 109], [65, 44], [147, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [149]]
 b := ![[], [111, 170]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [152, 44, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![832, 384, 90]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, -6, 90]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-34, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-34, 1, 0]] 
 ![![191, 0, 0], ![157, 1, 0], ![186, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-34, 1, 0], ![0, -34, 2], ![170, 0, -34]]]
  hmulB := by decide  
  f := ![![![4557, -134, 0], ![25594, 0, 0]], ![![3775, -111, 0], ![21202, 0, 0]], ![![4458, -114, -1], ![25038, 96, 0]]]
  g := ![![![1, 0, 0], ![-157, 191, 0], ![-186, 0, 191]], ![![-1, 1, 0], ![26, -34, 2], ![34, 0, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![5, 17, 1]] ![![191, 0, 0], ![-34, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-6494, 191, 0]], ![![955, 3247, 191], ![0, -573, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-34, 1, 0]]], ![![![5, 17, 1]], ![![0, -3, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [184, 176, 187, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [38, 26, 101], [161, 166, 92], [0, 1]]
 g := ![![[90, 184, 118], [2, 43], [72, 166], [3, 56], [104, 130], [34, 36], [1]], ![[74, 113, 60, 42], [], [41, 50], [153, 186], [183, 175], [122, 121], [181, 48, 148, 67]], ![[121, 146, 177, 112], [133, 43], [97, 25], [16, 62], [145, 86], [10, 96], [125, 105, 129, 126]]]
 h' := ![![[38, 26, 101], [11, 44, 73], [46, 191, 64], [39, 74, 72], [165, 143, 40], [1, 50, 55], [9, 17, 6], [0, 1]], ![[161, 166, 92], [110, 76, 157], [127, 93], [12, 133, 126], [76, 21, 46], [121, 149, 91], [145, 148, 11], [38, 26, 101]], ![[0, 1], [75, 73, 156], [187, 102, 129], [146, 179, 188], [52, 29, 107], [171, 187, 47], [9, 28, 176], [161, 166, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 64], []]
 b := ![[], [130, 152, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [184, 176, 187, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1535508, 158260, 20072]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7956, 820, 104]
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
  g := ![3, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB250I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1, I181N2]
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
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![181, 181, 181]
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
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I149N1, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [], [], [], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
