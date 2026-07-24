
import IdealArithmetic.Examples.NF3_1_662796_4.RI3_1_662796_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-132, 11, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-132, 11, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![7, 11, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-132, 11, 1], ![494, -18, 11], ![5434, 1748, -18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -11, 139]], ![![-1, 0, 1], ![3, -1, 11], ![40, 14, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [118, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 138], [0, 1]]
 g := ![![[55, 86], [9, 100], [49], [2, 112], [4], [42], [1]], ![[0, 53], [0, 39], [49], [92, 27], [4], [42], [1]]]
 h' := ![![[43, 138], [50, 15], [13, 129], [42, 132], [125, 23], [72, 137], [21, 43], [0, 1]], ![[0, 1], [0, 124], [0, 10], [19, 7], [2, 116], [125, 2], [63, 96], [43, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [125, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [118, 96, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1106, 626, 19]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![7, 3, 19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-11, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-11, 1, 0]] 
 ![![139, 0, 0], ![128, 1, 0], ![18, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-11, 1, 0], ![0, -11, 1], ![494, 114, -11]]]
  hmulB := by decide  
  f := ![![![485, -44, 0], ![6116, 0, 0]], ![![430, -39, 0], ![5422, 0, 0]], ![![78, -7, 0], ![984, 1, 0]]]
  g := ![![![1, 0, 0], ![-128, 139, 0], ![-18, 0, 139]], ![![-1, 1, 0], ![10, -11, 1], ![-100, 114, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-132, 11, 1]] ![![139, 0, 0], ![-11, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-1529, 139, 0]], ![![-18348, 1529, 139], ![1946, -139, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-11, 1, 0]]], ![![![-132, 11, 1]], ![![14, -1, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-50, 8, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-50, 8, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![99, 8, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-50, 8, 1], ![494, 64, 8], ![3952, 1406, 64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -8, 149]], ![![-1, 0, 1], ![-2, 0, 8], ![-16, 6, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [23, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 148], [0, 1]]
 g := ![![[127, 107], [144], [24, 31], [142], [33, 29], [54], [1]], ![[33, 42], [144], [65, 118], [142], [105, 120], [54], [1]]]
 h' := ![![[59, 148], [114, 16], [44, 12], [59, 39], [135, 69], [32, 25], [126, 59], [0, 1]], ![[0, 1], [15, 133], [7, 137], [125, 110], [34, 80], [17, 124], [31, 90], [59, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [120, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [23, 90, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5994, 2902, 1294]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-900, -50, 1294]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-8, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-8, 1, 0]] 
 ![![149, 0, 0], ![141, 1, 0], ![85, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-8, 1, 0], ![0, -8, 1], ![494, 114, -8]]]
  hmulB := by decide  
  f := ![![![481, -60, 0], ![8940, 0, 0]], ![![457, -57, 0], ![8494, 0, 0]], ![![289, -36, 0], ![5372, 1, 0]]]
  g := ![![![1, 0, 0], ![-141, 149, 0], ![-85, 0, 149]], ![![-1, 1, 0], ![7, -8, 1], ![-100, 114, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-50, 8, 1]] ![![149, 0, 0], ![-8, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-1192, 149, 0]], ![![-7450, 1192, 149], ![894, 0, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-8, 1, 0]]], ![![![-50, 8, 1]], ![![6, 0, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [92, 117, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 39, 54], [137, 111, 97], [0, 1]]
 g := ![![[139, 51, 110], [47, 40, 91], [139, 15, 19], [125, 100], [136, 56, 128], [33, 1], []], ![[99, 49, 43, 77], [52, 59, 114, 14], [88, 29, 54, 82], [90, 144], [115, 79, 67, 107], [143, 90], [25, 47]], ![[129, 90, 133, 25], [104, 77, 124, 10], [118, 82, 31, 110], [138, 31], [146, 14, 58, 125], [34, 11], [133, 47]]]
 h' := ![![[47, 39, 54], [55, 127, 84], [47, 112, 98], [115, 85, 87], [21, 30, 10], [135, 124, 66], [0, 0, 1], [0, 1]], ![[137, 111, 97], [41, 92, 25], [17, 81, 14], [119, 87, 53], [68, 70, 12], [108, 143, 130], [60, 41, 111], [47, 39, 54]], ![[0, 1], [127, 83, 42], [134, 109, 39], [140, 130, 11], [1, 51, 129], [133, 35, 106], [40, 110, 39], [137, 111, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 100], []]
 b := ![[], [55, 81, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [92, 117, 118, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![212306, -97395, -17667]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1406, -645, -117]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [141, 140, 53, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 38, 145], [115, 118, 12], [0, 1]]
 g := ![![[68, 100, 100], [17, 67], [30, 85, 3], [113, 143, 3], [109], [104, 1], []], ![[92, 3, 148, 64], [], [137, 152, 128, 144], [84, 37, 15, 64], [17, 104, 140, 48], [101, 108], [91, 144]], ![[51, 131, 57, 30], [2, 67], [9, 34, 91, 99], [138, 89, 49, 148], [132, 35, 29, 109], [7, 31], [67, 144]]]
 h' := ![![[146, 38, 145], [39, 44, 147], [9, 110, 99], [81, 102, 72], [17, 13, 72], [94, 57], [0, 0, 1], [0, 1]], ![[115, 118, 12], [113, 96, 19], [120, 126], [91, 57, 50], [64, 129, 19], [95, 125, 101], [7, 32, 118], [146, 38, 145]], ![[0, 1], [132, 17, 148], [147, 78, 58], [128, 155, 35], [34, 15, 66], [55, 132, 56], [10, 125, 38], [115, 118, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [116, 135], []]
 b := ![[], [31, 114, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [141, 140, 53, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5233595, -2483583, -281815]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33335, -15819, -1795]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-57, -63, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-57, -63, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![106, 100, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-57, -63, 1], ![494, 57, -63], ![-31122, -6688, 57]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-106, -100, 163]], ![![-1, -1, 1], ![44, 39, -63], ![-228, -76, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [90, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 162], [0, 1]]
 g := ![![[133, 96], [70, 140], [40], [85], [97], [103, 151], [1]], ![[0, 67], [73, 23], [40], [85], [97], [140, 12], [1]]]
 h' := ![![[92, 162], [57, 111], [136, 38], [98, 23], [24, 133], [21, 74], [73, 92], [0, 1]], ![[0, 1], [0, 52], [46, 125], [95, 140], [35, 30], [146, 89], [61, 71], [92, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [161, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [90, 71, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1078, 651, 44]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -23, 44]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![63, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![63, 1, 0]] 
 ![![163, 0, 0], ![63, 1, 0], ![106, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![63, 1, 0], ![0, 63, 1], ![494, 114, 63]]]
  hmulB := by decide  
  f := ![![![2269, 36, 0], ![-5868, 0, 0]], ![![819, 13, 0], ![-2118, 0, 0]], ![![1474, 23, 0], ![-3812, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 163, 0], ![-106, 0, 163]], ![![0, 1, 0], ![-25, 63, 1], ![-82, 114, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-57, -63, 1]] ![![163, 0, 0], ![63, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![10269, 163, 0]], ![![-9291, -10269, 163], ![-3097, -3912, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![63, 1, 0]]], ![![![-57, -63, 1]], ![![-19, -24, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [45, 88, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 146, 67], [23, 20, 100], [0, 1]]
 g := ![![[103, 7, 44], [81, 114, 152], [99, 120, 8], [129, 93], [149, 1], [0, 64, 1], []], ![[159, 95, 2, 138], [113, 154, 149, 105], [106, 47, 81, 123], [0, 12], [114, 19], [110, 158, 87, 80], [81, 147]], ![[64, 133, 115, 1], [5, 6, 118, 122], [106, 78, 125, 121], [95, 122], [88, 77], [33, 119, 49, 12], [48, 147]]]
 h' := ![![[41, 146, 67], [29, 10, 85], [54, 92, 73], [164, 31, 26], [142, 36, 107], [0, 126, 1], [0, 0, 1], [0, 1]], ![[23, 20, 100], [165, 56, 32], [66, 47, 109], [137, 63, 92], [53, 127, 43], [29, 92, 112], [40, 66, 20], [41, 146, 67]], ![[0, 1], [67, 101, 50], [7, 28, 152], [54, 73, 49], [133, 4, 17], [98, 116, 54], [39, 101, 146], [23, 20, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125, 121], []]
 b := ![[], [95, 102, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [45, 88, 103, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8832463, 2687531, 215263]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52889, 16093, 1289]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [53, 94, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 165, 146], [77, 7, 27], [0, 1]]
 g := ![![[107, 134, 56], [145, 4], [14, 93, 21], [145, 32, 23], [171, 83], [156, 115, 1], []], ![[121, 110, 151, 7], [79, 95], [21, 74, 136, 66], [131, 115, 82, 45], [80, 118], [160, 54, 116, 61], [16, 37]], ![[107, 56, 41, 128], [127, 10], [12, 95, 69, 68], [48, 107, 80, 75], [154, 151], [95, 62, 92, 171], [135, 37]]]
 h' := ![![[38, 165, 146], [5, 81, 70], [123, 122, 171], [100, 49, 114], [18, 13, 159], [36, 1, 157], [0, 0, 1], [0, 1]], ![[77, 7, 27], [169, 38, 33], [107, 77, 152], [14, 137, 167], [126, 1, 70], [53, 112, 34], [77, 79, 7], [38, 165, 146]], ![[0, 1], [2, 54, 70], [32, 147, 23], [87, 160, 65], [18, 159, 117], [7, 60, 155], [158, 94, 165], [77, 7, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 61], []]
 b := ![[], [137, 169, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [53, 94, 58, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![113142, -16435, -4844]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![654, -95, -28]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-105, -3, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-105, -3, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![74, 176, 1]] where
  M :=![![![-105, -3, 1], ![494, 9, -3], ![-1482, 152, 9]]]
  hmulB := by decide  
  f := ![![![3, 1, 0]], ![![0, 3, 1]], ![![4, 4, 1]]]
  g := ![![![-1, -1, 1], ![4, 3, -3], ![-12, -8, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [47, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 178], [0, 1]]
 g := ![![[162, 80], [71, 66], [60], [3], [145, 110], [135, 87], [1]], ![[0, 99], [0, 113], [60], [3], [146, 69], [17, 92], [1]]]
 h' := ![![[83, 178], [64, 120], [112, 31], [28, 113], [166, 19], [99, 17], [132, 83], [0, 1]], ![[0, 1], [0, 59], [0, 148], [99, 66], [132, 160], [78, 162], [40, 96], [83, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [164, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [47, 96, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2023, 2528, 649]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-257, -624, 649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![3, 1, 0]] 
 ![![179, 0, 0], ![3, 1, 0], ![170, 0, 1]] where
  M :=![![![3, 1, 0], ![0, 3, 1], ![494, 114, 3]]]
  hmulB := by decide  
  f := ![![![-105, -3, 1]], ![![1, 0, 0]], ![![-108, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 3, 1], ![-2, 114, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-105, -3, 1]] ![![3, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-162, 26, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-162, 26, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![19, 26, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-162, 26, 1], ![494, -48, 26], ![12844, 3458, -48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -26, 181]], ![![-1, 0, 1], ![0, -4, 26], ![76, 26, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [10, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 180], [0, 1]]
 g := ![![[27, 67], [27], [33, 132], [178], [17, 180], [177, 138], [1]], ![[37, 114], [27], [50, 49], [178], [106, 1], [22, 43], [1]]]
 h' := ![![[92, 180], [30, 130], [32, 82], [151, 48], [11, 97], [40, 162], [171, 92], [0, 1]], ![[0, 1], [44, 51], [155, 99], [42, 133], [66, 84], [102, 19], [128, 89], [92, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [145, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [10, 89, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19568, -3514, 742]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-186, -126, 742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-26, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-26, 1, 0]] 
 ![![181, 0, 0], ![155, 1, 0], ![48, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-26, 1, 0], ![0, -26, 1], ![494, 114, -26]]]
  hmulB := by decide  
  f := ![![![235, -9, 0], ![1629, 0, 0]], ![![209, -8, 0], ![1449, 0, 0]], ![![108, -4, 0], ![750, 1, 0]]]
  g := ![![![1, 0, 0], ![-155, 181, 0], ![-48, 0, 181]], ![![-1, 1, 0], ![22, -26, 1], ![-88, 114, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-162, 26, 1]] ![![181, 0, 0], ![-26, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-4706, 181, 0]], ![![-29322, 4706, 181], ![4706, -724, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-26, 1, 0]]], ![![![-162, 26, 1]], ![![26, -4, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-35, 35, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-35, 35, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![156, 35, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-35, 35, 1], ![494, 79, 35], ![17290, 4484, 79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-156, -35, 191]], ![![-1, 0, 1], ![-26, -6, 35], ![26, 9, 79]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [43, 172, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 190], [0, 1]]
 g := ![![[4, 40], [110, 90], [87, 184], [39, 49], [180, 134], [68, 170], [1]], ![[0, 151], [101, 101], [145, 7], [15, 142], [52, 57], [51, 21], [1]]]
 h' := ![![[19, 190], [45, 68], [79, 89], [42, 39], [91, 184], [132, 33], [148, 19], [0, 1]], ![[0, 1], [0, 123], [51, 102], [19, 152], [149, 7], [186, 158], [127, 172], [19, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [86, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [43, 172, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1460, 68, 313]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-248, -57, 313]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-35, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-35, 1, 0]] 
 ![![191, 0, 0], ![156, 1, 0], ![112, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-35, 1, 0], ![0, -35, 1], ![494, 114, -35]]]
  hmulB := by decide  
  f := ![![![5146, -147, 0], ![28077, 0, 0]], ![![4166, -119, 0], ![22730, 0, 0]], ![![3052, -87, 0], ![16652, 1, 0]]]
  g := ![![![1, 0, 0], ![-156, 191, 0], ![-112, 0, 191]], ![![-1, 1, 0], ![28, -35, 1], ![-70, 114, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-35, 35, 1]] ![![191, 0, 0], ![-35, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-6685, 191, 0]], ![![-6685, 6685, 191], ![1719, -1146, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-35, 1, 0]]], ![![![-35, 35, 1]], ![![9, -6, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![16, 55, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![16, 55, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![16, 55, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![16, 55, 1], ![494, 130, 55], ![27170, 6764, 130]]]
  hmulB := by decide  
  f := ![![![-15, -55, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -55, 193]], ![![0, 0, 1], ![-2, -15, 55], ![130, -2, 130]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [10, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [124, 192], [0, 1]]
 g := ![![[142, 6], [139], [187], [181], [150], [72], [124, 1]], ![[114, 187], [139], [187], [181], [150], [72], [55, 192]]]
 h' := ![![[124, 192], [20, 149], [161, 77], [78, 103], [99, 48], [21, 27], [111, 119], [0, 1]], ![[0, 1], [161, 44], [59, 116], [112, 90], [68, 145], [88, 166], [6, 74], [124, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [125, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [10, 69, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4032, 1122, 59]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, -11, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-55, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-55, 1, 0]] 
 ![![193, 0, 0], ![138, 1, 0], ![63, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-55, 1, 0], ![0, -55, 1], ![494, 114, -55]]]
  hmulB := by decide  
  f := ![![![10451, -190, 0], ![36670, 0, 0]], ![![7536, -137, 0], ![26442, 0, 0]], ![![3481, -63, 0], ![12214, 1, 0]]]
  g := ![![![1, 0, 0], ![-138, 193, 0], ![-63, 0, 193]], ![![-1, 1, 0], ![39, -55, 1], ![-61, 114, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![16, 55, 1]] ![![193, 0, 0], ![-55, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-10615, 193, 0]], ![![3088, 10615, 193], ![-386, -2895, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-55, 1, 0]]], ![![![16, 55, 1]], ![![-2, -15, 0]]]]
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


lemma PB231I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB231I3 : PrimesBelowBoundCertificateInterval O 137 193 231 where
  m := 11
  g := ![2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB231I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
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
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
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
  β := ![I139N1, I149N1, I163N1, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N1], [], [], [I163N1], [], [], [I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
