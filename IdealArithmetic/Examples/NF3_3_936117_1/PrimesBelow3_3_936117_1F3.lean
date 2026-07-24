
import IdealArithmetic.Examples.NF3_3_936117_1.RI3_3_936117_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [51, 131, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 136, 8], [32, 2, 131], [0, 1]]
 g := ![![[55, 27, 89], [117, 20, 117], [80, 122], [118, 80, 28], [100, 52], [7, 1], []], ![[52, 123, 82, 26], [107, 93, 110, 10], [99, 63], [91, 88, 113, 43], [11, 86], [94, 4], [122, 64]], ![[111, 111, 126, 86], [78, 89, 134, 20], [115, 41], [58, 31, 42, 6], [5, 41], [23, 9], [138, 64]]]
 h' := ![![[114, 136, 8], [10, 100, 111], [103, 101, 16], [98, 68, 119], [29, 138, 58], [60, 5, 57], [0, 0, 1], [0, 1]], ![[32, 2, 131], [75, 72, 49], [44, 100, 6], [111, 22, 87], [132, 126, 108], [50, 22, 15], [102, 86, 2], [114, 136, 8]], ![[0, 1], [76, 106, 118], [102, 77, 117], [95, 49, 72], [75, 14, 112], [57, 112, 67], [102, 53, 136], [32, 2, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 136], []]
 b := ![[], [45, 58, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [51, 131, 132, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2085, 3892, 3892]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, 28, 28]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-108, -16, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-108, -16, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![41, 133, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-108, -16, 1], ![89, -42, -16], ![-1424, -967, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -133, 149]], ![![-1, -1, 1], ![5, 14, -16], ![2, 31, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [140, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 148], [0, 1]]
 g := ![![[137, 33], [5], [67, 19], [107], [91, 114], [42], [1]], ![[0, 116], [5], [101, 130], [107], [146, 35], [42], [1]]]
 h' := ![![[41, 148], [94, 114], [7, 68], [32, 82], [74, 133], [12, 76], [9, 41], [0, 1]], ![[0, 1], [0, 35], [113, 81], [116, 67], [14, 16], [148, 73], [51, 108], [41, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [33, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [140, 108, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1035, -203, 916]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-259, -819, 916]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![16, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![16, 1, 0]] 
 ![![149, 0, 0], ![16, 1, 0], ![42, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![16, 1, 0], ![0, 16, 1], ![89, 66, 16]]]
  hmulB := by decide  
  f := ![![![417, 26, 0], ![-3874, 0, 0]], ![![16, 1, 0], ![-148, 0, 0]], ![![98, 6, 0], ![-910, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 149, 0], ![-42, 0, 149]], ![![0, 1, 0], ![-2, 16, 1], ![-11, 66, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-108, -16, 1]] ![![149, 0, 0], ![16, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![2384, 149, 0]], ![![-16092, -2384, 149], ![-1639, -298, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![16, 1, 0]]], ![![![-108, -16, 1]], ![![-11, -2, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [132, 68, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [40, 45, 25], [89, 105, 126], [0, 1]]
 g := ![![[18, 16, 137], [150, 111, 118], [2, 104, 32], [84, 121], [71, 14, 10], [129, 1], []], ![[14, 89, 44, 103], [34, 79, 31, 1], [140, 150, 57, 85], [112, 98], [74, 5, 147, 38], [136, 2], [127, 21]], ![[29, 67], [25, 0, 115, 51], [74, 102, 13, 28], [4, 55], [125, 1, 55, 131], [112, 62], [26, 21]]]
 h' := ![![[40, 45, 25], [132, 148, 99], [38, 45, 119], [35, 58, 33], [141, 136, 140], [35, 5, 114], [0, 0, 1], [0, 1]], ![[89, 105, 126], [18, 144, 52], [111, 13, 30], [92, 136, 83], [94, 49, 131], [36, 107, 15], [87, 44, 105], [40, 45, 25]], ![[0, 1], [34, 10], [70, 93, 2], [69, 108, 35], [12, 117, 31], [34, 39, 22], [110, 107, 45], [89, 105, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 22], []]
 b := ![[], [84, 117, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [132, 68, 22, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-136202, 17969, -25217]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-902, 119, -167]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-115, -39, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-115, -39, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![42, 118, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-115, -39, 1], ![89, -49, -39], ![-3471, -2485, -49]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -118, 157]], ![![-1, -1, 1], ![11, 29, -39], ![-9, 21, -49]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [139, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 156], [0, 1]]
 g := ![![[7, 99], [56], [29, 68], [56, 47], [13, 13], [19], [1]], ![[78, 58], [56], [119, 89], [12, 110], [81, 144], [19], [1]]]
 h' := ![![[126, 156], [155, 16], [51, 128], [66, 15], [77, 19], [38, 22], [18, 126], [0, 1]], ![[0, 1], [130, 141], [8, 29], [72, 142], [116, 138], [141, 135], [37, 31], [126, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119]]
 b := ![[], [98, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [139, 31, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-363, 438, 496]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-135, -370, 496]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![39, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![39, 1, 0]] 
 ![![157, 0, 0], ![39, 1, 0], ![49, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![39, 1, 0], ![0, 39, 1], ![89, 66, 39]]]
  hmulB := by decide  
  f := ![![![3238, 83, 0], ![-13031, 0, 0]], ![![780, 20, 0], ![-3139, 0, 0]], ![![946, 24, 0], ![-3807, 1, 0]]]
  g := ![![![1, 0, 0], ![-39, 157, 0], ![-49, 0, 157]], ![![0, 1, 0], ![-10, 39, 1], ![-28, 66, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-115, -39, 1]] ![![157, 0, 0], ![39, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![6123, 157, 0]], ![![-18055, -6123, 157], ![-4396, -1570, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![39, 1, 0]]], ![![![-115, -39, 1]], ![![-28, -10, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-242, -206, -23]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-242, -206, -23]] 
 ![![163, 0, 0], ![0, 163, 0], ![131, 94, 1]] where
  M :=![![![-242, -206, -23], ![-2047, -1760, -206], ![-18334, -15643, -1760]]]
  hmulB := by decide  
  f := ![![![-766, -17, 12]], ![![1068, 26, -17]], ![![-9, 1, 0]]]
  g := ![![![17, 12, -23], ![153, 108, -206], ![1302, 919, -1760]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [88, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 162], [0, 1]]
 g := ![![[126, 113], [93, 64], [104], [64], [77], [151, 16], [1]], ![[0, 50], [0, 99], [104], [64], [77], [87, 147], [1]]]
 h' := ![![[159, 162], [129, 73], [32, 8], [43, 58], [123, 155], [78, 27], [75, 159], [0, 1]], ![[0, 1], [0, 90], [0, 155], [137, 105], [155, 8], [133, 136], [91, 4], [159, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [33, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [88, 4, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![266, 217, 63]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-49, -35, 63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-766, -17, 12]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-766, -17, 12]] 
 ![![163, 0, 0], ![69, 1, 0], ![129, 0, 1]] where
  M :=![![![-766, -17, 12], ![1068, 26, -17], ![-1513, -54, 26]]]
  hmulB := by decide  
  f := ![![![-242, -206, -23]], ![![-115, -98, -11]], ![![-304, -259, -29]]]
  g := ![![![-7, -17, 12], ![9, 26, -17], ![-7, -54, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-242, -206, -23]] ![![-766, -17, 12]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-96, 53, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-96, 53, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![71, 53, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-96, 53, 1], ![89, -30, 53], ![4717, 3587, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -53, 167]], ![![-1, 0, 1], ![-22, -17, 53], ![41, 31, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [81, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 166], [0, 1]]
 g := ![![[97, 33], [82, 54], [58, 24], [150], [32], [116, 64], [1]], ![[0, 134], [151, 113], [33, 143], [150], [32], [105, 103], [1]]]
 h' := ![![[159, 166], [38, 130], [145, 87], [18, 109], [12, 145], [123, 115], [86, 159], [0, 1]], ![[0, 1], [0, 37], [117, 80], [148, 58], [21, 22], [38, 52], [150, 8], [159, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [36, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [81, 8, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3472, 2787, 437]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-165, -122, 437]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-53, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-53, 1, 0]] 
 ![![167, 0, 0], ![114, 1, 0], ![30, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-53, 1, 0], ![0, -53, 1], ![89, 66, -53]]]
  hmulB := by decide  
  f := ![![![6785, -128, 0], ![21376, 0, 0]], ![![4612, -87, 0], ![14530, 0, 0]], ![![1236, -23, 0], ![3894, 1, 0]]]
  g := ![![![1, 0, 0], ![-114, 167, 0], ![-30, 0, 167]], ![![-1, 1, 0], ![36, -53, 1], ![-35, 66, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-96, 53, 1]] ![![167, 0, 0], ![-53, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-8851, 167, 0]], ![![-16032, 8851, 167], ![5177, -2839, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-53, 1, 0]]], ![![![-96, 53, 1]], ![![31, -17, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [156, 159, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 171, 1], [87, 1, 172], [0, 1]]
 g := ![![[48, 116, 73], [133, 81], [172, 66, 33], [105, 80, 47], [131, 113], [74, 38, 1], []], ![[155, 25, 134, 23], [29, 92], [148, 54, 96, 22], [158, 46, 165, 144], [106, 157], [164, 164, 30, 1], [34, 1]], ![[140, 166, 19, 167], [5, 158], [114, 111, 132, 29], [32, 63, 123, 37], [65, 139], [3, 147, 37, 169], [36, 1]]]
 h' := ![![[124, 171, 1], [128, 79, 108], [156, 154, 164], [55, 100, 129], [111, 108, 77], [47, 125, 74], [0, 0, 1], [0, 1]], ![[87, 1, 172], [15, 37, 14], [53, 65, 145], [57, 105, 56], [167, 72, 12], [21, 47, 26], [38, 170, 1], [124, 171, 1]], ![[0, 1], [118, 57, 51], [129, 127, 37], [154, 141, 161], [36, 166, 84], [90, 1, 73], [50, 3, 171], [87, 1, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137, 38], []]
 b := ![[], [16, 155, 135], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [156, 159, 135, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23009, -14013, 4671]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-133, -81, 27]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [135, 177, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 129, 68], [25, 49, 111], [0, 1]]
 g := ![![[99, 153, 77], [61, 138, 77], [67, 61], [77, 61], [124, 84, 4], [67, 85, 1], []], ![[17, 130, 81, 17], [139, 87, 7, 177], [56, 88], [41, 110], [95, 115, 53, 22], [43, 82, 168, 20], [137, 149]], ![[1, 101, 5, 131], [79, 153, 32, 58], [100, 172], [110, 158], [152, 161, 84, 96], [11, 176, 67, 50], [94, 149]]]
 h' := ![![[60, 129, 68], [178, 24, 16], [51, 38, 163], [44, 123, 132], [86, 81, 132], [84, 115, 2], [0, 0, 1], [0, 1]], ![[25, 49, 111], [115, 87, 89], [75, 35, 10], [81, 127, 154], [109, 79, 162], [106, 27, 42], [141, 114, 49], [60, 129, 68]], ![[0, 1], [163, 68, 74], [5, 106, 6], [59, 108, 72], [125, 19, 64], [130, 37, 135], [107, 65, 129], [25, 49, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 27], []]
 b := ![[], [137, 122, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [135, 177, 94, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167544, 205313, 61576]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![936, 1147, 344]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 6, -1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![24, 6, -1]] 
 ![![181, 0, 0], ![21, 1, 0], ![102, 0, 1]] where
  M :=![![![24, 6, -1], ![-89, -42, 6], ![534, 307, -42]]]
  hmulB := by decide  
  f := ![![![78, 55, 6]], ![![12, 9, 1]], ![![71, 54, 6]]]
  g := ![![![0, 6, -1], ![1, -42, 6], ![-9, 307, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![194, 4, -3]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![194, 4, -3]] 
 ![![181, 0, 0], ![39, 1, 0], ![108, 0, 1]] where
  M :=![![![194, 4, -3], ![-267, -4, 4], ![356, -3, -4]]]
  hmulB := by decide  
  f := ![![![28, 25, 4]], ![![8, 7, 1]], ![![29, 26, 4]]]
  g := ![![![2, 4, -3], ![-3, -4, 4], ![5, -3, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![194, 166, 19]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![194, 166, 19]] 
 ![![181, 0, 0], ![121, 1, 0], ![20, 0, 1]] where
  M :=![![![194, 166, 19], ![1691, 1448, 166], ![14774, 12647, 1448]]]
  hmulB := by decide  
  f := ![![![2698, 75, -44]], ![![1782, 49, -29]], ![![335, 14, -6]]]
  g := ![![![-112, 166, 19], ![-977, 1448, 166], ![-8533, 12647, 1448]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![24, 6, -1]] ![![194, 4, -3]]
  ![![2698, 75, -44]] where
 M := ![![![2698, 75, -44]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![2698, 75, -44]] ![![194, 166, 19]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [41, 42, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [184, 181, 41], [86, 9, 150], [0, 1]]
 g := ![![[98, 14, 96], [174, 103, 134], [4, 147, 135], [60, 113, 92], [6, 95, 46], [87, 79, 1], []], ![[177, 85, 82, 7], [163, 68, 140, 33], [173, 158, 115, 91], [188, 69, 55, 182], [139, 180, 138, 53], [163, 190, 151, 74], [189, 153]], ![[145, 130, 37, 67], [72, 97, 47, 130], [26, 183, 30, 64], [75, 4, 156, 60], [81, 121, 84, 3], [115, 131, 82, 102], [80, 153]]]
 h' := ![![[184, 181, 41], [124, 85, 124], [27, 64, 33], [23, 74, 138], [136, 79, 130], [62, 174, 76], [0, 0, 1], [0, 1]], ![[86, 9, 150], [111, 86, 17], [82, 102, 56], [11, 123, 74], [187, 142, 16], [14, 183, 178], [131, 63, 9], [184, 181, 41]], ![[0, 1], [17, 20, 50], [19, 25, 102], [58, 185, 170], [143, 161, 45], [86, 25, 128], [105, 128, 181], [86, 9, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8, 137], []]
 b := ![[], [74, 52, 183], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [41, 42, 112, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1150011, -715868, 107724]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6021, -3748, 564]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [13, 4, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [108, 41, 152], [63, 151, 41], [0, 1]]
 g := ![![[155, 116, 161], [172, 62], [166, 27], [162, 49], [6, 130], [143, 98], [1]], ![[92, 95, 57, 53], [185, 55], [80, 191], [32, 157], [19, 36], [191, 75], [182, 19, 114, 173]], ![[154, 38, 6, 66], [17, 62], [177, 179], [146, 62], [135, 85], [66, 165], [93, 154, 54, 20]]]
 h' := ![![[108, 41, 152], [25, 188, 136], [157, 175, 86], [81, 55, 42], [8, 132, 186], [47, 188, 138], [180, 189, 171], [0, 1]], ![[63, 151, 41], [125, 31, 90], [139, 47, 21], [54, 80, 34], [108, 81, 93], [111, 148, 6], [144, 93, 123], [108, 41, 152]], ![[0, 1], [116, 167, 160], [12, 164, 86], [169, 58, 117], [41, 173, 107], [161, 50, 49], [61, 104, 92], [63, 151, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 177], []]
 b := ![[], [91, 71, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [13, 4, 22, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14668, -4825, 9457]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-76, -25, 49]
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



lemma PB216I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB216I3 : PrimesBelowBoundCertificateInterval O 137 193 216 where
  m := 11
  g := ![1, 2, 1, 2, 2, 2, 1, 1, 3, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB216I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0]
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
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![181, 181, 181]
    · exact ![6967871]
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I157N1, I163N1, I167N1, I181N0, I181N1, I181N2]
  Il := ![[], [I149N1], [], [I157N1], [I163N1], [I167N1], [], [], [I181N0, I181N1, I181N2], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
