
import IdealArithmetic.Examples.NF3_1_542700_3.RI3_1_542700_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![22, 38, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![22, 38, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![22, 38, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![22, 38, 1], ![10, -8, 190], ![380, -1138, -8]]]
  hmulB := by decide  
  f := ![![![-21, -38, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -38, 139]], ![![0, 0, 1], ![-30, -52, 190], ![4, -6, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [28, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 138], [0, 1]]
 g := ![![[41, 5], [75, 107], [24], [34, 136], [24], [45], [1]], ![[0, 134], [115, 32], [24], [3, 3], [24], [45], [1]]]
 h' := ![![[103, 138], [124, 127], [47, 61], [21, 118], [29, 85], [80, 118], [111, 103], [0, 1]], ![[0, 1], [0, 12], [75, 78], [82, 21], [27, 54], [2, 21], [17, 36], [103, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [69, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [28, 36, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48, -94, -61]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 16, -61]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-51, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-51, 1, 0]] 
 ![![139, 0, 0], ![88, 1, 0], ![8, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-51, 1, 0], ![0, -51, 5], ![10, -30, -51]]]
  hmulB := by decide  
  f := ![![![2347, -46, 0], ![6394, 0, 0]], ![![1480, -29, 0], ![4032, 0, 0]], ![![218, 6, -1], ![594, 28, 0]]]
  g := ![![![1, 0, 0], ![-88, 139, 0], ![-8, 0, 139]], ![![-1, 1, 0], ![32, -51, 5], ![22, -30, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![22, 38, 1]] ![![139, 0, 0], ![-51, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-7089, 139, 0]], ![![3058, 5282, 139], ![-1112, -1946, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-51, 1, 0]]], ![![![22, 38, 1]], ![![-8, -14, 1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [17, 5, 34, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 64, 116], [56, 84, 33], [0, 1]]
 g := ![![[128, 75, 85], [51, 24], [132, 81, 29], [38, 76], [45, 32, 42], [115, 1], []], ![[11, 99, 74, 37], [30, 19], [68, 82, 136, 120], [65, 76], [144, 80], [79, 53], [23, 46]], ![[141, 55, 74, 133], [48, 49], [87, 95, 87, 36], [], [96, 29, 49, 45], [44, 73], [106, 46]]]
 h' := ![![[59, 64, 116], [108, 145, 95], [140, 71, 89], [52, 77, 124], [129, 2, 134], [131, 4, 108], [0, 0, 1], [0, 1]], ![[56, 84, 33], [41, 60, 66], [113, 94, 67], [57, 69, 127], [87, 133, 15], [29, 71], [110, 99, 84], [59, 64, 116]], ![[0, 1], [113, 93, 137], [66, 133, 142], [69, 3, 47], [48, 14], [46, 74, 41], [142, 50, 64], [56, 84, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 143], []]
 b := ![[], [18, 116, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [17, 5, 34, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![12665, -38442, 10430]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![85, -258, 70]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [10, 101, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 29, 135], [53, 121, 16], [0, 1]]
 g := ![![[94, 30, 69], [130, 32, 94], [16, 27, 11], [15, 91], [51, 7, 103], [19, 1], []], ![[129, 141, 51, 24], [35, 47, 86, 53], [92, 29, 137, 117], [103, 50], [98, 131, 75, 126], [55, 145], [10, 105]], ![[24, 89, 139, 36], [116, 100, 16, 100], [2, 102, 149, 2], [0, 59], [78, 93, 65, 31], [81, 86], [129, 105]]]
 h' := ![![[117, 29, 135], [59, 70, 89], [142, 127, 68], [79, 48, 39], [94, 75, 53], [112, 34, 109], [0, 0, 1], [0, 1]], ![[53, 121, 16], [6, 146, 136], [135, 99, 5], [69, 127, 25], [58, 30, 79], [55, 2, 112], [150, 45, 121], [117, 29, 135]], ![[0, 1], [40, 86, 77], [86, 76, 78], [105, 127, 87], [16, 46, 19], [26, 115, 81], [9, 106, 29], [53, 121, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 106], []]
 b := ![[], [141, 95, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [10, 101, 132, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![272404, -5587, 5587]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1804, -37, 37]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [102, 68, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 104, 3], [98, 52, 154], [0, 1]]
 g := ![![[130, 75, 106], [21, 67], [153, 13, 9], [84, 83, 49], [35, 106, 86], [26, 1], []], ![[43, 112, 59, 120], [48, 93], [69, 20, 66, 127], [9, 3, 0, 25], [98, 100, 125, 145], [5, 35], [73, 9]], ![[31, 66, 138, 39], [117, 81], [148, 126, 155, 126], [51, 65, 72, 126], [136, 81, 152, 99], [112, 140], [79, 9]]]
 h' := ![![[85, 104, 3], [100, 98, 48], [94, 138, 99], [67, 63, 154], [41, 128, 7], [17, 14, 137], [0, 0, 1], [0, 1]], ![[98, 52, 154], [20, 149, 121], [150, 144, 67], [119, 46, 33], [111, 128, 120], [132, 54, 101], [93, 23, 52], [85, 104, 3]], ![[0, 1], [74, 67, 145], [95, 32, 148], [33, 48, 127], [14, 58, 30], [142, 89, 76], [133, 134, 104], [98, 52, 154]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 130], []]
 b := ![[], [71, 155, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [102, 68, 131, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16328, 54165, -59189]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-104, 345, -377]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [44, 42, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 27, 53], [104, 135, 110], [0, 1]]
 g := ![![[1, 21, 134], [23, 47, 1], [37, 97], [45, 6], [5, 36], [135, 60, 1], []], ![[40, 157, 106, 9], [112, 85, 14, 51], [86, 155], [91, 131], [92, 1], [107, 156, 25, 150], [89, 38]], ![[149, 123, 138, 128], [32, 83, 104, 98], [55, 140], [138, 58], [6, 25], [159, 12, 127, 157], [32, 38]]]
 h' := ![![[119, 27, 53], [129, 85, 42], [115, 88, 162], [73, 103, 74], [74, 56, 150], [91, 3, 157], [0, 0, 1], [0, 1]], ![[104, 135, 110], [108, 142, 69], [16, 56, 128], [122, 51, 127], [41, 40, 72], [103, 16, 1], [139, 38, 135], [119, 27, 53]], ![[0, 1], [28, 99, 52], [22, 19, 36], [46, 9, 125], [139, 67, 104], [27, 144, 5], [117, 125, 27], [104, 135, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 53], []]
 b := ![[], [10, 136, 162], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [44, 42, 103, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2934, -8476, -3097]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18, -52, -19]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [47, 88, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 135, 49], [50, 31, 118], [0, 1]]
 g := ![![[84, 39, 141], [3, 26, 76], [116, 1, 57], [123, 62], [69, 124], [155, 110, 1], []], ![[107, 106, 103, 124], [59, 26, 56, 50], [135, 127, 84, 28], [99, 157], [94, 12], [46, 114, 151, 162], [120, 63]], ![[107, 150, 73, 39], [14, 123, 63, 134], [125, 118, 160, 23], [81, 57], [8, 157], [4, 139, 96, 91], [51, 63]]]
 h' := ![![[60, 135, 49], [26, 158, 108], [59, 161, 110], [88, 108, 97], [58, 128, 88], [63, 61, 142], [0, 0, 1], [0, 1]], ![[50, 31, 118], [107, 42, 68], [81, 127, 110], [70, 62, 116], [61, 27, 149], [114, 44, 43], [131, 7, 31], [60, 135, 49]], ![[0, 1], [12, 134, 158], [67, 46, 114], [115, 164, 121], [158, 12, 97], [37, 62, 149], [103, 160, 135], [50, 31, 118]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159, 12], []]
 b := ![[], [87, 14, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [47, 88, 57, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![348863, -1031225, -54275]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2089, -6175, -325]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [51, 147, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 56, 121], [52, 116, 52], [0, 1]]
 g := ![![[44, 28, 35], [103, 23], [121, 11, 4], [155, 116, 13], [158, 84], [161, 57, 1], []], ![[163, 129, 136, 160], [106, 144], [39, 169, 29, 95], [145, 10, 172, 167], [96, 67], [25, 72, 140, 73], [43, 109]], ![[55, 172, 131, 106], [42, 157], [102, 47, 116, 54], [83, 46, 63, 47], [18, 34], [131, 76, 92, 106], [112, 109]]]
 h' := ![![[5, 56, 121], [72, 22, 30], [57, 31, 14], [53, 11, 171], [72, 16, 94], [93, 68, 55], [0, 0, 1], [0, 1]], ![[52, 116, 52], [17, 20, 87], [135, 167, 12], [119, 74, 61], [154, 74, 38], [44, 29, 76], [81, 98, 116], [5, 56, 121]], ![[0, 1], [71, 131, 56], [39, 148, 147], [67, 88, 114], [142, 83, 41], [117, 76, 42], [106, 75, 56], [52, 116, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 47], []]
 b := ![[], [43, 38, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [51, 147, 116, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8131, 24220, 5017]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-47, 140, 29]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-5, -72, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-5, -72, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![174, 107, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-5, -72, 1], ![10, -35, -360], ![-720, 2162, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-174, -107, 179]], ![![-1, -1, 1], ![350, 215, -360], ![30, 33, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [55, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 178], [0, 1]]
 g := ![![[92, 110], [85, 82], [20], [77], [161, 100], [119, 156], [1]], ![[3, 69], [87, 97], [20], [77], [15, 79], [149, 23], [1]]]
 h' := ![![[131, 178], [158, 17], [33, 145], [136, 60], [95, 16], [78, 10], [124, 131], [0, 1]], ![[0, 1], [58, 162], [54, 34], [120, 119], [43, 163], [135, 169], [101, 48], [131, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [135, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [55, 48, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95, -64, -19]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19, 11, -19]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![2, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![2, 1, 0]] 
 ![![179, 0, 0], ![2, 1, 0], ![35, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![2, 1, 0], ![0, 2, 5], ![10, -30, 2]]]
  hmulB := by decide  
  f := ![![![177, 88, 0], ![-15752, 0, 0]], ![![-2, -1, 0], ![180, 0, 0]], ![![33, 16, -1], ![-2936, 36, 0]]]
  g := ![![![1, 0, 0], ![-2, 179, 0], ![-35, 0, 179]], ![![0, 1, 0], ![-1, 2, 5], ![0, -30, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-5, -72, 1]] ![![179, 0, 0], ![2, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![358, 179, 0]], ![![-895, -12888, 179], ![0, -179, -358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![2, 1, 0]]], ![![![-5, -72, 1]], ![![0, -1, -2]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [20, 89, 114, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 22, 95], [34, 158, 86], [0, 1]]
 g := ![![[116, 145, 48], [105, 12], [53, 98, 165], [174, 148], [64, 68, 42], [56, 67, 1], []], ![[6, 60, 140, 173], [174, 45], [152, 179, 63, 58], [38, 37], [138, 114, 73, 35], [108, 12, 150, 118], [152, 156]], ![[170, 44, 22, 104], [88, 70], [164, 104, 66, 69], [49, 37], [175, 13, 149, 93], [148, 129, 5, 175], [161, 156]]]
 h' := ![![[33, 22, 95], [24, 144, 132], [26, 114, 66], [128, 109, 105], [168, 73, 87], [147, 11, 122], [0, 0, 1], [0, 1]], ![[34, 158, 86], [101, 61, 146], [93, 140, 81], [142, 161, 157], [84, 130, 47], [141, 132, 49], [40, 8, 158], [33, 22, 95]], ![[0, 1], [171, 157, 84], [170, 108, 34], [151, 92, 100], [100, 159, 47], [122, 38, 10], [108, 173, 22], [34, 158, 86]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 100], []]
 b := ![[], [158, 49, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [20, 89, 114, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-61178, 186430, -37286]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-338, 1030, -206]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![33, 29, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![33, 29, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![33, 29, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![33, 29, 1], ![10, 3, 145], ![290, -868, 3]]]
  hmulB := by decide  
  f := ![![![-32, -29, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -29, 191]], ![![0, 0, 1], ![-25, -22, 145], ![1, -5, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [16, 83, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [108, 190], [0, 1]]
 g := ![![[41, 12], [133, 12], [165, 150], [94, 36], [165, 64], [49, 13], [1]], ![[0, 179], [92, 179], [130, 41], [162, 155], [10, 127], [116, 178], [1]]]
 h' := ![![[108, 190], [164, 48], [34, 143], [24, 36], [34, 6], [171, 183], [175, 108], [0, 1]], ![[0, 1], [0, 143], [7, 48], [92, 155], [109, 185], [71, 8], [188, 83], [108, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [99, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [16, 83, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1244, -47, 84]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8, -13, 84]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![46, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![46, 1, 0]] 
 ![![191, 0, 0], ![46, 1, 0], ![188, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![46, 1, 0], ![0, 46, 5], ![10, -30, 46]]]
  hmulB := by decide  
  f := ![![![2117, 46, 0], ![-8786, 0, 0]], ![![506, 11, 0], ![-2100, 0, 0]], ![![2064, 8, -4], ![-8566, 153, 0]]]
  g := ![![![1, 0, 0], ![-46, 191, 0], ![-188, 0, 191]], ![![0, 1, 0], ![-16, 46, 5], ![-38, -30, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![33, 29, 1]] ![![191, 0, 0], ![46, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![8786, 191, 0]], ![![6303, 5539, 191], ![1528, 1337, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![46, 1, 0]]], ![![![33, 29, 1]], ![![8, 7, 1]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [21, 22, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [69, 103, 183], [187, 89, 10], [0, 1]]
 g := ![![[107, 99, 128], [13, 179], [39, 48], [10, 96], [8, 63], [42, 109], [1]], ![[115, 29, 76, 174], [158, 170], [32, 24], [128, 179], [48, 16], [110, 18], [63, 181, 131, 158]], ![[81, 120, 187, 37], [143, 101], [47, 59], [148, 157], [55, 144], [11, 157], [3, 46, 148, 35]]]
 h' := ![![[69, 103, 183], [167, 181, 163], [132, 190, 76], [76, 44, 56], [155, 163, 17], [138, 27, 16], [172, 171, 63], [0, 1]], ![[187, 89, 10], [181, 14, 152], [5, 127, 39], [22, 140, 105], [104, 126, 76], [98, 120, 189], [51, 127, 37], [69, 103, 183]], ![[0, 1], [149, 191, 71], [185, 69, 78], [173, 9, 32], [0, 97, 100], [24, 46, 181], [107, 88, 93], [187, 89, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 55], []]
 b := ![[], [192, 186, 102], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [21, 22, 130, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11194, -34354, 12545]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58, -178, 65]
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



lemma PB209I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB209I3 : PrimesBelowBoundCertificateInterval O 137 193 209 where
  m := 11
  g := ![2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB209I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
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
      exact NI139N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I179N1, I191N1]
  Il := ![[I139N1], [], [], [], [], [], [], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
