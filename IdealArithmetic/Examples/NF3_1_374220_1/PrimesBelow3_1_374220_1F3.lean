
import IdealArithmetic.Examples.NF3_1_374220_1.RI3_1_374220_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [11, 0, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 133, 83], [85, 5, 56], [0, 1]]
 g := ![![[55, 102, 121], [63, 95, 5], [44, 67], [2, 5, 137], [47, 79], [36, 1], []], ![[133, 15, 49, 29], [28, 97, 89, 9], [79, 100], [109, 30, 4, 89], [83, 49], [7, 25], [5, 78]], ![[101, 64, 128, 22], [18, 123, 117, 110], [96, 5], [1, 105, 133, 40], [114, 63], [2, 36], [32, 78]]]
 h' := ![![[90, 133, 83], [2, 67, 128], [0, 102, 127], [117, 22, 22], [63, 59, 89], [21, 128, 45], [0, 0, 1], [0, 1]], ![[85, 5, 56], [103, 66, 85], [71, 126, 66], [55, 44, 129], [107, 80, 60], [73, 9, 7], [122, 8, 5], [90, 133, 83]], ![[0, 1], [11, 6, 65], [3, 50, 85], [15, 73, 127], [32, 0, 129], [69, 2, 87], [62, 131, 133], [85, 5, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93, 69], []]
 b := ![[], [1, 4, 103], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [11, 0, 103, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16541, 10842, -2363]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![119, 78, -17]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [88, 44, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 28, 21], [38, 120, 128], [0, 1]]
 g := ![![[0, 105, 86], [64, 114], [61, 8, 4], [116, 144], [1, 141, 54], [38, 1], []], ![[91, 87, 102, 115], [2, 88], [129, 58, 62, 2], [11, 61], [98, 135, 137, 2], [125, 96], [54, 143]], ![[10, 21, 127, 111], [73, 67], [148, 38, 52, 48], [49, 67], [74, 132, 1, 126], [74, 39], [96, 143]]]
 h' := ![![[0, 28, 21], [46, 8, 91], [145, 32, 73], [69, 113, 2], [61, 99, 137], [83, 28, 59], [0, 0, 1], [0, 1]], ![[38, 120, 128], [12, 128, 62], [121, 92, 45], [101, 64, 80], [18, 65, 43], [133, 75, 69], [16, 89, 120], [0, 28, 21]], ![[0, 1], [110, 13, 145], [96, 25, 31], [40, 121, 67], [110, 134, 118], [45, 46, 21], [148, 60, 28], [38, 120, 128]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127, 65], []]
 b := ![[], [122, 0, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [88, 44, 111, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![313198, 10430, -15645]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2102, 70, -105]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![65, -54, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![65, -54, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![65, 97, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![65, -54, 1], ![114, 47, -54], ![-6156, 1086, 47]]]
  hmulB := by decide  
  f := ![![![-64, 54, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -97, 151]], ![![0, -1, 1], ![24, 35, -54], ![-61, -23, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [34, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 150], [0, 1]]
 g := ![![[93, 40], [87, 91], [54, 145], [88], [80, 99], [81], [1]], ![[0, 111], [0, 60], [0, 6], [88], [65, 52], [81], [1]]]
 h' := ![![[9, 150], [62, 77], [127, 53], [32, 30], [149, 115], [63, 117], [117, 9], [0, 1]], ![[0, 1], [0, 74], [0, 98], [0, 121], [127, 36], [59, 34], [47, 142], [9, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [52, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [34, 142, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5186, 164, -31]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, 21, -31]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![54, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![54, 1, 0]] 
 ![![151, 0, 0], ![54, 1, 0], ![104, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![54, 1, 0], ![0, 54, 1], ![114, -18, 54]]]
  hmulB := by decide  
  f := ![![![649, 12, 0], ![-1812, 0, 0]], ![![162, 3, 0], ![-452, 0, 0]], ![![452, 8, 0], ![-1262, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 151, 0], ![-104, 0, 151]], ![![0, 1, 0], ![-20, 54, 1], ![-30, -18, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![65, -54, 1]] ![![151, 0, 0], ![54, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![8154, 151, 0]], ![![9815, -8154, 151], ![3624, -2869, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![54, 1, 0]]], ![![![65, -54, 1]], ![![24, -19, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [111, 97, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 126, 81], [110, 30, 76], [0, 1]]
 g := ![![[99, 81, 12], [90, 37], [88, 109, 64], [14, 135, 117], [152, 126, 13], [111, 1], []], ![[156, 78, 80, 81], [103, 25], [19, 153, 119, 19], [136, 146, 120, 126], [127, 32, 78, 57], [155, 115], [107, 124]], ![[40, 154, 38, 138], [100, 11], [119, 70, 62, 67], [152, 1, 30, 106], [61, 19, 40, 108], [121, 19], [112, 124]]]
 h' := ![![[1, 126, 81], [115, 127, 13], [123, 31, 115], [16, 133, 149], [84, 131, 66], [82, 112, 135], [0, 0, 1], [0, 1]], ![[110, 30, 76], [28, 108, 1], [0, 16, 152], [15, 18, 14], [143, 123, 31], [61, 105, 91], [56, 130, 30], [1, 126, 81]], ![[0, 1], [35, 79, 143], [50, 110, 47], [32, 6, 151], [118, 60, 60], [81, 97, 88], [139, 27, 126], [110, 30, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 136], []]
 b := ![[], [102, 143, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [111, 97, 46, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-439443, 174270, -13973]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2799, 1110, -89]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![42, 26, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![42, 26, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![42, 26, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![42, 26, 1], ![114, 24, 26], ![2964, -354, 24]]]
  hmulB := by decide  
  f := ![![![-41, -26, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -26, 163]], ![![0, 0, 1], ![-6, -4, 26], ![12, -6, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [62, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 162], [0, 1]]
 g := ![![[88, 71], [5, 113], [22], [115], [46], [124, 61], [1]], ![[0, 92], [106, 50], [22], [115], [46], [154, 102], [1]]]
 h' := ![![[86, 162], [16, 87], [44, 73], [58, 115], [159, 142], [136, 131], [101, 86], [0, 1]], ![[0, 1], [0, 76], [128, 90], [5, 48], [146, 21], [155, 32], [162, 77], [86, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [10, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [62, 77, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![290, 1, -94]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![26, 15, -94]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-26, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-26, 1, 0]] 
 ![![163, 0, 0], ![137, 1, 0], ![139, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-26, 1, 0], ![0, -26, 1], ![114, -18, -26]]]
  hmulB := by decide  
  f := ![![![2159, -83, 0], ![13529, 0, 0]], ![![1821, -70, 0], ![11411, 0, 0]], ![![1851, -71, 0], ![11599, 1, 0]]]
  g := ![![![1, 0, 0], ![-137, 163, 0], ![-139, 0, 163]], ![![-1, 1, 0], ![21, -26, 1], ![38, -18, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![42, 26, 1]] ![![163, 0, 0], ![-26, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4238, 163, 0]], ![![6846, 4238, 163], ![-978, -652, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-26, 1, 0]]], ![![![42, 26, 1]], ![![-6, -4, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [133, 88, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 62, 141], [123, 104, 26], [0, 1]]
 g := ![![[74, 78, 114], [15, 19, 81], [117, 122, 150], [4, 85], [58, 56], [166, 134, 1], []], ![[15, 31, 73, 99], [10, 108, 52, 47], [151, 79, 95, 130], [117, 14], [52, 126], [46, 33, 158, 12], [19, 8]], ![[91, 44, 129, 149], [72, 111, 11, 69], [138, 135, 14, 15], [128, 22], [9, 16], [117, 104, 75, 78], [134, 8]]]
 h' := ![![[11, 62, 141], [9, 59, 75], [137, 131, 9], [157, 9, 22], [122, 145, 69], [133, 135, 132], [0, 0, 1], [0, 1]], ![[123, 104, 26], [67, 123, 87], [131, 116, 35], [96, 100, 50], [31, 160, 66], [157, 111, 31], [99, 131, 104], [11, 62, 141]], ![[0, 1], [13, 152, 5], [29, 87, 123], [134, 58, 95], [142, 29, 32], [105, 88, 4], [146, 36, 62], [123, 104, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 115], []]
 b := ![[], [104, 9, 165], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [133, 88, 33, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![834165, -3173, -167]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4995, -19, -1]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![16, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![16, 1, 0]] 
 ![![173, 0, 0], ![16, 1, 0], ![90, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![16, 1, 0], ![0, 16, 1], ![114, -18, 16]]]
  hmulB := by decide  
  f := ![![![1649, 103, 0], ![-17819, 0, 0]], ![![144, 9, 0], ![-1556, 0, 0]], ![![866, 54, 0], ![-9358, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 173, 0], ![-90, 0, 173]], ![![0, 1, 0], ![-2, 16, 1], ![-6, -18, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![76, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![76, 1, 0]] 
 ![![173, 0, 0], ![76, 1, 0], ![106, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![76, 1, 0], ![0, 76, 1], ![114, -18, 76]]]
  hmulB := by decide  
  f := ![![![4333, 57, 0], ![-9861, 0, 0]], ![![1900, 25, 0], ![-4324, 0, 0]], ![![2618, 34, 0], ![-5958, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 173, 0], ![-106, 0, 173]], ![![0, 1, 0], ![-34, 76, 1], ![-38, -18, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![81, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![81, 1, 0]] 
 ![![173, 0, 0], ![81, 1, 0], ![13, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![81, 1, 0], ![0, 81, 1], ![114, -18, 81]]]
  hmulB := by decide  
  f := ![![![2998, 37, 0], ![-6401, 0, 0]], ![![1296, 16, 0], ![-2767, 0, 0]], ![![200, 2, 0], ![-427, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 173, 0], ![-13, 0, 173]], ![![0, 1, 0], ![-38, 81, 1], ![3, -18, 81]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![16, 1, 0]] ![![173, 0, 0], ![76, 1, 0]]
  ![![173, 0, 0], ![5, -81, 1]] where
 M := ![![![29929, 0, 0], ![13148, 173, 0]], ![![2768, 173, 0], ![1216, 92, 1]]]
 hmul := by decide  
 g := ![![![![168, 81, -1], ![173, 0, 0]], ![![71, 82, -1], ![173, 0, 0]]], ![![![16, 1, 0], ![0, 0, 0]], ![![7, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![5, -81, 1]] ![![173, 0, 0], ![81, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![14013, 173, 0]], ![![865, -14013, 173], ![519, -6574, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![81, 1, 0]]], ![![![5, -81, 1]], ![![3, -38, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)


lemma PB174I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 173 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 173 (by omega)

def PB174I3 : PrimesBelowBoundCertificateInterval O 137 173 174 where
  m := 7
  g := ![1, 1, 2, 1, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB174I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
  β := ![I151N1, I163N1, I173N0, I173N1, I173N2]
  Il := ![[], [], [I151N1], [], [I163N1], [], [I173N0, I173N1, I173N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
