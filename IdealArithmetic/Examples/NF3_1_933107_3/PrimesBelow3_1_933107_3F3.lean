
import IdealArithmetic.Examples.NF3_1_933107_3.RI3_1_933107_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, -4, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![3, -4, 0]] 
 ![![139, 0, 0], ![34, 1, 0], ![138, 0, 1]] where
  M :=![![![3, -4, 0], ![-8, 7, -32], ![-92, 124, -1]]]
  hmulB := by decide  
  f := ![![![3961, -4, 128]], ![![990, -1, 32]], ![![3930, -4, 127]]]
  g := ![![![1, -4, 0], ![30, 7, -32], ![-30, 124, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-63, 0, -2]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-63, 0, -2]] 
 ![![139, 0, 0], ![122, 1, 0], ![101, 0, 1]] where
  M :=![![![-63, 0, -2], ![-46, -1, -2], ![4, 2, -1]]]
  hmulB := by decide  
  f := ![![![-5, 4, 2]], ![![-4, 3, 2]], ![![-3, 2, 1]]]
  g := ![![![1, 0, -2], ![2, -1, -2], ![-1, 2, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![3, -4, 0]] ![![-63, 0, -2]]
  ![![-5, 4, 2]] where
 M := ![![![-5, 4, 2]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-5, 4, 2]] ![![-63, 0, -2]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N1
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [17, 12, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 63, 29], [71, 85, 120], [0, 1]]
 g := ![![[145, 17, 114], [134, 119], [5, 128, 17], [138, 148], [0, 139, 145], [139, 1], []], ![[96, 12, 114, 67], [92, 46], [23, 58, 58, 80], [89, 9], [6, 127, 47, 67], [54, 73], [12, 96]], ![[90, 80, 26, 144], [126, 85], [130, 0, 125, 100], [54, 123], [124, 50, 74, 133], [8, 95], [70, 96]]]
 h' := ![![[68, 63, 29], [30, 38, 76], [64, 102, 62], [38, 0, 49], [0, 15, 44], [21, 103, 88], [0, 0, 1], [0, 1]], ![[71, 85, 120], [6, 66, 112], [26, 49, 33], [121, 91, 142], [12, 5, 3], [92, 139, 37], [99, 87, 85], [68, 63, 29]], ![[0, 1], [86, 45, 110], [69, 147, 54], [103, 58, 107], [53, 129, 102], [95, 56, 24], [126, 62, 63], [71, 85, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 84], []]
 b := ![[], [4, 72, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [17, 12, 10, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-375480, 307089, -1667608]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2520, 2061, -11192]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![6, -62, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![6, -62, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![6, 89, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![6, -62, 1], ![-101, 37, -495], ![-1428, 1921, -87]]]
  hmulB := by decide  
  f := ![![![-5, 62, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -89, 151]], ![![0, -1, 1], ![19, 292, -495], ![-6, 64, -87]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [122, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 150], [0, 1]]
 g := ![![[106, 127], [114, 21], [134, 69], [90], [84, 94], [47], [1]], ![[18, 24], [40, 130], [85, 82], [90], [26, 57], [47], [1]]]
 h' := ![![[54, 150], [135, 60], [111, 126], [141, 89], [20, 111], [90, 83], [29, 54], [0, 1]], ![[0, 1], [53, 91], [120, 25], [115, 62], [125, 40], [42, 68], [76, 97], [54, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [80, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [122, 97, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1692, 1931, -3906]
  a := ![3, -3, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![144, 2315, -3906]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![42, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![42, 1, 0]] 
 ![![151, 0, 0], ![42, 1, 0], ![87, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![42, 1, 0], ![2, 41, 8], ![23, -31, 43]]]
  hmulB := by decide  
  f := ![![![3853, 89286, 17424], ![1812, -328878, 0]], ![![1042, 24801, 4840], ![605, -91355, 0]], ![![2223, 51443, 10039], ![1033, -189486, 0]]]
  g := ![![![1, 0, 0], ![-42, 151, 0], ![-87, 0, 151]], ![![0, 1, 0], ![-16, 41, 8], ![-16, -31, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![6, -62, 1]] ![![151, 0, 0], ![42, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![6342, 151, 0]], ![![906, -9362, 151], ![151, -2567, -453]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![42, 1, 0]]], ![![![6, -62, 1]], ![![1, -17, -3]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [130, 0, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 139, 9], [67, 17, 148], [0, 1]]
 g := ![![[138, 18, 39], [74, 10], [154, 112, 10], [133, 108, 46], [138, 63, 9], [25, 1], []], ![[139, 143, 104, 126], [1, 35], [156, 155, 49, 46], [10, 79, 8, 118], [102, 82, 90, 35], [12, 132], [131, 81]], ![[33, 74, 60, 108], [142, 57], [53, 23, 100, 132], [115, 65, 116, 86], [85, 126, 141, 47], [121, 10], [149, 81]]]
 h' := ![![[115, 139, 9], [81, 106, 14], [76, 127, 139], [137, 127, 18], [115, 142, 108], [47, 27, 154], [0, 0, 1], [0, 1]], ![[67, 17, 148], [135, 109, 93], [118, 55, 52], [103, 83, 36], [46, 40, 131], [123, 35, 35], [120, 88, 17], [115, 139, 9]], ![[0, 1], [123, 99, 50], [123, 132, 123], [152, 104, 103], [113, 132, 75], [27, 95, 125], [34, 69, 139], [67, 17, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 141], []]
 b := ![[], [147, 112, 89], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [130, 0, 132, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-370339607, -354556711, -7141715224]
  a := ![-65, 1, -196]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2358851, -2258323, -45488632]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![1, 58, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![1, 58, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![1, 58, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![1, 58, 1], ![139, -88, 465], ![1332, -1799, 28]]]
  hmulB := by decide  
  f := ![![![0, 42, -5], ![-115, 2, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -58, 163]], ![![0, 0, 1], ![-2, -166, 465], ![8, -21, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [89, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 162], [0, 1]]
 g := ![![[70, 131], [17, 26], [161], [58], [62], [13, 155], [1]], ![[81, 32], [59, 137], [161], [58], [62], [138, 8], [1]]]
 h' := ![![[127, 162], [117, 72], [8, 29], [51, 145], [117, 59], [147, 15], [74, 127], [0, 1]], ![[0, 1], [133, 91], [105, 134], [47, 18], [112, 104], [96, 148], [66, 36], [127, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [61, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [89, 36, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2945, 2948, -9465]
  a := ![-4, 3, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40, 3386, -9465]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![24, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![24, 1, 0]] 
 ![![163, 0, 0], ![24, 1, 0], ![135, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![24, 1, 0], ![2, 23, 8], ![23, -31, 25]]]
  hmulB := by decide  
  f := ![![![-1923, -22676, -7888], ![-326, 160718, 0]], ![![-290, -3335, -1160], ![1, 23635, 0]], ![![-1599, -18781, -6533], ![-227, 133110, 0]]]
  g := ![![![1, 0, 0], ![-24, 163, 0], ![-135, 0, 163]], ![![0, 1, 0], ![-10, 23, 8], ![-16, -31, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![1, 58, 1]] ![![163, 0, 0], ![24, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![3912, 163, 0]], ![![163, 9454, 163], ![163, 1304, 489]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![24, 1, 0]]], ![![![1, 58, 1]], ![![1, 8, 3]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [157, 106, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [70, 26, 29], [164, 140, 138], [0, 1]]
 g := ![![[7, 162, 150], [69, 88, 121], [57, 58, 14], [8, 137], [114, 9], [41, 67, 1], []], ![[42, 52, 41, 42], [17, 153, 134, 64], [43, 46, 92, 99], [122, 124], [117, 28], [79, 8, 89, 99], [73, 6]], ![[26, 76, 93, 91], [80, 31, 89, 60], [98, 135, 112, 146], [100, 116], [17, 66], [100, 11, 122, 102], [131, 6]]]
 h' := ![![[70, 26, 29], [22, 164, 145], [69, 53, 11], [165, 118, 101], [69, 60, 53], [76, 165, 164], [0, 0, 1], [0, 1]], ![[164, 140, 138], [33, 81, 6], [78, 46, 71], [70, 38, 27], [55, 137, 142], [80, 38, 23], [119, 137, 140], [70, 26, 29]], ![[0, 1], [71, 89, 16], [57, 68, 85], [98, 11, 39], [157, 137, 139], [133, 131, 147], [150, 30, 26], [164, 140, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 66], []]
 b := ![[], [15, 163, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [157, 106, 100, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-450232, 360553, -2065456]
  a := ![-3, 1, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2696, 2159, -12368]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [116, 145, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 131, 166], [62, 41, 7], [0, 1]]
 g := ![![[127, 33, 9], [24, 33], [104, 40, 1], [57, 171, 152], [124, 132], [42, 35, 1], []], ![[97, 66, 108, 63], [161, 121], [112, 10, 30, 70], [54, 135, 23, 129], [11, 92], [20, 165, 105, 170], [54, 49]], ![[166, 101, 114, 127], [54, 51], [77, 38, 20, 93], [112, 170, 162, 20], [54, 135], [109, 111, 140, 65], [40, 49]]]
 h' := ![![[146, 131, 166], [24, 126, 3], [46, 62, 129], [135, 89, 1], [67, 19, 124], [145, 57, 85], [0, 0, 1], [0, 1]], ![[62, 41, 7], [85, 68, 106], [58, 35, 11], [155, 67, 110], [24, 116, 107], [75, 116, 145], [1, 172, 41], [146, 131, 166]], ![[0, 1], [85, 152, 64], [162, 76, 33], [13, 17, 62], [113, 38, 115], [29, 0, 116], [69, 1, 131], [62, 41, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [167, 38], []]
 b := ![[], [160, 30, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [116, 145, 138, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![38083355, 18583141, 584433963]
  a := ![22, -1, 87]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![220135, 107417, 3378231]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [84, 128, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 177, 129], [165, 1, 50], [0, 1]]
 g := ![![[154, 84, 117], [7, 12, 146], [114, 125], [50, 4], [139, 3, 59], [136, 117, 1], []], ![[136, 163, 19, 82], [146, 86, 131, 151], [150, 13], [11, 43], [26, 6, 111, 138], [152, 143, 49, 129], [35, 173]], ![[135, 163, 139, 99], [8, 156, 41, 58], [45, 93], [176, 12], [88, 55, 28, 69], [134, 102, 146, 21], [114, 173]]]
 h' := ![![[131, 177, 129], [128, 21, 98], [80, 103, 44], [166, 43, 29], [138, 164, 2], [32, 151, 136], [0, 0, 1], [0, 1]], ![[165, 1, 50], [158, 14, 122], [88, 126, 85], [64, 84, 27], [123, 159, 36], [84, 57, 104], [80, 154, 1], [131, 177, 129]], ![[0, 1], [117, 144, 138], [124, 129, 50], [161, 52, 123], [25, 35, 141], [119, 150, 118], [107, 25, 177], [165, 1, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 77], []]
 b := ![[], [44, 111, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [84, 128, 62, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![895, -1074, -1074]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, -6, -6]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [101, 46, 139, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [67, 145, 2], [156, 35, 179], [0, 1]]
 g := ![![[166, 138, 148], [124, 106], [172, 150, 3], [88, 133], [37, 161, 165], [89, 42, 1], []], ![[67, 48, 71, 8], [168, 106], [127, 169, 11, 53], [91, 116], [34, 30, 23, 28], [40, 5, 33, 97], [24, 4]], ![[180, 144, 176, 30], [41, 62], [46, 75, 57, 149], [63, 11], [169, 58, 173, 179], [139, 138, 138, 123], [28, 4]]]
 h' := ![![[67, 145, 2], [162, 166, 94], [4, 81, 123], [95, 132, 33], [64, 57, 155], [61, 171, 76], [0, 0, 1], [0, 1]], ![[156, 35, 179], [140, 98, 2], [53, 168, 123], [159, 53, 152], [149, 42, 109], [128, 45, 106], [74, 3, 35], [67, 145, 2]], ![[0, 1], [157, 98, 85], [139, 113, 116], [116, 177, 177], [169, 82, 98], [127, 146, 180], [150, 178, 145], [156, 35, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 101], []]
 b := ![[], [162, 25, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [101, 46, 139, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1615787, -1483838, 5811548]
  a := ![5, -2, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8927, -8198, 32108]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![88, -39, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![88, -39, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![88, 152, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![88, -39, 1], ![-55, 96, -311], ![-899, 1208, 18]]]
  hmulB := by decide  
  f := ![![![-87, 39, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -152, 191]], ![![0, -1, 1], ![143, 248, -311], ![-13, -8, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [125, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 190], [0, 1]]
 g := ![![[128, 136], [171, 115], [185, 1], [38, 156], [58, 2], [76, 26], [1]], ![[0, 55], [74, 76], [38, 190], [26, 35], [146, 189], [74, 165], [1]]]
 h' := ![![[44, 190], [17, 30], [177, 45], [25, 190], [8, 27], [50, 57], [66, 44], [0, 1]], ![[0, 1], [0, 161], [56, 146], [172, 1], [50, 164], [75, 134], [92, 147], [44, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108]]
 b := ![[], [149, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [125, 147, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1035, -225, -9030]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4155, 7185, -9030]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-71, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-71, 1, 0]] 
 ![![191, 0, 0], ![120, 1, 0], ![173, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-71, 1, 0], ![2, -72, 8], ![23, -31, -70]]]
  hmulB := by decide  
  f := ![![![20417, -898496, 99840], ![-12224, -2383680, 0]], ![![12841, -564440, 62720], ![-7639, -1497440, 0]], ![![18494, -813821, 90431], ![-11069, -2159040, 0]]]
  g := ![![![1, 0, 0], ![-120, 191, 0], ![-173, 0, 191]], ![![-1, 1, 0], ![38, -72, 8], ![83, -31, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![88, -39, 1]] ![![191, 0, 0], ![-71, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-13561, 191, 0]], ![![16808, -7449, 191], ![-6303, 2865, -382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-71, 1, 0]]], ![![![88, -39, 1]], ![![-33, 15, -2]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [117, 16, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [134, 90, 126], [5, 102, 67], [0, 1]]
 g := ![![[17, 179, 23], [125, 55], [81, 145], [57, 139], [17, 150], [15, 21], [1]], ![[43, 170, 16, 81], [2, 56], [134, 64], [146, 144], [93, 92], [136, 9], [68, 78, 49, 124]], ![[14, 109, 94, 50], [101, 54], [141, 8], [145, 172], [122, 190], [179, 92], [23, 19, 187, 69]]]
 h' := ![![[134, 90, 126], [70, 43, 122], [42, 32, 172], [86, 2, 96], [0, 90, 116], [161, 82, 166], [76, 177, 139], [0, 1]], ![[5, 102, 67], [160, 87, 106], [89, 160, 153], [83, 152, 8], [48, 121, 12], [182, 78, 51], [123, 168, 3], [134, 90, 126]], ![[0, 1], [176, 63, 158], [42, 1, 61], [83, 39, 89], [185, 175, 65], [62, 33, 169], [136, 41, 51], [5, 102, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 189], []]
 b := ![[], [128, 58, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [117, 16, 54, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1213005, -2337616, -5868744]
  a := ![-4, -2, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6285, -12112, -30408]
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



lemma PB274I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB274I3 : PrimesBelowBoundCertificateInterval O 137 193 274 where
  m := 11
  g := ![3, 1, 2, 1, 2, 1, 1, 1, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB274I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
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
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
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
  β := ![I139N0, I139N1, I151N1, I163N1, I191N1]
  Il := ![[I139N0, I139N1, I139N1], [], [I151N1], [], [I163N1], [], [], [], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
