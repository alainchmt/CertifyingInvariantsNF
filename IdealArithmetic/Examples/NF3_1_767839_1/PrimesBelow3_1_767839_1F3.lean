
import IdealArithmetic.Examples.NF3_1_767839_1.RI3_1_767839_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [73, 110, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 69, 96], [73, 69, 43], [0, 1]]
 g := ![![[23, 104, 99], [109, 37, 54], [84, 80], [0, 126, 127], [61, 83], [62, 1], []], ![[12, 55, 28, 122], [47, 52, 43, 113], [71, 113], [47, 40, 105, 41], [44, 81], [47, 35], [6, 42]], ![[34, 104, 71, 48], [95, 84, 110, 88], [49, 30], [113, 15, 27, 115], [13, 89], [123, 35], [59, 42]]]
 h' := ![![[128, 69, 96], [105, 21, 88], [123, 71, 101], [0, 94, 48], [102, 23, 31], [61, 57, 120], [0, 0, 1], [0, 1]], ![[73, 69, 43], [56, 67, 26], [129, 119, 24], [13, 109, 104], [30, 124, 38], [36, 14, 130], [100, 38, 69], [128, 69, 96]], ![[0, 1], [112, 51, 25], [108, 88, 14], [40, 75, 126], [103, 131, 70], [94, 68, 28], [49, 101, 69], [73, 69, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 137], []]
 b := ![[], [8, 128, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [73, 110, 77, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14178, 13344, -3753]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102, 96, -27]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-73, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-73, 1, 0]] 
 ![![149, 0, 0], ![76, 1, 0], ![35, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-73, 1, 0], ![0, -73, 1], ![155, -31, -73]]]
  hmulB := by decide  
  f := ![![![5476, -75, 0], ![11175, 0, 0]], ![![2848, -39, 0], ![5812, 0, 0]], ![![1350, -18, 0], ![2755, 1, 0]]]
  g := ![![![1, 0, 0], ![-76, 149, 0], ![-35, 0, 149]], ![![-1, 1, 0], ![37, -73, 1], ![34, -31, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-54, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-54, 1, 0]] 
 ![![149, 0, 0], ![95, 1, 0], ![64, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-54, 1, 0], ![0, -54, 1], ![155, -31, -54]]]
  hmulB := by decide  
  f := ![![![5023, -93, 0], ![13857, 0, 0]], ![![3241, -60, 0], ![8941, 0, 0]], ![![2180, -40, 0], ![6014, 1, 0]]]
  g := ![![![1, 0, 0], ![-95, 149, 0], ![-64, 0, 149]], ![![-1, 1, 0], ![34, -54, 1], ![44, -31, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-22, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-22, 1, 0]] 
 ![![149, 0, 0], ![127, 1, 0], ![112, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-22, 1, 0], ![0, -22, 1], ![155, -31, -22]]]
  hmulB := by decide  
  f := ![![![1607, -73, 0], ![10877, 0, 0]], ![![1365, -62, 0], ![9239, 0, 0]], ![![1192, -54, 0], ![8068, 1, 0]]]
  g := ![![![1, 0, 0], ![-127, 149, 0], ![-112, 0, 149]], ![![-1, 1, 0], ![18, -22, 1], ![44, -31, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-73, 1, 0]] ![![149, 0, 0], ![-54, 1, 0]]
  ![![149, 0, 0], ![68, 22, 1]] where
 M := ![![![22201, 0, 0], ![-8046, 149, 0]], ![![-10877, 149, 0], ![3942, -127, 1]]]
 hmul := by decide  
 g := ![![![![81, -22, -1], ![149, 0, 0]], ![![-54, 1, 0], ![0, 0, 0]]], ![![![-73, 1, 0], ![0, 0, 0]], ![![-42, -23, -1], ![150, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![68, 22, 1]] ![![149, 0, 0], ![-22, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3278, 149, 0]], ![![10132, 3278, 149], ![-1341, -447, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-22, 1, 0]]], ![![![68, 22, 1]], ![![-9, -3, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-76, 96, -21]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-76, 96, -21]] 
 ![![151, 0, 0], ![0, 151, 0], ![18, 17, 1]] where
  M :=![![![-76, 96, -21], ![-3255, 575, 96], ![14880, -6231, 575]]]
  hmulB := by decide  
  f := ![![![-6151, -501, -141]], ![![-21855, -1780, -501]], ![![-3708, -302, -85]]]
  g := ![![![2, 3, -21], ![-33, -7, 96], ![30, -106, 575]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [106, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 150], [0, 1]]
 g := ![![[31, 95], [42, 36], [4, 74], [18], [66, 128], [88], [1]], ![[129, 56], [130, 115], [101, 77], [18], [144, 23], [88], [1]]]
 h' := ![![[36, 150], [78, 47], [29, 145], [139, 136], [101, 138], [96, 66], [45, 36], [0, 1]], ![[0, 1], [109, 104], [115, 6], [52, 15], [86, 13], [56, 85], [133, 115], [36, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [70, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [106, 115, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1868, 1541, 64]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, 3, 64]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6151, 501, 141]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![6151, 501, 141]] 
 ![![151, 0, 0], ![134, 1, 0], ![13, 0, 1]] where
  M :=![![![6151, 501, 141], ![21855, 1780, 501], ![77655, 6324, 1780]]]
  hmulB := by decide  
  f := ![![![76, -96, 21]], ![![89, -89, 18]], ![![-92, 33, -2]]]
  g := ![![![-416, 501, 141], ![-1478, 1780, 501], ![-5251, 6324, 1780]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-76, 96, -21]] ![![6151, 501, 141]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [86, 0, 130, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 81, 83], [35, 75, 74], [0, 1]]
 g := ![![[22, 4, 56], [14, 101], [135, 83, 99], [2, 14, 108], [71, 104, 153], [27, 1], []], ![[76, 123, 28, 123], [111, 3], [65, 33, 80, 54], [46, 93, 44, 18], [82, 93, 91, 21], [45, 130], [59, 138]], ![[115, 2, 147, 55], [118, 141], [69, 7, 7, 38], [66, 141, 59, 41], [149, 37, 2, 131], [88, 124], [68, 138]]]
 h' := ![![[149, 81, 83], [116, 26, 128], [8, 152, 130], [142, 27, 16], [17, 152, 39], [33, 71, 101], [0, 0, 1], [0, 1]], ![[35, 75, 74], [130, 154, 140], [141, 46, 72], [150, 59, 144], [132, 60, 155], [94, 11, 123], [14, 24, 75], [149, 81, 83]], ![[0, 1], [73, 134, 46], [153, 116, 112], [124, 71, 154], [95, 102, 120], [1, 75, 90], [87, 133, 81], [35, 75, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 92], []]
 b := ![[], [106, 8, 154], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [86, 0, 130, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![251357, -5809, 5809]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1601, -37, 37]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![219, -19, -12]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![219, -19, -12]] 
 ![![163, 0, 0], ![56, 1, 0], ![124, 0, 1]] where
  M :=![![![219, -19, -12], ![-1860, 591, -19], ![-2945, -1271, 591]]]
  hmulB := by decide  
  f := ![![![325132, 26481, 7453]], ![![118789, 9675, 2723]], ![![272521, 22196, 6247]]]
  g := ![![![17, -19, -12], ![-200, 591, -19], ![-31, -1271, 591]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-43, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-43, 1, 0]] 
 ![![163, 0, 0], ![120, 1, 0], ![107, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-43, 1, 0], ![0, -43, 1], ![155, -31, -43]]]
  hmulB := by decide  
  f := ![![![4774, -111, 0], ![18093, 0, 0]], ![![3570, -83, 0], ![13530, 0, 0]], ![![3194, -74, 0], ![12105, 1, 0]]]
  g := ![![![1, 0, 0], ![-120, 163, 0], ![-107, 0, 163]], ![![-1, 1, 0], ![31, -43, 1], ![52, -31, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-13, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-13, 1, 0]] 
 ![![163, 0, 0], ![150, 1, 0], ![157, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-13, 1, 0], ![0, -13, 1], ![155, -31, -13]]]
  hmulB := by decide  
  f := ![![![1847, -142, 0], ![23146, 0, 0]], ![![1704, -131, 0], ![21354, 0, 0]], ![![1783, -137, 0], ![22344, 1, 0]]]
  g := ![![![1, 0, 0], ![-150, 163, 0], ![-157, 0, 163]], ![![-1, 1, 0], ![11, -13, 1], ![42, -31, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![219, -19, -12]] ![![163, 0, 0], ![-43, 1, 0]]
  ![![163, 0, 0], ![37, 13, 1]] where
 M := ![![![35697, -3097, -1956], ![-11277, 1408, 497]]]
 hmul := by decide  
 g := ![![![![182, -32, -13], ![163, 0, 0]], ![![-71, 8, 3], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![37, 13, 1]] ![![163, 0, 0], ![-13, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-2119, 163, 0]], ![![6031, 2119, 163], ![-326, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-13, 1, 0]]], ![![![37, 13, 1]], ![![-2, -1, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![26, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![26, 1, 0]] 
 ![![167, 0, 0], ![26, 1, 0], ![159, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![26, 1, 0], ![0, 26, 1], ![155, -31, 26]]]
  hmulB := by decide  
  f := ![![![1067, 41, 0], ![-6847, 0, 0]], ![![130, 5, 0], ![-834, 0, 0]], ![![1019, 39, 0], ![-6539, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 167, 0], ![-159, 0, 167]], ![![0, 1, 0], ![-5, 26, 1], ![-19, -31, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![43, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![43, 1, 0]] 
 ![![167, 0, 0], ![43, 1, 0], ![155, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![43, 1, 0], ![0, 43, 1], ![155, -31, 43]]]
  hmulB := by decide  
  f := ![![![3054, 71, 0], ![-11857, 0, 0]], ![![774, 18, 0], ![-3005, 0, 0]], ![![2850, 66, 0], ![-11065, 1, 0]]]
  g := ![![![1, 0, 0], ![-43, 167, 0], ![-155, 0, 167]], ![![0, 1, 0], ![-12, 43, 1], ![-31, -31, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-69, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-69, 1, 0]] 
 ![![167, 0, 0], ![98, 1, 0], ![82, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-69, 1, 0], ![0, -69, 1], ![155, -31, -69]]]
  hmulB := by decide  
  f := ![![![4831, -70, 0], ![11690, 0, 0]], ![![2830, -41, 0], ![6848, 0, 0]], ![![2444, -35, 0], ![5914, 1, 0]]]
  g := ![![![1, 0, 0], ![-98, 167, 0], ![-82, 0, 167]], ![![-1, 1, 0], ![40, -69, 1], ![53, -31, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![26, 1, 0]] ![![167, 0, 0], ![43, 1, 0]]
  ![![167, 0, 0], ![-51, 69, 1]] where
 M := ![![![27889, 0, 0], ![7181, 167, 0]], ![![4342, 167, 0], ![1118, 69, 1]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![43, 1, 0], ![0, 0, 0]]], ![![![26, 1, 0], ![0, 0, 0]], ![![7, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-51, 69, 1]] ![![167, 0, 0], ![-69, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11523, 167, 0]], ![![-8517, 11523, 167], ![3674, -4843, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-69, 1, 0]]], ![![![-51, 69, 1]], ![![22, -29, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![45, -35, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![45, -35, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![45, 138, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![45, -35, 1], ![155, 14, -35], ![-5425, 1240, 14]]]
  hmulB := by decide  
  f := ![![![-44, 35, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -138, 173]], ![![0, -1, 1], ![10, 28, -35], ![-35, -4, 14]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [142, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 172], [0, 1]]
 g := ![![[109, 106], [132], [28, 38], [18, 85], [13], [10, 160], [1]], ![[0, 67], [132], [64, 135], [53, 88], [13], [25, 13], [1]]]
 h' := ![![[92, 172], [122, 25], [3, 85], [39, 62], [142, 137], [137, 94], [31, 92], [0, 1]], ![[0, 1], [0, 148], [38, 88], [34, 111], [117, 36], [135, 79], [18, 81], [92, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134]]
 b := ![[], [32, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [142, 81, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-706, 1664, -527]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![133, 430, -527]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![35, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![35, 1, 0]] 
 ![![173, 0, 0], ![35, 1, 0], ![159, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![35, 1, 0], ![0, 35, 1], ![155, -31, 35]]]
  hmulB := by decide  
  f := ![![![2486, 71, 0], ![-12283, 0, 0]], ![![490, 14, 0], ![-2421, 0, 0]], ![![2248, 64, 0], ![-11107, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 173, 0], ![-159, 0, 173]], ![![0, 1, 0], ![-8, 35, 1], ![-25, -31, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![45, -35, 1]] ![![173, 0, 0], ![35, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![6055, 173, 0]], ![![7785, -6055, 173], ![1730, -1211, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![35, 1, 0]]], ![![![45, -35, 1]], ![![10, -7, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![101, -41, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![101, -41, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![101, 138, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![101, -41, 1], ![155, 70, -41], ![-6355, 1426, 70]]]
  hmulB := by decide  
  f := ![![![-100, 41, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -138, 179]], ![![0, -1, 1], ![24, 32, -41], ![-75, -46, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [123, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 178], [0, 1]]
 g := ![![[24, 93], [106, 139], [22], [153], [101, 25], [149, 47], [1]], ![[74, 86], [46, 40], [22], [153], [49, 154], [130, 132], [1]]]
 h' := ![![[91, 178], [29, 123], [45, 153], [148, 102], [107, 137], [110, 174], [56, 91], [0, 1]], ![[0, 1], [124, 56], [6, 26], [122, 77], [44, 42], [13, 5], [103, 88], [91, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [108, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [123, 88, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![433, 5, -118]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![69, 91, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![41, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![41, 1, 0]] 
 ![![179, 0, 0], ![41, 1, 0], ![109, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![41, 1, 0], ![0, 41, 1], ![155, -31, 41]]]
  hmulB := by decide  
  f := ![![![3650, 89, 0], ![-15931, 0, 0]], ![![820, 20, 0], ![-3579, 0, 0]], ![![2224, 54, 0], ![-9707, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 179, 0], ![-109, 0, 179]], ![![0, 1, 0], ![-10, 41, 1], ![-17, -31, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![101, -41, 1]] ![![179, 0, 0], ![41, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![7339, 179, 0]], ![![18079, -7339, 179], ![4296, -1611, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![41, 1, 0]]], ![![![101, -41, 1]], ![![24, -9, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [28, 119, 59, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [168, 45, 126], [135, 135, 55], [0, 1]]
 g := ![![[175, 103, 87], [48, 126], [90, 26, 70], [75, 154], [62, 152, 132], [104, 122, 1], []], ![[41, 44, 122, 111], [23, 135], [172, 1, 33, 166], [160, 62], [26, 48, 66, 46], [14, 39, 138, 3], [109, 129]], ![[130, 175, 70, 169], [32, 156], [155, 144, 43, 79], [118, 34], [24, 27, 55, 144], [155, 25, 4, 60], [180, 129]]]
 h' := ![![[168, 45, 126], [119, 95, 79], [14, 133, 137], [118, 56, 147], [74, 25, 71], [165, 136, 133], [0, 0, 1], [0, 1]], ![[135, 135, 55], [92, 13, 10], [66, 129, 139], [34, 134, 113], [129, 60, 65], [126, 143, 158], [13, 166, 135], [168, 45, 126]], ![[0, 1], [53, 73, 92], [15, 100, 86], [123, 172, 102], [13, 96, 45], [140, 83, 71], [153, 15, 45], [135, 135, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 45], []]
 b := ![[], [51, 55, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [28, 119, 59, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1178672, -58463, -3077]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6512, -323, -17]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [168, 31, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 12, 98], [164, 178, 93], [0, 1]]
 g := ![![[120, 151, 147], [87, 89, 54], [103, 96, 100], [187, 33, 2], [157, 150, 12], [12, 59, 1], []], ![[48, 123, 27, 90], [166, 52, 112, 51], [32, 101, 182, 40], [55, 3, 145, 8], [144, 4, 61, 103], [51, 170, 0, 136], [190, 54]], ![[98, 96, 57, 94], [134, 54, 74, 190], [52, 138, 16, 83], [27, 66, 72, 123], [182, 81, 62, 28], [123, 175, 51, 22], [4, 54]]]
 h' := ![![[86, 12, 98], [91, 122, 23], [77, 30, 98], [99, 61, 181], [173, 78, 57], [85, 30, 48], [0, 0, 1], [0, 1]], ![[164, 178, 93], [49, 96, 6], [175, 12, 138], [184, 23, 187], [66, 145, 27], [163, 96, 24], [115, 90, 178], [86, 12, 98]], ![[0, 1], [18, 164, 162], [78, 149, 146], [174, 107, 14], [170, 159, 107], [101, 65, 119], [57, 101, 12], [164, 178, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165, 78], []]
 b := ![[], [93, 25, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [168, 31, 132, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-182787, 56536, -1337]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-957, 296, -7]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [146, 50, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [45, 86, 46], [24, 106, 147], [0, 1]]
 g := ![![[157, 62, 189], [22, 14], [178, 124], [173, 24], [1, 165], [71, 129], [1]], ![[144, 21, 147, 144], [8, 84], [19, 166], [134, 50], [160, 27], [43, 16], [163, 186, 101, 64]], ![[182, 121, 164, 112], [156, 172], [77, 170], [155, 55], [68, 184], [173, 172], [76, 65, 113, 129]]]
 h' := ![![[45, 86, 46], [2, 7, 162], [60, 15, 20], [46, 86, 160], [139, 144, 88], [142, 129, 101], [47, 143, 69], [0, 1]], ![[24, 106, 147], [40, 136, 124], [67, 84, 108], [116, 64, 72], [90, 91, 126], [26, 5, 42], [163, 12, 189], [45, 86, 46]], ![[0, 1], [127, 50, 100], [124, 94, 65], [128, 43, 154], [131, 151, 172], [122, 59, 50], [26, 38, 128], [24, 106, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [162, 79], []]
 b := ![[], [62, 17, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [146, 50, 124, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![211721, -2895, -5790]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1097, -15, -30]
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



lemma PB248I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB248I3 : PrimesBelowBoundCertificateInterval O 137 193 248 where
  m := 11
  g := ![1, 3, 2, 1, 3, 3, 2, 2, 1, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB248I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![163, 163, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
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
      exact NI149N2
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
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N0, I149N1, I149N2, I151N1, I163N0, I163N1, I163N2, I167N0, I167N1, I167N2, I173N1, I179N1]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N1], [], [I163N0, I163N1, I163N2], [I167N0, I167N1, I167N2], [I173N1], [I179N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
