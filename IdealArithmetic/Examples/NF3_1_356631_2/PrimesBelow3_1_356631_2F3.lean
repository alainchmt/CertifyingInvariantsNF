
import IdealArithmetic.Examples.NF3_1_356631_2.RI3_1_356631_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-53, 67, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-53, 67, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![86, 67, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-53, 67, 1], ![189, -16, 201], ![12663, 2542, -16]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -67, 139]], ![![-1, 0, 1], ![-123, -97, 201], ![101, 26, -16]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [98, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 138], [0, 1]]
 g := ![![[40, 122], [44, 9], [38], [89, 24], [91], [89], [1]], ![[99, 17], [70, 130], [38], [112, 115], [91], [89], [1]]]
 h' := ![![[111, 138], [136, 119], [3, 3], [35, 49], [58, 118], [48, 77], [41, 111], [0, 1]], ![[0, 1], [1, 20], [58, 136], [53, 90], [90, 21], [116, 62], [130, 28], [111, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [78]]
 b := ![[], [129, 39]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [98, 28, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![476, 109, 12]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -5, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-62, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-62, 1, 0]] 
 ![![139, 0, 0], ![77, 1, 0], ![16, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-62, 1, 0], ![0, -62, 3], ![189, 37, -62]]]
  hmulB := by decide  
  f := ![![![6201, -100, 0], ![13900, 0, 0]], ![![3535, -57, 0], ![7924, 0, 0]], ![![712, 30, -2], ![1596, 93, 0]]]
  g := ![![![1, 0, 0], ![-77, 139, 0], ![-16, 0, 139]], ![![-1, 1, 0], ![34, -62, 3], ![-12, 37, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-53, 67, 1]] ![![139, 0, 0], ![-62, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-8618, 139, 0]], ![![-7367, 9313, 139], ![3475, -4170, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-62, 1, 0]]], ![![![-53, 67, 1]], ![![25, -30, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-95, 26, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-95, 26, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![54, 26, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-95, 26, 1], ![189, -58, 78], ![4914, 1025, -58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -26, 149]], ![![-1, 0, 1], ![-27, -14, 78], ![54, 17, -58]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [59, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 148], [0, 1]]
 g := ![![[122, 61], [81], [112, 107], [31], [31, 29], [30], [1]], ![[147, 88], [81], [107, 42], [31], [38, 120], [30], [1]]]
 h' := ![![[103, 148], [11, 106], [97, 9], [1, 133], [108, 110], [72, 25], [90, 103], [0, 1]], ![[0, 1], [52, 43], [130, 140], [141, 16], [114, 39], [114, 124], [120, 46], [103, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [74, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [59, 46, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2254, 35, 477]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-188, -83, 477]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![71, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![71, 1, 0]] 
 ![![149, 0, 0], ![71, 1, 0], ![58, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![71, 1, 0], ![0, 71, 3], ![189, 37, 71]]]
  hmulB := by decide  
  f := ![![![1208, 17, 0], ![-2533, 0, 0]], ![![568, 8, 0], ![-1191, 0, 0]], ![![414, -18, -1], ![-868, 50, 0]]]
  g := ![![![1, 0, 0], ![-71, 149, 0], ![-58, 0, 149]], ![![0, 1, 0], ![-35, 71, 3], ![-44, 37, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-95, 26, 1]] ![![149, 0, 0], ![71, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![10579, 149, 0]], ![![-14155, 3874, 149], ![-6556, 1788, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![71, 1, 0]]], ![![![-95, 26, 1]], ![![-44, 12, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-62, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-62, 1, 0]] 
 ![![151, 0, 0], ![89, 1, 0], ![128, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-62, 1, 0], ![0, -62, 3], ![189, 37, -62]]]
  hmulB := by decide  
  f := ![![![7503, -121, 0], ![18271, 0, 0]], ![![4465, -72, 0], ![10873, 0, 0]], ![![6416, -62, -2], ![15624, 101, 0]]]
  g := ![![![1, 0, 0], ![-89, 151, 0], ![-128, 0, 151]], ![![-1, 1, 0], ![34, -62, 3], ![32, 37, -62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 4, 1]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![13, 4, 1]] 
 ![![151, 0, 0], ![92, 1, 0], ![98, 0, 1]] where
  M :=![![![13, 4, 1], ![189, 50, 12], ![756, 211, 50]]]
  hmulB := by decide  
  f := ![![![-32, 11, -2]], ![![-22, 6, -1]], ![![-7, 9, -2]]]
  g := ![![![-3, 4, 1], ![-37, 50, 12], ![-156, 211, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-30, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-30, 1, 0]] 
 ![![151, 0, 0], ![121, 1, 0], ![2, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-30, 1, 0], ![0, -30, 3], ![189, 37, -30]]]
  hmulB := by decide  
  f := ![![![4441, -148, 0], ![22348, 0, 0]], ![![3571, -119, 0], ![17970, 0, 0]], ![![62, 18, -2], ![312, 101, 0]]]
  g := ![![![1, 0, 0], ![-121, 151, 0], ![-2, 0, 151]], ![![-1, 1, 0], ![24, -30, 3], ![-28, 37, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-62, 1, 0]] ![![13, 4, 1]]
  ![![151, 0, 0], ![-39, 10, 1]] where
 M := ![![![1963, 604, 151]], ![![-617, -198, -50]]]
 hmul := by decide  
 g := ![![![![13, 4, 1], ![0, 0, 0]]], ![![![22, -8, -1], ![101, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-39, 10, 1]] ![![151, 0, 0], ![-30, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-4530, 151, 0]], ![![-5889, 1510, 151], ![1359, -302, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-30, 1, 0]]], ![![![-39, 10, 1]], ![![9, -2, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-205, -55, -13]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-205, -55, -13]] 
 ![![157, 0, 0], ![0, 157, 0], ![52, 125, 1]] where
  M :=![![![-205, -55, -13], ![-2457, -686, -165], ![-10395, -2854, -686]]]
  hmulB := by decide  
  f := ![![![2, 4, -1]], ![![-189, -35, 12]], ![![-145, -26, 9]]]
  g := ![![![3, 10, -13], ![39, 127, -165], ![161, 528, -686]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [41, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 156], [0, 1]]
 g := ![![[77, 121], [52], [68, 111], [18, 71], [138, 143], [132], [1]], ![[61, 36], [52], [65, 46], [67, 86], [62, 14], [132], [1]]]
 h' := ![![[140, 156], [97, 11], [38, 113], [47, 116], [151, 68], [37, 92], [116, 140], [0, 1]], ![[0, 1], [67, 146], [1, 44], [116, 41], [94, 89], [43, 65], [91, 17], [140, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [133, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [41, 17, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2671, -122, 151]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, -121, 151]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, -4, 1]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-2, -4, 1]] 
 ![![157, 0, 0], ![96, 1, 0], ![68, 0, 1]] where
  M :=![![![-2, -4, 1], ![189, 35, -12], ![-756, -85, 35]]]
  hmulB := by decide  
  f := ![![![205, 55, 13]], ![![141, 38, 9]], ![![155, 42, 10]]]
  g := ![![![2, -4, 1], ![-15, 35, -12], ![32, -85, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-205, -55, -13]] ![![-2, -4, 1]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![63001, 17372, 4168]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![63001, 17372, 4168]] 
 ![![163, 0, 0], ![0, 163, 0], ![71, 157, 1]] where
  M :=![![![63001, 17372, 4168], ![787752, 217217, 52116], ![3283308, 905348, 217217]]]
  hmulB := by decide  
  f := ![![![667, -20, -8]], ![![-1512, 371, -60]], ![![-1189, 341, -59]]]
  g := ![![![-1429, -3908, 4168], ![-17868, -48865, 52116], ![-74473, -203667, 217217]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [141, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 162], [0, 1]]
 g := ![![[50, 64], [153, 15], [21], [146], [34], [17, 51], [1]], ![[34, 99], [27, 148], [21], [146], [34], [45, 112], [1]]]
 h' := ![![[122, 162], [106, 8], [88, 34], [21, 64], [118, 132], [48, 94], [22, 122], [0, 1]], ![[0, 1], [104, 155], [161, 129], [5, 99], [85, 31], [106, 69], [73, 41], [122, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [90, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [141, 41, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-951, 388, 207]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -197, 207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![667, -20, -8]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![667, -20, -8]] 
 ![![163, 0, 0], ![18, 1, 0], ![55, 0, 1]] where
  M :=![![![667, -20, -8], ![-1512, 371, -60], ![-3780, -1244, 371]]]
  hmulB := by decide  
  f := ![![![63001, 17372, 4168]], ![![11790, 3251, 780]], ![![41401, 11416, 2739]]]
  g := ![![![9, -20, -8], ![-30, 371, -60], ![-11, -1244, 371]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![63001, 17372, 4168]] ![![667, -20, -8]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [137, 23, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [116, 127, 50], [144, 39, 117], [0, 1]]
 g := ![![[15, 104, 162], [76, 145, 152], [22, 60, 1], [65, 107], [144, 144], [109, 93, 1], []], ![[163, 133, 46, 127], [69, 113, 138, 47], [133, 25, 56, 144], [87, 88], [152, 72], [69, 86, 133, 65], [44, 162]], ![[97, 129, 104, 90], [29, 148, 145, 103], [21, 128, 53, 83], [131, 44], [56, 14], [128, 134, 90, 160], [144, 162]]]
 h' := ![![[116, 127, 50], [109, 161, 50], [159, 129, 94], [2, 100, 166], [35, 132, 146], [97, 116, 12], [0, 0, 1], [0, 1]], ![[144, 39, 117], [73, 15, 147], [98, 95, 96], [166, 96, 118], [140, 75, 103], [151, 149, 89], [80, 79, 39], [116, 127, 50]], ![[0, 1], [46, 158, 137], [94, 110, 144], [34, 138, 50], [46, 127, 85], [6, 69, 66], [6, 88, 127], [144, 39, 117]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 11], []]
 b := ![[], [5, 140, 110], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [137, 23, 74, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5344, 668, 668]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, 4, 4]
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



lemma PB169I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 168 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 168 (by omega)

def PB169I3 : PrimesBelowBoundCertificateInterval O 137 168 169 where
  m := 6
  g := ![2, 2, 3, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB169I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
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
      exact NI151N1
      exact NI151N2
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
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
