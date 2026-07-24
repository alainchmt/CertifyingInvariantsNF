
import IdealArithmetic.Examples.NF3_1_428868_2.RI3_1_428868_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [49, 86, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 111, 46], [45, 27, 93], [0, 1]]
 g := ![![[57, 18, 106], [40, 62, 137], [47, 112], [9, 119, 127], [82, 113], [32, 1], []], ![[103, 93, 124, 81], [134, 30, 76, 34], [129, 9], [21, 75, 107, 129], [99, 113], [12, 34], [84, 31]], ![[81, 104, 71, 75], [102, 48, 100, 8], [41, 120], [49, 92, 97, 43], [], [59, 89], [37, 31]]]
 h' := ![![[126, 111, 46], [125, 61, 84], [80, 93, 50], [115, 92, 116], [5, 30, 108], [100, 118, 104], [0, 0, 1], [0, 1]], ![[45, 27, 93], [133, 16, 70], [13, 24, 68], [45, 96, 136], [69, 66, 126], [74, 55, 35], [84, 47, 27], [126, 111, 46]], ![[0, 1], [106, 62, 124], [131, 22, 21], [74, 90, 26], [65, 43, 44], [75, 105], [73, 92, 111], [45, 27, 93]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 78], []]
 b := ![[], [61, 48, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [49, 86, 107, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-54766, 73114, -50735]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-394, 526, -365]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [82, 50, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 3, 92], [111, 145, 57], [0, 1]]
 g := ![![[135, 105, 82], [44, 148], [144, 136, 143], [75, 53], [107, 31, 67], [67, 1], []], ![[116, 135, 132, 38], [24, 1], [121, 129, 67, 10], [65, 110], [106, 148, 64, 89], [69, 16], [99, 120]], ![[101, 53, 84, 44], [82, 88], [24, 5, 125, 106], [21, 148], [104, 40, 128, 48], [37, 9], [134, 120]]]
 h' := ![![[105, 3, 92], [145, 88, 126], [112, 91, 44], [99, 27, 21], [17, 68, 84], [19, 144, 118], [0, 0, 1], [0, 1]], ![[111, 145, 57], [38, 81, 142], [48, 53, 1], [60, 125, 16], [131, 82, 109], [118, 140, 111], [76, 144, 145], [105, 3, 92]], ![[0, 1], [114, 129, 30], [27, 5, 104], [97, 146, 112], [39, 148, 105], [10, 14, 69], [141, 5, 3], [111, 145, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 98], []]
 b := ![[], [115, 81, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [82, 50, 82, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![358643, -127693, 10430]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2407, -857, 70]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![44, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![44, 1, 0]] 
 ![![151, 0, 0], ![44, 1, 0], ![67, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![44, 1, 0], ![0, 45, 2], ![95, -29, 43]]]
  hmulB := by decide  
  f := ![![![4621, 105, 0], ![-15855, 0, 0]], ![![1276, 29, 0], ![-4378, 0, 0]], ![![2009, 23, -1], ![-6893, 76, 0]]]
  g := ![![![1, 0, 0], ![-44, 151, 0], ![-67, 0, 151]], ![![0, 1, 0], ![-14, 45, 2], ![-10, -29, 43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-23, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-23, 1, 0]] 
 ![![151, 0, 0], ![128, 1, 0], ![49, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-23, 1, 0], ![0, -22, 2], ![95, -29, -24]]]
  hmulB := by decide  
  f := ![![![1565, -68, 0], ![10268, 0, 0]], ![![1312, -57, 0], ![8608, 0, 0]], ![![531, -12, -1], ![3484, 76, 0]]]
  g := ![![![1, 0, 0], ![-128, 151, 0], ![-49, 0, 151]], ![![-1, 1, 0], ![18, -22, 2], ![33, -29, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-21, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-21, 1, 0]] 
 ![![151, 0, 0], ![130, 1, 0], ![92, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-21, 1, 0], ![0, -20, 2], ![95, -29, -22]]]
  hmulB := by decide  
  f := ![![![1051, -50, 0], ![7550, 0, 0]], ![![904, -43, 0], ![6494, 0, 0]], ![![674, -22, -1], ![4842, 76, 0]]]
  g := ![![![1, 0, 0], ![-130, 151, 0], ![-92, 0, 151]], ![![-1, 1, 0], ![16, -20, 2], ![39, -29, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![44, 1, 0]] ![![151, 0, 0], ![-23, 1, 0]]
  ![![151, 0, 0], ![-53, 11, 1]] where
 M := ![![![22801, 0, 0], ![-3473, 151, 0]], ![![6644, 151, 0], ![-1012, 22, 2]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![30, -10, -1], ![151, 0, 0]]], ![![![44, 1, 0], ![0, 0, 0]], ![![47, -11, -1], ![153, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-53, 11, 1]] ![![151, 0, 0], ![-21, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-3171, 151, 0]], ![![-8003, 1661, 151], ![1208, -302, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-21, 1, 0]]], ![![![-53, 11, 1]], ![![8, -2, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [94, 152, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [153, 132, 80], [26, 24, 77], [0, 1]]
 g := ![![[137, 82, 122], [65, 101], [44, 42, 145], [20, 32, 33], [47, 11, 10], [22, 1], []], ![[107, 83, 119, 83], [112, 140], [138, 142, 104, 107], [93, 134, 134, 116], [146, 150, 39, 102], [34, 105], [53, 120]], ![[138, 54, 29, 23], [142, 48], [112, 91, 122, 8], [126, 156, 27, 119], [120, 100, 145, 65], [49, 154], [56, 120]]]
 h' := ![![[153, 132, 80], [103, 12, 114], [103, 56, 27], [4, 88, 107], [135, 87, 70], [130, 16, 18], [0, 0, 1], [0, 1]], ![[26, 24, 77], [73, 25, 85], [32, 28, 104], [49, 40, 31], [79, 27, 5], [11, 81, 142], [58, 18, 24], [153, 132, 80]], ![[0, 1], [36, 120, 115], [143, 73, 26], [117, 29, 19], [104, 43, 82], [73, 60, 154], [122, 139, 132], [26, 24, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 96], []]
 b := ![[], [84, 9, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [94, 152, 135, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![278047, 0, 5809]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1771, 0, 37]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![54, 21, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![54, 21, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![54, 21, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![54, 21, 1], ![95, 46, 41], ![1900, -547, 5]]]
  hmulB := by decide  
  f := ![![![-53, -21, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -21, 163]], ![![0, 0, 1], ![-13, -5, 41], ![10, -4, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [126, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 162], [0, 1]]
 g := ![![[134, 22], [88, 85], [77], [41], [39], [147, 60], [1]], ![[0, 141], [0, 78], [77], [41], [39], [152, 103], [1]]]
 h' := ![![[68, 162], [159, 48], [84, 133], [150, 27], [153, 81], [60, 56], [37, 68], [0, 1]], ![[0, 1], [0, 115], [0, 30], [30, 136], [119, 82], [119, 107], [97, 95], [68, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [16, 105]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [126, 95, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-253, 780, -1197]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![395, 159, -1197]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-41, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-41, 1, 0]] 
 ![![163, 0, 0], ![122, 1, 0], ![158, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-41, 1, 0], ![0, -40, 2], ![95, -29, -42]]]
  hmulB := by decide  
  f := ![![![1149, -28, 0], ![4564, 0, 0]], ![![862, -21, 0], ![3424, 0, 0]], ![![1154, -8, -1], ![4584, 82, 0]]]
  g := ![![![1, 0, 0], ![-122, 163, 0], ![-158, 0, 163]], ![![-1, 1, 0], ![28, -40, 2], ![63, -29, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![54, 21, 1]] ![![163, 0, 0], ![-41, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-6683, 163, 0]], ![![8802, 3423, 163], ![-2119, -815, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-41, 1, 0]]], ![![![54, 21, 1]], ![![-13, -5, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-44, -67, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-44, -67, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![123, 100, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-44, -67, 1], ![95, -140, -135], ![-6460, 2005, -5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-123, -100, 167]], ![![-1, -1, 1], ![100, 80, -135], ![-35, 15, -5]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [142, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 166], [0, 1]]
 g := ![![[109, 63], [165, 1], [118, 6], [162], [76], [58, 137], [1]], ![[108, 104], [51, 166], [102, 161], [162], [76], [138, 30], [1]]]
 h' := ![![[53, 166], [117, 49], [111, 166], [129, 29], [33, 50], [114, 110], [25, 53], [0, 1]], ![[0, 1], [42, 118], [58, 1], [163, 138], [11, 117], [99, 57], [162, 114], [53, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [27, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [142, 114, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![427, -14, -598]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![443, 358, -598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-32, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-32, 1, 0]] 
 ![![167, 0, 0], ![135, 1, 0], ![5, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-32, 1, 0], ![0, -31, 2], ![95, -29, -33]]]
  hmulB := by decide  
  f := ![![![2337, -73, 0], ![12191, 0, 0]], ![![1921, -60, 0], ![10021, 0, 0]], ![![83, 13, -1], ![433, 84, 0]]]
  g := ![![![1, 0, 0], ![-135, 167, 0], ![-5, 0, 167]], ![![-1, 1, 0], ![25, -31, 2], ![25, -29, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-44, -67, 1]] ![![167, 0, 0], ![-32, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-5344, 167, 0]], ![![-7348, -11189, 167], ![1503, 2004, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-32, 1, 0]]], ![![![-44, -67, 1]], ![![9, 12, -1]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [100, 137, 156, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 0, 108], [90, 172, 65], [0, 1]]
 g := ![![[172, 51, 100], [15, 1], [145, 82, 77], [11, 108, 163], [158, 151], [152, 17, 1], []], ![[36, 70, 53, 48], [72, 117], [100, 54, 60, 76], [35, 15, 1, 17], [51, 95], [61, 127, 108, 108], [30, 73]], ![[139, 110, 133, 168], [75, 73], [77, 141, 59, 66], [130, 39, 14, 61], [124, 137], [29, 8], [73, 73]]]
 h' := ![![[100, 0, 108], [43, 30, 10], [32, 172, 1], [111, 149, 58], [0, 28, 110], [24, 139, 155], [0, 0, 1], [0, 1]], ![[90, 172, 65], [37, 80, 116], [12, 8, 64], [102, 118, 118], [9, 15, 146], [28, 29, 152], [80, 8, 172], [100, 0, 108]], ![[0, 1], [17, 63, 47], [50, 166, 108], [63, 79, 170], [41, 130, 90], [37, 5, 39], [108, 165], [90, 172, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 66], []]
 b := ![[], [39, 162, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [100, 137, 156, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13951239, -9631256, 6431967]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![80643, -55672, 37179]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![98, 6, 3]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![98, 6, 3]] 
 ![![179, 0, 0], ![9, 1, 0], ![134, 0, 1]] where
  M :=![![![98, 6, 3], ![285, 17, 9], ![285, 12, 8]]]
  hmulB := by decide  
  f := ![![![28, -12, 3]], ![![3, -1, 0]], ![![13, -6, 2]]]
  g := ![![![-2, 6, 3], ![-6, 17, 9], ![-5, 12, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![11, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![11, 1, 0]] 
 ![![179, 0, 0], ![11, 1, 0], ![113, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![11, 1, 0], ![0, 12, 2], ![95, -29, 10]]]
  hmulB := by decide  
  f := ![![![1233, 112, 0], ![-20048, 0, 0]], ![![55, 5, 0], ![-894, 0, 0]], ![![771, 64, -1], ![-12536, 90, 0]]]
  g := ![![![1, 0, 0], ![-11, 179, 0], ![-113, 0, 179]], ![![0, 1, 0], ![-2, 12, 2], ![-4, -29, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-20, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-20, 1, 0]] 
 ![![179, 0, 0], ![159, 1, 0], ![168, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-20, 1, 0], ![0, -19, 2], ![95, -29, -21]]]
  hmulB := by decide  
  f := ![![![461, -23, 0], ![4117, 0, 0]], ![![401, -20, 0], ![3581, 0, 0]], ![![432, -12, -1], ![3858, 90, 0]]]
  g := ![![![1, 0, 0], ![-159, 179, 0], ![-168, 0, 179]], ![![-1, 1, 0], ![15, -19, 2], ![46, -29, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![98, 6, 3]] ![![179, 0, 0], ![11, 1, 0]]
  ![![179, 0, 0], ![-40, -79, 1]] where
 M := ![![![17542, 1074, 537], ![1363, 83, 42]]]
 hmul := by decide  
 g := ![![![![98, 6, 3], ![0, 0, 0]], ![![17, 19, 0], ![42, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-40, -79, 1]] ![![179, 0, 0], ![-20, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-3580, 179, 0]], ![![-7160, -14141, 179], ![895, 1432, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-20, 1, 0]]], ![![![-40, -79, 1]], ![![5, 8, -1]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [44, 87, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 8, 153], [42, 172, 28], [0, 1]]
 g := ![![[27, 88, 148], [178, 106], [117, 177, 44], [102, 60], [58, 120, 144], [74, 121, 1], []], ![[145, 1, 2, 57], [180, 60], [84, 80, 33, 155], [168, 55], [23, 92, 108, 51], [113, 158, 120, 85], [115, 60]], ![[138, 153, 13, 118], [156, 176], [23, 69, 110, 112], [1, 178], [75, 168, 127, 28], [70, 122, 60, 163], [59, 60]]]
 h' := ![![[79, 8, 153], [16, 40, 94], [101, 134, 123], [180, 69, 166], [163, 176, 28], [2, 3, 12], [0, 0, 1], [0, 1]], ![[42, 172, 28], [160, 35, 25], [109, 158, 28], [43, 41, 13], [75, 33, 69], [112, 107, 170], [95, 22, 172], [79, 8, 153]], ![[0, 1], [51, 106, 62], [47, 70, 30], [173, 71, 2], [6, 153, 84], [99, 71, 180], [73, 159, 8], [42, 172, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84, 33], []]
 b := ![[], [38, 53, 124], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [44, 87, 60, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9231, -1086, -543]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51, -6, -3]
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



lemma PB186I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 185 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 185 (by omega)

def PB186I3 : PrimesBelowBoundCertificateInterval O 137 185 186 where
  m := 9
  g := ![1, 1, 3, 1, 2, 2, 1, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB186I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![5929741]
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
      exact NI151N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
  β := ![I151N0, I151N1, I151N2, I163N1, I167N1, I179N0, I179N1, I179N2]
  Il := ![[], [], [I151N0, I151N1, I151N2], [], [I163N1], [I167N1], [], [I179N0, I179N1, I179N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
