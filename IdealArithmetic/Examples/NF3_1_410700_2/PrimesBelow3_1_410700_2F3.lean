
import IdealArithmetic.Examples.NF3_1_410700_2.RI3_1_410700_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [71, 58, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 19, 137], [3, 119, 2], [0, 1]]
 g := ![![[45, 54, 4], [76, 38, 100], [71, 113], [110, 14, 99], [81, 116], [5, 1], []], ![[100, 10, 31, 35], [138, 93, 38, 79], [48, 69], [68, 93, 64, 45], [63, 64], [79, 122], [83, 4]], ![[61, 92, 40, 73], [55, 116, 3, 85], [86, 125], [73, 103, 105, 134], [46, 13], [126, 83], [79, 4]]]
 h' := ![![[2, 19, 137], [25, 61, 137], [83, 37, 129], [113, 124, 35], [39, 126, 88], [62, 56, 106], [0, 0, 1], [0, 1]], ![[3, 119, 2], [110, 83, 57], [111, 49, 126], [105, 58, 25], [112, 115, 73], [50, 129, 131], [88, 121, 119], [2, 19, 137]], ![[0, 1], [10, 134, 84], [38, 53, 23], [58, 96, 79], [94, 37, 117], [21, 93, 41], [99, 18, 19], [3, 119, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 13], []]
 b := ![[], [74, 116, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [71, 58, 134, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2266673, -619662, -100636]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16307, -4458, -724]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-20, 19, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-20, 19, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![129, 19, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-20, 19, 1], ![201, 40, 57], ![3752, 846, 21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -19, 149]], ![![-1, 0, 1], ![-48, -7, 57], ![7, 3, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [32, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 148], [0, 1]]
 g := ![![[118, 4], [5], [59, 80], [22], [10, 45], [68], [1]], ![[63, 145], [5], [2, 69], [22], [99, 104], [68], [1]]]
 h' := ![![[98, 148], [6, 2], [49, 68], [78, 123], [127, 97], [40, 94], [117, 98], [0, 1]], ![[0, 1], [53, 147], [8, 81], [63, 26], [97, 52], [14, 55], [36, 51], [98, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [53, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [32, 51, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![317, 2135, 1273]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1100, -148, 1273]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-57, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-57, 1, 0]] 
 ![![149, 0, 0], ![92, 1, 0], ![128, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-57, 1, 0], ![0, -56, 3], ![201, 41, -57]]]
  hmulB := by decide  
  f := ![![![2281, -40, 0], ![5960, 0, 0]], ![![1426, -25, 0], ![3726, 0, 0]], ![![1870, -14, -1], ![4886, 50, 0]]]
  g := ![![![1, 0, 0], ![-92, 149, 0], ![-128, 0, 149]], ![![-1, 1, 0], ![32, -56, 3], ![25, 41, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-20, 19, 1]] ![![149, 0, 0], ![-57, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-8493, 149, 0]], ![![-2980, 2831, 149], ![1341, -1043, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-57, 1, 0]]], ![![![-20, 19, 1]], ![![9, -7, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [94, 70, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 43, 25], [99, 107, 126], [0, 1]]
 g := ![![[12, 61, 86], [84, 49, 21], [11, 116, 37], [57, 16], [59, 19, 20], [28, 1], []], ![[1, 29, 51, 145], [111, 46, 1, 76], [49, 78, 144, 18], [140, 98], [53, 45, 1, 97], [115, 124], [20, 21]], ![[105, 22, 117, 28], [23, 63, 51, 142], [40, 140, 96, 117], [35, 105], [42, 14, 145, 102], [10, 37], [70, 21]]]
 h' := ![![[80, 43, 25], [107, 9, 29], [23, 44, 126], [98, 49, 43], [41, 121, 4], [86, 60, 110], [0, 0, 1], [0, 1]], ![[99, 107, 126], [84, 136, 6], [18, 10, 86], [115, 53, 88], [17, 50, 131], [11, 19, 133], [141, 33, 107], [80, 43, 25]], ![[0, 1], [32, 6, 116], [109, 97, 90], [2, 49, 20], [140, 131, 16], [50, 72, 59], [50, 118, 43], [99, 107, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 32], []]
 b := ![[], [43, 33, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [94, 70, 123, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![231181, -10117, -1057]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1531, -67, -7]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [14, 155, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 51, 105], [122, 105, 52], [0, 1]]
 g := ![![[16, 76, 39], [17, 27], [135, 115, 101], [36, 87, 57], [27, 4, 52], [55, 1], []], ![[91, 106, 142, 140], [102, 89], [34, 80, 48, 81], [67, 32, 134, 68], [49, 132, 46, 127], [73, 35], [75, 35]], ![[11, 42, 101, 138], [108, 11], [33, 41, 97, 101], [97, 54, 103, 82], [24, 23, 133, 144], [156, 89], [128, 35]]]
 h' := ![![[90, 51, 105], [112, 156, 14], [151, 63, 98], [124, 124, 130], [93, 66, 34], [15, 96, 44], [0, 0, 1], [0, 1]], ![[122, 105, 52], [126, 150, 109], [112, 67, 106], [71, 4, 137], [28, 131, 138], [145, 100, 99], [142, 48, 105], [90, 51, 105]], ![[0, 1], [59, 8, 34], [156, 27, 110], [103, 29, 47], [14, 117, 142], [124, 118, 14], [61, 109, 51], [122, 105, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 26], []]
 b := ![[], [141, 127, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [14, 155, 102, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5858141, -1935025, -413381]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37313, -12325, -2633]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [156, 98, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 92, 106], [142, 70, 57], [0, 1]]
 g := ![![[14, 53, 160], [160, 18, 152], [69, 113], [127, 133], [23, 143], [126, 77, 1], []], ![[126, 91, 30, 72], [75, 0, 12, 116], [86, 136], [7, 156], [104, 34], [109, 44, 132, 82], [75, 152]], ![[7, 19, 81, 131], [109, 112, 15, 47], [98, 22], [53, 131], [12, 55], [9, 157, 48, 131], [124, 152]]]
 h' := ![![[98, 92, 106], [142, 159, 46], [126, 152, 57], [135, 10, 90], [86, 49, 123], [67, 90, 44], [0, 0, 1], [0, 1]], ![[142, 70, 57], [156, 92, 25], [33, 47, 53], [88, 27, 25], [56, 33, 112], [119, 81, 69], [23, 10, 70], [98, 92, 106]], ![[0, 1], [130, 75, 92], [153, 127, 53], [49, 126, 48], [161, 81, 91], [27, 155, 50], [5, 153, 92], [142, 70, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 117], []]
 b := ![[], [6, 47, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [156, 98, 86, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2379148, -739694, -150612]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-14596, -4538, -924]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![26, 9, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![26, 9, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![26, 9, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![26, 9, 1], ![201, 76, 27], ![1742, 436, 67]]]
  hmulB := by decide  
  f := ![![![-25, -9, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -9, 167]], ![![0, 0, 1], ![-3, -1, 27], ![0, -1, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [122, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 166], [0, 1]]
 g := ![![[17, 141], [166, 31], [129, 9], [8], [76], [64, 57], [1]], ![[0, 26], [0, 136], [0, 158], [8], [76], [82, 110], [1]]]
 h' := ![![[97, 166], [122, 59], [127, 71], [124, 164], [91, 26], [41, 110], [45, 97], [0, 1]], ![[0, 1], [0, 108], [0, 96], [0, 3], [108, 141], [23, 57], [102, 70], [97, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [166, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [122, 70, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![217206, 181707, 73073]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10076, -2850, 73073]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-27, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-27, 1, 0]] 
 ![![167, 0, 0], ![140, 1, 0], ![100, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-27, 1, 0], ![0, -26, 3], ![201, 41, -27]]]
  hmulB := by decide  
  f := ![![![2836, -105, 0], ![17535, 0, 0]], ![![2404, -89, 0], ![14864, 0, 0]], ![![1694, -54, -1], ![10474, 56, 0]]]
  g := ![![![1, 0, 0], ![-140, 167, 0], ![-100, 0, 167]], ![![-1, 1, 0], ![20, -26, 3], ![-17, 41, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![26, 9, 1]] ![![167, 0, 0], ![-27, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-4509, 167, 0]], ![![4342, 1503, 167], ![-501, -167, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-27, 1, 0]]], ![![![26, 9, 1]], ![![-3, -1, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-1, -67, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-1, -67, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![172, 106, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-1, -67, 1], ![201, -27, -201], ![-13534, -2680, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-172, -106, 173]], ![![-1, -1, 1], ![201, 123, -201], ![-118, -40, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [82, 164, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 172], [0, 1]]
 g := ![![[2, 47], [35], [35, 150], [88, 124], [164], [118, 81], [1]], ![[79, 126], [35], [1, 23], [166, 49], [164], [155, 92], [1]]]
 h' := ![![[9, 172], [95, 77], [71, 30], [50, 82], [17, 41], [12, 106], [91, 9], [0, 1]], ![[0, 1], [96, 96], [168, 143], [96, 91], [40, 132], [101, 67], [172, 164], [9, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [63, 159]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [82, 164, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1728, 1423, 867]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-852, -523, 867]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![28, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![28, 1, 0]] 
 ![![173, 0, 0], ![28, 1, 0], ![133, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![28, 1, 0], ![0, 29, 3], ![201, 41, 28]]]
  hmulB := by decide  
  f := ![![![1849, 66, 0], ![-11418, 0, 0]], ![![252, 9, 0], ![-1556, 0, 0]], ![![1393, 40, -1], ![-8602, 58, 0]]]
  g := ![![![1, 0, 0], ![-28, 173, 0], ![-133, 0, 173]], ![![0, 1, 0], ![-7, 29, 3], ![-27, 41, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-1, -67, 1]] ![![173, 0, 0], ![28, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![4844, 173, 0]], ![![-173, -11591, 173], ![173, -1903, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![28, 1, 0]]], ![![![-1, -67, 1]], ![![1, -11, -1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![10, -47, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![10, -47, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![10, 132, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![10, -47, 1], ![201, 4, -141], ![-9514, -1860, 51]]]
  hmulB := by decide  
  f := ![![![-9, 47, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -132, 179]], ![![0, -1, 1], ![9, 104, -141], ![-56, -48, 51]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [166, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 178], [0, 1]]
 g := ![![[162, 124], [], [93], [61], [96, 100], [0, 153], [1]], ![[145, 55], [], [93], [61], [13, 79], [18, 26], [1]]]
 h' := ![![[137, 178], [0, 126], [157], [102, 56], [174, 132], [0, 10], [13, 137], [0, 1]], ![[0, 1], [78, 53], [157], [77, 123], [0, 47], [117, 169], [166, 42], [137, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [81, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [166, 42, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5526, 6391, 2987]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-136, -2167, 2987]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-38, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-38, 1, 0]] 
 ![![179, 0, 0], ![141, 1, 0], ![128, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-38, 1, 0], ![0, -37, 3], ![201, 41, -38]]]
  hmulB := by decide  
  f := ![![![3155, -83, 0], ![14857, 0, 0]], ![![2509, -66, 0], ![11815, 0, 0]], ![![2220, -46, -1], ![10454, 60, 0]]]
  g := ![![![1, 0, 0], ![-141, 179, 0], ![-128, 0, 179]], ![![-1, 1, 0], ![27, -37, 3], ![-4, 41, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![10, -47, 1]] ![![179, 0, 0], ![-38, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-6802, 179, 0]], ![![1790, -8413, 179], ![-179, 1790, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-38, 1, 0]]], ![![![10, -47, 1]], ![![-1, 10, -1]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [106, 24, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [157, 114, 171], [141, 66, 10], [0, 1]]
 g := ![![[130, 48, 148], [44, 25], [107, 142, 4], [155, 102], [118, 2, 15], [90, 117, 1], []], ![[127, 139, 166, 85], [108, 37], [179, 105, 91, 98], [19, 156], [139, 22, 57, 61], [39, 30, 68, 61], [8, 100]], ![[76, 162, 108, 68], [159, 135], [20, 66, 51, 174], [159, 106], [20, 167, 148, 71], [101, 73, 118, 2], [169, 100]]]
 h' := ![![[157, 114, 171], [143, 93, 94], [61, 89, 176], [40, 9, 2], [162, 127, 37], [53, 99, 14], [0, 0, 1], [0, 1]], ![[141, 66, 10], [36, 14, 25], [9, 61, 47], [4, 173, 42], [82, 55, 86], [23, 66, 115], [90, 26, 66], [157, 114, 171]], ![[0, 1], [140, 74, 62], [60, 31, 139], [175, 180, 137], [167, 180, 58], [101, 16, 52], [157, 155, 114], [141, 66, 10]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 104], []]
 b := ![[], [71, 157, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [106, 24, 64, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-66257222, -22132680, -5134608]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-366062, -122280, -28368]
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



lemma PB182I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 181 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 181 (by omega)

def PB182I3 : PrimesBelowBoundCertificateInterval O 137 181 182 where
  m := 9
  g := ![1, 2, 1, 1, 1, 2, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB182I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
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
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
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
  β := ![I149N1, I167N1, I173N1, I179N1]
  Il := ![[], [I149N1], [], [], [], [I167N1], [I173N1], [I179N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
