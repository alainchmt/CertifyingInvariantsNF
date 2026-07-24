
import IdealArithmetic.Examples.NF3_1_463091_1.RI3_1_463091_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [88, 36, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 130, 88], [62, 8, 51], [0, 1]]
 g := ![![[124, 114, 46], [129, 99, 116], [1, 71], [130, 131, 131], [63, 89], [131, 1], []], ![[115, 86, 32, 110], [102, 128, 29, 101], [117, 13], [50, 74, 92, 8], [133, 51], [56, 64], [126, 99]], ![[34, 97, 41, 116], [28, 119, 28, 49], [18, 1], [29, 0, 123, 45], [89, 125], [130, 81], [24, 99]]]
 h' := ![![[69, 130, 88], [46, 52, 18], [8, 75, 106], [97, 12, 99], [97, 33, 100], [9, 61, 28], [0, 0, 1], [0, 1]], ![[62, 8, 51], [114, 32, 133], [53, 30, 81], [52, 1, 41], [39, 56, 90], [117, 28, 32], [67, 105, 8], [69, 130, 88]], ![[0, 1], [113, 55, 127], [44, 34, 91], [88, 126, 138], [64, 50, 88], [23, 50, 79], [64, 34, 130], [62, 8, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 136], []]
 b := ![[], [77, 43, 49], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [88, 36, 8, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16680, -417, -417]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-120, -3, -3]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [82, 57, 128, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 58, 33], [143, 90, 116], [0, 1]]
 g := ![![[56, 96, 104], [19, 96], [36, 44, 63], [66, 61], [119, 143, 95], [21, 1], []], ![[55, 97, 45, 42], [63, 69], [68, 118, 90, 118], [14, 132], [72, 32, 135, 42], [18, 54], [26, 46]], ![[1, 8, 19, 39], [51, 118], [89, 9, 135, 85], [79, 133], [50, 22, 68, 28], [22, 86], [92, 46]]]
 h' := ![![[27, 58, 33], [120, 120, 36], [28, 37, 120], [66, 33, 19], [76, 2, 106], [66, 62, 86], [0, 0, 1], [0, 1]], ![[143, 90, 116], [85, 2, 48], [143, 61, 101], [77, 38, 117], [114, 25, 70], [133, 53, 101], [87, 113, 90], [27, 58, 33]], ![[0, 1], [143, 27, 65], [147, 51, 77], [107, 78, 13], [25, 122, 122], [70, 34, 111], [91, 36, 58], [143, 90, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [139, 34], []]
 b := ![[], [58, 121, 8], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [82, 57, 128, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![237655, 173883, -2086]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1595, 1167, -14]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-72983996, -15893214, -2975665]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-72983996, -15893214, -2975665]] 
 ![![151, 0, 0], ![0, 151, 0], ![30, 100, 1]] where
  M :=![![![-72983996, -15893214, -2975665], ![-389812115, -84886656, -15893214], ![-2082011034, -453384971, -84886656]]]
  hmulB := by decide  
  f := ![![![10758, -1181, -156]], ![![-20436, 10134, -1181]], ![![-12421, 6310, -746]]]
  g := ![![![107854, 1865386, -2975665], ![576055, 9963144, -15893214], ![3076746, 53213779, -84886656]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [78, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 150], [0, 1]]
 g := ![![[111, 91], [6, 9], [120, 29], [34], [89, 55], [34], [1]], ![[0, 60], [0, 142], [0, 122], [34], [2, 96], [34], [1]]]
 h' := ![![[100, 150], [136, 53], [2, 3], [82, 123], [4, 100], [110, 31], [73, 100], [0, 1]], ![[0, 1], [0, 98], [0, 148], [0, 28], [38, 51], [39, 120], [107, 51], [100, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [130, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [78, 51, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![648, 46, 82]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -54, 82]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10758, 1181, 156]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-10758, 1181, 156]] 
 ![![151, 0, 0], ![51, 1, 0], ![117, 0, 1]] where
  M :=![![![-10758, 1181, 156], ![20436, -10134, 1181], ![154711, 25160, -10134]]]
  hmulB := by decide  
  f := ![![![72983996, 15893214, 2975665]], ![![27231761, 5930070, 1110279]], ![![70338666, 15317159, 2867811]]]
  g := ![![![-591, 1181, 156], ![2643, -10134, 1181], ![379, 25160, -10134]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-72983996, -15893214, -2975665]] ![![-10758, 1181, 156]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6075326881, -1322981414, -247700024]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-6075326881, -1322981414, -247700024]] 
 ![![157, 0, 0], ![0, 157, 0], ![104, 39, 1]] where
  M :=![![![-6075326881, -1322981414, -247700024], ![-32448703144, -7066126977, -1322981414], ![-173310565234, -37740628800, -7066126977]]]
  hmulB := by decide  
  f := ![![![-89397, -546, 3236]], ![![423916, -76453, -546]], ![![45630, -16667, 1521]]]
  g := ![![![125385195, 53103946, -247700024], ![669690216, 283631517, -1322981414], ![3576857582, 1514893779, -7066126977]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [135, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 156], [0, 1]]
 g := ![![[119, 13], [122], [83, 56], [92, 99], [141, 82], [89], [1]], ![[84, 144], [122], [53, 101], [67, 58], [41, 75], [89], [1]]]
 h' := ![![[106, 156], [82, 22], [99, 114], [140, 29], [119, 141], [87, 125], [22, 106], [0, 1]], ![[0, 1], [59, 135], [94, 43], [74, 128], [150, 16], [149, 32], [111, 51], [106, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [21, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [135, 51, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-599, 1208, -122]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![77, 38, -122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89397, 546, -3236]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![89397, 546, -3236]] 
 ![![157, 0, 0], ![118, 1, 0], ![49, 0, 1]] where
  M :=![![![89397, 546, -3236], ![-423916, 76453, 546], ![71526, -421732, 76453]]]
  hmulB := by decide  
  f := ![![![6075326881, 1322981414, 247700024]], ![![4772848886, 1039349897, 194596078]], ![![3000010079, 653291198, 122314829]]]
  g := ![![![1169, 546, -3236], ![-60332, 76453, 546], ![293565, -421732, 76453]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-6075326881, -1322981414, -247700024]] ![![89397, 546, -3236]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [142, 108, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 144, 1], [49, 18, 162], [0, 1]]
 g := ![![[137, 82, 57], [76, 90, 161], [90, 91], [147, 24], [39, 88], [119, 155, 1], []], ![[35, 144, 20, 10], [53, 157, 112, 81], [33, 91], [120, 74], [87, 69], [72, 121, 94, 161], [117, 1]], ![[66, 121, 37, 114], [137, 33, 130, 82], [83, 38], [22, 160], [133, 156], [110, 92, 89, 128], [119, 1]]]
 h' := ![![[106, 144, 1], [129, 63, 100], [137, 156, 18], [23, 120, 108], [149, 122, 137], [54, 20, 96], [0, 0, 1], [0, 1]], ![[49, 18, 162], [61, 37, 70], [65, 153, 154], [137, 122, 108], [15, 80, 143], [151, 107, 118], [1, 146, 18], [106, 144, 1]], ![[0, 1], [141, 63, 156], [137, 17, 154], [137, 84, 110], [162, 124, 46], [38, 36, 112], [10, 17, 144], [49, 18, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 31], []]
 b := ![[], [70, 106, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [142, 108, 8, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16626, -489, -489]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-102, -3, -3]
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


def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7293786866, 1588316917, 297378432]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![7293786866, 1588316917, 297378432]] 
 ![![167, 0, 0], ![27, 1, 0], ![106, 0, 1]] where
  M :=![![![7293786866, 1588316917, 297378432], ![38956574592, 8483300594, 1588316917], ![208069516127, 45309842260, 8483300594]]]
  hmulB := by decide  
  f := ![![![1240416, -212378, -3719]], ![![197629, -26998, -1873]], ![![620734, -142807, 4978]]]
  g := ![![![-401873555, 1588316917, 297378432], ![-2146431944, 8483300594, 1588316917], ![-11464228071, 45309842260, 8483300594]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![470360812, 102427182, 19177303]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![470360812, 102427182, 19177303]] 
 ![![167, 0, 0], ![70, 1, 0], ![110, 0, 1]] where
  M :=![![![470360812, 102427182, 19177303], ![2512226693, 547070024, 102427182], ![13417960842, 2921935421, 547070024]]]
  hmulB := by decide  
  f := ![![![346954, -42805, -4148]], ![![142176, -15964, -1995]], ![![194955, -32474, -754]]]
  g := ![![![-52748774, 102427182, 19177303], ![-281734521, 547070024, 102427182], ![-1504761804, 2921935421, 547070024]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![7293786866, 1588316917, 297378432]] ![![470360812, 102427182, 19177303]]
  ![![11411135824508920417, 2484923182598027492, 465248812609262660]] where
 M := ![![![11411135824508920417, 2484923182598027492, 465248812609262660]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![11411135824508920417, 2484923182598027492, 465248812609262660]] ![![470360812, 102427182, 19177303]]
  ![![167, 0, 0]] where
 M := ![![![17852731811013665281506502280, 3887664456206950533523354562, 727882167440870613832286735]]]
 hmul := by decide  
 g := ![![![![106902585694692606476086840, 23279427881478745709720686, 4358575852939344993007705]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-46654126834, -10159542671, -1902157458]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-46654126834, -10159542671, -1902157458]] 
 ![![173, 0, 0], ![0, 173, 0], ![88, 145, 1]] where
  M :=![![![-46654126834, -10159542671, -1902157458], ![-249182626998, -54262756666, -10159542671], ![-1330900089901, -289820797682, -54262756666]]]
  hmulB := by decide  
  f := ![![![54642, -50390, 7519]], ![![984989, 84718, -50390]], ![![815207, 49903, -37920]]]
  g := ![![![697894390, 1535568143, -1902157458], ![3727497850, 8201566073, -10159542671], ![19908800559, 43805080456, -54262756666]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [104, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 172], [0, 1]]
 g := ![![[172, 109], [78], [116, 151], [84, 116], [25], [11, 90], [1]], ![[90, 64], [78], [77, 22], [38, 57], [25], [29, 83], [1]]]
 h' := ![![[104, 172], [59, 52], [46, 123], [87, 155], [159, 156], [67, 5], [69, 104], [0, 1]], ![[0, 1], [104, 121], [36, 50], [118, 18], [121, 17], [68, 168], [159, 69], [104, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [109, 121]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [104, 69, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5152, 1632, 436]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-192, -356, 436]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54642, 50390, -7519]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-54642, 50390, -7519]] 
 ![![173, 0, 0], ![28, 1, 0], ![81, 0, 1]] where
  M :=![![![-54642, 50390, -7519], ![-984989, -84718, 50390], ![6601090, -783429, -84718]]]
  hmulB := by decide  
  f := ![![![46654126834, 10159542671, 1902157458]], ![![8991318950, 1957976598, 366589315]], ![![29536903835, 6432044821, 1204263068]]]
  g := ![![![-4951, 50390, -7519], ![-15575, -84718, 50390], ![204620, -783429, -84718]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-46654126834, -10159542671, -1902157458]] ![![-54642, 50390, -7519]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![4, 1, 0]] 
 ![![179, 0, 0], ![4, 1, 0], ![163, 0, 1]] where
  M :=![![![4, 1, 0], ![0, 4, 1], ![131, 4, 4]]]
  hmulB := by decide  
  f := ![![![12, -4, 1]], ![![1, 0, 0]], ![![8, -3, 1]]]
  g := ![![![0, 1, 0], ![-1, 4, 1], ![-3, 4, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![46885338, -4268974, -844271]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![46885338, -4268974, -844271]] 
 ![![179, 0, 0], ![21, 1, 0], ![96, 0, 1]] where
  M :=![![![46885338, -4268974, -844271], ![-110599501, 43508254, -4268974], ![-559235594, -127675397, 43508254]]]
  hmulB := by decide  
  f := ![![![-1347925215895838, -293528240211983, -54956896125510]], ![![-198356329196952, -43194669524299, -8087279658367]], ![![-937726369797599, -204202108456090, -38232485075122]]]
  g := ![![![1215552, -4268974, -844271], ![-3432689, 43508254, -4268974], ![-11479579, -127675397, 43508254]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4190960, 847529, -305594]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![4190960, 847529, -305594]] 
 ![![179, 0, 0], ![154, 1, 0], ![91, 0, 1]] where
  M :=![![![4190960, 847529, -305594], ![-40032814, 2968584, 847529], ![111026299, -36642698, 2968584]]]
  hmulB := by decide  
  f := ![![![39868240158298, 8681827623676, 1625486864737]], ![![35489652310941, 7728333193650, 1446965389906]], ![![26621951246406, 5797275997373, 1085416158147]]]
  g := ![![![-550388, 847529, -305594], ![-3208491, 2968584, 847529], ![30636093, -36642698, 2968584]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![4, 1, 0]] ![![46885338, -4268974, -844271]]
  ![![76941851, 26432358, -7646058]] where
 M := ![![![76941851, 26432358, -7646058]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![76941851, 26432358, -7646058]] ![![4190960, 847529, -305594]]
  ![![179, 0, 0]] where
 M := ![![![-1584614973207794, 423849319261735, -23808743512984]]]
 hmul := by decide  
 g := ![![![![-8852597615686, 2367873291965, -133009740296]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-73883056, -16088996, -3012321]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-73883056, -16088996, -3012321]] 
 ![![181, 0, 0], ![0, 181, 0], ![71, 165, 1]] where
  M :=![![![-73883056, -16088996, -3012321], ![-394614051, -85932340, -16088996], ![-2107658476, -458970035, -85932340]]]
  hmulB := by decide  
  f := ![![![-3540, -1495, 404]], ![![52924, -1924, -1495]], ![![45775, -2081, -1215]]]
  g := ![![![773435, 2657149, -3012321], ![4130965, 14192000, -16088996], ![22063744, 75800365, -85932340]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [167, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 180], [0, 1]]
 g := ![![[21, 168], [44], [94, 67], [87], [57, 102], [52, 99], [1]], ![[0, 13], [44], [63, 114], [87], [180, 79], [17, 82], [1]]]
 h' := ![![[113, 180], [121, 63], [49, 166], [178, 130], [74, 102], [4, 37], [14, 113], [0, 1]], ![[0, 1], [0, 118], [164, 15], [26, 51], [16, 79], [22, 144], [113, 68], [113, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [114, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [167, 68, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-686, 305, -53]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 50, -53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3540, -1495, 404]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-3540, -1495, 404]] 
 ![![181, 0, 0], ![16, 1, 0], ![106, 0, 1]] where
  M :=![![![-3540, -1495, 404], ![52924, -1924, -1495], ![-195845, 46944, -1924]]]
  hmulB := by decide  
  f := ![![![-73883056, -16088996, -3012321]], ![![-8711287, -1896996, -355172]], ![![-54913052, -11958031, -2238886]]]
  g := ![![![-124, -1495, 404], ![1338, -1924, -1495], ![-4105, 46944, -1924]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-73883056, -16088996, -3012321]] ![![-3540, -1495, 404]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![618668, 134723, 25224]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![618668, 134723, 25224]] 
 ![![191, 0, 0], ![0, 191, 0], ![113, 133, 1]] where
  M :=![![![618668, 134723, 25224], ![3304344, 719564, 134723], ![17648713, 3843236, 719564]]]
  hmulB := by decide  
  f := ![![![348, -188, 23]], ![![3013, 440, -188]], ![![2175, 207, -115]]]
  g := ![![![-11684, -16859, 25224], ![-62405, -90045, 134723], ![-333309, -480936, 719564]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [121, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 190], [0, 1]]
 g := ![![[25, 30], [154, 32], [30, 36], [41, 59], [22, 180], [133, 6], [1]], ![[0, 161], [0, 159], [0, 155], [151, 132], [63, 11], [128, 185], [1]]]
 h' := ![![[31, 190], [84, 139], [190, 37], [5, 6], [12, 21], [142, 84], [70, 31], [0, 1]], ![[0, 1], [0, 52], [0, 154], [0, 185], [90, 170], [72, 107], [76, 160], [31, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [129, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [121, 160, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![645, 700, 337]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-196, -231, 337]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![348, -188, 23]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![348, -188, 23]] 
 ![![191, 0, 0], ![58, 1, 0], ![74, 0, 1]] where
  M :=![![![348, -188, 23], ![3013, 440, -188], ![-24628, 2261, 440]]]
  hmulB := by decide  
  f := ![![![618668, 134723, 25224]], ![![205168, 44678, 8365]], ![![332095, 72318, 13540]]]
  g := ![![![50, -188, 23], ![-45, 440, -188], ![-986, 2261, 440]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![618668, 134723, 25224]] ![![348, -188, 23]]
  ![![191, 0, 0]] where
 M := ![![![191, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


lemma PB193I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 192 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 192 (by omega)

def PB193I3 : PrimesBelowBoundCertificateInterval O 137 192 193 where
  m := 10
  g := ![1, 1, 2, 2, 1, 3, 2, 3, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191]
  hP := PB193I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
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
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
  β := ![I151N1, I157N1, I167N0, I167N1, I173N1, I179N0, I179N1, I179N2, I181N1, I191N1]
  Il := ![[], [], [I151N1], [I157N1], [], [I167N0, I167N1, I167N1], [I173N1], [I179N0, I179N1, I179N2], [I181N1], [I191N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
