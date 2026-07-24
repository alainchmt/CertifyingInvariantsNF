
import IdealArithmetic.Examples.NF3_1_865755_1.RI3_1_865755_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-47, 26, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-47, 26, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![92, 26, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-47, 26, 1], ![331, 18, 129], ![7158, 1062, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -26, 139]], ![![-1, 0, 1], ![-83, -24, 129], ![74, 14, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [47, 28, 1] where
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
 g := ![![[42, 71], [12, 64], [100], [123, 106], [1], [89], [1]], ![[0, 68], [27, 75], [100], [74, 33], [1], [89], [1]]]
 h' := ![![[111, 138], [131, 99], [78, 8], [57, 10], [42, 55], [111, 1], [92, 111], [0, 1]], ![[0, 1], [0, 40], [132, 131], [55, 129], [31, 84], [83, 138], [42, 28], [111, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [125]]
 b := ![[], [41, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [47, 28, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3183, 1936, 855]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-543, -146, 855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![10, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![10, 1, 0]] 
 ![![139, 0, 0], ![10, 1, 0], ![34, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![10, 1, 0], ![2, 11, 5], ![279, 39, 9]]]
  hmulB := by decide  
  f := ![![![-2499, -13858, -6300], ![-278, 175140, 0]], ![![-180, -990, -450], ![1, 12510, 0]], ![![-614, -3390, -1541], ![-30, 42840, 0]]]
  g := ![![![1, 0, 0], ![-10, 139, 0], ![-34, 0, 139]], ![![0, 1, 0], ![-2, 11, 5], ![-3, 39, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-47, 26, 1]] ![![139, 0, 0], ![10, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![1390, 139, 0]], ![![-6533, 3614, 139], ![-139, 278, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![10, 1, 0]]], ![![![-47, 26, 1]], ![![-1, 2, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-47, 38, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-47, 38, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![102, 38, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-47, 38, 1], ![355, 30, 189], ![10506, 1530, -46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-102, -38, 149]], ![![-1, 0, 1], ![-127, -48, 189], ![102, 22, -46]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [58, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 148], [0, 1]]
 g := ![![[8, 5], [16], [129, 17], [33], [111, 31], [140], [1]], ![[72, 144], [16], [138, 132], [33], [31, 118], [140], [1]]]
 h' := ![![[132, 148], [96, 68], [117, 4], [90, 100], [118, 35], [12, 39], [91, 132], [0, 1]], ![[0, 1], [132, 81], [49, 145], [29, 49], [119, 114], [94, 110], [82, 17], [132, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [18, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [58, 17, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16056, 8112, 6942]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4860, -1716, 6942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-40, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-40, 1, 0]] 
 ![![149, 0, 0], ![109, 1, 0], ![46, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-40, 1, 0], ![2, -39, 5], ![279, 39, -41]]]
  hmulB := by decide  
  f := ![![![10113, -218996, 28080], ![-4172, -836784, 0]], ![![7417, -160192, 20540], ![-2979, -612092, 0]], ![![3142, -67610, 8669], ![-1214, -258336, 0]]]
  g := ![![![1, 0, 0], ![-109, 149, 0], ![-46, 0, 149]], ![![-1, 1, 0], ![27, -39, 5], ![-14, 39, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-47, 38, 1]] ![![149, 0, 0], ![-40, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-5960, 149, 0]], ![![-7003, 5662, 149], ![2235, -1490, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-40, 1, 0]]], ![![![-47, 38, 1]], ![![15, -10, 1]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![38, -20, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![38, -20, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![38, 131, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![38, -20, 1], ![239, 57, -101], ![-5676, -732, 97]]]
  hmulB := by decide  
  f := ![![![-37, 20, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -131, 151]], ![![0, -1, 1], ![27, 88, -101], ![-62, -89, 97]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [139, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 150], [0, 1]]
 g := ![![[51, 88], [24, 148], [144, 76], [121], [113, 34], [64], [1]], ![[0, 63], [0, 3], [148, 75], [121], [83, 117], [64], [1]]]
 h' := ![![[8, 150], [137, 115], [67, 86], [102, 128], [148, 140], [6, 100], [12, 8], [0, 1]], ![[0, 1], [0, 36], [0, 65], [69, 23], [60, 11], [51, 51], [76, 143], [8, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [54, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [139, 143, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3054801, 1516400, 691864]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-153881, -590184, 691864]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-50, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-50, 1, 0]] 
 ![![151, 0, 0], ![101, 1, 0], ![54, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-50, 1, 0], ![2, -49, 5], ![279, 39, -51]]]
  hmulB := by decide  
  f := ![![![-15, 1616, -165], ![151, 4983, 0]], ![![7, 1077, -110], ![152, 3322, 0]], ![![-10, 578, -59], ![40, 1782, 0]]]
  g := ![![![1, 0, 0], ![-101, 151, 0], ![-54, 0, 151]], ![![-1, 1, 0], ![31, -49, 5], ![-6, 39, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![38, -20, 1]] ![![151, 0, 0], ![-50, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-7550, 151, 0]], ![![5738, -3020, 151], ![-1661, 1057, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-50, 1, 0]]], ![![![38, -20, 1]], ![![-11, 7, -1]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [43, 34, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 91, 43], [46, 65, 114], [0, 1]]
 g := ![![[25, 25, 48], [47, 105], [98, 106, 58], [137, 34, 27], [67, 49, 1], [70, 1], []], ![[34, 132, 48, 15], [29, 141], [116, 142, 35, 32], [115, 103, 23, 18], [147, 24, 112, 135], [148, 143], [38, 122]], ![[8, 66, 48, 38], [71, 51], [131, 130, 20, 55], [110, 86, 75, 62], [45, 18, 82, 91], [111, 117], [124, 122]]]
 h' := ![![[24, 91, 43], [17, 114, 26], [25, 90, 133], [75, 45, 134], [102, 112, 59], [130, 89, 156], [0, 0, 1], [0, 1]], ![[46, 65, 114], [51, 112, 155], [102, 139, 112], [55, 154, 126], [28, 69, 16], [27, 64, 151], [41, 28, 65], [24, 91, 43]], ![[0, 1], [145, 88, 133], [23, 85, 69], [125, 115, 54], [142, 133, 82], [61, 4, 7], [81, 129, 91], [46, 65, 114]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16, 43], []]
 b := ![[], [148, 6, 156], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [43, 34, 87, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27399326, -8325553, -2651887]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-174518, -53029, -16891]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![38, -46, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![38, -46, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![38, 117, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![38, -46, 1], ![187, 31, -231], ![-12930, -1746, 123]]]
  hmulB := by decide  
  f := ![![![-37, 46, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -117, 163]], ![![0, -1, 1], ![55, 166, -231], ![-108, -99, 123]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [68, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 162], [0, 1]]
 g := ![![[121, 140], [84, 53], [21], [55], [143], [117, 53], [1]], ![[122, 23], [25, 110], [21], [55], [143], [58, 110], [1]]]
 h' := ![![[85, 162], [156, 38], [96, 78], [63, 99], [39, 50], [31, 44], [95, 85], [0, 1]], ![[0, 1], [126, 125], [43, 85], [2, 64], [51, 113], [22, 119], [148, 78], [85, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [112, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [68, 78, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3104, 1836, 605]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-122, -423, 605]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![68, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![68, 1, 0]] 
 ![![163, 0, 0], ![68, 1, 0], ![40, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![68, 1, 0], ![2, 69, 5], ![279, 39, 67]]]
  hmulB := by decide  
  f := ![![![493, 24009, 1740], ![489, -56724, 0]], ![![222, 10004, 725], ![164, -23635, 0]], ![![68, 5891, 427], ![247, -13920, 0]]]
  g := ![![![1, 0, 0], ![-68, 163, 0], ![-40, 0, 163]], ![![0, 1, 0], ![-30, 69, 5], ![-31, 39, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![38, -46, 1]] ![![163, 0, 0], ![68, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![11084, 163, 0]], ![![6194, -7498, 163], ![2771, -3097, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![68, 1, 0]]], ![![![38, -46, 1]], ![![17, -19, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-14, -6, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-14, -6, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![153, 161, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-14, -6, 1], ![267, 19, -31], ![-1770, -186, 31]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -161, 167]], ![![-1, -1, 1], ![30, 30, -31], ![-39, -31, 31]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [9, 16, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 166], [0, 1]]
 g := ![![[76, 130], [81, 99], [163, 24], [81], [62], [33, 89], [1]], ![[0, 37], [0, 68], [113, 143], [81], [62], [112, 78], [1]]]
 h' := ![![[151, 166], [106, 111], [36, 44], [14, 109], [143, 9], [37, 88], [158, 151], [0, 1]], ![[0, 1], [0, 56], [0, 123], [107, 58], [166, 158], [132, 79], [80, 16], [151, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [6, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [9, 16, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78270, 14721, 3976]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3174, -3745, 3976]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![31, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![31, 1, 0]] 
 ![![167, 0, 0], ![31, 1, 0], ![136, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![31, 1, 0], ![2, 32, 5], ![279, 39, 30]]]
  hmulB := by decide  
  f := ![![![-18438, -310369, -48500], ![-5177, 1619900, 0]], ![![-3445, -57595, -9000], ![-834, 300600, 0]], ![![-15028, -252756, -39497], ![-4148, 1319200, 0]]]
  g := ![![![1, 0, 0], ![-31, 167, 0], ![-136, 0, 167]], ![![0, 1, 0], ![-10, 32, 5], ![-30, 39, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-14, -6, 1]] ![![167, 0, 0], ![31, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![5177, 167, 0]], ![![-2338, -1002, 167], ![-167, -167, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![31, 1, 0]]], ![![![-14, -6, 1]], ![![-1, -1, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![48, 21, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![48, 21, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![48, 21, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![48, 21, 1], ![321, 108, 104], ![5763, 867, 66]]]
  hmulB := by decide  
  f := ![![![-47, -21, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-48, -21, 173]], ![![0, 0, 1], ![-27, -12, 104], ![15, -3, 66]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [74, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 172], [0, 1]]
 g := ![![[26, 67], [106], [45, 151], [9, 54], [52], [75, 95], [1]], ![[3, 106], [106], [161, 22], [86, 119], [52], [156, 78], [1]]]
 h' := ![![[152, 172], [60, 97], [130, 148], [26, 155], [154, 20], [159, 158], [99, 152], [0, 1]], ![[0, 1], [99, 76], [136, 25], [58, 18], [80, 153], [128, 15], [21, 21], [152, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [44, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [74, 21, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8588, 1822, 1825]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-556, -211, 1825]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![69, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![69, 1, 0]] 
 ![![173, 0, 0], ![69, 1, 0], ![107, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![69, 1, 0], ![2, 70, 5], ![279, 39, 68]]]
  hmulB := by decide  
  f := ![![![24763, 1093586, 78120], ![16262, -2702952, 0]], ![![9840, 436132, 31155], ![6575, -1077963, 0]], ![![15262, 676379, 48317], ![10193, -1671768, 0]]]
  g := ![![![1, 0, 0], ![-69, 173, 0], ![-107, 0, 173]], ![![0, 1, 0], ![-31, 70, 5], ![-56, 39, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![48, 21, 1]] ![![173, 0, 0], ![69, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![11937, 173, 0]], ![![8304, 3633, 173], ![3633, 1557, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![69, 1, 0]]], ![![![48, 21, 1]], ![![21, 9, 1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [105, 24, 103, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 138, 107], [86, 40, 72], [0, 1]]
 g := ![![[145, 105, 14], [174, 173, 88], [36, 46], [127, 46], [8, 138, 106], [24, 76, 1], []], ![[44, 144], [142, 106, 163, 146], [88, 147], [3, 126], [153, 16, 6, 139], [1, 16, 68, 76], [2, 172]], ![[156, 56, 93, 113], [61, 163, 94, 96], [139, 66], [65, 116], [76, 43, 84, 30], [66, 71, 49, 28], [37, 172]]]
 h' := ![![[169, 138, 107], [167, 102, 112], [151, 174, 25], [72, 175, 164], [55, 13, 15], [165, 36, 74], [0, 0, 1], [0, 1]], ![[86, 40, 72], [73, 101], [136, 111, 107], [151, 113, 46], [65, 55, 22], [78, 136, 10], [69, 75, 40], [169, 138, 107]], ![[0, 1], [137, 155, 67], [144, 73, 47], [47, 70, 148], [138, 111, 142], [124, 7, 95], [110, 104, 138], [86, 40, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 106], []]
 b := ![[], [27, 120, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [105, 24, 103, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![20335832, 5975199, 2066555]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![113608, 33381, 11545]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-76, 17, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-76, 17, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![105, 17, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-76, 17, 1], ![313, -20, 84], ![4647, 711, -54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -17, 181]], ![![-1, 0, 1], ![-47, -8, 84], ![57, 9, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [101, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 180], [0, 1]]
 g := ![![[147, 138], [176], [70, 79], [170], [73, 49], [161, 25], [1]], ![[0, 43], [176], [37, 102], [170], [9, 132], [36, 156], [1]]]
 h' := ![![[176, 180], [83, 89], [170, 30], [157, 160], [48, 52], [29, 174], [80, 176], [0, 1]], ![[0, 1], [0, 92], [20, 151], [81, 21], [150, 129], [64, 7], [105, 5], [176, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [160, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [101, 5, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![18451, 8750, 3975]
  a := ![-5, -5, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2204, -325, 3975]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-84, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-84, 1, 0]] 
 ![![181, 0, 0], ![97, 1, 0], ![54, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-84, 1, 0], ![2, -83, 5], ![279, 39, -85]]]
  hmulB := by decide  
  f := ![![![-2295, 130134, -7840], ![1810, 283808, 0]], ![![-1175, 69714, -4200], ![1087, 152040, 0]], ![![-642, 38824, -2339], ![632, 84672, 0]]]
  g := ![![![1, 0, 0], ![-97, 181, 0], ![-54, 0, 181]], ![![-1, 1, 0], ![43, -83, 5], ![6, 39, -85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-76, 17, 1]] ![![181, 0, 0], ![-84, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-15204, 181, 0]], ![![-13756, 3077, 181], ![6697, -1448, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-84, 1, 0]]], ![![![-76, 17, 1]], ![![37, -8, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [51, 46, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 88, 133], [27, 102, 58], [0, 1]]
 g := ![![[181, 93, 104], [187, 168, 90], [163, 94, 170], [5, 26, 25], [168, 164, 107], [104, 155, 1], []], ![[41, 163, 97, 170], [51, 14, 6, 8], [88, 102, 44, 51], [158, 1, 124, 162], [115, 183, 4, 46], [95, 49, 39, 128], [96, 117]], ![[180, 34, 16, 159], [160, 55, 80, 182], [148, 101, 140, 186], [170, 8, 165, 38], [27, 170, 21, 112], [85, 147, 148, 111], [171, 117]]]
 h' := ![![[128, 88, 133], [13, 88, 88], [91, 17, 89], [127, 128, 172], [27, 169, 5], [44, 108, 153], [0, 0, 1], [0, 1]], ![[27, 102, 58], [180, 28, 52], [175, 4, 70], [126, 159, 188], [25, 152, 67], [7, 91, 174], [28, 112, 102], [128, 88, 133]], ![[0, 1], [63, 75, 51], [164, 170, 32], [148, 95, 22], [156, 61, 119], [101, 183, 55], [30, 79, 88], [27, 102, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75, 124], []]
 b := ![[], [185, 65, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [51, 46, 36, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16399833, 5608524, 3805484]
  a := ![6, -6, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-85863, 29364, 19924]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [150, 118, 46, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [191, 138, 90], [149, 54, 103], [0, 1]]
 g := ![![[175, 91, 187], [38, 175], [143, 59], [66, 72], [173, 184], [177, 186], [1]], ![[179, 79, 127, 53], [6, 177], [173, 98], [126, 83], [9, 59], [67, 14], [117, 161, 161, 39]], ![[71, 44, 152, 183], [180, 69], [167, 21], [161, 63], [94, 162], [190, 97], [89, 126, 50, 154]]]
 h' := ![![[191, 138, 90], [108, 60, 103], [37, 51, 102], [8, 79, 161], [114, 15, 74], [3, 124, 143], [43, 75, 147], [0, 1]], ![[149, 54, 103], [140, 57, 154], [123, 184, 62], [37, 91, 171], [122, 159, 135], [11, 63, 161], [5, 177, 20], [191, 138, 90]], ![[0, 1], [79, 76, 129], [32, 151, 29], [68, 23, 54], [155, 19, 177], [72, 6, 82], [89, 134, 26], [149, 54, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 174], []]
 b := ![[], [133, 140, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [150, 118, 46, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![710855284, 178665890, 55117519]
  a := ![15, 13, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3683188, 925730, 285583]
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



lemma PB264I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB264I3 : PrimesBelowBoundCertificateInterval O 137 193 264 where
  m := 11
  g := ![2, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB264I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
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
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N1, I151N1, I163N1, I167N1, I173N1, I181N1]
  Il := ![[I139N1], [I149N1], [I151N1], [], [I163N1], [I167N1], [I173N1], [], [I181N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
