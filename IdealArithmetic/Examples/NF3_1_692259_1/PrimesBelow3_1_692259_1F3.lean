
import IdealArithmetic.Examples.NF3_1_692259_1.RI3_1_692259_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [61, 129, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 67, 27], [125, 71, 112], [0, 1]]
 g := ![![[62, 58, 28], [21, 4, 89], [91, 117], [87, 2, 54], [20, 63], [96, 1], []], ![[48, 53, 107, 94], [127, 128, 53, 56], [108, 89], [118, 43, 73, 76], [82, 120], [34, 37], [71, 34]], ![[60, 133, 82, 122], [80, 48, 2, 51], [137, 129], [68, 117, 90, 5], [137, 107], [65, 41], [125, 34]]]
 h' := ![![[110, 67, 27], [109, 73, 81], [78, 56, 28], [114, 5, 123], [77, 133, 38], [121, 65, 52], [0, 0, 1], [0, 1]], ![[125, 71, 112], [113, 116, 77], [119, 61, 25], [70, 101, 111], [98, 119, 34], [97, 42, 26], [124, 32, 71], [110, 67, 27]], ![[0, 1], [42, 89, 120], [60, 22, 86], [63, 33, 44], [29, 26, 67], [18, 32, 61], [77, 107, 67], [125, 71, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [122, 122], []]
 b := ![[], [108, 5, 83], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [61, 129, 43, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-102582, 57546, -17097]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-738, 414, -123]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [110, 129, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [134, 56, 53], [56, 92, 96], [0, 1]]
 g := ![![[34, 105, 100], [59, 39], [115, 143, 9], [104, 45], [33, 92, 119], [41, 1], []], ![[123, 47, 55, 61], [28, 1], [25, 116, 115, 37], [94, 26], [137, 100, 65, 47], [76, 120], [117, 127]], ![[14, 139, 80, 28], [27, 96], [23, 17, 35, 20], [25, 114], [68, 71, 46, 6], [113, 7], [74, 127]]]
 h' := ![![[134, 56, 53], [142, 88, 139], [15, 47, 28], [118, 137, 146], [95, 37, 55], [109, 114, 62], [0, 0, 1], [0, 1]], ![[56, 92, 96], [112, 54, 19], [19, 68, 1], [89, 71, 131], [44, 122, 18], [86, 68, 124], [20, 100, 92], [134, 56, 53]], ![[0, 1], [129, 7, 140], [62, 34, 120], [5, 90, 21], [64, 139, 76], [56, 116, 112], [62, 49, 56], [56, 92, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109, 84], []]
 b := ![[], [94, 120, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [110, 129, 108, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4566254, -503471, -51703]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![30646, -3379, -347]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![8, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![8, 1, 0]] 
 ![![151, 0, 0], ![8, 1, 0], ![132, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![8, 1, 0], ![-1, 7, 3], ![154, -16, 9]]]
  hmulB := by decide  
  f := ![![![-2317, 16226, 6954], ![0, -350018, 0]], ![![-122, 854, 366], ![1, -18422, 0]], ![![-2028, 14184, 6079], ![48, -305976, 0]]]
  g := ![![![1, 0, 0], ![-8, 151, 0], ![-132, 0, 151]], ![![0, 1, 0], ![-3, 7, 3], ![-6, -16, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![27, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![27, 1, 0]] 
 ![![151, 0, 0], ![27, 1, 0], ![118, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![27, 1, 0], ![-1, 26, 3], ![154, -16, 28]]]
  hmulB := by decide  
  f := ![![![-391, 10192, 1176], ![0, -59192, 0]], ![![-70, 1820, 210], ![1, -10570, 0]], ![![-322, 7964, 919], ![92, -46256, 0]]]
  g := ![![![1, 0, 0], ![-27, 151, 0], ![-118, 0, 151]], ![![0, 1, 0], ![-7, 26, 3], ![-18, -16, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36105, 2139, 1357]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![36105, 2139, 1357]] 
 ![![151, 0, 0], ![116, 1, 0], ![83, 0, 1]] where
  M :=![![![36105, 2139, 1357], ![206839, 12254, 7774], ![475962, 28198, 17889]]]
  hmulB := by decide  
  f := ![![![554, 115, -92]], ![![331, 101, -69]], ![![356, 23, -37]]]
  g := ![![![-2150, 2139, 1357], ![-12317, 12254, 7774], ![-28343, 28198, 17889]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![8, 1, 0]] ![![151, 0, 0], ![27, 1, 0]]
  ![![554, 115, -92]] where
 M := ![![![22801, 0, 0], ![4077, 151, 0]], ![![1208, 151, 0], ![215, 34, 3]]]
 hmul := by decide  
 g := ![![![![5451855, 322989, 204907]], ![![1181674, 70007, 44413]]], ![![![495679, 29366, 18630]], ![![107437, 6365, 4038]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![554, 115, -92]] ![![36105, 2139, 1357]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [74, 79, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [124, 51, 59], [72, 105, 98], [0, 1]]
 g := ![![[45, 128, 130], [104, 120], [10, 122, 14], [55, 122, 111], [78, 58, 56], [39, 1], []], ![[1, 10, 50, 135], [144, 49], [26, 15, 83, 43], [47, 29, 65, 155], [88, 103, 92, 102], [142, 35], [6, 27]], ![[154, 99, 122, 149], [143, 148], [146, 104, 55, 85], [22, 80, 81, 155], [18, 124, 8, 88], [149, 89], [124, 27]]]
 h' := ![![[124, 51, 59], [138, 79, 82], [45, 60, 77], [12, 85, 64], [37, 54, 41], [97, 142, 29], [0, 0, 1], [0, 1]], ![[72, 105, 98], [24, 81, 83], [2, 42, 7], [22, 124, 117], [51, 152, 112], [143, 121, 119], [17, 128, 105], [124, 51, 59]], ![[0, 1], [18, 154, 149], [148, 55, 73], [117, 105, 133], [79, 108, 4], [57, 51, 9], [90, 29, 51], [72, 105, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 49], []]
 b := ![[], [13, 135, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [74, 79, 118, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1653290384, 462402680, -118838324]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10530512, 2945240, -756932]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![42390, -74781, 29282]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![42390, -74781, 29282]] 
 ![![163, 0, 0], ![0, 163, 0], ![101, 5, 1]] where
  M :=![![![42390, -74781, 29282], ![4584209, -351341, -195061], ![-8353818, 2543468, -471621]]]
  hmulB := by decide  
  f := ![![![-4060314143, -240549325, -152606281]], ![![-23260817949, -1378064322, -874254256]], ![![-3557803022, -210778547, -133719478]]]
  g := ![![![-17884, -1357, 29282], ![148990, 3828, -195061], ![240981, 30071, -471621]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [12, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 162], [0, 1]]
 g := ![![[5, 135], [15, 115], [155], [16], [1], [111, 14], [1]], ![[55, 28], [124, 48], [155], [16], [1], [86, 149], [1]]]
 h' := ![![[103, 162], [146, 102], [10, 142], [27, 36], [120, 159], [135, 162], [151, 103], [0, 1]], ![[0, 1], [57, 61], [129, 21], [149, 127], [34, 4], [32, 1], [2, 60], [103, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [136, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [12, 60, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2759, 4216, -1504]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![915, 72, -1504]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4060314143, 240549325, 152606281]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![4060314143, 240549325, 152606281]] 
 ![![163, 0, 0], ![147, 1, 0], ![72, 0, 1]] where
  M :=![![![4060314143, 240549325, 152606281], ![23260817949, 1378064322, 874254256], ![53526074398, 3171099726, 2011769253]]]
  hmulB := by decide  
  f := ![![![-42390, 74781, -29282]], ![![-66353, 69596, -25211]], ![![32526, 17428, -10041]]]
  g := ![![![-259436128, 240549325, 152606281], ![-1486263459, 1378064322, 874254256], ![-3420079580, 3171099726, 2011769253]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![42390, -74781, 29282]] ![![4060314143, 240549325, 152606281]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![7, 75, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![7, 75, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![7, 75, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![7, 75, 1], ![79, -84, 226], ![11658, -1154, 67]]]
  hmulB := by decide  
  f := ![![![-6, -75, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -75, 167]], ![![0, 0, 1], ![-9, -102, 226], ![67, -37, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [43, 38, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 166], [0, 1]]
 g := ![![[164, 7], [123, 29], [35, 152], [127], [44], [166, 108], [1]], ![[65, 160], [23, 138], [104, 15], [127], [44], [70, 59], [1]]]
 h' := ![![[129, 166], [55, 95], [165, 153], [62, 94], [124, 36], [43, 82], [124, 129], [0, 1]], ![[0, 1], [119, 72], [29, 14], [164, 73], [92, 131], [100, 85], [65, 38], [129, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [58, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [43, 38, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1054, 414, -255]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 117, -255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-59, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-59, 1, 0]] 
 ![![167, 0, 0], ![108, 1, 0], ![100, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-59, 1, 0], ![-1, -60, 3], ![154, -16, -58]]]
  hmulB := by decide  
  f := ![![![-1949, -117000, 5850], ![0, -325650, 0]], ![![-1260, -75660, 3783], ![1, -210587, 0]], ![![-1160, -70060, 3503], ![20, -195000, 0]]]
  g := ![![![1, 0, 0], ![-108, 167, 0], ![-100, 0, 167]], ![![-1, 1, 0], ![37, -60, 3], ![46, -16, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![7, 75, 1]] ![![167, 0, 0], ![-59, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-9853, 167, 0]], ![![1169, 12525, 167], ![-334, -4509, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-59, 1, 0]]], ![![![7, 75, 1]], ![![-2, -27, 1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1068, 63, 40]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![1068, 63, 40]] 
 ![![173, 0, 0], ![0, 173, 0], ![44, 127, 1]] where
  M :=![![![1068, 63, 40], ![6097, 365, 229], ![14022, 832, 531]]]
  hmulB := by decide  
  f := ![![![19, -1, -1]], ![![-153, 36, -4]], ![![-109, 26, -3]]]
  g := ![![![-4, -29, 40], ![-23, -166, 229], ![-54, -385, 531]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [135, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 172], [0, 1]]
 g := ![![[118, 132], [96], [15, 51], [99, 88], [67], [171, 23], [1]], ![[0, 41], [96], [166, 122], [78, 85], [67], [22, 150], [1]]]
 h' := ![![[159, 172], [21, 88], [51, 31], [129, 33], [18, 61], [97, 97], [38, 159], [0, 1]], ![[0, 1], [0, 85], [136, 142], [13, 140], [29, 112], [123, 76], [61, 14], [159, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171]]
 b := ![[], [166, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [135, 14, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23702, -1676, 924]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98, -688, 924]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -1, -1]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![19, -1, -1]] 
 ![![173, 0, 0], ![137, 1, 0], ![17, 0, 1]] where
  M :=![![![19, -1, -1], ![-153, 36, -4], ![-262, -30, 33]]]
  hmulB := by decide  
  f := ![![![1068, 63, 40]], ![![881, 52, 33]], ![![186, 11, 7]]]
  g := ![![![1, -1, -1], ![-29, 36, -4], ![19, -30, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![1068, 63, 40]] ![![19, -1, -1]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-667, 52, 28]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-667, 52, 28]] 
 ![![179, 0, 0], ![0, 179, 0], ![136, 53, 1]] where
  M :=![![![-667, 52, 28], ![4260, -1167, 184], ![11032, 456, -1035]]]
  hmulB := by decide  
  f := ![![![6279, 372, 236]], ![![35972, 2131, 1352]], ![![15884, 941, 597]]]
  g := ![![![-25, -8, 28], ![-116, -61, 184], ![848, 309, -1035]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [148, 176, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 178], [0, 1]]
 g := ![![[156, 88], [81, 68], [151], [14], [155, 45], [34, 9], [1]], ![[62, 91], [106, 111], [151], [14], [111, 134], [61, 170], [1]]]
 h' := ![![[3, 178], [5, 25], [178, 151], [144, 35], [151, 112], [159, 89], [31, 3], [0, 1]], ![[0, 1], [80, 154], [94, 28], [70, 144], [129, 67], [68, 90], [40, 176], [3, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [105, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [148, 176, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2891, 1944, -936]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![695, 288, -936]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6279, -372, -236]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-6279, -372, -236]] 
 ![![179, 0, 0], ![19, 1, 0], ![5, 0, 1]] where
  M :=![![![-6279, -372, -236], ![-35972, -2131, -1352], ![-82776, -4904, -3111]]]
  hmulB := by decide  
  f := ![![![667, -52, -28]], ![![47, 1, -4]], ![![-43, -4, 5]]]
  g := ![![![11, -372, -236], ![63, -2131, -1352], ![145, -4904, -3111]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-667, 52, 28]] ![![-6279, -372, -236]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![64, -83, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![64, -83, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![64, 98, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![64, -83, 1], ![237, 131, -248], ![-12674, 1374, -34]]]
  hmulB := by decide  
  f := ![![![-63, 83, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -98, 181]], ![![0, -1, 1], ![89, 135, -248], ![-58, 26, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [24, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 180], [0, 1]]
 g := ![![[55, 81], [12], [168, 13], [34], [84, 154], [96, 94], [1]], ![[106, 100], [12], [22, 168], [34], [67, 27], [1, 87], [1]]]
 h' := ![![[128, 180], [40, 172], [131, 115], [171, 111], [156, 45], [49, 110], [157, 128], [0, 1]], ![[0, 1], [155, 9], [9, 66], [80, 70], [124, 136], [11, 71], [70, 53], [128, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [117, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [24, 53, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1961, 1798, -255]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![101, 148, -255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![67, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![67, 1, 0]] 
 ![![181, 0, 0], ![67, 1, 0], ![34, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![67, 1, 0], ![-1, 66, 3], ![154, -16, 68]]]
  hmulB := by decide  
  f := ![![![17798, -1179025, -53592], ![181, 3233384, 0]], ![![6545, -436393, -19836], ![182, 1196772, 0]], ![![3297, -221475, -10067], ![159, 607376, 0]]]
  g := ![![![1, 0, 0], ![-67, 181, 0], ![-34, 0, 181]], ![![0, 1, 0], ![-25, 66, 3], ![-6, -16, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![64, -83, 1]] ![![181, 0, 0], ![67, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![12127, 181, 0]], ![![11584, -15023, 181], ![4525, -5430, -181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![67, 1, 0]]], ![![![64, -83, 1]], ![![25, -30, -1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![82, -26, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![82, -26, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![82, 165, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![82, -26, 1], ![180, 92, -77], ![-3896, 462, 41]]]
  hmulB := by decide  
  f := ![![![-81, 26, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -165, 191]], ![![0, -1, 1], ![34, 67, -77], ![-38, -33, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [123, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 190], [0, 1]]
 g := ![![[39, 36], [27, 25], [100, 6], [153, 25], [188, 27], [112, 102], [1]], ![[11, 155], [50, 166], [159, 185], [176, 166], [167, 164], [160, 89], [1]]]
 h' := ![![[169, 190], [117, 6], [115, 5], [90, 31], [178, 186], [167, 119], [68, 169], [0, 1]], ![[0, 1], [176, 185], [5, 186], [172, 160], [97, 5], [32, 72], [170, 22], [169, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [146, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [123, 22, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2823, 1150, -485]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223, 425, -485]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![77, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![77, 1, 0]] 
 ![![191, 0, 0], ![77, 1, 0], ![150, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![77, 1, 0], ![-1, 76, 3], ![154, -16, 78]]]
  hmulB := by decide  
  f := ![![![19274, -1470601, -58050], ![191, 3695850, 0]], ![![7723, -592801, -23400], ![192, 1489800, 0]], ![![15156, -1154922, -45589], ![102, 2902500, 0]]]
  g := ![![![1, 0, 0], ![-77, 191, 0], ![-150, 0, 191]], ![![0, 1, 0], ![-33, 76, 3], ![-54, -16, 78]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![82, -26, 1]] ![![191, 0, 0], ![77, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![14707, 191, 0]], ![![15662, -4966, 191], ![6494, -1910, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![77, 1, 0]]], ![![![82, -26, 1]], ![![34, -10, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [116, 177, 61, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [182, 122, 167], [143, 70, 26], [0, 1]]
 g := ![![[55, 78, 129], [139, 23], [159, 165], [38, 12], [116, 18], [158, 54], [1]], ![[41, 18, 114, 77], [116, 175], [20, 101], [68, 93], [56, 112], [156, 21], [104, 109, 11, 180]], ![[136, 118, 78, 163], [68, 189], [109, 143], [103, 100], [178, 36], [178, 101], [162, 87, 84, 13]]]
 h' := ![![[182, 122, 167], [143, 148, 124], [21, 106, 71], [138, 171, 101], [140, 62, 28], [146, 79, 37], [77, 16, 132], [0, 1]], ![[143, 70, 26], [184, 61, 7], [55, 177, 91], [32, 21, 115], [59, 120, 155], [147, 77, 150], [115, 110, 139], [182, 122, 167]], ![[0, 1], [1, 177, 62], [13, 103, 31], [43, 1, 170], [5, 11, 10], [52, 37, 6], [186, 67, 115], [143, 70, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [185, 76], []]
 b := ![[], [91, 42, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [116, 177, 61, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6759246, -487132, -291816]
  a := ![-2, -12, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![35022, -2524, -1512]
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



lemma PB236I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB236I3 : PrimesBelowBoundCertificateInterval O 137 193 236 where
  m := 11
  g := ![1, 1, 3, 1, 2, 2, 2, 2, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB236I3_primes
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
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
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
    · exact ![2685619]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
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
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I151N0, I151N1, I151N2, I163N1, I167N1, I173N1, I179N1, I181N1, I191N1]
  Il := ![[], [], [I151N0, I151N1, I151N2], [], [I163N1], [I167N1], [I173N1], [I179N1], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
