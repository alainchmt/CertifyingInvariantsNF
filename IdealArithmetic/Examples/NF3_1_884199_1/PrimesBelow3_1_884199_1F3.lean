
import IdealArithmetic.Examples.NF3_1_884199_1.RI3_1_884199_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-282466219, -8120597, 5232064]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-282466219, -8120597, 5232064]] 
 ![![139, 0, 0], ![0, 139, 0], ![40, 34, 1]] where
  M :=![![![-282466219, -8120597, 5232064], ![1710884928, 12872896, -24361791], ![-3225730195, 99300350, 20993493]]]
  hmulB := by decide  
  f := ![![![19348067805702, 4964212105739, 938708425697]], ![![306957655202919, 78757368601867, 14892636317217]], ![![91593245534554, 23500449908107, 4443821066974]]]
  g := ![![![-3537761, -1338207, 5232064], ![19319112, 6051610, -24361791], ![-29247985, -4420708, 20993493]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [59, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [112, 138], [0, 1]]
 g := ![![[57, 55], [45, 11], [55], [40, 44], [129], [34], [1]], ![[101, 84], [26, 128], [55], [103, 95], [129], [34], [1]]]
 h' := ![![[112, 138], [125, 74], [100, 17], [3, 65], [31, 105], [85, 44], [80, 112], [0, 1]], ![[0, 1], [73, 65], [58, 122], [55, 74], [115, 34], [9, 95], [114, 27], [112, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [60, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [59, 27, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3874, 3835, 1327]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-354, -297, 1327]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4455059, 184178, -93842]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![4455059, 184178, -93842]] 
 ![![139, 0, 0], ![37, 1, 0], ![41, 0, 1]] where
  M :=![![![4455059, 184178, -93842], ![-30686334, -803599, 552534], ![70454984, 453546, -987777]]]
  hmulB := by decide  
  f := ![![![-543177023859, -139365128574, -26353269694]], ![![-206583230739, -53003896057, -10022779600]], ![![-467411141189, -119925569248, -22677343335]]]
  g := ![![![10705, 184178, -93842], ![-169835, -803599, 552534], ![677501, 453546, -987777]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-282466219, -8120597, 5232064]] ![![4455059, 184178, -93842]]
  ![![139, 0, 0]] where
 M := ![![![-640587333923547, -43125377955435, 16852176498872]]]
 hmul := by decide  
 g := ![![![![-4608541970673, -310254517665, 121238679848]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [65, 119, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 96, 94], [120, 52, 55], [0, 1]]
 g := ![![[9, 105, 69], [121, 86], [59, 129, 64], [97, 20], [61, 58, 7], [131, 1], []], ![[72, 21, 110, 11], [93, 95], [17, 92, 3, 50], [45, 20], [15, 143, 135, 52], [98, 22], [103, 45]], ![[57, 66, 53, 66], [115, 25], [107, 121, 45, 48], [135, 80], [79, 50, 140, 58], [80, 127], [142, 45]]]
 h' := ![![[11, 96, 94], [63, 28, 48], [39, 121, 58], [39, 41, 141], [58, 34, 136], [127, 140, 56], [0, 0, 1], [0, 1]], ![[120, 52, 55], [103, 85, 62], [28, 46, 86], [38, 24, 11], [70, 36, 136], [63, 147, 129], [131, 42, 52], [11, 96, 94]], ![[0, 1], [71, 36, 39], [29, 131, 5], [104, 84, 146], [104, 79, 26], [103, 11, 113], [104, 107, 96], [120, 52, 55]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51, 104], []]
 b := ![[], [78, 70, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [65, 119, 18, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5096694, 1888426, 456238]
  a := ![-1, 1, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![34206, 12674, 3062]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-64, 62, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-64, 62, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![87, 62, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-64, 62, 1], ![327, 56, 186], ![20165, 3705, -6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -62, 151]], ![![-1, 0, 1], ![-105, -76, 186], ![137, 27, -6]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [103, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 150], [0, 1]]
 g := ![![[64, 22], [95, 94], [27, 99], [34], [72, 88], [137], [1]], ![[0, 129], [0, 57], [41, 52], [34], [118, 63], [137], [1]]]
 h' := ![![[52, 150], [30, 133], [88, 68], [109, 34], [134, 51], [122, 36], [48, 52], [0, 1]], ![[0, 1], [0, 18], [0, 83], [65, 117], [68, 100], [31, 115], [34, 99], [52, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [97, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [103, 99, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2246, 109, 87]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-65, -35, 87]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-35, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-35, 1, 0]] 
 ![![151, 0, 0], ![116, 1, 0], ![6, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-35, 1, 0], ![0, -34, 3], ![327, 58, -35]]]
  hmulB := by decide  
  f := ![![![3151, -90, 0], ![13590, 0, 0]], ![![2416, -69, 0], ![10420, 0, 0]], ![![166, 18, -2], ![716, 101, 0]]]
  g := ![![![1, 0, 0], ![-116, 151, 0], ![-6, 0, 151]], ![![-1, 1, 0], ![26, -34, 3], ![-41, 58, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-64, 62, 1]] ![![151, 0, 0], ![-35, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-5285, 151, 0]], ![![-9664, 9362, 151], ![2567, -2114, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-35, 1, 0]]], ![![![-64, 62, 1]], ![![17, -14, 1]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [35, 132, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 121, 145], [112, 35, 12], [0, 1]]
 g := ![![[143, 44, 68], [96, 9], [24, 87, 110], [154, 149, 118], [144, 76, 148], [131, 1], []], ![[42, 145, 145, 67], [138, 148], [78, 145, 90, 52], [107, 96, 125, 106], [11, 76, 156, 138], [24, 126], [103, 144]], ![[119, 13, 88, 99], [154, 124], [144, 19, 11, 99], [150, 74, 77, 9], [20, 149, 46, 31], [89, 40], [79, 144]]]
 h' := ![![[19, 121, 145], [136, 128, 142], [102, 102, 154], [105, 147, 96], [141, 80, 78], [125, 100, 73], [0, 0, 1], [0, 1]], ![[112, 35, 12], [46, 135, 137], [154, 134, 84], [136, 86, 26], [143, 57, 43], [85, 133, 99], [53, 92, 35], [19, 121, 145]], ![[0, 1], [138, 51, 35], [87, 78, 76], [8, 81, 35], [51, 20, 36], [9, 81, 142], [45, 65, 121], [112, 35, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 68], []]
 b := ![[], [39, 120, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [35, 132, 26, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15530126, -5157921, -1145786]
  a := ![1, -2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-98918, -32853, -7298]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-19, 20, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-19, 20, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![144, 20, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-19, 20, 1], ![327, 59, 60], ![6431, 1269, 39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-144, -20, 163]], ![![-1, 0, 1], ![-51, -7, 60], ![5, 3, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [129, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 162], [0, 1]]
 g := ![![[112, 55], [37, 10], [26], [1], [16], [99, 58], [1]], ![[97, 108], [138, 153], [26], [1], [16], [98, 105], [1]]]
 h' := ![![[59, 162], [117, 50], [102, 70], [14, 134], [44, 162], [106, 4], [34, 59], [0, 1]], ![[0, 1], [133, 113], [157, 93], [96, 29], [148, 1], [16, 159], [92, 104], [59, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [65, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [129, 104, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3944, 3681, 942]
  a := ![0, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-808, -93, 942]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-60, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-60, 1, 0]] 
 ![![163, 0, 0], ![103, 1, 0], ![124, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-60, 1, 0], ![0, -59, 3], ![327, 58, -60]]]
  hmulB := by decide  
  f := ![![![9121, -152, 0], ![24776, 0, 0]], ![![5821, -97, 0], ![15812, 0, 0]], ![![6988, -77, -2], ![18982, 109, 0]]]
  g := ![![![1, 0, 0], ![-103, 163, 0], ![-124, 0, 163]], ![![-1, 1, 0], ![35, -59, 3], ![11, 58, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-19, 20, 1]] ![![163, 0, 0], ![-60, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-9780, 163, 0]], ![![-3097, 3260, 163], ![1467, -1141, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-60, 1, 0]]], ![![![-19, 20, 1]], ![![9, -7, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [94, 19, 64, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 97, 138], [21, 69, 29], [0, 1]]
 g := ![![[24, 14, 114], [3, 61, 31], [159, 82, 1], [28, 38], [9, 112], [69, 103, 1], []], ![[84, 133, 46, 134], [125, 39, 22, 106], [7, 51, 50, 135], [45, 114], [123, 25], [32, 83, 160, 40], [2, 6]], ![[24, 105, 152, 44], [96, 78, 130, 27], [39, 132, 166, 14], [67, 21], [37, 11], [134, 85, 1, 150], [111, 6]]]
 h' := ![![[82, 97, 138], [52, 96, 92], [84, 15, 96], [35, 94, 166], [50, 52, 120], [27, 29, 46], [0, 0, 1], [0, 1]], ![[21, 69, 29], [20, 135, 57], [15, 62, 10], [38, 158, 44], [60, 88, 92], [123, 145, 162], [23, 109, 69], [82, 97, 138]], ![[0, 1], [43, 103, 18], [152, 90, 61], [145, 82, 124], [40, 27, 122], [41, 160, 126], [27, 58, 97], [21, 69, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 96], []]
 b := ![[], [157, 145, 130], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [94, 19, 64, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3965245996, 1249751347, 272522791]
  a := ![1, 20, 41]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23743988, 7483541, 1631873]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![11, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![11, 1, 0]] 
 ![![173, 0, 0], ![11, 1, 0], ![129, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![11, 1, 0], ![0, 12, 3], ![327, 58, 11]]]
  hmulB := by decide  
  f := ![![![628, 57, 0], ![-9861, 0, 0]], ![![22, 2, 0], ![-345, 0, 0]], ![![474, 39, -1], ![-7443, 58, 0]]]
  g := ![![![1, 0, 0], ![-11, 173, 0], ![-129, 0, 173]], ![![0, 1, 0], ![-3, 12, 3], ![-10, 58, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![44, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![44, 1, 0]] 
 ![![173, 0, 0], ![44, 1, 0], ![32, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![44, 1, 0], ![0, 45, 3], ![327, 58, 44]]]
  hmulB := by decide  
  f := ![![![2157, 49, 0], ![-8477, 0, 0]], ![![484, 11, 0], ![-1902, 0, 0]], ![![400, -6, -1], ![-1572, 58, 0]]]
  g := ![![![1, 0, 0], ![-44, 173, 0], ![-32, 0, 173]], ![![0, 1, 0], ![-12, 45, 3], ![-21, 58, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-56, 1, 0]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-56, 1, 0]] 
 ![![173, 0, 0], ![117, 1, 0], ![69, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-56, 1, 0], ![0, -55, 3], ![327, 58, -56]]]
  hmulB := by decide  
  f := ![![![5825, -104, 0], ![17992, 0, 0]], ![![3977, -71, 0], ![12284, 0, 0]], ![![2377, -24, -1], ![7342, 58, 0]]]
  g := ![![![1, 0, 0], ![-117, 173, 0], ![-69, 0, 173]], ![![-1, 1, 0], ![36, -55, 3], ![-15, 58, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![11, 1, 0]] ![![173, 0, 0], ![44, 1, 0]]
  ![![173, 0, 0], ![46, -39, 1]] where
 M := ![![![29929, 0, 0], ![7612, 173, 0]], ![![1903, 173, 0], ![484, 56, 3]]]
 hmul := by decide  
 g := ![![![![127, 39, -1], ![173, 0, 0]], ![![-2, 40, -1], ![173, 0, 0]]], ![![![-35, 40, -1], ![173, 0, 0]], ![![2, 1, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![46, -39, 1]] ![![173, 0, 0], ![-56, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-9688, 173, 0]], ![![7958, -6747, 173], ![-2249, 2249, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-56, 1, 0]]], ![![![46, -39, 1]], ![![-13, 13, -1]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [29, 161, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 45, 151], [33, 133, 28], [0, 1]]
 g := ![![[162, 151, 68], [89, 117, 49], [120, 88], [113, 20], [65, 112, 82], [139, 168, 1], []], ![[29, 91, 118, 153], [176, 99, 0, 45], [90, 47], [150, 135], [84, 58, 118, 67], [3, 162, 57, 1], [133, 68]], ![[159, 79, 65, 120], [108, 123, 160, 8], [99, 60], [19, 89], [17, 111, 132, 32], [87, 40, 173, 136], [77, 68]]]
 h' := ![![[135, 45, 151], [104, 115, 151], [142, 98, 7], [20, 57, 154], [84, 127, 119], [86, 136, 34], [0, 0, 1], [0, 1]], ![[33, 133, 28], [144, 61, 37], [104, 50, 156], [71, 83, 91], [29, 152, 99], [30, 30, 177], [48, 42, 133], [135, 45, 151]], ![[0, 1], [131, 3, 170], [22, 31, 16], [71, 39, 113], [62, 79, 140], [46, 13, 147], [109, 137, 45], [33, 133, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 121], []]
 b := ![[], [94, 90, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [29, 161, 11, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1847101, 552036, 116529]
  a := ![-1, 2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10319, 3084, 651]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![60, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![60, 1, 0]] 
 ![![181, 0, 0], ![60, 1, 0], ![47, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![60, 1, 0], ![0, 61, 3], ![327, 58, 60]]]
  hmulB := by decide  
  f := ![![![7321, 122, 0], ![-22082, 0, 0]], ![![2340, 39, 0], ![-7058, 0, 0]], ![![1907, -9, -2], ![-5752, 121, 0]]]
  g := ![![![1, 0, 0], ![-60, 181, 0], ![-47, 0, 181]], ![![0, 1, 0], ![-21, 61, 3], ![-33, 58, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-57, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-57, 1, 0]] 
 ![![181, 0, 0], ![124, 1, 0], ![22, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-57, 1, 0], ![0, -56, 3], ![327, 58, -57]]]
  hmulB := by decide  
  f := ![![![6271, -110, 0], ![19910, 0, 0]], ![![4276, -75, 0], ![13576, 0, 0]], ![![766, 24, -2], ![2432, 121, 0]]]
  g := ![![![1, 0, 0], ![-124, 181, 0], ![-22, 0, 181]], ![![-1, 1, 0], ![38, -56, 3], ![-31, 58, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![81, 21, 4]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![81, 21, 4]] 
 ![![181, 0, 0], ![177, 1, 0], ![177, 0, 1]] where
  M :=![![![81, 21, 4], ![1308, 334, 63], ![6431, 1654, 313]]]
  hmulB := by decide  
  f := ![![![340, 43, -13]], ![![309, 40, -12]], ![![418, 48, -15]]]
  g := ![![![-24, 21, 4], ![-381, 334, 63], ![-1888, 1654, 313]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![60, 1, 0]] ![![181, 0, 0], ![-57, 1, 0]]
  ![![340, 43, -13]] where
 M := ![![![32761, 0, 0], ![-10317, 181, 0]], ![![10860, 181, 0], ![-3420, 4, 3]]]
 hmul := by decide  
 g := ![![![![14661, 3801, 724]], ![![-3309, -863, -165]]], ![![![6168, 1594, 303]], ![![-1395, -362, -69]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![340, 43, -13]] ![![81, 21, 4]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-112, 86, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-112, 86, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![79, 86, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-112, 86, 1], ![327, 32, 258], ![28013, 5097, -54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -86, 191]], ![![-1, 0, 1], ![-105, -116, 258], ![169, 51, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [172, 175, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 190], [0, 1]]
 g := ![![[31, 10], [92, 60], [97, 170], [67, 27], [163, 163], [120, 65], [1]], ![[0, 181], [97, 131], [143, 21], [117, 164], [97, 28], [14, 126], [1]]]
 h' := ![![[16, 190], [29, 34], [124, 92], [127, 19], [41, 119], [179, 78], [19, 16], [0, 1]], ![[0, 1], [0, 157], [68, 99], [49, 172], [35, 72], [90, 113], [84, 175], [16, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [99, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [172, 175, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8892, 10294, 5139]
  a := ![0, 3, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2079, -2260, 5139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-67, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-67, 1, 0]] 
 ![![191, 0, 0], ![124, 1, 0], ![54, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-67, 1, 0], ![0, -66, 3], ![327, 58, -67]]]
  hmulB := by decide  
  f := ![![![9783, -146, 0], ![27886, 0, 0]], ![![6366, -95, 0], ![18146, 0, 0]], ![![2822, -20, -1], ![8044, 64, 0]]]
  g := ![![![1, 0, 0], ![-124, 191, 0], ![-54, 0, 191]], ![![-1, 1, 0], ![42, -66, 3], ![-17, 58, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-112, 86, 1]] ![![191, 0, 0], ![-67, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-12797, 191, 0]], ![![-21392, 16426, 191], ![7831, -5730, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-67, 1, 0]]], ![![![-112, 86, 1]], ![![41, -30, 1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-69, 18, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-69, 18, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![124, 18, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-69, 18, 1], ![327, 7, 54], ![5777, 1153, -11]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -18, 193]], ![![-1, 0, 1], ![-33, -5, 54], ![37, 7, -11]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [63, 192, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [1, 192], [0, 1]]
 g := ![![[49, 144], [93], [27], [75], [179], [177], [1, 1]], ![[0, 49], [93], [27], [75], [179], [177], [2, 192]]]
 h' := ![![[1, 192], [12, 181], [9, 155], [121, 42], [54, 123], [152, 76], [130, 131], [0, 1]], ![[0, 1], [0, 12], [164, 38], [163, 151], [177, 70], [35, 117], [68, 62], [1, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [183, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [63, 192, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52335, 32852, 8816]
  a := ![2, -8, -14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5393, -652, 8816]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-54, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-54, 1, 0]] 
 ![![193, 0, 0], ![139, 1, 0], ![11, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-54, 1, 0], ![0, -53, 3], ![327, 58, -54]]]
  hmulB := by decide  
  f := ![![![9289, -172, 0], ![33196, 0, 0]], ![![6751, -125, 0], ![24126, 0, 0]], ![![563, 25, -2], ![2012, 129, 0]]]
  g := ![![![1, 0, 0], ![-139, 193, 0], ![-11, 0, 193]], ![![-1, 1, 0], ![38, -53, 3], ![-37, 58, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-69, 18, 1]] ![![193, 0, 0], ![-54, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-10422, 193, 0]], ![![-13317, 3474, 193], ![4053, -965, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-54, 1, 0]]], ![![![-69, 18, 1]], ![![21, -5, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB267I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB267I3 : PrimesBelowBoundCertificateInterval O 137 193 267 where
  m := 11
  g := ![2, 1, 2, 1, 2, 1, 3, 1, 3, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB267I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![173, 173, 173]
    · exact ![5735339]
    · exact ![181, 181, 181]
    · exact ![36481, 191]
    · exact ![37249, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I151N1, I163N1, I173N0, I173N1, I173N2, I181N0, I181N1, I181N2, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [], [I163N1], [], [I173N0, I173N1, I173N2], [], [I181N0, I181N1, I181N2], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
