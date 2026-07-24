
import IdealArithmetic.Examples.NF3_1_456435_2.RI3_1_456435_2
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [94, 49, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 55, 80], [105, 83, 59], [0, 1]]
 g := ![![[62, 111, 5], [44, 109, 83], [70, 44], [112, 10, 51], [43, 7], [115, 1], []], ![[87, 133, 131, 67], [33, 13, 128, 118], [69, 78], [91, 121, 103, 67], [41, 28], [134, 78], [38, 6]], ![[29, 85, 31, 135], [117, 28, 38, 126], [103, 67], [70, 51, 112, 53], [47, 7], [7, 106], [59, 6]]]
 h' := ![![[10, 55, 80], [34, 112, 127], [137, 102, 120], [36, 37, 34], [40, 41, 32], [32, 109, 110], [0, 0, 1], [0, 1]], ![[105, 83, 59], [6, 110, 41], [127, 85, 50], [91, 41, 83], [129, 133, 98], [62, 108, 58], [3, 64, 83], [10, 55, 80]], ![[0, 1], [117, 56, 110], [15, 91, 108], [55, 61, 22], [85, 104, 9], [65, 61, 110], [58, 75, 55], [105, 83, 59]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 39], []]
 b := ![[], [34, 18, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [94, 49, 24, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5951980, -1446434, -555444]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-42820, -10406, -3996]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![23, 70, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![23, 70, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![23, 70, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![23, 70, 1], ![295, 250, 557], ![10738, 1203, -168]]]
  hmulB := by decide  
  f := ![![![-22, -70, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -70, 149]], ![![0, 0, 1], ![-84, -260, 557], ![98, 87, -168]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [132, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 148], [0, 1]]
 g := ![![[69, 35], [53], [16, 133], [47], [35, 45], [63], [1]], ![[0, 114], [53], [22, 16], [47], [74, 104], [63], [1]]]
 h' := ![![[130, 148], [87, 83], [123, 65], [55, 122], [148, 14], [19, 94], [17, 130], [0, 1]], ![[0, 1], [0, 66], [80, 84], [121, 27], [31, 135], [21, 55], [80, 19], [130, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [59, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [132, 19, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3310, 1723, 1670]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-280, -773, 1670]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![39, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![39, 1, 0]] 
 ![![149, 0, 0], ![39, 1, 0], ![19, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![39, 1, 0], ![2, 42, 8], ![155, 17, 36]]]
  hmulB := by decide  
  f := ![![![26219, 611110, 116416], ![11026, -2168248, 0]], ![![6836, 159916, 30464], ![2981, -567392, 0]], ![![3313, 77926, 14845], ![1522, -276488, 0]]]
  g := ![![![1, 0, 0], ![-39, 149, 0], ![-19, 0, 149]], ![![0, 1, 0], ![-12, 42, 8], ![-8, 17, 36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![23, 70, 1]] ![![149, 0, 0], ![39, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![5811, 149, 0]], ![![3427, 10430, 149], ![1192, 2980, 596]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![39, 1, 0]]], ![![![23, 70, 1]], ![![8, 20, 4]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![15, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![15, 1, 0]] 
 ![![151, 0, 0], ![15, 1, 0], ![42, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![15, 1, 0], ![2, 18, 8], ![155, 17, 12]]]
  hmulB := by decide  
  f := ![![![1099, 10150, 4512], ![302, -85164, 0]], ![![97, 1007, 448], ![152, -8456, 0]], ![![303, 2823, 1255], ![111, -23688, 0]]]
  g := ![![![1, 0, 0], ![-15, 151, 0], ![-42, 0, 151]], ![![0, 1, 0], ![-4, 18, 8], ![-4, 17, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![64, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![64, 1, 0]] 
 ![![151, 0, 0], ![64, 1, 0], ![106, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![64, 1, 0], ![2, 67, 8], ![155, 17, 61]]]
  hmulB := by decide  
  f := ![![![-7037, -304349, -36344], ![-4832, 685993, 0]], ![![-3018, -128962, -15400], ![-1962, 290675, 0]], ![![-4942, -213649, -25513], ![-3387, 481558, 0]]]
  g := ![![![1, 0, 0], ![-64, 151, 0], ![-106, 0, 151]], ![![0, 1, 0], ![-34, 67, 8], ![-49, 17, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![72, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![72, 1, 0]] 
 ![![151, 0, 0], ![72, 1, 0], ![118, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![72, 1, 0], ![2, 75, 8], ![155, 17, 69]]]
  hmulB := by decide  
  f := ![![![-16939, -883558, -94256], ![-13892, 1779082, 0]], ![![-8138, -421232, -44936], ![-6492, 848167, 0]], ![![-13270, -690463, -73657], ![-10787, 1390276, 0]]]
  g := ![![![1, 0, 0], ![-72, 151, 0], ![-118, 0, 151]], ![![0, 1, 0], ![-42, 75, 8], ![-61, 17, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![15, 1, 0]] ![![151, 0, 0], ![64, 1, 0]]
  ![![151, 0, 0], ![7, 48, 1]] where
 M := ![![![22801, 0, 0], ![9664, 151, 0]], ![![2265, 151, 0], ![962, 82, 8]]]
 hmul := by decide  
 g := ![![![![144, -48, -1], ![151, 0, 0]], ![![57, -47, -1], ![151, 0, 0]]], ![![![8, -47, -1], ![151, 0, 0]], ![![6, -2, 0], ![8, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![7, 48, 1]] ![![151, 0, 0], ![72, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![10872, 151, 0]], ![![1057, 7248, 151], ![755, 3624, 453]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![72, 1, 0]]], ![![![7, 48, 1]], ![![5, 24, 3]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [90, 116, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 82, 129], [91, 74, 28], [0, 1]]
 g := ![![[64, 104, 33], [69, 10], [139, 102, 110], [14, 19, 10], [140, 137, 99], [140, 1], []], ![[28, 35, 34, 103], [117, 130], [111, 97], [68, 69, 72, 152], [4, 56, 84, 54], [148, 138], [135, 156]], ![[72, 29, 44, 78], [18, 109], [59, 35, 69, 97], [145, 114, 55, 152], [147, 54], [131, 130], [79, 156]]]
 h' := ![![[49, 82, 129], [58, 44, 70], [50, 146, 139], [153, 150, 61], [117, 34, 139], [117, 155, 16], [0, 0, 1], [0, 1]], ![[91, 74, 28], [65, 137, 23], [95, 4, 75], [151, 19], [12, 83, 71], [93, 25, 141], [142, 2, 74], [49, 82, 129]], ![[0, 1], [153, 133, 64], [108, 7, 100], [140, 145, 96], [31, 40, 104], [145, 134], [72, 155, 82], [91, 74, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 7], []]
 b := ![[], [149, 134, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [90, 116, 17, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-329767511256, -83806729682, -33649644208]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2100430008, -533800826, -214328944]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-8, 40, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-8, 40, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![155, 40, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-8, 40, 1], ![235, 129, 317], ![6088, 693, -109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-155, -40, 163]], ![![-1, 0, 1], ![-300, -77, 317], ![141, 31, -109]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [89, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 162], [0, 1]]
 g := ![![[7, 10], [56, 155], [113], [119], [136], [156, 26], [1]], ![[134, 153], [150, 8], [113], [119], [136], [95, 137], [1]]]
 h' := ![![[29, 162], [69, 70], [4, 36], [97, 90], [147, 49], [134, 25], [74, 29], [0, 1]], ![[0, 1], [143, 93], [70, 127], [99, 73], [101, 114], [44, 138], [100, 134], [29, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [115, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [89, 134, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3080, 3501, 1363]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1315, -313, 1363]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![9, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![9, 1, 0]] 
 ![![163, 0, 0], ![9, 1, 0], ![109, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![9, 1, 0], ![2, 12, 8], ![155, 17, 6]]]
  hmulB := by decide  
  f := ![![![4904, 29577, 19720], ![489, -401795, 0]], ![![263, 1631, 1088], ![164, -22168, 0]], ![![3275, 19778, 13187], ![406, -268685, 0]]]
  g := ![![![1, 0, 0], ![-9, 163, 0], ![-109, 0, 163]], ![![0, 1, 0], ![-6, 12, 8], ![-4, 17, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-8, 40, 1]] ![![163, 0, 0], ![9, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![1467, 163, 0]], ![![-1304, 6520, 163], ![163, 489, 326]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![9, 1, 0]]], ![![![-8, 40, 1]], ![![1, 3, 2]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![24, -70, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![24, -70, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![24, 97, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![24, -70, 1], ![15, -169, -563], ![-10962, -1177, 253]]]
  hmulB := by decide  
  f := ![![![-23, 70, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -97, 167]], ![![0, -1, 1], ![81, 326, -563], ![-102, -154, 253]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [11, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 166], [0, 1]]
 g := ![![[126, 76], [166, 76], [139, 18], [36], [28], [14, 162], [1]], ![[0, 91], [40, 91], [74, 149], [36], [28], [97, 5], [1]]]
 h' := ![![[117, 166], [11, 57], [141, 110], [54, 39], [28, 6], [13, 144], [156, 117], [0, 1]], ![[0, 1], [0, 110], [152, 57], [108, 128], [62, 161], [161, 23], [151, 50], [117, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [76, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [11, 50, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2392, 3767, 2048]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-280, -1167, 2048]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![62, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![62, 1, 0]] 
 ![![167, 0, 0], ![62, 1, 0], ![81, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![62, 1, 0], ![2, 65, 8], ![155, 17, 59]]]
  hmulB := by decide  
  f := ![![![25791, 1029505, 126720], ![15865, -2645280, 0]], ![![9528, 382164, 47040], ![6013, -981960, 0]], ![![12525, 499341, 61463], ![7653, -1283040, 0]]]
  g := ![![![1, 0, 0], ![-62, 167, 0], ![-81, 0, 167]], ![![0, 1, 0], ![-28, 65, 8], ![-34, 17, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![24, -70, 1]] ![![167, 0, 0], ![62, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![10354, 167, 0]], ![![4008, -11690, 167], ![1503, -4509, -501]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![62, 1, 0]]], ![![![24, -70, 1]], ![![9, -27, -3]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![72, -31, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![72, -31, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![72, 142, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![72, -31, 1], ![93, -4, -251], ![-4917, -514, 184]]]
  hmulB := by decide  
  f := ![![![-71, 31, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-72, -142, 173]], ![![0, -1, 1], ![105, 206, -251], ![-105, -154, 184]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [7, 129, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 172], [0, 1]]
 g := ![![[142, 169], [130], [148, 57], [63, 169], [113], [144, 33], [1]], ![[139, 4], [130], [61, 116], [60, 4], [113], [39, 140], [1]]]
 h' := ![![[44, 172], [132, 13], [2, 87], [78, 149], [109, 13], [30, 99], [166, 44], [0, 1]], ![[0, 1], [12, 160], [24, 86], [60, 24], [162, 160], [61, 74], [26, 129], [44, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [78, 138]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [7, 129, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![321143, 257297, 164728]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66701, -133723, 164728]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![78, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![78, 1, 0]] 
 ![![173, 0, 0], ![78, 1, 0], ![162, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![78, 1, 0], ![2, 81, 8], ![155, 17, 75]]]
  hmulB := by decide  
  f := ![![![-21957, -1195625, -118096], ![-16781, 2553826, 0]], ![![-9956, -539012, -53240], ![-7438, 1151315, 0]], ![![-20592, -1119603, -110587], ![-15645, 2391444, 0]]]
  g := ![![![1, 0, 0], ![-78, 173, 0], ![-162, 0, 173]], ![![0, 1, 0], ![-44, 81, 8], ![-77, 17, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![72, -31, 1]] ![![173, 0, 0], ![78, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![13494, 173, 0]], ![![12456, -5363, 173], ![5709, -2422, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![78, 1, 0]]], ![![![72, -31, 1]], ![![33, -14, -1]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [103, 10, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 45, 70], [18, 133, 109], [0, 1]]
 g := ![![[109, 158, 16], [158, 158, 74], [70, 56], [89, 3], [42, 126, 22], [139, 68, 1], []], ![[32, 97, 53, 101], [89, 23, 47, 155], [120, 88], [26, 49], [10, 18, 141, 141], [83, 10, 77, 87], [116, 67]], ![[87, 88, 35, 165], [49, 122, 143, 159], [134, 42], [108, 139], [33, 126, 146, 163], [78, 56, 29, 18], [77, 67]]]
 h' := ![![[50, 45, 70], [15, 18, 4], [144, 68, 130], [146, 42, 45], [149, 36, 160], [3, 19, 77], [0, 0, 1], [0, 1]], ![[18, 133, 109], [176, 170, 2], [22, 160, 33], [63, 60, 154], [134, 6, 172], [18, 170, 115], [39, 19, 133], [50, 45, 70]], ![[0, 1], [162, 170, 173], [1, 130, 16], [119, 77, 159], [161, 137, 26], [115, 169, 166], [90, 160, 45], [18, 133, 109]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 63], []]
 b := ![[], [96, 102, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [103, 10, 111, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-105610, 0, 13425]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-590, 0, 75]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-14, 26, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-14, 26, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![167, 26, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-14, 26, 1], ![207, 81, 205], ![3918, 455, -73]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-167, -26, 181]], ![![-1, 0, 1], ![-188, -29, 205], ![89, 13, -73]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [180, 174, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 180], [0, 1]]
 g := ![![[7, 180], [59], [129, 67], [138], [158, 44], [176, 49], [1]], ![[0, 1], [59], [55, 114], [138], [104, 137], [157, 132], [1]]]
 h' := ![![[7, 180], [48, 19], [129, 56], [124, 130], [158, 89], [176, 15], [1, 7], [0, 1]], ![[0, 1], [0, 162], [159, 125], [129, 51], [57, 92], [100, 166], [50, 174], [7, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [106, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [180, 174, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6003, 12304, 10832]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9961, -1488, 10832]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-24, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-24, 1, 0]] 
 ![![181, 0, 0], ![157, 1, 0], ![73, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-24, 1, 0], ![2, -21, 8], ![155, 17, -27]]]
  hmulB := by decide  
  f := ![![![957, -10289, 3920], ![-181, -88690, 0]], ![![851, -8925, 3400], ![1, -76925, 0]], ![![393, -4150, 1581], ![-20, -35770, 0]]]
  g := ![![![1, 0, 0], ![-157, 181, 0], ![-73, 0, 181]], ![![-1, 1, 0], ![15, -21, 8], ![-3, 17, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-14, 26, 1]] ![![181, 0, 0], ![-24, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-4344, 181, 0]], ![![-2534, 4706, 181], ![543, -543, 181]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-24, 1, 0]]], ![![![-14, 26, 1]], ![![3, -3, 1]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-34, 73, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-34, 73, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![157, 73, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-34, 73, 1], ![301, 202, 581], ![11203, 1254, -234]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-157, -73, 191]], ![![-1, 0, 1], ![-476, -221, 581], ![251, 96, -234]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [61, 182, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 190], [0, 1]]
 g := ![![[75, 10], [117, 147], [122, 184], [79, 48], [13, 130], [13, 81], [1]], ![[165, 181], [103, 44], [59, 7], [129, 143], [37, 61], [169, 110], [1]]]
 h' := ![![[9, 190], [121, 157], [7, 23], [147, 152], [162, 95], [162, 43], [130, 9], [0, 1]], ![[0, 1], [6, 34], [23, 168], [178, 39], [62, 96], [167, 148], [20, 182], [9, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109]]
 b := ![[], [89, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [61, 182, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24341, 32020, 16255]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13234, -6045, 16255]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-8, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-8, 1, 0]] 
 ![![191, 0, 0], ![183, 1, 0], ![43, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-8, 1, 0], ![2, -5, 8], ![155, 17, -11]]]
  hmulB := by decide  
  f := ![![![13337, -33397, 53440], ![-573, -1275880, 0]], ![![12777, -31997, 51200], ![-572, -1222400, 0]], ![![3005, -7519, 12031], ![-71, -287240, 0]]]
  g := ![![![1, 0, 0], ![-183, 191, 0], ![-43, 0, 191]], ![![-1, 1, 0], ![3, -5, 8], ![-13, 17, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-34, 73, 1]] ![![191, 0, 0], ![-8, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-1528, 191, 0]], ![![-6494, 13943, 191], ![573, -382, 573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-8, 1, 0]]], ![![![-34, 73, 1]], ![![3, -2, 3]]]]
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


lemma PB192I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 191 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 191 (by omega)

def PB192I3 : PrimesBelowBoundCertificateInterval O 137 191 192 where
  m := 10
  g := ![1, 2, 3, 1, 2, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191]
  hP := PB192I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
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
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
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
      exact NI149N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
  β := ![I149N1, I151N0, I151N1, I151N2, I163N1, I167N1, I173N1, I181N1, I191N1]
  Il := ![[], [I149N1], [I151N0, I151N1, I151N2], [], [I163N1], [I167N1], [I173N1], [], [I181N1], [I191N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
