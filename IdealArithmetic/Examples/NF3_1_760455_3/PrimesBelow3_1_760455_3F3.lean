
import IdealArithmetic.Examples.NF3_1_760455_3.RI3_1_760455_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-411986, -455, -13699]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-411986, -455, -13699]] 
 ![![139, 0, 0], ![0, 139, 0], ![45, 107, 1]] where
  M :=![![![-411986, -455, -13699], ![-507773, -561, -16884], ![-44233, -49, -1471]]]
  hmulB := by decide  
  f := ![![![15, -14, 21]], ![![749, -601, -77]], ![![578, -464, -57]]]
  g := ![![![1471, 10542, -13699], ![1813, 12993, -16884], ![158, 1132, -1471]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [30, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [19, 138], [0, 1]]
 g := ![![[4, 51], [11, 36], [65], [59, 11], [122], [83], [1]], ![[0, 88], [0, 103], [65], [129, 128], [122], [83], [1]]]
 h' := ![![[19, 138], [87, 32], [114, 133], [37, 64], [61, 17], [78, 20], [109, 19], [0, 1]], ![[0, 1], [0, 107], [0, 6], [2, 75], [106, 122], [41, 119], [53, 120], [19, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [7, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [30, 120, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-108, 49, -2282]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![738, 1757, -2282]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -14, 21]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![15, -14, 21]] 
 ![![139, 0, 0], ![84, 1, 0], ![17, 0, 1]] where
  M :=![![![15, -14, 21], ![749, -601, -77], ![-476, 441, -629]]]
  hmulB := by decide  
  f := ![![![-411986, -455, -13699]], ![![-252623, -279, -8400]], ![![-50705, -56, -1686]]]
  g := ![![![6, -14, 21], ![378, -601, -77], ![-193, 441, -629]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-411986, -455, -13699]] ![![15, -14, 21]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![5, 10, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![5, 10, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![5, 10, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![5, 10, 1], ![57, -35, 71], ![372, -299, -15]]]
  hmulB := by decide  
  f := ![![![-4, -10, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -10, 149]], ![![0, 0, 1], ![-2, -5, 71], ![3, -1, -15]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [60, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 148], [0, 1]]
 g := ![![[144, 29], [49], [29, 5], [31], [17, 35], [4], [1]], ![[53, 120], [49], [39, 144], [31], [87, 114], [4], [1]]]
 h' := ![![[2, 148], [109, 25], [48, 7], [10, 68], [23, 39], [82, 66], [89, 2], [0, 1]], ![[0, 1], [10, 124], [62, 142], [146, 81], [101, 110], [65, 83], [93, 147], [2, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [125, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [60, 147, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5142, 4914, -6899]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![197, 496, -6899]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-71, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-71, 1, 0]] 
 ![![149, 0, 0], ![78, 1, 0], ![15, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-71, 1, 0], ![2, -72, 7], ![37, -30, -70]]]
  hmulB := by decide  
  f := ![![![26641, -1326960, 129024], ![-21456, -2746368, 0]], ![![13972, -694581, 67536], ![-11174, -1437552, 0]], ![![2712, -133587, 12989], ![-2097, -276480, 0]]]
  g := ![![![1, 0, 0], ![-78, 149, 0], ![-15, 0, 149]], ![![-1, 1, 0], ![37, -72, 7], ![23, -30, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![5, 10, 1]] ![![149, 0, 0], ![-71, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10579, 149, 0]], ![![745, 1490, 149], ![-298, -745, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-71, 1, 0]]], ![![![5, 10, 1]], ![![-2, -5, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1016960976, -1123151, -33815118]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-1016960976, -1123151, -33815118]] 
 ![![151, 0, 0], ![0, 151, 0], ![33, 62, 1]] where
  M :=![![![-1016960976, -1123151, -33815118], ![-1253405668, -1384285, -41677175], ![-109186823, -120588, -3630587]]]
  hmulB := by decide  
  f := ![![![355, -197, -1045]], ![![-39059, 31902, -2424]], ![![-16022, 13088, -1015]]]
  g := ![![![655218, 13876915, -33815118], ![807557, 17103315, -41677175], ![70348, 1489906, -3630587]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [87, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 150], [0, 1]]
 g := ![![[130, 49], [15, 9], [123, 25], [136], [111, 100], [74], [1]], ![[110, 102], [150, 142], [45, 126], [136], [101, 51], [74], [1]]]
 h' := ![![[15, 150], [54, 144], [20, 148], [146, 146], [7, 102], [74, 10], [64, 15], [0, 1]], ![[0, 1], [100, 7], [126, 3], [71, 5], [27, 49], [73, 141], [138, 136], [15, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [43]]
 b := ![[], [103, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [87, 136, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![45225, 63485, -1189594]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![260277, 488863, -1189594]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-355, 197, 1045]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-355, 197, 1045]] 
 ![![151, 0, 0], ![18, 1, 0], ![86, 0, 1]] where
  M :=![![![-355, 197, 1045], ![39059, -31902, 2424], ![9379, -4865, -31508]]]
  hmulB := by decide  
  f := ![![![1016960976, 1123151, 33815118]], ![![129527836, 143053, 4306949]], ![![579919409, 640474, 19282985]]]
  g := ![![![-621, 197, 1045], ![2681, -31902, 2424], ![18587, -4865, -31508]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-1016960976, -1123151, -33815118]] ![![-355, 197, 1045]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![58, 5, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![58, 5, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![58, 5, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![58, 5, 1], ![47, 23, 36], ![187, -149, 33]]]
  hmulB := by decide  
  f := ![![![-57, -5, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -5, 157]], ![![0, 0, 1], ![-13, -1, 36], ![-11, -2, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [63, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 156], [0, 1]]
 g := ![![[93, 93], [120], [102, 13], [43, 75], [14, 64], [145], [1]], ![[153, 64], [120], [80, 144], [61, 82], [111, 93], [145], [1]]]
 h' := ![![[107, 156], [97, 90], [11, 77], [117, 22], [60, 46], [15, 149], [94, 107], [0, 1]], ![[0, 1], [150, 67], [86, 80], [116, 135], [115, 111], [101, 8], [82, 50], [107, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [156, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [63, 50, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4810, 4788, -10472]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3838, 364, -10472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-36, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-36, 1, 0]] 
 ![![157, 0, 0], ![121, 1, 0], ![124, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-36, 1, 0], ![2, -37, 7], ![37, -30, -35]]]
  hmulB := by decide  
  f := ![![![1637, -32261, 6104], ![-471, -136904, 0]], ![![1273, -24862, 4704], ![-313, -105504, 0]], ![![1292, -25480, 4821], ![-376, -108128, 0]]]
  g := ![![![1, 0, 0], ![-121, 157, 0], ![-124, 0, 157]], ![![-1, 1, 0], ![23, -37, 7], ![51, -30, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![58, 5, 1]] ![![157, 0, 0], ![-36, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-5652, 157, 0]], ![![9106, 785, 157], ![-2041, -157, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-36, 1, 0]]], ![![![58, 5, 1]], ![![-13, -1, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-47971, 42639, -42673]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-47971, 42639, -42673]] 
 ![![163, 0, 0], ![0, 163, 0], ![122, 77, 1]] where
  M :=![![![-47971, 42639, -42673], ![-1493623, 1189580, 255800], ![1492297, -1321843, 1274858]]]
  hmulB := by decide  
  f := ![![![11378362080, 12566479, 378343580]], ![![14023845418, 15488201, 466308933]], ![![15148576183, 16730375, 503707520]]]
  g := ![![![31645, 20420, -42673], ![-200621, -113540, 255800], ![-945033, -610343, 1274858]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [8, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [132, 162], [0, 1]]
 g := ![![[65, 62], [25, 10], [155], [64], [145], [45, 146], [1]], ![[99, 101], [41, 153], [155], [64], [145], [83, 17], [1]]]
 h' := ![![[132, 162], [126, 15], [113, 70], [156, 36], [159, 155], [129, 109], [155, 132], [0, 1]], ![[0, 1], [150, 148], [62, 93], [18, 127], [81, 8], [10, 54], [138, 31], [132, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [147, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [8, 31, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![48, 49, -1659]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1242, 784, -1659]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11378362080, -12566479, -378343580]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-11378362080, -12566479, -378343580]] 
 ![![163, 0, 0], ![112, 1, 0], ![157, 0, 1]] where
  M :=![![![-11378362080, -12566479, -378343580], ![-14023845418, -15488201, -466308933], ![-1221646883, -1349210, -40621159]]]
  hmulB := by decide  
  f := ![![![47971, -42639, 42673]], ![![42125, -36596, 27752]], ![![37050, -32960, 33281]]]
  g := ![![![303245556, -12566479, -378343580], ![373750525, -15488201, -466308933], ![32558200, -1349210, -40621159]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-47971, 42639, -42673]] ![![-11378362080, -12566479, -378343580]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [143, 61, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 92, 106], [68, 74, 61], [0, 1]]
 g := ![![[63, 61, 124], [2, 9, 89], [64, 85, 97], [165, 63], [45, 128], [23, 77, 1], []], ![[53, 87, 128, 142], [140, 44, 2, 159], [86, 102, 25, 53], [154, 32], [66, 84], [10, 16, 112, 131], [77, 47]], ![[47, 99, 163, 144], [148, 49, 32, 7], [46, 5, 49, 9], [157, 9], [53, 61], [126, 55, 130, 107], [122, 47]]]
 h' := ![![[9, 92, 106], [48, 14, 25], [33, 141, 16], [1, 58, 40], [7, 126, 49], [51, 111, 104], [0, 0, 1], [0, 1]], ![[68, 74, 61], [136, 56, 161], [102, 66, 98], [28, 125, 90], [138, 19, 115], [97, 137, 90], [92, 91, 74], [9, 92, 106]], ![[0, 1], [88, 97, 148], [26, 127, 53], [81, 151, 37], [34, 22, 3], [91, 86, 140], [37, 76, 92], [68, 74, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 147], []]
 b := ![[], [73, 149, 38], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [143, 61, 90, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3327141, 2877744, -1283228]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19923, 17232, -7684]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36269, 40, 1206]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![36269, 40, 1206]] 
 ![![173, 0, 0], ![0, 173, 0], ![116, 165, 1]] where
  M :=![![![36269, 40, 1206], ![44702, 49, 1486], ![3892, 6, 129]]]
  hmulB := by decide  
  f := ![![![-15, 12, 2]], ![![98, -87, 86]], ![![86, -77, 83]]]
  g := ![![![-599, -1150, 1206], ![-738, -1417, 1486], ![-64, -123, 129]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [51, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 172], [0, 1]]
 g := ![![[118, 95], [126], [110, 83], [92, 142], [90], [169, 158], [1]], ![[0, 78], [126], [67, 90], [156, 31], [90], [133, 15], [1]]]
 h' := ![![[37, 172], [88, 21], [99, 105], [152, 157], [4, 90], [31, 104], [122, 37], [0, 1]], ![[0, 1], [0, 152], [5, 68], [79, 16], [47, 83], [73, 69], [107, 136], [37, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143]]
 b := ![[], [18, 158]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [51, 136, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3076, 3004, -4268]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2844, 4088, -4268]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, -12, -2]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![15, -12, -2]] 
 ![![173, 0, 0], ![55, 1, 0], ![95, 0, 1]] where
  M :=![![![15, -12, -2], ![-98, 87, -86], ![-448, 358, 63]]]
  hmulB := by decide  
  f := ![![![-36269, -40, -1206]], ![![-11789, -13, -392]], ![![-19939, -22, -663]]]
  g := ![![![5, -12, -2], ![19, 87, -86], ![-151, 358, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![36269, 40, 1206]] ![![15, -12, -2]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [152, 11, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 164, 55], [100, 14, 124], [0, 1]]
 g := ![![[138, 127, 141], [118, 162, 93], [58, 3], [16, 16], [22, 13, 68], [3, 67, 1], []], ![[39, 141, 127, 162], [82, 2, 162, 96], [19, 51], [33, 146], [164, 70, 60, 162], [84, 113, 97, 40], [8, 161]], ![[166, 156, 55, 88], [72, 129, 134, 87], [18, 149], [49, 168], [84, 159, 175, 60], [27, 11, 175, 155], [118, 161]]]
 h' := ![![[146, 164, 55], [143, 94, 118], [132, 43, 123], [101, 65, 160], [57, 47, 4], [81, 165, 28], [0, 0, 1], [0, 1]], ![[100, 14, 124], [134, 64, 20], [97, 45, 149], [11, 71, 87], [146, 64, 135], [30, 44, 159], [52, 58, 14], [146, 164, 55]], ![[0, 1], [136, 21, 41], [95, 91, 86], [44, 43, 111], [42, 68, 40], [44, 149, 171], [119, 121, 164], [100, 14, 124]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 15], []]
 b := ![[], [139, 67, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [152, 11, 112, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![509613, -565282, 1764224]
  a := ![4, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2847, -3158, 9856]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![57, 77, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![57, 77, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![57, 77, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![57, 77, 1], ![191, -50, 540], ![2851, -2309, 104]]]
  hmulB := by decide  
  f := ![![![-56, -77, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -77, 181]], ![![0, 0, 1], ![-169, -230, 540], ![-17, -57, 104]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [81, 84, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 180], [0, 1]]
 g := ![![[115, 38], [14], [115, 178], [170], [112, 42], [104, 178], [1]], ![[0, 143], [14], [5, 3], [170], [23, 139], [175, 3], [1]]]
 h' := ![![[97, 180], [130, 161], [97, 75], [108, 84], [159, 52], [83, 59], [100, 97], [0, 1]], ![[0, 1], [0, 20], [132, 106], [111, 97], [135, 129], [14, 122], [97, 84], [97, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [70, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [81, 84, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![136, 225, -7860]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2476, 3345, -7860]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![3, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![3, 1, 0]] 
 ![![181, 0, 0], ![3, 1, 0], ![77, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![3, 1, 0], ![2, 2, 7], ![37, -30, 4]]]
  hmulB := by decide  
  f := ![![![11127, 11130, 38962], ![362, -1007446, 0]], ![![181, 183, 644], ![182, -16652, 0]], ![![4734, 4735, 16575], ![129, -428582, 0]]]
  g := ![![![1, 0, 0], ![-3, 181, 0], ![-77, 0, 181]], ![![0, 1, 0], ![-3, 2, 7], ![-1, -30, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![57, 77, 1]] ![![181, 0, 0], ![3, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![543, 181, 0]], ![![10317, 13937, 181], ![362, 181, 543]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![3, 1, 0]]], ![![![57, 77, 1]], ![![2, 1, 3]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [60, 163, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 23, 126], [139, 167, 65], [0, 1]]
 g := ![![[178, 112, 125], [88, 165, 172], [175, 84, 162], [45, 126, 32], [116, 158, 156], [178, 155, 1], []], ![[83, 17, 7, 181], [34, 96, 9, 165], [113, 178, 77, 22], [39, 29, 93, 93], [71, 62, 12, 182], [134, 31, 17, 187], [2, 23]], ![[29, 126, 40, 64], [171, 105, 26, 102], [25, 88, 101, 64], [82, 2, 132, 150], [8, 162, 108, 108], [187, 168, 77, 5], [63, 23]]]
 h' := ![![[16, 23, 126], [68, 38, 121], [5, 154, 118], [165, 183, 60], [107, 136, 37], [16, 77, 164], [0, 0, 1], [0, 1]], ![[139, 167, 65], [133, 14, 165], [181, 53, 146], [175, 62, 35], [57, 90, 13], [59, 75, 36], [136, 176, 167], [16, 23, 126]], ![[0, 1], [68, 139, 96], [66, 175, 118], [6, 137, 96], [18, 156, 141], [43, 39, 182], [70, 15, 23], [139, 167, 65]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52, 146], []]
 b := ![[], [8, 10, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [60, 163, 36, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14230646, -11994036, 5144012]
  a := ![6, -12, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![74506, -62796, 26932]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![84, 76, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![84, 76, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![84, 76, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![84, 76, 1], ![189, -22, 533], ![2814, -2279, 130]]]
  hmulB := by decide  
  f := ![![![-83, -76, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -76, 193]], ![![0, 0, 1], ![-231, -210, 533], ![-42, -63, 130]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [115, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [76, 192], [0, 1]]
 g := ![![[95, 161], [64], [129], [134], [24], [43], [76, 1]], ![[172, 32], [64], [129], [134], [24], [43], [152, 192]]]
 h' := ![![[76, 192], [10, 136], [187, 8], [57, 124], [42, 110], [10, 88], [138, 64], [0, 1]], ![[0, 1], [117, 57], [23, 185], [24, 69], [103, 83], [136, 105], [177, 129], [76, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [43, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [115, 117, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-473, 7338, -56874]
  a := ![15, -2, 46]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![24751, 22434, -56874]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![46, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![46, 1, 0]] 
 ![![193, 0, 0], ![46, 1, 0], ![63, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![46, 1, 0], ![2, 45, 7], ![37, -30, 47]]]
  hmulB := by decide  
  f := ![![![4959, 121895, 18963], ![1930, -522837, 0]], ![![1152, 29022, 4515], ![580, -124485, 0]], ![![1593, 39789, 6190], ![738, -170667, 0]]]
  g := ![![![1, 0, 0], ![-46, 193, 0], ![-63, 0, 193]], ![![0, 1, 0], ![-13, 45, 7], ![-8, -30, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![84, 76, 1]] ![![193, 0, 0], ![46, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![8878, 193, 0]], ![![16212, 14668, 193], ![4053, 3474, 579]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![46, 1, 0]]], ![![![84, 76, 1]], ![![21, 18, 3]]]]
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


lemma PB247I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB247I3 : PrimesBelowBoundCertificateInterval O 137 193 247 where
  m := 11
  g := ![2, 2, 2, 2, 2, 1, 2, 1, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB247I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![6967871]
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
      exact NI149N1
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
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
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
      exact NI193N1
  β := ![I139N1, I149N1, I151N1, I157N1, I163N1, I173N1, I181N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N1], [], [I173N1], [], [I181N1], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
