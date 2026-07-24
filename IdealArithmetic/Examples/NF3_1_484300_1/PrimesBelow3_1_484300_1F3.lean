
import IdealArithmetic.Examples.NF3_1_484300_1.RI3_1_484300_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-19, -15, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-19, -15, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![120, 124, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-19, -15, 1], ![-137, -35, -44], ![1784, 194, -50]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -124, 139]], ![![-1, -1, 1], ![37, 39, -44], ![56, 46, -50]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [1, 101, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 138], [0, 1]]
 g := ![![[101, 1], [38, 99], [45], [52, 112], [66], [54], [1]], ![[0, 138], [47, 40], [45], [138, 27], [66], [54], [1]]]
 h' := ![![[38, 138], [101, 1], [18, 51], [87, 36], [102, 23], [86, 30], [138, 38], [0, 1]], ![[0, 1], [0, 138], [10, 88], [65, 103], [3, 116], [114, 109], [53, 101], [38, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [23, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [1, 101, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1244, -609, -432]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![364, 381, -432]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![44, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![44, 1, 0]] 
 ![![139, 0, 0], ![44, 1, 0], ![50, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![44, 1, 0], ![1, 44, 3], ![-122, -16, 45]]]
  hmulB := by decide  
  f := ![![![-271, -13903, -948], ![-139, 43924, 0]], ![![-100, -4400, -300], ![1, 13900, 0]], ![![-94, -5001, -341], ![-61, 15800, 0]]]
  g := ![![![1, 0, 0], ![-44, 139, 0], ![-50, 0, 139]], ![![0, 1, 0], ![-15, 44, 3], ![-12, -16, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-19, -15, 1]] ![![139, 0, 0], ![44, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![6116, 139, 0]], ![![-2641, -2085, 139], ![-973, -695, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![44, 1, 0]]], ![![![-19, -15, 1]], ![![-7, -5, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![51, -8, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![51, -8, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![51, 141, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![51, -8, 1], ![-130, 35, -23], ![930, 82, 27]]]
  hmulB := by decide  
  f := ![![![-50, 8, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -141, 149]], ![![0, -1, 1], ![7, 22, -23], ![-3, -25, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [109, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 148], [0, 1]]
 g := ![![[37, 53], [63], [101, 6], [33], [48, 144], [100], [1]], ![[103, 96], [63], [41, 143], [33], [98, 5], [100], [1]]]
 h' := ![![[139, 148], [127, 65], [17, 130], [119, 119], [132, 35], [87, 137], [40, 139], [0, 1]], ![[0, 1], [73, 84], [58, 19], [121, 30], [80, 114], [58, 12], [140, 10], [139, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [63, 102]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [109, 10, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1299, -1834, -702]
  a := ![2, -2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![249, 652, -702]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![23, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![23, 1, 0]] 
 ![![149, 0, 0], ![23, 1, 0], ![122, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![23, 1, 0], ![1, 23, 3], ![-122, -16, 24]]]
  hmulB := by decide  
  f := ![![![173, 4484, 585], ![149, -29055, 0]], ![![7, 689, 90], ![150, -4470, 0]], ![![131, 3671, 479], ![191, -23790, 0]]]
  g := ![![![1, 0, 0], ![-23, 149, 0], ![-122, 0, 149]], ![![0, 1, 0], ![-6, 23, 3], ![-18, -16, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![51, -8, 1]] ![![149, 0, 0], ![23, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![3427, 149, 0]], ![![7599, -1192, 149], ![1043, -149, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![23, 1, 0]]], ![![![51, -8, 1]], ![![7, -1, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![32, -35, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![32, -35, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![32, 116, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![32, -35, 1], ![-157, 16, -104], ![4224, 514, -19]]]
  hmulB := by decide  
  f := ![![![-31, 35, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -116, 151]], ![![0, -1, 1], ![21, 80, -104], ![32, 18, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [97, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 150], [0, 1]]
 g := ![![[87, 137], [145, 31], [149, 62], [1], [45, 2], [138], [1]], ![[0, 14], [68, 120], [146, 89], [1], [79, 149], [138], [1]]]
 h' := ![![[17, 150], [129, 99], [43, 129], [99, 45], [14, 1], [100, 105], [54, 17], [0, 1]], ![[0, 1], [0, 52], [122, 22], [109, 106], [31, 150], [73, 46], [41, 134], [17, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [131, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [97, 134, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-761829, -785210, -275359]
  a := ![-65, 1, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![53309, 206334, -275359]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-47, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-47, 1, 0]] 
 ![![151, 0, 0], ![104, 1, 0], ![19, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-47, 1, 0], ![1, -47, 3], ![-122, -16, -46]]]
  hmulB := by decide  
  f := ![![![6588, -373621, 23850], ![-4379, -1200450, 0]], ![![4536, -257305, 16425], ![-3019, -826725, 0]], ![![833, -47012, 3001], ![-538, -151050, 0]]]
  g := ![![![1, 0, 0], ![-104, 151, 0], ![-19, 0, 151]], ![![-1, 1, 0], ![32, -47, 3], ![16, -16, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![32, -35, 1]] ![![151, 0, 0], ![-47, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-7097, 151, 0]], ![![4832, -5285, 151], ![-1661, 1661, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-47, 1, 0]]], ![![![32, -35, 1]], ![![-11, 11, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![17, -75, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![17, -75, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![17, 82, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![17, -75, 1], ![-197, 1, -224], ![9104, 1154, -74]]]
  hmulB := by decide  
  f := ![![![-16, 75, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -82, 157]], ![![0, -1, 1], ![23, 117, -224], ![66, 46, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [156, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 156], [0, 1]]
 g := ![![[84, 156], [156], [155, 40], [147, 3], [153, 30], [148], [1]], ![[0, 1], [156], [61, 117], [85, 154], [4, 127], [148], [1]]]
 h' := ![![[84, 156], [3, 28], [155, 129], [147, 121], [153, 72], [149, 40], [1, 84], [0, 1]], ![[0, 1], [0, 129], [1, 28], [106, 36], [78, 85], [55, 117], [149, 73], [84, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [46, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [156, 73, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-531, -1961, -1278]
  a := ![-2, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![135, 655, -1278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![67, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![67, 1, 0]] 
 ![![157, 0, 0], ![67, 1, 0], ![74, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![67, 1, 0], ![1, 67, 3], ![-122, -16, 68]]]
  hmulB := by decide  
  f := ![![![-3084, -296455, -13275], ![-3140, 694725, 0]], ![![-1352, -126488, -5664], ![-1255, 296416, 0]], ![![-1495, -139731, -6257], ![-1383, 327450, 0]]]
  g := ![![![1, 0, 0], ![-67, 157, 0], ![-74, 0, 157]], ![![0, 1, 0], ![-30, 67, 3], ![-26, -16, 68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![17, -75, 1]] ![![157, 0, 0], ![67, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![10519, 157, 0]], ![![2669, -11775, 157], ![942, -5024, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![67, 1, 0]]], ![![![17, -75, 1]], ![![6, -32, -1]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [161, 63, 71, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 77, 52], [85, 85, 111], [0, 1]]
 g := ![![[85, 105, 104], [88, 133, 65], [10, 49], [26, 156], [70, 74], [88, 92, 1], []], ![[136, 141, 85, 137], [141, 142, 88, 139], [11, 60], [14, 71], [91, 43], [101, 80, 98, 148], [51, 96]], ![[100, 100, 69, 6], [53, 1, 103, 145], [71, 135], [161, 136], [97, 57], [133, 39, 25, 88], [155, 96]]]
 h' := ![![[7, 77, 52], [13, 142, 105], [82, 95, 37], [15, 135, 156], [146, 144, 51], [13, 19, 20], [0, 0, 1], [0, 1]], ![[85, 85, 111], [73, 74, 9], [140, 135, 98], [66, 35, 68], [53, 15, 87], [69, 93, 80], [151, 13, 85], [7, 77, 52]], ![[0, 1], [157, 110, 49], [72, 96, 28], [147, 156, 102], [92, 4, 25], [86, 51, 63], [37, 150, 77], [85, 85, 111]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 115], []]
 b := ![[], [26, 112, 26], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [161, 63, 71, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-298942, -78729, -8802]
  a := ![-1, -1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1834, -483, -54]
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


def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![6, 1, 0]] 
 ![![167, 0, 0], ![6, 1, 0], ![44, 0, 1]] where
  M :=![![![6, 1, 0], ![1, 6, 3], ![-122, -16, 7]]]
  hmulB := by decide  
  f := ![![![90, -7, 3]], ![![1, 0, 0]], ![![28, -2, 1]]]
  g := ![![![0, 1, 0], ![-1, 6, 3], ![-2, -16, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 6, -3]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-77, 6, -3]] 
 ![![167, 0, 0], ![154, 1, 0], ![111, 0, 1]] where
  M :=![![![-77, 6, -3], ![372, -29, 15], ![-594, 42, -23]]]
  hmulB := by decide  
  f := ![![![-37, -12, -3]], ![![-32, -11, -3]], ![![-15, -6, -2]]]
  g := ![![![-4, 6, -3], ![19, -29, 15], ![-27, 42, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![6, 1, 0]] ![![6, 1, 0]]
  ![![37, 12, 3]] where
 M := ![![![37, 12, 3]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI167N1 : IdealMulLeCertificate' Table 
  ![![37, 12, 3]] ![![-77, 6, -3]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [67, 163, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 66, 132], [114, 106, 41], [0, 1]]
 g := ![![[107, 116, 137], [65, 109], [26, 109, 130], [135, 17, 31], [2, 159], [70, 38, 1], []], ![[125, 47, 28, 157], [37, 4], [135, 91, 135, 92], [171, 58, 54, 83], [23, 116], [152, 49, 91, 23], [165, 124]], ![[131, 103, 87, 25], [89, 78], [157, 163, 168, 90], [107, 29, 27, 96], [56, 152], [139, 89, 69, 60], [83, 124]]]
 h' := ![![[97, 66, 132], [114, 90, 39], [161, 29, 52], [124, 13, 87], [54, 3, 66], [154, 57, 32], [0, 0, 1], [0, 1]], ![[114, 106, 41], [10, 147, 98], [76, 72, 171], [43, 125, 39], [7, 149, 126], [67, 100, 17], [84, 91, 106], [97, 66, 132]], ![[0, 1], [11, 109, 36], [145, 72, 123], [47, 35, 47], [132, 21, 154], [123, 16, 124], [169, 82, 66], [114, 106, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 24], []]
 b := ![[], [122, 152, 47], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [67, 163, 135, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3126802, -1163598, -306210]
  a := ![2, 19, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18074, -6726, -1770]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![15, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![15, 1, 0]] 
 ![![179, 0, 0], ![15, 1, 0], ![164, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![15, 1, 0], ![1, 15, 3], ![-122, -16, 16]]]
  hmulB := by decide  
  f := ![![![706, 10799, 2160], ![179, -128880, 0]], ![![45, 899, 180], ![180, -10740, 0]], ![![646, 9894, 1979], ![174, -118080, 0]]]
  g := ![![![1, 0, 0], ![-15, 179, 0], ![-164, 0, 179]], ![![0, 1, 0], ![-4, 15, 3], ![-14, -16, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![72, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![72, 1, 0]] 
 ![![179, 0, 0], ![72, 1, 0], ![122, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![72, 1, 0], ![1, 72, 3], ![-122, -16, 73]]]
  hmulB := by decide  
  f := ![![![-611, -59613, -2484], ![-537, 148212, 0]], ![![-261, -23975, -999], ![-178, 59607, 0]], ![![-410, -40630, -1693], ![-382, 101016, 0]]]
  g := ![![![1, 0, 0], ![-72, 179, 0], ![-122, 0, 179]], ![![0, 1, 0], ![-31, 72, 3], ![-44, -16, 73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-88, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-88, 1, 0]] 
 ![![179, 0, 0], ![91, 1, 0], ![104, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-88, 1, 0], ![1, -88, 3], ![-122, -16, -87]]]
  hmulB := by decide  
  f := ![![![2769, -390701, 13320], ![-3401, -794760, 0]], ![![1466, -198607, 6771], ![-1610, -404003, 0]], ![![1656, -227000, 7739], ![-1880, -461760, 0]]]
  g := ![![![1, 0, 0], ![-91, 179, 0], ![-104, 0, 179]], ![![-1, 1, 0], ![43, -88, 3], ![58, -16, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![15, 1, 0]] ![![179, 0, 0], ![72, 1, 0]]
  ![![179, 0, 0], ![62, 29, 1]] where
 M := ![![![32041, 0, 0], ![12888, 179, 0]], ![![2685, 179, 0], ![1081, 87, 3]]]
 hmul := by decide  
 g := ![![![![117, -29, -1], ![179, 0, 0]], ![![10, -28, -1], ![179, 0, 0]]], ![![![-47, -28, -1], ![179, 0, 0]], ![![5, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![62, 29, 1]] ![![179, 0, 0], ![-88, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-15752, 179, 0]], ![![11098, 5191, 179], ![-5549, -2506, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-88, 1, 0]]], ![![![62, 29, 1]], ![![-31, -14, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [133, 38, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 36, 110], [50, 144, 71], [0, 1]]
 g := ![![[6, 101, 169], [162, 117], [2, 46, 48], [132, 13], [31, 1, 36], [176, 157, 1], []], ![[90, 67, 140, 149], [38, 52], [151, 37, 47, 107], [178, 156], [159, 79, 33, 92], [18, 11, 97, 179], [61, 154]], ![[2, 45, 14, 164], [35, 13], [94, 153, 33, 112], [31, 82], [13, 122, 23, 118], [47, 8, 145, 68], [100, 154]]]
 h' := ![![[107, 36, 110], [159, 42, 168], [96, 20, 29], [153, 154, 132], [40, 179, 70], [122, 124, 175], [0, 0, 1], [0, 1]], ![[50, 144, 71], [19, 108, 33], [154, 51, 41], [139, 71, 110], [37, 67, 86], [71, 15, 106], [78, 108, 144], [107, 36, 110]], ![[0, 1], [31, 31, 161], [121, 110, 111], [26, 137, 120], [158, 116, 25], [170, 42, 81], [60, 73, 36], [50, 144, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 86], []]
 b := ![[], [161, 138, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [133, 38, 24, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-310415, -131587, -55748]
  a := ![-2, 3, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1715, -727, -308]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![39, 76, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![39, 76, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![39, 76, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![39, 76, 1], ![-46, 23, 229], ![-9318, -1262, 99]]]
  hmulB := by decide  
  f := ![![![-38, -76, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -76, 191]], ![![0, 0, 1], ![-47, -91, 229], ![-69, -46, 99]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [89, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 190], [0, 1]]
 g := ![![[65, 49], [104, 109], [152, 103], [15, 18], [81, 6], [35, 160], [1]], ![[44, 142], [30, 82], [26, 88], [171, 173], [133, 185], [21, 31], [1]]]
 h' := ![![[136, 190], [103, 184], [33, 49], [2, 165], [49, 20], [132, 160], [102, 136], [0, 1]], ![[0, 1], [106, 7], [12, 142], [95, 26], [95, 171], [118, 31], [71, 55], [136, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [11, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [89, 55, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2916, -1789, -207]
  a := ![2, 1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27, 73, -207]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-38, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-38, 1, 0]] 
 ![![191, 0, 0], ![153, 1, 0], ![92, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-38, 1, 0], ![1, -38, 3], ![-122, -16, -37]]]
  hmulB := by decide  
  f := ![![![-161, 7599, -600], ![191, 38200, 0]], ![![-121, 6079, -480], ![192, 30560, 0]], ![![-68, 3660, -289], ![140, 18400, 0]]]
  g := ![![![1, 0, 0], ![-153, 191, 0], ![-92, 0, 191]], ![![-1, 1, 0], ![29, -38, 3], ![30, -16, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![39, 76, 1]] ![![191, 0, 0], ![-38, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-7258, 191, 0]], ![![7449, 14516, 191], ![-1528, -2865, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-38, 1, 0]]], ![![![39, 76, 1]], ![![-8, -15, 1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99289, 7608, -3894]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-99289, 7608, -3894]] 
 ![![193, 0, 0], ![26, 1, 0], ![161, 0, 1]] where
  M :=![![![-99289, 7608, -3894], ![482676, -36985, 18930], ![-749052, 57396, -29377]]]
  hmulB := by decide  
  f := ![![![-2065, -192, 150]], ![![-374, -49, 18]], ![![-1637, -180, 101]]]
  g := ![![![1709, 7608, -3894], ![-8308, -36985, 18930], ![12893, 57396, -29377]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-17, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-17, 1, 0]] 
 ![![193, 0, 0], ![176, 1, 0], ![97, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-17, 1, 0], ![1, -17, 3], ![-122, -16, -16]]]
  hmulB := by decide  
  f := ![![![-1767, 30632, -5406], ![386, 347786, 0]], ![![-1608, 27929, -4929], ![387, 317099, 0]], ![![-882, 15395, -2717], ![263, 174794, 0]]]
  g := ![![![1, 0, 0], ![-176, 193, 0], ![-97, 0, 193]], ![![-1, 1, 0], ![14, -17, 3], ![22, -16, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-10, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-10, 1, 0]] 
 ![![193, 0, 0], ![183, 1, 0], ![160, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-10, 1, 0], ![1, -10, 3], ![-122, -16, -9]]]
  hmulB := by decide  
  f := ![![![-529, 5399, -1620], ![193, 104220, 0]], ![![-501, 5119, -1536], ![194, 98816, 0]], ![![-440, 4476, -1343], ![132, 86400, 0]]]
  g := ![![![1, 0, 0], ![-183, 193, 0], ![-160, 0, 193]], ![![-1, 1, 0], ![7, -10, 3], ![22, -16, -9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-99289, 7608, -3894]] ![![193, 0, 0], ![-17, 1, 0]]
  ![![193, 0, 0], ![46, 3, 1]] where
 M := ![![![-19162777, 1468344, -751542], ![2170589, -166321, 85128]]]
 hmul := by decide  
 g := ![![![![-93999, 7953, -3779], ![-22195, 0, 0]], ![![10599, -904, 427], ![2717, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![46, 3, 1]] ![![193, 0, 0], ![-10, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-1930, 193, 0]], ![![8878, 579, 193], ![-579, 0, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-10, 1, 0]]], ![![![46, 3, 1]], ![![-3, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB197I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 196 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 196 (by omega)

def PB197I3 : PrimesBelowBoundCertificateInterval O 137 196 197 where
  m := 11
  g := ![2, 2, 2, 2, 1, 3, 1, 3, 1, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB197I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![193, 193, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I149N1, I151N1, I157N1, I167N0, I167N1, I179N0, I179N1, I179N2, I191N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [], [I167N0, I167N0, I167N1], [], [I179N0, I179N1, I179N2], [], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
