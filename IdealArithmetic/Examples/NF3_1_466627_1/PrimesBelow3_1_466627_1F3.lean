
import IdealArithmetic.Examples.NF3_1_466627_1.RI3_1_466627_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-104, -21, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-104, -21, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![35, 118, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-104, -21, 1], ![412, 3, -20], ![-8240, -1728, -17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -118, 139]], ![![-1, -1, 1], ![8, 17, -20], ![-55, 2, -17]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [49, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 138], [0, 1]]
 g := ![![[8, 122], [118, 9], [124], [122, 86], [66], [69], [1]], ![[0, 17], [65, 130], [124], [48, 53], [66], [69], [1]]]
 h' := ![![[25, 138], [56, 20], [41, 136], [138, 92], [12, 124], [132, 109], [90, 25], [0, 1]], ![[0, 1], [0, 119], [105, 3], [75, 47], [54, 15], [77, 30], [20, 114], [25, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [60, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [49, 114, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1285, 619, -3]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 7, -3]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![20, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![20, 1, 0]] 
 ![![139, 0, 0], ![20, 1, 0], ![17, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![20, 1, 0], ![0, 20, 1], ![412, 107, 21]]]
  hmulB := by decide  
  f := ![![![101, 5, 0], ![-695, 0, 0]], ![![-20, -1, 0], ![140, 0, 0]], ![![-17, -1, 0], ![119, 1, 0]]]
  g := ![![![1, 0, 0], ![-20, 139, 0], ![-17, 0, 139]], ![![0, 1, 0], ![-3, 20, 1], ![-15, 107, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-104, -21, 1]] ![![139, 0, 0], ![20, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2780, 139, 0]], ![![-14456, -2919, 139], ![-1668, -417, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![20, 1, 0]]], ![![![-104, -21, 1]], ![![-12, -3, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-70, -75, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-70, -75, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![79, 74, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-70, -75, 1], ![412, 37, -74], ![-30488, -7506, -37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -74, 149]], ![![-1, -1, 1], ![42, 37, -74], ![-185, -32, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [66, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 148], [0, 1]]
 g := ![![[36, 67], [31], [82, 114], [125], [47, 22], [64], [1]], ![[125, 82], [31], [100, 35], [125], [74, 127], [64], [1]]]
 h' := ![![[8, 148], [109, 118], [101, 110], [78, 73], [27, 107], [132, 52], [83, 8], [0, 1]], ![[0, 1], [10, 31], [87, 39], [66, 76], [138, 42], [101, 97], [147, 141], [8, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [143, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [66, 141, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1310, 3109, 1381]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-741, -665, 1381]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![74, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![74, 1, 0]] 
 ![![149, 0, 0], ![74, 1, 0], ![37, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![74, 1, 0], ![0, 74, 1], ![412, 107, 75]]]
  hmulB := by decide  
  f := ![![![2295, 31, 0], ![-4619, 0, 0]], ![![1110, 15, 0], ![-2234, 0, 0]], ![![555, 7, 0], ![-1117, 1, 0]]]
  g := ![![![1, 0, 0], ![-74, 149, 0], ![-37, 0, 149]], ![![0, 1, 0], ![-37, 74, 1], ![-69, 107, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-70, -75, 1]] ![![149, 0, 0], ![74, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![11026, 149, 0]], ![![-10430, -11175, 149], ![-4768, -5513, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![74, 1, 0]]], ![![![-70, -75, 1]], ![![-32, -37, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-8, 23, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-8, 23, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![143, 23, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-8, 23, 1], ![412, 99, 24], ![9888, 2980, 123]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-143, -23, 151]], ![![-1, 0, 1], ![-20, -3, 24], ![-51, 1, 123]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [3, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 150], [0, 1]]
 g := ![![[81, 100], [127, 68], [47, 62], [116], [9, 32], [8], [1]], ![[92, 51], [62, 83], [81, 89], [116], [85, 119], [8], [1]]]
 h' := ![![[59, 150], [72, 141], [10, 70], [79, 45], [124, 56], [136, 118], [148, 59], [0, 1]], ![[0, 1], [86, 10], [63, 81], [16, 106], [106, 95], [1, 33], [5, 92], [59, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [23, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [3, 92, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2201, 269, 143]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-150, -20, 143]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-24, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-24, 1, 0]] 
 ![![151, 0, 0], ![127, 1, 0], ![28, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-24, 1, 0], ![0, -24, 1], ![412, 107, -23]]]
  hmulB := by decide  
  f := ![![![2809, -117, 0], ![17667, 0, 0]], ![![2401, -100, 0], ![15101, 0, 0]], ![![532, -22, 0], ![3346, 1, 0]]]
  g := ![![![1, 0, 0], ![-127, 151, 0], ![-28, 0, 151]], ![![-1, 1, 0], ![20, -24, 1], ![-83, 107, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-8, 23, 1]] ![![151, 0, 0], ![-24, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-3624, 151, 0]], ![![-1208, 3473, 151], ![604, -453, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-24, 1, 0]]], ![![![-8, 23, 1]], ![![4, -3, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-20, -53, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-20, -53, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![137, 104, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-20, -53, 1], ![412, 87, -52], ![-21424, -5152, 35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-137, -104, 157]], ![![-1, -1, 1], ![48, 35, -52], ![-167, -56, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [151, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 156], [0, 1]]
 g := ![![[50, 46], [48], [32, 14], [42, 42], [108, 17], [39], [1]], ![[34, 111], [48], [150, 143], [82, 115], [27, 140], [39], [1]]]
 h' := ![![[143, 156], [100, 49], [35, 26], [95, 64], [20, 55], [113, 71], [6, 143], [0, 1]], ![[0, 1], [42, 108], [142, 131], [141, 93], [35, 102], [61, 86], [45, 14], [143, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [87, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [151, 14, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1402, 4045, 919]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-793, -583, 919]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![52, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![52, 1, 0]] 
 ![![157, 0, 0], ![52, 1, 0], ![122, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![52, 1, 0], ![0, 52, 1], ![412, 107, 53]]]
  hmulB := by decide  
  f := ![![![3225, 62, 0], ![-9734, 0, 0]], ![![1092, 21, 0], ![-3296, 0, 0]], ![![2514, 48, 0], ![-7588, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 157, 0], ![-122, 0, 157]], ![![0, 1, 0], ![-18, 52, 1], ![-74, 107, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-20, -53, 1]] ![![157, 0, 0], ![52, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![8164, 157, 0]], ![![-3140, -8321, 157], ![-628, -2669, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![52, 1, 0]]], ![![![-20, -53, 1]], ![![-4, -17, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![8, -31, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![8, -31, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![8, 132, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![8, -31, 1], ![412, 115, -30], ![-12360, -2798, 85]]]
  hmulB := by decide  
  f := ![![![-7, 31, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -132, 163]], ![![0, -1, 1], ![4, 25, -30], ![-80, -86, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [157, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 162], [0, 1]]
 g := ![![[109, 97], [10, 61], [69], [84], [54], [32, 4], [1]], ![[140, 66], [132, 102], [69], [84], [54], [40, 159], [1]]]
 h' := ![![[2, 162], [60, 74], [60, 86], [102, 118], [24, 128], [29, 124], [6, 2], [0, 1]], ![[0, 1], [45, 89], [69, 77], [12, 45], [117, 35], [114, 39], [10, 161], [2, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [93]]
 b := ![[], [35, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [157, 161, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1393, 572, -50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 44, -50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![30, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![30, 1, 0]] 
 ![![163, 0, 0], ![30, 1, 0], ![78, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![30, 1, 0], ![0, 30, 1], ![412, 107, 31]]]
  hmulB := by decide  
  f := ![![![2671, 89, 0], ![-14507, 0, 0]], ![![450, 15, 0], ![-2444, 0, 0]], ![![1266, 42, 0], ![-6876, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 163, 0], ![-78, 0, 163]], ![![0, 1, 0], ![-6, 30, 1], ![-32, 107, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![8, -31, 1]] ![![163, 0, 0], ![30, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![4890, 163, 0]], ![![1304, -5053, 163], ![652, -815, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![30, 1, 0]]], ![![![8, -31, 1]], ![![4, -5, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-138, 42, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-138, 42, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![29, 42, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-138, 42, 1], ![412, -31, 43], ![17716, 5013, 12]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -42, 167]], ![![-1, 0, 1], ![-5, -11, 43], ![104, 27, 12]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [99, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 166], [0, 1]]
 g := ![![[146, 27], [65, 115], [108, 99], [122], [18], [46, 114], [1]], ![[0, 140], [6, 52], [18, 68], [122], [18], [79, 53], [1]]]
 h' := ![![[75, 166], [78, 19], [163, 68], [44, 44], [76, 17], [122, 128], [68, 75], [0, 1]], ![[0, 1], [0, 148], [86, 99], [4, 123], [15, 150], [36, 39], [15, 92], [75, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [101, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [99, 92, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16260, 6371, 601]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -113, 601]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-43, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-43, 1, 0]] 
 ![![167, 0, 0], ![124, 1, 0], ![155, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-43, 1, 0], ![0, -43, 1], ![412, 107, -42]]]
  hmulB := by decide  
  f := ![![![5204, -121, 0], ![20207, 0, 0]], ![![3914, -91, 0], ![15198, 0, 0]], ![![4828, -112, 0], ![18747, 1, 0]]]
  g := ![![![1, 0, 0], ![-124, 167, 0], ![-155, 0, 167]], ![![-1, 1, 0], ![31, -43, 1], ![-38, 107, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-138, 42, 1]] ![![167, 0, 0], ![-43, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-7181, 167, 0]], ![![-23046, 7014, 167], ![6346, -1837, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-43, 1, 0]]], ![![![-138, 42, 1]], ![![38, -11, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-107, 0, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-107, 0, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![66, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-107, 0, 1], ![412, 0, 1], ![412, 519, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, 0, 173]], ![![-1, 0, 1], ![2, 0, 1], ![2, 3, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [148, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [130, 172], [0, 1]]
 g := ![![[109, 83], [158], [154, 89], [68, 33], [100], [172, 119], [1]], ![[0, 90], [158], [133, 84], [33, 140], [100], [72, 54], [1]]]
 h' := ![![[130, 172], [4, 157], [44, 136], [143, 98], [11, 44], [148, 10], [25, 130], [0, 1]], ![[0, 1], [0, 16], [78, 37], [81, 75], [22, 129], [64, 163], [144, 43], [130, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [63, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [148, 43, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1954, 0, 70]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-38, 0, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-1, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-1, 1, 0]] 
 ![![173, 0, 0], ![172, 1, 0], ![172, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-1, 1, 0], ![0, -1, 1], ![412, 107, 0]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![519, 0, 0]], ![![2, -1, 0], ![174, 0, 0]], ![![2, -1, 0], ![174, 1, 0]]]
  g := ![![![1, 0, 0], ![-172, 173, 0], ![-172, 0, 173]], ![![-1, 1, 0], ![0, -1, 1], ![-104, 107, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-107, 0, 1]] ![![173, 0, 0], ![-1, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-173, 173, 0]], ![![-18511, 0, 173], ![519, 0, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-1, 1, 0]]], ![![![-107, 0, 1]], ![![3, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-1, -55, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-1, -55, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![178, 124, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-1, -55, 1], ![412, 106, -54], ![-22248, -5366, 52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-178, -124, 179]], ![![-1, -1, 1], ![56, 38, -54], ![-176, -66, 52]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [72, 156, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 178], [0, 1]]
 g := ![![[32, 17], [80, 124], [64], [144], [16, 25], [84, 171], [1]], ![[65, 162], [68, 55], [64], [144], [54, 154], [79, 8], [1]]]
 h' := ![![[23, 178], [147, 14], [11, 53], [12, 8], [101, 12], [38, 174], [107, 23], [0, 1]], ![[0, 1], [111, 165], [156, 126], [17, 171], [19, 167], [102, 5], [99, 156], [23, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [75]]
 b := ![[], [61, 127]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [72, 156, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3368, 2660, 749]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-726, -504, 749]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![54, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![54, 1, 0]] 
 ![![179, 0, 0], ![54, 1, 0], ![127, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![54, 1, 0], ![0, 54, 1], ![412, 107, 55]]]
  hmulB := by decide  
  f := ![![![2647, 49, 0], ![-8771, 0, 0]], ![![810, 15, 0], ![-2684, 0, 0]], ![![1907, 35, 0], ![-6319, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 179, 0], ![-127, 0, 179]], ![![0, 1, 0], ![-17, 54, 1], ![-69, 107, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-1, -55, 1]] ![![179, 0, 0], ![54, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![9666, 179, 0]], ![![-179, -9845, 179], ![358, -2864, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![54, 1, 0]]], ![![![-1, -55, 1]], ![![2, -16, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [122, 79, 117, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 151, 115], [69, 29, 66], [0, 1]]
 g := ![![[49, 166, 142], [61, 37], [12, 161, 132], [64, 154], [84, 98, 135], [35, 64, 1], []], ![[39, 86, 62, 149], [70, 59], [75, 158, 137, 66], [111, 125], [137, 132, 17, 171], [120, 170, 13, 61], [22, 12]], ![[141, 36, 13, 118], [15, 111], [19, 10, 18, 158], [70, 82], [115, 23, 26, 134], [18, 177, 44, 32], [71, 12]]]
 h' := ![![[176, 151, 115], [54, 98, 93], [165, 39, 47], [30, 40, 48], [69, 97, 110], [74, 106, 139], [0, 0, 1], [0, 1]], ![[69, 29, 66], [66, 122, 30], [68, 177, 56], [165, 141, 19], [133, 50, 46], [88, 149, 112], [56, 175, 29], [176, 151, 115]], ![[0, 1], [50, 142, 58], [147, 146, 78], [162, 0, 114], [106, 34, 25], [4, 107, 111], [81, 6, 151], [69, 29, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 56], []]
 b := ![[], [59, 128, 127], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [122, 79, 117, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5261308, -615762, 150954]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29068, -3402, 834]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [64, 169, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 44, 83], [158, 146, 108], [0, 1]]
 g := ![![[97, 39, 85], [186, 70, 135], [174, 63, 149], [80, 33, 34], [141, 31, 17], [46, 62, 1], []], ![[121, 99, 160, 76], [82, 23, 170, 57], [159, 39, 53, 35], [84, 51, 32, 22], [55, 76, 79, 186], [54, 134, 62, 186], [88, 13]], ![[40, 162, 56, 9], [119, 187, 78, 153], [13, 125, 68, 177], [105, 173, 125, 15], [31, 91, 74, 26], [63, 119, 126, 134], [63, 13]]]
 h' := ![![[95, 44, 83], [129, 111, 127], [133, 19, 53], [37, 138, 128], [144, 101, 176], [112, 100, 141], [0, 0, 1], [0, 1]], ![[158, 146, 108], [184, 74, 60], [126, 98, 147], [129, 30, 155], [100, 4, 81], [20, 105, 45], [146, 105, 146], [95, 44, 83]], ![[0, 1], [121, 6, 4], [147, 74, 182], [15, 23, 99], [82, 86, 125], [139, 177, 5], [113, 86, 44], [158, 146, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 122], []]
 b := ![[], [172, 15, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [64, 169, 129, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![82703, 124341, 33043]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![433, 651, 173]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-151, 18, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-151, 18, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![42, 18, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-151, 18, 1], ![412, -44, 19], ![7828, 2445, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -18, 193]], ![![-1, 0, 1], ![-2, -2, 19], ![46, 15, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [17, 166, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [27, 192], [0, 1]]
 g := ![![[146, 192], [108], [130], [172], [9], [126], [27, 1]], ![[119, 1], [108], [130], [172], [9], [126], [54, 192]]]
 h' := ![![[27, 192], [38, 81], [152, 84], [168, 138], [191, 65], [99, 3], [120, 133], [0, 1]], ![[0, 1], [102, 112], [104, 109], [34, 55], [16, 128], [180, 190], [44, 60], [27, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [78, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [17, 166, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3892, 703, -36]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![28, 7, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-19, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-19, 1, 0]] 
 ![![193, 0, 0], ![174, 1, 0], ![25, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-19, 1, 0], ![0, -19, 1], ![412, 107, -18]]]
  hmulB := by decide  
  f := ![![![1350, -71, 0], ![13703, 0, 0]], ![![1198, -63, 0], ![12160, 0, 0]], ![![192, -10, 0], ![1949, 1, 0]]]
  g := ![![![1, 0, 0], ![-174, 193, 0], ![-25, 0, 193]], ![![-1, 1, 0], ![17, -19, 1], ![-92, 107, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-151, 18, 1]] ![![193, 0, 0], ![-19, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-3667, 193, 0]], ![![-29143, 3474, 193], ![3281, -386, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-19, 1, 0]]], ![![![-151, 18, 1]], ![![17, -2, 0]]]]
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


lemma PB194I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB194I3 : PrimesBelowBoundCertificateInterval O 137 193 194 where
  m := 11
  g := ![2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB194I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N1, I157N1, I163N1, I167N1, I173N1, I179N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
