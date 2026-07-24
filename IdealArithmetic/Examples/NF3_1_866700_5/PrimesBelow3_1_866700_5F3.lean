
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![28, 31, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![28, 31, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![28, 31, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![28, 31, 1], ![-4, 214, 397], ![5474, 14, -152]]]
  hmulB := by decide  
  f := ![![![-27, -31, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-28, -31, 139]], ![![0, 0, 1], ![-80, -87, 397], ![70, 34, -152]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [110, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 138], [0, 1]]
 g := ![![[35, 136], [113, 57], [66], [19, 31], [55], [96], [1]], ![[48, 3], [5, 82], [66], [70, 108], [55], [96], [1]]]
 h' := ![![[42, 138], [80, 54], [132, 14], [134, 109], [48, 46], [11, 74], [29, 42], [0, 1]], ![[0, 1], [124, 85], [25, 125], [125, 30], [34, 93], [61, 65], [125, 97], [42, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [12, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [110, 97, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5166, 1897, -858]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![210, 205, -858]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![20, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![20, 1, 0]] 
 ![![139, 0, 0], ![20, 1, 0], ![13, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![20, 1, 0], ![-6, 26, 13], ![182, 0, 14]]]
  hmulB := by decide  
  f := ![![![-3803, 16747, 8372], ![-417, -89516, 0]], ![![-552, 2392, 1196], ![1, -12788, 0]], ![![-361, 1566, 783], ![-2, -8372, 0]]]
  g := ![![![1, 0, 0], ![-20, 139, 0], ![-13, 0, 139]], ![![0, 1, 0], ![-5, 26, 13], ![0, 0, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![28, 31, 1]] ![![139, 0, 0], ![20, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2780, 139, 0]], ![![3892, 4309, 139], ![556, 834, 417]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![20, 1, 0]]], ![![![28, 31, 1]], ![![4, 6, 3]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [89, 78, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 42, 10], [73, 106, 139], [0, 1]]
 g := ![![[140, 66, 9], [131, 118], [52, 140, 64], [12, 67], [6, 84, 129], [129, 1], []], ![[139, 0, 23, 59], [115, 130], [46, 66, 39, 72], [137, 96], [91, 8, 102, 60], [46, 61], [32, 100]], ![[139, 105, 124, 126], [107, 110], [72, 69, 12, 89], [10, 24], [105, 148, 33, 87], [133, 125], [52, 100]]]
 h' := ![![[56, 42, 10], [44, 108, 146], [140, 68, 72], [94, 126, 8], [62, 17, 31], [141, 130, 24], [0, 0, 1], [0, 1]], ![[73, 106, 139], [13, 27, 17], [99, 67, 117], [67, 32, 22], [108, 74, 29], [29, 110, 119], [139, 13, 106], [56, 42, 10]], ![[0, 1], [14, 14, 135], [148, 14, 109], [0, 140, 119], [88, 58, 89], [82, 58, 6], [105, 136, 42], [73, 106, 139]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82, 36], []]
 b := ![[], [32, 18, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [89, 78, 20, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51249146, 1207794, -1053728]
  a := ![-13, 10, 28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![343954, 8106, -7072]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [64, 145, 2, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 52, 95], [68, 98, 56], [0, 1]]
 g := ![![[53, 143, 94], [119, 75, 19], [91, 43, 91], [116, 38], [145, 92, 100], [149, 1], []], ![[150, 85, 9, 8], [26, 15, 112, 88], [62, 52, 28, 72], [115, 22], [66, 142, 131, 85], [30, 91], [135, 116]], ![[50, 148, 96, 41], [88, 86, 63, 112], [15, 103, 144, 15], [27, 78], [101, 12, 14, 12], [85, 137], [23, 116]]]
 h' := ![![[81, 52, 95], [85, 139, 68], [65, 64, 87], [55, 5, 98], [82, 41, 76], [128, 75, 10], [0, 0, 1], [0, 1]], ![[68, 98, 56], [134, 146, 88], [140, 134, 110], [115, 64, 113], [23, 17, 18], [60, 105, 102], [35, 149, 98], [81, 52, 95]], ![[0, 1], [91, 17, 146], [46, 104, 105], [43, 82, 91], [67, 93, 57], [55, 122, 39], [132, 2, 52], [68, 98, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 123], []]
 b := ![[], [79, 11, 75], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [64, 145, 2, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-940104947580, -33754318785, -18250195975]
  a := ![326, -389, -717]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6225860580, -223538535, -120862225]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-25, 25, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-25, 25, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![132, 25, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-25, 25, 1], ![32, 125, 319], ![4382, 14, -169]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-132, -25, 157]], ![![-1, 0, 1], ![-268, -50, 319], ![170, 27, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [45, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 156], [0, 1]]
 g := ![![[135, 130], [121], [90, 39], [104, 39], [128, 132], [106], [1]], ![[95, 27], [121], [78, 118], [92, 118], [27, 25], [106], [1]]]
 h' := ![![[48, 156], [132, 75], [32, 11], [30, 143], [49, 14], [81, 140], [112, 48], [0, 1]], ![[0, 1], [121, 82], [89, 146], [143, 14], [93, 143], [50, 17], [61, 109], [48, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [63, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [45, 109, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18695, 10217, -1199]
  a := ![13, -11, -28]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![889, 256, -1199]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-5, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-5, 1, 0]] 
 ![![157, 0, 0], ![152, 1, 0], ![12, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-5, 1, 0], ![-6, 1, 13], ![182, 0, -11]]]
  hmulB := by decide  
  f := ![![![2821, -470, -6110], ![0, 73790, 0]], ![![2731, -455, -5915], ![1, 71435, 0]], ![![216, -36, -467], ![12, 5640, 0]]]
  g := ![![![1, 0, 0], ![-152, 157, 0], ![-12, 0, 157]], ![![-1, 1, 0], ![-2, 1, 13], ![2, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-25, 25, 1]] ![![157, 0, 0], ![-5, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-785, 157, 0]], ![![-3925, 3925, 157], ![157, 0, 314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-5, 1, 0]]], ![![![-25, 25, 1]], ![![1, 0, 2]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 3, 2]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![23, 3, 2]] 
 ![![163, 0, 0], ![71, 1, 0], ![68, 0, 1]] where
  M :=![![![23, 3, 2], ![346, 41, 27], ![210, 28, 17]]]
  hmulB := by decide  
  f := ![![![-59, 5, -1]], ![![-27, 2, 0]], ![![-18, 2, -1]]]
  g := ![![![-2, 3, 2], ![-27, 41, 27], ![-18, 28, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-61, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-61, 1, 0]] 
 ![![163, 0, 0], ![102, 1, 0], ![80, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-61, 1, 0], ![-6, -55, 13], ![182, 0, -67]]]
  hmulB := by decide  
  f := ![![![3056, 30805, -7280], ![-815, 91280, 0]], ![![1918, 19253, -4550], ![-488, 57050, 0]], ![![1501, 15119, -3573], ![-397, 44800, 0]]]
  g := ![![![1, 0, 0], ![-102, 163, 0], ![-80, 0, 163]], ![![-1, 1, 0], ![28, -55, 13], ![34, 0, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-10, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-10, 1, 0]] 
 ![![163, 0, 0], ![153, 1, 0], ![9, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-10, 1, 0], ![-6, -4, 13], ![182, 0, -16]]]
  hmulB := by decide  
  f := ![![![43627, 29199, -94848], ![-2445, 1189248, 0]], ![![40949, 27406, -89024], ![-2281, 1116224, 0]], ![![2411, 1612, -5237], ![-100, 65664, 0]]]
  g := ![![![1, 0, 0], ![-153, 163, 0], ![-9, 0, 163]], ![![-1, 1, 0], ![3, -4, 13], ![2, 0, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![23, 3, 2]] ![![163, 0, 0], ![-61, 1, 0]]
  ![![163, 0, 0], ![30, -74, 1]] where
 M := ![![![3749, 489, 326], ![-1057, -142, -95]]]
 hmul := by decide  
 g := ![![![![-7, 77, 1], ![163, 0, 0]], ![![-19, 30, -1], ![68, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![30, -74, 1]] ![![163, 0, 0], ![-10, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-1630, 163, 0]], ![![4890, -12062, 163], ![326, 326, -978]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-10, 1, 0]]], ![![![30, -74, 1]], ![![2, 2, -6]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-21, -54, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-21, -54, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![146, 113, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-21, -54, 1], ![506, -345, -708], ![-9996, 14, 309]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-146, -113, 167]], ![![-1, -1, 1], ![622, 477, -708], ![-330, -209, 309]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [55, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [164, 166], [0, 1]]
 g := ![![[79, 6], [122, 77], [100, 56], [19], [63], [136, 9], [1]], ![[61, 161], [58, 90], [99, 111], [19], [63], [109, 158], [1]]]
 h' := ![![[164, 166], [137, 29], [11, 54], [42, 35], [98, 55], [35, 118], [112, 164], [0, 1]], ![[0, 1], [50, 138], [16, 113], [104, 132], [100, 112], [15, 49], [121, 3], [164, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [57, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [55, 3, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4547, 2555, 364]
  a := ![6, -7, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-291, -231, 364]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![40, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![40, 1, 0]] 
 ![![167, 0, 0], ![40, 1, 0], ![25, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![40, 1, 0], ![-6, 46, 13], ![182, 0, 34]]]
  hmulB := by decide  
  f := ![![![58625, -470372, -132912], ![11356, 1707408, 0]], ![![14008, -112625, -31824], ![2840, 408816, 0]], ![![8775, -70415, -19897], ![1705, 255600, 0]]]
  g := ![![![1, 0, 0], ![-40, 167, 0], ![-25, 0, 167]], ![![0, 1, 0], ![-13, 46, 13], ![-4, 0, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-21, -54, 1]] ![![167, 0, 0], ![40, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![6680, 167, 0]], ![![-3507, -9018, 167], ![-334, -2505, -668]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![40, 1, 0]]], ![![![-21, -54, 1]], ![![-2, -15, -4]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![21, -33, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![21, -33, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![21, 140, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![21, -33, 1], ![380, -177, -435], ![-6174, 14, 225]]]
  hmulB := by decide  
  f := ![![![-20, 33, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-21, -140, 173]], ![![0, -1, 1], ![55, 351, -435], ![-63, -182, 225]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [86, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 172], [0, 1]]
 g := ![![[152, 151], [85], [54, 22], [2, 51], [60], [151, 67], [1]], ![[37, 22], [85], [169, 151], [72, 122], [60], [53, 106], [1]]]
 h' := ![![[76, 172], [166, 18], [27, 137], [1, 56], [151, 33], [162, 135], [87, 76], [0, 1]], ![[0, 1], [150, 155], [59, 36], [105, 117], [64, 140], [42, 38], [154, 97], [76, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [139, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [86, 97, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![167422, 16155, 8821]
  a := ![-11, 31, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-103, -7045, 8821]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-84, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-84, 1, 0]] 
 ![![173, 0, 0], ![89, 1, 0], ![121, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-84, 1, 0], ![-6, -78, 13], ![182, 0, -90]]]
  hmulB := by decide  
  f := ![![![-23729, -368605, 61425], ![9515, -817425, 0]], ![![-12227, -189568, 31590], ![4845, -420390, 0]], ![![-16549, -257811, 42962], ![6753, -571725, 0]]]
  g := ![![![1, 0, 0], ![-89, 173, 0], ![-121, 0, 173]], ![![-1, 1, 0], ![31, -78, 13], ![64, 0, -90]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![21, -33, 1]] ![![173, 0, 0], ![-84, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-14532, 173, 0]], ![![3633, -5709, 173], ![-1384, 2595, -519]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-84, 1, 0]]], ![![![21, -33, 1]], ![![-8, 15, -3]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-29, 82, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-29, 82, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![150, 82, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-29, 82, 1], ![-310, 463, 1060], ![14756, 14, -515]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-150, -82, 179]], ![![-1, 0, 1], ![-890, -483, 1060], ![514, 236, -515]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [154, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [101, 178], [0, 1]]
 g := ![![[47, 147], [157, 169], [49], [5], [19, 142], [15, 177], [1]], ![[37, 32], [42, 10], [49], [5], [41, 37], [171, 2], [1]]]
 h' := ![![[101, 178], [166, 46], [38, 13], [31, 7], [117, 30], [17, 121], [25, 101], [0, 1]], ![[0, 1], [158, 133], [98, 166], [22, 172], [104, 149], [66, 58], [23, 78], [101, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168]]
 b := ![[], [54, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [154, 78, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-17497, 7650, -483]
  a := ![11, -9, -24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![307, 264, -483]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![14, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![14, 1, 0]] 
 ![![179, 0, 0], ![14, 1, 0], ![157, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![14, 1, 0], ![-6, 20, 13], ![182, 0, 8]]]
  hmulB := by decide  
  f := ![![![13371, -44805, -29120], ![895, 400960, 0]], ![![1036, -3501, -2275], ![180, 31325, 0]], ![![11731, -39298, -25541], ![742, 351680, 0]]]
  g := ![![![1, 0, 0], ![-14, 179, 0], ![-157, 0, 179]], ![![0, 1, 0], ![-13, 20, 13], ![-6, 0, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-29, 82, 1]] ![![179, 0, 0], ![14, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![2506, 179, 0]], ![![-5191, 14678, 179], ![-716, 1611, 1074]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![14, 1, 0]]], ![![![-29, 82, 1]], ![![-4, 9, 6]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![707, 88, 57]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![707, 88, 57]] 
 ![![181, 0, 0], ![0, 181, 0], ![168, 46, 1]] where
  M :=![![![707, 88, 57], ![9846, 1235, 802], ![6440, 798, 521]]]
  hmulB := by decide  
  f := ![![![19, -2, 1]], ![![194, 7, -32]], ![![64, 0, -7]]]
  g := ![![![-49, -14, 57], ![-690, -197, 802], ![-448, -128, 521]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [93, 25, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 180], [0, 1]]
 g := ![![[10, 99], [114], [49, 144], [33], [102, 178], [66, 82], [1]], ![[69, 82], [114], [69, 37], [33], [177, 3], [7, 99], [1]]]
 h' := ![![[156, 180], [15, 113], [149, 64], [54, 12], [107, 157], [16, 97], [88, 156], [0, 1]], ![[0, 1], [86, 68], [178, 117], [116, 169], [164, 24], [125, 84], [170, 25], [156, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [153, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [93, 25, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8387, 10491, 2223]
  a := ![-12, 13, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2017, -507, 2223]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, -2, 1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![19, -2, 1]] 
 ![![181, 0, 0], ![132, 1, 0], ![102, 0, 1]] where
  M :=![![![19, -2, 1], ![194, 7, -32], ![-532, 14, 37]]]
  hmulB := by decide  
  f := ![![![707, 88, 57]], ![![570, 71, 46]], ![![434, 54, 35]]]
  g := ![![![1, -2, 1], ![14, 7, -32], ![-34, 14, 37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![707, 88, 57]] ![![19, -2, 1]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![19, -63, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![19, -63, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![19, 128, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![19, -63, 1], ![560, -359, -825], ![-11634, 14, 403]]]
  hmulB := by decide  
  f := ![![![-18, 63, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -128, 191]], ![![0, -1, 1], ![85, 551, -825], ![-101, -270, 403]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [78, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 190], [0, 1]]
 g := ![![[0, 120], [0, 65], [0, 10], [0, 69], [0, 20], [], [1]], ![[0, 71], [0, 126], [0, 181], [0, 122], [0, 171], [], [1]]]
 h' := ![![[0, 190], [0, 87], [0, 175], [0, 157], [0, 159], [0, 163], [113], [0, 1]], ![[0, 1], [0, 104], [0, 16], [0, 34], [0, 32], [0, 28], [113], [0, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [0, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [78, 0, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87703, 46250, 7300]
  a := ![25, -30, -55]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-267, -4650, 7300]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![61, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![61, 1, 0]] 
 ![![191, 0, 0], ![61, 1, 0], ![170, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![61, 1, 0], ![-6, 67, 13], ![182, 0, 55]]]
  hmulB := by decide  
  f := ![![![96315, -1164188, -225862], ![24830, 3318434, 0]], ![![30726, -371758, -72124], ![8023, 1059668, 0]], ![![85742, -1036188, -201029], ![22048, 2953580, 0]]]
  g := ![![![1, 0, 0], ![-61, 191, 0], ![-170, 0, 191]], ![![0, 1, 0], ![-33, 67, 13], ![-48, 0, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![19, -63, 1]] ![![191, 0, 0], ![61, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![11651, 191, 0]], ![![3629, -12033, 191], ![1719, -4202, -764]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![61, 1, 0]]], ![![![19, -63, 1]], ![![9, -22, -4]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![58, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![58, 1, 0]] 
 ![![193, 0, 0], ![58, 1, 0], ![100, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![58, 1, 0], ![-6, 64, 13], ![182, 0, 52]]]
  hmulB := by decide  
  f := ![![![-10043, 114572, 23270], ![-2316, -345470, 0]], ![![-3048, 34371, 6981], ![-578, -103641, 0]], ![![-5246, 59363, 12057], ![-1059, -179000, 0]]]
  g := ![![![1, 0, 0], ![-58, 193, 0], ![-100, 0, 193]], ![![0, 1, 0], ![-26, 64, 13], ![-26, 0, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-33, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-33, 1, 0]] 
 ![![193, 0, 0], ![160, 1, 0], ![124, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-33, 1, 0], ![-6, -27, 13], ![182, 0, -39]]]
  hmulB := by decide  
  f := ![![![81859, 377630, -181792], ![-11966, 2698912, 0]], ![![67870, 313035, -150696], ![-9842, 2237256, 0]], ![![52606, 242622, -116799], ![-7614, 1734016, 0]]]
  g := ![![![1, 0, 0], ![-160, 193, 0], ![-124, 0, 193]], ![![-1, 1, 0], ![14, -27, 13], ![26, 0, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-25, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-25, 1, 0]] 
 ![![193, 0, 0], ![168, 1, 0], ![156, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-25, 1, 0], ![-6, -19, 13], ![182, 0, -31]]]
  hmulB := by decide  
  f := ![![![35789, 114932, -78624], ![-3860, 1167264, 0]], ![![31135, 100034, -68432], ![-3473, 1015952, 0]], ![![28913, 92899, -63551], ![-3235, 943488, 0]]]
  g := ![![![1, 0, 0], ![-168, 193, 0], ![-156, 0, 193]], ![![-1, 1, 0], ![6, -19, 13], ![26, 0, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![58, 1, 0]] ![![193, 0, 0], ![-33, 1, 0]]
  ![![193, 0, 0], ![75, -57, 1]] where
 M := ![![![37249, 0, 0], ![-6369, 193, 0]], ![![11194, 193, 0], ![-1920, 31, 13]]]
 hmul := by decide  
 g := ![![![![118, 57, -1], ![193, 0, 0]], ![![-33, 1, 0], ![0, 0, 0]]], ![![![-17, 58, -1], ![193, 0, 0]], ![![-15, 4, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![75, -57, 1]] ![![193, 0, 0], ![-25, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-4825, 193, 0]], ![![14475, -11001, 193], ![-1351, 1158, -772]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-25, 1, 0]]], ![![![75, -57, 1]], ![![-7, 6, -4]]]]
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


lemma PB264I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB264I3 : PrimesBelowBoundCertificateInterval O 137 193 264 where
  m := 11
  g := ![2, 1, 1, 2, 3, 2, 2, 2, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB264I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
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
    · exact ![3307949]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![32761, 181]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
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
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I157N1, I163N0, I163N1, I163N2, I167N1, I173N1, I179N1, I181N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [], [], [I157N1], [I163N0, I163N1, I163N2], [I167N1], [I173N1], [I179N1], [I181N1], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
