
import IdealArithmetic.Examples.NF3_1_542700_2.RI3_1_542700_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![37, 31, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![37, 31, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![37, 31, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![37, 31, 1], ![210, 67, 186], ![6510, 965, 67]]]
  hmulB := by decide  
  f := ![![![-36, -31, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -31, 139]], ![![0, 0, 1], ![-48, -41, 186], ![29, -8, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [130, 85, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 138], [0, 1]]
 g := ![![[6, 66], [73, 36], [7], [79, 11], [20], [136], [1]], ![[95, 73], [71, 103], [7], [117, 128], [20], [136], [1]]]
 h' := ![![[54, 138], [101, 109], [41, 6], [16, 110], [38, 17], [54, 115], [9, 54], [0, 1]], ![[0, 1], [10, 30], [87, 133], [118, 29], [122, 122], [9, 24], [6, 85], [54, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [128, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [130, 85, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![550, 10, -49]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 11, -49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-47, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-47, 1, 0]] 
 ![![139, 0, 0], ![92, 1, 0], ![72, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-47, 1, 0], ![0, -47, 6], ![210, 30, -47]]]
  hmulB := by decide  
  f := ![![![4372, -93, 0], ![12927, 0, 0]], ![![2868, -61, 0], ![8480, 0, 0]], ![![2314, -10, -5], ![6842, 116, 0]]]
  g := ![![![1, 0, 0], ![-92, 139, 0], ![-72, 0, 139]], ![![-1, 1, 0], ![28, -47, 6], ![6, 30, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![37, 31, 1]] ![![139, 0, 0], ![-47, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-6533, 139, 0]], ![![5143, 4309, 139], ![-1529, -1390, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-47, 1, 0]]], ![![![37, 31, 1]], ![![-11, -10, 1]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [59, 75, 121, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 27, 123], [140, 121, 26], [0, 1]]
 g := ![![[12, 43, 16], [52, 68], [132, 108, 88], [121, 7], [93, 122, 104], [28, 1], []], ![[28, 68, 62, 140], [91, 54], [63, 88, 109, 82], [128, 80], [91, 131, 135, 68], [69, 39], [91, 80]], ![[131, 7, 140, 142], [64, 64], [130, 142, 107, 127], [78, 6], [132, 135, 21, 61], [146, 133], [39, 80]]]
 h' := ![![[37, 27, 123], [22, 117, 4], [109, 125, 51], [93, 3, 104], [26, 2, 93], [136, 76, 113], [0, 0, 1], [0, 1]], ![[140, 121, 26], [122, 135, 124], [96, 132, 90], [63, 129, 139], [4, 74, 26], [34, 64, 75], [23, 138, 121], [37, 27, 123]], ![[0, 1], [72, 46, 21], [47, 41, 8], [136, 17, 55], [62, 73, 30], [104, 9, 110], [15, 11, 27], [140, 121, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [126, 146], []]
 b := ![[], [81, 71, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [59, 75, 121, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-449086, 9238, 53640]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3014, 62, 360]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![4, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![4, 1, 0]] 
 ![![151, 0, 0], ![4, 1, 0], ![98, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![4, 1, 0], ![0, 4, 6], ![210, 30, 4]]]
  hmulB := by decide  
  f := ![![![145, 36, 0], ![-5436, 0, 0]], ![![-4, -1, 0], ![152, 0, 0]], ![![94, 20, -5], ![-3524, 126, 0]]]
  g := ![![![1, 0, 0], ![-4, 151, 0], ![-98, 0, 151]], ![![0, 1, 0], ![-4, 4, 6], ![-2, 30, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![33, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![33, 1, 0]] 
 ![![151, 0, 0], ![33, 1, 0], ![45, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![33, 1, 0], ![0, 33, 6], ![210, 30, 33]]]
  hmulB := by decide  
  f := ![![![2608, 79, 0], ![-11929, 0, 0]], ![![528, 16, 0], ![-2415, 0, 0]], ![![744, -5, -5], ![-3403, 126, 0]]]
  g := ![![![1, 0, 0], ![-33, 151, 0], ![-45, 0, 151]], ![![0, 1, 0], ![-9, 33, 6], ![-15, 30, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-37, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-37, 1, 0]] 
 ![![151, 0, 0], ![114, 1, 0], ![99, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-37, 1, 0], ![0, -37, 6], ![210, 30, -37]]]
  hmulB := by decide  
  f := ![![![2406, -65, 0], ![9815, 0, 0]], ![![1814, -49, 0], ![7400, 0, 0]], ![![1624, -13, -5], ![6625, 126, 0]]]
  g := ![![![1, 0, 0], ![-114, 151, 0], ![-99, 0, 151]], ![![-1, 1, 0], ![24, -37, 6], ![3, 30, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![4, 1, 0]] ![![151, 0, 0], ![33, 1, 0]]
  ![![151, 0, 0], ![22, -19, 1]] where
 M := ![![![22801, 0, 0], ![4983, 151, 0]], ![![604, 151, 0], ![132, 37, 6]]]
 hmul := by decide  
 g := ![![![![129, 19, -1], ![151, 0, 0]], ![![11, 20, -1], ![151, 0, 0]]], ![![![-18, 20, -1], ![151, 0, 0]], ![![0, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![22, -19, 1]] ![![151, 0, 0], ![-37, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-5587, 151, 0]], ![![3322, -2869, 151], ![-604, 755, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-37, 1, 0]]], ![![![22, -19, 1]], ![![-4, 5, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![52, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![52, 1, 0]] 
 ![![157, 0, 0], ![52, 1, 0], ![125, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![52, 1, 0], ![0, 52, 6], ![210, 30, 52]]]
  hmulB := by decide  
  f := ![![![3225, 62, 0], ![-9734, 0, 0]], ![![1092, 21, 0], ![-3296, 0, 0]], ![![2569, 58, 1], ![-7754, -26, 0]]]
  g := ![![![1, 0, 0], ![-52, 157, 0], ![-125, 0, 157]], ![![0, 1, 0], ![-22, 52, 6], ![-50, 30, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-32, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-32, 1, 0]] 
 ![![157, 0, 0], ![125, 1, 0], ![91, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-32, 1, 0], ![0, -32, 6], ![210, 30, -32]]]
  hmulB := by decide  
  f := ![![![2177, -68, 0], ![10676, 0, 0]], ![![1761, -55, 0], ![8636, 0, 0]], ![![1303, -14, -5], ![6390, 131, 0]]]
  g := ![![![1, 0, 0], ![-125, 157, 0], ![-91, 0, 157]], ![![-1, 1, 0], ![22, -32, 6], ![-4, 30, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-20, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-20, 1, 0]] 
 ![![157, 0, 0], ![137, 1, 0], ![38, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-20, 1, 0], ![0, -20, 6], ![210, 30, -20]]]
  hmulB := by decide  
  f := ![![![1301, -65, 0], ![10205, 0, 0]], ![![1121, -56, 0], ![8793, 0, 0]], ![![334, 0, -5], ![2620, 131, 0]]]
  g := ![![![1, 0, 0], ![-137, 157, 0], ![-38, 0, 157]], ![![-1, 1, 0], ![16, -20, 6], ![-20, 30, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![52, 1, 0]] ![![157, 0, 0], ![-32, 1, 0]]
  ![![157, 0, 0], ![-68, -49, 1]] where
 M := ![![![24649, 0, 0], ![-5024, 157, 0]], ![![8164, 157, 0], ![-1664, 20, 6]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![36, 50, -1], ![157, 0, 0]]], ![![![52, 1, 0], ![0, 0, 0]], ![![-8, 2, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-68, -49, 1]] ![![157, 0, 0], ![-20, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-3140, 157, 0]], ![![-10676, -7693, 157], ![1570, 942, -314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-20, 1, 0]]], ![![![-68, -49, 1]], ![![10, 6, -2]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [8, 128, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 2, 51], [58, 160, 112], [0, 1]]
 g := ![![[161, 148, 56], [23, 47, 140], [23, 38], [84, 100], [77, 140], [132, 74, 1], []], ![[53, 66, 1, 62], [133, 33, 109, 64], [122, 57], [42, 36], [63, 1], [26, 84, 122, 133], [12, 156]], ![[0, 61, 69, 101], [37, 0, 47, 120], [146, 90], [136, 16], [61, 54], [87, 40, 23, 122], [114, 156]]]
 h' := ![![[16, 2, 51], [142, 73, 120], [40, 155, 125], [77, 129, 53], [89, 105, 153], [85, 116, 125], [0, 0, 1], [0, 1]], ![[58, 160, 112], [135, 72, 103], [26, 2, 32], [26, 27, 63], [6, 26, 6], [99, 87, 162], [160, 51, 160], [16, 2, 51]], ![[0, 1], [0, 18, 103], [125, 6, 6], [106, 7, 47], [78, 32, 4], [27, 123, 39], [7, 112, 2], [58, 160, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [134, 61], []]
 b := ![[], [147, 121, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [8, 128, 89, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![150286, 3749, -5542]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![922, 23, -34]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [105, 101, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 164, 37], [137, 2, 130], [0, 1]]
 g := ![![[135, 66, 66], [95, 139, 72], [150, 124, 81], [43, 19], [87, 54], [166, 157, 1], []], ![[132, 121, 16, 13], [22, 39, 1, 153], [122, 110, 85, 55], [83, 22], [79, 25], [87, 10, 150, 148], [116, 33]], ![[51, 94, 84, 58], [106, 33, 77, 97], [70, 69, 74, 63], [26, 54], [76, 114], [105, 0, 50, 1], [23, 33]]]
 h' := ![![[20, 164, 37], [45, 57, 147], [115, 13, 78], [131, 78, 158], [53, 133, 112], [105, 149, 80], [0, 0, 1], [0, 1]], ![[137, 2, 130], [146, 72, 65], [35, 32, 136], [163, 34, 29], [148, 144, 135], [60, 84, 162], [77, 63, 2], [20, 164, 37]], ![[0, 1], [78, 38, 122], [125, 122, 120], [70, 55, 147], [63, 57, 87], [19, 101, 92], [155, 104, 164], [137, 2, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 116], []]
 b := ![[], [30, 102, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [105, 101, 10, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-43253, -32231, -17034]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-259, -193, -102]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [61, 90, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 137, 162], [77, 35, 11], [0, 1]]
 g := ![![[93, 36, 126], [135, 92], [87, 73, 92], [81, 141, 29], [132, 142], [50, 113, 1], []], ![[159, 20], [68, 56], [36, 35, 31, 128], [12, 135, 126, 8], [141, 31], [100, 45, 46, 19], [106, 121]], ![[128, 82, 41, 2], [66, 89], [25, 75, 162, 125], [75, 79, 91, 45], [72, 57], [88, 34, 126, 70], [84, 121]]]
 h' := ![![[36, 137, 162], [91, 122, 68], [56, 67, 28], [76, 35, 28], [23, 131, 95], [64, 25, 90], [0, 0, 1], [0, 1]], ![[77, 35, 11], [134, 132], [87, 153, 70], [166, 94, 76], [65, 88, 154], [169, 91, 107], [20, 36, 35], [36, 137, 162]], ![[0, 1], [42, 92, 105], [75, 126, 75], [53, 44, 69], [85, 127, 97], [49, 57, 149], [113, 137, 137], [77, 35, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54, 35], []]
 b := ![[], [144, 45, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [61, 90, 60, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2249, 0, 0]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13, 0, 0]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![43, -20, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![43, -20, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![43, 159, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![43, -20, 1], ![210, 73, -120], ![-4200, -565, 73]]]
  hmulB := by decide  
  f := ![![![-42, 20, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -159, 179]], ![![0, -1, 1], ![30, 107, -120], ![-41, -68, 73]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [6, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 178], [0, 1]]
 g := ![![[129, 27], [154, 22], [49], [89], [55, 22], [157, 142], [1]], ![[174, 152], [131, 157], [49], [89], [32, 157], [155, 37], [1]]]
 h' := ![![[121, 178], [150, 122], [93, 102], [71, 172], [28, 140], [132, 102], [173, 121], [0, 1]], ![[0, 1], [55, 57], [84, 77], [119, 7], [142, 39], [123, 77], [136, 58], [121, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [133, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [6, 58, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![8045, 2315, 2256]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-497, -1991, 2256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-59, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-59, 1, 0]] 
 ![![179, 0, 0], ![120, 1, 0], ![106, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-59, 1, 0], ![0, -59, 6], ![210, 30, -59]]]
  hmulB := by decide  
  f := ![![![6845, -116, 0], ![20764, 0, 0]], ![![4544, -77, 0], ![13784, 0, 0]], ![![4006, -58, -1], ![12152, 30, 0]]]
  g := ![![![1, 0, 0], ![-120, 179, 0], ![-106, 0, 179]], ![![-1, 1, 0], ![36, -59, 6], ![16, 30, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![43, -20, 1]] ![![179, 0, 0], ![-59, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-10561, 179, 0]], ![![7697, -3580, 179], ![-2327, 1253, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-59, 1, 0]]], ![![![43, -20, 1]], ![![-13, 7, -1]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [158, 26, 63, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 135, 6], [70, 45, 175], [0, 1]]
 g := ![![[128, 141, 34], [140, 116], [157, 143, 116], [148, 152], [62, 84, 34], [142, 118, 1], []], ![[162, 158, 139, 155], [104, 67], [144, 17, 134, 77], [91, 42], [19, 179, 50, 19], [101, 100, 104, 23], [76, 36]], ![[164, 176, 86, 91], [2, 106], [29, 24, 69, 124], [90, 180], [128, 110, 5, 107], [16, 71, 143, 155], [88, 36]]]
 h' := ![![[48, 135, 6], [43, 140, 45], [172, 79, 109], [87, 128, 109], [159, 22, 40], [8, 108, 136], [0, 0, 1], [0, 1]], ![[70, 45, 175], [139, 19, 150], [10, 41, 130], [105, 140, 62], [33, 144, 122], [51, 157, 71], [70, 47, 45], [48, 135, 6]], ![[0, 1], [148, 22, 167], [37, 61, 123], [124, 94, 10], [100, 15, 19], [68, 97, 155], [46, 134, 135], [70, 45, 175]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 113], []]
 b := ![[], [113, 102, 132], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [158, 26, 63, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7964, -3801, 1267]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44, -21, 7]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-114, -69, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-114, -69, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![77, 122, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-114, -69, 1], ![210, -84, -414], ![-14490, -2035, -84]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-77, -122, 191]], ![![-1, -1, 1], ![168, 264, -414], ![-42, 43, -84]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [74, 62, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 190], [0, 1]]
 g := ![![[6, 52], [180, 34], [138, 128], [152, 130], [72, 72], [48, 24], [1]], ![[29, 139], [173, 157], [33, 63], [114, 61], [1, 119], [88, 167], [1]]]
 h' := ![![[129, 190], [50, 166], [102, 176], [21, 74], [20, 148], [77, 151], [117, 129], [0, 1]], ![[0, 1], [72, 25], [77, 15], [17, 117], [12, 43], [74, 40], [141, 62], [129, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [55, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [74, 62, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![914, 322, 250]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-96, -158, 250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![32, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![32, 1, 0]] 
 ![![191, 0, 0], ![32, 1, 0], ![84, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![32, 1, 0], ![0, 32, 6], ![210, 30, 32]]]
  hmulB := by decide  
  f := ![![![129, 4, 0], ![-764, 0, 0]], ![![-32, -1, 0], ![192, 0, 0]], ![![44, -4, -1], ![-260, 32, 0]]]
  g := ![![![1, 0, 0], ![-32, 191, 0], ![-84, 0, 191]], ![![0, 1, 0], ![-8, 32, 6], ![-18, 30, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-114, -69, 1]] ![![191, 0, 0], ![32, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![6112, 191, 0]], ![![-21774, -13179, 191], ![-3438, -2292, -382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![32, 1, 0]]], ![![![-114, -69, 1]], ![![-18, -12, -2]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [50, 43, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [40, 11, 167], [86, 181, 26], [0, 1]]
 g := ![![[115, 172, 100], [172, 138], [102, 93], [44, 124], [11, 124], [96, 50], [1]], ![[133, 122, 125, 103], [28, 181], [16, 101], [123, 92], [51, 43], [49, 64], [159, 137, 19, 180]], ![[147, 161, 91, 158], [14, 144], [73, 56], [167, 108], [181, 145], [192, 28], [70, 113, 76, 13]]]
 h' := ![![[40, 11, 167], [168, 81, 183], [135, 104, 36], [88, 30, 38], [92, 84, 160], [16, 181, 160], [143, 150, 126], [0, 1]], ![[86, 181, 26], [20, 53, 137], [164, 185, 145], [112, 79, 115], [146, 50, 142], [90, 152, 129], [80, 127, 185], [40, 11, 167]], ![[0, 1], [74, 59, 66], [141, 97, 12], [160, 84, 40], [37, 59, 84], [4, 53, 97], [95, 109, 75], [86, 181, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151, 106], []]
 b := ![[], [67, 31, 108], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [50, 43, 67, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2569988, -225810, 143206]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-13316, -1170, 742]
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



lemma PB209I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB209I3 : PrimesBelowBoundCertificateInterval O 137 193 209 where
  m := 11
  g := ![2, 1, 3, 3, 1, 1, 1, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB209I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
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
      exact NI139N1
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
      exact NI157N1
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
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
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I151N0, I151N1, I151N2, I157N0, I157N1, I157N2, I179N1, I191N1]
  Il := ![[I139N1], [], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N2], [], [], [], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
