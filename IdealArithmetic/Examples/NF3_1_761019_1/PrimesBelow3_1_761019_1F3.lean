
import IdealArithmetic.Examples.NF3_1_761019_1.RI3_1_761019_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [51, 118, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 70, 112], [19, 68, 27], [0, 1]]
 g := ![![[34, 27, 57], [80, 32, 13], [116, 78], [134, 11, 63], [30, 36], [92, 1], []], ![[120, 98, 102, 77], [57, 108, 103, 31], [1, 106], [20, 87, 31, 51], [16, 107], [118, 37], [43, 34]], ![[111, 20, 41, 56], [43, 86, 42, 62], [60, 1], [26, 112, 82, 27], [63, 106], [86, 35], [128, 34]]]
 h' := ![![[73, 70, 112], [90, 92, 125], [34, 57, 41], [116, 71, 56], [43, 73, 87], [34, 74, 6], [0, 0, 1], [0, 1]], ![[19, 68, 27], [15, 94, 39], [26, 17, 137], [76, 52, 84], [65, 46, 53], [66, 76, 78], [78, 76, 68], [73, 70, 112]], ![[0, 1], [50, 92, 114], [138, 65, 100], [138, 16, 138], [51, 20, 138], [22, 128, 55], [88, 63, 70], [19, 68, 27]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 70], []]
 b := ![[], [38, 27, 121], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [51, 118, 47, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1114641, -465372, -236022]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8019, -3348, -1698]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [35, 50, 137, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 39, 138], [102, 109, 11], [0, 1]]
 g := ![![[109, 141, 88], [84, 35], [20, 6, 54], [143, 112], [25, 62, 45], [12, 1], []], ![[25, 25, 63, 109], [147, 132], [76, 39, 137, 65], [5, 132], [55, 127, 13, 93], [18, 110], [147, 121]], ![[39, 137, 32, 13], [74, 20], [89, 57, 97, 146], [78, 25], [47, 62, 17, 15], [4, 31], [125, 121]]]
 h' := ![![[59, 39, 138], [128, 35, 104], [45, 11, 66], [124, 61, 90], [19, 140, 75], [27, 110, 94], [0, 0, 1], [0, 1]], ![[102, 109, 11], [40, 18, 74], [87, 110, 70], [132, 7, 50], [146, 106, 79], [144, 61, 96], [124, 20, 109], [59, 39, 138]], ![[0, 1], [146, 96, 120], [59, 28, 13], [40, 81, 9], [104, 52, 144], [2, 127, 108], [69, 129, 39], [102, 109, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31, 59], []]
 b := ![[], [118, 138, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [35, 50, 137, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![834400, 318711, 123819]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5600, 2139, 831]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![54, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![54, 1, 0]] 
 ![![151, 0, 0], ![54, 1, 0], ![40, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![54, 1, 0], ![2, 53, 4], ![-92, -32, 56]]]
  hmulB := by decide  
  f := ![![![3359, 107577, 8120], ![1963, -306530, 0]], ![![1180, 38420, 2900], ![756, -109475, 0]], ![![878, 28497, 2151], ![553, -81200, 0]]]
  g := ![![![1, 0, 0], ![-54, 151, 0], ![-40, 0, 151]], ![![0, 1, 0], ![-20, 53, 4], ![-4, -32, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-47, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-47, 1, 0]] 
 ![![151, 0, 0], ![104, 1, 0], ![116, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-47, 1, 0], ![2, -48, 4], ![-92, -32, -45]]]
  hmulB := by decide  
  f := ![![![3347, -91574, 7632], ![-1510, -288108, 0]], ![![2300, -63065, 5256], ![-1056, -198414, 0]], ![![2560, -70348, 5863], ![-1196, -221328, 0]]]
  g := ![![![1, 0, 0], ![-104, 151, 0], ![-116, 0, 151]], ![![-1, 1, 0], ![30, -48, 4], ![56, -32, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-8, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-8, 1, 0]] 
 ![![151, 0, 0], ![143, 1, 0], ![58, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-8, 1, 0], ![2, -9, 4], ![-92, -32, -6]]]
  hmulB := by decide  
  f := ![![![32857, -148482, 66000], ![-2718, -2491500, 0]], ![![31115, -140608, 62500], ![-2566, -2359375, 0]], ![![12622, -57033, 25351], ![-1017, -957000, 0]]]
  g := ![![![1, 0, 0], ![-143, 151, 0], ![-58, 0, 151]], ![![-1, 1, 0], ![7, -9, 4], ![32, -32, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![54, 1, 0]] ![![151, 0, 0], ![-47, 1, 0]]
  ![![151, 0, 0], ![-30, -74, 1]] where
 M := ![![![22801, 0, 0], ![-7097, 151, 0]], ![![8154, 151, 0], ![-2536, 6, 4]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![-17, 75, -1], ![151, 0, 0]]], ![![![54, 1, 0], ![0, 0, 0]], ![![-16, 2, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-30, -74, 1]] ![![151, 0, 0], ![-8, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-1208, 151, 0]], ![![-4530, -11174, 151], ![0, 604, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-8, 1, 0]]], ![![![-30, -74, 1]], ![![0, 4, -2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![74, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![74, 1, 0]] 
 ![![157, 0, 0], ![74, 1, 0], ![63, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![74, 1, 0], ![2, 73, 4], ![-92, -32, 76]]]
  hmulB := by decide  
  f := ![![![-1843, -88906, -4872], ![-1256, 191226, 0]], ![![-852, -41898, -2296], ![-627, 90118, 0]], ![![-765, -35676, -1955], ![-450, 76734, 0]]]
  g := ![![![1, 0, 0], ![-74, 157, 0], ![-63, 0, 157]], ![![0, 1, 0], ![-36, 73, 4], ![-16, -32, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-65, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-65, 1, 0]] 
 ![![157, 0, 0], ![92, 1, 0], ![27, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-65, 1, 0], ![2, -66, 4], ![-92, -32, -63]]]
  hmulB := by decide  
  f := ![![![19564, -827819, 50176], ![-13345, -1969408, 0]], ![![11516, -485051, 29400], ![-7692, -1153950, 0]], ![![3379, -142364, 8629], ![-2260, -338688, 0]]]
  g := ![![![1, 0, 0], ![-92, 157, 0], ![-27, 0, 157]], ![![-1, 1, 0], ![38, -66, 4], ![29, -32, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-10, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-10, 1, 0]] 
 ![![157, 0, 0], ![147, 1, 0], ![130, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-10, 1, 0], ![2, -11, 4], ![-92, -32, -8]]]
  hmulB := by decide  
  f := ![![![-271, 1550, -564], ![157, 22137, 0]], ![![-253, 1451, -528], ![158, 20724, 0]], ![![-230, 1284, -467], ![42, 18330, 0]]]
  g := ![![![1, 0, 0], ![-147, 157, 0], ![-130, 0, 157]], ![![-1, 1, 0], ![7, -11, 4], ![36, -32, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![74, 1, 0]] ![![157, 0, 0], ![-65, 1, 0]]
  ![![157, 0, 0], ![54, 2, 1]] where
 M := ![![![24649, 0, 0], ![-10205, 157, 0]], ![![11618, 157, 0], ![-4808, 8, 4]]]
 hmul := by decide  
 g := ![![![![103, -2, -1], ![157, 0, 0]], ![![-65, 1, 0], ![0, 0, 0]]], ![![![20, -1, -1], ![157, 0, 0]], ![![-32, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![54, 2, 1]] ![![157, 0, 0], ![-10, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-1570, 157, 0]], ![![8478, 314, 157], ![-628, 0, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-10, 1, 0]]], ![![![54, 2, 1]], ![![-4, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-1, 15, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-1, 15, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![162, 15, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-1, 15, 1], ![-62, -48, 62], ![-1465, -519, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-162, -15, 163]], ![![-1, 0, 1], ![-62, -6, 62], ![-7, -3, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [62, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 162], [0, 1]]
 g := ![![[88, 71], [5, 113], [22], [115], [46], [124, 61], [1]], ![[0, 92], [106, 50], [22], [115], [46], [154, 102], [1]]]
 h' := ![![[86, 162], [16, 87], [44, 73], [58, 115], [159, 142], [136, 131], [101, 86], [0, 1]], ![[0, 1], [0, 76], [128, 90], [5, 48], [146, 21], [155, 32], [162, 77], [86, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [10, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [62, 77, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-358832, -165714, -131798]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![128788, 11112, -131798]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-62, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-62, 1, 0]] 
 ![![163, 0, 0], ![101, 1, 0], ![2, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-62, 1, 0], ![2, -63, 4], ![-92, -32, -60]]]
  hmulB := by decide  
  f := ![![![19395, -753407, 47840], ![-11899, -1949480, 0]], ![![12031, -466785, 29640], ![-7334, -1207830, 0]], ![![284, -9245, 587], ![-25, -23920, 0]]]
  g := ![![![1, 0, 0], ![-101, 163, 0], ![-2, 0, 163]], ![![-1, 1, 0], ![39, -63, 4], ![20, -32, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-1, 15, 1]] ![![163, 0, 0], ![-62, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-10106, 163, 0]], ![![-163, 2445, 163], ![0, -978, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-62, 1, 0]]], ![![![-1, 15, 1]], ![![0, -6, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![18, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![18, 1, 0]] 
 ![![167, 0, 0], ![18, 1, 0], ![91, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![18, 1, 0], ![2, 17, 4], ![-92, -32, 20]]]
  hmulB := by decide  
  f := ![![![-4347, -37566, -8840], ![-668, 369070, 0]], ![![-476, -4046, -952], ![1, 39746, 0]], ![![-2385, -20471, -4817], ![-213, 201110, 0]]]
  g := ![![![1, 0, 0], ![-18, 167, 0], ![-91, 0, 167]], ![![0, 1, 0], ![-4, 17, 4], ![-8, -32, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![74, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![74, 1, 0]] 
 ![![167, 0, 0], ![74, 1, 0], ![153, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![74, 1, 0], ![2, 73, 4], ![-92, -32, 76]]]
  hmulB := by decide  
  f := ![![![-13403, -645846, -35392], ![-9686, 1477616, 0]], ![![-5990, -286135, -15680], ![-4174, 654640, 0]], ![![-12263, -591703, -32425], ![-8911, 1353744, 0]]]
  g := ![![![1, 0, 0], ![-74, 167, 0], ![-153, 0, 167]], ![![0, 1, 0], ![-36, 73, 4], ![-56, -32, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![18, 1, 0]] ![![167, 0, 0], ![74, 1, 0]]
  ![![167, 0, 0], ![83, -19, 1]] where
 M := ![![![27889, 0, 0], ![12358, 167, 0]], ![![3006, 167, 0], ![1334, 91, 4]]]
 hmul := by decide  
 g := ![![![![84, 19, -1], ![167, 0, 0]], ![![-9, 20, -1], ![167, 0, 0]]], ![![![-65, 20, -1], ![167, 0, 0]], ![![6, 1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![83, -19, 1]] ![![167, 0, 0], ![74, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![12358, 167, 0]], ![![13861, -3173, 167], ![6012, -1336, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![74, 1, 0]]], ![![![83, -19, 1]], ![![36, -8, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![15, -20, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![15, -20, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![15, 153, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![15, -20, 1], ![-132, 3, -78], ![1755, 601, -56]]]
  hmulB := by decide  
  f := ![![![-14, 20, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-15, -153, 173]], ![![0, -1, 1], ![6, 69, -78], ![15, 53, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [48, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 172], [0, 1]]
 g := ![![[66, 92], [4], [19, 35], [102, 169], [122], [133, 148], [1]], ![[115, 81], [4], [32, 138], [145, 4], [122], [99, 25], [1]]]
 h' := ![![[119, 172], [114, 145], [126, 171], [121, 143], [142, 13], [17, 128], [125, 119], [0, 1]], ![[0, 1], [69, 28], [61, 2], [11, 30], [132, 160], [25, 45], [100, 54], [119, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [72, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [48, 54, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2051, -1302, -2997]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![248, 2643, -2997]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![78, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![78, 1, 0]] 
 ![![173, 0, 0], ![78, 1, 0], ![56, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![78, 1, 0], ![2, 77, 4], ![-92, -32, 80]]]
  hmulB := by decide  
  f := ![![![-26321, -1352623, -70272], ![-19549, 3039264, 0]], ![![-11862, -609789, -31680], ![-8822, 1370160, 0]], ![![-8576, -437844, -22747], ![-6204, 983808, 0]]]
  g := ![![![1, 0, 0], ![-78, 173, 0], ![-56, 0, 173]], ![![0, 1, 0], ![-36, 77, 4], ![-12, -32, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![15, -20, 1]] ![![173, 0, 0], ![78, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![13494, 173, 0]], ![![2595, -3460, 173], ![1038, -1557, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![78, 1, 0]]], ![![![15, -20, 1]], ![![6, -9, 0]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [44, 178, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 3, 144], [47, 175, 35], [0, 1]]
 g := ![![[13, 50, 49], [146, 13, 68], [143, 129], [43, 141], [95, 121, 101], [145, 12, 1], []], ![[65, 3, 38, 19], [75, 41, 10, 108], [104, 14], [50, 66], [120, 91, 173, 31], [52, 122, 55, 156], [170, 151]], ![[137, 112, 117, 120], [173, 163, 7, 128], [62, 135], [159, 51], [158, 41, 175, 166], [0, 149, 86, 136], [100, 151]]]
 h' := ![![[144, 3, 144], [20, 115, 7], [2, 40, 28], [108, 20, 32], [116, 120, 61], [64, 154, 97], [0, 0, 1], [0, 1]], ![[47, 175, 35], [3, 97, 64], [135, 23, 99], [86, 77, 67], [106, 40, 31], [119, 94, 129], [10, 118, 175], [144, 3, 144]], ![[0, 1], [112, 146, 108], [141, 116, 52], [30, 82, 80], [90, 19, 87], [88, 110, 132], [136, 61, 3], [47, 175, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 56], []]
 b := ![[], [67, 92, 109], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [44, 178, 167, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1348228, -588552, -368382]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7532, -3288, -2058]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![7, -18, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![7, -18, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![7, 163, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![7, -18, 1], ![-128, -7, -70], ![1571, 537, -60]]]
  hmulB := by decide  
  f := ![![![-6, 18, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -163, 181]], ![![0, -1, 1], ![2, 63, -70], ![11, 57, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [54, 156, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 180], [0, 1]]
 g := ![![[23, 111], [60], [100, 143], [1], [49, 33], [74, 82], [1]], ![[83, 70], [60], [55, 38], [1], [150, 148], [133, 99], [1]]]
 h' := ![![[25, 180], [13, 103], [30, 28], [1, 163], [69, 1], [167, 157], [127, 25], [0, 1]], ![[0, 1], [54, 78], [6, 153], [94, 18], [94, 180], [110, 24], [28, 156], [25, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [66, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [54, 156, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-145281, -69560, -48887]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1088, 43641, -48887]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![70, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![70, 1, 0]] 
 ![![181, 0, 0], ![70, 1, 0], ![60, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![70, 1, 0], ![2, 69, 4], ![-92, -32, 72]]]
  hmulB := by decide  
  f := ![![![-4649, -196635, -11400], ![-2715, 515850, 0]], ![![-1784, -76032, -4408], ![-1085, 199462, 0]], ![![-1550, -65183, -3779], ![-877, 171000, 0]]]
  g := ![![![1, 0, 0], ![-70, 181, 0], ![-60, 0, 181]], ![![0, 1, 0], ![-28, 69, 4], ![-12, -32, 72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![7, -18, 1]] ![![181, 0, 0], ![70, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![12670, 181, 0]], ![![1267, -3258, 181], ![362, -1267, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![70, 1, 0]]], ![![![7, -18, 1]], ![![2, -7, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![78, -39, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![78, -39, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![78, 152, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![78, -39, 1], ![-170, 85, -154], ![3503, 1209, -31]]]
  hmulB := by decide  
  f := ![![![-77, 39, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -152, 191]], ![![0, -1, 1], ![62, 123, -154], ![31, 31, -31]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [148, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 190], [0, 1]]
 g := ![![[145, 133], [87, 108], [93, 153], [139, 10], [80, 5], [27, 40], [1]], ![[78, 58], [1, 83], [3, 38], [32, 181], [122, 186], [172, 151], [1]]]
 h' := ![![[123, 190], [112, 18], [179, 144], [56, 150], [2, 157], [15, 14], [43, 123], [0, 1]], ![[0, 1], [34, 173], [128, 47], [170, 41], [22, 34], [18, 177], [83, 68], [123, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18]]
 b := ![[], [115, 9]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [148, 68, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-119, -36, 45]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19, -36, 45]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-37, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-37, 1, 0]] 
 ![![191, 0, 0], ![154, 1, 0], ![31, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-37, 1, 0], ![2, -38, 4], ![-92, -32, -35]]]
  hmulB := by decide  
  f := ![![![2450, -48637, 5120], ![-573, -244480, 0]], ![![1954, -39213, 4128], ![-572, -197112, 0]], ![![399, -7894, 831], ![-86, -39680, 0]]]
  g := ![![![1, 0, 0], ![-154, 191, 0], ![-31, 0, 191]], ![![-1, 1, 0], ![30, -38, 4], ![31, -32, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![78, -39, 1]] ![![191, 0, 0], ![-37, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-7067, 191, 0]], ![![14898, -7449, 191], ![-3056, 1528, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-37, 1, 0]]], ![![![78, -39, 1]], ![![-16, 8, -1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-44, -26, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-44, -26, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![149, 167, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-44, -26, 1], ![-144, -50, -102], ![2307, 793, -127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-149, -167, 193]], ![![-1, -1, 1], ![78, 88, -102], ![110, 114, -127]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [12, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 192], [0, 1]]
 g := ![![[156, 177], [31], [192], [108], [124], [23], [58, 1]], ![[0, 16], [31], [192], [108], [124], [23], [116, 192]]]
 h' := ![![[58, 192], [122, 131], [84, 113], [119, 81], [8, 84], [96, 160], [76, 71], [0, 1]], ![[0, 1], [0, 62], [76, 80], [185, 112], [55, 109], [112, 33], [141, 122], [58, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [134, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [12, 135, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4100, -2914, -1714]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1302, 1468, -1714]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-91, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-91, 1, 0]] 
 ![![193, 0, 0], ![102, 1, 0], ![127, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-91, 1, 0], ![2, -92, 4], ![-92, -32, -89]]]
  hmulB := by decide  
  f := ![![![33846, -2138585, 92988], ![-26827, -4486671, 0]], ![![17928, -1130147, 49140], ![-14088, -2371005, 0]], ![![22234, -1407255, 61189], ![-17733, -2952369, 0]]]
  g := ![![![1, 0, 0], ![-102, 193, 0], ![-127, 0, 193]], ![![-1, 1, 0], ![46, -92, 4], ![75, -32, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-44, -26, 1]] ![![193, 0, 0], ![-91, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-17563, 193, 0]], ![![-8492, -5018, 193], ![3860, 2316, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-91, 1, 0]]], ![![![-44, -26, 1]], ![![20, 12, -1]]]]
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
  g := ![1, 1, 3, 3, 2, 3, 2, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB247I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![2685619]
    · exact ![3307949]
    · exact ![151, 151, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
      exact NI163N1
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
  β := ![I151N0, I151N1, I151N2, I157N0, I157N1, I157N2, I163N1, I167N0, I167N1, I173N1, I181N1, I191N1, I193N1]
  Il := ![[], [], [I151N0, I151N1, I151N2], [I157N0, I157N1, I157N2], [I163N1], [I167N0, I167N1, I167N1], [I173N1], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
