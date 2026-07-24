
import IdealArithmetic.Examples.NF3_1_644799_1.RI3_1_644799_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-36, 69, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-36, 69, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![103, 69, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-36, 69, 1], ![-363, -173, 624], ![-10851, 52, 174]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -69, 139]], ![![-1, 0, 1], ![-465, -311, 624], ![-207, -86, 174]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [29, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 138], [0, 1]]
 g := ![![[96, 24], [69, 52], [118], [5, 86], [7], [16], [1]], ![[0, 115], [0, 87], [118], [78, 53], [7], [16], [1]]]
 h' := ![![[135, 138], [84, 21], [89, 57], [133, 37], [7, 15], [99, 29], [110, 135], [0, 1]], ![[0, 1], [0, 118], [0, 82], [124, 102], [86, 124], [122, 110], [126, 4], [135, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [89, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [29, 4, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5488, -3891, 276]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-244, -165, 276]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-68, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-68, 1, 0]] 
 ![![139, 0, 0], ![71, 1, 0], ![104, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-68, 1, 0], ![-3, -70, 9], ![-156, 1, -65]]]
  hmulB := by decide  
  f := ![![![-5742, -154643, 19881], ![1807, -307051, 0]], ![![-2907, -78967, 10152], ![974, -156792, 0]], ![![-4304, -115704, 14875], ![1336, -229736, 0]]]
  g := ![![![1, 0, 0], ![-71, 139, 0], ![-104, 0, 139]], ![![-1, 1, 0], ![29, -70, 9], ![47, 1, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-36, 69, 1]] ![![139, 0, 0], ![-68, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-9452, 139, 0]], ![![-5004, 9591, 139], ![2085, -4865, 556]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-68, 1, 0]]], ![![![-36, 69, 1]], ![![15, -35, 4]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [109, 103, 112, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 0, 67], [122, 148, 82], [0, 1]]
 g := ![![[91, 112, 145], [73, 103], [75, 64, 35], [98, 132], [47, 18, 112], [37, 1], []], ![[117, 90, 108, 35], [69, 133], [7, 65, 7, 125], [121, 73], [125, 25, 92, 120], [146, 1], [107, 19]], ![[73, 21, 35, 121], [3, 53], [133, 139, 59, 130], [88, 76], [54, 100, 117, 103], [], [92, 19]]]
 h' := ![![[64, 0, 67], [42, 29, 61], [20, 41, 38], [17, 24, 83], [92, 2, 70], [139, 103, 74], [0, 0, 1], [0, 1]], ![[122, 148, 82], [125, 28, 94], [135, 15, 27], [37, 21, 35], [76, 59, 64], [10, 139, 122], [32, 20, 148], [64, 0, 67]], ![[0, 1], [8, 92, 143], [22, 93, 84], [117, 104, 31], [89, 88, 15], [145, 56, 102], [88, 129], [122, 148, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42, 2], []]
 b := ![[], [145, 50, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [109, 103, 112, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7353001, -507196, 21456]
  a := ![-5, -4, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![49349, -3404, 144]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-15, 18, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-15, 18, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![136, 18, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-15, 18, 1], ![-210, -50, 165], ![-2895, 1, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -18, 151]], ![![-1, 0, 1], ![-150, -20, 165], ![-57, -5, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [44, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 150], [0, 1]]
 g := ![![[138, 127], [25, 81], [34, 86], [94], [126, 47], [118], [1]], ![[0, 24], [0, 70], [0, 65], [94], [132, 104], [118], [1]]]
 h' := ![![[119, 150], [108, 60], [14, 142], [129, 122], [43, 68], [66, 97], [107, 119], [0, 1]], ![[0, 1], [0, 91], [0, 9], [0, 29], [132, 83], [133, 54], [74, 32], [119, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [37, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [44, 32, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-369565, -76415, 10796]
  a := ![1, 1, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12171, -1793, 10796]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-14, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-14, 1, 0]] 
 ![![151, 0, 0], ![137, 1, 0], ![109, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-14, 1, 0], ![-3, -16, 9], ![-156, 1, -11]]]
  hmulB := by decide  
  f := ![![![8107, 43459, -24444], ![-453, 410116, 0]], ![![7365, 39426, -22176], ![-301, 372064, 0]], ![![5853, 31371, -17645], ![-317, 296044, 0]]]
  g := ![![![1, 0, 0], ![-137, 151, 0], ![-109, 0, 151]], ![![-1, 1, 0], ![8, -16, 9], ![6, 1, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-15, 18, 1]] ![![151, 0, 0], ![-14, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-2114, 151, 0]], ![![-2265, 2718, 151], ![0, -302, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-14, 1, 0]]], ![![![-15, 18, 1]], ![![0, -2, 1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![24, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![24, 1, 0]] 
 ![![157, 0, 0], ![24, 1, 0], ![98, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![24, 1, 0], ![-3, 22, 9], ![-156, 1, 27]]]
  hmulB := by decide  
  f := ![![![6577, -49109, -20088], ![785, 350424, 0]], ![![999, -7503, -3069], ![158, 53537, 0]], ![![4106, -30654, -12539], ![486, 218736, 0]]]
  g := ![![![1, 0, 0], ![-24, 157, 0], ![-98, 0, 157]], ![![0, 1, 0], ![-9, 22, 9], ![-18, 1, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![66, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![66, 1, 0]] 
 ![![157, 0, 0], ![66, 1, 0], ![106, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![66, 1, 0], ![-3, 64, 9], ![-156, 1, 69]]]
  hmulB := by decide  
  f := ![![![15607, -370971, -52164], ![4239, 909972, 0]], ![![6516, -155916, -21924], ![1885, 382452, 0]], ![![10504, -250465, -35219], ![2941, 614376, 0]]]
  g := ![![![1, 0, 0], ![-66, 157, 0], ![-106, 0, 157]], ![![0, 1, 0], ![-33, 64, 9], ![-48, 1, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![24, 1, 0]] ![![157, 0, 0], ![66, 1, 0]]
  ![![157, 0, 0], ![71, -60, 1]] where
 M := ![![![24649, 0, 0], ![10362, 157, 0]], ![![3768, 157, 0], ![1581, 88, 9]]]
 hmul := by decide  
 g := ![![![![86, 60, -1], ![157, 0, 0]], ![![-5, 61, -1], ![157, 0, 0]]], ![![![-47, 61, -1], ![157, 0, 0]], ![![6, 4, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![71, -60, 1]] ![![157, 0, 0], ![66, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![10362, 157, 0]], ![![11147, -9420, 157], ![4710, -3768, -471]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![66, 1, 0]]], ![![![71, -60, 1]], ![![30, -24, -3]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-72, -38, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-72, -38, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![91, 125, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-72, -38, 1], ![-42, 5, -339], ![5841, -55, -183]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -125, 163]], ![![-1, -1, 1], ![189, 260, -339], ![138, 140, -183]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [148, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 162], [0, 1]]
 g := ![![[104, 104], [159, 146], [26], [95], [133], [134, 10], [1]], ![[159, 59], [45, 17], [26], [95], [133], [86, 153], [1]]]
 h' := ![![[93, 162], [103, 58], [14, 132], [73, 29], [21, 62], [54, 123], [15, 93], [0, 1]], ![[0, 1], [118, 105], [65, 31], [162, 134], [82, 101], [83, 40], [25, 70], [93, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [162, 149]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [148, 70, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2988, -6630, -855]
  a := ![7, 5, -20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![459, 615, -855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![13, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![13, 1, 0]] 
 ![![163, 0, 0], ![13, 1, 0], ![20, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![13, 1, 0], ![-3, 11, 9], ![-156, 1, 16]]]
  hmulB := by decide  
  f := ![![![55631, -204950, -167670], ![3260, 3036690, 0]], ![![4429, -16337, -13365], ![327, 242055, 0]], ![![6816, -25148, -20573], ![524, 372600, 0]]]
  g := ![![![1, 0, 0], ![-13, 163, 0], ![-20, 0, 163]], ![![0, 1, 0], ![-2, 11, 9], ![-3, 1, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-72, -38, 1]] ![![163, 0, 0], ![13, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![2119, 163, 0]], ![![-11736, -6194, 163], ![-978, -489, -326]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![13, 1, 0]]], ![![![-72, -38, 1]], ![![-6, -3, -2]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-54, 56, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-54, 56, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![113, 56, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-54, 56, 1], ![-324, -165, 507], ![-8823, 39, 117]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -56, 167]], ![![-1, 0, 1], ![-345, -171, 507], ![-132, -39, 117]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [17, 147, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [20, 166], [0, 1]]
 g := ![![[156, 57], [95, 7], [159, 108], [116], [76], [139, 66], [1]], ![[127, 110], [68, 160], [148, 59], [116], [76], [123, 101], [1]]]
 h' := ![![[20, 166], [55, 70], [136, 95], [33, 38], [1, 28], [142, 110], [150, 20], [0, 1]], ![[0, 1], [119, 97], [32, 72], [125, 129], [60, 139], [4, 57], [49, 147], [20, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [157, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [17, 147, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4785, -3462, -1869]
  a := ![5, 3, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1236, 606, -1869]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-6, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-6, 1, 0]] 
 ![![167, 0, 0], ![161, 1, 0], ![50, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-6, 1, 0], ![-3, -8, 9], ![-156, 1, -3]]]
  hmulB := by decide  
  f := ![![![49177, 131221, -147618], ![-835, 2739134, 0]], ![![47407, 126501, -142308], ![-834, 2640604, 0]], ![![14728, 39287, -44197], ![-129, 820100, 0]]]
  g := ![![![1, 0, 0], ![-161, 167, 0], ![-50, 0, 167]], ![![-1, 1, 0], ![5, -8, 9], ![-1, 1, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-54, 56, 1]] ![![167, 0, 0], ![-6, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-1002, 167, 0]], ![![-9018, 9352, 167], ![0, -501, 501]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-6, 1, 0]]], ![![![-54, 56, 1]], ![![0, -3, 3]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-68, 11, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-68, 11, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![105, 11, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-68, 11, 1], ![-189, -89, 102], ![-1803, -6, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -11, 173]], ![![-1, 0, 1], ![-63, -7, 102], ![9, 2, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [4, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 172], [0, 1]]
 g := ![![[61, 130], [158], [60, 56], [83, 78], [34], [75, 24], [1]], ![[0, 43], [158], [63, 117], [81, 95], [34], [101, 149], [1]]]
 h' := ![![[102, 172], [51, 86], [106, 37], [14, 70], [77, 123], [46, 131], [169, 102], [0, 1]], ![[0, 1], [0, 87], [74, 136], [61, 103], [167, 50], [87, 42], [20, 71], [102, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [56, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [4, 71, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-527813, -267251, 33109]
  a := ![-41, -21, 124]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-23146, -3650, 33109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![71, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![71, 1, 0]] 
 ![![173, 0, 0], ![71, 1, 0], ![32, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![71, 1, 0], ![-3, 69, 9], ![-156, 1, 74]]]
  hmulB := by decide  
  f := ![![![14000, -357925, -46683], ![3806, 897351, 0]], ![![5745, -146841, -19152], ![1558, 368144, 0]], ![![2574, -66206, -8635], ![742, 165984, 0]]]
  g := ![![![1, 0, 0], ![-71, 173, 0], ![-32, 0, 173]], ![![0, 1, 0], ![-30, 69, 9], ![-15, 1, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-68, 11, 1]] ![![173, 0, 0], ![71, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![12283, 173, 0]], ![![-11764, 1903, 173], ![-5017, 692, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![71, 1, 0]]], ![![![-68, 11, 1]], ![![-29, 4, 1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![21, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![21, 1, 0]] 
 ![![179, 0, 0], ![21, 1, 0], ![15, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![21, 1, 0], ![-3, 19, 9], ![-156, 1, 24]]]
  hmulB := by decide  
  f := ![![![13462, -86191, -40824], ![1253, 811944, 0]], ![![1575, -10109, -4788], ![180, 95228, 0]], ![![1122, -7223, -3421], ![157, 68040, 0]]]
  g := ![![![1, 0, 0], ![-21, 179, 0], ![-15, 0, 179]], ![![0, 1, 0], ![-3, 19, 9], ![-3, 1, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![60, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![60, 1, 0]] 
 ![![179, 0, 0], ![60, 1, 0], ![150, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![60, 1, 0], ![-3, 58, 9], ![-156, 1, 63]]]
  hmulB := by decide  
  f := ![![![-1478, 29755, 4617], ![-179, -91827, 0]], ![![-513, 9918, 1539], ![1, -30609, 0]], ![![-1260, 24934, 3869], ![-86, -76950, 0]]]
  g := ![![![1, 0, 0], ![-60, 179, 0], ![-150, 0, 179]], ![![0, 1, 0], ![-27, 58, 9], ![-54, 1, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-82, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-82, 1, 0]] 
 ![![179, 0, 0], ![97, 1, 0], ![10, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-82, 1, 0], ![-3, -84, 9], ![-156, 1, -79]]]
  hmulB := by decide  
  f := ![![![999, 30241, -3240], ![-179, 64440, 0]], ![![586, 16380, -1755], ![1, 34905, 0]], ![![92, 1689, -181], ![69, 3600, 0]]]
  g := ![![![1, 0, 0], ![-97, 179, 0], ![-10, 0, 179]], ![![-1, 1, 0], ![45, -84, 9], ![3, 1, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![21, 1, 0]] ![![179, 0, 0], ![60, 1, 0]]
  ![![179, 0, 0], ![80, -31, 1]] where
 M := ![![![32041, 0, 0], ![10740, 179, 0]], ![![3759, 179, 0], ![1257, 79, 9]]]
 hmul := by decide  
 g := ![![![![99, 31, -1], ![179, 0, 0]], ![![-20, 32, -1], ![179, 0, 0]]], ![![![-59, 32, -1], ![179, 0, 0]], ![![3, 2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![80, -31, 1]] ![![179, 0, 0], ![-82, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-14678, 179, 0]], ![![14320, -5549, 179], ![-6623, 2685, -358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-82, 1, 0]]], ![![![80, -31, 1]], ![![-37, 15, -2]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-84, -47, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-84, -47, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![97, 134, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-84, -47, 1], ![-15, 11, -420], ![7245, -64, -222]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -134, 181]], ![![-1, -1, 1], ![225, 311, -420], ![159, 164, -222]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [103, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 180], [0, 1]]
 g := ![![[85, 79], [48], [91, 4], [170], [165, 135], [105, 145], [1]], ![[41, 102], [48], [4, 177], [170], [170, 46], [164, 36], [1]]]
 h' := ![![[114, 180], [16, 21], [39, 132], [46, 179], [19, 52], [45, 42], [78, 114], [0, 1]], ![[0, 1], [57, 160], [64, 49], [180, 2], [155, 129], [127, 139], [42, 67], [114, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [160]]
 b := ![[], [146, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [103, 67, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3164, -1167, 641]
  a := ![-3, -1, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-361, -481, 641]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![58, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![58, 1, 0]] 
 ![![181, 0, 0], ![58, 1, 0], ![41, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![58, 1, 0], ![-3, 56, 9], ![-156, 1, 61]]]
  hmulB := by decide  
  f := ![![![17323, -346101, -55620], ![3801, 1118580, 0]], ![![5534, -110887, -17820], ![1268, 358380, 0]], ![![3899, -78399, -12599], ![939, 253380, 0]]]
  g := ![![![1, 0, 0], ![-58, 181, 0], ![-41, 0, 181]], ![![0, 1, 0], ![-20, 56, 9], ![-15, 1, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-84, -47, 1]] ![![181, 0, 0], ![58, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![10498, 181, 0]], ![![-15204, -8507, 181], ![-4887, -2715, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![58, 1, 0]]], ![![![-84, -47, 1]], ![![-27, -15, -2]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [77, 124, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 18, 31], [22, 172, 160], [0, 1]]
 g := ![![[116, 117, 24], [173, 34, 40], [111, 164, 136], [61, 116, 65], [183, 22, 135], [163, 67, 1], []], ![[44, 147, 179, 84], [14, 184, 139, 62], [171, 32, 106, 174], [39, 160, 34, 73], [93, 165, 127, 99], [15, 152, 172, 113], [181, 6]], ![[106, 176, 143, 100], [37, 77, 76, 1], [134, 21, 158, 170], [61, 18, 148, 23], [165, 4, 115, 121], [23, 169, 159, 79], [52, 6]]]
 h' := ![![[45, 18, 31], [49, 8, 62], [48, 129, 123], [78, 60, 161], [43, 31, 175], [55, 32, 53], [0, 0, 1], [0, 1]], ![[22, 172, 160], [80, 31, 25], [108, 80, 134], [103, 1, 138], [75, 8, 119], [77, 82, 176], [121, 106, 172], [45, 18, 31]], ![[0, 1], [107, 152, 104], [58, 173, 125], [38, 130, 83], [127, 152, 88], [42, 77, 153], [109, 85, 18], [22, 172, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 58], []]
 b := ![[], [105, 98, 146], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [77, 124, 124, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![34714823, -1788142, -424593]
  a := ![-8, -5, 24]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![181753, -9362, -2223]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![95, -11, 7]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![95, -11, 7]] 
 ![![193, 0, 0], ![19, 1, 0], ![71, 0, 1]] where
  M :=![![![95, -11, 7], ![-1059, 124, -78], ![1107, -130, 83]]]
  hmulB := by decide  
  f := ![![![152, 3, -10]], ![![23, 1, -1]], ![![58, 2, -3]]]
  g := ![![![-1, -11, 7], ![11, 124, -78], ![-12, -130, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![63, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![63, 1, 0]] 
 ![![193, 0, 0], ![63, 1, 0], ![23, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![63, 1, 0], ![-3, 61, 9], ![-156, 1, 66]]]
  hmulB := by decide  
  f := ![![![40735, -887230, -130896], ![8878, 2806992, 0]], ![![13296, -289582, -42723], ![2896, 916171, 0]], ![![4859, -105732, -15599], ![1044, 334512, 0]]]
  g := ![![![1, 0, 0], ![-63, 193, 0], ![-23, 0, 193]], ![![0, 1, 0], ![-21, 61, 9], ![-9, 1, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-83, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-83, 1, 0]] 
 ![![193, 0, 0], ![110, 1, 0], ![95, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-83, 1, 0], ![-3, -85, 9], ![-156, 1, -80]]]
  hmulB := by decide  
  f := ![![![48091, 1517826, -160704], ![-12738, 3446208, 0]], ![![27458, 864997, -91584], ![-7140, 1963968, 0]], ![![23707, 747116, -79103], ![-6188, 1696320, 0]]]
  g := ![![![1, 0, 0], ![-110, 193, 0], ![-95, 0, 193]], ![![-1, 1, 0], ![44, -85, 9], ![38, 1, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![95, -11, 7]] ![![193, 0, 0], ![63, 1, 0]]
  ![![193, 0, 0], ![4, -34, 1]] where
 M := ![![![18335, -2123, 1351], ![4926, -569, 363]]]
 hmul := by decide  
 g := ![![![![91, 23, 6], ![193, 0, 0]], ![![22, 27, 1], ![170, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![4, -34, 1]] ![![193, 0, 0], ![-83, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-16019, 193, 0]], ![![772, -6562, 193], ![-386, 2895, -386]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-83, 1, 0]]], ![![![4, -34, 1]], ![![-2, 15, -2]]]]
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


lemma PB228I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB228I3 : PrimesBelowBoundCertificateInterval O 137 193 228 where
  m := 11
  g := ![2, 1, 2, 3, 2, 2, 2, 3, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB228I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![6967871]
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
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
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
      exact NI179N2
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
      exact NI193N2
  β := ![I139N1, I151N1, I157N0, I157N1, I163N1, I167N1, I173N1, I179N0, I179N1, I179N2, I181N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [], [I151N1], [I157N0, I157N1, I157N1], [I163N1], [I167N1], [I173N1], [I179N0, I179N1, I179N2], [I181N1], [], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
