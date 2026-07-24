
import IdealArithmetic.Examples.NF3_1_599427_1.RI3_1_599427_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![28, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![28, 1, 0]] 
 ![![139, 0, 0], ![28, 1, 0], ![50, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![28, 1, 0], ![0, 28, 1], ![149, 0, 28]]]
  hmulB := by decide  
  f := ![![![85, 3, 0], ![-417, 0, 0]], ![![-28, -1, 0], ![140, 0, 0]], ![![6, 0, 0], ![-28, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 139, 0], ![-50, 0, 139]], ![![0, 1, 0], ![-6, 28, 1], ![-9, 0, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![47, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![47, 1, 0]] 
 ![![139, 0, 0], ![47, 1, 0], ![15, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![47, 1, 0], ![0, 47, 1], ![149, 0, 47]]]
  hmulB := by decide  
  f := ![![![2210, 47, 0], ![-6533, 0, 0]], ![![752, 16, 0], ![-2223, 0, 0]], ![![204, 4, 0], ![-603, 1, 0]]]
  g := ![![![1, 0, 0], ![-47, 139, 0], ![-15, 0, 139]], ![![0, 1, 0], ![-16, 47, 1], ![-4, 0, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -2, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![11, -2, 0]] 
 ![![139, 0, 0], ![64, 1, 0], ![74, 0, 1]] where
  M :=![![![11, -2, 0], ![0, 11, -2], ![-298, 0, 11]]]
  hmulB := by decide  
  f := ![![![121, 22, 4]], ![![60, 11, 2]], ![![88, 16, 3]]]
  g := ![![![1, -2, 0], ![-4, 11, -2], ![-8, 0, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![28, 1, 0]] ![![139, 0, 0], ![47, 1, 0]]
  ![![121, 22, 4]] where
 M := ![![![19321, 0, 0], ![6533, 139, 0]], ![![3892, 139, 0], ![1316, 75, 1]]]
 hmul := by decide  
 g := ![![![![1529, -278, 0]], ![![517, -83, -2]]], ![![![308, -45, -2]], ![![102, -13, -1]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![121, 22, 4]] ![![11, -2, 0]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![149, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![149, 0, 0]]]
  hmulB := by decide  
  f := ![![![0, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 0, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![0, 1, 0]]
  ![![0, 0, 1]] where
 M := ![![![0, 0, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  
def MulI149N1 : IdealMulLeCertificate' Table 
  ![![0, 0, 1]] ![![0, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![149, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N0, I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N0
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [2, 6, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 39, 72], [14, 111, 79], [0, 1]]
 g := ![![[7, 145, 22], [120, 21, 72], [59, 24, 32], [34, 148], [90, 24, 36], [0, 1], []], ![[37, 12, 61, 36], [39, 60, 107, 100], [108, 59, 123, 98], [45, 76], [25, 36, 76, 58], [107, 90], [29, 50]], ![[79, 94, 133, 70], [42, 40, 9, 82], [103, 34, 140, 122], [107, 43], [24, 113, 115, 113], [93, 11], [22, 50]]]
 h' := ![![[137, 39, 72], [62, 25, 18], [33, 73, 26], [18, 82, 118], [122, 16, 86], [0, 149, 145], [0, 0, 1], [0, 1]], ![[14, 111, 79], [82, 94, 23], [32, 98, 139], [54, 107, 127], [139, 22, 128], [106, 115, 96], [138, 144, 111], [137, 39, 72]], ![[0, 1], [128, 32, 110], [24, 131, 137], [76, 113, 57], [130, 113, 88], [117, 38, 61], [1, 7, 39], [14, 111, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26, 128], []]
 b := ![[], [36, 84, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [2, 6, 0, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22348, -453, -453]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-148, -3, -3]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![157, 0, 0], ![2, 1, 0], ![153, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![149, 0, 2]]]
  hmulB := by decide  
  f := ![![![4, -2, 1]], ![![1, 0, 0]], ![![2, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 0, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![24, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![24, 1, 0]] 
 ![![157, 0, 0], ![24, 1, 0], ![52, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![24, 1, 0], ![0, 24, 1], ![149, 0, 24]]]
  hmulB := by decide  
  f := ![![![1489, 62, 0], ![-9734, 0, 0]], ![![216, 9, 0], ![-1412, 0, 0]], ![![484, 20, 0], ![-3164, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 157, 0], ![-52, 0, 157]], ![![0, 1, 0], ![-4, 24, 1], ![-7, 0, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-26, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-26, 1, 0]] 
 ![![157, 0, 0], ![131, 1, 0], ![109, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-26, 1, 0], ![0, -26, 1], ![149, 0, -26]]]
  hmulB := by decide  
  f := ![![![3979, -153, 0], ![24021, 0, 0]], ![![3329, -128, 0], ![20097, 0, 0]], ![![2787, -107, 0], ![16825, 1, 0]]]
  g := ![![![1, 0, 0], ![-131, 157, 0], ![-109, 0, 157]], ![![-1, 1, 0], ![21, -26, 1], ![19, 0, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![2, 1, 0]] ![![157, 0, 0], ![24, 1, 0]]
  ![![157, 0, 0], ![48, 26, 1]] where
 M := ![![![314, 157, 0], ![48, 26, 1]]]
 hmul := by decide  
 g := ![![![![-46, -25, -1], ![157, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![48, 26, 1]] ![![157, 0, 0], ![-26, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-4082, 157, 0]], ![![7536, 4082, 157], ![-1099, -628, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-26, 1, 0]]], ![![![48, 26, 1]], ![![-7, -4, 0]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [50, 77, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 85, 53], [68, 77, 110], [0, 1]]
 g := ![![[109, 99, 115], [16, 116, 64], [109, 104], [29, 51], [0, 58], [95, 160, 1], []], ![[0, 9, 74, 51], [14, 145, 64, 43], [63, 39], [127, 69], [143, 87], [97, 28, 160, 136], [94, 38]], ![[152, 120, 121, 52], [48, 39, 21, 67], [135, 4], [87, 16], [121, 43], [117, 17, 125, 125], [37, 38]]]
 h' := ![![[92, 85, 53], [15, 127, 21], [98, 103, 155], [150, 50, 58], [40, 38, 41], [140, 7, 59], [0, 0, 1], [0, 1]], ![[68, 77, 110], [115, 148, 35], [0, 97, 116], [78, 109, 107], [76, 47, 118], [39, 22, 24], [15, 145, 77], [92, 85, 53]], ![[0, 1], [75, 51, 107], [69, 126, 55], [138, 4, 161], [139, 78, 4], [141, 134, 80], [3, 18, 85], [68, 77, 110]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 24], []]
 b := ![[], [115, 132, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [50, 77, 3, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![598210, 5216, -7824]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3670, 32, -48]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![57, 70, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![57, 70, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![57, 70, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![57, 70, 1], ![149, 57, 70], ![10430, 149, 57]]]
  hmulB := by decide  
  f := ![![![-56, -70, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-57, -70, 167]], ![![0, 0, 1], ![-23, -29, 70], ![43, -23, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [33, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 166], [0, 1]]
 g := ![![[65, 81], [83, 144], [144, 87], [124], [61], [162, 8], [1]], ![[0, 86], [153, 23], [68, 80], [124], [61], [36, 159], [1]]]
 h' := ![![[26, 166], [100, 9], [91, 12], [108, 134], [162, 142], [165, 27], [134, 26], [0, 1]], ![[0, 1], [0, 158], [69, 155], [85, 33], [13, 25], [32, 140], [142, 141], [26, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [121, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [33, 141, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5193, 162, -12]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, 6, -12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-70, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-70, 1, 0]] 
 ![![167, 0, 0], ![97, 1, 0], ![110, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-70, 1, 0], ![0, -70, 1], ![149, 0, -70]]]
  hmulB := by decide  
  f := ![![![10781, -154, 0], ![25718, 0, 0]], ![![6371, -91, 0], ![15198, 0, 0]], ![![7170, -102, 0], ![17104, 1, 0]]]
  g := ![![![1, 0, 0], ![-97, 167, 0], ![-110, 0, 167]], ![![-1, 1, 0], ![40, -70, 1], ![47, 0, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![57, 70, 1]] ![![167, 0, 0], ![-70, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-11690, 167, 0]], ![![9519, 11690, 167], ![-3841, -4843, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-70, 1, 0]]], ![![![57, 70, 1]], ![![-23, -29, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![23, 14, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![23, 14, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![23, 14, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![23, 14, 1], ![149, 23, 14], ![2086, 149, 23]]]
  hmulB := by decide  
  f := ![![![-22, -14, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -14, 173]], ![![0, 0, 1], ![-1, -1, 14], ![9, -1, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [97, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 172], [0, 1]]
 g := ![![[44, 40], [106], [92, 167], [75, 90], [140], [97, 135], [1]], ![[75, 133], [106], [96, 6], [15, 83], [140], [7, 38], [1]]]
 h' := ![![[57, 172], [92, 127], [72, 25], [164, 72], [78, 104], [106, 113], [76, 57], [0, 1]], ![[0, 1], [65, 46], [113, 148], [116, 101], [124, 69], [146, 60], [38, 116], [57, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [62, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [97, 116, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-680, 1459, -353]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![43, 37, -353]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-14, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-14, 1, 0]] 
 ![![173, 0, 0], ![159, 1, 0], ![150, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-14, 1, 0], ![0, -14, 1], ![149, 0, -14]]]
  hmulB := by decide  
  f := ![![![1989, -142, 0], ![24566, 0, 0]], ![![1835, -131, 0], ![22664, 0, 0]], ![![1710, -122, 0], ![21120, 1, 0]]]
  g := ![![![1, 0, 0], ![-159, 173, 0], ![-150, 0, 173]], ![![-1, 1, 0], ![12, -14, 1], ![13, 0, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![23, 14, 1]] ![![173, 0, 0], ![-14, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-2422, 173, 0]], ![![3979, 2422, 173], ![-173, -173, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-14, 1, 0]]], ![![![23, 14, 1]], ![![-1, -1, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7054580, -4055331, 1015950]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-7054580, -4055331, 1015950]] 
 ![![179, 0, 0], ![0, 179, 0], ![156, 48, 1]] where
  M :=![![![-7054580, -4055331, 1015950], ![151376550, -7054580, -4055331], ![-604244319, 151376550, -7054580]]]
  hmulB := by decide  
  f := ![![![3707536954550, 699342731880, 131915140059]], ![![19655355868791, 3707536954550, 699342731880]], ![![9083993931072, 1713489362349, 323210893486]]]
  g := ![![![-924820, -295089, 1015950], ![4379934, 1048052, -4055331], ![2772459, 2737410, -7054580]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [178, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 178], [0, 1]]
 g := ![![[25, 108], [55, 149], [61], [172], [19, 147], [102, 88], [1]], ![[40, 71], [21, 30], [61], [172], [114, 32], [154, 91], [1]]]
 h' := ![![[25, 178], [55, 114], [77, 111], [175, 132], [19, 107], [102, 133], [1, 25], [0, 1]], ![[0, 1], [41, 65], [167, 68], [74, 47], [9, 72], [26, 46], [89, 154], [25, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [10, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [178, 154, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![476, -5, -153]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![136, 41, -153]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3707536954550, -699342731880, -131915140059]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-3707536954550, -699342731880, -131915140059]] 
 ![![179, 0, 0], ![131, 1, 0], ![23, 0, 1]] where
  M :=![![![-3707536954550, -699342731880, -131915140059], ![-19655355868791, -3707536954550, -699342731880], ![-104202067050120, -19655355868791, -3707536954550]]]
  hmulB := by decide  
  f := ![![![7054580, 4055331, -1015950]], ![![4317170, 3007279, -720861]], ![![4282121, -324603, -91130]]]
  g := ![![![508046978453, -699342731880, -131915140059], ![2693390324081, -3707536954550, -699342731880], ![14278898892269, -19655355868791, -3707536954550]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-7054580, -4055331, 1015950]] ![![-3707536954550, -699342731880, -131915140059]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [163, 17, 178, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 129, 100], [82, 51, 81], [0, 1]]
 g := ![![[66, 170, 70], [87, 100], [101, 132, 39], [81, 94], [97, 33, 172], [173, 3, 1], []], ![[146, 166, 132, 60], [24, 144], [154, 61, 46, 15], [176, 14], [127, 31, 107, 79], [105, 55, 134, 3], [52, 45]], ![[127, 18, 148, 34], [59, 4], [29, 140, 175, 154], [7, 94], [172, 39, 1, 145], [132, 139, 92, 14], [71, 45]]]
 h' := ![![[102, 129, 100], [1, 42, 34], [8, 107, 10], [124, 124, 138], [117, 133, 53], [37, 9, 124], [0, 0, 1], [0, 1]], ![[82, 51, 81], [152, 67, 142], [156, 17, 169], [96, 16, 71], [27, 165, 75], [21, 65, 165], [118, 178, 51], [102, 129, 100]], ![[0, 1], [31, 72, 5], [112, 57, 2], [151, 41, 153], [5, 64, 53], [57, 107, 73], [38, 3, 129], [82, 51, 81]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 119], []]
 b := ![[], [11, 172, 178], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [163, 17, 178, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2069373, 195480, 74210]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11433, 1080, 410]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![10, 34, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![10, 34, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![10, 34, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![10, 34, 1], ![149, 10, 34], ![5066, 149, 10]]]
  hmulB := by decide  
  f := ![![![-9, -34, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -34, 191]], ![![0, 0, 1], ![-1, -6, 34], ![26, -1, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [157, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 190], [0, 1]]
 g := ![![[177, 34], [1, 5], [34, 49], [101, 125], [114, 136], [177, 50], [1]], ![[37, 157], [104, 186], [12, 142], [2, 66], [127, 55], [61, 141], [1]]]
 h' := ![![[97, 190], [34, 176], [10, 14], [187, 184], [56, 70], [97, 161], [34, 97], [0, 1]], ![[0, 1], [107, 15], [31, 177], [81, 7], [161, 121], [52, 30], [84, 94], [97, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [57, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [157, 94, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-830, 425, -83]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, 17, -83]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-34, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-34, 1, 0]] 
 ![![191, 0, 0], ![157, 1, 0], ![181, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-34, 1, 0], ![0, -34, 1], ![149, 0, -34]]]
  hmulB := by decide  
  f := ![![![4557, -134, 0], ![25594, 0, 0]], ![![3775, -111, 0], ![21202, 0, 0]], ![![4359, -128, 0], ![24482, 1, 0]]]
  g := ![![![1, 0, 0], ![-157, 191, 0], ![-181, 0, 191]], ![![-1, 1, 0], ![27, -34, 1], ![33, 0, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![10, 34, 1]] ![![191, 0, 0], ![-34, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-6494, 191, 0]], ![![1910, 6494, 191], ![-191, -1146, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-34, 1, 0]]], ![![![10, 34, 1]], ![![-1, -6, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [189, 71, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 171, 19], [130, 21, 174], [0, 1]]
 g := ![![[64, 78, 130], [7, 16], [165, 168], [170, 59], [120, 143], [], [1]], ![[115, 45, 43, 80], [169, 14], [20, 1], [173, 107], [0, 31], [72, 4], [61, 39, 106, 104]], ![[24, 112, 144, 73], [30, 63], [162, 131], [107, 84], [97, 161], [174, 4], [134, 96, 162, 89]]]
 h' := ![![[63, 171, 19], [100, 113, 55], [74, 168, 189], [46, 82, 174], [157, 124, 161], [16, 11, 23], [4, 122], [0, 1]], ![[130, 21, 174], [99, 115, 21], [52, 38, 20], [92, 10, 1], [128, 124, 140], [30, 0, 113], [163, 18, 2], [63, 171, 19]], ![[0, 1], [11, 158, 117], [85, 180, 177], [189, 101, 18], [98, 138, 85], [17, 182, 57], [38, 53, 191], [130, 21, 174]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 14], []]
 b := ![[], [101, 137, 111], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [189, 71, 0, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![177946, 965, 1930]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![922, 5, 10]
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



lemma PB220I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB220I3 : PrimesBelowBoundCertificateInterval O 137 193 220 where
  m := 11
  g := ![3, 3, 1, 3, 1, 2, 2, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB220I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N0, I149N0]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
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
    · exact ![139, 139, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
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
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N0
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
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
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N0, I139N1, I139N2, I149N0, I157N0, I157N1, I157N2, I167N1, I173N1, I179N1, I191N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N0, I149N0, I149N0], [], [I157N0, I157N1, I157N2], [], [I167N1], [I173N1], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
