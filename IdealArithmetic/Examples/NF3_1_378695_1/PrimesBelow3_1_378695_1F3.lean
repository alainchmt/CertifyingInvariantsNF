
import IdealArithmetic.Examples.NF3_1_378695_1.RI3_1_378695_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6006, 2258, -255]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-6006, 2258, -255]] 
 ![![139, 0, 0], ![18, 1, 0], ![93, 0, 1]] where
  M :=![![![-6006, 2258, -255], ![47175, -17736, 2003], ![-370555, 139313, -15733]]]
  hmulB := by decide  
  f := ![![![3451, -299, -94]], ![![572, -45, -15]], ![![2832, -205, -72]]]
  g := ![![![-165, 2258, -255], ![1296, -17736, 2003], ![-10180, 139313, -15733]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-619, 94, 22]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-619, 94, 22]] 
 ![![139, 0, 0], ![121, 1, 0], ![93, 0, 1]] where
  M :=![![![-619, 94, 22], ![-4070, 393, 116], ![-21460, 1266, 509]]]
  hmulB := by decide  
  f := ![![![-53181, 19994, -2258]], ![![-43289, 16275, -1838]], ![![-59187, 22252, -2513]]]
  g := ![![![-101, 94, 22], ![-449, 393, 116], ![-1597, 1266, 509]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![139, 0, 0], ![138, 1, 0], ![138, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![-185, 46, 0]]]
  hmulB := by decide  
  f := ![![![46, 0, -1]], ![![47, 0, -1]], ![![47, 1, -1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![-47, 46, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-6006, 2258, -255]] ![![-619, 94, 22]]
  ![![-46, 0, 1]] where
 M := ![![![-46, 0, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-46, 0, 1]] ![![-1, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [49, 118, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 107, 30], [138, 41, 119], [0, 1]]
 g := ![![[99, 60, 95], [25, 31], [36, 84, 69], [12, 5], [97, 63, 114], [55, 1], []], ![[130, 27, 8, 88], [146, 20], [133, 21, 90, 17], [115, 45], [50, 30, 69, 53], [54, 42], [45, 6]], ![[78, 0, 128, 121], [71, 22], [86, 94, 26, 35], [3, 20], [148, 137, 26, 73], [54, 125], [105, 6]]]
 h' := ![![[66, 107, 30], [96, 95, 63], [24, 33, 110], [84, 115, 48], [15, 89, 68], [136, 17, 76], [0, 0, 1], [0, 1]], ![[138, 41, 119], [31, 95, 69], [114, 94, 136], [66, 42, 54], [28, 35, 94], [89, 146, 50], [65, 27, 41], [66, 107, 30]], ![[0, 1], [58, 108, 17], [109, 22, 52], [90, 141, 47], [104, 25, 136], [12, 135, 23], [42, 122, 107], [138, 41, 119]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 138], []]
 b := ![[], [105, 117, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [49, 118, 94, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-42316, 2831, 2831]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-284, 19, 19]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-656, 50, 17]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-656, 50, 17]] 
 ![![151, 0, 0], ![0, 151, 0], ![68, 74, 1]] where
  M :=![![![-656, 50, 17], ![-3145, 126, 67], ![-12395, -63, 193]]]
  hmulB := by decide  
  f := ![![![189, -71, 8]], ![![-1480, 557, -63]], ![![-563, 212, -24]]]
  g := ![![![-12, -8, 17], ![-51, -32, 67], ![-169, -95, 193]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [43, 142, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 150], [0, 1]]
 g := ![![[63, 144], [150, 84], [130, 103], [97], [91, 62], [81], [1]], ![[0, 7], [0, 67], [0, 48], [97], [45, 89], [81], [1]]]
 h' := ![![[9, 150], [43, 12], [148, 101], [75, 42], [13, 90], [27, 106], [108, 9], [0, 1]], ![[0, 1], [0, 139], [0, 50], [0, 109], [68, 61], [75, 45], [38, 142], [9, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10]]
 b := ![[], [53, 5]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [43, 142, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![457, -2083, 835]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-373, -423, 835]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-189, 71, -8]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-189, 71, -8]] 
 ![![151, 0, 0], ![76, 1, 0], ![113, 0, 1]] where
  M :=![![![-189, 71, -8], ![1480, -557, 63], ![-11655, 4378, -494]]]
  hmulB := by decide  
  f := ![![![656, -50, -17]], ![![351, -26, -9]], ![![573, -37, -14]]]
  g := ![![![-31, 71, -8], ![243, -557, 63], ![-1911, 4378, -494]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-656, 50, 17]] ![![-189, 71, -8]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1603, -8, -27]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![1603, -8, -27]] 
 ![![157, 0, 0], ![25, 1, 0], ![3, 0, 1]] where
  M :=![![![1603, -8, -27], ![4995, 361, -35], ![6475, 3385, 326]]]
  hmulB := by decide  
  f := ![![![-236161, 88787, -10027]], ![![-25790, 9696, -1095]], ![![-97319, 36588, -4132]]]
  g := ![![![12, -8, -27], ![-25, 361, -35], ![-504, 3385, 326]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15898, -5977, 675]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![15898, -5977, 675]] 
 ![![157, 0, 0], ![138, 1, 0], ![110, 0, 1]] where
  M :=![![![15898, -5977, 675], ![-124875, 46948, -5302], ![980870, -368767, 41646]]]
  hmulB := by decide  
  f := ![![![-6226, 417, 154]], ![![-5654, 372, 139]], ![![-5035, 278, 117]]]
  g := ![![![4882, -5977, 675], ![-38347, 46948, -5302], ![301208, -368767, 41646]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-7, 1, 0]] 
 ![![157, 0, 0], ![150, 1, 0], ![108, 0, 1]] where
  M :=![![![-7, 1, 0], ![0, -7, 1], ![-185, 46, -6]]]
  hmulB := by decide  
  f := ![![![4, -6, -1]], ![![5, -6, -1]], ![![11, -5, -1]]]
  g := ![![![-1, 1, 0], ![6, -7, 1], ![-41, 46, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![1603, -8, -27]] ![![15898, -5977, 675]]
  ![![4, -6, -1]] where
 M := ![![![4, -6, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![4, -6, -1]] ![![-7, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-916, -745, -80]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-916, -745, -80]] 
 ![![163, 0, 0], ![0, 163, 0], ![150, 101, 1]] where
  M :=![![![-916, -745, -80], ![14800, -4596, -825], ![152625, -23150, -5421]]]
  hmulB := by decide  
  f := ![![![35682, -13415, 1515]], ![![-280275, 105372, -11900]], ![![-127325, 47869, -5406]]]
  g := ![![![68, 45, -80], ![850, 483, -825], ![5925, 3217, -5421]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [32, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 162], [0, 1]]
 g := ![![[123, 91], [91, 35], [10], [95], [53], [100, 87], [1]], ![[58, 72], [66, 128], [10], [95], [53], [131, 76], [1]]]
 h' := ![![[139, 162], [22, 108], [106, 19], [153, 93], [111, 101], [60, 78], [131, 139], [0, 1]], ![[0, 1], [38, 55], [139, 144], [40, 70], [132, 62], [144, 85], [55, 24], [139, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [16]]
 b := ![[], [96, 8]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [32, 24, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2777, -335, 150]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -95, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35682, 13415, -1515]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-35682, 13415, -1515]] 
 ![![163, 0, 0], ![61, 1, 0], ![28, 0, 1]] where
  M :=![![![-35682, 13415, -1515], ![280275, -105372, 11900], ![-2201500, 827675, -93472]]]
  hmulB := by decide  
  f := ![![![916, 745, 80]], ![![252, 307, 35]], ![![-779, 270, 47]]]
  g := ![![![-4979, 13415, -1515], ![39109, -105372, 11900], ![-307193, 827675, -93472]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-916, -745, -80]] ![![-35682, 13415, -1515]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [108, 41, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [139, 28, 65], [87, 138, 102], [0, 1]]
 g := ![![[25, 59, 54], [84, 122, 89], [72, 75, 9], [34, 97], [17, 87], [100, 59, 1], []], ![[137, 37, 94, 127], [5, 132, 11, 61], [121, 33, 99, 81], [104, 152], [16, 76], [94, 16, 25, 56], [77, 50]], ![[107, 105, 117, 82], [14, 106, 90, 131], [126, 30, 72, 119], [28, 87], [94, 84], [158, 78, 67, 142], [40, 50]]]
 h' := ![![[139, 28, 65], [113, 65, 80], [73, 85, 16], [68, 76, 164], [20, 140, 127], [55, 49, 33], [0, 0, 1], [0, 1]], ![[87, 138, 102], [106, 100, 68], [93, 32, 51], [162, 105, 17], [120, 104, 73], [126, 78, 57], [150, 62, 138], [139, 28, 65]], ![[0, 1], [158, 2, 19], [0, 50, 100], [106, 153, 153], [142, 90, 134], [146, 40, 77], [76, 105, 28], [87, 138, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 33], []]
 b := ![[], [19, 23, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [108, 41, 108, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-754172, 234468, -8183]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4516, 1404, -49]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-60, -70, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-60, -70, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![113, 103, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-60, -70, 1], ![-185, -14, -69], ![12765, -3359, -83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -103, 173]], ![![-1, -1, 1], ![44, 41, -69], ![128, 30, -83]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [32, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 172], [0, 1]]
 g := ![![[105, 52], [49], [42, 138], [162, 90], [160], [61, 139], [1]], ![[115, 121], [49], [2, 35], [166, 83], [160], [121, 34], [1]]]
 h' := ![![[100, 172], [32, 15], [40, 166], [6, 151], [49, 104], [124, 81], [141, 100], [0, 1]], ![[0, 1], [148, 158], [32, 7], [55, 22], [69, 69], [93, 92], [107, 73], [100, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [72, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [32, 73, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-523, -120, -23]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![12, 13, -23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![69, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![69, 1, 0]] 
 ![![173, 0, 0], ![69, 1, 0], ![83, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![69, 1, 0], ![0, 69, 1], ![-185, 46, 70]]]
  hmulB := by decide  
  f := ![![![3727, 54, 0], ![-9342, 0, 0]], ![![1449, 21, 0], ![-3632, 0, 0]], ![![1753, 25, 0], ![-4394, 1, 0]]]
  g := ![![![1, 0, 0], ![-69, 173, 0], ![-83, 0, 173]], ![![0, 1, 0], ![-28, 69, 1], ![-53, 46, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-60, -70, 1]] ![![173, 0, 0], ![69, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![11937, 173, 0]], ![![-10380, -12110, 173], ![-4325, -4844, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![69, 1, 0]]], ![![![-60, -70, 1]], ![![-25, -28, 0]]]]
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


lemma PB175I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 174 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 174 (by omega)

def PB175I3 : PrimesBelowBoundCertificateInterval O 137 174 175 where
  m := 7
  g := ![3, 1, 2, 3, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB175I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
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
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I139N0, I139N1, I139N2, I151N1, I157N0, I157N1, I157N2, I163N1, I173N1]
  Il := ![[I139N0, I139N1, I139N2], [], [I151N1], [I157N0, I157N1, I157N2], [I163N1], [], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
