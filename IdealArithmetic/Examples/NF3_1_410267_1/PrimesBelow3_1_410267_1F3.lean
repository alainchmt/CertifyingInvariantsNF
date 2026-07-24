
import IdealArithmetic.Examples.NF3_1_410267_1.RI3_1_410267_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![19, -9, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![19, -9, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![19, 130, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![19, -9, 1], ![99, -3, -46], ![-1105, 143, 15]]]
  hmulB := by decide  
  f := ![![![-18, 9, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-19, -130, 139]], ![![0, -1, 1], ![7, 43, -46], ![-10, -13, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [93, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 138], [0, 1]]
 g := ![![[90, 122], [101, 63], [46], [66, 117], [57], [66], [1]], ![[44, 17], [18, 76], [46], [31, 22], [57], [66], [1]]]
 h' := ![![[109, 138], [59, 20], [98, 52], [117, 18], [62, 123], [9, 125], [46, 109], [0, 1]], ![[0, 1], [15, 119], [67, 87], [133, 121], [125, 16], [12, 14], [112, 30], [109, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [11, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [93, 30, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1085, 342, -455]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, 428, -455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![46, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![46, 1, 0]] 
 ![![139, 0, 0], ![46, 1, 0], ![124, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![46, 1, 0], ![2, 47, 5], ![117, -13, 45]]]
  hmulB := by decide  
  f := ![![![4839, 134213, 14280], ![2641, -396984, 0]], ![![1568, 44408, 4725], ![974, -131355, 0]], ![![4336, 119730, 12739], ![2298, -354144, 0]]]
  g := ![![![1, 0, 0], ![-46, 139, 0], ![-124, 0, 139]], ![![0, 1, 0], ![-20, 47, 5], ![-35, -13, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![19, -9, 1]] ![![139, 0, 0], ![46, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![6394, 139, 0]], ![![2641, -1251, 139], ![973, -417, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![46, 1, 0]]], ![![![19, -9, 1]], ![![7, -3, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-64, 4, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-64, 4, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![85, 4, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-64, 4, 1], ![125, -73, 19], ![416, -26, -81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -4, 149]], ![![-1, 0, 1], ![-10, -1, 19], ![49, 2, -81]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [45, 20, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 148], [0, 1]]
 g := ![![[17, 53], [9], [52, 37], [16], [81, 86], [102], [1]], ![[0, 96], [9], [57, 112], [16], [0, 63], [102], [1]]]
 h' := ![![[129, 148], [41, 84], [44, 3], [18, 22], [80, 4], [117, 58], [104, 129], [0, 1]], ![[0, 1], [0, 65], [133, 146], [25, 127], [0, 145], [0, 91], [57, 20], [129, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [27, 107]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [45, 20, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8618, 4394, -1807]
  a := ![5, 0, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![973, 78, -1807]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-19, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-19, 1, 0]] 
 ![![149, 0, 0], ![130, 1, 0], ![81, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-19, 1, 0], ![2, -18, 5], ![117, -13, -20]]]
  hmulB := by decide  
  f := ![![![-356, 3383, -940], ![149, 28012, 0]], ![![-308, 2951, -820], ![150, 24436, 0]], ![![-192, 1839, -511], ![93, 15228, 0]]]
  g := ![![![1, 0, 0], ![-130, 149, 0], ![-81, 0, 149]], ![![-1, 1, 0], ![13, -18, 5], ![23, -13, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-64, 4, 1]] ![![149, 0, 0], ![-19, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-2831, 149, 0]], ![![-9536, 596, 149], ![1341, -149, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-19, 1, 0]]], ![![![-64, 4, 1]], ![![9, -1, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-69, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-69, 1, 0]] 
 ![![151, 0, 0], ![82, 1, 0], ![119, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-69, 1, 0], ![2, -68, 5], ![117, -13, -70]]]
  hmulB := by decide  
  f := ![![![-2955, 138024, -10150], ![2416, 306530, 0]], ![![-1582, 74927, -5510], ![1360, 166402, 0]], ![![-2337, 108774, -7999], ![1886, 241570, 0]]]
  g := ![![![1, 0, 0], ![-82, 151, 0], ![-119, 0, 151]], ![![-1, 1, 0], ![33, -68, 5], ![63, -13, -70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-13, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-13, 1, 0]] 
 ![![151, 0, 0], ![138, 1, 0], ![90, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-13, 1, 0], ![2, -12, 5], ![117, -13, -14]]]
  hmulB := by decide  
  f := ![![![-12036, 73069, -30450], ![1661, 919590, 0]], ![![-10999, 66770, -27825], ![1511, 840315, 0]], ![![-7173, 43551, -18149], ![999, 548100, 0]]]
  g := ![![![1, 0, 0], ![-138, 151, 0], ![-90, 0, 151]], ![![-1, 1, 0], ![8, -12, 5], ![21, -13, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-69, 1, 0]] ![![151, 0, 0], ![-69, 1, 0]]
  ![![151, 0, 0], ![-44, 33, 1]] where
 M := ![![![22801, 0, 0], ![-10419, 151, 0]], ![![-10419, 151, 0], ![4763, -137, 5]]]
 hmul := by decide  
 g := ![![![![151, 0, 0], ![0, 0, 0]], ![![-25, -32, -1], ![151, 0, 0]]], ![![![-25, -32, -1], ![151, 0, 0]], ![![33, -2, 0], ![5, 0, 0]]]]
 hle2 := by decide  
def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-44, 33, 1]] ![![151, 0, 0], ![-13, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-1963, 151, 0]], ![![-6644, 4983, 151], ![755, -453, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-13, 1, 0]]], ![![![-44, 33, 1]], ![![5, -3, 1]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-26, 79, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-26, 79, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![131, 79, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-26, 79, 1], ![275, 40, 394], ![9191, -1001, -118]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-131, -79, 157]], ![![-1, 0, 1], ![-327, -198, 394], ![157, 53, -118]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [20, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [131, 156], [0, 1]]
 g := ![![[17, 153], [19], [103, 106], [143, 36], [13, 89], [48], [1]], ![[121, 4], [19], [16, 51], [149, 121], [54, 68], [48], [1]]]
 h' := ![![[131, 156], [138, 56], [138, 126], [123, 48], [54, 151], [68, 106], [137, 131], [0, 1]], ![[0, 1], [95, 101], [2, 31], [131, 109], [53, 6], [138, 51], [28, 26], [131, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [148, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [20, 26, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1082832, 249482, -212403]
  a := ![-66, -64, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![184125, 108467, -212403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![77, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![77, 1, 0]] 
 ![![157, 0, 0], ![77, 1, 0], ![118, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![77, 1, 0], ![2, 78, 5], ![117, -13, 76]]]
  hmulB := by decide  
  f := ![![![-13722, -754343, -48360], ![-11461, 1518504, 0]], ![![-6791, -369919, -23715], ![-5494, 744651, 0]], ![![-10357, -566959, -36347], ![-8525, 1141296, 0]]]
  g := ![![![1, 0, 0], ![-77, 157, 0], ![-118, 0, 157]], ![![0, 1, 0], ![-42, 78, 5], ![-50, -13, 76]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-26, 79, 1]] ![![157, 0, 0], ![77, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![12089, 157, 0]], ![![-4082, 12403, 157], ![-1727, 6123, 471]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![77, 1, 0]]], ![![![-26, 79, 1]], ![![-11, 39, 3]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [67, 21, 3, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [13, 114, 65], [147, 48, 98], [0, 1]]
 g := ![![[29, 65, 21], [124, 84, 113], [112, 160], [140, 152], [3, 46], [151, 160, 1], []], ![[63, 136, 87, 6], [39, 39, 71, 36], [69, 9], [132, 93], [18, 121], [97, 51, 41, 126], [26, 150]], ![[39, 61, 48, 142], [154, 68, 50, 92], [37, 56], [156, 113], [48, 56], [10, 153, 15, 89], [156, 150]]]
 h' := ![![[13, 114, 65], [5, 162, 99], [154, 71, 73], [117, 29, 117], [83, 92, 106], [152, 127, 32], [0, 0, 1], [0, 1]], ![[147, 48, 98], [93, 149, 123], [22, 105, 132], [154, 16, 3], [149, 33, 147], [41, 84, 11], [57, 29, 48], [13, 114, 65]], ![[0, 1], [76, 15, 104], [109, 150, 121], [44, 118, 43], [155, 38, 73], [130, 115, 120], [73, 134, 114], [147, 48, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101, 79], []]
 b := ![[], [119, 88, 69], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [67, 21, 3, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7349833, 1359420, -244174]
  a := ![-5, -1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45091, 8340, -1498]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-3, -46, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-3, -46, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![164, 121, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-3, -46, 1], ![25, -62, -231], ![-5434, 624, 30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-164, -121, 167]], ![![-1, -1, 1], ![227, 167, -231], ![-62, -18, 30]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [19, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 166], [0, 1]]
 g := ![![[1, 44], [85, 66], [147, 122], [147], [32], [42, 27], [1]], ![[0, 123], [0, 101], [0, 45], [147], [32], [30, 140], [1]]]
 h' := ![![[148, 166], [55, 82], [46, 20], [11, 150], [93, 67], [37, 52], [148, 148], [0, 1]], ![[0, 1], [0, 85], [0, 147], [0, 17], [156, 100], [51, 115], [8, 19], [148, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [89, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [19, 19, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1033, 364, -400]
  a := ![-2, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![399, 292, -400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![64, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![64, 1, 0]] 
 ![![167, 0, 0], ![64, 1, 0], ![137, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![64, 1, 0], ![2, 65, 5], ![117, -13, 63]]]
  hmulB := by decide  
  f := ![![![-17667, -709345, -54570], ![-10855, 1822638, 0]], ![![-6764, -271805, -20910], ![-4174, 698394, 0]], ![![-14509, -581918, -44767], ![-8864, 1495218, 0]]]
  g := ![![![1, 0, 0], ![-64, 167, 0], ![-137, 0, 167]], ![![0, 1, 0], ![-29, 65, 5], ![-46, -13, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-3, -46, 1]] ![![167, 0, 0], ![64, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![10688, 167, 0]], ![![-501, -7682, 167], ![-167, -3006, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![64, 1, 0]]], ![![![-3, -46, 1]], ![![-1, -18, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [102, 88, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 31, 104], [69, 141, 69], [0, 1]]
 g := ![![[77, 61, 119], [20, 92], [74, 36, 167], [7, 155, 83], [60, 24], [85, 0, 1], []], ![[45, 71, 100, 105], [145, 126], [12, 160, 41, 99], [136, 75, 9, 72], [97, 60], [61, 5, 146, 101], [47, 90]], ![[25, 28, 88, 91], [48, 43], [167, 170, 131, 80], [4, 107, 18, 68], [13, 117], [85, 91, 64, 50], [82, 90]]]
 h' := ![![[104, 31, 104], [153, 122, 130], [64, 161, 28], [151, 130, 72], [162, 140, 16], [153, 132, 71], [0, 0, 1], [0, 1]], ![[69, 141, 69], [74, 162, 51], [141, 46, 105], [50, 162, 144], [8, 155, 35], [120, 172, 38], [140, 52, 141], [104, 31, 104]], ![[0, 1], [15, 62, 165], [76, 139, 40], [36, 54, 130], [95, 51, 122], [146, 42, 64], [30, 121, 31], [69, 141, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55, 43], []]
 b := ![[], [154, 143, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [102, 88, 0, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1147336, 702380, -107779]
  a := ![3, 21, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6632, 4060, -623]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [135, 135, 6, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 178, 82], [46, 0, 97], [0, 1]]
 g := ![![[129, 104, 51], [162, 114, 52], [53, 68], [26, 64], [121, 89, 77], [80, 173, 1], []], ![[99, 60, 127, 15], [108, 59, 177, 117], [77, 81], [116, 4], [24, 0, 152, 177], [165, 155], [125, 101]], ![[47, 82, 21, 38], [85, 47, 142, 28], [100, 3], [119, 36], [62, 125, 44, 150], [47, 138, 136, 97], [110, 101]]]
 h' := ![![[127, 178, 82], [147, 82, 92], [17, 6, 125], [38, 142, 151], [133, 131, 171], [119, 34, 16], [0, 0, 1], [0, 1]], ![[46, 0, 97], [104, 157, 101], [72, 130, 134], [117, 81, 9], [5, 35, 2], [19, 171, 103], [149, 24], [127, 178, 82]], ![[0, 1], [8, 119, 165], [32, 43, 99], [110, 135, 19], [94, 13, 6], [30, 153, 60], [154, 155, 178], [46, 0, 97]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 145], []]
 b := ![[], [136, 163, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [135, 135, 6, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1475318, 246125, -7876]
  a := ![-3, 1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8242, 1375, -44]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [163, 151, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 39, 19], [81, 141, 162], [0, 1]]
 g := ![![[32, 10, 132], [170, 33], [8, 149, 20], [158, 177], [28, 126, 73], [175, 114, 1], []], ![[146, 144, 130, 77], [51, 42], [145, 55, 77, 83], [0, 81], [40, 129, 167, 179], [151, 92, 119, 173], [101, 180]], ![[175, 78, 73, 26], [163, 139], [8, 111, 78, 113], [92, 117], [35, 52, 148, 19], [144, 33, 107, 61], [139, 180]]]
 h' := ![![[33, 39, 19], [85, 96, 48], [144, 105, 157], [21, 173, 54], [142, 111, 143], [73, 62, 39], [0, 0, 1], [0, 1]], ![[81, 141, 162], [161, 10, 85], [87, 170, 59], [170, 148, 41], [129, 30, 9], [14, 176, 161], [11, 156, 141], [33, 39, 19]], ![[0, 1], [159, 75, 48], [11, 87, 146], [75, 41, 86], [132, 40, 29], [172, 124, 162], [13, 25, 39], [81, 141, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 169], []]
 b := ![[], [9, 73, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [163, 151, 67, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2520244, -370688, 105885]
  a := ![4, 3, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13924, -2048, 585]
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



lemma PB182I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 181 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 181 (by omega)

def PB182I3 : PrimesBelowBoundCertificateInterval O 137 181 182 where
  m := 9
  g := ![2, 2, 3, 2, 1, 2, 1, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB182I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![5929741]
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
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
  β := ![I139N1, I149N1, I151N0, I151N1, I157N1, I167N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N0, I151N1], [I157N1], [], [I167N1], [], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
