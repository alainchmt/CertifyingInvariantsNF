
import IdealArithmetic.Examples.NF3_1_588735_1.RI3_1_588735_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [119, 87, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 135, 83], [34, 3, 56], [0, 1]]
 g := ![![[13, 108, 4], [102, 61, 117], [82, 121], [25, 105, 9], [51, 66], [16, 1], []], ![[0, 25, 21, 29], [10, 89, 126, 41], [91, 1], [108, 20, 31, 4], [112, 106], [61, 9], [28, 78]], ![[73, 34, 95, 53], [5, 14, 34, 126], [120, 5], [17, 4, 121, 33], [8, 136], [99, 16], [55, 78]]]
 h' := ![![[121, 135, 83], [94, 128, 137], [50, 87, 123], [83, 80, 11], [4, 63, 3], [42, 18, 30], [0, 0, 1], [0, 1]], ![[34, 3, 56], [53, 118, 54], [47, 105, 84], [27, 107, 1], [132, 54, 95], [106, 69, 55], [50, 102, 3], [121, 135, 83]], ![[0, 1], [73, 32, 87], [133, 86, 71], [97, 91, 127], [18, 22, 41], [85, 52, 54], [32, 37, 135], [34, 3, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 120], []]
 b := ![[], [128, 110, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [119, 87, 123, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32804, 52125, -200160]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![236, 375, -1440]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![22, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![22, 1, 0]] 
 ![![149, 0, 0], ![22, 1, 0], ![57, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![22, 1, 0], ![2, 21, 5], ![55, -30, 23]]]
  hmulB := by decide  
  f := ![![![-10649, -115275, -27450], ![-2235, 818010, 0]], ![![-1576, -17008, -4050], ![-297, 120690, 0]], ![![-4085, -44099, -10501], ![-779, 312930, 0]]]
  g := ![![![1, 0, 0], ![-22, 149, 0], ![-57, 0, 149]], ![![0, 1, 0], ![-5, 21, 5], ![-4, -30, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![47, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![47, 1, 0]] 
 ![![149, 0, 0], ![47, 1, 0], ![15, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![47, 1, 0], ![2, 46, 5], ![55, -30, 48]]]
  hmulB := by decide  
  f := ![![![12327, 328858, 35750], ![6258, -1065350, 0]], ![![3899, 103717, 11275], ![1938, -335995, 0]], ![![1217, 33106, 3599], ![706, -107250, 0]]]
  g := ![![![1, 0, 0], ![-47, 149, 0], ![-15, 0, 149]], ![![0, 1, 0], ![-15, 46, 5], ![5, -30, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-69, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-69, 1, 0]] 
 ![![149, 0, 0], ![80, 1, 0], ![137, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-69, 1, 0], ![2, -70, 5], ![55, -30, -68]]]
  hmulB := by decide  
  f := ![![![7138, -339113, 24225], ![-5513, -721905, 0]], ![![3823, -182050, 13005], ![-2979, -387549, 0]], ![![6571, -311802, 22274], ![-5052, -663765, 0]]]
  g := ![![![1, 0, 0], ![-80, 149, 0], ![-137, 0, 149]], ![![-1, 1, 0], ![33, -70, 5], ![79, -30, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![22, 1, 0]] ![![149, 0, 0], ![47, 1, 0]]
  ![![149, 0, 0], ![88, -46, 1]] where
 M := ![![![22201, 0, 0], ![7003, 149, 0]], ![![3278, 149, 0], ![1036, 68, 5]]]
 hmul := by decide  
 g := ![![![![61, 46, -1], ![149, 0, 0]], ![![-41, 47, -1], ![149, 0, 0]]], ![![![-66, 47, -1], ![149, 0, 0]], ![![4, 2, 0], ![5, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![88, -46, 1]] ![![149, 0, 0], ![-69, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10281, 149, 0]], ![![13112, -6854, 149], ![-6109, 3278, -298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-69, 1, 0]]], ![![![88, -46, 1]], ![![-41, 22, -2]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![32, 68, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![32, 68, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![32, 68, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![32, 68, 1], ![191, -66, 341], ![3750, -2035, 70]]]
  hmulB := by decide  
  f := ![![![-31, -68, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-32, -68, 151]], ![![0, 0, 1], ![-71, -154, 341], ![10, -45, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [101, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 150], [0, 1]]
 g := ![![[76, 16], [105, 118], [131, 118], [38], [36, 25], [21], [1]], ![[23, 135], [35, 33], [61, 33], [38], [57, 126], [21], [1]]]
 h' := ![![[25, 150], [116, 147], [57, 32], [81, 32], [139, 76], [77, 5], [50, 25], [0, 1]], ![[0, 1], [16, 4], [102, 119], [126, 119], [76, 75], [51, 146], [71, 126], [25, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138]]
 b := ![[], [119, 69]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [101, 126, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4654, 4040, -3307]
  a := ![5, -5, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![670, 1516, -3307]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-39, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-39, 1, 0]] 
 ![![151, 0, 0], ![112, 1, 0], ![81, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-39, 1, 0], ![2, -40, 5], ![55, -30, -38]]]
  hmulB := by decide  
  f := ![![![22420, -494341, 61800], ![-8909, -1866360, 0]], ![![16619, -366636, 45835], ![-6643, -1384217, 0]], ![![12015, -265176, 33151], ![-4824, -1001160, 0]]]
  g := ![![![1, 0, 0], ![-112, 151, 0], ![-81, 0, 151]], ![![-1, 1, 0], ![27, -40, 5], ![43, -30, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![32, 68, 1]] ![![151, 0, 0], ![-39, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-5889, 151, 0]], ![![4832, 10268, 151], ![-1057, -2718, 302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-39, 1, 0]]], ![![![32, 68, 1]], ![![-7, -18, 2]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![71, 64, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![71, 64, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![71, 64, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![71, 64, 1], ![183, -23, 321], ![3530, -1915, 105]]]
  hmulB := by decide  
  f := ![![![-70, -64, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -64, 157]], ![![0, 0, 1], ![-144, -131, 321], ![-25, -55, 105]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [115, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 156], [0, 1]]
 g := ![![[134, 71], [33], [10, 67], [116, 39], [136, 132], [105], [1]], ![[0, 86], [33], [129, 90], [122, 118], [108, 25], [105], [1]]]
 h' := ![![[133, 156], [62, 68], [106, 87], [5, 99], [60, 14], [51, 17], [42, 133], [0, 1]], ![[0, 1], [0, 89], [59, 70], [141, 58], [38, 143], [114, 140], [147, 24], [133, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [81, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [115, 24, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![150525, 104185, -516818]
  a := ![-66, 2, -133]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![234679, 211341, -516818]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-7, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-7, 1, 0]] 
 ![![157, 0, 0], ![150, 1, 0], ![52, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-7, 1, 0], ![2, -8, 5], ![55, -30, -6]]]
  hmulB := by decide  
  f := ![![![20105, -80632, 50400], ![-1256, -1582560, 0]], ![![19205, -77032, 48150], ![-1255, -1511910, 0]], ![![6658, -26706, 16693], ![-438, -524160, 0]]]
  g := ![![![1, 0, 0], ![-150, 157, 0], ![-52, 0, 157]], ![![-1, 1, 0], ![6, -8, 5], ![31, -30, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![71, 64, 1]] ![![157, 0, 0], ![-7, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-1099, 157, 0]], ![![11147, 10048, 157], ![-314, -471, 314]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-7, 1, 0]]], ![![![71, 64, 1]], ![![-2, -3, 2]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [39, 18, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [123, 107, 148], [153, 55, 15], [0, 1]]
 g := ![![[47, 145, 25], [15, 15, 133], [45, 160], [87, 90], [95, 121], [37, 113, 1], []], ![[81, 149, 37, 2], [102, 27, 93, 11], [64, 131], [157, 161], [120, 115], [45, 119, 40, 102], [47, 62]], ![[99, 62, 139, 121], [91, 108, 144, 55], [40, 69], [83, 26], [11, 100], [53, 132, 117, 96], [17, 62]]]
 h' := ![![[123, 107, 148], [67, 105, 158], [109, 12, 40], [76, 10, 117], [131, 109, 116], [24, 143, 152], [0, 0, 1], [0, 1]], ![[153, 55, 15], [129, 102, 106], [89, 46, 64], [125, 65, 91], [39, 151, 18], [127, 132, 21], [93, 75, 55], [123, 107, 148]], ![[0, 1], [39, 119, 62], [126, 105, 59], [120, 88, 118], [74, 66, 29], [60, 51, 153], [89, 88, 107], [153, 55, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 106], []]
 b := ![[], [33, 70, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [39, 18, 50, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3389259, 2587299, -2100418]
  a := ![-5, 4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20793, 15873, -12886]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [37, 62, 40, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 21, 65], [166, 145, 102], [0, 1]]
 g := ![![[150, 101, 29], [33, 106, 144], [147, 112, 57], [82, 7], [94, 11], [35, 127, 1], []], ![[96, 144, 107, 65], [93, 44, 127, 49], [3, 24], [120, 152], [53, 36], [125, 115, 87, 64], [62, 50]], ![[18, 97, 98, 71], [116, 91, 150, 80], [153, 98, 97, 136], [4, 1], [119, 38], [104, 13, 55, 59], [25, 50]]]
 h' := ![![[128, 21, 65], [115, 51, 14], [72, 20, 155], [69, 165, 70], [40, 144, 72], [41, 145, 41], [0, 0, 1], [0, 1]], ![[166, 145, 102], [163, 126, 1], [51, 61, 61], [145, 76], [57, 1, 94], [101, 27, 6], [62, 16, 145], [128, 21, 65]], ![[0, 1], [154, 157, 152], [118, 86, 118], [20, 93, 97], [1, 22, 1], [88, 162, 120], [78, 151, 21], [166, 145, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 107], []]
 b := ![[], [154, 115, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [37, 62, 40, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11690, 41750, -139445]
  a := ![-2, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, 250, -835]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [79, 15, 65, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 26, 40], [82, 146, 133], [0, 1]]
 g := ![![[15, 110, 38], [59, 148], [152, 88, 56], [146, 51, 172], [157, 164], [58, 108, 1], []], ![[147, 2, 82, 163], [89, 60], [152, 69, 53, 49], [46, 90, 60, 40], [129, 135], [32, 47, 160, 96], [150, 43]], ![[23, 8, 98, 78], [86, 160], [35, 167, 137, 60], [1, 133, 61, 172], [89, 100], [49, 105, 126, 121], [57, 43]]]
 h' := ![![[26, 26, 40], [34, 35, 111], [102, 72, 54], [57, 92, 103], [16, 132, 93], [89, 113, 67], [0, 0, 1], [0, 1]], ![[82, 146, 133], [2, 88, 133], [99, 32, 38], [74, 119, 34], [17, 167, 1], [172, 104, 116], [71, 30, 146], [26, 26, 40]], ![[0, 1], [142, 50, 102], [169, 69, 81], [46, 135, 36], [105, 47, 79], [40, 129, 163], [145, 143, 26], [82, 146, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 55], []]
 b := ![[], [94, 27, 150], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [79, 15, 65, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1679311, 1251136, -680409]
  a := ![3, 18, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9707, 7232, -3933]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-5, -42, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-5, -42, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![174, 137, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-5, -42, 1], ![-29, 7, -209], ![-2300, 1265, -77]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-174, -137, 179]], ![![-1, -1, 1], ![203, 160, -209], ![62, 66, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [93, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 178], [0, 1]]
 g := ![![[27, 77], [74, 158], [126], [153], [99, 68], [89, 25], [1]], ![[0, 102], [0, 21], [126], [153], [117, 111], [143, 154], [1]]]
 h' := ![![[174, 178], [99, 163], [141, 64], [89, 22], [101, 42], [136, 151], [86, 174], [0, 1]], ![[0, 1], [0, 16], [0, 115], [158, 157], [70, 137], [97, 28], [111, 5], [174, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [146, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [93, 5, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2471, 1905, -1439]
  a := ![-3, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1385, 1112, -1439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![30, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![30, 1, 0]] 
 ![![179, 0, 0], ![30, 1, 0], ![77, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![30, 1, 0], ![2, 29, 5], ![55, -30, 31]]]
  hmulB := by decide  
  f := ![![![1807, 27489, 4740], ![537, -169692, 0]], ![![286, 4581, 790], ![180, -28282, 0]], ![![781, 11825, 2039], ![209, -72996, 0]]]
  g := ![![![1, 0, 0], ![-30, 179, 0], ![-77, 0, 179]], ![![0, 1, 0], ![-7, 29, 5], ![-8, -30, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-5, -42, 1]] ![![179, 0, 0], ![30, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![5370, 179, 0]], ![![-895, -7518, 179], ![-179, -1253, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![30, 1, 0]]], ![![![-5, -42, 1]], ![![-1, -7, -1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![22, -55, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![22, -55, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![22, 126, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![22, -55, 1], ![-55, 47, -274], ![-3015, 1655, -63]]]
  hmulB := by decide  
  f := ![![![-21, 55, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-22, -126, 181]], ![![0, -1, 1], ![33, 191, -274], ![-9, 53, -63]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [63, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 180], [0, 1]]
 g := ![![[179, 73], [64], [98, 100], [59], [68, 176], [16, 129], [1]], ![[146, 108], [64], [28, 81], [59], [162, 5], [161, 52], [1]]]
 h' := ![![[126, 180], [169, 142], [161, 8], [64, 171], [60, 125], [78, 30], [118, 126], [0, 1]], ![[0, 1], [142, 39], [83, 173], [71, 10], [63, 56], [57, 151], [66, 55], [126, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [131]]
 b := ![[], [127, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [63, 55, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201, 1036, -2385]
  a := ![4, -1, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![291, 1666, -2385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-88, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-88, 1, 0]] 
 ![![181, 0, 0], ![93, 1, 0], ![63, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-88, 1, 0], ![2, -89, 5], ![55, -30, -87]]]
  hmulB := by decide  
  f := ![![![12295, -766323, 43055], ![-10136, -1558591, 0]], ![![6385, -393708, 22120], ![-5067, -800744, 0]], ![![4349, -266732, 14986], ![-3385, -542493, 0]]]
  g := ![![![1, 0, 0], ![-93, 181, 0], ![-63, 0, 181]], ![![-1, 1, 0], ![44, -89, 5], ![46, -30, -87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![22, -55, 1]] ![![181, 0, 0], ![-88, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-15928, 181, 0]], ![![3982, -9955, 181], ![-1991, 4887, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-88, 1, 0]]], ![![![22, -55, 1]], ![![-11, 27, -2]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [66, 63, 179, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [82, 176, 188], [121, 14, 3], [0, 1]]
 g := ![![[74, 55, 120], [58, 71, 10], [39, 180, 26], [25, 185, 135], [118, 86, 153], [81, 12, 1], []], ![[158, 159, 25, 159], [97, 84, 128, 63], [15, 185, 5, 155], [68, 172, 77, 83], [92, 144, 72, 186], [31, 44, 140, 176], [7, 9]], ![[83, 182, 175, 17], [59, 140, 43, 102], [78, 175, 132, 48], [39, 35, 58, 129], [23, 36, 28, 34], [62, 55, 8, 102], [1, 9]]]
 h' := ![![[82, 176, 188], [183, 132, 104], [100, 165, 34], [69, 97, 147], [43, 73, 138], [2, 26, 150], [0, 0, 1], [0, 1]], ![[121, 14, 3], [58, 114, 105], [12, 171, 172], [86, 98, 48], [180, 16, 185], [186, 37, 112], [150, 134, 14], [82, 176, 188]], ![[0, 1], [135, 136, 173], [106, 46, 176], [42, 187, 187], [19, 102, 59], [156, 128, 120], [59, 57, 176], [121, 14, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 138], []]
 b := ![[], [63, 11, 46], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [66, 63, 179, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![193101, 382000, -1390480]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1011, 2000, -7280]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [54, 32, 50, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [183, 188, 46], [153, 4, 147], [0, 1]]
 g := ![![[136, 16, 21], [92, 92], [190, 165], [170, 42], [133, 67], [176, 184], [1]], ![[187, 14, 148, 126], [10, 16], [6, 189], [22, 65], [114, 3], [105, 172], [158, 32, 186, 64]], ![[111, 125, 22, 186], [144, 130], [143, 54], [48, 64], [179, 55], [13, 32], [180, 52, 28, 129]]]
 h' := ![![[183, 188, 46], [0, 8, 139], [23, 147, 142], [132, 80, 101], [56, 104, 87], [167, 47, 35], [139, 161, 143], [0, 1]], ![[153, 4, 147], [123, 35, 152], [85, 140, 189], [71, 28, 31], [115, 99, 114], [148, 156, 179], [118, 15, 65], [183, 188, 46]], ![[0, 1], [138, 150, 95], [1, 99, 55], [14, 85, 61], [26, 183, 185], [106, 183, 172], [6, 17, 178], [153, 4, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147, 14], []]
 b := ![[], [41, 174, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [54, 32, 50, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9899742, -5888816, 1281520]
  a := ![6, -12, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![51294, -30512, 6640]
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



lemma PB218I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB218I3 : PrimesBelowBoundCertificateInterval O 137 193 218 where
  m := 11
  g := ![1, 3, 2, 2, 1, 1, 1, 2, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB218I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![2685619]
    · exact ![149, 149, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![32761, 181]
    · exact ![6967871]
    · exact ![7189057]
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
      exact NI149N1
      exact NI149N2
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
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N0, I149N1, I149N2, I151N1, I157N1, I179N1, I181N1]
  Il := ![[], [I149N0, I149N1, I149N2], [I151N1], [I157N1], [], [], [], [I179N1], [I181N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
