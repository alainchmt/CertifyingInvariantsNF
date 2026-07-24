
import IdealArithmetic.Examples.NF3_1_466627_2.RI3_1_466627_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-74, -45, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-74, -45, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![65, 94, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-74, -45, 1], ![133, -60, -45], ![-5985, -497, -60]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -94, 139]], ![![-1, -1, 1], ![22, 30, -45], ![-15, 37, -60]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [126, 133, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 138], [0, 1]]
 g := ![![[86, 51], [110, 42], [7], [25, 25], [79], [36], [1]], ![[114, 88], [84, 97], [7], [36, 114], [79], [36], [1]]]
 h' := ![![[6, 138], [40, 32], [76, 96], [47, 110], [82, 134], [81, 94], [13, 6], [0, 1]], ![[0, 1], [93, 107], [96, 43], [12, 29], [52, 5], [89, 45], [49, 133], [6, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [98, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [126, 133, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![392, 28, -118]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![58, 80, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![45, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![45, 1, 0]] 
 ![![139, 0, 0], ![45, 1, 0], ![60, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![45, 1, 0], ![0, 45, 1], ![133, 14, 45]]]
  hmulB := by decide  
  f := ![![![1261, 28, 0], ![-3892, 0, 0]], ![![405, 9, 0], ![-1250, 0, 0]], ![![510, 11, 0], ![-1574, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 139, 0], ![-60, 0, 139]], ![![0, 1, 0], ![-15, 45, 1], ![-23, 14, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-74, -45, 1]] ![![139, 0, 0], ![45, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![6255, 139, 0]], ![![-10286, -6255, 139], ![-3197, -2085, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![45, 1, 0]]], ![![![-74, -45, 1]], ![![-23, -15, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-9, 68, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-9, 68, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![140, 68, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-9, 68, 1], ![133, 5, 68], ![9044, 1085, 5]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-140, -68, 149]], ![![-1, 0, 1], ![-63, -31, 68], ![56, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [95, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [54, 148], [0, 1]]
 g := ![![[1, 80], [28], [44, 144], [16], [27, 64], [85], [1]], ![[0, 69], [28], [72, 5], [16], [56, 85], [85], [1]]]
 h' := ![![[54, 148], [86, 26], [141, 37], [100, 12], [117, 4], [56, 141], [54, 54], [0, 1]], ![[0, 1], [0, 123], [53, 112], [3, 137], [35, 145], [71, 8], [139, 95], [54, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [18, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [95, 95, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1595, 843, 409]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-395, -181, 409]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-68, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-68, 1, 0]] 
 ![![149, 0, 0], ![81, 1, 0], ![144, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-68, 1, 0], ![0, -68, 1], ![133, 14, -68]]]
  hmulB := by decide  
  f := ![![![8773, -129, 0], ![19221, 0, 0]], ![![4761, -70, 0], ![10431, 0, 0]], ![![8464, -124, 0], ![18544, 1, 0]]]
  g := ![![![1, 0, 0], ![-81, 149, 0], ![-144, 0, 149]], ![![-1, 1, 0], ![36, -68, 1], ![59, 14, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-9, 68, 1]] ![![149, 0, 0], ![-68, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10132, 149, 0]], ![![-1341, 10132, 149], ![745, -4619, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-68, 1, 0]]], ![![![-9, 68, 1]], ![![5, -31, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![5, -64, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![5, -64, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![5, 87, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![5, -64, 1], ![133, 19, -64], ![-8512, -763, 19]]]
  hmulB := by decide  
  f := ![![![-4, 64, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -87, 151]], ![![0, -1, 1], ![3, 37, -64], ![-57, -16, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [135, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 150], [0, 1]]
 g := ![![[137, 94], [52, 121], [79, 85], [43], [87, 11], [44], [1]], ![[70, 57], [128, 30], [65, 66], [43], [39, 140], [44], [1]]]
 h' := ![![[78, 150], [77, 68], [56, 140], [116, 113], [33, 63], [54, 39], [16, 78], [0, 1]], ![[0, 1], [96, 83], [104, 11], [21, 38], [115, 88], [76, 112], [60, 73], [78, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [93, 137]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [135, 73, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-707, 50, 70]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -40, 70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![64, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![64, 1, 0]] 
 ![![151, 0, 0], ![64, 1, 0], ![132, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![64, 1, 0], ![0, 64, 1], ![133, 14, 64]]]
  hmulB := by decide  
  f := ![![![2625, 41, 0], ![-6191, 0, 0]], ![![1088, 17, 0], ![-2566, 0, 0]], ![![2332, 36, 0], ![-5500, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 151, 0], ![-132, 0, 151]], ![![0, 1, 0], ![-28, 64, 1], ![-61, 14, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![5, -64, 1]] ![![151, 0, 0], ![64, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![9664, 151, 0]], ![![755, -9664, 151], ![453, -4077, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![64, 1, 0]]], ![![![5, -64, 1]], ![![3, -27, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![23, -42, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![23, -42, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![23, 115, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![23, -42, 1], ![133, 37, -42], ![-5586, -455, 37]]]
  hmulB := by decide  
  f := ![![![-22, 42, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -115, 157]], ![![0, -1, 1], ![7, 31, -42], ![-41, -30, 37]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [72, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 156], [0, 1]]
 g := ![![[23, 46], [146], [115, 106], [149, 145], [124, 71], [17], [1]], ![[149, 111], [146], [105, 51], [82, 12], [141, 86], [17], [1]]]
 h' := ![![[71, 156], [118, 108], [41, 97], [105, 109], [21, 50], [35, 89], [85, 71], [0, 1]], ![[0, 1], [93, 49], [20, 60], [151, 48], [117, 107], [74, 68], [102, 86], [71, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [155, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [72, 86, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-639, 1201, -137]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 108, -137]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![42, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![42, 1, 0]] 
 ![![157, 0, 0], ![42, 1, 0], ![120, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![42, 1, 0], ![0, 42, 1], ![133, 14, 42]]]
  hmulB := by decide  
  f := ![![![2605, 62, 0], ![-9734, 0, 0]], ![![630, 15, 0], ![-2354, 0, 0]], ![![1944, 46, 0], ![-7264, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 157, 0], ![-120, 0, 157]], ![![0, 1, 0], ![-12, 42, 1], ![-35, 14, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![23, -42, 1]] ![![157, 0, 0], ![42, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![6594, 157, 0]], ![![3611, -6594, 157], ![1099, -1727, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![42, 1, 0]]], ![![![23, -42, 1]], ![![7, -11, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![55, -45, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![55, -45, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![55, 118, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![55, -45, 1], ![133, 69, -45], ![-5985, -497, 69]]]
  hmulB := by decide  
  f := ![![![-54, 45, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -118, 163]], ![![0, -1, 1], ![16, 33, -45], ![-60, -53, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [13, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 162], [0, 1]]
 g := ![![[63, 156], [154, 16], [77], [161], [155], [40, 16], [1]], ![[91, 7], [90, 147], [77], [161], [155], [139, 147], [1]]]
 h' := ![![[159, 162], [117, 51], [95, 159], [97, 136], [87, 145], [132, 127], [150, 159], [0, 1]], ![[0, 1], [76, 112], [111, 4], [42, 27], [159, 18], [113, 36], [3, 4], [159, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145]]
 b := ![[], [145, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [13, 4, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![279, 157, 11]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, -7, 11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![45, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![45, 1, 0]] 
 ![![163, 0, 0], ![45, 1, 0], ![94, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![45, 1, 0], ![0, 45, 1], ![133, 14, 45]]]
  hmulB := by decide  
  f := ![![![1126, 25, 0], ![-4075, 0, 0]], ![![270, 6, 0], ![-977, 0, 0]], ![![598, 13, 0], ![-2164, 1, 0]]]
  g := ![![![1, 0, 0], ![-45, 163, 0], ![-94, 0, 163]], ![![0, 1, 0], ![-13, 45, 1], ![-29, 14, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![55, -45, 1]] ![![163, 0, 0], ![45, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![7335, 163, 0]], ![![8965, -7335, 163], ![2608, -1956, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![45, 1, 0]]], ![![![55, -45, 1]], ![![16, -12, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-48, -48, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-48, -48, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![119, 119, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-48, -48, 1], ![133, -34, -48], ![-6384, -539, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-119, -119, 167]], ![![-1, -1, 1], ![35, 34, -48], ![-14, 21, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [124, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 166], [0, 1]]
 g := ![![[46, 66], [82, 16], [17, 97], [54], [47], [61, 8], [1]], ![[0, 101], [0, 151], [0, 70], [54], [47], [20, 159], [1]]]
 h' := ![![[141, 166], [19, 20], [63, 163], [38, 40], [80, 80], [118, 106], [43, 141], [0, 1]], ![[0, 1], [0, 147], [0, 4], [0, 127], [4, 87], [34, 61], [51, 26], [141, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [165, 154]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [124, 26, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5205, 1197, 403]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-256, -280, 403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![48, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![48, 1, 0]] 
 ![![167, 0, 0], ![48, 1, 0], ![34, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![48, 1, 0], ![0, 48, 1], ![133, 14, 48]]]
  hmulB := by decide  
  f := ![![![2929, 61, 0], ![-10187, 0, 0]], ![![816, 17, 0], ![-2838, 0, 0]], ![![590, 12, 0], ![-2052, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 167, 0], ![-34, 0, 167]], ![![0, 1, 0], ![-14, 48, 1], ![-13, 14, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-48, -48, 1]] ![![167, 0, 0], ![48, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![8016, 167, 0]], ![![-8016, -8016, 167], ![-2171, -2338, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![48, 1, 0]]], ![![![-48, -48, 1]], ![![-13, -14, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-49, 22, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-49, 22, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![124, 22, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-49, 22, 1], ![133, -35, 22], ![2926, 441, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-124, -22, 173]], ![![-1, 0, 1], ![-15, -3, 22], ![42, 7, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [67, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 172], [0, 1]]
 g := ![![[82, 31], [139], [43, 33], [40, 47], [138], [125, 34], [1]], ![[0, 142], [139], [45, 140], [111, 126], [138], [169, 139], [1]]]
 h' := ![![[42, 172], [169, 66], [60, 73], [88, 129], [120, 77], [102, 22], [106, 42], [0, 1]], ![[0, 1], [0, 107], [12, 100], [143, 44], [67, 96], [161, 151], [140, 131], [42, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [22, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [67, 131, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-861, 436, -106]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71, 16, -106]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-22, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-22, 1, 0]] 
 ![![173, 0, 0], ![151, 1, 0], ![35, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-22, 1, 0], ![0, -22, 1], ![133, 14, -22]]]
  hmulB := by decide  
  f := ![![![2817, -128, 0], ![22144, 0, 0]], ![![2487, -113, 0], ![19550, 0, 0]], ![![575, -26, 0], ![4520, 1, 0]]]
  g := ![![![1, 0, 0], ![-151, 173, 0], ![-35, 0, 173]], ![![-1, 1, 0], ![19, -22, 1], ![-7, 14, -22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-49, 22, 1]] ![![173, 0, 0], ![-22, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-3806, 173, 0]], ![![-8477, 3806, 173], ![1211, -519, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-22, 1, 0]]], ![![![-49, 22, 1]], ![![7, -3, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-24, -13, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-24, -13, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![155, 166, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-24, -13, 1], ![133, -10, -13], ![-1729, -49, -10]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-155, -166, 179]], ![![-1, -1, 1], ![12, 12, -13], ![-1, 9, -10]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [45, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 178], [0, 1]]
 g := ![![[2, 4], [175, 171], [46], [149], [136, 93], [112, 45], [1]], ![[0, 175], [0, 8], [46], [149], [0, 86], [0, 134], [1]]]
 h' := ![![[89, 178], [1, 2], [78, 156], [0, 164], [145, 111], [151, 123], [134, 89], [0, 1]], ![[0, 1], [0, 177], [0, 23], [97, 15], [0, 68], [0, 56], [0, 90], [89, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [120, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [45, 90, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![577, 678, 237]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-202, -216, 237]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![13, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![13, 1, 0]] 
 ![![179, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![13, 1, 0], ![0, 13, 1], ![133, 14, 13]]]
  hmulB := by decide  
  f := ![![![1431, 110, 0], ![-19690, 0, 0]], ![![91, 7, 0], ![-1252, 0, 0]], ![![66, 5, 0], ![-908, 1, 0]]]
  g := ![![![1, 0, 0], ![-13, 179, 0], ![-10, 0, 179]], ![![0, 1, 0], ![-1, 13, 1], ![-1, 14, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-24, -13, 1]] ![![179, 0, 0], ![13, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![2327, 179, 0]], ![![-4296, -2327, 179], ![-179, -179, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![13, 1, 0]]], ![![![-24, -13, 1]], ![![-1, -1, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [150, 179, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [21, 124, 2], [41, 56, 179], [0, 1]]
 g := ![![[170, 108, 178], [32, 136], [19, 169, 16], [133, 125], [113, 147, 48], [45, 62, 1], []], ![[8, 128, 140, 95], [22, 101], [161, 74, 162, 10], [141, 122], [113, 16, 103, 127], [151, 154, 11, 118], [20, 4]], ![[55, 37, 79, 131], [83, 117], [44, 41, 105, 28], [0, 99], [157, 91, 95, 160], [39, 70, 80, 18], [24, 4]]]
 h' := ![![[21, 124, 2], [31, 47, 84], [46, 74, 90], [74, 146, 4], [64, 171, 46], [128, 21, 49], [0, 0, 1], [0, 1]], ![[41, 56, 179], [4, 51, 92], [74, 155, 120], [144, 134, 154], [152, 74, 22], [68, 124, 71], [156, 123, 56], [21, 124, 2]], ![[0, 1], [42, 83, 5], [148, 133, 152], [13, 82, 23], [70, 117, 113], [173, 36, 61], [72, 58, 124], [41, 56, 179]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 58], []]
 b := ![[], [3, 51, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [150, 179, 119, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-878936, 61902, 14842]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4856, 342, 82]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [98, 97, 124, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 63, 154], [50, 127, 37], [0, 1]]
 g := ![![[146, 7, 34], [186, 139, 108], [78], [32, 70, 51], [160, 37, 59], [190, 67, 1], []], ![[47, 58, 6, 135], [8, 101, 162, 147], [32, 55, 26, 92], [180, 95, 12, 144], [111, 173, 92, 100], [100, 76, 107, 102], [156, 32]], ![[180, 76, 83, 58], [174, 126, 164, 44], [14, 140, 126, 99], [125, 63, 54, 56], [180, 20, 190, 7], [74, 81, 84, 165], [82, 32]]]
 h' := ![![[17, 63, 154], [108, 58, 15], [187, 171, 144], [111, 101], [173, 8, 137], [98, 25, 21], [0, 0, 1], [0, 1]], ![[50, 127, 37], [152, 132, 141], [10, 111, 119], [109, 60, 83], [33, 157, 104], [121, 44, 23], [90, 109, 127], [17, 63, 154]], ![[0, 1], [188, 1, 35], [1, 100, 119], [4, 30, 108], [29, 26, 141], [74, 122, 147], [3, 82, 63], [50, 127, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128, 143], []]
 b := ![[], [161, 49, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [98, 97, 124, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6876, 16808, 6112]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, 88, 32]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![9, -71, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![9, -71, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![9, 122, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![9, -71, 1], ![133, 23, -71], ![-9443, -861, 23]]]
  hmulB := by decide  
  f := ![![![-8, 71, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-9, -122, 193]], ![![0, -1, 1], ![4, 45, -71], ![-50, -19, 23]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [177, 94, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 192], [0, 1]]
 g := ![![[163, 12], [161], [172], [62], [16], [97], [99, 1]], ![[0, 181], [161], [172], [62], [16], [97], [5, 192]]]
 h' := ![![[99, 192], [70, 165], [179, 136], [69, 65], [106, 107], [64, 189], [40, 167], [0, 1]], ![[0, 1], [0, 28], [133, 57], [135, 128], [84, 86], [54, 4], [168, 26], [99, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [101, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [177, 94, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1336, -139, -66]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, 41, -66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![71, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![71, 1, 0]] 
 ![![193, 0, 0], ![71, 1, 0], ![170, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![71, 1, 0], ![0, 71, 1], ![133, 14, 71]]]
  hmulB := by decide  
  f := ![![![4332, 61, 0], ![-11773, 0, 0]], ![![1562, 22, 0], ![-4245, 0, 0]], ![![3790, 53, 0], ![-10300, 1, 0]]]
  g := ![![![1, 0, 0], ![-71, 193, 0], ![-170, 0, 193]], ![![0, 1, 0], ![-27, 71, 1], ![-67, 14, 71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![9, -71, 1]] ![![193, 0, 0], ![71, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![13703, 193, 0]], ![![1737, -13703, 193], ![772, -5018, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![71, 1, 0]]], ![![![9, -71, 1]], ![![4, -26, 0]]]]
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
