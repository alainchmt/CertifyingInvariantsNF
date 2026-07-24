
import IdealArithmetic.Examples.NF3_1_466796_1.RI3_1_466796_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-32, 68, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-32, 68, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![107, 68, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-32, 68, 1], ![-679, 105, 69], ![-46851, 8774, 174]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -68, 139]], ![![-1, 0, 1], ![-58, -33, 69], ![-471, -22, 174]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [110, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 138], [0, 1]]
 g := ![![[42, 127], [7, 77], [37], [125, 63], [42], [116], [1]], ![[21, 12], [107, 62], [37], [131, 76], [42], [116], [1]]]
 h' := ![![[106, 138], [64, 108], [82, 63], [11, 71], [80, 52], [35, 96], [29, 106], [0, 1]], ![[0, 1], [114, 31], [88, 76], [31, 68], [32, 87], [64, 43], [6, 33], [106, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [40, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [110, 33, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1927, -301, 108]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97, -55, 108]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-69, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-69, 1, 0]] 
 ![![139, 0, 0], ![70, 1, 0], ![104, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-69, 1, 0], ![0, -69, 1], ![-679, 137, -68]]]
  hmulB := by decide  
  f := ![![![9592, -139, 0], ![19321, 0, 0]], ![![4900, -71, 0], ![9870, 0, 0]], ![![7280, -105, 0], ![14664, 1, 0]]]
  g := ![![![1, 0, 0], ![-70, 139, 0], ![-104, 0, 139]], ![![-1, 1, 0], ![34, -69, 1], ![-23, 137, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-32, 68, 1]] ![![139, 0, 0], ![-69, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-9591, 139, 0]], ![![-4448, 9452, 139], ![1529, -4587, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-69, 1, 0]]], ![![![-32, 68, 1]], ![![11, -33, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-20, -49, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-20, -49, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![129, 100, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-20, -49, 1], ![-679, 117, -48], ![32592, -7255, 69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -100, 149]], ![![-1, -1, 1], ![37, 33, -48], ![159, -95, 69]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [90, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 148], [0, 1]]
 g := ![![[130, 53], [37], [111, 110], [116], [21, 123], [124], [1]], ![[19, 96], [37], [24, 39], [116], [112, 26], [124], [1]]]
 h' := ![![[71, 148], [146, 84], [142, 22], [113, 109], [47, 99], [69, 47], [59, 71], [0, 1]], ![[0, 1], [1, 65], [65, 127], [104, 40], [73, 50], [128, 102], [34, 78], [71, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [42, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [90, 78, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2050, -6674, 1462]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1252, -1026, 1462]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![48, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![48, 1, 0]] 
 ![![149, 0, 0], ![48, 1, 0], ![80, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![48, 1, 0], ![0, 48, 1], ![-679, 137, 49]]]
  hmulB := by decide  
  f := ![![![2161, 45, 0], ![-6705, 0, 0]], ![![624, 13, 0], ![-1936, 0, 0]], ![![1168, 24, 0], ![-3624, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 149, 0], ![-80, 0, 149]], ![![0, 1, 0], ![-16, 48, 1], ![-75, 137, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-20, -49, 1]] ![![149, 0, 0], ![48, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![7152, 149, 0]], ![![-2980, -7301, 149], ![-1639, -2235, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![48, 1, 0]]], ![![![-20, -49, 1]], ![![-11, -15, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-144, 53, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-144, 53, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![7, 53, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-144, 53, 1], ![-679, -7, 54], ![-36666, 6719, 47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -53, 151]], ![![-1, 0, 1], ![-7, -19, 54], ![-245, 28, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [8, 107, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 150], [0, 1]]
 g := ![![[70, 19], [101, 8], [98, 91], [80], [32, 58], [124], [1]], ![[0, 132], [0, 143], [25, 60], [80], [17, 93], [124], [1]]]
 h' := ![![[44, 150], [98, 87], [122, 59], [117, 53], [46, 69], [129, 71], [143, 44], [0, 1]], ![[0, 1], [0, 64], [0, 92], [33, 98], [62, 82], [82, 80], [116, 107], [44, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [105]]
 b := ![[], [53, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [8, 107, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2065, -837, 158]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, -61, 158]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-54, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-54, 1, 0]] 
 ![![151, 0, 0], ![97, 1, 0], ![104, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-54, 1, 0], ![0, -54, 1], ![-679, 137, -53]]]
  hmulB := by decide  
  f := ![![![1297, -24, 0], ![3624, 0, 0]], ![![811, -15, 0], ![2266, 0, 0]], ![![884, -16, 0], ![2470, 1, 0]]]
  g := ![![![1, 0, 0], ![-97, 151, 0], ![-104, 0, 151]], ![![-1, 1, 0], ![34, -54, 1], ![-56, 137, -53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-144, 53, 1]] ![![151, 0, 0], ![-54, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-8154, 151, 0]], ![![-21744, 8003, 151], ![7097, -2869, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-54, 1, 0]]], ![![![-144, 53, 1]], ![![47, -19, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [121, 19, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 2, 81], [6, 154, 76], [0, 1]]
 g := ![![[25, 122, 76], [12, 132], [95, 54, 49], [147, 9, 122], [29, 77, 127], [121, 1], []], ![[60, 86, 41, 138], [7, 12], [1, 59, 16, 130], [28, 125, 83, 11], [16, 145, 129, 93], [101, 9], [99, 124]], ![[24, 108, 106, 141], [124, 115], [64, 9, 0, 110], [79, 104, 122, 109], [31, 106, 15, 31], [87, 4], [104, 124]]]
 h' := ![![[115, 2, 81], [18, 20, 95], [123, 57, 17], [111, 85, 7], [102, 53, 43], [117, 92, 21], [0, 0, 1], [0, 1]], ![[6, 154, 76], [112, 88, 79], [71, 35, 13], [82, 119, 113], [115, 17, 82], [125, 31, 10], [147, 60, 154], [115, 2, 81]], ![[0, 1], [22, 49, 140], [41, 65, 127], [77, 110, 37], [151, 87, 32], [136, 34, 126], [12, 97, 2], [6, 154, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 124], []]
 b := ![[], [67, 108, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [121, 19, 36, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10010320, 4299288, -445409]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63760, 27384, -2837]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [136, 48, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 1, 28], [102, 161, 135], [0, 1]]
 g := ![![[149, 111, 53], [109, 142, 158], [128, 64], [62, 150], [65, 88], [7, 50, 1], []], ![[11, 76, 125, 18], [31, 24, 158, 112], [75, 6], [129, 151], [148, 1], [133, 23, 74, 112], [136, 132]], ![[157, 46, 98, 53], [155, 150, 15, 47], [162, 25], [86, 77], [59, 118], [76, 135, 59, 135], [29, 132]]]
 h' := ![![[111, 1, 28], [9, 103, 85], [94, 83, 22], [77, 134, 8], [149, 150, 98], [26, 36, 96], [0, 0, 1], [0, 1]], ![[102, 161, 135], [17, 123, 106], [108, 69, 161], [107, 40, 150], [79, 58, 92], [141, 49, 1], [19, 29, 161], [111, 1, 28]], ![[0, 1], [36, 100, 135], [68, 11, 143], [62, 152, 5], [115, 118, 136], [57, 78, 66], [103, 134, 1], [102, 161, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [104, 154], []]
 b := ![[], [156, 85, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [136, 48, 113, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-220539, 65526, -1141]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1353, 402, -7]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![405, -22, -4]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![405, -22, -4]] 
 ![![167, 0, 0], ![0, 167, 0], ![24, 89, 1]] where
  M :=![![![405, -22, -4], ![2716, -143, -26], ![17654, -846, -169]]]
  hmulB := by decide  
  f := ![![![-13, 2, 0]], ![![0, -13, 2]], ![![-10, -5, 1]]]
  g := ![![![3, 2, -4], ![20, 13, -26], ![130, 85, -169]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [56, 162, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 166], [0, 1]]
 g := ![![[152, 3], [95, 114], [93, 116], [11], [3], [66, 25], [1]], ![[0, 164], [164, 53], [5, 51], [11], [3], [24, 142], [1]]]
 h' := ![![[5, 166], [24, 62], [136, 75], [42, 28], [149, 126], [145, 62], [111, 5], [0, 1]], ![[0, 1], [0, 105], [10, 92], [15, 139], [111, 41], [121, 105], [136, 162], [5, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [99, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [56, 162, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-26262, 7780, 701]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-258, -327, 701]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, -2, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![13, -2, 0]] 
 ![![167, 0, 0], ![77, 1, 0], ![83, 0, 1]] where
  M :=![![![13, -2, 0], ![0, 13, -2], ![1358, -274, 11]]]
  hmulB := by decide  
  f := ![![![-405, 22, 4]], ![![-203, 11, 2]], ![![-307, 16, 3]]]
  g := ![![![1, -2, 0], ![-5, 13, -2], ![129, -274, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![405, -22, -4]] ![![13, -2, 0]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-150, -23, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-150, -23, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![23, 150, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-150, -23, 1], ![-679, -13, -22], ![14938, -3693, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-23, -150, 173]], ![![-1, -1, 1], ![-1, 19, -22], ![91, 9, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [83, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 172], [0, 1]]
 g := ![![[153, 148], [138], [56, 136], [41, 1], [140], [88, 56], [1]], ![[0, 25], [138], [51, 37], [144, 172], [140], [147, 117], [1]]]
 h' := ![![[103, 172], [147, 54], [23, 151], [57, 84], [31, 172], [135, 60], [90, 103], [0, 1]], ![[0, 1], [0, 119], [6, 22], [59, 89], [101, 1], [87, 113], [146, 70], [103, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [168]]
 b := ![[], [172, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [83, 70, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3409, -1160, 73]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![10, -70, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![22, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![22, 1, 0]] 
 ![![173, 0, 0], ![22, 1, 0], ![35, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![22, 1, 0], ![0, 22, 1], ![-679, 137, 23]]]
  hmulB := by decide  
  f := ![![![2113, 96, 0], ![-16608, 0, 0]], ![![242, 11, 0], ![-1902, 0, 0]], ![![399, 18, 0], ![-3136, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 173, 0], ![-35, 0, 173]], ![![0, 1, 0], ![-3, 22, 1], ![-26, 137, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-150, -23, 1]] ![![173, 0, 0], ![22, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![3806, 173, 0]], ![![-25950, -3979, 173], ![-3979, -519, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![22, 1, 0]]], ![![![-150, -23, 1]], ![![-23, -3, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![19, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![19, 1, 0]] 
 ![![179, 0, 0], ![19, 1, 0], ![176, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![19, 1, 0], ![0, 19, 1], ![-679, 137, 20]]]
  hmulB := by decide  
  f := ![![![1141, 60, 0], ![-10740, 0, 0]], ![![95, 5, 0], ![-894, 0, 0]], ![![1124, 59, 0], ![-10580, 1, 0]]]
  g := ![![![1, 0, 0], ![-19, 179, 0], ![-176, 0, 179]], ![![0, 1, 0], ![-3, 19, 1], ![-38, 137, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-16, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-16, 1, 0]] 
 ![![179, 0, 0], ![163, 1, 0], ![102, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-16, 1, 0], ![0, -16, 1], ![-679, 137, -15]]]
  hmulB := by decide  
  f := ![![![1025, -64, 0], ![11456, 0, 0]], ![![945, -59, 0], ![10562, 0, 0]], ![![578, -36, 0], ![6460, 1, 0]]]
  g := ![![![1, 0, 0], ![-163, 179, 0], ![-102, 0, 179]], ![![-1, 1, 0], ![14, -16, 1], ![-120, 137, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![179, 0, 0], ![175, 1, 0], ![163, 0, 1]] where
  M :=![![![-4, 1, 0], ![0, -4, 1], ![-679, 137, -3]]]
  hmulB := by decide  
  f := ![![![125, -3, -1]], ![![126, -3, -1]], ![![129, -2, -1]]]
  g := ![![![-1, 1, 0], ![3, -4, 1], ![-135, 137, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![19, 1, 0]] ![![179, 0, 0], ![-16, 1, 0]]
  ![![-125, 3, 1]] where
 M := ![![![32041, 0, 0], ![-2864, 179, 0]], ![![3401, 179, 0], ![-304, 3, 1]]]
 hmul := by decide  
 g := ![![![![716, -179, 0]], ![![-64, 20, -1]]], ![![![76, -15, -1]], ![![-3, 1, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-125, 3, 1]] ![![-4, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [180, 6, 173, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 166, 145], [5, 14, 36], [0, 1]]
 g := ![![[3, 14, 132], [91, 29], [20, 152, 145], [22, 5], [40, 13, 129], [58, 8, 1], []], ![[20, 160, 159, 133], [72, 42], [167, 68, 162, 11], [29, 60], [87, 113, 166, 133], [138, 61, 45, 3], [45, 29]], ![[143, 31, 150, 106], [173, 167], [11, 69, 147, 144], [159, 129], [118, 55, 95, 108], [38, 146, 70, 136], [154, 29]]]
 h' := ![![[3, 166, 145], [129, 8, 48], [20, 81, 36], [174, 148, 114], [40, 60, 27], [58, 22, 55], [0, 0, 1], [0, 1]], ![[5, 14, 36], [30, 101, 22], [35, 82, 122], [77, 47, 69], [49, 118, 28], [17, 108, 159], [54, 31, 14], [3, 166, 145]], ![[0, 1], [73, 72, 111], [172, 18, 23], [143, 167, 179], [105, 3, 126], [58, 51, 148], [179, 150, 166], [5, 14, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63, 61], []]
 b := ![[], [142, 169, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [180, 6, 173, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125795, -1257045, 234938]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![695, -6945, 1298]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![30, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![30, 1, 0]] 
 ![![191, 0, 0], ![30, 1, 0], ![55, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![30, 1, 0], ![0, 30, 1], ![-679, 137, 31]]]
  hmulB := by decide  
  f := ![![![2911, 97, 0], ![-18527, 0, 0]], ![![450, 15, 0], ![-2864, 0, 0]], ![![815, 27, 0], ![-5187, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 191, 0], ![-55, 0, 191]], ![![0, 1, 0], ![-5, 30, 1], ![-34, 137, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-20, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-20, 1, 0]] 
 ![![191, 0, 0], ![171, 1, 0], ![173, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-20, 1, 0], ![0, -20, 1], ![-679, 137, -19]]]
  hmulB := by decide  
  f := ![![![1921, -96, 0], ![18336, 0, 0]], ![![1741, -87, 0], ![16618, 0, 0]], ![![1763, -88, 0], ![16828, 1, 0]]]
  g := ![![![1, 0, 0], ![-171, 191, 0], ![-173, 0, 191]], ![![-1, 1, 0], ![17, -20, 1], ![-109, 137, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-11, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-11, 1, 0]] 
 ![![191, 0, 0], ![180, 1, 0], ![70, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-11, 1, 0], ![0, -11, 1], ![-679, 137, -10]]]
  hmulB := by decide  
  f := ![![![1596, -145, 0], ![27695, 0, 0]], ![![1508, -137, 0], ![26168, 0, 0]], ![![584, -53, 0], ![10134, 1, 0]]]
  g := ![![![1, 0, 0], ![-180, 191, 0], ![-70, 0, 191]], ![![-1, 1, 0], ![10, -11, 1], ![-129, 137, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![30, 1, 0]] ![![191, 0, 0], ![-20, 1, 0]]
  ![![191, 0, 0], ![-27, 10, 1]] where
 M := ![![![36481, 0, 0], ![-3820, 191, 0]], ![![5730, 191, 0], ![-600, 10, 1]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![7, -9, -1], ![191, 0, 0]]], ![![![30, 1, 0], ![0, 0, 0]], ![![-3, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-27, 10, 1]] ![![191, 0, 0], ![-11, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-2101, 191, 0]], ![![-5157, 1910, 191], ![-382, 0, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-11, 1, 0]]], ![![![-27, 10, 1]], ![![-2, 0, 0]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![281, -82, 6]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![281, -82, 6]] 
 ![![193, 0, 0], ![0, 193, 0], ![79, 115, 1]] where
  M :=![![![281, -82, 6], ![-4074, 1103, -76], ![51604, -14486, 1027]]]
  hmulB := by decide  
  f := ![![![165, -14, -2]], ![![1358, -109, -16]], ![![933, -75, -11]]]
  g := ![![![-1, -4, 6], ![10, 51, -76], ![-153, -687, 1027]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [94, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 192], [0, 1]]
 g := ![![[30, 83], [191], [65], [143], [147], [110], [75, 1]], ![[79, 110], [191], [65], [143], [147], [110], [150, 192]]]
 h' := ![![[75, 192], [95, 135], [10, 159], [41, 79], [121, 23], [64, 98], [91, 127], [0, 1]], ![[0, 1], [184, 58], [162, 34], [176, 114], [109, 170], [80, 95], [159, 66], [75, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [68, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [94, 118, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24778, -8868, 856]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-222, -556, 856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-165, 14, 2]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-165, 14, 2]] 
 ![![193, 0, 0], ![77, 1, 0], ![54, 0, 1]] where
  M :=![![![-165, 14, 2], ![-1358, 109, 16], ![-10864, 834, 125]]]
  hmulB := by decide  
  f := ![![![-281, 82, -6]], ![![-91, 27, -2]], ![![-346, 98, -7]]]
  g := ![![![-7, 14, 2], ![-55, 109, 16], ![-424, 834, 125]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![281, -82, 6]] ![![-165, 14, 2]]
  ![![193, 0, 0]] where
 M := ![![![-193, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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
  g := ![2, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB194I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
    · exact ![5929741]
    · exact ![191, 191, 191]
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
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N1, I167N1, I173N1, I179N0, I179N1, I179N2, I191N0, I191N1, I191N2, I193N1]
  Il := ![[I139N1], [I149N1], [I151N1], [], [], [I167N1], [I173N1], [I179N0, I179N1, I179N2], [], [I191N0, I191N1, I191N2], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
