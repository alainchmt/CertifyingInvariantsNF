
import IdealArithmetic.Examples.NF3_1_853335_2.RI3_1_853335_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![55, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![55, 1, 0]] 
 ![![139, 0, 0], ![55, 1, 0], ![104, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![55, 1, 0], ![0, 55, 7], ![203, 21, 55]]]
  hmulB := by decide  
  f := ![![![2696, 49, 0], ![-6811, 0, 0]], ![![990, 18, 0], ![-2501, 0, 0]], ![![1976, 28, -1], ![-4992, 20, 0]]]
  g := ![![![1, 0, 0], ![-55, 139, 0], ![-104, 0, 139]], ![![0, 1, 0], ![-27, 55, 7], ![-48, 21, 55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-47, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-47, 1, 0]] 
 ![![139, 0, 0], ![92, 1, 0], ![22, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-47, 1, 0], ![0, -47, 7], ![203, 21, -47]]]
  hmulB := by decide  
  f := ![![![4372, -93, 0], ![12927, 0, 0]], ![![2868, -61, 0], ![8480, 0, 0]], ![![694, -8, -1], ![2052, 20, 0]]]
  g := ![![![1, 0, 0], ![-92, 139, 0], ![-22, 0, 139]], ![![-1, 1, 0], ![30, -47, 7], ![-5, 21, -47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-8, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-8, 1, 0]] 
 ![![139, 0, 0], ![131, 1, 0], ![110, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-8, 1, 0], ![0, -8, 7], ![203, 21, -8]]]
  hmulB := by decide  
  f := ![![![729, -91, 0], ![12649, 0, 0]], ![![689, -86, 0], ![11955, 0, 0]], ![![586, -72, -1], ![10168, 20, 0]]]
  g := ![![![1, 0, 0], ![-131, 139, 0], ![-110, 0, 139]], ![![-1, 1, 0], ![2, -8, 7], ![-12, 21, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![55, 1, 0]] ![![139, 0, 0], ![-47, 1, 0]]
  ![![139, 0, 0], ![8, 21, 1]] where
 M := ![![![19321, 0, 0], ![-6533, 139, 0]], ![![7645, 139, 0], ![-2585, 8, 7]]]
 hmul := by decide  
 g := ![![![![131, -21, -1], ![139, 0, 0]], ![![-47, 1, 0], ![0, 0, 0]]], ![![![47, -20, -1], ![139, 0, 0]], ![![-19, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![8, 21, 1]] ![![139, 0, 0], ![-8, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-1112, 139, 0]], ![![1112, 2919, 139], ![139, -139, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-8, 1, 0]]], ![![![8, 21, 1]], ![![1, -1, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-2, 60, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-2, 60, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![147, 60, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-2, 60, 1], ![203, 19, 420], ![12180, 1289, 19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-147, -60, 149]], ![![-1, 0, 1], ![-413, -169, 420], ![63, 1, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [85, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 148], [0, 1]]
 g := ![![[97, 142], [107], [123, 4], [19], [94, 26], [116], [1]], ![[0, 7], [107], [72, 145], [19], [135, 123], [116], [1]]]
 h' := ![![[99, 148], [23, 69], [124, 133], [31, 147], [56, 67], [47, 18], [64, 99], [0, 1]], ![[0, 1], [0, 80], [30, 16], [131, 2], [133, 82], [41, 131], [31, 50], [99, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [100, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [85, 50, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![491, 21, -22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, 9, -22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![27, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![27, 1, 0]] 
 ![![149, 0, 0], ![27, 1, 0], ![130, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![27, 1, 0], ![0, 27, 7], ![203, 21, 27]]]
  hmulB := by decide  
  f := ![![![2485, 92, 0], ![-13708, 0, 0]], ![![405, 15, 0], ![-2234, 0, 0]], ![![2150, 68, -3], ![-11860, 64, 0]]]
  g := ![![![1, 0, 0], ![-27, 149, 0], ![-130, 0, 149]], ![![0, 1, 0], ![-11, 27, 7], ![-26, 21, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-2, 60, 1]] ![![149, 0, 0], ![27, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![4023, 149, 0]], ![![-298, 8940, 149], ![149, 1639, 447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![27, 1, 0]]], ![![![-2, 60, 1]], ![![1, 11, 3]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-59, -44, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-59, -44, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![92, 107, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-59, -44, 1], ![203, -38, -308], ![-8932, -895, -38]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-92, -107, 151]], ![![-1, -1, 1], ![189, 218, -308], ![-36, 21, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [15, 76, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 150], [0, 1]]
 g := ![![[146, 31], [104, 10], [22, 72], [80], [34, 16], [38], [1]], ![[55, 120], [99, 141], [137, 79], [80], [26, 135], [38], [1]]]
 h' := ![![[75, 150], [101, 129], [123, 114], [86, 125], [94, 82], [108, 147], [136, 75], [0, 1]], ![[0, 1], [112, 22], [66, 37], [99, 26], [53, 69], [110, 4], [23, 76], [75, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [127, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [15, 76, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2496, -139, 439]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-284, -312, 439]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![6, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![6, 1, 0]] 
 ![![151, 0, 0], ![6, 1, 0], ![38, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![6, 1, 0], ![0, 6, 7], ![203, 21, 6]]]
  hmulB := by decide  
  f := ![![![697, 116, 0], ![-17516, 0, 0]], ![![18, 3, 0], ![-452, 0, 0]], ![![170, 24, -5], ![-4272, 108, 0]]]
  g := ![![![1, 0, 0], ![-6, 151, 0], ![-38, 0, 151]], ![![0, 1, 0], ![-2, 6, 7], ![-1, 21, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-59, -44, 1]] ![![151, 0, 0], ![6, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![906, 151, 0]], ![![-8909, -6644, 151], ![-151, -302, -302]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![6, 1, 0]]], ![![![-59, -44, 1]], ![![-1, -2, -2]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [24, 41, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 102, 108], [7, 54, 49], [0, 1]]
 g := ![![[82, 80, 68], [78, 145], [41, 87, 75], [38, 86, 10], [140, 13, 118], [80, 1], []], ![[115, 115, 123, 100], [27, 146], [18, 75, 73, 67], [121, 113, 150, 109], [9, 22, 113, 39], [147, 90], [121, 46]], ![[56, 136, 80, 17], [36, 100], [109, 73, 1, 75], [38, 138, 133, 109], [137, 70, 135, 9], [145, 42], [23, 46]]]
 h' := ![![[73, 102, 108], [49, 74, 142], [115, 114, 50], [30, 33, 46], [94, 111, 18], [121, 150, 79], [0, 0, 1], [0, 1]], ![[7, 54, 49], [5, 115, 117], [5, 33, 97], [7, 109, 82], [37, 20, 86], [116, 10, 56], [70, 35, 54], [73, 102, 108]], ![[0, 1], [105, 125, 55], [98, 10, 10], [45, 15, 29], [138, 26, 53], [56, 154, 22], [125, 122, 102], [7, 54, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 74], []]
 b := ![[], [90, 122, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [24, 41, 77, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![105661, 3611, -5966]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![673, 23, -38]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [150, 21, 123, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [114, 51, 28], [89, 111, 135], [0, 1]]
 g := ![![[84, 151, 156], [35, 152, 155], [55, 16], [68, 119], [87, 88], [112, 40, 1], []], ![[87, 124, 74, 122], [99, 23, 88, 109], [17, 91], [75, 10], [148, 144], [99, 99, 62, 80], [149, 132]], ![[129, 9, 8, 60], [89, 88, 87, 90], [151, 156], [118, 143], [24, 91], [34, 70, 28, 33], [42, 132]]]
 h' := ![![[114, 51, 28], [129, 25, 51], [67, 79, 36], [2, 12, 159], [111, 12, 49], [152, 124, 67], [0, 0, 1], [0, 1]], ![[89, 111, 135], [92, 151, 4], [122, 129, 14], [155, 13, 55], [22, 85, 70], [124, 98, 151], [100, 109, 111], [114, 51, 28]], ![[0, 1], [102, 150, 108], [91, 118, 113], [128, 138, 112], [86, 66, 44], [153, 104, 108], [154, 54, 51], [89, 111, 135]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 37], []]
 b := ![[], [112, 162, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [150, 21, 123, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-195600, -5379, 16137]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1200, -33, 99]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![26, -31, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![26, -31, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![26, 136, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![26, -31, 1], ![203, 47, -217], ![-6293, -622, 47]]]
  hmulB := by decide  
  f := ![![![-25, 31, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -136, 167]], ![![0, -1, 1], ![35, 177, -217], ![-45, -42, 47]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [154, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 166], [0, 1]]
 g := ![![[125, 77], [70, 150], [78, 24], [12], [132], [56, 21], [1]], ![[0, 90], [0, 17], [0, 143], [12], [132], [113, 146], [1]]]
 h' := ![![[122, 166], [75, 113], [12, 145], [105, 58], [139, 43], [60, 93], [13, 122], [0, 1]], ![[0, 1], [0, 54], [0, 22], [0, 109], [41, 124], [50, 74], [34, 45], [122, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [52, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [154, 45, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![560, 26, -17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6, 14, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![50, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![50, 1, 0]] 
 ![![167, 0, 0], ![50, 1, 0], ![120, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![50, 1, 0], ![0, 50, 7], ![203, 21, 50]]]
  hmulB := by decide  
  f := ![![![3751, 75, 0], ![-12525, 0, 0]], ![![1050, 21, 0], ![-3506, 0, 0]], ![![2660, 46, -1], ![-8882, 24, 0]]]
  g := ![![![1, 0, 0], ![-50, 167, 0], ![-120, 0, 167]], ![![0, 1, 0], ![-20, 50, 7], ![-41, 21, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![26, -31, 1]] ![![167, 0, 0], ![50, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![8350, 167, 0]], ![![4342, -5177, 167], ![1503, -1503, -167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![50, 1, 0]]], ![![![26, -31, 1]], ![![9, -9, -1]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-69, -28, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-69, -28, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![104, 145, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-69, -28, 1], ![203, -48, -196], ![-5684, -559, -48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -145, 173]], ![![-1, -1, 1], ![119, 164, -196], ![-4, 37, -48]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [69, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [10, 172], [0, 1]]
 g := ![![[50, 109], [126], [136, 24], [67, 54], [135], [139, 100], [1]], ![[102, 64], [126], [30, 149], [88, 119], [135], [101, 73], [1]]]
 h' := ![![[10, 172], [163, 52], [131, 105], [48, 71], [94, 153], [97, 116], [104, 10], [0, 1]], ![[0, 1], [164, 121], [143, 68], [66, 102], [67, 20], [46, 57], [31, 163], [10, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59]]
 b := ![[], [112, 116]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [69, 163, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7947, 3962, 2713]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1585, -2251, 2713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![23, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![23, 1, 0]] 
 ![![173, 0, 0], ![23, 1, 0], ![48, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![23, 1, 0], ![0, 23, 7], ![203, 21, 23]]]
  hmulB := by decide  
  f := ![![![2761, 120, 0], ![-20760, 0, 0]], ![![345, 15, 0], ![-2594, 0, 0]], ![![740, 19, -4], ![-5564, 99, 0]]]
  g := ![![![1, 0, 0], ![-23, 173, 0], ![-48, 0, 173]], ![![0, 1, 0], ![-5, 23, 7], ![-8, 21, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-69, -28, 1]] ![![173, 0, 0], ![23, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![3979, 173, 0]], ![![-11937, -4844, 173], ![-1384, -692, -173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![23, 1, 0]]], ![![![-69, -28, 1]], ![![-8, -4, -1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![65, 39, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![65, 39, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![65, 39, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![65, 39, 1], ![203, 86, 273], ![7917, 848, 86]]]
  hmulB := by decide  
  f := ![![![-64, -39, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-65, -39, 179]], ![![0, 0, 1], ![-98, -59, 273], ![13, -14, 86]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [39, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 178], [0, 1]]
 g := ![![[75, 101], [64, 48], [116], [149], [148, 172], [95, 141], [1]], ![[0, 78], [0, 131], [116], [149], [38, 7], [86, 38], [1]]]
 h' := ![![[118, 178], [10, 97], [161, 76], [63, 142], [135, 68], [54, 72], [140, 118], [0, 1]], ![[0, 1], [0, 82], [0, 103], [172, 37], [104, 111], [137, 107], [102, 61], [118, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [16, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [39, 61, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1239, 80, 25]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-16, -5, 25]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![85, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![85, 1, 0]] 
 ![![179, 0, 0], ![85, 1, 0], ![93, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![85, 1, 0], ![0, 85, 7], ![203, 21, 85]]]
  hmulB := by decide  
  f := ![![![4676, 55, 0], ![-9845, 0, 0]], ![![2210, 26, 0], ![-4653, 0, 0]], ![![2362, -33, -5], ![-4973, 128, 0]]]
  g := ![![![1, 0, 0], ![-85, 179, 0], ![-93, 0, 179]], ![![0, 1, 0], ![-44, 85, 7], ![-53, 21, 85]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![65, 39, 1]] ![![179, 0, 0], ![85, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![15215, 179, 0]], ![![11635, 6981, 179], ![5728, 3401, 358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![85, 1, 0]]], ![![![65, 39, 1]], ![![32, 19, 2]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [29, 37, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 36, 174], [37, 144, 7], [0, 1]]
 g := ![![[92, 170, 67], [77, 178], [40, 37, 34], [169, 46], [131, 150, 180], [141, 84, 1], []], ![[168, 139, 80, 118], [5, 49], [101, 128, 133, 23], [148, 36], [31, 40, 135, 18], [134, 118, 165, 10], [173, 49]], ![[166, 47, 25, 140], [91, 137], [159, 60, 24, 7], [45, 99], [105, 68, 120, 68], [129, 93, 5, 22], [159, 49]]]
 h' := ![![[47, 36, 174], [166, 92, 51], [107, 81, 97], [171, 154, 136], [2, 80, 107], [74, 130, 19], [0, 0, 1], [0, 1]], ![[37, 144, 7], [109, 147, 3], [142, 133, 7], [10, 0, 44], [146, 62, 6], [73, 179, 16], [88, 87, 144], [47, 36, 174]], ![[0, 1], [42, 123, 127], [131, 148, 77], [81, 27, 1], [149, 39, 68], [120, 53, 146], [16, 94, 36], [37, 144, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 78], []]
 b := ![[], [178, 144, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [29, 37, 97, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![178466, 35838, 15747]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![986, 198, 87]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-90, 40, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-90, 40, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![101, 40, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-90, 40, 1], ![203, -69, 280], ![8120, 869, -69]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-101, -40, 191]], ![![-1, 0, 1], ![-147, -59, 280], ![79, 19, -69]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [136, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [161, 190], [0, 1]]
 g := ![![[121, 125], [125, 36], [153, 177], [136, 30], [180, 6], [69, 136], [1]], ![[0, 66], [0, 155], [0, 14], [0, 161], [0, 185], [0, 55], [1]]]
 h' := ![![[161, 190], [190, 70], [11, 185], [31, 122], [159, 139], [166, 31], [55, 161], [0, 1]], ![[0, 1], [0, 121], [0, 6], [0, 69], [0, 52], [0, 160], [0, 30], [161, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103]]
 b := ![[], [104, 147]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [136, 30, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7920, -1064, 852]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-492, -184, 852]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-89, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-89, 1, 0]] 
 ![![191, 0, 0], ![102, 1, 0], ![69, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-89, 1, 0], ![0, -89, 7], ![203, 21, -89]]]
  hmulB := by decide  
  f := ![![![11215, -126, 0], ![24066, 0, 0]], ![![5964, -67, 0], ![12798, 0, 0]], ![![4113, -8, -3], ![8826, 82, 0]]]
  g := ![![![1, 0, 0], ![-102, 191, 0], ![-69, 0, 191]], ![![-1, 1, 0], ![45, -89, 7], ![22, 21, -89]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-90, 40, 1]] ![![191, 0, 0], ![-89, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-16999, 191, 0]], ![![-17190, 7640, 191], ![8213, -3629, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-89, 1, 0]]], ![![![-90, 40, 1]], ![![43, -19, 1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-106, -64, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-106, -64, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![87, 129, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-106, -64, 1], ![203, -85, -448], ![-12992, -1315, -85]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -129, 193]], ![![-1, -1, 1], ![203, 299, -448], ![-29, 50, -85]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [131, 102, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 192], [0, 1]]
 g := ![![[154, 28], [54], [49], [138], [50], [6], [91, 1]], ![[0, 165], [54], [49], [138], [50], [6], [182, 192]]]
 h' := ![![[91, 192], [70, 118], [14, 132], [185, 186], [11, 157], [81, 67], [45, 44], [0, 1]], ![[0, 1], [0, 75], [60, 61], [127, 7], [16, 36], [2, 126], [189, 149], [91, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [112, 146]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [131, 102, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1220, -141, 156]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -105, 156]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![62, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![62, 1, 0]] 
 ![![193, 0, 0], ![62, 1, 0], ![85, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![62, 1, 0], ![0, 62, 7], ![203, 21, 62]]]
  hmulB := by decide  
  f := ![![![5023, 81, 0], ![-15633, 0, 0]], ![![1550, 25, 0], ![-4824, 0, 0]], ![![2191, -9, -5], ![-6819, 138, 0]]]
  g := ![![![1, 0, 0], ![-62, 193, 0], ![-85, 0, 193]], ![![0, 1, 0], ![-23, 62, 7], ![-33, 21, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-106, -64, 1]] ![![193, 0, 0], ![62, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![11966, 193, 0]], ![![-20458, -12352, 193], ![-6369, -4053, -386]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![62, 1, 0]]], ![![![-106, -64, 1]], ![![-33, -21, -2]]]]
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


lemma PB262I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB262I3 : PrimesBelowBoundCertificateInterval O 137 193 262 where
  m := 11
  g := ![3, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB262I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
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
      exact NI139N1
      exact NI139N2
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
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I149N1, I151N1, I167N1, I173N1, I179N1, I191N1, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [I151N1], [], [], [I167N1], [I173N1], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
