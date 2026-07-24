
import IdealArithmetic.Examples.NF3_1_377196_2.RI3_1_377196_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-35, -43, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-35, -43, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![104, 96, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-35, -43, 1], ![75, -27, -300], ![-5056, -326, -70]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -96, 139]], ![![-1, -1, 1], ![225, 207, -300], ![16, 46, -70]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [124, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 138], [0, 1]]
 g := ![![[125, 37], [21, 34], [86], [41, 66], [127], [37], [1]], ![[0, 102], [109, 105], [86], [81, 73], [127], [37], [1]]]
 h' := ![![[68, 138], [37, 71], [45, 112], [59, 15], [95, 30], [85, 108], [15, 68], [0, 1]], ![[0, 1], [0, 68], [16, 27], [106, 124], [50, 109], [62, 31], [52, 71], [68, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106]]
 b := ![[], [5, 53]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [124, 71, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2589, 925, -70]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![71, 55, -70]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![22, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![22, 1, 0]] 
 ![![139, 0, 0], ![22, 1, 0], ![70, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![22, 1, 0], ![1, 22, 7], ![118, 8, 23]]]
  hmulB := by decide  
  f := ![![![1680, 38870, 12369], ![556, -245613, 0]], ![![257, 6137, 1953], ![140, -38781, 0]], ![![828, 19574, 6229], ![394, -123690, 0]]]
  g := ![![![1, 0, 0], ![-22, 139, 0], ![-70, 0, 139]], ![![0, 1, 0], ![-7, 22, 7], ![-12, 8, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-35, -43, 1]] ![![139, 0, 0], ![22, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![3058, 139, 0]], ![![-4865, -5977, 139], ![-695, -973, -278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![22, 1, 0]]], ![![![-35, -43, 1]], ![![-5, -7, -2]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-50, 39, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-50, 39, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![99, 39, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-50, 39, 1], ![157, -42, 274], ![4620, 330, -3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-99, -39, 149]], ![![-1, 0, 1], ![-181, -72, 274], ![33, 3, -3]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [13, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 148], [0, 1]]
 g := ![![[16, 25], [102], [64, 119], [103], [13, 20], [54], [1]], ![[31, 124], [102], [46, 30], [103], [25, 129], [54], [1]]]
 h' := ![![[90, 148], [134, 144], [62, 129], [104, 62], [129, 111], [63, 136], [136, 90], [0, 1]], ![[0, 1], [131, 5], [50, 20], [22, 87], [136, 38], [85, 13], [41, 59], [90, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [147]]
 b := ![[], [45, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [13, 59, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2891, 3444, 2713]
  a := ![2, -2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1822, -687, 2713]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![24, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![24, 1, 0]] 
 ![![149, 0, 0], ![24, 1, 0], ![3, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![24, 1, 0], ![1, 24, 7], ![118, 8, 25]]]
  hmulB := by decide  
  f := ![![![-7285, -184064, -53690], ![-2384, 1142830, 0]], ![![-1187, -29638, -8645], ![-297, 184015, 0]], ![![-147, -3706, -1081], ![-46, 23010, 0]]]
  g := ![![![1, 0, 0], ![-24, 149, 0], ![-3, 0, 149]], ![![0, 1, 0], ![-4, 24, 7], ![-1, 8, 25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-50, 39, 1]] ![![149, 0, 0], ![24, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![3576, 149, 0]], ![![-7450, 5811, 149], ![-1043, 894, 298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![24, 1, 0]]], ![![![-50, 39, 1]], ![![-7, 6, 2]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-54354, -8251, -5357]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-54354, -8251, -5357]] 
 ![![151, 0, 0], ![48, 1, 0], ![124, 0, 1]] where
  M :=![![![-54354, -8251, -5357], ![-640377, -97210, -63114], ![-1070044, -162434, -105461]]]
  hmulB := by decide  
  f := ![![![-4334, -227, 356]], ![![-1101, -82, 105]], ![![-3694, -156, 281]]]
  g := ![![![6662, -8251, -5357], ![78489, -97210, -63114], ![131152, -162434, -105461]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2395761, 188152, 9094]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-2395761, 188152, 9094]] 
 ![![151, 0, 0], ![49, 1, 0], ![67, 0, 1]] where
  M :=![![![-2395761, 188152, 9094], ![1261244, -2323009, 1326158], ![22365628, 1668908, -2134857]]]
  hmulB := by decide  
  f := ![![![2746056329249, 416854663616, 270644723862]], ![![1105362200083, 167795315479, 108941846612]], ![![1576465095337, 239309303316, 155372617765]]]
  g := ![![![-80957, 188152, 9094], ![173749, -2323009, 1326158], ![553805, 1668908, -2134857]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10684006, -1621845, -1052990]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![-10684006, -1621845, -1052990]] 
 ![![151, 0, 0], ![53, 1, 0], ![95, 0, 1]] where
  M :=![![![-10684006, -1621845, -1052990], ![-125874665, -19107926, -12405905], ![-210331530, -31928580, -20729771]]]
  hmulB := by decide  
  f := ![![![-46, -6705, 4015]], ![![3077, -2141, 1125]], ![![-4790, -4095, 2694]]]
  g := ![![![1160979, -1621845, -1052990], ![13678188, -19107926, -12405905], ![22855705, -31928580, -20729771]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-54354, -8251, -5357]] ![![-2395761, 188152, 9094]]
  ![![-46, -6705, 4015]] where
 M := ![![![-46, -6705, 4015]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![-46, -6705, 4015]] ![![-10684006, -1621845, -1052990]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [94, 96, 13, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 98, 61], [41, 58, 96], [0, 1]]
 g := ![![[44, 40, 148], [145, 106], [116, 32, 11], [9, 144, 89], [88, 140, 148], [144, 1], []], ![[52, 29, 57, 137], [28, 25], [103, 56, 51, 83], [16, 120, 46, 131], [105, 83, 117, 62], [27, 67], [7, 110]], ![[127, 141, 6, 32], [103, 140], [32, 9, 22, 128], [63, 90, 19, 129], [69, 35, 31, 97], [59, 27], [129, 110]]]
 h' := ![![[103, 98, 61], [46, 7, 73], [86, 96, 48], [96, 90, 110], [49, 115, 106], [123, 55, 73], [0, 0, 1], [0, 1]], ![[41, 58, 96], [123, 144, 108], [137, 51, 5], [109, 35, 95], [42, 7, 132], [120, 138, 53], [60, 70, 58], [103, 98, 61]], ![[0, 1], [83, 6, 133], [38, 10, 104], [151, 32, 109], [48, 35, 76], [87, 121, 31], [74, 87, 98], [41, 58, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118, 28], []]
 b := ![[], [92, 40, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [94, 96, 13, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-135616238586, -17677851146, -6143042149]
  a := ![-65, 1, -391]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-863797698, -112597778, -39127657]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-77, -23, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-77, -23, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![86, 140, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-77, -23, 1], ![95, -69, -160], ![-2696, -166, -92]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-86, -140, 163]], ![![-1, -1, 1], ![85, 137, -160], ![32, 78, -92]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [108, 159, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [4, 162], [0, 1]]
 g := ![![[6, 22], [149, 35], [131], [151], [38], [15, 16], [1]], ![[94, 141], [126, 128], [131], [151], [38], [79, 147], [1]]]
 h' := ![![[4, 162], [45, 115], [107, 144], [143, 91], [71, 71], [10, 53], [55, 4], [0, 1]], ![[0, 1], [16, 48], [31, 19], [18, 72], [29, 92], [59, 110], [71, 159], [4, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58]]
 b := ![[], [105, 29]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [108, 159, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![305, 3965, -548]
  a := ![-2, 1, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![291, 495, -548]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-3, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-3, 1, 0]] 
 ![![163, 0, 0], ![160, 1, 0], ![92, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-3, 1, 0], ![1, -3, 7], ![118, 8, -2]]]
  hmulB := by decide  
  f := ![![![-7715, 23164, -54054], ![326, 1258686, 0]], ![![-7572, 22735, -53053], ![327, 1235377, 0]], ![![-4354, 13074, -30509], ![210, 710424, 0]]]
  g := ![![![1, 0, 0], ![-160, 163, 0], ![-92, 0, 163]], ![![-1, 1, 0], ![-1, -3, 7], ![-6, 8, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-77, -23, 1]] ![![163, 0, 0], ![-3, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-489, 163, 0]], ![![-12551, -3749, 163], ![326, 0, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-3, 1, 0]]], ![![![-77, -23, 1]], ![![2, 0, -1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [149, 12, 116, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 100, 88], [5, 66, 79], [0, 1]]
 g := ![![[151, 0, 84], [57, 130, 89], [126, 164, 9], [132, 62], [156, 89], [84, 51, 1], []], ![[29, 31, 79, 152], [135, 32, 121, 29], [118, 139, 145, 58], [99, 63], [38, 122], [0, 85, 100, 63], [54, 62]], ![[107, 155, 95, 86], [137, 121, 131, 40], [95, 28, 118, 70], [145, 18], [103, 1], [78, 28, 96, 90], [63, 62]]]
 h' := ![![[46, 100, 88], [24, 43, 90], [97, 24, 16], [33, 77, 164], [50, 114, 79], [9, 77, 16], [0, 0, 1], [0, 1]], ![[5, 66, 79], [30, 8, 38], [8, 108, 162], [156, 72, 65], [82, 125, 49], [20, 64, 150], [82, 149, 66], [46, 100, 88]], ![[0, 1], [7, 116, 39], [57, 35, 156], [114, 18, 105], [164, 95, 39], [67, 26, 1], [157, 18, 100], [5, 66, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 133], []]
 b := ![[], [73, 75, 156], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [149, 12, 116, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-636103, -1002, -7014]
  a := ![-1, -1, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3809, -6, -42]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [121, 153, 113, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 150, 119], [146, 22, 54], [0, 1]]
 g := ![![[5, 94, 158], [1, 21], [65, 159, 84], [126, 85, 144], [24, 133], [160, 60, 1], []], ![[150, 83, 132, 38], [105, 95], [52, 154, 164, 4], [68, 11, 138, 122], [96, 41], [168, 137, 34, 160], [119, 148]], ![[18, 115, 58, 126], [114, 172], [92, 41, 85, 89], [111, 63, 49, 118], [26, 36], [78, 50, 63, 21], [11, 148]]]
 h' := ![![[87, 150, 119], [51, 135, 37], [93, 18, 114], [151, 61, 55], [120, 133, 161], [16, 92, 126], [0, 0, 1], [0, 1]], ![[146, 22, 54], [75, 20, 98], [155, 22, 152], [28, 161, 165], [58, 0, 166], [157, 105, 53], [90, 19, 22], [87, 150, 119]], ![[0, 1], [82, 18, 38], [6, 133, 80], [167, 124, 126], [120, 40, 19], [49, 149, 167], [90, 154, 150], [146, 22, 54]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117, 105], []]
 b := ![[], [60, 142, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [121, 153, 113, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![29031822, 4431568, 2889446]
  a := ![2, 19, 13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![167814, 25616, 16702]
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



lemma PB174I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 173 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 173 (by omega)

def PB174I3 : PrimesBelowBoundCertificateInterval O 137 173 174 where
  m := 7
  g := ![2, 2, 3, 1, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB174I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
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
      exact NI151N2
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I163N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [], [I163N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
