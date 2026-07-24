
import IdealArithmetic.Examples.NF3_1_936684_4.RI3_1_936684_4
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [42, 84, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [16, 72, 16], [94, 66, 123], [0, 1]]
 g := ![![[132, 29, 63], [135, 113, 69], [19, 55], [74, 80, 121], [93, 91], [110, 1], []], ![[47, 78, 64, 41], [123, 1, 25, 31], [39, 91], [107, 119, 82, 120], [7, 1], [129, 47], [23, 117]], ![[21, 96, 9, 135], [42, 74, 47, 3], [40, 9], [134, 15, 113, 104], [49, 77], [115, 41], [55, 117]]]
 h' := ![![[16, 72, 16], [29, 82, 52], [34, 30, 114], [89, 133, 74], [102, 81, 11], [106, 31, 62], [0, 0, 1], [0, 1]], ![[94, 66, 123], [5, 43, 18], [55, 62, 81], [134, 118, 62], [121, 72, 76], [89, 18, 1], [124, 45, 66], [16, 72, 16]], ![[0, 1], [6, 14, 69], [110, 47, 83], [119, 27, 3], [133, 125, 52], [84, 90, 76], [132, 94, 72], [94, 66, 123]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57, 104], []]
 b := ![[], [85, 67, 63], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [42, 84, 29, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-190708, -66164, -5977]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1372, -476, -43]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![11, -63, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![11, -63, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![11, 86, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![11, -63, 1], ![350, 95, -63], ![-22050, -4942, 95]]]
  hmulB := by decide  
  f := ![![![-10, 63, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -86, 149]], ![![0, -1, 1], ![7, 37, -63], ![-155, -88, 95]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [12, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 148], [0, 1]]
 g := ![![[129, 142], [68], [140, 124], [69], [102, 102], [86], [1]], ![[88, 7], [68], [100, 25], [69], [146, 47], [86], [1]]]
 h' := ![![[91, 148], [120, 69], [108, 51], [47, 78], [117, 48], [6, 129], [137, 91], [0, 1]], ![[0, 1], [141, 80], [130, 98], [142, 71], [15, 101], [123, 20], [74, 58], [91, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [22, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [12, 58, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4245, 2030, 928]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-97, -522, 928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![63, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![63, 1, 0]] 
 ![![149, 0, 0], ![63, 1, 0], ![54, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![63, 1, 0], ![0, 63, 1], ![350, 84, 63]]]
  hmulB := by decide  
  f := ![![![3088, 49, 0], ![-7301, 0, 0]], ![![1260, 20, 0], ![-2979, 0, 0]], ![![1098, 17, 0], ![-2596, 1, 0]]]
  g := ![![![1, 0, 0], ![-63, 149, 0], ![-54, 0, 149]], ![![0, 1, 0], ![-27, 63, 1], ![-56, 84, 63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![11, -63, 1]] ![![149, 0, 0], ![63, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![9387, 149, 0]], ![![1639, -9387, 149], ![1043, -3874, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![63, 1, 0]]], ![![![11, -63, 1]], ![![7, -26, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-66, 13, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-66, 13, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![85, 13, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-66, 13, 1], ![350, 18, 13], ![4550, 1442, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-85, -13, 151]], ![![-1, 0, 1], ![-5, -1, 13], ![20, 8, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [142, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 150], [0, 1]]
 g := ![![[18, 118], [19, 97], [125, 136], [21], [111, 59], [121], [1]], ![[108, 33], [29, 54], [111, 15], [21], [5, 92], [121], [1]]]
 h' := ![![[11, 150], [20, 119], [68, 90], [80, 49], [93, 25], [113, 19], [9, 11], [0, 1]], ![[0, 1], [121, 32], [1, 61], [15, 102], [66, 126], [20, 132], [130, 140], [11, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [27, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [142, 140, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5422, 194, 73]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -5, 73]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-13, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-13, 1, 0]] 
 ![![151, 0, 0], ![138, 1, 0], ![133, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-13, 1, 0], ![0, -13, 1], ![350, 84, -13]]]
  hmulB := by decide  
  f := ![![![1314, -101, 0], ![15251, 0, 0]], ![![1184, -91, 0], ![13742, 0, 0]], ![![1146, -88, 0], ![13301, 1, 0]]]
  g := ![![![1, 0, 0], ![-138, 151, 0], ![-133, 0, 151]], ![![-1, 1, 0], ![11, -13, 1], ![-63, 84, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-66, 13, 1]] ![![151, 0, 0], ![-13, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-1963, 151, 0]], ![![-9966, 1963, 151], ![1208, -151, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-13, 1, 0]]], ![![![-66, 13, 1]], ![![8, -1, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-49, -52, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-49, -52, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![108, 105, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-49, -52, 1], ![350, 35, -52], ![-18200, -4018, 35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-108, -105, 157]], ![![-1, -1, 1], ![38, 35, -52], ![-140, -49, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [127, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [126, 156], [0, 1]]
 g := ![![[67, 68], [17], [13, 122], [132, 89], [9, 44], [19], [1]], ![[0, 89], [17], [156, 35], [42, 68], [58, 113], [19], [1]]]
 h' := ![![[126, 156], [6, 142], [76, 86], [35, 43], [113, 51], [57, 63], [30, 126], [0, 1]], ![[0, 1], [0, 15], [79, 71], [115, 114], [102, 106], [145, 94], [49, 31], [126, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [150, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [127, 31, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1941, 2679, 658]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-465, -423, 658]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![52, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![52, 1, 0]] 
 ![![157, 0, 0], ![52, 1, 0], ![122, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![52, 1, 0], ![0, 52, 1], ![350, 84, 52]]]
  hmulB := by decide  
  f := ![![![3225, 62, 0], ![-9734, 0, 0]], ![![1092, 21, 0], ![-3296, 0, 0]], ![![2514, 48, 0], ![-7588, 1, 0]]]
  g := ![![![1, 0, 0], ![-52, 157, 0], ![-122, 0, 157]], ![![0, 1, 0], ![-18, 52, 1], ![-66, 84, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-49, -52, 1]] ![![157, 0, 0], ![52, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![8164, 157, 0]], ![![-7693, -8164, 157], ![-2198, -2669, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![52, 1, 0]]], ![![![-49, -52, 1]], ![![-14, -17, 0]]]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [51, 54, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 9, 61], [87, 153, 102], [0, 1]]
 g := ![![[5, 109, 156], [151, 44, 144], [36, 46], [77, 155], [124, 140], [134, 158, 1], []], ![[113, 128, 19, 74], [105, 42, 39, 97], [97, 51], [85, 57], [162, 87], [2, 152, 93, 69], [97, 135]], ![[10, 156, 118, 79], [104, 60, 39, 89], [120, 81], [95, 21], [16, 95], [121, 10, 89, 112], [56, 135]]]
 h' := ![![[71, 9, 61], [123, 103, 51], [118, 104, 151], [18, 113, 131], [14, 39, 36], [12, 28, 38], [0, 0, 1], [0, 1]], ![[87, 153, 102], [5, 76, 68], [17, 24, 107], [143, 52, 41], [136, 153, 63], [30, 43, 24], [94, 76, 153], [71, 9, 61]], ![[0, 1], [57, 147, 44], [43, 35, 68], [28, 161, 154], [132, 134, 64], [123, 92, 101], [149, 87, 9], [87, 153, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [114, 26], []]
 b := ![[], [150, 105, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [51, 54, 5, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-207499, -78566, -7987]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1273, -482, -49]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [1, 40, 163, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 18, 7], [100, 148, 160], [0, 1]]
 g := ![![[96, 4, 162], [45, 32, 11], [83, 156, 56], [12, 81], [99, 84], [143, 4, 1], []], ![[51, 27, 86, 99], [16, 44, 56, 133], [85, 42, 74, 61], [158, 29], [79, 32], [90, 115, 81, 22], [114, 49]], ![[3, 4, 12, 102], [127, 60, 61, 131], [16, 1, 136, 73], [10, 25], [65, 108], [135, 123, 146, 70], [128, 49]]]
 h' := ![![[71, 18, 7], [122, 47, 50], [84, 159, 126], [63, 104, 35], [143, 94, 9], [24, 121, 77], [0, 0, 1], [0, 1]], ![[100, 148, 160], [144, 66, 47], [80, 28, 55], [33, 157, 63], [58, 82, 153], [53, 75, 52], [84, 118, 148], [71, 18, 7]], ![[0, 1], [94, 54, 70], [8, 147, 153], [106, 73, 69], [28, 158, 5], [60, 138, 38], [19, 49, 18], [100, 148, 160]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 67], []]
 b := ![[], [41, 41, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [1, 40, 163, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6406955, 2011181, 192217]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![38365, 12043, 1151]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-109, -54, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-109, -54, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![64, 119, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-109, -54, 1], ![350, -25, -54], ![-18900, -4186, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -119, 173]], ![![-1, -1, 1], ![22, 37, -54], ![-100, -7, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [45, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 172], [0, 1]]
 g := ![![[93, 113], [78], [39, 10], [148, 109], [100], [76, 51], [1]], ![[170, 60], [78], [55, 163], [11, 64], [100], [123, 122], [1]]]
 h' := ![![[140, 172], [56, 99], [148, 123], [87, 23], [41, 52], [40, 163], [128, 140], [0, 1]], ![[0, 1], [76, 74], [68, 50], [20, 150], [55, 121], [24, 10], [6, 33], [140, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110]]
 b := ![[], [129, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [45, 33, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2087, -61, 62]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -43, 62]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![54, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![54, 1, 0]] 
 ![![173, 0, 0], ![54, 1, 0], ![25, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![54, 1, 0], ![0, 54, 1], ![350, 84, 54]]]
  hmulB := by decide  
  f := ![![![4051, 75, 0], ![-12975, 0, 0]], ![![1242, 23, 0], ![-3978, 0, 0]], ![![503, 9, 0], ![-1611, 1, 0]]]
  g := ![![![1, 0, 0], ![-54, 173, 0], ![-25, 0, 173]], ![![0, 1, 0], ![-17, 54, 1], ![-32, 84, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-109, -54, 1]] ![![173, 0, 0], ![54, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![9342, 173, 0]], ![![-18857, -9342, 173], ![-5536, -2941, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![54, 1, 0]]], ![![![-109, -54, 1]], ![![-32, -17, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-134, -32, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-134, -32, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![45, 147, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-134, -32, 1], ![350, -50, -32], ![-11200, -2338, -50]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -147, 179]], ![![-1, -1, 1], ![10, 26, -32], ![-50, 28, -50]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [106, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 178], [0, 1]]
 g := ![![[53, 76], [142, 108], [145], [117], [0, 158], [85, 107], [1]], ![[0, 103], [29, 71], [145], [117], [17, 21], [41, 72], [1]]]
 h' := ![![[110, 178], [163, 75], [119, 65], [128, 161], [0, 98], [119, 115], [73, 110], [0, 1]], ![[0, 1], [0, 104], [109, 114], [117, 18], [40, 81], [60, 64], [1, 69], [110, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [90, 96]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [106, 69, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1506, 1805, 475]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111, -380, 475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![32, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![32, 1, 0]] 
 ![![179, 0, 0], ![32, 1, 0], ![50, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![32, 1, 0], ![0, 32, 1], ![350, 84, 32]]]
  hmulB := by decide  
  f := ![![![833, 26, 0], ![-4654, 0, 0]], ![![96, 3, 0], ![-536, 0, 0]], ![![198, 6, 0], ![-1106, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 179, 0], ![-50, 0, 179]], ![![0, 1, 0], ![-6, 32, 1], ![-22, 84, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-134, -32, 1]] ![![179, 0, 0], ![32, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![5728, 179, 0]], ![![-23986, -5728, 179], ![-3938, -1074, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![32, 1, 0]]], ![![![-134, -32, 1]], ![![-22, -6, 0]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [97, 7, 20, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 123, 30], [10, 57, 151], [0, 1]]
 g := ![![[116, 44, 49], [58, 43], [3, 111, 119], [129, 46], [146, 172, 70], [31, 161, 1], []], ![[115, 180, 149, 28], [104, 56], [127, 41, 110, 98], [126, 39], [40, 106, 41, 123], [176, 102, 155, 92], [59, 176]], ![[148, 108, 136, 28], [37, 142], [62, 156, 8, 7], [95, 56], [30, 18, 14, 89], [92, 179, 30, 78], [119, 176]]]
 h' := ![![[151, 123, 30], [139, 82, 174], [71, 159, 119], [102, 87, 32], [137, 45, 74], [70, 94, 147], [0, 0, 1], [0, 1]], ![[10, 57, 151], [127, 64, 70], [21, 62, 150], [83, 18, 90], [84, 141, 138], [142, 118, 158], [64, 113, 57], [151, 123, 30]], ![[0, 1], [153, 35, 118], [159, 141, 93], [54, 76, 59], [161, 176, 150], [17, 150, 57], [141, 68, 123], [10, 57, 151]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [145, 106], []]
 b := ![[], [143, 35, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [97, 7, 20, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3261801, -302270, 76382]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18021, -1670, 422]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-139, -30, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-139, -30, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![52, 161, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-139, -30, 1], ![350, -55, -30], ![-10500, -2170, -55]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-52, -161, 191]], ![![-1, -1, 1], ![10, 25, -30], ![-40, 35, -55]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [54, 163, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 190], [0, 1]]
 g := ![![[49, 46], [95, 150], [184, 97], [69, 52], [46, 46], [19, 20], [1]], ![[0, 145], [93, 41], [35, 94], [188, 139], [188, 145], [6, 171], [1]]]
 h' := ![![[28, 190], [27, 115], [187, 155], [94, 80], [190, 25], [120, 76], [137, 28], [0, 1]], ![[0, 1], [0, 76], [134, 36], [42, 111], [126, 166], [147, 115], [157, 163], [28, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [109, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [54, 163, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1642, -7, 274]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-66, -231, 274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![30, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![30, 1, 0]] 
 ![![191, 0, 0], ![30, 1, 0], ![55, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![30, 1, 0], ![0, 30, 1], ![350, 84, 30]]]
  hmulB := by decide  
  f := ![![![2911, 97, 0], ![-18527, 0, 0]], ![![450, 15, 0], ![-2864, 0, 0]], ![![815, 27, 0], ![-5187, 1, 0]]]
  g := ![![![1, 0, 0], ![-30, 191, 0], ![-55, 0, 191]], ![![0, 1, 0], ![-5, 30, 1], ![-20, 84, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-139, -30, 1]] ![![191, 0, 0], ![30, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![5730, 191, 0]], ![![-26549, -5730, 191], ![-3820, -955, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![30, 1, 0]]], ![![![-139, -30, 1]], ![![-20, -5, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [93, 21, 165, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [118, 164, 61], [103, 28, 132], [0, 1]]
 g := ![![[144, 3, 55], [82, 83], [102, 16], [24, 191], [81, 46], [125, 12], [1]], ![[1, 148, 49, 80], [36, 129], [163, 189], [68, 4], [78, 112], [86, 162], [131, 56, 105, 13]], ![[17, 109, 41, 149], [45, 110], [152, 67], [46, 138], [79, 131], [54, 134], [19, 146, 119, 180]]]
 h' := ![![[118, 164, 61], [46, 32, 172], [97, 16, 135], [133, 5, 4], [186, 101, 159], [112, 165, 25], [100, 172, 28], [0, 1]], ![[103, 28, 132], [61, 184, 13], [163, 135, 124], [70, 20, 31], [188, 11, 191], [109, 58, 150], [192, 27, 82], [118, 164, 61]], ![[0, 1], [13, 170, 8], [96, 42, 127], [23, 168, 158], [172, 81, 36], [125, 163, 18], [124, 187, 83], [103, 28, 132]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 40], []]
 b := ![[], [171, 144, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [93, 21, 165, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27020, 4632, 1158]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140, 24, 6]
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



lemma PB274I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB274I3 : PrimesBelowBoundCertificateInterval O 137 193 274 where
  m := 11
  g := ![1, 2, 2, 2, 1, 1, 2, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB274I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
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
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
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
  β := ![I149N1, I151N1, I157N1, I173N1, I179N1, I191N1]
  Il := ![[], [I149N1], [I151N1], [I157N1], [], [], [I173N1], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
