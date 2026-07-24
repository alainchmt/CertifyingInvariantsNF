
import IdealArithmetic.Examples.NF3_1_387059_1.RI3_1_387059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![55, -40, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![55, -40, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![55, 99, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![55, -40, 1], ![-72, 65, -158], ![-329, 1187, -54]]]
  hmulB := by decide  
  f := ![![![-54, 40, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -99, 139]], ![![0, -1, 1], ![62, 113, -158], ![19, 47, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [96, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 138], [0, 1]]
 g := ![![[98, 42], [44, 79], [7], [85, 78], [64], [129], [1]], ![[0, 97], [45, 60], [7], [42, 61], [64], [129], [1]]]
 h' := ![![[44, 138], [85, 96], [36, 45], [41, 29], [118, 83], [29, 8], [43, 44], [0, 1]], ![[0, 1], [0, 43], [70, 94], [66, 110], [17, 56], [103, 131], [33, 95], [44, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [24]]
 b := ![[], [14, 12]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [96, 95, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-598, -20, -1598]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![628, 1138, -1598]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![19, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![19, 1, 0]] 
 ![![139, 0, 0], ![19, 1, 0], ![54, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![19, 1, 0], ![2, 18, 4], ![8, -30, 21]]]
  hmulB := by decide  
  f := ![![![-5278, -48701, -10824], ![-973, 376134, 0]], ![![-719, -6641, -1476], ![-138, 51291, 0]], ![![-2054, -18920, -4205], ![-352, 146124, 0]]]
  g := ![![![1, 0, 0], ![-19, 139, 0], ![-54, 0, 139]], ![![0, 1, 0], ![-4, 18, 4], ![-4, -30, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![55, -40, 1]] ![![139, 0, 0], ![19, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2641, 139, 0]], ![![7645, -5560, 139], ![973, -695, -139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![19, 1, 0]]], ![![![55, -40, 1]], ![![7, -5, -1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![51, -58, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![51, -58, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![51, 91, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![51, -58, 1], ![-108, 79, -230], ![-473, 1727, -94]]]
  hmulB := by decide  
  f := ![![![-50, 58, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -91, 149]], ![![0, -1, 1], ![78, 141, -230], ![29, 69, -94]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [107, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 148], [0, 1]]
 g := ![![[103, 39], [37], [138, 45], [148], [137, 68], [25], [1]], ![[0, 110], [37], [65, 104], [148], [30, 81], [25], [1]]]
 h' := ![![[5, 148], [140, 121], [134, 22], [78, 94], [92, 105], [132, 98], [42, 5], [0, 1]], ![[0, 1], [0, 28], [95, 127], [101, 55], [21, 44], [26, 51], [67, 144], [5, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [78, 88]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [107, 144, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-211, 164, -419]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![142, 257, -419]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-68, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-68, 1, 0]] 
 ![![149, 0, 0], ![81, 1, 0], ![94, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-68, 1, 0], ![2, -69, 4], ![8, -30, -66]]]
  hmulB := by decide  
  f := ![![![4277, -196767, 11408], ![-3129, -424948, 0]], ![![2353, -106939, 6200], ![-1638, -230950, 0]], ![![2706, -124135, 7197], ![-1957, -268088, 0]]]
  g := ![![![1, 0, 0], ![-81, 149, 0], ![-94, 0, 149]], ![![-1, 1, 0], ![35, -69, 4], ![58, -30, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![51, -58, 1]] ![![149, 0, 0], ![-68, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-10132, 149, 0]], ![![7599, -8642, 149], ![-3576, 4023, -298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-68, 1, 0]]], ![![![51, -58, 1]], ![![-24, 27, -2]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![30, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![30, 1, 0]] 
 ![![151, 0, 0], ![30, 1, 0], ![85, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![30, 1, 0], ![2, 29, 4], ![8, -30, 32]]]
  hmulB := by decide  
  f := ![![![8543, 131237, 18104], ![2567, -683426, 0]], ![![1678, 26067, 3596], ![605, -135749, 0]], ![![4805, 73875, 10191], ![1465, -384710, 0]]]
  g := ![![![1, 0, 0], ![-30, 151, 0], ![-85, 0, 151]], ![![0, 1, 0], ![-8, 29, 4], ![-12, -30, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![43, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![43, 1, 0]] 
 ![![151, 0, 0], ![43, 1, 0], ![2, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![43, 1, 0], ![2, 42, 4], ![8, -30, 45]]]
  hmulB := by decide  
  f := ![![![22752, 538205, 51264], ![10117, -1935216, 0]], ![![6481, 153239, 14596], ![2870, -550999, 0]], ![![278, 7128, 679], ![216, -25632, 0]]]
  g := ![![![1, 0, 0], ![-43, 151, 0], ![-2, 0, 151]], ![![0, 1, 0], ![-12, 42, 4], ![8, -30, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-74, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-74, 1, 0]] 
 ![![151, 0, 0], ![77, 1, 0], ![123, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-74, 1, 0], ![2, -75, 4], ![8, -30, -72]]]
  hmulB := by decide  
  f := ![![![2145, -110914, 5916], ![-1661, -223329, 0]], ![![1139, -56545, 3016], ![-754, -113854, 0]], ![![1735, -90347, 4819], ![-1378, -181917, 0]]]
  g := ![![![1, 0, 0], ![-77, 151, 0], ![-123, 0, 151]], ![![-1, 1, 0], ![35, -75, 4], ![74, -30, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![30, 1, 0]] ![![151, 0, 0], ![43, 1, 0]]
  ![![151, 0, 0], ![21, 18, 1]] where
 M := ![![![22801, 0, 0], ![6493, 151, 0]], ![![4530, 151, 0], ![1292, 72, 4]]]
 hmul := by decide  
 g := ![![![![130, -18, -1], ![151, 0, 0]], ![![22, -17, -1], ![151, 0, 0]]], ![![![9, -17, -1], ![151, 0, 0]], ![![8, 0, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![21, 18, 1]] ![![151, 0, 0], ![-74, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-11174, 151, 0]], ![![3171, 2718, 151], ![-1510, -1359, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-74, 1, 0]]], ![![![21, 18, 1]], ![![-10, -9, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![71, 14, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![71, 14, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![71, 14, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![71, 14, 1], ![36, 27, 58], ![103, -433, 70]]]
  hmulB := by decide  
  f := ![![![-70, -14, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -14, 157]], ![![0, 0, 1], ![-26, -5, 58], ![-31, -9, 70]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [38, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 156], [0, 1]]
 g := ![![[99, 154], [10], [124, 19], [10, 132], [144, 138], [36], [1]], ![[81, 3], [10], [81, 138], [17, 25], [30, 19], [36], [1]]]
 h' := ![![[6, 156], [95, 132], [155, 139], [91, 126], [23, 140], [76, 74], [119, 6], [0, 1]], ![[0, 1], [102, 25], [47, 18], [62, 31], [78, 17], [49, 83], [155, 151], [6, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65]]
 b := ![[], [138, 111]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [38, 151, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45810, -52648, -127970]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![57580, 11076, -127970]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-58, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-58, 1, 0]] 
 ![![157, 0, 0], ![99, 1, 0], ![87, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-58, 1, 0], ![2, -59, 4], ![8, -30, -56]]]
  hmulB := by decide  
  f := ![![![-1927, 70556, -4784], ![1256, 187772, 0]], ![![-1217, 44481, -3016], ![786, 118378, 0]], ![![-1073, 39098, -2651], ![682, 104052, 0]]]
  g := ![![![1, 0, 0], ![-99, 157, 0], ![-87, 0, 157]], ![![-1, 1, 0], ![35, -59, 4], ![50, -30, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![71, 14, 1]] ![![157, 0, 0], ![-58, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-9106, 157, 0]], ![![11147, 2198, 157], ![-4082, -785, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-58, 1, 0]]], ![![![71, 14, 1]], ![![-26, -5, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-47, -40, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-47, -40, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![116, 123, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-47, -40, 1], ![-72, -37, -158], ![-329, 1187, -156]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-116, -123, 163]], ![![-1, -1, 1], ![112, 119, -158], ![109, 125, -156]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [92, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [85, 162], [0, 1]]
 g := ![![[54, 131], [76, 1], [60], [33], [60], [112, 53], [1]], ![[105, 32], [161, 162], [60], [33], [60], [53, 110], [1]]]
 h' := ![![[85, 162], [17, 72], [77, 1], [50, 68], [106, 14], [128, 68], [71, 85], [0, 1]], ![[0, 1], [106, 91], [162, 162], [125, 95], [155, 149], [40, 95], [124, 78], [85, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [67, 148]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [92, 78, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1347, 768, -3051]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2163, 2307, -3051]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-5, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-5, 1, 0]] 
 ![![163, 0, 0], ![158, 1, 0], ![156, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-5, 1, 0], ![2, -6, 4], ![8, -30, -3]]]
  hmulB := by decide  
  f := ![![![-774, 2339, -1560], ![163, 63570, 0]], ![![-750, 2267, -1512], ![164, 61614, 0]], ![![-743, 2239, -1493], ![83, 60840, 0]]]
  g := ![![![1, 0, 0], ![-158, 163, 0], ![-156, 0, 163]], ![![-1, 1, 0], ![2, -6, 4], ![32, -30, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-47, -40, 1]] ![![163, 0, 0], ![-5, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-815, 163, 0]], ![![-7661, -6520, 163], ![163, 163, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-5, 1, 0]]], ![![![-47, -40, 1]], ![![1, 1, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![81, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![81, 1, 0]] 
 ![![167, 0, 0], ![81, 1, 0], ![134, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![81, 1, 0], ![2, 80, 4], ![8, -30, 83]]]
  hmulB := by decide  
  f := ![![![550, 31677, 1584], ![501, -66132, 0]], ![![222, 15358, 768], ![335, -32064, 0]], ![![403, 25417, 1271], ![481, -53064, 0]]]
  g := ![![![1, 0, 0], ![-81, 167, 0], ![-134, 0, 167]], ![![0, 1, 0], ![-42, 80, 4], ![-52, -30, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-51, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-51, 1, 0]] 
 ![![167, 0, 0], ![116, 1, 0], ![89, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-51, 1, 0], ![2, -52, 4], ![8, -30, -49]]]
  hmulB := by decide  
  f := ![![![-4139, 123540, -9504], ![2004, 396792, 0]], ![![-2840, 85791, -6600], ![1504, 275550, 0]], ![![-2171, 65838, -5065], ![1182, 211464, 0]]]
  g := ![![![1, 0, 0], ![-116, 167, 0], ![-89, 0, 167]], ![![-1, 1, 0], ![34, -52, 4], ![47, -30, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-31, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-31, 1, 0]] 
 ![![167, 0, 0], ![136, 1, 0], ![3, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-31, 1, 0], ![2, -32, 4], ![8, -30, -29]]]
  hmulB := by decide  
  f := ![![![13319, -223978, 28000], ![-3674, -1169000, 0]], ![![10843, -182382, 22800], ![-3005, -951900, 0]], ![![253, -4024, 503], ![8, -21000, 0]]]
  g := ![![![1, 0, 0], ![-136, 167, 0], ![-3, 0, 167]], ![![-1, 1, 0], ![26, -32, 4], ![25, -30, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![81, 1, 0]] ![![167, 0, 0], ![-51, 1, 0]]
  ![![167, 0, 0], ![95, 49, 1]] where
 M := ![![![27889, 0, 0], ![-8517, 167, 0]], ![![13527, 167, 0], ![-4129, 29, 4]]]
 hmul := by decide  
 g := ![![![![72, -49, -1], ![167, 0, 0]], ![![-51, 1, 0], ![0, 0, 0]]], ![![![-14, -48, -1], ![167, 0, 0]], ![![-27, -1, 0], ![4, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![95, 49, 1]] ![![167, 0, 0], ![-31, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-5177, 167, 0]], ![![15865, 8183, 167], ![-2839, -1503, 167]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-31, 1, 0]]], ![![![95, 49, 1]], ![![-17, -9, 1]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![7, 53, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![7, 53, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![7, 53, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![7, 53, 1], ![114, -76, 214], ![415, -1603, 84]]]
  hmulB := by decide  
  f := ![![![-6, -53, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-7, -53, 173]], ![![0, 0, 1], ![-8, -66, 214], ![-1, -35, 84]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [142, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 172], [0, 1]]
 g := ![![[82, 106], [159], [137, 24], [121, 51], [148], [77, 41], [1]], ![[0, 67], [159], [76, 149], [13, 122], [148], [153, 132], [1]]]
 h' := ![![[120, 172], [114, 25], [95, 141], [118, 102], [104, 140], [138, 54], [31, 120], [0, 1]], ![[0, 1], [0, 148], [61, 32], [75, 71], [123, 33], [44, 119], [72, 53], [120, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87]]
 b := ![[], [158, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [142, 53, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-426, -62, -1346]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![52, 412, -1346]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-41, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-41, 1, 0]] 
 ![![173, 0, 0], ![132, 1, 0], ![89, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-41, 1, 0], ![2, -42, 4], ![8, -30, -39]]]
  hmulB := by decide  
  f := ![![![13932, -317491, 30240], ![-5017, -1307880, 0]], ![![10635, -242234, 23072], ![-3805, -997864, 0]], ![![7187, -163334, 15557], ![-2498, -672840, 0]]]
  g := ![![![1, 0, 0], ![-132, 173, 0], ![-89, 0, 173]], ![![-1, 1, 0], ![30, -42, 4], ![43, -30, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![7, 53, 1]] ![![173, 0, 0], ![-41, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-7093, 173, 0]], ![![1211, 9169, 173], ![-173, -2249, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-41, 1, 0]]], ![![![7, 53, 1]], ![![-1, -13, 1]]]]
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


lemma PB177I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 176 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 176 (by omega)

def PB177I3 : PrimesBelowBoundCertificateInterval O 137 176 177 where
  m := 7
  g := ![2, 2, 3, 2, 2, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173]
  hP := PB177I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
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
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I167N0, I167N1, I167N2, I173N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [I167N0, I167N1, I167N2], [I173N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
