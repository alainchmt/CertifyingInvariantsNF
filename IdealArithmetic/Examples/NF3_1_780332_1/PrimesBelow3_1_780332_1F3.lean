
import IdealArithmetic.Examples.NF3_1_780332_1.RI3_1_780332_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-151, 23, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-151, 23, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![127, 23, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-151, 23, 1], ![558, -27, 23], ![12834, 3410, -27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-127, -23, 139]], ![![-2, 0, 1], ![-17, -4, 23], ![117, 29, -27]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [130, 113, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 138], [0, 1]]
 g := ![![[111, 51], [113, 79], [44], [37, 117], [120], [120], [1]], ![[47, 88], [82, 60], [44], [21, 22], [120], [120], [1]]]
 h' := ![![[26, 138], [44, 32], [85, 45], [55, 105], [6, 16], [49, 113], [9, 26], [0, 1]], ![[0, 1], [42, 107], [4, 94], [5, 34], [5, 123], [68, 26], [129, 113], [26, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [116, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [130, 113, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1246, 693, 12]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2, 3, 12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-23, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-23, 1, 0]] 
 ![![139, 0, 0], ![116, 1, 0], ![27, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-23, 1, 0], ![0, -23, 1], ![558, 124, -23]]]
  hmulB := by decide  
  f := ![![![3106, -135, 0], ![18765, 0, 0]], ![![2600, -113, 0], ![15708, 0, 0]], ![![648, -28, 0], ![3915, 1, 0]]]
  g := ![![![1, 0, 0], ![-116, 139, 0], ![-27, 0, 139]], ![![-1, 1, 0], ![19, -23, 1], ![-95, 124, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-151, 23, 1]] ![![139, 0, 0], ![-23, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-3197, 139, 0]], ![![-20989, 3197, 139], ![4031, -556, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-23, 1, 0]]], ![![![-151, 23, 1]], ![![29, -4, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [56, 129, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 74, 111], [133, 74, 38], [0, 1]]
 g := ![![[53, 127, 127], [82, 49], [84, 112, 26], [39, 148], [56, 73, 104], [145, 1], []], ![[61, 107, 19, 50], [18, 88], [109, 93, 33, 3], [112, 113], [92, 112, 66, 72], [147, 112], [73, 103]], ![[55, 108, 101, 105], [132, 103], [51, 27, 15, 99], [97, 124], [136, 130, 13, 72], [0, 112], [146, 103]]]
 h' := ![![[12, 74, 111], [100, 58, 53], [64, 44, 142], [100, 143, 131], [142, 124, 44], [75, 13, 36], [0, 0, 1], [0, 1]], ![[133, 74, 38], [66, 24, 79], [39, 120, 45], [96, 134, 88], [40, 131, 34], [95, 104, 84], [79, 1, 74], [12, 74, 111]], ![[0, 1], [39, 67, 17], [117, 134, 111], [14, 21, 79], [126, 43, 71], [82, 32, 29], [126, 148, 74], [133, 74, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [143, 11], []]
 b := ![[], [115, 71, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [56, 129, 4, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4659230, 2928446, 390976]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![31270, 19654, 2624]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [111, 105, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [115, 108, 116], [49, 42, 35], [0, 1]]
 g := ![![[135, 41, 47], [13, 117, 90], [47, 83, 128], [86, 94], [27, 69, 19], [13, 1], []], ![[150, 45, 127, 123], [94, 75, 79, 127], [97, 39, 83, 95], [4, 16], [52, 149, 37, 94], [119, 103], [60, 17]], ![[3, 83, 138, 53], [108, 91, 100, 134], [136, 30, 28, 33], [92, 50], [13, 16, 32, 114], [102, 37], [141, 17]]]
 h' := ![![[115, 108, 116], [67, 87, 54], [68, 83, 111], [43, 115, 66], [23, 35, 83], [67, 34, 64], [0, 0, 1], [0, 1]], ![[49, 42, 35], [68, 91, 129], [89, 147, 96], [51, 7, 106], [58, 101, 147], [129, 82, 139], [72, 43, 42], [115, 108, 116]], ![[0, 1], [40, 124, 119], [48, 72, 95], [32, 29, 130], [60, 15, 72], [88, 35, 99], [38, 108, 108], [49, 42, 35]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 31], []]
 b := ![[], [14, 60, 126], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [111, 105, 138, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![253529, -115817, -15553]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1679, -767, -103]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![22, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![22, 1, 0]] 
 ![![157, 0, 0], ![22, 1, 0], ![144, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![22, 1, 0], ![0, 22, 1], ![558, 124, 22]]]
  hmulB := by decide  
  f := ![![![969, 44, 0], ![-6908, 0, 0]], ![![110, 5, 0], ![-784, 0, 0]], ![![884, 40, 0], ![-6302, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 157, 0], ![-144, 0, 157]], ![![0, 1, 0], ![-4, 22, 1], ![-34, 124, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![35, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![35, 1, 0]] 
 ![![157, 0, 0], ![35, 1, 0], ![31, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![35, 1, 0], ![0, 35, 1], ![558, 124, 35]]]
  hmulB := by decide  
  f := ![![![246, 7, 0], ![-1099, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![8, 0, 0], ![-35, 1, 0]]]
  g := ![![![1, 0, 0], ![-35, 157, 0], ![-31, 0, 157]], ![![0, 1, 0], ![-8, 35, 1], ![-31, 124, 35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-57, 1, 0]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-57, 1, 0]] 
 ![![157, 0, 0], ![100, 1, 0], ![48, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-57, 1, 0], ![0, -57, 1], ![558, 124, -57]]]
  hmulB := by decide  
  f := ![![![8779, -154, 0], ![24178, 0, 0]], ![![5644, -99, 0], ![15544, 0, 0]], ![![2700, -47, 0], ![7436, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 157, 0], ![-48, 0, 157]], ![![-1, 1, 0], ![36, -57, 1], ![-58, 124, -57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![22, 1, 0]] ![![157, 0, 0], ![35, 1, 0]]
  ![![157, 0, 0], ![-15, 57, 1]] where
 M := ![![![24649, 0, 0], ![5495, 157, 0]], ![![3454, 157, 0], ![770, 57, 1]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![35, 1, 0], ![0, 0, 0]]], ![![![22, 1, 0], ![0, 0, 0]], ![![5, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-15, 57, 1]] ![![157, 0, 0], ![-57, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8949, 157, 0]], ![![-2355, 8949, 157], ![1413, -3140, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-57, 1, 0]]], ![![![-15, 57, 1]], ![![9, -20, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-153, -42, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-153, -42, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![10, 121, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-153, -42, 1], ![558, -29, -42], ![-23436, -4650, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -121, 163]], ![![-1, -1, 1], ![6, 31, -42], ![-142, -7, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [3, 135, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 162], [0, 1]]
 g := ![![[45, 71], [114, 118], [77], [15], [91], [105, 132], [1]], ![[77, 92], [158, 45], [77], [15], [91], [52, 31], [1]]]
 h' := ![![[28, 162], [147, 76], [3, 66], [76, 27], [11, 34], [11, 108], [160, 28], [0, 1]], ![[0, 1], [156, 87], [58, 97], [17, 136], [148, 129], [101, 55], [129, 135], [28, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [60, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [3, 135, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3209, 4415, 706]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-63, -497, 706]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![42, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![42, 1, 0]] 
 ![![163, 0, 0], ![42, 1, 0], ![29, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![42, 1, 0], ![0, 42, 1], ![558, 124, 42]]]
  hmulB := by decide  
  f := ![![![2185, 52, 0], ![-8476, 0, 0]], ![![546, 13, 0], ![-2118, 0, 0]], ![![347, 8, 0], ![-1346, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 163, 0], ![-29, 0, 163]], ![![0, 1, 0], ![-11, 42, 1], ![-36, 124, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-153, -42, 1]] ![![163, 0, 0], ![42, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![6846, 163, 0]], ![![-24939, -6846, 163], ![-5868, -1793, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![42, 1, 0]]], ![![![-153, -42, 1]], ![![-36, -11, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-8, -28, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-8, -28, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![159, 139, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-8, -28, 1], ![558, 116, -28], ![-15624, -2914, 116]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-159, -139, 167]], ![![-1, -1, 1], ![30, 24, -28], ![-204, -114, 116]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [166, 160, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [7, 166], [0, 1]]
 g := ![![[7, 81], [6, 50], [90, 77], [21], [99], [23, 49], [1]], ![[73, 86], [22, 117], [128, 90], [21], [99], [32, 118], [1]]]
 h' := ![![[7, 166], [6, 9], [90, 102], [118, 54], [127, 45], [23, 44], [1, 7], [0, 1]], ![[0, 1], [69, 158], [136, 65], [162, 113], [108, 122], [164, 123], [50, 160], [7, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85]]
 b := ![[], [60, 126]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [166, 160, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1282, 646, -35]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![41, 33, -35]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![28, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![28, 1, 0]] 
 ![![167, 0, 0], ![28, 1, 0], ![51, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![28, 1, 0], ![0, 28, 1], ![558, 124, 28]]]
  hmulB := by decide  
  f := ![![![113, 4, 0], ![-668, 0, 0]], ![![-28, -1, 0], ![168, 0, 0]], ![![5, 0, 0], ![-28, 1, 0]]]
  g := ![![![1, 0, 0], ![-28, 167, 0], ![-51, 0, 167]], ![![0, 1, 0], ![-5, 28, 1], ![-26, 124, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-8, -28, 1]] ![![167, 0, 0], ![28, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![4676, 167, 0]], ![![-1336, -4676, 167], ![334, -668, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![28, 1, 0]]], ![![![-8, -28, 1]], ![![2, -4, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-60, 8, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-60, 8, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![113, 8, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-60, 8, 1], ![558, 64, 8], ![4464, 1550, 64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -8, 173]], ![![-1, 0, 1], ![-2, 0, 8], ![-16, 6, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [89, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [34, 172], [0, 1]]
 g := ![![[21, 35], [13], [19, 92], [105, 96], [37], [36, 118], [1]], ![[0, 138], [13], [33, 81], [82, 77], [37], [69, 55], [1]]]
 h' := ![![[34, 172], [18, 30], [39, 79], [170, 28], [136, 31], [83, 27], [84, 34], [0, 1]], ![[0, 1], [0, 143], [130, 94], [84, 145], [152, 142], [136, 146], [29, 139], [34, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [74, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [89, 139, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21433, 7949, 626]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-285, 17, 626]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-8, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-8, 1, 0]] 
 ![![173, 0, 0], ![165, 1, 0], ![109, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-8, 1, 0], ![0, -8, 1], ![558, 124, -8]]]
  hmulB := by decide  
  f := ![![![553, -69, 0], ![11937, 0, 0]], ![![529, -66, 0], ![11419, 0, 0]], ![![361, -45, 0], ![7793, 1, 0]]]
  g := ![![![1, 0, 0], ![-165, 173, 0], ![-109, 0, 173]], ![![-1, 1, 0], ![7, -8, 1], ![-110, 124, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-60, 8, 1]] ![![173, 0, 0], ![-8, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-1384, 173, 0]], ![![-10380, 1384, 173], ![1038, 0, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-8, 1, 0]]], ![![![-60, 8, 1]], ![![6, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [9, 91, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 48, 59], [95, 130, 120], [0, 1]]
 g := ![![[118, 57, 36], [71, 154, 74], [34, 5], [170, 124], [120, 95, 25], [81, 107, 1], []], ![[100, 170, 167, 139], [43, 125, 146, 177], [103, 107], [103, 144], [4, 14, 18, 87], [19, 64, 165, 70], [83, 80]], ![[75, 76, 81, 55], [82, 171, 163, 159], [109, 135], [139, 70], [26, 4, 158, 159], [61, 17, 93, 104], [22, 80]]]
 h' := ![![[12, 48, 59], [77, 3, 173], [137, 50, 130], [117, 71, 149], [173, 29, 126], [166, 79, 174], [0, 0, 1], [0, 1]], ![[95, 130, 120], [151, 89, 113], [33, 131, 160], [85, 90, 110], [81, 41, 12], [12, 17, 73], [113, 39, 130], [12, 48, 59]], ![[0, 1], [26, 87, 72], [174, 177, 68], [170, 18, 99], [139, 109, 41], [52, 83, 111], [56, 140, 48], [95, 130, 120]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [58, 136], []]
 b := ![[], [61, 159, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [9, 91, 72, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![95407, -24702, -4475]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![533, -138, -25]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-88, 6, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-88, 6, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![93, 6, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-88, 6, 1], ![558, 36, 6], ![3348, 1302, 36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-93, -6, 181]], ![![-1, 0, 1], ![0, 0, 6], ![0, 6, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [88, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 180], [0, 1]]
 g := ![![[131, 156], [82], [91, 161], [132], [22, 49], [145, 59], [1]], ![[179, 25], [82], [57, 20], [132], [51, 132], [10, 122], [1]]]
 h' := ![![[56, 180], [150, 95], [137, 156], [97, 121], [55, 133], [91, 174], [93, 56], [0, 1]], ![[0, 1], [40, 86], [4, 25], [176, 60], [82, 48], [61, 7], [152, 125], [56, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [90, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [88, 125, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2320, 2853, 747]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-371, -9, 747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-6, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-6, 1, 0]] 
 ![![181, 0, 0], ![175, 1, 0], ![145, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-6, 1, 0], ![0, -6, 1], ![558, 124, -6]]]
  hmulB := by decide  
  f := ![![![919, -153, 0], ![27693, 0, 0]], ![![889, -148, 0], ![26789, 0, 0]], ![![739, -123, 0], ![22269, 1, 0]]]
  g := ![![![1, 0, 0], ![-175, 181, 0], ![-145, 0, 181]], ![![-1, 1, 0], ![5, -6, 1], ![-112, 124, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-88, 6, 1]] ![![181, 0, 0], ![-6, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![-1086, 181, 0]], ![![-15928, 1086, 181], ![1086, 0, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![-6, 1, 0]]], ![![![-88, 6, 1]], ![![6, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-38, -75, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-38, -75, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![153, 116, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-38, -75, 1], ![558, 86, -75], ![-41850, -8742, 86]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -116, 191]], ![![-1, -1, 1], ![63, 46, -75], ![-288, -98, 86]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [64, 40, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [151, 190], [0, 1]]
 g := ![![[120, 3], [176, 78], [4, 13], [67, 2], [162, 72], [139, 72], [1]], ![[0, 188], [112, 113], [57, 178], [178, 189], [147, 119], [124, 119], [1]]]
 h' := ![![[151, 190], [5, 24], [126, 101], [105, 108], [137, 57], [81, 40], [127, 151], [0, 1]], ![[0, 1], [0, 167], [97, 90], [178, 83], [149, 134], [9, 151], [8, 40], [151, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [158, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [64, 40, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22172, -3168, 684]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-664, -432, 684]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![75, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![75, 1, 0]] 
 ![![191, 0, 0], ![75, 1, 0], ![105, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![75, 1, 0], ![0, 75, 1], ![558, 124, 75]]]
  hmulB := by decide  
  f := ![![![5026, 67, 0], ![-12797, 0, 0]], ![![1950, 26, 0], ![-4965, 0, 0]], ![![2730, 36, 0], ![-6951, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 191, 0], ![-105, 0, 191]], ![![0, 1, 0], ![-30, 75, 1], ![-87, 124, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-38, -75, 1]] ![![191, 0, 0], ![75, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![14325, 191, 0]], ![![-7258, -14325, 191], ![-2292, -5539, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![75, 1, 0]]], ![![![-38, -75, 1]], ![![-12, -29, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-97, 42, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-97, 42, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![96, 42, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-97, 42, 1], ![558, 27, 42], ![23436, 5766, 27]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -42, 193]], ![![-1, 0, 1], ![-18, -9, 42], ![108, 24, 27]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [141, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 192], [0, 1]]
 g := ![![[180, 85], [55], [139], [48], [143], [16], [96, 1]], ![[41, 108], [55], [139], [48], [143], [16], [192, 192]]]
 h' := ![![[96, 192], [109, 144], [12, 172], [73, 116], [47, 137], [157, 170], [167, 4], [0, 1]], ![[0, 1], [37, 49], [119, 21], [15, 77], [75, 56], [72, 23], [165, 189], [96, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [155, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [141, 97, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![455, 187, 248]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -53, 248]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-42, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-42, 1, 0]] 
 ![![193, 0, 0], ![151, 1, 0], ![166, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-42, 1, 0], ![0, -42, 1], ![558, 124, -42]]]
  hmulB := by decide  
  f := ![![![1387, -33, 0], ![6369, 0, 0]], ![![1093, -26, 0], ![5019, 0, 0]], ![![1186, -28, 0], ![5446, 1, 0]]]
  g := ![![![1, 0, 0], ![-151, 193, 0], ![-166, 0, 193]], ![![-1, 1, 0], ![32, -42, 1], ![-58, 124, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-97, 42, 1]] ![![193, 0, 0], ![-42, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-8106, 193, 0]], ![![-18721, 8106, 193], ![4632, -1737, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-42, 1, 0]]], ![![![-97, 42, 1]], ![![24, -9, 0]]]]
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


lemma PB250I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB250I3 : PrimesBelowBoundCertificateInterval O 137 193 250 where
  m := 11
  g := ![2, 1, 1, 3, 2, 2, 2, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB250I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
    · dsimp ; intro j
      fin_cases j
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I157N0, I157N1, I157N2, I163N1, I167N1, I173N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [], [], [I157N0, I157N1, I157N2], [I163N1], [I167N1], [I173N1], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
