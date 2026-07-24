
import IdealArithmetic.Examples.NF3_1_614075_2.RI3_1_614075_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-10, 38, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-10, 38, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![129, 38, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-10, 38, 1], ![-112, -47, 39], ![-4368, -1555, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-129, -38, 139]], ![![-1, 0, 1], ![-37, -11, 39], ![-24, -9, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [53, 36, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 138], [0, 1]]
 g := ![![[61, 1], [24, 71], [127], [15, 46], [89], [45], [1]], ![[25, 138], [109, 68], [127], [27, 93], [89], [45], [1]]]
 h' := ![![[103, 138], [118, 1], [72, 99], [39, 108], [58, 18], [7, 111], [86, 103], [0, 1]], ![[0, 1], [82, 138], [122, 40], [43, 31], [105, 121], [42, 28], [131, 36], [103, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [41, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [53, 36, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-283, -259, -69]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![62, 17, -69]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-39, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-39, 1, 0]] 
 ![![139, 0, 0], ![100, 1, 0], ![8, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-39, 1, 0], ![0, -39, 1], ![-112, -37, -38]]]
  hmulB := by decide  
  f := ![![![3901, -100, 0], ![13900, 0, 0]], ![![2848, -73, 0], ![10148, 0, 0]], ![![284, -7, 0], ![1012, 1, 0]]]
  g := ![![![1, 0, 0], ![-100, 139, 0], ![-8, 0, 139]], ![![-1, 1, 0], ![28, -39, 1], ![28, -37, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-10, 38, 1]] ![![139, 0, 0], ![-39, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-5421, 139, 0]], ![![-1390, 5282, 139], ![278, -1529, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-39, 1, 0]]], ![![![-10, 38, 1]], ![![2, -11, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![74, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![74, 1, 0]] 
 ![![149, 0, 0], ![74, 1, 0], ![37, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![74, 1, 0], ![0, 74, 1], ![-112, -37, 75]]]
  hmulB := by decide  
  f := ![![![2295, 31, 0], ![-4619, 0, 0]], ![![1110, 15, 0], ![-2234, 0, 0]], ![![555, 7, 0], ![-1117, 1, 0]]]
  g := ![![![1, 0, 0], ![-74, 149, 0], ![-37, 0, 149]], ![![0, 1, 0], ![-37, 74, 1], ![-1, -37, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-74, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-74, 1, 0]] 
 ![![149, 0, 0], ![75, 1, 0], ![37, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-74, 1, 0], ![0, -74, 1], ![-112, -37, -73]]]
  hmulB := by decide  
  f := ![![![11027, -149, 0], ![22201, 0, 0]], ![![5625, -76, 0], ![11325, 0, 0]], ![![2775, -37, 0], ![5587, 1, 0]]]
  g := ![![![1, 0, 0], ![-75, 149, 0], ![-37, 0, 149]], ![![-1, 1, 0], ![37, -74, 1], ![36, -37, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![149, 0, 0], ![148, 1, 0], ![148, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![-112, -37, 0]]]
  hmulB := by decide  
  f := ![![![-37, 0, -1]], ![![-36, 0, -1]], ![![-36, 1, -1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![36, -37, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![74, 1, 0]] ![![149, 0, 0], ![-74, 1, 0]]
  ![![37, 0, 1]] where
 M := ![![![22201, 0, 0], ![-11026, 149, 0]], ![![11026, 149, 0], ![-5476, 0, 1]]]
 hmul := by decide  
 g := ![![![![149, -149, 0]], ![![-74, 75, -1]]], ![![![74, -73, -1]], ![![-36, 37, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![37, 0, 1]] ![![-1, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![16, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![16, 1, 0]] 
 ![![151, 0, 0], ![16, 1, 0], ![46, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![16, 1, 0], ![0, 16, 1], ![-112, -37, 17]]]
  hmulB := by decide  
  f := ![![![1169, 73, 0], ![-11023, 0, 0]], ![![112, 7, 0], ![-1056, 0, 0]], ![![354, 22, 0], ![-3338, 1, 0]]]
  g := ![![![1, 0, 0], ![-16, 151, 0], ![-46, 0, 151]], ![![0, 1, 0], ![-2, 16, 1], ![-2, -37, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![25, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![25, 1, 0]] 
 ![![151, 0, 0], ![25, 1, 0], ![130, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![25, 1, 0], ![0, 25, 1], ![-112, -37, 26]]]
  hmulB := by decide  
  f := ![![![2476, 99, 0], ![-14949, 0, 0]], ![![400, 16, 0], ![-2415, 0, 0]], ![![2130, 85, 0], ![-12860, 1, 0]]]
  g := ![![![1, 0, 0], ![-25, 151, 0], ![-130, 0, 151]], ![![0, 1, 0], ![-5, 25, 1], ![-17, -37, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-42, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-42, 1, 0]] 
 ![![151, 0, 0], ![109, 1, 0], ![48, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-42, 1, 0], ![0, -42, 1], ![-112, -37, -41]]]
  hmulB := by decide  
  f := ![![![1177, -28, 0], ![4228, 0, 0]], ![![799, -19, 0], ![2870, 0, 0]], ![![432, -10, 0], ![1552, 1, 0]]]
  g := ![![![1, 0, 0], ![-109, 151, 0], ![-48, 0, 151]], ![![-1, 1, 0], ![30, -42, 1], ![39, -37, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![16, 1, 0]] ![![151, 0, 0], ![25, 1, 0]]
  ![![151, 0, 0], ![98, 41, 1]] where
 M := ![![![22801, 0, 0], ![3775, 151, 0]], ![![2416, 151, 0], ![400, 41, 1]]]
 hmul := by decide  
 g := ![![![![53, -41, -1], ![151, 0, 0]], ![![-73, -40, -1], ![151, 0, 0]]], ![![![-82, -40, -1], ![151, 0, 0]], ![![-96, -41, -1], ![152, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![98, 41, 1]] ![![151, 0, 0], ![-42, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-6342, 151, 0]], ![![14798, 6191, 151], ![-4228, -1661, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-42, 1, 0]]], ![![![98, 41, 1]], ![![-28, -11, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [144, 132, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 84, 86], [33, 72, 71], [0, 1]]
 g := ![![[101, 120, 33], [86, 40], [75, 22, 154], [59, 80, 37], [69, 97, 108], [90, 1], []], ![[112, 88, 72, 33], [50, 52], [146, 65, 32, 47], [67, 79, 30, 10], [18, 25, 27, 76], [4, 3], [121, 17]], ![[12, 84, 71, 48], [55, 64], [102, 38, 28, 57], [5, 73, 41, 9], [31, 124, 123, 64], [76, 148], [136, 17]]]
 h' := ![![[57, 84, 86], [9, 103, 70], [33, 130, 36], [139, 144, 25], [112, 20, 115], [71, 65, 118], [0, 0, 1], [0, 1]], ![[33, 72, 71], [61, 145, 82], [14, 99, 113], [0, 120, 54], [2, 96, 109], [36, 109, 113], [112, 105, 72], [57, 84, 86]], ![[0, 1], [83, 66, 5], [101, 85, 8], [14, 50, 78], [98, 41, 90], [65, 140, 83], [31, 52, 84], [33, 72, 71]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 78], []]
 b := ![[], [150, 95, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [144, 132, 67, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![360158, 165321, 15386]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2294, 1053, 98]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![271, 88, -9]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![271, 88, -9]] 
 ![![163, 0, 0], ![0, 163, 0], ![151, 117, 1]] where
  M :=![![![271, 88, -9], ![1008, 604, 79], ![-8848, -1915, 683]]]
  hmulB := by decide  
  f := ![![![-3459, 263, -76]], ![![8512, -647, 187]], ![![2777, -211, 61]]]
  g := ![![![10, 7, -9], ![-67, -53, 79], ![-687, -502, 683]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [83, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [60, 162], [0, 1]]
 g := ![![[123, 55], [119, 4], [21], [22], [6], [8, 14], [1]], ![[0, 108], [33, 159], [21], [22], [6], [33, 149], [1]]]
 h' := ![![[60, 162], [66, 113], [71, 161], [99, 99], [135, 48], [151, 13], [80, 60], [0, 1]], ![[0, 1], [0, 50], [114, 2], [8, 64], [81, 115], [116, 150], [94, 103], [60, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [89, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [83, 103, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2301, -100, -12]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 8, -12]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3459, 263, -76]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![-3459, 263, -76]] 
 ![![163, 0, 0], ![45, 1, 0], ![94, 0, 1]] where
  M :=![![![-3459, 263, -76], ![8512, -647, 187], ![-20944, 1593, -460]]]
  hmulB := by decide  
  f := ![![![271, 88, -9]], ![![81, 28, -2]], ![![102, 39, -1]]]
  g := ![![![-50, 263, -76], ![123, -647, 187], ![-303, 1593, -460]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![271, 88, -9]] ![![-3459, 263, -76]]
  ![![163, 0, 0]] where
 M := ![![![163, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![1, 54, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![1, 54, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![1, 54, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![1, 54, 1], ![-112, -36, 55], ![-6160, -2147, 19]]]
  hmulB := by decide  
  f := ![![![0, -18, 0], ![55, -1, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-1, -54, 167]], ![![0, 0, 1], ![-1, -18, 55], ![-37, -19, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [61, 110, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 166], [0, 1]]
 g := ![![[125, 115], [150, 33], [79, 115], [3], [85], [50, 76], [1]], ![[0, 52], [27, 134], [121, 52], [3], [85], [40, 91], [1]]]
 h' := ![![[57, 166], [35, 99], [24, 37], [82, 99], [91, 62], [123, 98], [106, 57], [0, 1]], ![[0, 1], [0, 68], [129, 130], [47, 68], [118, 105], [31, 69], [15, 110], [57, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4]]
 b := ![[], [110, 2]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [61, 110, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164, -1007, -665]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 209, -665]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-55, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-55, 1, 0]] 
 ![![167, 0, 0], ![112, 1, 0], ![148, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-55, 1, 0], ![0, -55, 1], ![-112, -37, -54]]]
  hmulB := by decide  
  f := ![![![5941, -108, 0], ![18036, 0, 0]], ![![4016, -73, 0], ![12192, 0, 0]], ![![5244, -95, 0], ![15920, 1, 0]]]
  g := ![![![1, 0, 0], ![-112, 167, 0], ![-148, 0, 167]], ![![-1, 1, 0], ![36, -55, 1], ![72, -37, -54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![1, 54, 1]] ![![167, 0, 0], ![-55, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-9185, 167, 0]], ![![167, 9018, 167], ![-167, -3006, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-55, 1, 0]]], ![![![1, 54, 1]], ![![-1, -18, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![45, -65, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![45, -65, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![45, 108, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![45, -65, 1], ![-112, 8, -64], ![7168, 2256, -56]]]
  hmulB := by decide  
  f := ![![![-44, 65, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -108, 173]], ![![0, -1, 1], ![16, 40, -64], ![56, 48, -56]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [151, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 172], [0, 1]]
 g := ![![[45, 55], [169], [171, 64], [108, 119], [40], [92, 55], [1]], ![[0, 118], [169], [40, 109], [105, 54], [40], [47, 118], [1]]]
 h' := ![![[125, 172], [118, 125], [129, 160], [127, 8], [124, 43], [121, 46], [22, 125], [0, 1]], ![[0, 1], [0, 48], [61, 13], [89, 165], [136, 130], [162, 127], [77, 48], [125, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [127]]
 b := ![[], [140, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [151, 48, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-185, -271, -81]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![20, 49, -81]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![64, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![64, 1, 0]] 
 ![![173, 0, 0], ![64, 1, 0], ![56, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![64, 1, 0], ![0, 64, 1], ![-112, -37, 65]]]
  hmulB := by decide  
  f := ![![![3265, 51, 0], ![-8823, 0, 0]], ![![1216, 19, 0], ![-3286, 0, 0]], ![![1048, 16, 0], ![-2832, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 173, 0], ![-56, 0, 173]], ![![0, 1, 0], ![-24, 64, 1], ![-8, -37, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![45, -65, 1]] ![![173, 0, 0], ![64, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![11072, 173, 0]], ![![7785, -11245, 173], ![2768, -4152, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![64, 1, 0]]], ![![![45, -65, 1]], ![![16, -24, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![48, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![48, 1, 0]] 
 ![![179, 0, 0], ![48, 1, 0], ![23, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![48, 1, 0], ![0, 48, 1], ![-112, -37, 49]]]
  hmulB := by decide  
  f := ![![![4033, 84, 0], ![-15036, 0, 0]], ![![1008, 21, 0], ![-3758, 0, 0]], ![![493, 10, 0], ![-1838, 1, 0]]]
  g := ![![![1, 0, 0], ![-48, 179, 0], ![-23, 0, 179]], ![![0, 1, 0], ![-13, 48, 1], ![3, -37, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![50, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![50, 1, 0]] 
 ![![179, 0, 0], ![50, 1, 0], ![6, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![50, 1, 0], ![0, 50, 1], ![-112, -37, 51]]]
  hmulB := by decide  
  f := ![![![3751, 75, 0], ![-13425, 0, 0]], ![![1050, 21, 0], ![-3758, 0, 0]], ![![114, 2, 0], ![-408, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 179, 0], ![-6, 0, 179]], ![![0, 1, 0], ![-14, 50, 1], ![8, -37, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11561, -879, 254]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![11561, -879, 254]] 
 ![![179, 0, 0], ![80, 1, 0], ![44, 0, 1]] where
  M :=![![![11561, -879, 254], ![-28448, 2163, -625], ![70000, -5323, 1538]]]
  hmulB := by decide  
  f := ![![![-181, -140, -27]], ![![-64, -58, -13]], ![![60, 17, -3]]]
  g := ![![![395, -879, 254], ![-972, 2163, -625], ![2392, -5323, 1538]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![48, 1, 0]] ![![179, 0, 0], ![50, 1, 0]]
  ![![-181, -140, -27]] where
 M := ![![![32041, 0, 0], ![8950, 179, 0]], ![![8592, 179, 0], ![2400, 98, 1]]]
 hmul := by decide  
 g := ![![![![2069419, -157341, 45466]], ![![549602, -41787, 12075]]], ![![![526480, -40029, 11567]], ![![139824, -10631, 3072]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![-181, -140, -27]] ![![11561, -879, 254]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![79, -7, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![79, -7, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![79, 174, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![79, -7, 1], ![-112, 42, -6], ![672, 110, 36]]]
  hmulB := by decide  
  f := ![![![-78, 7, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-79, -174, 181]], ![![0, -1, 1], ![2, 6, -6], ![-12, -34, 36]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [42, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 180], [0, 1]]
 g := ![![[8, 125], [148], [8, 169], [144], [78, 38], [7, 133], [1]], ![[0, 56], [148], [58, 12], [144], [161, 143], [26, 48], [1]]]
 h' := ![![[26, 180], [71, 46], [26, 87], [68, 13], [163, 169], [68, 161], [139, 26], [0, 1]], ![[0, 1], [0, 135], [116, 94], [44, 168], [32, 12], [91, 20], [91, 155], [26, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [82, 119]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [42, 155, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4170, 1428, 520]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-250, -492, 520]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![6, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![6, 1, 0]] 
 ![![181, 0, 0], ![6, 1, 0], ![145, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![6, 1, 0], ![0, 6, 1], ![-112, -37, 7]]]
  hmulB := by decide  
  f := ![![![847, 141, 0], ![-25521, 0, 0]], ![![18, 3, 0], ![-542, 0, 0]], ![![679, 113, 0], ![-20459, 1, 0]]]
  g := ![![![1, 0, 0], ![-6, 181, 0], ![-145, 0, 181]], ![![0, 1, 0], ![-1, 6, 1], ![-5, -37, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![79, -7, 1]] ![![181, 0, 0], ![6, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![1086, 181, 0]], ![![14299, -1267, 181], ![362, 0, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![6, 1, 0]]], ![![![79, -7, 1]], ![![2, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![40, -42, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![40, -42, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![40, 149, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![40, -42, 1], ![-112, 3, -41], ![4592, 1405, -38]]]
  hmulB := by decide  
  f := ![![![-39, 42, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -149, 191]], ![![0, -1, 1], ![8, 32, -41], ![32, 37, -38]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [7, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [159, 190], [0, 1]]
 g := ![![[141, 138], [175, 50], [61, 3], [74, 12], [49, 8], [150, 69], [1]], ![[118, 53], [103, 141], [156, 188], [72, 179], [175, 183], [43, 122], [1]]]
 h' := ![![[159, 190], [112, 86], [146, 97], [55, 24], [39, 143], [96, 114], [184, 159], [0, 1]], ![[0, 1], [34, 105], [98, 94], [51, 167], [47, 48], [77, 77], [62, 32], [159, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [125, 163]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [7, 32, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![536, 163, -63]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 50, -63]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![41, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![41, 1, 0]] 
 ![![191, 0, 0], ![41, 1, 0], ![38, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![41, 1, 0], ![0, 41, 1], ![-112, -37, 42]]]
  hmulB := by decide  
  f := ![![![493, 12, 0], ![-2292, 0, 0]], ![![41, 1, 0], ![-190, 0, 0]], ![![50, 1, 0], ![-232, 1, 0]]]
  g := ![![![1, 0, 0], ![-41, 191, 0], ![-38, 0, 191]], ![![0, 1, 0], ![-9, 41, 1], ![-1, -37, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![40, -42, 1]] ![![191, 0, 0], ![41, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![7831, 191, 0]], ![![7640, -8022, 191], ![1528, -1719, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![41, 1, 0]]], ![![![40, -42, 1]], ![![8, -9, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![35, 73, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![35, 73, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![35, 73, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![35, 73, 1], ![-112, -2, 74], ![-8288, -2850, 72]]]
  hmulB := by decide  
  f := ![![![-34, -73, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -73, 193]], ![![0, 0, 1], ![-14, -28, 74], ![-56, -42, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [18, 170, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [23, 192], [0, 1]]
 g := ![![[181, 118], [9], [192], [59], [112], [185], [23, 1]], ![[0, 75], [9], [192], [59], [112], [185], [46, 192]]]
 h' := ![![[23, 192], [58, 73], [42, 3], [88, 112], [125, 161], [156, 150], [165, 125], [0, 1]], ![[0, 1], [0, 120], [111, 190], [155, 81], [161, 32], [132, 43], [145, 68], [23, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [71, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [18, 170, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-878, -574, 201]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41, -79, 201]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-74, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-74, 1, 0]] 
 ![![193, 0, 0], ![119, 1, 0], ![121, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-74, 1, 0], ![0, -74, 1], ![-112, -37, -73]]]
  hmulB := by decide  
  f := ![![![6513, -88, 0], ![16984, 0, 0]], ![![4071, -55, 0], ![10616, 0, 0]], ![![4173, -56, 0], ![10882, 1, 0]]]
  g := ![![![1, 0, 0], ![-119, 193, 0], ![-121, 0, 193]], ![![-1, 1, 0], ![45, -74, 1], ![68, -37, -73]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![35, 73, 1]] ![![193, 0, 0], ![-74, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-14282, 193, 0]], ![![6755, 14089, 193], ![-2702, -5404, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-74, 1, 0]]], ![![![35, 73, 1]], ![![-14, -28, 0]]]]
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


lemma PB222I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB222I3 : PrimesBelowBoundCertificateInterval O 137 193 222 where
  m := 11
  g := ![2, 3, 3, 1, 2, 2, 2, 3, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB222I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
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
    · exact ![149, 149, 149]
    · exact ![151, 151, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
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
      exact NI149N1
      exact NI149N2
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
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N0, I149N1, I149N2, I151N0, I151N1, I151N2, I163N1, I167N1, I173N1, I179N0, I179N1, I179N2, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [I151N0, I151N1, I151N2], [], [I163N1], [I167N1], [I173N1], [I179N0, I179N1, I179N2], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
