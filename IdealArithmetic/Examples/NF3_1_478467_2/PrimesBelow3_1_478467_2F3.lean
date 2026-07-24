
import IdealArithmetic.Examples.NF3_1_478467_2.RI3_1_478467_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80, -10, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-80, -10, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![59, 129, 1]] where
  M :=![![![-80, -10, 1], ![939, 100, -10], ![-9390, -861, 100]]]
  hmulB := by decide  
  f := ![![![10, 1, 0]], ![![0, 10, 1]], ![![11, 11, 1]]]
  g := ![![![-1, -1, 1], ![11, 10, -10], ![-110, -99, 100]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [99, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 138], [0, 1]]
 g := ![![[28, 66], [133, 30], [107], [95, 31], [71], [64], [1]], ![[0, 73], [95, 109], [107], [65, 108], [71], [64], [1]]]
 h' := ![![[8, 138], [38, 30], [95, 126], [47, 78], [21, 46], [129, 40], [40, 8], [0, 1]], ![[0, 1], [0, 109], [130, 13], [115, 61], [111, 93], [32, 99], [104, 131], [8, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [5, 103]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [99, 131, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1977, 1168, 50]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7, -38, 50]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![10, 1, 0]] 
 ![![139, 0, 0], ![10, 1, 0], ![39, 0, 1]] where
  M :=![![![10, 1, 0], ![0, 10, 1], ![939, 180, 10]]]
  hmulB := by decide  
  f := ![![![-80, -10, 1]], ![![1, 0, 0]], ![![-90, -9, 1]]]
  g := ![![![0, 1, 0], ![-1, 10, 1], ![-9, 180, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-80, -10, 1]] ![![10, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [53, 26, 115, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 137, 72], [109, 11, 77], [0, 1]]
 g := ![![[97, 104, 67], [25, 5], [84, 145, 63], [147, 142], [36, 140, 119], [34, 1], []], ![[110, 49, 52, 41], [86, 53], [26, 66, 7, 115], [18, 133], [67, 116, 113, 55], [129, 121], [49, 118]], ![[146, 94, 104, 115], [12, 9], [115, 129, 7, 83], [126, 127], [10, 146, 29, 59], [34, 144], [44, 118]]]
 h' := ![![[74, 137, 72], [42, 13, 31], [18, 92, 81], [53, 69, 19], [29, 35, 80], [135, 106, 87], [0, 0, 1], [0, 1]], ![[109, 11, 77], [108, 33, 85], [135, 106, 65], [111, 4, 111], [52, 111, 122], [86, 138, 96], [48, 83, 11], [74, 137, 72]], ![[0, 1], [74, 103, 33], [73, 100, 3], [73, 76, 19], [116, 3, 96], [6, 54, 115], [13, 66, 137], [109, 11, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 59], []]
 b := ![[], [18, 131, 113], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [53, 26, 115, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13410000, 8114838, 1011859]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![90000, 54462, 6791]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-163, 35, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-163, 35, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![139, 35, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-163, 35, 1], ![939, 17, 35], ![32865, 7239, 17]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-139, -35, 151]], ![![-2, 0, 1], ![-26, -8, 35], ![202, 44, 17]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [65, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 150], [0, 1]]
 g := ![![[110, 62], [29, 139], [38, 98], [22], [107, 95], [91], [1]], ![[146, 89], [61, 12], [129, 53], [22], [55, 56], [91], [1]]]
 h' := ![![[98, 150], [78, 45], [97, 21], [10, 20], [142, 18], [122, 104], [86, 98], [0, 1]], ![[0, 1], [109, 106], [41, 130], [7, 131], [94, 133], [46, 47], [26, 53], [98, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [112, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [65, 53, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1109, 504, 256]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-243, -56, 256]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-35, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-35, 1, 0]] 
 ![![151, 0, 0], ![116, 1, 0], ![134, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-35, 1, 0], ![0, -35, 1], ![939, 180, -35]]]
  hmulB := by decide  
  f := ![![![3501, -100, 0], ![15100, 0, 0]], ![![2696, -77, 0], ![11628, 0, 0]], ![![3124, -89, 0], ![13474, 1, 0]]]
  g := ![![![1, 0, 0], ![-116, 151, 0], ![-134, 0, 151]], ![![-1, 1, 0], ![26, -35, 1], ![-101, 180, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-163, 35, 1]] ![![151, 0, 0], ![-35, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-5285, 151, 0]], ![![-24613, 5285, 151], ![6644, -1208, 0]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-35, 1, 0]]], ![![![-163, 35, 1]], ![![44, -8, 0]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-69, 41, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-69, 41, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![88, 41, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-69, 41, 1], ![939, 111, 41], ![38499, 8319, 111]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -41, 157]], ![![-1, 0, 1], ![-17, -10, 41], ![183, 24, 111]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [65, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [156, 156], [0, 1]]
 g := ![![[29, 109], [36], [107, 11], [154, 9], [29, 156], [1], [1]], ![[77, 48], [36], [96, 146], [145, 148], [30, 1], [1], [1]]]
 h' := ![![[156, 156], [26, 57], [110, 151], [38, 47], [156, 154], [78, 129], [92, 156], [0, 1]], ![[0, 1], [126, 100], [116, 6], [148, 110], [2, 3], [106, 28], [93, 1], [156, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [137, 117]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [65, 1, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5567, 7374, 1612]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-939, -374, 1612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-41, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-41, 1, 0]] 
 ![![157, 0, 0], ![116, 1, 0], ![46, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-41, 1, 0], ![0, -41, 1], ![939, 180, -41]]]
  hmulB := by decide  
  f := ![![![1354, -33, 0], ![5181, 0, 0]], ![![1026, -25, 0], ![3926, 0, 0]], ![![462, -11, 0], ![1768, 1, 0]]]
  g := ![![![1, 0, 0], ![-116, 157, 0], ![-46, 0, 157]], ![![-1, 1, 0], ![30, -41, 1], ![-115, 180, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-69, 41, 1]] ![![157, 0, 0], ![-41, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6437, 157, 0]], ![![-10833, 6437, 157], ![3768, -1570, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-41, 1, 0]]], ![![![-69, 41, 1]], ![![24, -10, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-137, -83, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-137, -83, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![26, 80, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-137, -83, 1], ![939, 43, -83], ![-77937, -14001, 43]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-26, -80, 163]], ![![-1, -1, 1], ![19, 41, -83], ![-485, -107, 43]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [89, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [89, 162], [0, 1]]
 g := ![![[162, 140], [17, 62], [9], [46], [10], [126, 97], [1]], ![[71, 23], [156, 101], [9], [46], [10], [120, 66], [1]]]
 h' := ![![[89, 162], [117, 38], [91, 148], [136, 160], [36, 131], [33, 70], [74, 89], [0, 1]], ![[0, 1], [76, 125], [60, 15], [32, 3], [122, 32], [69, 93], [8, 74], [89, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [140, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [89, 74, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1967, 1225, 107]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -45, 107]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-80, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-80, 1, 0]] 
 ![![163, 0, 0], ![83, 1, 0], ![120, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-80, 1, 0], ![0, -80, 1], ![939, 180, -80]]]
  hmulB := by decide  
  f := ![![![11041, -138, 0], ![22494, 0, 0]], ![![5681, -71, 0], ![11574, 0, 0]], ![![8200, -102, 0], ![16706, 1, 0]]]
  g := ![![![1, 0, 0], ![-83, 163, 0], ![-120, 0, 163]], ![![-1, 1, 0], ![40, -80, 1], ![-27, 180, -80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-137, -83, 1]] ![![163, 0, 0], ![-80, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-13040, 163, 0]], ![![-22331, -13529, 163], ![11899, 6683, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-80, 1, 0]]], ![![![-137, -83, 1]], ![![73, 41, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-93, 33, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-93, 33, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![74, 33, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-93, 33, 1], ![939, 87, 33], ![30987, 6879, 87]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -33, 167]], ![![-1, 0, 1], ![-9, -6, 33], ![147, 24, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [135, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 166], [0, 1]]
 g := ![![[156, 154], [118, 130], [110, 137], [84], [9], [30, 157], [1]], ![[56, 13], [116, 37], [149, 30], [84], [9], [43, 10], [1]]]
 h' := ![![[149, 166], [102, 34], [13, 56], [149, 114], [48, 90], [125, 164], [32, 149], [0, 1]], ![[0, 1], [158, 133], [7, 111], [101, 53], [98, 77], [12, 3], [22, 18], [149, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133]]
 b := ![[], [14, 150]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [135, 18, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![35836, 8159, 561]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -62, 561]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-33, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-33, 1, 0]] 
 ![![167, 0, 0], ![134, 1, 0], ![80, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-33, 1, 0], ![0, -33, 1], ![939, 180, -33]]]
  hmulB := by decide  
  f := ![![![3202, -97, 0], ![16199, 0, 0]], ![![2608, -79, 0], ![13194, 0, 0]], ![![1558, -47, 0], ![7882, 1, 0]]]
  g := ![![![1, 0, 0], ![-134, 167, 0], ![-80, 0, 167]], ![![-1, 1, 0], ![26, -33, 1], ![-123, 180, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-93, 33, 1]] ![![167, 0, 0], ![-33, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-5511, 167, 0]], ![![-15531, 5511, 167], ![4008, -1002, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-33, 1, 0]]], ![![![-93, 33, 1]], ![![24, -6, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [163, 164, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 35, 57], [145, 137, 116], [0, 1]]
 g := ![![[53, 74, 64], [169, 1], [135, 168, 51], [163, 91, 92], [131, 15], [125, 156, 1], []], ![[56, 35, 19, 135], [93, 89], [145, 46, 70, 151], [65, 35], [95, 126], [64, 57, 157, 1], [138, 135]], ![[129, 117, 49, 106], [157, 67], [131, 92, 50, 89], [38, 112, 162, 119], [127, 130], [79, 118, 47, 67], [79, 135]]]
 h' := ![![[11, 35, 57], [78, 51, 8], [139, 93, 1], [73, 118, 140], [63, 45, 28], [39, 90, 154], [0, 0, 1], [0, 1]], ![[145, 137, 116], [18, 136, 24], [68, 43, 75], [105, 98, 129], [28, 42], [17, 168, 105], [117, 75, 137], [11, 35, 57]], ![[0, 1], [170, 159, 141], [147, 37, 97], [14, 130, 77], [144, 86, 145], [137, 88, 87], [17, 98, 35], [145, 137, 116]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1, 31], []]
 b := ![[], [1, 136, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [163, 164, 17, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![585951, -68508, -26296]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3387, -396, -152]
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


def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5916992, 1515756, 97731]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![5916992, 1515756, 97731]] 
 ![![179, 0, 0], ![47, 1, 0], ![118, 0, 1]] where
  M :=![![![5916992, 1515756, 97731], ![91769409, 23508572, 1515756], ![1423294884, 364605489, 23508572]]]
  hmulB := by decide  
  f := ![![![-105500, -14973, 1404]], ![![-20336, -3109, 285]], ![![-148093, -17562, 1748]]]
  g := ![![![-429362, 1515756, 97731], ![-6659177, 23508572, 1515756], ![-103280305, 364605489, 23508572]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![66, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![66, 1, 0]] 
 ![![179, 0, 0], ![66, 1, 0], ![119, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![66, 1, 0], ![0, 66, 1], ![939, 180, 66]]]
  hmulB := by decide  
  f := ![![![1123, 17, 0], ![-3043, 0, 0]], ![![330, 5, 0], ![-894, 0, 0]], ![![751, 11, 0], ![-2035, 1, 0]]]
  g := ![![![1, 0, 0], ![-66, 179, 0], ![-119, 0, 179]], ![![0, 1, 0], ![-25, 66, 1], ![-105, 180, 66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![5916992, 1515756, 97731]] ![![179, 0, 0], ![66, 1, 0]]
  ![![179, 0, 0], ![-120, -66, 1]] where
 M := ![![![1059141568, 271320324, 17493849], ![482290881, 123548468, 7966002]]]
 hmul := by decide  
 g := ![![![![4003592, 463386, 113676], ![-2854155, 0, 0]], ![![1823139, 211042, 51763], ![-1299575, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-120, -66, 1]] ![![179, 0, 0], ![66, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![11814, 179, 0]], ![![-21480, -11814, 179], ![-6981, -4296, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![66, 1, 0]]], ![![![-120, -66, 1]], ![![-39, -24, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-209, -40, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-209, -40, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![153, 141, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-209, -40, 1], ![939, -29, -40], ![-37560, -6261, -29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -141, 181]], ![![-2, -1, 1], ![39, 31, -40], ![-183, -12, -29]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [144, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 180], [0, 1]]
 g := ![![[27, 44], [39], [154, 73], [4], [141, 43], [53, 148], [1]], ![[0, 137], [39], [138, 108], [4], [20, 138], [28, 33], [1]]]
 h' := ![![[94, 180], [143, 166], [87, 138], [86, 142], [149, 179], [151, 62], [37, 94], [0, 1]], ![[0, 1], [0, 15], [27, 43], [40, 39], [142, 2], [6, 119], [4, 87], [94, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [26, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [144, 87, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3900, 4563, 895]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-735, -672, 895]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![40, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![40, 1, 0]] 
 ![![181, 0, 0], ![40, 1, 0], ![29, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![40, 1, 0], ![0, 40, 1], ![939, 180, 40]]]
  hmulB := by decide  
  f := ![![![2721, 68, 0], ![-12308, 0, 0]], ![![600, 15, 0], ![-2714, 0, 0]], ![![409, 10, 0], ![-1850, 1, 0]]]
  g := ![![![1, 0, 0], ![-40, 181, 0], ![-29, 0, 181]], ![![0, 1, 0], ![-9, 40, 1], ![-41, 180, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-209, -40, 1]] ![![181, 0, 0], ![40, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![7240, 181, 0]], ![![-37829, -7240, 181], ![-7421, -1629, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![40, 1, 0]]], ![![![-209, -40, 1]], ![![-41, -9, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-194, 69, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-194, 69, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![188, 69, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-194, 69, 1], ![939, -14, 69], ![64791, 13359, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-188, -69, 191]], ![![-2, 0, 1], ![-63, -25, 69], ![353, 75, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [4, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [105, 190], [0, 1]]
 g := ![![[117, 48], [154, 24], [187, 160], [33, 136], [14, 147], [89, 138], [1]], ![[0, 143], [0, 167], [179, 31], [179, 55], [169, 44], [63, 53], [1]]]
 h' := ![![[105, 190], [148, 95], [16, 129], [59, 136], [135, 30], [26, 23], [187, 105], [0, 1]], ![[0, 1], [0, 96], [0, 62], [14, 55], [38, 161], [149, 168], [134, 86], [105, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [144]]
 b := ![[], [40, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [4, 86, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37380, -4344, 1000]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1180, -384, 1000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-69, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-69, 1, 0]] 
 ![![191, 0, 0], ![122, 1, 0], ![14, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-69, 1, 0], ![0, -69, 1], ![939, 180, -69]]]
  hmulB := by decide  
  f := ![![![3865, -56, 0], ![10696, 0, 0]], ![![2416, -35, 0], ![6686, 0, 0]], ![![370, -5, 0], ![1024, 1, 0]]]
  g := ![![![1, 0, 0], ![-122, 191, 0], ![-14, 0, 191]], ![![-1, 1, 0], ![44, -69, 1], ![-105, 180, -69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-194, 69, 1]] ![![191, 0, 0], ![-69, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-13179, 191, 0]], ![![-37054, 13179, 191], ![14325, -4775, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-69, 1, 0]]], ![![![-194, 69, 1]], ![![75, -25, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-43, 41, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-43, 41, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![150, 41, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-43, 41, 1], ![939, 137, 41], ![38499, 8319, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-150, -41, 193]], ![![-1, 0, 1], ![-27, -8, 41], ![93, 14, 137]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [170, 96, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [97, 192], [0, 1]]
 g := ![![[21, 151], [56], [118], [96], [150], [46], [97, 1]], ![[0, 42], [56], [118], [96], [150], [46], [1, 192]]]
 h' := ![![[97, 192], [146, 94], [189, 40], [62, 73], [39, 176], [177, 27], [108, 168], [0, 1]], ![[0, 1], [0, 99], [16, 153], [2, 120], [127, 17], [94, 166], [192, 25], [97, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [68, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [170, 96, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-291, 457, 303]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-237, -62, 303]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-41, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-41, 1, 0]] 
 ![![193, 0, 0], ![152, 1, 0], ![56, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-41, 1, 0], ![0, -41, 1], ![939, 180, -41]]]
  hmulB := by decide  
  f := ![![![5454, -133, 0], ![25669, 0, 0]], ![![4306, -105, 0], ![20266, 0, 0]], ![![1608, -39, 0], ![7568, 1, 0]]]
  g := ![![![1, 0, 0], ![-152, 193, 0], ![-56, 0, 193]], ![![-1, 1, 0], ![32, -41, 1], ![-125, 180, -41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-43, 41, 1]] ![![193, 0, 0], ![-41, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-7913, 193, 0]], ![![-8299, 7913, 193], ![2702, -1544, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-41, 1, 0]]], ![![![-43, 41, 1]], ![![14, -8, 0]]]]
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


lemma PB196I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 195 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 195 (by omega)

def PB196I3 : PrimesBelowBoundCertificateInterval O 137 195 196 where
  m := 11
  g := ![2, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB196I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N1]
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
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N1
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
  β := ![I139N1, I151N1, I157N1, I163N1, I167N1, I179N0, I179N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [], [I151N1], [I157N1], [I163N1], [I167N1], [], [I179N0, I179N1, I179N1], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
