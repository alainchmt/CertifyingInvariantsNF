
import IdealArithmetic.Examples.NF3_1_532652_1.RI3_1_532652_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-66, -50, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-66, -50, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![73, 89, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-66, -50, 1], ![242, -2, -50], ![-12100, -2958, -2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-73, -89, 139]], ![![-1, -1, 1], ![28, 32, -50], ![-86, -20, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [17, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 138], [0, 1]]
 g := ![![[76, 4], [21, 121], [83], [75, 136], [34], [13], [1]], ![[51, 135], [64, 18], [83], [59, 3], [34], [13], [1]]]
 h' := ![![[98, 138], [60, 2], [138, 11], [115, 120], [15, 54], [68, 27], [122, 98], [0, 1]], ![[0, 1], [117, 137], [104, 128], [60, 19], [25, 85], [73, 112], [135, 41], [98, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86]]
 b := ![[], [117, 43]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [17, 41, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![501, 329, 24]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9, -13, 24]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![50, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![50, 1, 0]] 
 ![![139, 0, 0], ![50, 1, 0], ![2, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![50, 1, 0], ![0, 50, 1], ![242, 64, 50]]]
  hmulB := by decide  
  f := ![![![2701, 54, 0], ![-7506, 0, 0]], ![![950, 19, 0], ![-2640, 0, 0]], ![![18, 0, 0], ![-50, 1, 0]]]
  g := ![![![1, 0, 0], ![-50, 139, 0], ![-2, 0, 139]], ![![0, 1, 0], ![-18, 50, 1], ![-22, 64, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-66, -50, 1]] ![![139, 0, 0], ![50, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![6950, 139, 0]], ![![-9174, -6950, 139], ![-3058, -2502, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![50, 1, 0]]], ![![![-66, -50, 1]], ![![-22, -18, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![3, 31, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![3, 31, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![3, 31, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![3, 31, 1], ![242, 67, 31], ![7502, 2226, 67]]]
  hmulB := by decide  
  f := ![![![-2, -31, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -31, 149]], ![![0, 0, 1], ![1, -6, 31], ![49, 1, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [109, 55, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 148], [0, 1]]
 g := ![![[129, 140], [46], [99, 69], [26], [123, 143], [45], [1]], ![[28, 9], [46], [29, 80], [26], [6, 6], [45], [1]]]
 h' := ![![[94, 148], [147, 17], [86, 33], [6, 101], [3, 131], [122, 128], [40, 94], [0, 1]], ![[0, 1], [106, 132], [59, 116], [113, 48], [99, 18], [85, 21], [85, 55], [94, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [117]]
 b := ![[], [7, 133]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [109, 55, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2849, 1304, 739]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-34, -145, 739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-31, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-31, 1, 0]] 
 ![![149, 0, 0], ![118, 1, 0], ![82, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-31, 1, 0], ![0, -31, 1], ![242, 64, -31]]]
  hmulB := by decide  
  f := ![![![4186, -135, 0], ![20115, 0, 0]], ![![3318, -107, 0], ![15944, 0, 0]], ![![2332, -75, 0], ![11206, 1, 0]]]
  g := ![![![1, 0, 0], ![-118, 149, 0], ![-82, 0, 149]], ![![-1, 1, 0], ![24, -31, 1], ![-32, 64, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![3, 31, 1]] ![![149, 0, 0], ![-31, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-4619, 149, 0]], ![![447, 4619, 149], ![149, -894, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-31, 1, 0]]], ![![![3, 31, 1]], ![![1, -6, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [91, 59, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 10, 136], [106, 140, 15], [0, 1]]
 g := ![![[8, 119, 144], [21, 59, 128], [48, 33, 81], [74, 95], [27, 144, 10], [133, 1], []], ![[15, 133, 78, 36], [81, 80, 118, 148], [123, 51, 54, 125], [128, 123], [146, 42, 72, 39], [45, 121], [29, 74]], ![[141, 81, 86, 120], [46, 105, 7, 147], [123, 19, 39, 77], [91, 58], [19, 129, 73, 15], [15, 100], [150, 74]]]
 h' := ![![[27, 10, 136], [52, 6, 12], [11, 122, 66], [81, 108, 9], [110, 26, 104], [128, 65, 114], [0, 0, 1], [0, 1]], ![[106, 140, 15], [95, 28, 80], [8, 138, 11], [1, 150, 93], [133, 33, 127], [73, 44, 36], [53, 98, 140], [27, 10, 136]], ![[0, 1], [108, 117, 59], [89, 42, 74], [71, 44, 49], [54, 92, 71], [149, 42, 1], [2, 53, 10], [106, 140, 15]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 25], []]
 b := ![[], [131, 96, 52], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [91, 59, 18, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-119743, -29143, -24915]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-793, -193, -165]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [156, 62, 67, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 99, 75], [57, 57, 82], [0, 1]]
 g := ![![[33, 148, 4], [103, 122], [86, 154, 67], [78, 124, 14], [119, 113, 19], [90, 1], []], ![[114, 140, 120, 108], [12, 115], [134, 19, 150, 27], [20, 138, 19, 71], [127, 110, 38, 13], [155, 109], [17, 130]], ![[146, 29, 135, 17], [153, 12], [91, 84, 60, 90], [92, 24, 134, 12], [103, 62, 101, 76], [59, 67], [10, 130]]]
 h' := ![![[33, 99, 75], [120, 104, 2], [86, 121, 114], [78, 29, 99], [119, 50, 64], [90, 73, 31], [0, 0, 1], [0, 1]], ![[57, 57, 82], [112, 7, 64], [10, 126, 30], [1, 126, 125], [19, 64, 19], [47, 116, 20], [7, 115, 57], [33, 99, 75]], ![[0, 1], [6, 46, 91], [139, 67, 13], [10, 2, 90], [66, 43, 74], [90, 125, 106], [119, 42, 99], [57, 57, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 35], []]
 b := ![[], [15, 37, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [156, 62, 67, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1264164, -602095, -64841]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8052, -3835, -413]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-207, -35, 6]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-207, -35, 6]] 
 ![![163, 0, 0], ![0, 163, 0], ![47, 130, 1]] where
  M :=![![![-207, -35, 6], ![1452, 177, -35], ![-8470, -788, 177]]]
  hmulB := by decide  
  f := ![![![-23, -9, -1]], ![![-242, -87, -9]], ![![-213, -77, -8]]]
  g := ![![![-3, -5, 6], ![19, 29, -35], ![-103, -146, 177]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [58, 50, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 162], [0, 1]]
 g := ![![[147, 104], [50, 1], [151], [36], [47], [116, 55], [1]], ![[0, 59], [0, 162], [151], [36], [47], [137, 108], [1]]]
 h' := ![![[113, 162], [34, 105], [50, 1], [150, 92], [114, 157], [118, 79], [105, 113], [0, 1]], ![[0, 1], [0, 58], [0, 162], [114, 71], [88, 6], [80, 84], [160, 50], [113, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140]]
 b := ![[], [120, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [58, 50, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![542, 320, 15]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -10, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 9, 1]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![23, 9, 1]] 
 ![![163, 0, 0], ![33, 1, 0], ![52, 0, 1]] where
  M :=![![![23, 9, 1], ![242, 87, 9], ![2178, 818, 87]]]
  hmulB := by decide  
  f := ![![![207, 35, -6]], ![![33, 6, -1]], ![![118, 16, -3]]]
  g := ![![![-2, 9, 1], ![-19, 87, 9], ![-180, 818, 87]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-207, -35, 6]] ![![23, 9, 1]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-14, -65, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-14, -65, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![153, 102, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-14, -65, 1], ![242, 50, -65], ![-15730, -3918, 50]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-153, -102, 167]], ![![-1, -1, 1], ![61, 40, -65], ![-140, -54, 50]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [41, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [146, 166], [0, 1]]
 g := ![![[139, 107], [89, 133], [156, 1], [61], [126], [143, 107], [1]], ![[63, 60], [135, 34], [135, 166], [61], [126], [67, 60], [1]]]
 h' := ![![[146, 166], [25, 21], [117, 48], [5, 1], [1, 140], [149, 136], [126, 146], [0, 1]], ![[0, 1], [85, 146], [111, 119], [151, 166], [67, 27], [132, 31], [66, 21], [146, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [141, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [41, 21, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9259, 3111, 448]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-355, -255, 448]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![65, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![65, 1, 0]] 
 ![![167, 0, 0], ![65, 1, 0], ![117, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![65, 1, 0], ![0, 65, 1], ![242, 64, 65]]]
  hmulB := by decide  
  f := ![![![1041, 16, 0], ![-2672, 0, 0]], ![![325, 5, 0], ![-834, 0, 0]], ![![741, 11, 0], ![-1902, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 167, 0], ![-117, 0, 167]], ![![0, 1, 0], ![-26, 65, 1], ![-69, 64, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-14, -65, 1]] ![![167, 0, 0], ![65, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![10855, 167, 0]], ![![-2338, -10855, 167], ![-668, -4175, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![65, 1, 0]]], ![![![-14, -65, 1]], ![![-4, -25, 0]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [2, 75, 131, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [162, 52, 136], [53, 120, 37], [0, 1]]
 g := ![![[92, 52, 89], [128, 126], [133, 117, 84], [160, 155, 126], [27, 35], [132, 42, 1], []], ![[51, 94, 111, 117], [6, 84], [126, 140, 139, 144], [158, 133, 69, 159], [41, 130], [50, 156, 51, 40], [20, 158]], ![[121, 51, 83, 15], [54, 78], [4, 8, 21, 10], [140, 145, 96, 24], [167, 22], [44, 145, 57, 54], [119, 158]]]
 h' := ![![[162, 52, 136], [89, 70, 75], [80, 155, 105], [26, 20, 118], [96, 50, 68], [82, 50, 143], [0, 0, 1], [0, 1]], ![[53, 120, 37], [31, 139, 9], [133, 10, 118], [22, 9, 99], [37, 97, 82], [43, 56, 86], [81, 154, 120], [162, 52, 136]], ![[0, 1], [96, 137, 89], [66, 8, 123], [157, 144, 129], [76, 26, 23], [165, 67, 117], [149, 19, 52], [53, 120, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 135], []]
 b := ![[], [5, 160, 13], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [2, 75, 131, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98437, -17646, 5882]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-569, -102, 34]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![1, 1, 0]] 
 ![![179, 0, 0], ![1, 1, 0], ![178, 0, 1]] where
  M :=![![![1, 1, 0], ![0, 1, 1], ![242, 64, 1]]]
  hmulB := by decide  
  f := ![![![-63, -1, 1]], ![![1, 0, 0]], ![![-64, 0, 1]]]
  g := ![![![0, 1, 0], ![-1, 1, 1], ![0, 64, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![24, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![24, 1, 0]] 
 ![![179, 0, 0], ![24, 1, 0], ![140, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![24, 1, 0], ![0, 24, 1], ![242, 64, 24]]]
  hmulB := by decide  
  f := ![![![1993, 83, 0], ![-14857, 0, 0]], ![![264, 11, 0], ![-1968, 0, 0]], ![![1540, 64, 0], ![-11480, 1, 0]]]
  g := ![![![1, 0, 0], ![-24, 179, 0], ![-140, 0, 179]], ![![0, 1, 0], ![-4, 24, 1], ![-26, 64, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-25, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-25, 1, 0]] 
 ![![179, 0, 0], ![154, 1, 0], ![91, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-25, 1, 0], ![0, -25, 1], ![242, 64, -25]]]
  hmulB := by decide  
  f := ![![![1326, -53, 0], ![9487, 0, 0]], ![![1126, -45, 0], ![8056, 0, 0]], ![![704, -28, 0], ![5037, 1, 0]]]
  g := ![![![1, 0, 0], ![-154, 179, 0], ![-91, 0, 179]], ![![-1, 1, 0], ![21, -25, 1], ![-41, 64, -25]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 0]] ![![179, 0, 0], ![24, 1, 0]]
  ![![179, 0, 0], ![24, 25, 1]] where
 M := ![![![179, 179, 0], ![24, 25, 1]]]
 hmul := by decide  
 g := ![![![![-23, -24, -1], ![179, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![24, 25, 1]] ![![179, 0, 0], ![-25, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-4475, 179, 0]], ![![4296, 4475, 179], ![-358, -537, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-25, 1, 0]]], ![![![24, 25, 1]], ![![-2, -3, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-17361, -6426, -679]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-17361, -6426, -679]] 
 ![![181, 0, 0], ![0, 181, 0], ![121, 2, 1]] where
  M :=![![![-17361, -6426, -679], ![-164318, -60817, -6426], ![-1555092, -575582, -60817]]]
  hmulB := by decide  
  f := ![![![-97, -56, 7]], ![![1694, 351, -56]], ![![-121, -44, 6]]]
  g := ![![![358, -28, -679], ![3388, -265, -6426], ![32065, -2508, -60817]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [100, 116, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [65, 180], [0, 1]]
 g := ![![[117, 143], [79], [120, 52], [79], [123, 147], [80, 62], [1]], ![[0, 38], [79], [61, 129], [79], [85, 34], [128, 119], [1]]]
 h' := ![![[65, 180], [84, 163], [127, 160], [128, 41], [8, 21], [145, 131], [81, 65], [0, 1]], ![[0, 1], [0, 18], [29, 21], [78, 140], [106, 160], [153, 50], [143, 116], [65, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [146, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [100, 116, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1068, 1340, 489]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-321, 2, 489]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 56, -7]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![97, 56, -7]] 
 ![![181, 0, 0], ![179, 1, 0], ![177, 0, 1]] where
  M :=![![![97, 56, -7], ![-1694, -351, 56], ![13552, 1890, -351]]]
  hmulB := by decide  
  f := ![![![17361, 6426, 679]], ![![18077, 6691, 707]], ![![25569, 9464, 1000]]]
  g := ![![![-48, 56, -7], ![283, -351, 56], ![-1451, 1890, -351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-17361, -6426, -679]] ![![97, 56, -7]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-25, 82, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-25, 82, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![166, 82, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-25, 82, 1], ![242, 39, 82], ![19844, 5490, 39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-166, -82, 191]], ![![-1, 0, 1], ![-70, -35, 82], ![70, 12, 39]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [155, 144, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [47, 190], [0, 1]]
 g := ![![[187, 25], [97, 130], [55, 130], [32, 100], [137, 34], [56, 108], [1]], ![[25, 166], [95, 61], [53, 61], [148, 91], [16, 157], [166, 83], [1]]]
 h' := ![![[47, 190], [54, 5], [70, 43], [6, 148], [157, 181], [106, 176], [36, 47], [0, 1]], ![[0, 1], [98, 186], [181, 148], [86, 43], [69, 10], [165, 15], [144, 144], [47, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [54, 144]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [155, 144, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9233, -3072, 652]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-615, -296, 652]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-82, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-82, 1, 0]] 
 ![![191, 0, 0], ![109, 1, 0], ![152, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-82, 1, 0], ![0, -82, 1], ![242, 64, -82]]]
  hmulB := by decide  
  f := ![![![1067, -13, 0], ![2483, 0, 0]], ![![657, -8, 0], ![1529, 0, 0]], ![![856, -10, 0], ![1992, 1, 0]]]
  g := ![![![1, 0, 0], ![-109, 191, 0], ![-152, 0, 191]], ![![-1, 1, 0], ![46, -82, 1], ![30, 64, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-25, 82, 1]] ![![191, 0, 0], ![-82, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-15662, 191, 0]], ![![-4775, 15662, 191], ![2292, -6685, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-82, 1, 0]]], ![![![-25, 82, 1]], ![![12, -35, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [118, 101, 26, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [121, 185, 127], [46, 7, 66], [0, 1]]
 g := ![![[138, 148, 161], [89, 129], [175, 139], [74, 69], [142, 98], [28, 97], [1]], ![[83, 129, 14, 19], [173, 48], [171, 131], [52, 3], [49, 55], [121, 101], [125, 67, 68, 74]], ![[184, 56, 0, 116], [32, 169], [92, 147], [27, 112], [86, 1], [16, 8], [22, 51, 181, 119]]]
 h' := ![![[121, 185, 127], [30, 187, 57], [66, 24, 124], [79, 112, 116], [60, 41, 164], [5, 105, 22], [75, 92, 167], [0, 1]], ![[46, 7, 66], [68, 106, 23], [105, 73, 56], [37, 99, 175], [24, 147, 179], [189, 144, 172], [125, 189, 115], [121, 185, 127]], ![[0, 1], [146, 93, 113], [86, 96, 13], [83, 175, 95], [145, 5, 43], [185, 137, 192], [170, 105, 104], [46, 7, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [165, 24], []]
 b := ![[], [64, 110, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [118, 101, 26, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11580, 25476, 9071]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-60, 132, 47]
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



lemma PB207I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB207I3 : PrimesBelowBoundCertificateInterval O 137 193 207 where
  m := 11
  g := ![2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB207I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
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
  β := ![I139N1, I149N1, I163N1, I167N1, I179N0, I179N1, I179N2, I181N1, I191N1]
  Il := ![[I139N1], [I149N1], [], [], [I163N1], [I167N1], [], [I179N0, I179N1, I179N2], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
