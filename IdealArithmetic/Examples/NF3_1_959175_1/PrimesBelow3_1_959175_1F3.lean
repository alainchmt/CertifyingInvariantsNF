
import IdealArithmetic.Examples.NF3_1_959175_1.RI3_1_959175_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [138, 29, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 57, 126], [78, 81, 13], [0, 1]]
 g := ![![[24, 28, 106], [13, 67, 71], [21, 125], [59, 98, 66], [121, 137], [102, 1], []], ![[32, 56, 0, 21], [21, 38, 2, 8], [104, 137], [120, 137, 124, 82], [90, 28], [14, 28], [49, 30]], ![[102, 118, 18, 36], [43, 33, 79, 121], [31, 7], [114, 4, 13, 49], [36, 64], [9, 52], [23, 30]]]
 h' := ![![[24, 57, 126], [13, 2, 84], [27, 58, 40], [59, 47, 79], [100, 135, 30], [102, 101, 89], [0, 0, 1], [0, 1]], ![[78, 81, 13], [19, 87, 106], [9, 116, 123], [105, 97, 89], [128, 90, 119], [49, 84, 58], [69, 94, 81], [24, 57, 126]], ![[0, 1], [108, 50, 88], [21, 104, 115], [95, 134, 110], [74, 53, 129], [90, 93, 131], [130, 45, 57], [78, 81, 13]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [14, 110], []]
 b := ![[], [18, 131, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [138, 29, 37, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1225702, -412830, -61021]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8818, -2970, -439]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-75, -56, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-75, -56, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![74, 93, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-75, -56, 1], ![280, -79, -113], ![-15960, -2798, 34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -93, 149]], ![![-1, -1, 1], ![58, 70, -113], ![-124, -40, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [131, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [97, 148], [0, 1]]
 g := ![![[113, 53], [22], [41, 133], [121], [117, 104], [22], [1]], ![[39, 96], [22], [128, 16], [121], [73, 45], [22], [1]]]
 h' := ![![[97, 148], [147, 65], [142, 52], [45, 122], [20, 138], [124, 113], [18, 97], [0, 1]], ![[0, 1], [45, 84], [120, 97], [108, 27], [145, 11], [59, 36], [40, 52], [97, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [47, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [131, 52, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2160, 2291, 1042]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-532, -635, 1042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-36, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-36, 1, 0]] 
 ![![149, 0, 0], ![113, 1, 0], ![115, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-36, 1, 0], ![0, -35, 2], ![280, 52, -37]]]
  hmulB := by decide  
  f := ![![![2773, -77, 0], ![11473, 0, 0]], ![![2089, -58, 0], ![8643, 0, 0]], ![![2147, -42, -1], ![8883, 75, 0]]]
  g := ![![![1, 0, 0], ![-113, 149, 0], ![-115, 0, 149]], ![![-1, 1, 0], ![25, -35, 2], ![-9, 52, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-75, -56, 1]] ![![149, 0, 0], ![-36, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-5364, 149, 0]], ![![-11175, -8344, 149], ![2980, 1937, -149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-36, 1, 0]]], ![![![-75, -56, 1]], ![![20, 13, -1]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [27, 37, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 123, 78], [92, 27, 73], [0, 1]]
 g := ![![[20, 113, 116], [135, 75, 68], [113, 69, 37], [119, 21], [20, 70, 144], [5, 1], []], ![[99, 7, 89, 136], [32, 82, 26, 38], [25, 21, 78, 97], [105, 99], [107, 37, 135, 116], [8, 125], [80, 44]], ![[78, 4, 140, 83], [115, 133, 130, 7], [107, 27, 107, 146], [134, 81], [46, 31, 71, 77], [70, 29], [85, 44]]]
 h' := ![![[64, 123, 78], [130, 132, 56], [120, 72, 81], [128, 104, 43], [64, 42, 126], [16, 90, 139], [0, 0, 1], [0, 1]], ![[92, 27, 73], [120, 4, 30], [125, 3, 102], [36, 134, 62], [105, 52, 34], [60, 117, 52], [124, 120, 27], [64, 123, 78]], ![[0, 1], [19, 15, 65], [130, 76, 119], [143, 64, 46], [99, 57, 142], [104, 95, 111], [129, 31, 123], [92, 27, 73]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 125], []]
 b := ![[], [112, 1, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [27, 37, 146, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![329331, -17214, 1510]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2181, -114, 10]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![3, 21, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![3, 21, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![3, 21, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![3, 21, 1], ![280, 76, 41], ![5600, 1206, 35]]]
  hmulB := by decide  
  f := ![![![-2, -21, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -21, 157]], ![![0, 0, 1], ![1, -5, 41], ![35, 3, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [110, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 156], [0, 1]]
 g := ![![[148, 10], [153], [58, 101], [9, 35], [102, 58], [106], [1]], ![[0, 147], [153], [39, 56], [119, 122], [60, 99], [106], [1]]]
 h' := ![![[48, 156], [78, 18], [57, 101], [109, 27], [84, 105], [126, 23], [47, 48], [0, 1]], ![[0, 1], [0, 139], [38, 56], [149, 130], [100, 52], [131, 134], [153, 109], [48, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [29, 110]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [110, 109, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1180, 3672, 758]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, -78, 758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-41, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-41, 1, 0]] 
 ![![157, 0, 0], ![116, 1, 0], ![122, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-41, 1, 0], ![0, -40, 2], ![280, 52, -42]]]
  hmulB := by decide  
  f := ![![![2748, -67, 0], ![10519, 0, 0]], ![![2010, -49, 0], ![7694, 0, 0]], ![![2138, -32, -1], ![8184, 79, 0]]]
  g := ![![![1, 0, 0], ![-116, 157, 0], ![-122, 0, 157]], ![![-1, 1, 0], ![28, -40, 2], ![-4, 52, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![3, 21, 1]] ![![157, 0, 0], ![-41, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-6437, 157, 0]], ![![471, 3297, 157], ![157, -785, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-41, 1, 0]]], ![![![3, 21, 1]], ![![1, -5, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-58, 29, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-58, 29, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![105, 29, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-58, 29, 1], ![280, 23, 57], ![7840, 1622, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-105, -29, 163]], ![![-1, 0, 1], ![-35, -10, 57], ![70, 16, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [161, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 162], [0, 1]]
 g := ![![[93, 81], [22, 77], [140], [151], [156], [34, 40], [1]], ![[0, 82], [0, 86], [140], [151], [156], [139, 123], [1]]]
 h' := ![![[23, 162], [44, 154], [31, 27], [136, 38], [46, 92], [68, 51], [2, 23], [0, 1]], ![[0, 1], [0, 9], [0, 136], [32, 125], [43, 71], [100, 112], [42, 140], [23, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [95]]
 b := ![[], [65, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [161, 140, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1001, 1374, 53]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-28, -1, 53]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-57, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-57, 1, 0]] 
 ![![163, 0, 0], ![106, 1, 0], ![34, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-57, 1, 0], ![0, -56, 2], ![280, 52, -58]]]
  hmulB := by decide  
  f := ![![![8722, -153, 0], ![24939, 0, 0]], ![![5758, -101, 0], ![16464, 0, 0]], ![![1834, -4, -1], ![5244, 82, 0]]]
  g := ![![![1, 0, 0], ![-106, 163, 0], ![-34, 0, 163]], ![![-1, 1, 0], ![36, -56, 2], ![-20, 52, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-58, 29, 1]] ![![163, 0, 0], ![-57, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-9291, 163, 0]], ![![-9454, 4727, 163], ![3586, -1630, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-57, 1, 0]]], ![![![-58, 29, 1]], ![![22, -10, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-112, 41, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-112, 41, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![55, 41, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-112, 41, 1], ![280, -19, 81], ![11200, 2246, -100]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -41, 167]], ![![-1, 0, 1], ![-25, -20, 81], ![100, 38, -100]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [119, 152, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 166], [0, 1]]
 g := ![![[136, 72], [103, 141], [71, 154], [48], [64], [139, 58], [1]], ![[47, 95], [47, 26], [43, 13], [48], [64], [7, 109], [1]]]
 h' := ![![[15, 166], [101, 78], [68, 108], [166, 34], [130, 86], [159, 159], [48, 15], [0, 1]], ![[0, 1], [102, 89], [18, 59], [8, 133], [84, 81], [39, 8], [106, 152], [15, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [137, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [119, 152, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![111992, 97434, 26567]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8079, -5939, 26567]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-81, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-81, 1, 0]] 
 ![![167, 0, 0], ![86, 1, 0], ![100, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-81, 1, 0], ![0, -80, 2], ![280, 52, -82]]]
  hmulB := by decide  
  f := ![![![8830, -109, 0], ![18203, 0, 0]], ![![4618, -57, 0], ![9520, 0, 0]], ![![5204, -24, -1], ![10728, 84, 0]]]
  g := ![![![1, 0, 0], ![-86, 167, 0], ![-100, 0, 167]], ![![-1, 1, 0], ![40, -80, 2], ![24, 52, -82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-112, 41, 1]] ![![167, 0, 0], ![-81, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-13527, 167, 0]], ![![-18704, 6847, 167], ![9352, -3340, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-81, 1, 0]]], ![![![-112, 41, 1]], ![![56, -20, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![51, 66, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![51, 66, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![51, 66, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![51, 66, 1], ![280, 169, 131], ![18200, 3546, 38]]]
  hmulB := by decide  
  f := ![![![-50, -66, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-51, -66, 173]], ![![0, 0, 1], ![-37, -49, 131], ![94, 6, 38]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [98, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [149, 172], [0, 1]]
 g := ![![[145, 49], [140], [20, 67], [121, 33], [113], [49, 57], [1]], ![[7, 124], [140], [142, 106], [21, 140], [113], [65, 116], [1]]]
 h' := ![![[149, 172], [82, 7], [116, 60], [79, 76], [32, 44], [42, 74], [75, 149], [0, 1]], ![[0, 1], [87, 166], [60, 113], [158, 97], [14, 129], [169, 99], [132, 24], [149, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [45, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [98, 24, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![915, 370, 79]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -28, 79]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![42, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![42, 1, 0]] 
 ![![173, 0, 0], ![42, 1, 0], ![135, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![42, 1, 0], ![0, 43, 2], ![280, 52, 41]]]
  hmulB := by decide  
  f := ![![![2311, 55, 0], ![-9515, 0, 0]], ![![546, 13, 0], ![-2248, 0, 0]], ![![1749, 20, -1], ![-7201, 87, 0]]]
  g := ![![![1, 0, 0], ![-42, 173, 0], ![-135, 0, 173]], ![![0, 1, 0], ![-12, 43, 2], ![-43, 52, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![51, 66, 1]] ![![173, 0, 0], ![42, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![7266, 173, 0]], ![![8823, 11418, 173], ![2422, 2941, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![42, 1, 0]]], ![![![51, 66, 1]], ![![14, 17, 1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![39, -90, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![39, -90, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![39, 89, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![39, -90, 1], ![280, 1, -181], ![-25480, -4566, 182]]]
  hmulB := by decide  
  f := ![![![-38, 90, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -89, 179]], ![![0, -1, 1], ![41, 90, -181], ![-182, -116, 182]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [23, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [158, 178], [0, 1]]
 g := ![![[141, 29], [74, 13], [85], [161], [43, 135], [118, 83], [1]], ![[69, 150], [159, 166], [85], [161], [72, 44], [165, 96], [1]]]
 h' := ![![[158, 178], [88, 108], [156, 152], [121, 62], [85, 55], [150, 80], [156, 158], [0, 1]], ![[0, 1], [147, 71], [7, 27], [72, 117], [4, 124], [81, 99], [60, 21], [158, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [62, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [23, 21, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1423, 4482, 1418]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-301, -680, 1418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![2, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![2, 1, 0]] 
 ![![179, 0, 0], ![2, 1, 0], ![176, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![2, 1, 0], ![0, 3, 2], ![280, 52, 1]]]
  hmulB := by decide  
  f := ![![![177, 88, 0], ![-15752, 0, 0]], ![![-2, -1, 0], ![180, 0, 0]], ![![172, 84, -1], ![-15306, 90, 0]]]
  g := ![![![1, 0, 0], ![-2, 179, 0], ![-176, 0, 179]], ![![0, 1, 0], ![-2, 3, 2], ![0, 52, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![39, -90, 1]] ![![179, 0, 0], ![2, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![358, 179, 0]], ![![6981, -16110, 179], ![358, -179, -179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![2, 1, 0]]], ![![![39, -90, 1]], ![![2, -1, -1]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [180, 112, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 59, 79], [95, 121, 102], [0, 1]]
 g := ![![[5, 28, 106], [65, 102], [51, 113, 87], [144, 168], [63, 79, 38], [114, 100, 1], []], ![[170, 17, 53, 14], [149, 33], [137, 168, 57, 14], [4, 49], [94, 165, 170, 180], [42, 7, 32, 49], [103, 87]], ![[95, 73, 151, 9], [3, 101], [15, 119, 62, 16], [19, 13], [39, 127, 15, 44], [9, 53, 78, 121], [80, 87]]]
 h' := ![![[5, 59, 79], [132, 171, 58], [51, 159, 37], [131, 153, 79], [63, 46, 118], [114, 2, 20], [0, 0, 1], [0, 1]], ![[95, 121, 102], [85, 11, 74], [152, 6, 24], [148, 56, 107], [12, 117, 174], [150, 138, 44], [128, 1, 121], [5, 59, 79]], ![[0, 1], [19, 180, 49], [177, 16, 120], [6, 153, 176], [63, 18, 70], [137, 41, 117], [55, 180, 59], [95, 121, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156, 32], []]
 b := ![[], [140, 137, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [180, 112, 81, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15012864, -4406264, -627708]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82944, -24344, -3468]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-94, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-94, 1, 0]] 
 ![![191, 0, 0], ![97, 1, 0], ![22, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-94, 1, 0], ![0, -93, 2], ![280, 52, -95]]]
  hmulB := by decide  
  f := ![![![9683, -103, 0], ![19673, 0, 0]], ![![5077, -54, 0], ![10315, 0, 0]], ![![1198, 34, -1], ![2434, 96, 0]]]
  g := ![![![1, 0, 0], ![-97, 191, 0], ![-22, 0, 191]], ![![-1, 1, 0], ![47, -93, 2], ![-14, 52, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-66, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-66, 1, 0]] 
 ![![191, 0, 0], ![125, 1, 0], ![147, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-66, 1, 0], ![0, -65, 2], ![280, 52, -67]]]
  hmulB := by decide  
  f := ![![![7855, -119, 0], ![22729, 0, 0]], ![![5149, -78, 0], ![14899, 0, 0]], ![![6051, -59, -1], ![17509, 96, 0]]]
  g := ![![![1, 0, 0], ![-125, 191, 0], ![-147, 0, 191]], ![![-1, 1, 0], ![41, -65, 2], ![19, 52, -67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-31, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-31, 1, 0]] 
 ![![191, 0, 0], ![160, 1, 0], ![108, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-31, 1, 0], ![0, -30, 2], ![280, 52, -32]]]
  hmulB := by decide  
  f := ![![![2078, -67, 0], ![12797, 0, 0]], ![![1768, -57, 0], ![10888, 0, 0]], ![![1212, -24, -1], ![7464, 96, 0]]]
  g := ![![![1, 0, 0], ![-160, 191, 0], ![-108, 0, 191]], ![![-1, 1, 0], ![24, -30, 2], ![-24, 52, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-94, 1, 0]] ![![191, 0, 0], ![-66, 1, 0]]
  ![![191, 0, 0], ![46, 16, 1]] where
 M := ![![![36481, 0, 0], ![-12606, 191, 0]], ![![-17954, 191, 0], ![6204, -159, 2]]]
 hmul := by decide  
 g := ![![![![145, -16, -1], ![191, 0, 0]], ![![-66, 1, 0], ![0, 0, 0]]], ![![![-94, 1, 0], ![0, 0, 0]], ![![-14, -17, -1], ![193, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![46, 16, 1]] ![![191, 0, 0], ![-31, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-5921, 191, 0]], ![![8786, 3056, 191], ![-1146, -382, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-31, 1, 0]]], ![![![46, 16, 1]], ![![-6, -2, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![38, -72, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![38, -72, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![38, 121, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![38, -72, 1], ![280, 18, -145], ![-20440, -3630, 163]]]
  hmulB := by decide  
  f := ![![![-37, 72, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-38, -121, 193]], ![![0, -1, 1], ![30, 91, -145], ![-138, -121, 163]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [53, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [161, 192], [0, 1]]
 g := ![![[88, 109], [25], [98], [170], [157], [36], [161, 1]], ![[74, 84], [25], [98], [170], [157], [36], [129, 192]]]
 h' := ![![[161, 192], [183, 130], [100, 188], [58, 22], [169, 39], [159, 93], [152, 6], [0, 1]], ![[0, 1], [76, 63], [67, 5], [126, 171], [79, 154], [78, 100], [153, 187], [161, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [115, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [53, 32, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![358, 114, 111]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -69, 111]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-48, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-48, 1, 0]] 
 ![![193, 0, 0], ![145, 1, 0], ![30, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-48, 1, 0], ![0, -47, 2], ![280, 52, -49]]]
  hmulB := by decide  
  f := ![![![9169, -191, 0], ![36863, 0, 0]], ![![6913, -144, 0], ![27793, 0, 0]], ![![1470, -7, -1], ![5910, 97, 0]]]
  g := ![![![1, 0, 0], ![-145, 193, 0], ![-30, 0, 193]], ![![-1, 1, 0], ![35, -47, 2], ![-30, 52, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![38, -72, 1]] ![![193, 0, 0], ![-48, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-9264, 193, 0]], ![![7334, -13896, 193], ![-1544, 3474, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-48, 1, 0]]], ![![![38, -72, 1]], ![![-8, 18, -1]]]]
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


lemma PB278I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB278I3 : PrimesBelowBoundCertificateInterval O 137 193 278 where
  m := 11
  g := ![1, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB278I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
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
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I149N1, I157N1, I163N1, I167N1, I173N1, I179N1, I191N0, I191N1, I191N2, I193N1]
  Il := ![[], [I149N1], [], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [], [I191N0, I191N1, I191N2], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
