
import IdealArithmetic.Examples.NF3_1_565068_1.RI3_1_565068_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [117, 102, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [9, 39, 65], [94, 99, 74], [0, 1]]
 g := ![![[32, 105, 42], [39, 101, 52], [55, 29], [53, 57, 71], [128, 52], [103, 1], []], ![[129, 77, 80, 1], [130, 10, 128, 30], [120, 28], [84, 84, 0, 112], [4, 120], [103, 71], [32, 55]], ![[15, 23, 34, 105], [105, 138, 95, 15], [37, 89], [40, 123, 94, 26], [132, 78], [104, 131], [23, 55]]]
 h' := ![![[9, 39, 65], [24, 41, 96], [95, 40, 82], [54, 67, 86], [132, 90, 40], [42, 80, 82], [0, 0, 1], [0, 1]], ![[94, 99, 74], [137, 104, 76], [51, 89, 15], [57, 43, 81], [94, 26, 80], [80, 120, 113], [90, 38, 99], [9, 39, 65]], ![[0, 1], [129, 133, 106], [117, 10, 42], [89, 29, 111], [22, 23, 19], [71, 78, 83], [29, 101, 39], [94, 99, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 94], []]
 b := ![[], [55, 66, 129], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [117, 102, 36, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-769365, -844008, -666922]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5535, -6072, -4798]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![11, -55, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![11, -55, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![11, 94, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![11, -55, 1], ![-45, -73, -275], ![2484, 1586, -18]]]
  hmulB := by decide  
  f := ![![![-10, 55, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -94, 149]], ![![0, -1, 1], ![20, 173, -275], ![18, 22, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [124, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 148], [0, 1]]
 g := ![![[113, 143], [36], [105, 129], [37], [129, 142], [36], [1]], ![[0, 6], [36], [76, 20], [37], [22, 7], [36], [1]]]
 h' := ![![[143, 148], [126, 21], [92, 143], [9, 24], [96, 127], [35, 80], [25, 143], [0, 1]], ![[0, 1], [0, 128], [128, 6], [14, 125], [79, 22], [2, 69], [61, 6], [143, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [138, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [124, 6, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-70, -842, -1388]
  a := ![-1, 1, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![102, 870, -1388]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-23, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-23, 1, 0]] 
 ![![149, 0, 0], ![126, 1, 0], ![18, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-23, 1, 0], ![0, -22, 5], ![-45, -29, -23]]]
  hmulB := by decide  
  f := ![![![714, -31, 0], ![4619, 0, 0]], ![![576, -25, 0], ![3726, 0, 0]], ![![102, 0, -1], ![660, 30, 0]]]
  g := ![![![1, 0, 0], ![-126, 149, 0], ![-18, 0, 149]], ![![-1, 1, 0], ![18, -22, 5], ![27, -29, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![11, -55, 1]] ![![149, 0, 0], ![-23, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-3427, 149, 0]], ![![1639, -8195, 149], ![-298, 1192, -298]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-23, 1, 0]]], ![![![11, -55, 1]], ![![-2, 8, -2]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [121, 109, 134, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 116, 135], [139, 34, 16], [0, 1]]
 g := ![![[6, 87, 47], [31, 53, 5], [149, 91, 118], [96, 38], [58, 69, 86], [17, 1], []], ![[129, 133, 104, 70], [121, 20, 142, 53], [67, 95, 97, 113], [52, 8], [70, 59, 102, 119], [63, 99], [36, 105]], ![[127, 87, 64, 40], [146, 12, 40, 69], [67, 110, 125, 91], [3, 105], [0, 49, 41, 94], [7, 17], [4, 105]]]
 h' := ![![[29, 116, 135], [24, 150, 54], [91, 25, 96], [61, 114, 32], [79, 54, 76], [57, 140, 29], [0, 0, 1], [0, 1]], ![[139, 34, 16], [143, 72, 40], [106, 80, 146], [60, 53, 19], [114, 30, 59], [30, 5, 105], [109, 65, 34], [29, 116, 135]], ![[0, 1], [98, 80, 57], [69, 46, 60], [44, 135, 100], [16, 67, 16], [144, 6, 17], [113, 86, 116], [139, 34, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 25], []]
 b := ![[], [29, 92, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [121, 109, 134, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![279199, 0, 5587]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1849, 0, 37]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [107, 140, 146, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 17, 136], [136, 139, 21], [0, 1]]
 g := ![![[76, 148, 117], [104, 90], [104, 47, 12], [87, 118, 127], [151, 146, 47], [11, 1], []], ![[26, 74, 25, 125], [105, 36], [152, 19, 62, 152], [61, 115, 2, 91], [0, 52, 17, 96], [122, 10], [55, 127]], ![[143, 70, 80, 129], [20, 106], [110, 95, 33, 96], [3, 17, 153, 74], [94, 49, 147, 73], [155, 132], [13, 127]]]
 h' := ![![[32, 17, 136], [66, 124, 91], [19, 111, 54], [111, 39, 13], [14, 94, 136], [79, 80, 138], [0, 0, 1], [0, 1]], ![[136, 139, 21], [27, 89, 154], [127, 142, 151], [24, 83, 46], [70, 35, 131], [13, 58, 75], [6, 52, 139], [32, 17, 136]], ![[0, 1], [31, 101, 69], [82, 61, 109], [130, 35, 98], [92, 28, 47], [121, 19, 101], [149, 105, 17], [136, 139, 21]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 37], []]
 b := ![[], [87, 22, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [107, 140, 146, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1269659, -1647087, -1604226]
  a := ![1, -2, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8087, -10491, -10218]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [83, 116, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 137, 107], [162, 25, 56], [0, 1]]
 g := ![![[33, 34, 134], [93, 18, 161], [100, 97], [34, 46], [18, 158], [30, 31, 1], []], ![[21, 16, 7, 101], [58, 35, 36, 162], [70, 14], [42, 95], [129, 121], [60, 12, 28, 45], [46, 39]], ![[19, 70, 12, 4], [65, 33, 58, 134], [54, 26], [109, 34], [43, 121], [32, 155, 158, 40], [97, 39]]]
 h' := ![![[32, 137, 107], [105, 145, 42], [56, 34, 145], [83, 96, 74], [42, 144, 131], [118, 141, 22], [0, 0, 1], [0, 1]], ![[162, 25, 56], [30, 19, 102], [91, 7, 91], [149, 35, 60], [7, 122, 101], [49, 135, 152], [140, 32, 25], [32, 137, 107]], ![[0, 1], [85, 162, 19], [15, 122, 90], [52, 32, 29], [121, 60, 94], [58, 50, 152], [100, 131, 137], [162, 25, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12, 127], []]
 b := ![[], [137, 140, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [83, 116, 132, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-854935, -1013860, -890632]
  a := ![0, -2, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5245, -6220, -5464]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-35, -57, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-35, -57, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![132, 110, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-35, -57, 1], ![-45, -121, -285], ![2574, 1644, -64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-132, -110, 167]], ![![-1, -1, 1], ![225, 187, -285], ![66, 52, -64]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [94, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [29, 166], [0, 1]]
 g := ![![[37, 16], [19, 122], [14, 124], [62], [1], [66, 6], [1]], ![[0, 151], [50, 45], [103, 43], [62], [1], [73, 161], [1]]]
 h' := ![![[29, 166], [51, 4], [20, 150], [82, 25], [30, 79], [142, 166], [73, 29], [0, 1]], ![[0, 1], [0, 163], [28, 17], [139, 142], [150, 88], [113, 1], [79, 138], [29, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [143, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [94, 138, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-86518, -149809, -176929]
  a := ![1, 20, 81]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![139330, 115643, -176929]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-49, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-49, 1, 0]] 
 ![![167, 0, 0], ![118, 1, 0], ![64, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-49, 1, 0], ![0, -48, 5], ![-45, -29, -49]]]
  hmulB := by decide  
  f := ![![![4950, -101, 0], ![16867, 0, 0]], ![![3480, -71, 0], ![11858, 0, 0]], ![![1924, -20, -2], ![6556, 67, 0]]]
  g := ![![![1, 0, 0], ![-118, 167, 0], ![-64, 0, 167]], ![![-1, 1, 0], ![32, -48, 5], ![39, -29, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-35, -57, 1]] ![![167, 0, 0], ![-49, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-8183, 167, 0]], ![![-5845, -9519, 167], ![1670, 2672, -334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-49, 1, 0]]], ![![![-35, -57, 1]], ![![10, 16, -2]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![64, 35, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![64, 35, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![64, 35, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![64, 35, 1], ![-45, 70, 175], ![-1566, -1024, 35]]]
  hmulB := by decide  
  f := ![![![-63, -35, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -35, 173]], ![![0, 0, 1], ![-65, -35, 175], ![-22, -13, 35]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [40, 136, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 172], [0, 1]]
 g := ![![[38, 13], [163], [12, 31], [170, 60], [64], [118, 158], [1]], ![[0, 160], [163], [121, 142], [141, 113], [64], [82, 15], [1]]]
 h' := ![![[37, 172], [18, 79], [39, 110], [120, 107], [14, 38], [124, 165], [133, 37], [0, 1]], ![[0, 1], [0, 94], [130, 63], [100, 66], [36, 135], [1, 8], [118, 136], [37, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [68, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [40, 136, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-914, -981, -463]
  a := ![-1, 2, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![166, 88, -463]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-2, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-2, 1, 0]] 
 ![![173, 0, 0], ![171, 1, 0], ![138, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-2, 1, 0], ![0, -1, 5], ![-45, -29, -2]]]
  hmulB := by decide  
  f := ![![![3, 85, -430], ![173, 14878, 0]], ![![1, 85, -425], ![1, 14705, 0]], ![![2, 68, -343], ![104, 11868, 0]]]
  g := ![![![1, 0, 0], ![-171, 173, 0], ![-138, 0, 173]], ![![-1, 1, 0], ![-3, -1, 5], ![30, -29, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![64, 35, 1]] ![![173, 0, 0], ![-2, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-346, 173, 0]], ![![11072, 6055, 173], ![-173, 0, 173]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-2, 1, 0]]], ![![![64, 35, 1]], ![![-1, 0, 1]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-6, -88, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-6, -88, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![173, 91, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-6, -88, 1], ![-45, -123, -440], ![3969, 2543, -35]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-173, -91, 179]], ![![-1, -1, 1], ![425, 223, -440], ![56, 32, -35]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [4, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 178], [0, 1]]
 g := ![![[63, 45], [121, 68], [125], [77], [170, 70], [176, 138], [1]], ![[0, 134], [169, 111], [125], [77], [72, 109], [126, 41], [1]]]
 h' := ![![[106, 178], [53, 89], [94, 28], [93, 29], [36, 163], [12, 41], [175, 106], [0, 1]], ![[0, 1], [0, 90], [19, 151], [124, 150], [130, 16], [62, 138], [134, 73], [106, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88]]
 b := ![[], [174, 44]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [4, 73, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2012, -3972, -4617]
  a := ![0, 3, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4451, 2325, -4617]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![82, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![82, 1, 0]] 
 ![![179, 0, 0], ![82, 1, 0], ![35, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![82, 1, 0], ![0, 83, 5], ![-45, -29, 82]]]
  hmulB := by decide  
  f := ![![![6643, 81, 0], ![-14499, 0, 0]], ![![3034, 37, 0], ![-6622, 0, 0]], ![![1287, -1, -1], ![-2809, 36, 0]]]
  g := ![![![1, 0, 0], ![-82, 179, 0], ![-35, 0, 179]], ![![0, 1, 0], ![-39, 83, 5], ![-3, -29, 82]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-6, -88, 1]] ![![179, 0, 0], ![82, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![14678, 179, 0]], ![![-1074, -15752, 179], ![-537, -7339, -358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![82, 1, 0]]], ![![![-6, -88, 1]], ![![-3, -41, -2]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [124, 33, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [76, 59, 50], [33, 121, 131], [0, 1]]
 g := ![![[122, 160, 172], [152, 43], [69, 155, 9], [67, 119], [140, 51, 137], [83, 109, 1], []], ![[157, 81, 100, 109], [84, 55], [90, 139, 65, 54], [144, 100], [112, 88, 115, 134], [179, 158, 162, 86], [22, 147]], ![[89, 146, 100, 158], [17, 49], [68, 12, 99, 72], [89, 122], [128, 133, 178, 61], [58, 127, 170, 72], [122, 147]]]
 h' := ![![[76, 59, 50], [24, 37, 57], [132, 3, 119], [93, 164, 3], [16, 179, 149], [25, 35, 77], [0, 0, 1], [0, 1]], ![[33, 121, 131], [97, 54, 59], [167, 108, 69], [162, 171, 56], [68, 150, 10], [90, 40, 26], [152, 150, 121], [76, 59, 50]], ![[0, 1], [137, 90, 65], [39, 70, 174], [131, 27, 122], [137, 33, 22], [23, 106, 78], [79, 31, 59], [33, 121, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98, 109], []]
 b := ![[], [114, 107, 139], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [124, 33, 72, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-33013314, -33474864, -23166190]
  a := ![2, -8, -30]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-182394, -184944, -127990]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-18, -95, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-18, -95, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![173, 96, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-18, -95, 1], ![-45, -142, -475], ![4284, 2746, -47]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-173, -96, 191]], ![![-1, -1, 1], ![430, 238, -475], ![65, 38, -47]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [150, 176, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 190], [0, 1]]
 g := ![![[19, 177], [26, 108], [43, 109], [100, 85], [36, 12], [21, 34], [1]], ![[0, 14], [118, 83], [150, 82], [38, 106], [25, 179], [149, 157], [1]]]
 h' := ![![[15, 190], [111, 69], [44, 47], [89, 49], [139, 127], [97, 143], [41, 15], [0, 1]], ![[0, 1], [0, 122], [176, 144], [60, 142], [134, 64], [141, 48], [75, 176], [15, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [84, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [150, 176, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2616, -9, 173]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-143, -87, 173]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![93, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![93, 1, 0]] 
 ![![191, 0, 0], ![93, 1, 0], ![47, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![93, 1, 0], ![0, 94, 5], ![-45, -29, 93]]]
  hmulB := by decide  
  f := ![![![5209, 56, 0], ![-10696, 0, 0]], ![![2511, 27, 0], ![-5156, 0, 0]], ![![1237, -62, -4], ![-2540, 153, 0]]]
  g := ![![![1, 0, 0], ![-93, 191, 0], ![-47, 0, 191]], ![![0, 1, 0], ![-47, 94, 5], ![-9, -29, 93]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-18, -95, 1]] ![![191, 0, 0], ![93, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![17763, 191, 0]], ![![-3438, -18145, 191], ![-1719, -8977, -382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![93, 1, 0]]], ![![![-18, -95, 1]], ![![-9, -47, -2]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [120, 26, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [123, 161, 137], [128, 31, 56], [0, 1]]
 g := ![![[81, 50, 63], [39, 43], [27, 93], [64, 3], [34, 175], [61, 83], [1]], ![[68, 52, 185, 93], [12, 27], [30, 72], [53, 28], [143, 100], [34, 150], [73, 147, 64, 14]], ![[136, 74, 189, 92], [39, 98], [86, 192], [90, 8], [169, 165], [7, 189], [47, 77, 178, 179]]]
 h' := ![![[123, 161, 137], [136, 8, 16], [50, 112, 64], [190, 63, 155], [27, 128, 179], [132, 98, 102], [73, 167, 58], [0, 1]], ![[128, 31, 56], [187, 138, 48], [58, 115, 151], [143, 88, 119], [110, 143, 118], [38, 3, 183], [79, 89, 166], [123, 161, 137]], ![[0, 1], [80, 47, 129], [30, 159, 171], [11, 42, 112], [179, 115, 89], [1, 92, 101], [164, 130, 162], [128, 31, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 98], []]
 b := ![[], [176, 45, 50], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [120, 26, 135, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-10694130, -11649094, -9100336]
  a := ![1, -5, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55410, -60358, -47152]
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



lemma PB213I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB213I3 : PrimesBelowBoundCertificateInterval O 137 193 213 where
  m := 11
  g := ![1, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB213I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
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
    · exact ![3442951]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![27889, 167]
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
  β := ![I149N1, I167N1, I173N1, I179N1, I191N1]
  Il := ![[], [I149N1], [], [], [], [I167N1], [I173N1], [I179N1], [], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
