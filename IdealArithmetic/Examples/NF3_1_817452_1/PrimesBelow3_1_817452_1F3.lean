
import IdealArithmetic.Examples.NF3_1_817452_1.RI3_1_817452_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [9, 34, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 114, 72], [36, 24, 67], [0, 1]]
 g := ![![[4, 59, 112], [48, 43, 41], [90, 20], [135, 47, 69], [56, 44], [0, 1], []], ![[11, 48, 63, 108], [97, 71, 121, 82], [105, 117], [37, 97, 31, 114], [112, 55], [109, 20], [14, 41]], ![[78, 23, 102, 16], [83, 85, 129, 13], [65, 71], [129, 116, 22, 1], [45, 127], [73, 69], [19, 41]]]
 h' := ![![[103, 114, 72], [124, 101, 23], [69, 92, 72], [36, 54, 24], [52, 63, 114], [0, 130, 105], [0, 0, 1], [0, 1]], ![[36, 24, 67], [46, 119, 40], [99, 18, 12], [40, 25, 16], [87, 126, 44], [20, 3, 65], [58, 121, 24], [103, 114, 72]], ![[0, 1], [28, 58, 76], [8, 29, 55], [68, 60, 99], [49, 89, 120], [68, 6, 108], [13, 18, 114], [36, 24, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 116], []]
 b := ![[], [27, 79, 37], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [9, 34, 0, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30441, -556, -556]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-219, -4, -4]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-54, 63, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-54, 63, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![95, 63, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-54, 63, 1], ![174, -54, 63], ![10962, 174, -54]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-95, -63, 149]], ![![-1, 0, 1], ![-39, -27, 63], ![108, 24, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [114, 12, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [137, 148], [0, 1]]
 g := ![![[55, 17], [22], [105, 16], [53], [8, 33], [144], [1]], ![[0, 132], [22], [62, 133], [53], [59, 116], [144], [1]]]
 h' := ![![[137, 148], [141, 49], [99, 52], [93, 4], [131, 65], [7, 114], [35, 137], [0, 1]], ![[0, 1], [0, 100], [71, 97], [45, 145], [96, 84], [129, 35], [30, 12], [137, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [86, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [114, 12, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1985, 1546, 34]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-35, -4, 34]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-63, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-63, 1, 0]] 
 ![![149, 0, 0], ![86, 1, 0], ![54, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-63, 1, 0], ![0, -63, 1], ![174, 0, -63]]]
  hmulB := by decide  
  f := ![![![8758, -139, 0], ![20711, 0, 0]], ![![5104, -81, 0], ![12070, 0, 0]], ![![3240, -51, 0], ![7662, 1, 0]]]
  g := ![![![1, 0, 0], ![-86, 149, 0], ![-54, 0, 149]], ![![-1, 1, 0], ![36, -63, 1], ![24, 0, -63]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-54, 63, 1]] ![![149, 0, 0], ![-63, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9387, 149, 0]], ![![-8046, 9387, 149], ![3576, -4023, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-63, 1, 0]]], ![![![-54, 63, 1]], ![![24, -27, 0]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [98, 126, 41, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 71, 9], [68, 79, 142], [0, 1]]
 g := ![![[129, 10, 58], [1, 129, 121], [79, 150, 64], [65, 88], [1, 125, 62], [110, 1], []], ![[94, 60, 30, 1], [32, 65, 128, 45], [111, 51, 33, 39], [], [35, 7, 136, 72], [30, 50], [71, 81]], ![[55, 23, 107, 54], [15, 83, 35, 92], [43, 33, 0, 28], [79, 88], [24, 58, 38, 48], [59, 58], [89, 81]]]
 h' := ![![[42, 71, 9], [53, 87, 71], [110, 2, 140], [63, 72, 143], [53, 14, 115], [92, 85, 45], [0, 0, 1], [0, 1]], ![[68, 79, 142], [51, 51, 50], [99, 66, 55], [94, 60, 16], [83, 4], [56, 100, 92], [91, 103, 79], [42, 71, 9]], ![[0, 1], [99, 13, 30], [24, 83, 107], [144, 19, 143], [100, 133, 36], [95, 117, 14], [130, 48, 71], [68, 79, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 61], []]
 b := ![[], [127, 45, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [98, 126, 41, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79728, -19630, -6795]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-528, -130, -45]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [96, 156, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [99, 84, 36], [61, 72, 121], [0, 1]]
 g := ![![[102, 80, 52], [80, 57], [73, 87, 140], [87, 47, 19], [36, 10, 100], [3, 1], []], ![[46, 76, 16, 100], [132, 117], [40, 154, 78, 40], [112, 127, 60, 118], [129, 60, 47, 71], [19, 3], [45, 40]], ![[68, 129, 79, 127], [118, 82], [21, 38, 64, 127], [99, 139, 23, 12], [52, 150, 113, 93], [66, 148], [117, 40]]]
 h' := ![![[99, 84, 36], [122, 149, 44], [57, 61, 34], [126, 132, 104], [155, 66, 126], [26, 64, 10], [0, 0, 1], [0, 1]], ![[61, 72, 121], [127, 55, 54], [125, 98, 91], [120, 18, 151], [58, 97, 144], [99, 139, 41], [143, 120, 72], [99, 84, 36]], ![[0, 1], [106, 110, 59], [75, 155, 32], [102, 7, 59], [109, 151, 44], [98, 111, 106], [25, 37, 84], [61, 72, 121]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 147], []]
 b := ![[], [91, 21, 9], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [96, 156, 154, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-980779, 244763, 3454]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6247, 1559, 22]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [132, 130, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 76, 135], [36, 86, 28], [0, 1]]
 g := ![![[104, 98, 16], [132, 54, 49], [110, 15], [89, 56], [36, 146], [33, 0, 1], []], ![[71, 121, 57, 135], [18, 38, 88, 115], [121, 146], [157, 121], [23, 90], [103, 96, 44, 85], [145, 132]], ![[118, 60, 133, 48], [53, 25, 156, 120], [78, 150], [32, 145], [149, 53], [77, 23, 73, 32], [89, 132]]]
 h' := ![![[127, 76, 135], [17, 110, 159], [33, 66, 156], [131, 147, 129], [44, 56, 43], [45, 111, 31], [0, 0, 1], [0, 1]], ![[36, 86, 28], [114, 119, 162], [152, 89, 158], [65, 48, 132], [96, 59, 11], [19, 54, 47], [86, 145, 86], [127, 76, 135]], ![[0, 1], [145, 97, 5], [104, 8, 12], [72, 131, 65], [59, 48, 109], [161, 161, 85], [143, 18, 76], [36, 86, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 141], []]
 b := ![[], [112, 119, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [132, 130, 0, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30318, -652, -652]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-186, -4, -4]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![6, 29, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![6, 29, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![6, 29, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![6, 29, 1], ![174, 6, 29], ![5046, 174, 6]]]
  hmulB := by decide  
  f := ![![![-5, -29, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-6, -29, 167]], ![![0, 0, 1], ![0, -5, 29], ![30, 0, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [10, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 166], [0, 1]]
 g := ![![[139, 81], [141, 115], [35, 49], [18], [21], [95, 77], [1]], ![[107, 86], [110, 52], [61, 118], [18], [21], [112, 90], [1]]]
 h' := ![![[113, 166], [93, 9], [151, 99], [108, 7], [156, 39], [52, 45], [157, 113], [0, 1]], ![[0, 1], [108, 158], [149, 68], [64, 160], [54, 128], [127, 122], [67, 54], [113, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [152, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [10, 54, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6677, 1238, 417]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![25, -65, 417]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-29, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-29, 1, 0]] 
 ![![167, 0, 0], ![138, 1, 0], ![161, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-29, 1, 0], ![0, -29, 1], ![174, 0, -29]]]
  hmulB := by decide  
  f := ![![![4409, -152, 0], ![25384, 0, 0]], ![![3626, -125, 0], ![20876, 0, 0]], ![![4269, -147, 0], ![24578, 1, 0]]]
  g := ![![![1, 0, 0], ![-138, 167, 0], ![-161, 0, 167]], ![![-1, 1, 0], ![23, -29, 1], ![29, 0, -29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![6, 29, 1]] ![![167, 0, 0], ![-29, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-4843, 167, 0]], ![![1002, 4843, 167], ![0, -835, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-29, 1, 0]]], ![![![6, 29, 1]], ![![0, -5, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, 1, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![1, 1, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![1, 1, 1]] where
  M :=![![![1, 1, 1], ![174, 1, 1], ![174, 174, 1]]]
  hmulB := by decide  
  f := ![![![-1, 1, 0]], ![![0, -1, 1]], ![![1, 0, 0]]]
  g := ![![![0, 0, 1], ![1, 0, 1], ![1, 1, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [16, 4, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [169, 172], [0, 1]]
 g := ![![[130, 119], [119], [], [84, 152], [142], [64, 16], [1]], ![[0, 54], [119], [], [168, 21], [142], [0, 157], [1]]]
 h' := ![![[169, 172], [172, 43], [0, 43], [40], [0, 49], [14, 90], [157, 169], [0, 1]], ![[0, 1], [0, 130], [1, 130], [40], [150, 124], [0, 83], [0, 4], [169, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [101, 137]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [16, 4, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1031, 180, 7]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, 1, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![173, 0, 0], ![172, 1, 0], ![172, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 1], ![174, 0, -1]]]
  hmulB := by decide  
  f := ![![![1, 1, 1]], ![![2, 1, 1]], ![![2, 2, 1]]]
  g := ![![![-1, 1, 0], ![0, -1, 1], ![2, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![1, 1, 1]] ![![-1, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-8, 23, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-8, 23, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![171, 23, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-8, 23, 1], ![174, -8, 23], ![4002, 174, -8]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-171, -23, 179]], ![![-1, 0, 1], ![-21, -3, 23], ![30, 2, -8]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [79, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 178], [0, 1]]
 g := ![![[59, 156], [148, 3], [22], [64], [50, 172], [47, 49], [1]], ![[41, 23], [127, 176], [22], [64], [99, 7], [62, 130], [1]]]
 h' := ![![[172, 178], [122, 48], [28, 19], [100, 102], [167, 171], [46, 72], [100, 172], [0, 1]], ![[0, 1], [144, 131], [74, 160], [102, 77], [44, 8], [79, 107], [149, 7], [172, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [57]]
 b := ![[], [55, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [79, 7, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![775, 703, 15]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10, 2, 15]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-23, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-23, 1, 0]] 
 ![![179, 0, 0], ![156, 1, 0], ![8, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-23, 1, 0], ![0, -23, 1], ![174, 0, -23]]]
  hmulB := by decide  
  f := ![![![2784, -121, 0], ![21659, 0, 0]], ![![2416, -105, 0], ![18796, 0, 0]], ![![164, -7, 0], ![1276, 1, 0]]]
  g := ![![![1, 0, 0], ![-156, 179, 0], ![-8, 0, 179]], ![![-1, 1, 0], ![20, -23, 1], ![2, 0, -23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-8, 23, 1]] ![![179, 0, 0], ![-23, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-4117, 179, 0]], ![![-1432, 4117, 179], ![358, -537, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-23, 1, 0]]], ![![![-8, 23, 1]], ![![2, -3, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![32, 1, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![32, 1, 0]] 
 ![![181, 0, 0], ![32, 1, 0], ![62, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![32, 1, 0], ![0, 32, 1], ![174, 0, 32]]]
  hmulB := by decide  
  f := ![![![481, 15, 0], ![-2715, 0, 0]], ![![32, 1, 0], ![-180, 0, 0]], ![![134, 4, 0], ![-756, 1, 0]]]
  g := ![![![1, 0, 0], ![-32, 181, 0], ![-62, 0, 181]], ![![0, 1, 0], ![-6, 32, 1], ![-10, 0, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N0 : Nat.card (O ⧸ I181N0) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N0)

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := prime_ideal_of_norm_prime hp181.out _ NI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![61, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![61, 1, 0]] 
 ![![181, 0, 0], ![61, 1, 0], ![80, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![61, 1, 0], ![0, 61, 1], ![174, 0, 61]]]
  hmulB := by decide  
  f := ![![![3783, 62, 0], ![-11222, 0, 0]], ![![1281, 21, 0], ![-3800, 0, 0]], ![![1668, 27, 0], ![-4948, 1, 0]]]
  g := ![![![1, 0, 0], ![-61, 181, 0], ![-80, 0, 181]], ![![0, 1, 0], ![-21, 61, 1], ![-26, 0, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![88, 1, 0]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![181, 0, 0], ![88, 1, 0]] 
 ![![181, 0, 0], ![88, 1, 0], ![39, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![88, 1, 0], ![0, 88, 1], ![174, 0, 88]]]
  hmulB := by decide  
  f := ![![![4225, 48, 0], ![-8688, 0, 0]], ![![2024, 23, 0], ![-4162, 0, 0]], ![![923, 10, 0], ![-1898, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 181, 0], ![-39, 0, 181]], ![![0, 1, 0], ![-43, 88, 1], ![-18, 0, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![32, 1, 0]] ![![181, 0, 0], ![61, 1, 0]]
  ![![181, 0, 0], ![-39, -88, 1]] where
 M := ![![![32761, 0, 0], ![11041, 181, 0]], ![![5792, 181, 0], ![1952, 93, 1]]]
 hmul := by decide  
 g := ![![![![181, 0, 0], ![0, 0, 0]], ![![61, 1, 0], ![0, 0, 0]]], ![![![32, 1, 0], ![0, 0, 0]], ![![11, 1, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-39, -88, 1]] ![![181, 0, 0], ![88, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![15928, 181, 0]], ![![-7059, -15928, 181], ![-3258, -7783, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![88, 1, 0]]], ![![![-39, -88, 1]], ![![-18, -43, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-21, 19, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-21, 19, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![170, 19, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-21, 19, 1], ![174, -21, 19], ![3306, 174, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-170, -19, 191]], ![![-1, 0, 1], ![-16, -2, 19], ![36, 3, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [174, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [45, 190], [0, 1]]
 g := ![![[115, 50], [63, 78], [50, 72], [147, 104], [153, 104], [20, 115], [1]], ![[73, 141], [135, 113], [43, 119], [52, 87], [58, 87], [38, 76], [1]]]
 h' := ![![[45, 190], [116, 97], [86, 101], [16, 151], [118, 103], [149, 88], [17, 45], [0, 1]], ![[0, 1], [88, 94], [47, 90], [126, 40], [169, 88], [98, 103], [132, 146], [45, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96]]
 b := ![[], [66, 48]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [174, 146, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6490, -804, 400]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-390, -44, 400]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-19, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-19, 1, 0]] 
 ![![191, 0, 0], ![172, 1, 0], ![21, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-19, 1, 0], ![0, -19, 1], ![174, 0, -19]]]
  hmulB := by decide  
  f := ![![![3478, -183, 0], ![34953, 0, 0]], ![![3136, -165, 0], ![31516, 0, 0]], ![![420, -22, 0], ![4221, 1, 0]]]
  g := ![![![1, 0, 0], ![-172, 191, 0], ![-21, 0, 191]], ![![-1, 1, 0], ![17, -19, 1], ![3, 0, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-21, 19, 1]] ![![191, 0, 0], ![-19, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-3629, 191, 0]], ![![-4011, 3629, 191], ![573, -382, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-19, 1, 0]]], ![![![-21, 19, 1]], ![![3, -2, 0]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [94, 64, 154, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [154, 144, 63], [78, 48, 130], [0, 1]]
 g := ![![[23, 84, 162], [88, 179], [185, 65], [80, 7], [103, 12], [94, 170], [1]], ![[4, 174, 161, 85], [149, 124], [73, 108], [125, 109], [6, 8], [150, 18], [53, 167, 118, 112]], ![[8, 83, 9, 169], [96, 108], [156, 25], [71, 16], [79, 179], [175, 4], [33, 24, 134, 81]]]
 h' := ![![[154, 144, 63], [21, 2, 82], [90, 39, 117], [66, 12, 79], [161, 0, 134], [0, 72, 165], [99, 129, 39], [0, 1]], ![[78, 48, 130], [71, 151, 9], [145, 33, 160], [32, 12, 109], [3, 148, 63], [48, 134, 104], [161, 117, 156], [154, 144, 63]], ![[0, 1], [19, 40, 102], [101, 121, 109], [26, 169, 5], [157, 45, 189], [40, 180, 117], [144, 140, 191], [78, 48, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [159, 147], []]
 b := ![[], [17, 153, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [94, 64, 154, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7913, 29529, 4246]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-41, 153, 22]
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



lemma PB256I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB256I3 : PrimesBelowBoundCertificateInterval O 137 193 256 where
  m := 11
  g := ![1, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB256I3_primes
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
    · exact ![I181N0, I181N1, I181N2]
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
    · exact ![181, 181, 181]
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
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I167N1, I173N1, I179N1, I181N0, I181N1, I181N2, I191N1]
  Il := ![[], [I149N1], [], [], [], [I167N1], [I173N1], [I179N1], [I181N0, I181N1, I181N2], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
