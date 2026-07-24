
import IdealArithmetic.Examples.NF3_1_703404_2.RI3_1_703404_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-2, 8, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-2, 8, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![137, 8, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-2, 8, 1], ![262, 64, 8], ![2096, 790, 64]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-137, -8, 139]], ![![-1, 0, 1], ![-6, 0, 8], ![-48, 2, 64]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [18, 60, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 138], [0, 1]]
 g := ![![[96, 30], [110, 79], [117], [110, 127], [28], [125], [1]], ![[103, 109], [96, 60], [117], [135, 12], [28], [125], [1]]]
 h' := ![![[79, 138], [105, 13], [23, 45], [105, 123], [35, 31], [20, 81], [121, 79], [0, 1]], ![[0, 1], [20, 126], [103, 94], [92, 16], [121, 108], [25, 58], [107, 60], [79, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [130, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [18, 60, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![542, 334, 7]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, 2, 7]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-8, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-8, 1, 0]] 
 ![![139, 0, 0], ![131, 1, 0], ![75, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-8, 1, 0], ![0, -8, 1], ![262, 66, -8]]]
  hmulB := by decide  
  f := ![![![729, -91, 0], ![12649, 0, 0]], ![![689, -86, 0], ![11955, 0, 0]], ![![393, -49, 0], ![6819, 1, 0]]]
  g := ![![![1, 0, 0], ![-131, 139, 0], ![-75, 0, 139]], ![![-1, 1, 0], ![7, -8, 1], ![-56, 66, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-2, 8, 1]] ![![139, 0, 0], ![-8, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-1112, 139, 0]], ![![-278, 1112, 139], ![278, 0, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-8, 1, 0]]], ![![![-2, 8, 1]], ![![2, 0, 0]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [89, 104, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [140, 79, 100], [104, 69, 49], [0, 1]]
 g := ![![[52, 132, 76], [12, 42], [133, 148, 82], [50, 1], [59, 89, 63], [95, 1], []], ![[3, 109, 141, 140], [39, 4], [119, 91, 121, 17], [46, 85], [28, 110, 11, 16], [2, 142], [131, 17]], ![[93, 102, 144, 123], [97, 61], [37, 134, 31, 19], [10, 45], [64, 0, 63, 61], [55, 132], [33, 17]]]
 h' := ![![[140, 79, 100], [10, 127, 134], [83, 143, 108], [124, 56, 126], [113, 52, 1], [38, 14, 130], [0, 0, 1], [0, 1]], ![[104, 69, 49], [144, 52, 43], [121, 48, 147], [98, 116, 139], [136, 65, 54], [119, 145, 89], [44, 129, 69], [140, 79, 100]], ![[0, 1], [78, 119, 121], [48, 107, 43], [104, 126, 33], [139, 32, 94], [48, 139, 79], [131, 20, 79], [104, 69, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 50], []]
 b := ![[], [141, 26, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [89, 104, 54, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![757218, 787316, 136335]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5082, 5284, 915]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [69, 134, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 65, 52], [132, 85, 99], [0, 1]]
 g := ![![[46, 18, 19], [4, 82, 139], [137, 95, 69], [50, 127], [42, 102, 39], [129, 1], []], ![[98, 95, 111, 126], [64, 3, 76, 107], [22, 77, 33, 150], [90, 68], [130, 79, 20, 63], [120, 128], [122, 137]], ![[109, 103, 46, 110], [101, 55, 10, 10], [47, 115, 42, 49], [98, 100], [90, 12, 75, 148], [148, 148], [75, 137]]]
 h' := ![![[148, 65, 52], [26, 124, 87], [60, 105, 130], [109, 15, 89], [122, 82, 91], [8, 10, 48], [0, 0, 1], [0, 1]], ![[132, 85, 99], [119, 30, 102], [117, 99, 51], [19, 57, 40], [76, 48, 70], [120, 104, 70], [47, 83, 85], [148, 65, 52]], ![[0, 1], [142, 148, 113], [103, 98, 121], [67, 79, 22], [51, 21, 141], [78, 37, 33], [18, 68, 65], [132, 85, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [0, 129], []]
 b := ![[], [50, 7, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [69, 134, 22, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-107965, -34730, -24764]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-715, -230, -164]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [129, 44, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 48, 141], [41, 108, 16], [0, 1]]
 g := ![![[63, 146, 93], [67, 13], [55, 152, 146], [45, 66, 49], [32, 109, 138], [78, 1], []], ![[34, 146, 148, 12], [14, 86], [36, 64, 107, 122], [141, 85, 72, 138], [124, 4, 97, 44], [107, 46], [63, 99]], ![[71, 92, 134, 110], [136, 4], [116, 126, 107, 13], [124, 78, 151, 27], [18, 96, 22, 47], [116, 106], [31, 99]]]
 h' := ![![[37, 48, 141], [107, 121, 90], [127, 125, 135], [4, 100, 60], [111, 113, 7], [143, 50, 74], [0, 0, 1], [0, 1]], ![[41, 108, 16], [29, 27, 91], [39, 76, 20], [144, 4, 13], [4, 144, 47], [62, 75, 127], [150, 98, 108], [37, 48, 141]], ![[0, 1], [77, 9, 133], [42, 113, 2], [44, 53, 84], [136, 57, 103], [64, 32, 113], [37, 59, 48], [41, 108, 16]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 147], []]
 b := ![[], [90, 78, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [129, 44, 79, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1514893, -657359, -62957]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9649, -4187, -401]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [106, 81, 132, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [14, 85, 145], [17, 77, 18], [0, 1]]
 g := ![![[46, 87, 34], [42, 125, 161], [23, 90], [141, 121], [73, 55], [65, 31, 1], []], ![[148, 126, 95, 150], [109, 121, 155, 146], [108, 156], [64, 158], [159, 93], [112, 2, 108, 43], [138, 161]], ![[145, 157, 156, 29], [131, 35, 32, 27], [123, 16], [30, 111], [94, 15], [61, 105, 82, 139], [102, 161]]]
 h' := ![![[14, 85, 145], [112, 20, 94], [32, 108, 145], [5, 59, 47], [66, 73, 11], [119, 88, 50], [0, 0, 1], [0, 1]], ![[17, 77, 18], [107, 162, 32], [31, 76, 93], [118, 8, 112], [120, 105, 22], [48, 24, 147], [75, 53, 77], [14, 85, 145]], ![[0, 1], [48, 144, 37], [83, 142, 88], [154, 96, 4], [143, 148, 130], [162, 51, 129], [72, 110, 85], [17, 77, 18]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66, 115], []]
 b := ![[], [1, 92, 106], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [106, 81, 132, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-51508, 3423, 3423]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-316, 21, 21]
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


def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![64, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![64, 1, 0]] 
 ![![167, 0, 0], ![64, 1, 0], ![79, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![64, 1, 0], ![0, 64, 1], ![262, 66, 64]]]
  hmulB := by decide  
  f := ![![![3905, 61, 0], ![-10187, 0, 0]], ![![1472, 23, 0], ![-3840, 0, 0]], ![![1753, 27, 0], ![-4573, 1, 0]]]
  g := ![![![1, 0, 0], ![-64, 167, 0], ![-79, 0, 167]], ![![0, 1, 0], ![-25, 64, 1], ![-54, 66, 64]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-32, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-32, 1, 0]] 
 ![![167, 0, 0], ![135, 1, 0], ![145, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-32, 1, 0], ![0, -32, 1], ![262, 66, -32]]]
  hmulB := by decide  
  f := ![![![1953, -61, 0], ![10187, 0, 0]], ![![1601, -50, 0], ![8351, 0, 0]], ![![1703, -53, 0], ![8883, 1, 0]]]
  g := ![![![1, 0, 0], ![-135, 167, 0], ![-145, 0, 167]], ![![-1, 1, 0], ![25, -32, 1], ![-24, 66, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![64, 1, 0]] ![![167, 0, 0], ![-32, 1, 0]]
  ![![167, 0, 0], ![-44, 32, 1]] where
 M := ![![![27889, 0, 0], ![-5344, 167, 0]], ![![10688, 167, 0], ![-2048, 32, 1]]]
 hmul := by decide  
 g := ![![![![167, 0, 0], ![0, 0, 0]], ![![12, -31, -1], ![167, 0, 0]]], ![![![64, 1, 0], ![0, 0, 0]], ![![32, -32, -1], ![168, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-44, 32, 1]] ![![167, 0, 0], ![-32, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-5344, 167, 0]], ![![-7348, 5344, 167], ![1670, -1002, 0]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-32, 1, 0]]], ![![![-44, 32, 1]], ![![10, -6, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [141, 117, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [143, 73, 115], [165, 99, 58], [0, 1]]
 g := ![![[118, 72, 139], [170, 51], [4, 98, 126], [133, 22, 135], [92, 56], [116, 135, 1], []], ![[77, 57, 117, 128], [129, 124], [171, 120, 38, 153], [69, 133, 78, 75], [150, 54], [83, 61, 88, 20], [24, 77]], ![[64, 31, 166, 155], [149, 113], [147, 14, 134, 127], [36, 106, 155, 42], [12, 78], [130, 19, 163, 104], [81, 77]]]
 h' := ![![[143, 73, 115], [26, 115, 100], [128, 163, 33], [104, 104, 105], [16, 58, 116], [79, 90, 70], [0, 0, 1], [0, 1]], ![[165, 99, 58], [64, 154, 116], [112, 116, 41], [162, 124, 38], [80, 162, 162], [132, 92, 153], [111, 120, 99], [143, 73, 115]], ![[0, 1], [16, 77, 130], [145, 67, 99], [141, 118, 30], [54, 126, 68], [169, 164, 123], [61, 53, 73], [165, 99, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [72, 146], []]
 b := ![[], [125, 56, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [141, 117, 38, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3259839, 1136610, 108471]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18843, 6570, 627]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 58, 6]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![163, 58, 6]] 
 ![![179, 0, 0], ![38, 1, 0], ![167, 0, 1]] where
  M :=![![![163, 58, 6], ![1572, 559, 58], ![15196, 5400, 559]]]
  hmulB := by decide  
  f := ![![![-719, -22, 10]], ![![-138, -5, 2]], ![![-703, -14, 9]]]
  g := ![![![-17, 58, 6], ![-164, 559, 58], ![-1583, 5400, 559]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![67, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![67, 1, 0]] 
 ![![179, 0, 0], ![67, 1, 0], ![165, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![67, 1, 0], ![0, 67, 1], ![262, 66, 67]]]
  hmulB := by decide  
  f := ![![![4222, 63, 0], ![-11277, 0, 0]], ![![1474, 22, 0], ![-3937, 0, 0]], ![![3912, 58, 0], ![-10449, 1, 0]]]
  g := ![![![1, 0, 0], ![-67, 179, 0], ![-165, 0, 179]], ![![0, 1, 0], ![-26, 67, 1], ![-85, 66, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![74, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![74, 1, 0]] 
 ![![179, 0, 0], ![74, 1, 0], ![73, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![74, 1, 0], ![0, 74, 1], ![262, 66, 74]]]
  hmulB := by decide  
  f := ![![![3775, 51, 0], ![-9129, 0, 0]], ![![1554, 21, 0], ![-3758, 0, 0]], ![![1585, 21, 0], ![-3833, 1, 0]]]
  g := ![![![1, 0, 0], ![-74, 179, 0], ![-73, 0, 179]], ![![0, 1, 0], ![-31, 74, 1], ![-56, 66, 74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![163, 58, 6]] ![![179, 0, 0], ![67, 1, 0]]
  ![![179, 0, 0], ![40, -74, 1]] where
 M := ![![![29177, 10382, 1074], ![12493, 4445, 460]]]
 hmul := by decide  
 g := ![![![![123, 132, 5], ![179, 0, 0]], ![![47, 67, 2], ![102, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![40, -74, 1]] ![![179, 0, 0], ![74, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![13246, 179, 0]], ![![7160, -13246, 179], ![3222, -5370, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![74, 1, 0]]], ![![![40, -74, 1]], ![![18, -30, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [58, 52, 135, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 11, 104], [143, 169, 77], [0, 1]]
 g := ![![[36, 73, 137], [155, 62], [144, 32, 11], [50, 167], [92, 2, 9], [73, 46, 1], []], ![[109, 153, 72, 118], [87, 145], [20, 160, 85, 149], [62, 138], [167, 71, 168, 164], [119, 21, 80, 134], [83, 137]], ![[83, 177, 92, 115], [77, 48], [42, 53, 43, 58], [168, 55], [127, 129, 168, 159], [100, 52, 121, 86], [110, 137]]]
 h' := ![![[84, 11, 104], [12, 138, 104], [155, 170, 65], [144, 104, 83], [94, 141, 23], [110, 52, 3], [0, 0, 1], [0, 1]], ![[143, 169, 77], [60, 118, 72], [161, 90, 67], [29, 152, 46], [154, 44, 89], [163, 100, 123], [70, 84, 169], [84, 11, 104]], ![[0, 1], [170, 106, 5], [103, 102, 49], [89, 106, 52], [125, 177, 69], [159, 29, 55], [132, 97, 11], [143, 169, 77]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [132, 169], []]
 b := ![[], [36, 155, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [58, 52, 135, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113306, -19005, 6335]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-626, -105, 35]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [119, 124, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 15, 145], [51, 175, 46], [0, 1]]
 g := ![![[186, 188, 121], [104, 82, 13], [173, 140, 5], [52, 181, 80], [40, 154, 149], [48, 73, 1], []], ![[129, 130, 162, 7], [154, 106, 86, 132], [11, 53, 151, 123], [173, 150, 67, 165], [64, 185, 47, 174], [121, 99, 135, 66], [97, 15]], ![[95, 132, 144, 97], [42, 74, 98, 65], [91, 102, 64, 133], [182, 62, 30, 54], [15, 71, 3, 149], [178, 128, 11, 36], [5, 15]]]
 h' := ![![[22, 15, 145], [39, 37, 180], [41, 134, 83], [115, 124, 177], [15, 149, 56], [18, 68, 63], [0, 0, 1], [0, 1]], ![[51, 175, 46], [71, 78, 2], [173, 157, 148], [94, 159, 59], [155, 62, 81], [37, 175, 66], [19, 26, 175], [22, 15, 145]], ![[0, 1], [106, 76, 9], [136, 91, 151], [129, 99, 146], [2, 171, 54], [175, 139, 62], [96, 165, 15], [51, 175, 46]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 104], []]
 b := ![[], [86, 4, 77], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [119, 124, 118, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![880701, 485522, 69906]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4611, 2542, 366]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![17, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![17, 1, 0]] 
 ![![193, 0, 0], ![17, 1, 0], ![97, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![17, 1, 0], ![0, 17, 1], ![262, 66, 17]]]
  hmulB := by decide  
  f := ![![![2296, 135, 0], ![-26055, 0, 0]], ![![170, 10, 0], ![-1929, 0, 0]], ![![1158, 68, 0], ![-13141, 1, 0]]]
  g := ![![![1, 0, 0], ![-17, 193, 0], ![-97, 0, 193]], ![![0, 1, 0], ![-2, 17, 1], ![-13, 66, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-15, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-15, 1, 0]] 
 ![![193, 0, 0], ![178, 1, 0], ![161, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-15, 1, 0], ![0, -15, 1], ![262, 66, -15]]]
  hmulB := by decide  
  f := ![![![1666, -111, 0], ![21423, 0, 0]], ![![1546, -103, 0], ![19880, 0, 0]], ![![1412, -94, 0], ![18157, 1, 0]]]
  g := ![![![1, 0, 0], ![-178, 193, 0], ![-161, 0, 193]], ![![-1, 1, 0], ![13, -15, 1], ![-47, 66, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-2, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-2, 1, 0]] 
 ![![193, 0, 0], ![191, 1, 0], ![189, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-2, 1, 0], ![0, -2, 1], ![262, 66, -2]]]
  hmulB := by decide  
  f := ![![![199, -99, 0], ![19107, 0, 0]], ![![197, -98, 0], ![18915, 0, 0]], ![![195, -97, 0], ![18723, 1, 0]]]
  g := ![![![1, 0, 0], ![-191, 193, 0], ![-189, 0, 193]], ![![-1, 1, 0], ![1, -2, 1], ![-62, 66, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![17, 1, 0]] ![![193, 0, 0], ![-15, 1, 0]]
  ![![193, 0, 0], ![-62, 2, 1]] where
 M := ![![![37249, 0, 0], ![-2895, 193, 0]], ![![3281, 193, 0], ![-255, 2, 1]]]
 hmul := by decide  
 g := ![![![![193, 0, 0], ![0, 0, 0]], ![![47, -1, -1], ![193, 0, 0]]], ![![![17, 1, 0], ![0, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-62, 2, 1]] ![![193, 0, 0], ![-2, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-386, 193, 0]], ![![-11966, 386, 193], ![386, 0, 0]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-2, 1, 0]]], ![![![-62, 2, 1]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB238I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB238I3 : PrimesBelowBoundCertificateInterval O 137 193 238 where
  m := 11
  g := ![2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB238I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0]
    · exact ![I191N0]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![3869893]
    · exact ![4330747]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![5929741]
    · exact ![6967871]
    · exact ![193, 193, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I167N0, I167N1, I179N0, I179N1, I179N2, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [], [], [], [], [I167N0, I167N1, I167N1], [], [I179N0, I179N1, I179N2], [], [], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
