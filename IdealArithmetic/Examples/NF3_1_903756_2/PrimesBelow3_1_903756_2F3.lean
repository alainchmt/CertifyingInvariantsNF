
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1721644, 12527, -86886]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![1721644, 12527, -86886]] 
 ![![139, 0, 0], ![0, 139, 0], ![102, 49, 1]] where
  M :=![![![1721644, 12527, -86886], ![-15850030, 1262160, -122861], ![-5092869, -1501313, 1237909]]]
  hmulB := by decide  
  f := ![![![9913571273, 826876225, 777877367]], ![![145659063061, 12149205658, 11429270576]], ![![60186448095, 5020062057, 4722584272]]]
  g := ![![![76144, 30719, -86886], ![-23872, 52391, -122861], ![-945033, -447186, 1237909]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [132, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [50, 138], [0, 1]]
 g := ![![[27, 55], [34, 24], [57], [104, 107], [129], [137], [1]], ![[136, 84], [122, 115], [57], [33, 32], [129], [137], [1]]]
 h' := ![![[50, 138], [99, 74], [98, 21], [33, 14], [43, 78], [35, 44], [7, 50], [0, 1]], ![[0, 1], [46, 65], [36, 118], [38, 125], [51, 61], [11, 95], [5, 89], [50, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [34, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [132, 89, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6055, 2147, -220]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![205, 93, -220]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9913571273, 826876225, 777877367]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![9913571273, 826876225, 777877367]] 
 ![![139, 0, 0], ![14, 1, 0], ![23, 0, 1]] where
  M :=![![![9913571273, 826876225, 777877367], ![145659063061, 12149205658, 11429270576], ![217437925370, 18136173731, 17061464150]]]
  hmulB := by decide  
  f := ![![![1721644, 12527, -86886]], ![![59374, 10342, -9635]], ![![248237, -8728, -5471]]]
  g := ![![![-140675362, 826876225, 777877367], ![-2066928341, 12149205658, 11429270576], ![-3085483326, 18136173731, 17061464150]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![1721644, 12527, -86886]] ![![9913571273, 826876225, 777877367]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-23, -52, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-23, -52, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![126, 97, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-23, -52, 1], ![-25, 86, -569], ![-9431, -242, -173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-126, -97, 149]], ![![-1, -1, 1], ![481, 371, -569], ![83, 111, -173]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [66, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 148], [0, 1]]
 g := ![![[144, 110], [22], [23, 102], [9], [52, 73], [130], [1]], ![[88, 39], [22], [9, 47], [9], [4, 76], [130], [1]]]
 h' := ![![[32, 148], [77, 40], [121, 97], [27, 20], [144, 146], [97, 85], [83, 32], [0, 1]], ![[0, 1], [16, 109], [96, 52], [71, 129], [48, 3], [135, 64], [64, 117], [32, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109]]
 b := ![[], [22, 129]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [66, 117, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9529, 8457, 6614]
  a := ![9, -7, 25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5657, -4249, 6614]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-27, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-27, 1, 0]] 
 ![![149, 0, 0], ![122, 1, 0], ![24, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-27, 1, 0], ![4, -29, 11], ![183, 5, -24]]]
  hmulB := by decide  
  f := ![![![-2047, 15627, -5929], ![596, 80311, 0]], ![![-1682, 12786, -4851], ![448, 65709, 0]], ![![-327, 2517, -955], ![111, 12936, 0]]]
  g := ![![![1, 0, 0], ![-122, 149, 0], ![-24, 0, 149]], ![![-1, 1, 0], ![22, -29, 11], ![1, 5, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-23, -52, 1]] ![![149, 0, 0], ![-27, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-4023, 149, 0]], ![![-3427, -7748, 149], ![596, 1490, -596]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-27, 1, 0]]], ![![![-23, -52, 1]], ![![4, 10, -4]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![35, -64, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![35, -64, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![35, 87, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![35, -64, 1], ![-73, 168, -701], ![-11627, -302, -151]]]
  hmulB := by decide  
  f := ![![![-34, 64, -1], ![151, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-35, -87, 151]], ![![0, -1, 1], ![162, 405, -701], ![-42, 85, -151]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [49, 32, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 150], [0, 1]]
 g := ![![[127, 37], [25, 81], [65, 74], [16], [73, 88], [118], [1]], ![[0, 114], [0, 70], [113, 77], [16], [126, 63], [118], [1]]]
 h' := ![![[119, 150], [134, 108], [137, 9], [66, 15], [47, 4], [92, 115], [102, 119], [0, 1]], ![[0, 1], [0, 43], [0, 142], [39, 136], [70, 147], [36, 36], [69, 32], [119, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [43, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [49, 32, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10475108, 4540014, 1668587]
  a := ![-196, 67, -523]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-317387, -931305, 1668587]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-54, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-54, 1, 0]] 
 ![![151, 0, 0], ![97, 1, 0], ![0, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-54, 1, 0], ![4, -56, 11], ![183, 5, -51]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![20, 20, -4], ![60, 55, 0]]]
  g := ![![![1, 0, 0], ![-97, 151, 0], ![0, 0, 151]], ![![-1, 1, 0], ![36, -56, 11], ![-2, 5, -51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![35, -64, 1]] ![![151, 0, 0], ![-54, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-8154, 151, 0]], ![![5285, -9664, 151], ![-1963, 3624, -755]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-54, 1, 0]]], ![![![35, -64, 1]], ![![-13, 24, -5]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [81, 139, 139, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 116, 63], [104, 40, 94], [0, 1]]
 g := ![![[3, 153, 9], [95, 46], [106, 94, 90], [40, 114, 47], [5, 88, 156], [18, 1], []], ![[3, 76, 87, 28], [12, 33], [25, 129, 105, 6], [150, 146, 103, 50], [137, 101, 34, 62], [86, 30], [22, 44]], ![[59, 156, 93, 128], [84, 127], [126, 49, 76, 54], [54, 134, 3, 28], [138, 130, 74, 63], [49, 111], [148, 44]]]
 h' := ![![[71, 116, 63], [44, 77, 3], [49, 55, 49], [57, 81, 103], [66, 11, 138], [112, 86, 28], [0, 0, 1], [0, 1]], ![[104, 40, 94], [59, 17, 104], [51, 132, 87], [10, 149, 117], [156, 14, 90], [130, 36, 101], [119, 116, 40], [71, 116, 63]], ![[0, 1], [140, 63, 50], [151, 127, 21], [20, 84, 94], [85, 132, 86], [104, 35, 28], [84, 41, 116], [104, 40, 94]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [154, 150], []]
 b := ![[], [114, 141, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [81, 139, 139, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47551532, -1627776, -58247]
  a := ![-9, 6, -25]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-302876, -10368, -371]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-65, -47, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-65, -47, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![98, 116, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-65, -47, 1], ![-5, 34, -514], ![-8516, -217, -200]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-98, -116, 163]], ![![-1, -1, 1], ![309, 366, -514], ![68, 141, -200]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [72, 21, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [142, 162], [0, 1]]
 g := ![![[75, 87], [135, 38], [36], [88], [97], [120, 115], [1]], ![[41, 76], [152, 125], [36], [88], [97], [150, 48], [1]]]
 h' := ![![[142, 162], [60, 24], [85, 110], [45, 6], [26, 67], [162, 89], [91, 142], [0, 1]], ![[0, 1], [45, 139], [57, 53], [82, 157], [86, 96], [86, 74], [43, 21], [142, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [51, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [72, 21, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6267, 2079, 528]
  a := ![-4, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-279, -363, 528]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![25, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![25, 1, 0]] 
 ![![163, 0, 0], ![25, 1, 0], ![37, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![25, 1, 0], ![4, 23, 11], ![183, 5, 28]]]
  hmulB := by decide  
  f := ![![![29151, 172466, 82500], ![5542, -1222500, 0]], ![![4450, 26444, 12650], ![979, -187450, 0]], ![![6599, 39148, 18727], ![1376, -277500, 0]]]
  g := ![![![1, 0, 0], ![-25, 163, 0], ![-37, 0, 163]], ![![0, 1, 0], ![-6, 23, 11], ![-6, 5, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-65, -47, 1]] ![![163, 0, 0], ![25, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![4075, 163, 0]], ![![-10595, -7661, 163], ![-1630, -1141, -489]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![25, 1, 0]]], ![![![-65, -47, 1]], ![![-10, -7, -3]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [79, 159, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 72, 99], [125, 94, 68], [0, 1]]
 g := ![![[64, 159, 93], [46, 159, 2], [103, 121, 94], [85, 3], [19, 31], [70, 79, 1], []], ![[66, 141, 95, 18], [137, 44, 47, 99], [31, 28, 131, 147], [91, 127], [61, 126], [126, 59, 165, 18], [128, 115]], ![[89, 34, 62, 136], [46, 110, 29, 106], [104, 6, 10, 95], [63, 8], [28, 50], [31, 157, 22, 142], [159, 115]]]
 h' := ![![[121, 72, 99], [40, 110, 107], [46, 122, 154], [138, 81, 125], [29, 155, 62], [148, 164, 71], [0, 0, 1], [0, 1]], ![[125, 94, 68], [126, 79, 73], [19, 124, 1], [81, 26, 63], [151, 152, 131], [36, 64, 31], [20, 11, 94], [121, 72, 99]], ![[0, 1], [123, 145, 154], [13, 88, 12], [145, 60, 146], [121, 27, 141], [50, 106, 65], [58, 156, 72], [125, 94, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61, 12], []]
 b := ![[], [112, 103, 10], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [79, 159, 88, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![78470628, 6736780, 6693193]
  a := ![7, 16, 19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![469884, 40340, 40079]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [48, 149, 51, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [166, 39, 142], [129, 133, 31], [0, 1]]
 g := ![![[47, 165, 55], [29, 172], [160, 23, 24], [171, 51, 35], [171, 118], [30, 122, 1], []], ![[96, 49, 114, 140], [26, 159], [32, 156, 143, 133], [6, 8, 14, 43], [54, 159], [84, 133, 88, 51], [125, 96]], ![[40, 43, 101, 89], [13, 55], [64, 94, 13, 88], [61, 116, 165, 81], [97, 4], [160, 129, 89, 95], [63, 96]]]
 h' := ![![[166, 39, 142], [118, 88, 125], [105, 15, 80], [96, 10, 71], [118, 4, 143], [117, 54, 139], [0, 0, 1], [0, 1]], ![[129, 133, 31], [46, 83, 57], [16, 54, 141], [144, 42, 137], [84, 74, 38], [9, 87, 32], [104, 95, 133], [166, 39, 142]], ![[0, 1], [30, 2, 164], [116, 104, 125], [85, 121, 138], [58, 95, 165], [133, 32, 2], [123, 78, 39], [129, 133, 31]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37, 70], []]
 b := ![[], [130, 95, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [48, 149, 51, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19549173, -1060836, 138573]
  a := ![-7, 6, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-113001, -6132, 801]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [32, 147, 95, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [172, 124, 128], [91, 54, 51], [0, 1]]
 g := ![![[17, 61, 95], [78, 93, 126], [171, 9], [88, 155], [50, 4, 81], [107, 84, 1], []], ![[132, 113, 103, 128], [129, 144, 16, 10], [138, 15], [33, 81], [72, 104, 1, 78], [153, 52, 170, 33], [165, 95]], ![[141, 160, 99, 74], [98, 176, 83, 149], [22, 43], [171, 67], [48, 178, 157, 5], [162, 91, 95, 156], [63, 95]]]
 h' := ![![[172, 124, 128], [10, 61, 51], [177, 153, 157], [169, 171, 3], [11, 32, 100], [156, 20, 9], [0, 0, 1], [0, 1]], ![[91, 54, 51], [49, 153, 1], [165, 8, 138], [105, 162, 33], [83, 131, 9], [14, 35, 3], [139, 146, 54], [172, 124, 128]], ![[0, 1], [12, 144, 127], [138, 18, 63], [157, 25, 143], [59, 16, 70], [7, 124, 167], [0, 33, 124], [91, 54, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 41], []]
 b := ![[], [110, 169, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [32, 147, 95, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![37725503, 2824620, 1311354]
  a := ![8, -3, 22]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![210757, 15780, 7326]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22864, -1907, -1794]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-22864, -1907, -1794]] 
 ![![181, 0, 0], ![0, 181, 0], ![19, 141, 1]] where
  M :=![![![-22864, -1907, -1794], ![-335930, -28020, -26359], ![-501471, -41827, -39349]]]
  hmulB := by decide  
  f := ![![![-227, 5, 7]], ![![1301, -202, 76]], ![![998, -156, 59]]]
  g := ![![![62, 1387, -1794], ![911, 20379, -26359], ![1360, 30422, -39349]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [94, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 180], [0, 1]]
 g := ![![[103, 52], [136], [31, 64], [152], [38, 25], [106, 138], [1]], ![[0, 129], [136], [127, 117], [152], [166, 156], [132, 43], [1]]]
 h' := ![![[92, 180], [29, 41], [163, 90], [143, 8], [48, 141], [172, 5], [87, 92], [0, 1]], ![[0, 1], [0, 140], [117, 91], [155, 173], [169, 40], [89, 176], [44, 89], [92, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [100, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [94, 89, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![61884, 27045, 6315]
  a := ![-15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-321, -4770, 6315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-227, 5, 7]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-227, 5, 7]] 
 ![![181, 0, 0], ![75, 1, 0], ![95, 0, 1]] where
  M :=![![![-227, 5, 7], ![1301, -202, 76], ![1510, 151, -170]]]
  hmulB := by decide  
  f := ![![![-22864, -1907, -1794]], ![![-11330, -945, -889]], ![![-14771, -1232, -1159]]]
  g := ![![![-7, 5, 7], ![51, -202, 76], ![35, 151, -170]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-22864, -1907, -1794]] ![![-227, 5, 7]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![70, 82, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![70, 82, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![70, 82, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![70, 82, 1], ![511, -89, 905], ![15091, 428, 322]]]
  hmulB := by decide  
  f := ![![![-69, -82, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-70, -82, 191]], ![![0, 0, 1], ![-329, -389, 905], ![-39, -136, 322]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [72, 0, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [0, 190], [0, 1]]
 g := ![![[0, 130], [0, 51], [0, 144], [0, 32], [0, 156], [], [1]], ![[0, 61], [0, 140], [0, 47], [0, 159], [0, 35], [], [1]]]
 h' := ![![[0, 190], [0, 148], [0, 137], [0, 179], [0, 37], [0, 27], [119], [0, 1]], ![[0, 1], [0, 43], [0, 54], [0, 12], [0, 154], [0, 164], [119], [0, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130]]
 b := ![[], [0, 65]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [72, 0, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-98496, 18952, 8896]
  a := ![14, -16, 38]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3776, -3720, 8896]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![50, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![50, 1, 0]] 
 ![![191, 0, 0], ![50, 1, 0], ![60, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![50, 1, 0], ![4, 48, 11], ![183, 5, 53]]]
  hmulB := by decide  
  f := ![![![58673, 765162, 175373], ![19482, -3045113, 0]], ![![15342, 200277, 45903], ![5158, -797043, 0]], ![![18430, 240365, 55091], ![6125, -956580, 0]]]
  g := ![![![1, 0, 0], ![-50, 191, 0], ![-60, 0, 191]], ![![0, 1, 0], ![-16, 48, 11], ![-17, 5, 53]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![70, 82, 1]] ![![191, 0, 0], ![50, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![9550, 191, 0]], ![![13370, 15662, 191], ![4011, 4011, 955]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![50, 1, 0]]], ![![![70, 82, 1]], ![![21, 21, 5]]]]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [125, 83, 166, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [117, 185, 55], [103, 7, 138], [0, 1]]
 g := ![![[67, 25, 85], [84, 65], [118, 49], [153, 8], [37, 112], [147, 150], [1]], ![[170, 19, 10, 128], [116, 86], [96, 63], [12, 162], [121, 192], [172, 109], [121, 152, 18, 9]], ![[112, 165, 185, 2], [114, 59], [57, 143], [85, 98], [136, 93], [74, 187], [48, 7, 171, 184]]]
 h' := ![![[117, 185, 55], [46, 98, 144], [160, 147, 79], [7, 155, 186], [188, 120, 89], [145, 28, 150], [68, 110, 27], [0, 1]], ![[103, 7, 138], [44, 123, 29], [29, 44, 146], [16, 20, 177], [101, 4, 82], [128, 182, 81], [28, 50, 63], [117, 185, 55]], ![[0, 1], [4, 165, 20], [101, 2, 161], [49, 18, 23], [161, 69, 22], [62, 176, 155], [137, 33, 103], [103, 7, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129, 50], []]
 b := ![[], [9, 90, 157], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [125, 83, 166, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5218378390, 331657376, 157915109]
  a := ![43, -16, 115]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27038230, 1718432, 818213]
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



lemma PB269I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB269I3 : PrimesBelowBoundCertificateInterval O 137 193 269 where
  m := 11
  g := ![2, 2, 2, 1, 2, 1, 1, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB269I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
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
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
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
      exact NI151N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
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
  β := ![I139N1, I149N1, I151N1, I163N1, I181N1, I191N1]
  Il := ![[I139N1], [I149N1], [I151N1], [], [I163N1], [], [], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
