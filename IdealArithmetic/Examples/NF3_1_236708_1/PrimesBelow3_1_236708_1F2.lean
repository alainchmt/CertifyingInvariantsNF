
import IdealArithmetic.Examples.NF3_1_236708_1.RI3_1_236708_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-508481049, 58585110, 27532108]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-508481049, 58585110, 27532108]] 
 ![![83, 0, 0], ![0, 83, 0], ![9, 74, 1]] where
  M :=![![![-508481049, 58585110, 27532108], ![2588018152, -1059123209, 86117218], ![8095018492, 865673792, -973005991]]]
  hmulB := by decide  
  f := ![![![11517877215681861, 973945630692862, 412109412830344]], ![![38738284806052336, 3275688959074981, 1386055043523206]], ![![37356423429881819, 3158839488956296, 1336612071551669]]]
  g := ![![![-9111687, -23840854, 27532108], ![21842930, -89539727, 86117218], ![203037017, 877929122, -973005991]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [5, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 82], [0, 1]]
 g := ![![[31, 41], [46, 64], [21], [30], [59, 38], [1]], ![[67, 42], [3, 19], [21], [30], [62, 45], [1]]]
 h' := ![![[11, 82], [19, 37], [73, 8], [57, 41], [37, 69], [78, 11], [0, 1]], ![[0, 1], [11, 46], [78, 75], [10, 42], [49, 14], [33, 72], [11, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [79, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [5, 72, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![287, -38, -88]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 78, -88]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11517877215681861, -973945630692862, -412109412830344]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-11517877215681861, -973945630692862, -412109412830344]] 
 ![![83, 0, 0], ![8, 1, 0], ![19, 0, 1]] where
  M :=![![![-11517877215681861, -973945630692862, -412109412830344], ![-38738284806052336, -3275688959074981, -1386055043523206], ![-130289174091181364, -11017183935588216, -4661744002598187]]]
  hmulB := by decide  
  f := ![![![508481049, -58585110, -27532108]], ![![17829280, 7113763, -3691254]], ![![18868933, -23840854, 5420433]]]
  g := ![![![49442971971537, -973945630692862, -412109412830344], ![166292442090222, -3275688959074981, -1386055043523206], ![559294378829999, -11017183935588216, -4661744002598187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-508481049, 58585110, 27532108]] ![![-11517877215681861, -973945630692862, -412109412830344]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [68, 63, 33, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [87, 28, 83], [58, 60, 6], [0, 1]]
 g := ![![[55, 2, 72], [28, 1], [23, 87], [37, 79, 47], [47, 56, 1], []], ![[74, 0, 69, 52], [31, 88], [71, 4], [55, 28, 16, 12], [25, 58, 35, 27], [78, 36]], ![[54, 25, 73, 76], [72, 21], [39, 20], [10, 5, 66, 83], [3, 69, 72, 76], [66, 36]]]
 h' := ![![[87, 28, 83], [46, 52, 28], [80, 14, 88], [65, 15, 49], [8, 84, 15], [0, 0, 1], [0, 1]], ![[58, 60, 6], [83, 88, 33], [12, 34, 34], [37, 73, 2], [84, 68, 40], [40, 2, 60], [87, 28, 83]], ![[0, 1], [70, 38, 28], [58, 41, 56], [60, 1, 38], [35, 26, 34], [33, 87, 28], [58, 60, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22, 37], []]
 b := ![[], [80, 5, 21], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [68, 63, 33, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![230243, -73514, 5251]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2587, -826, 59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 704969 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def PBC89 : ContainsPrimesAboveP 89 ![I89N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![89, 0, 0]]) timesTableT_eq_Table B_one_repr 89 (by decide) 𝕀

instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24315, 2056, 870]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![24315, 2056, 870]] 
 ![![97, 0, 0], ![0, 97, 0], ![43, 26, 1]] where
  M :=![![![24315, 2056, 870], ![81780, 6915, 2926], ![275044, 23260, 9841]]]
  hmulB := by decide  
  f := ![![![-85, 32, -2]], ![![-188, -45, 30]], ![![-59, -6, 7]]]
  g := ![![![-135, -212, 870], ![-454, -713, 2926], ![-1527, -2398, 9841]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [67, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [32, 96], [0, 1]]
 g := ![![[14, 3], [11], [25], [18], [72], [32, 1]], ![[13, 94], [11], [25], [18], [72], [64, 96]]]
 h' := ![![[32, 96], [72, 87], [18, 60], [23, 5], [29, 42], [87, 84], [0, 1]], ![[0, 1], [43, 10], [95, 37], [86, 92], [15, 55], [59, 13], [32, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [76, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [67, 65, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-91, 51, 43]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -11, 43]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![85, -32, 2]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![85, -32, 2]] 
 ![![97, 0, 0], ![70, 1, 0], ![47, 0, 1]] where
  M :=![![![85, -32, 2], ![188, 45, -30], ![-2820, 788, 15]]]
  hmulB := by decide  
  f := ![![![-24315, -2056, -870]], ![![-18390, -1555, -658]], ![![-14617, -1236, -523]]]
  g := ![![![23, -32, 2], ![-16, 45, -30], ![-605, 788, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![24315, 2056, 870]] ![![85, -32, 2]]
  ![![97, 0, 0]] where
 M := ![![![-97, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC97 : ContainsPrimesAboveP 97 ![I97N0, I97N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
    exact isPrimeI97N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 97 (by decide) (𝕀 ⊙ MulI97N0)
instance hp101 : Fact (Nat.Prime 101) := {out := by norm_num}

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0]] 
 ![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [39, 24, 81, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [83, 19, 2], [38, 81, 99], [0, 1]]
 g := ![![[16, 47, 6], [53, 9], [38, 87, 31], [59, 22], [71, 97], [1]], ![[32, 52, 29, 27], [6, 13], [74, 8, 3, 91], [5, 49], [28, 17], [75, 24, 85, 8]], ![[0, 44, 17, 26], [50, 14], [81, 13, 21, 15], [74, 45], [88, 71], [14, 45, 4, 93]]]
 h' := ![![[83, 19, 2], [32, 10, 62], [33, 63, 3], [5, 52, 58], [65, 21, 27], [62, 77, 20], [0, 1]], ![[38, 81, 99], [70, 95, 93], [1, 70, 66], [6, 39, 55], [10, 53, 7], [30, 77, 57], [83, 19, 2]], ![[0, 1], [0, 97, 47], [58, 69, 32], [48, 10, 89], [45, 27, 67], [89, 48, 24], [38, 81, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 30], []]
 b := ![[], [87, 64, 86], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [39, 24, 81, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-164731, 156247, -27977]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1631, 1547, -277]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 1030301 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def PBC101 : ContainsPrimesAboveP 101 ![I101N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![101, 0, 0]]) timesTableT_eq_Table B_one_repr 101 (by decide) 𝕀

instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![934573, 79027, 33439]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![934573, 79027, 33439]] 
 ![![103, 0, 0], ![0, 103, 0], ![50, 5, 1]] where
  M :=![![![934573, 79027, 33439], ![3143266, 265793, 112466], ![10571804, 893946, 378259]]]
  hmulB := by decide  
  f := ![![![617, -133, -15]], ![![-1410, 917, -148]], ![![96, -5, -7]]]
  g := ![![![-7159, -856, 33439], ![-24078, -2879, 112466], ![-80982, -9683, 378259]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [34, 23, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 102], [0, 1]]
 g := ![![[34, 100], [72, 30], [22, 33], [1], [91], [80, 1]], ![[0, 3], [0, 73], [87, 70], [1], [91], [57, 102]]]
 h' := ![![[80, 102], [24, 10], [76, 66], [47, 62], [9, 102], [61, 83], [0, 1]], ![[0, 1], [0, 93], [0, 37], [63, 41], [32, 1], [6, 20], [80, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49]]
 b := ![[], [50, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [34, 23, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![316, 11, -39]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![22, 2, -39]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-617, 133, 15]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![-617, 133, 15]] 
 ![![103, 0, 0], ![97, 1, 0], ![67, 0, 1]] where
  M :=![![![-617, 133, 15], ![1410, -917, 148], ![13912, -1550, -769]]]
  hmulB := by decide  
  f := ![![![-934573, -79027, -33439]], ![![-910649, -77004, -32583]], ![![-710565, -60085, -25424]]]
  g := ![![![-141, 133, 15], ![781, -917, 148], ![2095, -1550, -769]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![934573, 79027, 33439]] ![![-617, 133, 15]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1039653, -30954617, 9111687]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![1039653, -30954617, 9111687]] 
 ![![107, 0, 0], ![49, 1, 0], ![60, 0, 1]] where
  M :=![![![1039653, -30954617, 9111687], ![856498578, -181194087, -21842930], ![-2053235420, 1293357178, -203037017]]]
  hmulB := by decide  
  f := ![![![-65039817226570019, -5499732687081797, -2327123339302579]], ![![-31828977925199751, -2691441608481556, -1138840183665521]], ![![-43346855140881612, -3665387239174418, -1550949596495865]]]
  g := ![![![9075838, -30954617, 9111687], ![103229763, -181194087, -21842930], ![-497621646, 1293357178, -203037017]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![462986206317725, 39149869743382, 16565637058048]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![462986206317725, 39149869743382, 16565637058048]] 
 ![![107, 0, 0], ![73, 1, 0], ![21, 0, 1]] where
  M :=![![![462986206317725, 39149869743382, 16565637058048], ![1557169883456512, 131673465156765, 55715506801430], ![5237257639334420, 442859747427912, 187388971958195]]]
  hmulB := by decide  
  f := ![![![77925015, -42479714, 5741540]], ![![58207765, -29326401, 3573778]], ![![-16980963, 3573778, 438583]]]
  g := ![![![-25633950123067, 39149869743382, 16565637058048], ![-86215128185209, 131673465156765, 55715506801430], ![-289968900317993, 442859747427912, 187388971958195]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 7, 3]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![83, 7, 3]] 
 ![![107, 0, 0], ![91, 1, 0], ![65, 0, 1]] where
  M :=![![![83, 7, 3], ![282, 23, 10], ![940, 82, 33]]]
  hmulB := by decide  
  f := ![![![-61, 15, 1]], ![![-51, 12, 1]], ![![-23, 7, 0]]]
  g := ![![![-7, 7, 3], ![-23, 23, 10], ![-81, 82, 33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![1039653, -30954617, 9111687]] ![![462986206317725, 39149869743382, 16565637058048]]
  ![![61, -15, -1]] where
 M := ![![![61, -15, -1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![61, -15, -1]] ![![83, 7, 3]]
  ![![107, 0, 0]] where
 M := ![![![-107, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1, I107N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
    exact isPrimeI107N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0 ⊙ MulI107N1)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20023, -16346, 3090]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![20023, -16346, 3090]] 
 ![![109, 0, 0], ![0, 109, 0], ![2, 46, 1]] where
  M :=![![![20023, -16346, 3090], ![290460, -41777, -13256], ![-1246064, 555580, -55033]]]
  hmulB := by decide  
  f := ![![![-88659469, -7496998, -3172234]], ![![-298189996, -25214789, -10669232]], ![![-136669418, -11556694, -4890029]]]
  g := ![![![127, -1454, 3090], ![2908, 5211, -13256], ![-10422, 28322, -55033]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [108, 68, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 108], [0, 1]]
 g := ![![[41, 108], [38], [94, 88], [27, 78], [29], [41, 1]], ![[0, 1], [38], [105, 21], [64, 31], [29], [82, 108]]]
 h' := ![![[41, 108], [45, 76], [94, 93], [27, 52], [75, 29], [41, 47], [0, 1]], ![[0, 1], [0, 33], [92, 16], [88, 57], [65, 80], [6, 62], [41, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [3, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [108, 68, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3843, 644, 450]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![27, -184, 450]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-88659469, -7496998, -3172234]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-88659469, -7496998, -3172234]] 
 ![![109, 0, 0], ![62, 1, 0], ![80, 0, 1]] where
  M :=![![![-88659469, -7496998, -3172234], ![-298189996, -25214789, -10669232], ![-1002907808, -84805356, -35884021]]]
  hmulB := by decide  
  f := ![![![20023, -16346, 3090]], ![![14054, -9681, 1636]], ![![3264, -6900, 1763]]]
  g := ![![![5779203, -7496998, -3172234], ![19437298, -25214789, -10669232], ![65373816, -84805356, -35884021]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![20023, -16346, 3090]] ![![-88659469, -7496998, -3172234]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7531, -1025, -361]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![7531, -1025, -361]] 
 ![![113, 0, 0], ![0, 113, 0], ![84, 62, 1]] where
  M :=![![![7531, -1025, -361], ![-33934, 14751, -1386], ![-130284, -6214, 13365]]]
  hmulB := by decide  
  f := ![![![-1668447, -141083, -59697]], ![![-5611518, -474507, -200780]], ![![-4486168, -379348, -160515]]]
  g := ![![![335, 189, -361], ![730, 891, -1386], ![-11088, -7388, 13365]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [66, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [91, 112], [0, 1]]
 g := ![![[38, 49], [31], [13], [13], [19, 26], [91, 1]], ![[90, 64], [31], [13], [13], [12, 87], [69, 112]]]
 h' := ![![[91, 112], [112, 7], [24, 12], [54, 76], [102, 76], [96, 79], [0, 1]], ![[0, 1], [71, 106], [99, 101], [77, 37], [12, 37], [53, 34], [91, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [79, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [66, 22, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-425, 254, -36]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![23, 22, -36]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1668447, -141083, -59697]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-1668447, -141083, -59697]] 
 ![![113, 0, 0], ![50, 1, 0], ![99, 0, 1]] where
  M :=![![![-1668447, -141083, -59697], ![-5611518, -474507, -200780], ![-18873320, -1595918, -675287]]]
  hmulB := by decide  
  f := ![![![7531, -1025, -361]], ![![3032, -323, -172]], ![![5445, -953, -198]]]
  g := ![![![99962, -141083, -59697], ![336204, -474507, -200780], ![1130761, -1595918, -675287]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![7531, -1025, -361]] ![![-1668447, -141083, -59697]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![412633, 34892, 14764]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![412633, 34892, 14764]] 
 ![![127, 0, 0], ![0, 127, 0], ![40, 122, 1]] where
  M :=![![![412633, 34892, 14764], ![1387816, 117353, 49656], ![4667664, 394696, 167009]]]
  hmulB := by decide  
  f := ![![![-137, 108, -20]], ![![-1880, 263, 88]], ![![-1784, 258, 81]]]
  g := ![![![-1401, -13908, 14764], ![-4712, -46777, 49656], ![-15848, -157326, 167009]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [109, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 126], [0, 1]]
 g := ![![[100, 60], [93, 34], [89, 18], [29, 69], [104, 36], [22, 1]], ![[23, 67], [79, 93], [104, 109], [23, 58], [7, 91], [44, 126]]]
 h' := ![![[22, 126], [23, 106], [78, 65], [14, 48], [94, 113], [15, 121], [0, 1]], ![[0, 1], [69, 21], [111, 62], [54, 79], [40, 14], [10, 6], [22, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74]]
 b := ![[], [101, 37]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [109, 105, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![861, 321, 139]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -131, 139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, 108, -20]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-137, 108, -20]] 
 ![![127, 0, 0], ![4, 1, 0], ![111, 0, 1]] where
  M :=![![![-137, 108, -20], ![-1880, 263, 88], ![8272, -3640, 351]]]
  hmulB := by decide  
  f := ![![![412633, 34892, 14764]], ![![23924, 2023, 856]], ![![397401, 33604, 14219]]]
  g := ![![![13, 108, -20], ![-100, 263, 88], ![-127, -3640, 351]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![412633, 34892, 14764]] ![![-137, 108, -20]]
  ![![127, 0, 0]] where
 M := ![![![127, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [83, 19, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 40, 26], [118, 90, 105], [0, 1]]
 g := ![![[105, 46, 55], [94, 15, 65], [125, 3], [89, 58], [119, 52], [49, 1], []], ![[67, 107, 51, 130], [121, 8, 79, 40], [18, 129], [83, 41], [118, 44], [107, 109], [96, 21]], ![[13, 14, 98, 112], [33, 21, 68, 108], [57, 100], [82, 7], [91, 12], [103, 28], [17, 21]]]
 h' := ![![[62, 40, 26], [58, 66, 102], [79, 29, 117], [74, 79, 38], [115, 89, 78], [125, 34, 24], [0, 0, 1], [0, 1]], ![[118, 90, 105], [82, 102, 23], [8, 129, 18], [89, 26, 103], [64, 78, 33], [66, 77, 31], [68, 83, 90], [62, 40, 26]], ![[0, 1], [110, 94, 6], [60, 104, 127], [59, 26, 121], [70, 95, 20], [5, 20, 76], [68, 48, 40], [118, 90, 105]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 59], []]
 b := ![[], [104, 94, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [83, 19, 82, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79255, 77290, -15458]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-605, 590, -118]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 2248091 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def PBC131 : ContainsPrimesAboveP 131 ![I131N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![131, 0, 0]]) timesTableT_eq_Table B_one_repr 131 (by decide) 𝕀

instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0]] 
 ![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [90, 98, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 82, 11], [79, 54, 126], [0, 1]]
 g := ![![[77, 50, 93], [17, 7], [11, 118], [12, 52, 103], [136, 93], [136, 1], []], ![[99, 29, 127, 88], [81, 128], [72, 87], [97, 9, 118, 107], [94, 122], [22, 39], [39, 121]], ![[1, 13, 46, 19], [15, 59], [83, 120], [70, 53, 35, 121], [10, 37], [8, 11], [61, 121]]]
 h' := ![![[57, 82, 11], [49, 72, 40], [88, 1, 12], [16, 113, 23], [107, 18, 69], [90, 8, 40], [0, 0, 1], [0, 1]], ![[79, 54, 126], [15, 132, 75], [27, 104, 111], [43, 15, 19], [112, 27, 88], [107, 90, 56], [13, 116, 54], [57, 82, 11]], ![[0, 1], [20, 70, 22], [0, 32, 14], [49, 9, 95], [55, 92, 117], [74, 39, 41], [66, 21, 82], [79, 54, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 30], []]
 b := ![[], [97, 99, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [90, 98, 1, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10686, -137, 137]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![78, -1, 1]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 2571353 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def PBC137 : ContainsPrimesAboveP 137 ![I137N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![137, 0, 0]]) timesTableT_eq_Table B_one_repr 137 (by decide) 𝕀



lemma PB138I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB138I2 : PrimesBelowBoundCertificateInterval O 79 137 138 where
  m := 11
  g := ![2, 1, 2, 1, 2, 3, 2, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB138I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
    · exact ![I137N0]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC83
    · exact PBC89
    · exact PBC97
    · exact PBC101
    · exact PBC103
    · exact PBC107
    · exact PBC109
    · exact PBC113
    · exact PBC127
    · exact PBC131
    · exact PBC137
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![6889, 83]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![2248091]
    · exact ![2571353]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
      exact NI97N1
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
      exact NI103N1
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
      exact NI107N2
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I97N1, I103N1, I107N0, I107N1, I107N2, I109N1, I113N1, I127N1]
  Il := ![[I83N1], [], [I97N1], [], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [I113N1], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
