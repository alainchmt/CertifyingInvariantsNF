
import IdealArithmetic.Examples.NF3_1_463091_1.RI3_1_463091_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1035, -116, 58]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-1035, -116, 58]] 
 ![![83, 0, 0], ![20, 1, 0], ![15, 0, 1]] where
  M :=![![![-1035, -116, 58], ![7598, -803, -116], ![-15196, 7134, -803]]]
  hmulB := by decide  
  f := ![![![-1472353, -320624, -60030]], ![![-449530, -97891, -18328]], ![![-772133, -168142, -31481]]]
  g := ![![![5, -116, 58], ![306, -803, -116], ![-1757, 7134, -803]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N0 : Nat.card (O ⧸ I83N0) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N0)

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := prime_ideal_of_norm_prime hp83.out _ NI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1097900, -239082, -44763]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-1097900, -239082, -44763]] 
 ![![83, 0, 0], ![67, 1, 0], ![76, 0, 1]] where
  M :=![![![-1097900, -239082, -44763], ![-5863953, -1276952, -239082], ![-31319742, -6820281, -1276952]]]
  hmulB := by decide  
  f := ![![![11738, -339, -348]], ![![8926, -149, -285]], ![![10213, -876, -194]]]
  g := ![![![220754, -239082, -44763], ![1179061, -1276952, -239082], ![6297439, -6820281, -1276952]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1

def I83N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4, 1, 0]] i)))

def SI83N2: IdealEqSpanCertificate' Table ![![-4, 1, 0]] 
 ![![83, 0, 0], ![79, 1, 0], ![67, 0, 1]] where
  M :=![![![-4, 1, 0], ![0, -4, 1], ![131, 4, -4]]]
  hmulB := by decide  
  f := ![![![12, 4, 1]], ![![13, 4, 1]], ![![16, 5, 1]]]
  g := ![![![-1, 1, 0], ![3, -4, 1], ![1, 4, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N2 : Nat.card (O ⧸ I83N2) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N2)

lemma isPrimeI83N2 : Ideal.IsPrime I83N2 := prime_ideal_of_norm_prime hp83.out _ NI83N2
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-1035, -116, 58]] ![![-1097900, -239082, -44763]]
  ![![12, 4, 1]] where
 M := ![![![12, 4, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI83N1 : IdealMulLeCertificate' Table 
  ![![12, 4, 1]] ![![-4, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC83 : ContainsPrimesAboveP 83 ![I83N0, I83N1, I83N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
    exact isPrimeI83N1
    exact isPrimeI83N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 83 (by decide) (𝕀 ⊙ MulI83N0 ⊙ MulI83N1)
instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15654, -3246, 59]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![15654, -3246, 59]] 
 ![![89, 0, 0], ![0, 89, 0], ![30, 37, 1]] where
  M :=![![![15654, -3246, 59], ![7729, 15890, -3246], ![-425226, -5255, 15890]]]
  hmulB := by decide  
  f := ![![![-2645330, -576055, -107854]], ![![-14128874, -3076746, -576055]], ![![-7613387, -1657914, -310409]]]
  g := ![![![156, -61, 59], ![1181, 1528, -3246], ![-10134, -6665, 15890]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [87, 26, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 88], [0, 1]]
 g := ![![[76, 44], [25], [57], [45, 78], [31, 53], [1]], ![[0, 45], [25], [57], [64, 11], [77, 36], [1]]]
 h' := ![![[63, 88], [14, 69], [26, 84], [1, 71], [62, 16], [2, 63], [0, 1]], ![[0, 1], [0, 20], [67, 5], [24, 18], [2, 73], [55, 26], [63, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [20, 70]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [87, 26, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![349, 113, -21]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11, 10, -21]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2645330, 576055, 107854]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![2645330, 576055, 107854]] 
 ![![89, 0, 0], ![52, 1, 0], ![55, 0, 1]] where
  M :=![![![2645330, 576055, 107854], ![14128874, 3076746, 576055], ![75463205, 16433094, 3076746]]]
  hmulB := by decide  
  f := ![![![-15654, 3246, -59]], ![![-9233, 1718, 2]], ![![-4896, 2065, -215]]]
  g := ![![![-373500, 576055, 107854], ![-1994887, 3076746, 576055], ![-10654817, 16433094, 3076746]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![15654, -3246, 59]] ![![2645330, 576055, 107854]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC89 : ContainsPrimesAboveP 89 ![I89N0, I89N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI89N0
    exact isPrimeI89N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 89 (by decide) (𝕀 ⊙ MulI89N0)
instance hp97 : Fact (Nat.Prime 97) := {out := by norm_num}

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6952, -274, 295]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-6952, -274, 295]] 
 ![![97, 0, 0], ![0, 97, 0], ![8, 77, 1]] where
  M :=![![![-6952, -274, 295], ![38645, -5772, -274], ![-35894, 37549, -5772]]]
  hmulB := by decide  
  f := ![![![-449530, -97891, -18328]], ![![-2400968, -522842, -97891]], ![![-2075201, -451902, -84609]]]
  g := ![![![-96, -237, 295], ![421, 158, -274], ![106, 4969, -5772]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [89, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 96], [0, 1]]
 g := ![![[66, 12], [54], [64], [33], [2], [43, 1]], ![[0, 85], [54], [64], [33], [2], [86, 96]]]
 h' := ![![[43, 96], [13, 20], [39, 65], [20, 8], [12, 18], [53, 14], [0, 1]], ![[0, 1], [0, 77], [21, 32], [73, 89], [10, 79], [73, 83], [43, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5]]
 b := ![[], [19, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [89, 54, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1536, 1027, 196]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-32, -145, 196]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![449530, 97891, 18328]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![449530, 97891, 18328]] 
 ![![97, 0, 0], ![20, 1, 0], ![85, 0, 1]] where
  M :=![![![449530, 97891, 18328], ![2400968, 522842, 97891], ![12823721, 2792532, 522842]]]
  hmulB := by decide  
  f := ![![![6952, 274, -295]], ![![1035, 116, -58]], ![![6462, -147, -199]]]
  g := ![![![-31610, 97891, 18328], ![-168831, 522842, 97891], ![-901737, 2792532, 522842]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-6952, -274, 295]] ![![449530, 97891, 18328]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [36, 82, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [22, 78, 14], [81, 22, 87], [0, 1]]
 g := ![![[5, 79, 17], [38, 4], [69, 13, 36], [15, 17], [84, 4], [1]], ![[79, 48, 21, 47], [54, 82], [53, 58, 48, 13], [78, 36], [36, 49], [18, 13, 44, 17]], ![[77, 63, 24, 17], [72, 76], [34, 73, 88, 82], [1, 30], [78, 81], [71, 59, 75, 84]]]
 h' := ![![[22, 78, 14], [10, 82, 44], [41, 58, 2], [86, 47, 95], [90, 84, 57], [65, 19, 2], [0, 1]], ![[81, 22, 87], [98, 70, 96], [27, 22, 48], [41, 2, 21], [18, 51, 6], [1, 10, 7], [22, 78, 14]], ![[0, 1], [15, 50, 62], [53, 21, 51], [74, 52, 86], [98, 67, 38], [49, 72, 92], [81, 22, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13, 94], []]
 b := ![[], [66, 35, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [36, 82, 99, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147056, -13130, 202]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1456, -130, 2]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-75306723, -16399018, -3070366]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![-75306723, -16399018, -3070366]] 
 ![![103, 0, 0], ![9, 1, 0], ![22, 0, 1]] where
  M :=![![![-75306723, -16399018, -3070366], ![-402217946, -87588187, -16399018], ![-2148271358, -467814018, -87588187]]]
  hmulB := by decide  
  f := ![![![-112645, 9778, 2118]], ![![-7149, -157, 280]], ![![-11624, 5162, -559]]]
  g := ![![![1357597, -16399018, -3070366], ![7251011, -87588187, -16399018], ![38728106, -467814018, -87588187]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![325767, 70940, 13282]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![325767, 70940, 13282]] 
 ![![103, 0, 0], ![25, 1, 0], ![96, 0, 1]] where
  M :=![![![325767, 70940, 13282], ![1739942, 378895, 70940], ![9293140, 2023702, 378895]]]
  hmulB := by decide  
  f := ![![![1145, -1336, 210]], ![![545, -305, 38]], ![![-632, -1030, 215]]]
  g := ![![![-26435, 70940, 13282], ![-141191, 378895, 70940], ![-754110, 2023702, 378895]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2239511, -2105346, 315676]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![2239511, -2105346, 315676]] 
 ![![103, 0, 0], ![69, 1, 0], ![80, 0, 1]] where
  M :=![![![2239511, -2105346, 315676], ![41353556, 3502215, -2105346], ![-275800326, 32932172, 3502215]]]
  hmulB := by decide  
  f := ![![![81599126497737, 17769270669662, 3326916557376]], ![![58894813566603, 12825111348873, 2401228282802]], ![![85977714345094, 18722765099688, 3505438032207]]]
  g := ![![![1186935, -2105346, 315676], ![-309433, 3502215, -2105346], ![-27459198, 32932172, 3502215]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![-75306723, -16399018, -3070366]] ![![325767, 70940, 13282]]
  ![![-81599126497737, -17769270669662, -3326916557376]] where
 M := ![![![-81599126497737, -17769270669662, -3326916557376]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![-81599126497737, -17769270669662, -3326916557376]] ![![2239511, -2105346, 315676]]
  ![![103, 0, 0]] where
 M := ![![![-103, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC103 : ContainsPrimesAboveP 103 ![I103N0, I103N1, I103N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
    exact isPrimeI103N1
    exact isPrimeI103N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 103 (by decide) (𝕀 ⊙ MulI103N0 ⊙ MulI103N1)
instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![105, 22, 4]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![105, 22, 4]] 
 ![![107, 0, 0], ![0, 107, 0], ![53, 59, 1]] where
  M :=![![![105, 22, 4], ![524, 121, 22], ![2882, 612, 121]]]
  hmulB := by decide  
  f := ![![![11, -2, 0]], ![![0, 11, -2]], ![![3, 5, -1]]]
  g := ![![![-1, -2, 4], ![-6, -11, 22], ![-33, -61, 121]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [29, 17, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 106], [0, 1]]
 g := ![![[67, 48], [98, 75], [49], [97, 61], [83], [90, 1]], ![[0, 59], [0, 32], [49], [23, 46], [83], [73, 106]]]
 h' := ![![[90, 106], [47, 72], [75, 17], [76, 7], [106, 75], [65, 46], [0, 1]], ![[0, 1], [0, 35], [0, 90], [64, 100], [8, 32], [32, 61], [90, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [50, 94]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [29, 17, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-739, 1174, -20]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, 22, -20]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, -2, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![11, -2, 0]] 
 ![![107, 0, 0], ![48, 1, 0], ![50, 0, 1]] where
  M :=![![![11, -2, 0], ![0, 11, -2], ![-262, -8, 11]]]
  hmulB := by decide  
  f := ![![![105, 22, 4]], ![![52, 11, 2]], ![![76, 16, 3]]]
  g := ![![![1, -2, 0], ![-4, 11, -2], ![-4, -8, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![105, 22, 4]] ![![11, -2, 0]]
  ![![107, 0, 0]] where
 M := ![![![107, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC107 : ContainsPrimesAboveP 107 ![I107N0, I107N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
    exact isPrimeI107N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 107 (by decide) (𝕀 ⊙ MulI107N0)
instance hp109 : Fact (Nat.Prime 109) := {out := by norm_num}

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3141912238, 684192238, 128100389]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![3141912238, 684192238, 128100389]] 
 ![![109, 0, 0], ![0, 109, 0], ![42, 68, 1]] where
  M :=![![![3141912238, 684192238, 128100389], ![16781150959, 3654313794, 684192238], ![89629183178, 19517919911, 3654313794]]]
  hmulB := by decide  
  f := ![![![62602, -10877, -158]], ![![-20698, 61970, -10877]], ![![-1863, 33880, -6278]]]
  g := ![![![-20534900, -73638846, 128100389], ![-109678193, -393309710, 684192238], ![-585798130, -2100691909, 3654313794]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [40, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 108], [0, 1]]
 g := ![![[90, 87], [82], [16, 84], [64, 43], [89], [106, 1]], ![[47, 22], [82], [91, 25], [44, 66], [89], [103, 108]]]
 h' := ![![[106, 108], [77, 95], [14, 55], [56, 53], [49, 32], [11, 78], [0, 1]], ![[0, 1], [10, 14], [67, 54], [6, 56], [62, 77], [104, 31], [106, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [39, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [40, 3, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![302, 136, 2]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 0, 2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-62602, 10877, 158]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![-62602, 10877, 158]] 
 ![![109, 0, 0], ![41, 1, 0], ![63, 0, 1]] where
  M :=![![![-62602, 10877, 158], ![20698, -61970, 10877], ![1424887, 64206, -61970]]]
  hmulB := by decide  
  f := ![![![-3141912238, -684192238, -128100389]], ![![-1335775713, -290882528, -54461543]], ![![-2638253708, -574514045, -107565489]]]
  g := ![![![-4757, 10877, 158], ![17213, -61970, 10877], ![24739, 64206, -61970]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![3141912238, 684192238, 128100389]] ![![-62602, 10877, 158]]
  ![![109, 0, 0]] where
 M := ![![![-109, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1244593846, -271026491, -50743924]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-1244593846, -271026491, -50743924]] 
 ![![113, 0, 0], ![0, 113, 0], ![65, 42, 1]] where
  M :=![![![-1244593846, -271026491, -50743924], ![-6647454044, -1447569542, -271026491], ![-35504470321, -7731560008, -1447569542]]]
  hmulB := by decide  
  f := ![![![-16972, -5790, 1679]], ![![219949, -10256, -5790]], ![![65276, -5401, -1277]]]
  g := ![![![18174878, 16462109, -50743924], ![97073167, 87925160, -271026491], ![518473893, 469613812, -1447569542]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [48, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 112], [0, 1]]
 g := ![![[72, 106], [81], [30], [1], [58, 83], [47, 1]], ![[82, 7], [81], [30], [1], [4, 30], [94, 112]]]
 h' := ![![[47, 112], [11, 85], [31, 104], [51, 16], [41, 1], [4, 14], [0, 1]], ![[0, 1], [51, 28], [60, 9], [12, 97], [88, 112], [97, 99], [47, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [77, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [48, 66, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5093, 1575, 433]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-204, -147, 433]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16972, 5790, -1679]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![16972, 5790, -1679]] 
 ![![113, 0, 0], ![71, 1, 0], ![44, 0, 1]] where
  M :=![![![16972, 5790, -1679], ![-219949, 10256, 5790], ![758490, -196789, 10256]]]
  hmulB := by decide  
  f := ![![![1244593846, 271026491, 50743924]], ![![840828470, 183101331, 34281815]], ![![798819465, 173953324, 32569046]]]
  g := ![![![-2834, 5790, -1679], ![-10645, 10256, 5790], ![126365, -196789, 10256]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-1244593846, -271026491, -50743924]] ![![16972, 5790, -1679]]
  ![![113, 0, 0]] where
 M := ![![![-113, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![48786, -236375, 42546]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![48786, -236375, 42546]] 
 ![![127, 0, 0], ![0, 127, 0], ![18, 99, 1]] where
  M :=![![![48786, -236375, 42546], ![5573526, 218970, -236375], ![-30965125, 4628026, 218970]]]
  hmulB := by decide  
  f := ![![![-8991318950, -1957976598, -366589315]], ![![-48023200265, -10457676210, -1957976598]], ![![-40729413399, -8869359293, -1660598166]]]
  g := ![![![-5646, -35027, 42546], ![77388, 185985, -236375], ![-274855, -134252, 218970]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [20, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 126], [0, 1]]
 g := ![![[46, 44], [1, 2], [38, 47], [88, 99], [87, 37], [96, 1]], ![[79, 83], [66, 125], [105, 80], [67, 28], [83, 90], [65, 126]]]
 h' := ![![[96, 126], [107, 60], [2, 111], [18, 38], [38, 90], [112, 52], [0, 1]], ![[0, 1], [25, 67], [117, 16], [110, 89], [42, 37], [24, 75], [96, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [64]]
 b := ![[], [115, 32]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [20, 31, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-796, 194, -16]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, 14, -16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![8991318950, 1957976598, 366589315]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![8991318950, 1957976598, 366589315]] 
 ![![127, 0, 0], ![28, 1, 0], ![105, 0, 1]] where
  M :=![![![8991318950, 1957976598, 366589315], ![48023200265, 10457676210, 1957976598], ![256494934338, 55855106657, 10457676210]]]
  hmulB := by decide  
  f := ![![![-48786, 236375, -42546]], ![![-54642, 50390, -7519]], ![![203485, 158987, -36900]]]
  g := ![![![-663967747, 1957976598, 366589315], ![-3546293515, 10457676210, 1957976598], ![-18940976804, 55855106657, 10457676210]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![48786, -236375, 42546]] ![![8991318950, 1957976598, 366589315]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![131, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![131, 4, 0]]]
  hmulB := by decide  
  f := ![![![-4, 0, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 4, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N0 : Nat.card (O ⧸ I131N0) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N0)

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := prime_ideal_of_norm_prime hp131.out _ NI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![2, 1, 0]] 
 ![![131, 0, 0], ![2, 1, 0], ![127, 0, 1]] where
  M :=![![![2, 1, 0], ![0, 2, 1], ![131, 4, 2]]]
  hmulB := by decide  
  f := ![![![0, -2, 1]], ![![1, 0, 0]], ![![-2, -1, 1]]]
  g := ![![![0, 1, 0], ![-1, 2, 1], ![-1, 4, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1

def I131N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, 0]] i)))

def SI131N2: IdealEqSpanCertificate' Table ![![-2, 1, 0]] 
 ![![131, 0, 0], ![129, 1, 0], ![127, 0, 1]] where
  M :=![![![-2, 1, 0], ![0, -2, 1], ![131, 4, -2]]]
  hmulB := by decide  
  f := ![![![0, 2, 1]], ![![1, 2, 1]], ![![2, 3, 1]]]
  g := ![![![-1, 1, 0], ![1, -2, 1], ![-1, 4, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N2 : Nat.card (O ⧸ I131N2) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N2)

lemma isPrimeI131N2 : Ideal.IsPrime I131N2 := prime_ideal_of_norm_prime hp131.out _ NI131N2
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![2, 1, 0]]
  ![![0, 2, 1]] where
 M := ![![![0, 2, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI131N1 : IdealMulLeCertificate' Table 
  ![![0, 2, 1]] ![![-2, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1, I131N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
    exact isPrimeI131N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0 ⊙ MulI131N1)
instance hp137 : Fact (Nat.Prime 137) := {out := by norm_num}

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-314, -32, 17]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![-314, -32, 17]] 
 ![![137, 0, 0], ![0, 137, 0], ![46, 119, 1]] where
  M :=![![![-314, -32, 17], ![2227, -246, -32], ![-4192, 2099, -246]]]
  hmulB := by decide  
  f := ![![![932, 203, 38]], ![![4978, 1084, 203]], ![![4831, 1052, 197]]]
  g := ![![![-8, -15, 17], ![27, 26, -32], ![52, 229, -246]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [28, 66, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [71, 136], [0, 1]]
 g := ![![[110, 93], [103], [135], [10, 63], [123], [109], [1]], ![[0, 44], [103], [135], [99, 74], [123], [109], [1]]]
 h' := ![![[71, 136], [100, 97], [92, 68], [131, 51], [3, 101], [61, 64], [109, 71], [0, 1]], ![[0, 1], [0, 40], [125, 69], [53, 86], [50, 36], [84, 73], [81, 66], [71, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [22, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [28, 66, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![552, 606, 149]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-46, -125, 149]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![932, 203, 38]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![932, 203, 38]] 
 ![![137, 0, 0], ![18, 1, 0], ![87, 0, 1]] where
  M :=![![![932, 203, 38], ![4978, 1084, 203], ![26593, 5790, 1084]]]
  hmulB := by decide  
  f := ![![![-314, -32, 17]], ![![-25, -6, 2]], ![![-230, -5, 9]]]
  g := ![![![-44, 203, 38], ![-235, 1084, 203], ![-1255, 5790, 1084]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![-314, -32, 17]] ![![932, 203, 38]]
  ![![137, 0, 0]] where
 M := ![![![137, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0)


lemma PB193I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB193I2 : PrimesBelowBoundCertificateInterval O 79 137 193 where
  m := 11
  g := ![3, 2, 2, 1, 3, 2, 2, 2, 2, 3, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB193I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1, I83N2]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1, I131N2]
    · exact ![I137N0, I137N1]
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
    · exact ![83, 83, 83]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![131, 131, 131]
    · exact ![18769, 137]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
      exact NI83N1
      exact NI83N2
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
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
      exact NI103N2
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
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
      exact NI131N1
      exact NI131N2
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N0, I83N1, I83N2, I89N1, I97N1, I103N0, I103N1, I103N2, I107N1, I109N1, I113N1, I127N1, I131N0, I131N1, I131N2, I137N1]
  Il := ![[I83N0, I83N1, I83N2], [I89N1], [I97N1], [], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [I113N1], [I127N1], [I131N0, I131N1, I131N2], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
