
import IdealArithmetic.Examples.NF3_1_853335_1.RI3_1_853335_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-29, -31, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-29, -31, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![54, 52, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-29, -31, 1], ![-6, 68, -369], ![-5488, -108, -117]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -52, 83]], ![![-1, -1, 1], ![240, 232, -369], ![10, 72, -117]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [78, 61, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 82], [0, 1]]
 g := ![![[21, 33], [32, 21], [41], [38], [78, 69], [1]], ![[0, 50], [79, 62], [41], [38], [19, 14], [1]]]
 h' := ![![[22, 82], [77, 38], [15, 41], [68, 37], [58, 11], [5, 22], [0, 1]], ![[0, 1], [0, 45], [4, 42], [52, 46], [51, 72], [74, 61], [22, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [59, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [78, 61, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1062, 580, -174]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![126, 116, -174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![37, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![37, 1, 0]] 
 ![![83, 0, 0], ![37, 1, 0], ![34, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![37, 1, 0], ![6, 34, 12], ![180, 4, 40]]]
  hmulB := by decide  
  f := ![![![-2360, -16509, -5832], ![-1245, 40338, 0]], ![![-1074, -7338, -2592], ![-497, 17928, 0]], ![![-977, -6763, -2389], ![-487, 16524, 0]]]
  g := ![![![1, 0, 0], ![-37, 83, 0], ![-34, 0, 83]], ![![0, 1, 0], ![-20, 34, 12], ![-16, 4, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-29, -31, 1]] ![![83, 0, 0], ![37, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![3071, 83, 0]], ![![-2407, -2573, 83], ![-1079, -1079, -332]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![37, 1, 0]]], ![![![-29, -31, 1]], ![![-13, -13, -4]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-46, 9, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-46, 9, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![43, 9, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-46, 9, 1], ![234, -69, 111], ![1712, 52, -14]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -9, 89]], ![![-1, 0, 1], ![-51, -12, 111], ![26, 2, -14]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [35, 34, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 88], [0, 1]]
 g := ![![[62, 69], [36], [71], [44, 16], [11, 88], [1]], ![[30, 20], [36], [71], [34, 73], [45, 1], [1]]]
 h' := ![![[55, 88], [28, 43], [24, 6], [62, 31], [60, 85], [54, 55], [0, 1]], ![[0, 1], [79, 46], [87, 83], [76, 58], [18, 4], [53, 34], [55, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [52, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [35, 34, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2852, 469, 507]
  a := ![3, -3, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-277, -46, 507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-22, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-22, 1, 0]] 
 ![![89, 0, 0], ![67, 1, 0], ![14, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-22, 1, 0], ![6, -25, 12], ![180, 4, -19]]]
  hmulB := by decide  
  f := ![![![-435, 1998, -960], ![178, 7120, 0]], ![![-315, 1498, -720], ![179, 5340, 0]], ![![-62, 314, -151], ![54, 1120, 0]]]
  g := ![![![1, 0, 0], ![-67, 89, 0], ![-14, 0, 89]], ![![-1, 1, 0], ![17, -25, 12], ![2, 4, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-46, 9, 1]] ![![89, 0, 0], ![-22, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-1958, 89, 0]], ![![-4094, 801, 89], ![1246, -267, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-22, 1, 0]]], ![![![-46, 9, 1]], ![![14, -3, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![41, -40, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![41, -40, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![41, 57, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![41, -40, 1], ![-60, 165, -477], ![-7108, -144, -74]]]
  hmulB := by decide  
  f := ![![![-40, 40, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-41, -57, 97]], ![![0, -1, 1], ![201, 282, -477], ![-42, 42, -74]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [39, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [10, 96], [0, 1]]
 g := ![![[47, 95], [12], [12], [81], [35], [10, 1]], ![[27, 2], [12], [12], [81], [35], [20, 96]]]
 h' := ![![[10, 96], [18, 80], [96, 20], [51, 77], [94, 9], [95, 61], [0, 1]], ![[0, 1], [42, 17], [5, 77], [45, 20], [87, 88], [26, 36], [10, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [7]]
 b := ![[], [31, 52]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [39, 87, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![375607, 69122, 24234]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6371, -13528, 24234]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-8, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-8, 1, 0]] 
 ![![97, 0, 0], ![89, 1, 0], ![74, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-8, 1, 0], ![6, -11, 12], ![180, 4, -5]]]
  hmulB := by decide  
  f := ![![![-6423, 11873, -12960], ![679, 104760, 0]], ![![-5883, 10883, -11880], ![680, 96030, 0]], ![![-4894, 9057, -9887], ![591, 79920, 0]]]
  g := ![![![1, 0, 0], ![-89, 97, 0], ![-74, 0, 97]], ![![-1, 1, 0], ![1, -11, 12], ![2, 4, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![41, -40, 1]] ![![97, 0, 0], ![-8, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-776, 97, 0]], ![![3977, -3880, 97], ![-388, 485, -485]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-8, 1, 0]]], ![![![41, -40, 1]], ![![-4, 5, -5]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [86, 62, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 54, 37], [49, 46, 64], [0, 1]]
 g := ![![[4, 39, 13], [38, 37], [34, 81, 25], [70, 68], [25, 64], [1]], ![[43, 87, 18, 20], [65, 70], [46, 74, 60, 31], [92, 85], [74, 49], [100, 12, 95, 52]], ![[3, 37, 88, 95], [78, 25], [95, 55, 26, 95], [60, 82], [16, 1], [83, 9, 40, 49]]]
 h' := ![![[60, 54, 37], [90, 64, 35], [5, 35, 80], [76, 22, 96], [95, 75, 13], [15, 39, 8], [0, 1]], ![[49, 46, 64], [44, 86, 39], [33, 74, 26], [61, 39, 79], [87, 28, 40], [47, 66, 94], [60, 54, 37]], ![[0, 1], [63, 52, 27], [2, 93, 96], [62, 40, 27], [24, 99, 48], [17, 97, 100], [49, 46, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 43], []]
 b := ![[], [92, 3, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [86, 62, 93, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1966066, -16968, 50904]
  a := ![-4, 3, -9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-19466, -168, 504]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-20, -6, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-20, -6, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![83, 97, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-20, -6, 1], ![144, 2, -69], ![-988, -8, -33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -97, 103]], ![![-1, -1, 1], ![57, 65, -69], ![17, 31, -33]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [9, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 102], [0, 1]]
 g := ![![[21, 23], [7, 15], [59, 60], [16], [17], [17, 1]], ![[0, 80], [56, 88], [49, 43], [16], [17], [34, 102]]]
 h' := ![![[17, 102], [40, 34], [87, 85], [31, 36], [81, 99], [53, 74], [0, 1]], ![[0, 1], [0, 69], [90, 18], [25, 67], [13, 4], [75, 29], [17, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [42, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [9, 86, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![918, 605, -324]
  a := ![-3, 1, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![270, 311, -324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-34, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-34, 1, 0]] 
 ![![103, 0, 0], ![69, 1, 0], ![33, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-34, 1, 0], ![6, -37, 12], ![180, 4, -31]]]
  hmulB := by decide  
  f := ![![![-235, 1664, -540], ![103, 4635, 0]], ![![-145, 1109, -360], ![104, 3090, 0]], ![![-71, 533, -173], ![46, 1485, 0]]]
  g := ![![![1, 0, 0], ![-69, 103, 0], ![-33, 0, 103]], ![![-1, 1, 0], ![21, -37, 12], ![9, 4, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-20, -6, 1]] ![![103, 0, 0], ![-34, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3502, 103, 0]], ![![-2060, -618, 103], ![824, 206, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-34, 1, 0]]], ![![![-20, -6, 1]], ![![8, 2, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-43, 32, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-43, 32, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![64, 32, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-43, 32, 1], ![372, -135, 387], ![5852, 144, 58]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-64, -32, 107]], ![![-1, 0, 1], ![-228, -117, 387], ![20, -16, 58]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [4, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 106], [0, 1]]
 g := ![![[98, 27], [49, 13], [44], [], [64], [36, 1]], ![[0, 80], [89, 94], [44], [], [64], [72, 106]]]
 h' := ![![[36, 106], [18, 53], [38, 86], [0, 30], [43], [70, 8], [0, 1]], ![[0, 1], [0, 54], [31, 21], [10, 77], [43], [37, 99], [36, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [1]]
 b := ![[], [98, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [4, 71, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![156684, 29122, 13944]
  a := ![22, -1, 43]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6876, -3898, 13944]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![41, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![41, 1, 0]] 
 ![![107, 0, 0], ![41, 1, 0], ![49, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![41, 1, 0], ![6, 38, 12], ![180, 4, 44]]]
  hmulB := by decide  
  f := ![![![19681, 146368, 46248], ![8988, -412378, 0]], ![![7544, 56056, 17712], ![3425, -157932, 0]], ![![8999, 67028, 21179], ![4152, -188846, 0]]]
  g := ![![![1, 0, 0], ![-41, 107, 0], ![-49, 0, 107]], ![![0, 1, 0], ![-20, 38, 12], ![-20, 4, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-43, 32, 1]] ![![107, 0, 0], ![41, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![4387, 107, 0]], ![![-4601, 3424, 107], ![-1391, 1177, 428]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![41, 1, 0]]], ![![![-43, 32, 1]], ![![-13, 11, 4]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0]] 
 ![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [64, 13, 100, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 59, 66], [85, 49, 43], [0, 1]]
 g := ![![[8, 89, 105], [51, 43], [31, 91, 7], [51, 59, 5], [59, 81], [1]], ![[37, 6, 49, 78], [49, 43], [56, 90, 10, 60], [101, 86, 72, 106], [28, 34], [0, 54, 77, 63]], ![[40, 8, 32, 71], [], [102, 61, 93, 94], [30, 71, 40, 89], [61, 21], [64, 37, 44, 46]]]
 h' := ![![[33, 59, 66], [54, 86, 66], [87, 22, 32], [6, 79, 94], [102, 73, 21], [45, 96, 9], [0, 1]], ![[85, 49, 43], [16, 7, 81], [99, 70, 77], [66, 100, 10], [60, 54, 70], [76, 73, 19], [33, 59, 66]], ![[0, 1], [27, 16, 71], [71, 17], [50, 39, 5], [103, 91, 18], [65, 49, 81], [85, 49, 43]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [108, 88], []]
 b := ![[], [35, 82, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [64, 13, 100, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![56026, 3052, 3270]
  a := ![0, 1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![514, 28, 30]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 1295029 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def PBC109 : ContainsPrimesAboveP 109 ![I109N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![109, 0, 0]]) timesTableT_eq_Table B_one_repr 109 (by decide) 𝕀

instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![26, 1, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![26, 1, 0]] 
 ![![113, 0, 0], ![26, 1, 0], ![26, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![26, 1, 0], ![6, 23, 12], ![180, 4, 29]]]
  hmulB := by decide  
  f := ![![![26563, 108037, 56400], ![7119, -531100, 0]], ![![6096, 24848, 12972], ![1696, -122153, 0]], ![![6110, 24858, 12977], ![1646, -122200, 0]]]
  g := ![![![1, 0, 0], ![-26, 113, 0], ![-26, 0, 113]], ![![0, 1, 0], ![-8, 23, 12], ![-6, 4, 29]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-24, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-24, 1, 0]] 
 ![![113, 0, 0], ![89, 1, 0], ![3, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-24, 1, 0], ![6, -27, 12], ![180, 4, -21]]]
  hmulB := by decide  
  f := ![![![34633, -164083, 72960], ![-8701, -687040, 0]], ![![27265, -129215, 57456], ![-6892, -541044, 0]], ![![939, -4357, 1937], ![-139, -18240, 0]]]
  g := ![![![1, 0, 0], ![-89, 113, 0], ![-3, 0, 113]], ![![-1, 1, 0], ![21, -27, 12], ![-1, 4, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-2, 1, 0]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-2, 1, 0]] 
 ![![113, 0, 0], ![111, 1, 0], ![75, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-2, 1, 0], ![6, -5, 12], ![180, 4, 1]]]
  hmulB := by decide  
  f := ![![![18809, -15676, 37632], ![-452, -354368, 0]], ![![18473, -15396, 36960], ![-451, -348040, 0]], ![![12485, -10405, 24977], ![-235, -235200, 0]]]
  g := ![![![1, 0, 0], ![-111, 113, 0], ![-75, 0, 113]], ![![-1, 1, 0], ![-3, -5, 12], ![-3, 4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![26, 1, 0]] ![![113, 0, 0], ![-24, 1, 0]]
  ![![113, 0, 0], ![5, 47, 1]] where
 M := ![![![12769, 0, 0], ![-2712, 113, 0]], ![![2938, 113, 0], ![-618, -1, 12]]]
 hmul := by decide  
 g := ![![![![108, -47, -1], ![113, 0, 0]], ![![-24, 1, 0], ![0, 0, 0]]], ![![![21, -46, -1], ![113, 0, 0]], ![![-6, -5, 0], ![12, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![5, 47, 1]] ![![113, 0, 0], ![-2, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-226, 113, 0]], ![![565, 5311, 113], ![452, -226, 565]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-2, 1, 0]]], ![![![5, 47, 1]], ![![4, -2, 5]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)
instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![14, 62, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![14, 62, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![14, 62, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![14, 62, 1], ![552, -168, 747], ![11252, 264, 205]]]
  hmulB := by decide  
  f := ![![![-13, -62, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-14, -62, 127]], ![![0, 0, 1], ![-78, -366, 747], ![66, -98, 205]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [101, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [52, 126], [0, 1]]
 g := ![![[2, 47], [30, 84], [7, 88], [85, 72], [58, 32], [52, 1]], ![[33, 80], [80, 43], [11, 39], [19, 55], [71, 95], [104, 126]]]
 h' := ![![[52, 126], [18, 38], [55, 46], [51, 71], [111, 31], [82, 63], [0, 1]], ![[0, 1], [89, 89], [34, 81], [60, 56], [72, 96], [56, 64], [52, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36]]
 b := ![[], [40, 18]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [101, 75, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2525, 1258, 1278]
  a := ![5, -2, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-121, -614, 1278]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![15, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![15, 1, 0]] 
 ![![127, 0, 0], ![15, 1, 0], ![49, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![15, 1, 0], ![6, 12, 12], ![180, 4, 18]]]
  hmulB := by decide  
  f := ![![![-2417, -4894, -4896], ![-254, 51816, 0]], ![![-288, -576, -576], ![1, 6096, 0]], ![![-944, -1889, -1889], ![-1, 19992, 0]]]
  g := ![![![1, 0, 0], ![-15, 127, 0], ![-49, 0, 127]], ![![0, 1, 0], ![-6, 12, 12], ![-6, 4, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![14, 62, 1]] ![![127, 0, 0], ![15, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![1905, 127, 0]], ![![1778, 7874, 127], ![762, 762, 762]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![15, 1, 0]]], ![![![14, 62, 1]], ![![6, 6, 6]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-60, 6, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-60, 6, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![71, 6, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-60, 6, 1], ![216, -74, 75], ![1172, 40, -37]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-71, -6, 131]], ![![-1, 0, 1], ![-39, -4, 75], ![29, 2, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [115, 109, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [22, 130], [0, 1]]
 g := ![![[116, 112], [109, 35], [34], [65], [60], [91], [1]], ![[91, 19], [93, 96], [34], [65], [60], [91], [1]]]
 h' := ![![[22, 130], [41, 80], [129, 67], [41, 54], [124, 117], [9, 86], [16, 22], [0, 1]], ![[0, 1], [98, 51], [31, 64], [50, 77], [78, 14], [67, 45], [107, 109], [22, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109]]
 b := ![[], [121, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [115, 109, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1895, 400, -370]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![215, 20, -370]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![56, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![56, 1, 0]] 
 ![![131, 0, 0], ![56, 1, 0], ![37, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![56, 1, 0], ![6, 53, 12], ![180, 4, 59]]]
  hmulB := by decide  
  f := ![![![24385, 262784, 59520], ![12576, -649760, 0]], ![![10424, 112319, 25440], ![5372, -277720, 0]], ![![6863, 74221, 16811], ![3609, -183520, 0]]]
  g := ![![![1, 0, 0], ![-56, 131, 0], ![-37, 0, 131]], ![![0, 1, 0], ![-26, 53, 12], ![-17, 4, 59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-60, 6, 1]] ![![131, 0, 0], ![56, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![7336, 131, 0]], ![![-7860, 786, 131], ![-3144, 262, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![56, 1, 0]]], ![![![-60, 6, 1]], ![![-24, 2, 1]]]]
 hle2 := by decide  


def PBC131 : ContainsPrimesAboveP 131 ![I131N0, I131N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI131N0
    exact isPrimeI131N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 131 (by decide) (𝕀 ⊙ MulI131N0)
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [51, 55, 102, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 128, 76], [80, 8, 61], [0, 1]]
 g := ![![[17, 129, 100], [70, 9], [104, 77], [97, 78, 121], [44, 133], [35, 1], []], ![[88, 31, 32, 64], [42, 128], [88, 100], [25, 117, 99, 61], [87, 126], [11, 64], [87, 22]], ![[19, 23, 109, 109], [35, 19], [70, 129], [88, 25, 136, 136], [106, 68], [2, 81], [102, 22]]]
 h' := ![![[92, 128, 76], [92, 126, 10], [127, 18, 134], [122, 66, 25], [101, 29, 11], [133, 79, 74], [0, 0, 1], [0, 1]], ![[80, 8, 61], [31, 93, 66], [114, 59, 111], [9, 76, 10], [75, 116, 100], [26, 94, 20], [54, 109, 8], [92, 128, 76]], ![[0, 1], [95, 55, 61], [28, 60, 29], [6, 132, 102], [118, 129, 26], [27, 101, 43], [102, 28, 128], [80, 8, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46, 61], []]
 b := ![[], [113, 15, 1], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [51, 55, 102, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2542857, -45758, -228790]
  a := ![-4, -2, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18561, -334, -1670]
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



lemma PB262I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB262I2 : PrimesBelowBoundCertificateInterval O 79 137 262 where
  m := 11
  g := ![2, 2, 2, 1, 2, 2, 1, 3, 2, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB262I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0]
    · exact ![I113N0, I113N1, I113N2]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![1295029]
    · exact ![113, 113, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I83N1, I89N1, I97N1, I103N1, I107N1, I113N0, I113N1, I113N2, I127N1, I131N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [I107N1], [], [I113N0, I113N1, I113N2], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
