
import IdealArithmetic.Examples.NF3_3_240149_1.RI3_3_240149_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [67, 25, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 75, 34], [11, 7, 49], [0, 1]]
 g := ![![[10, 36, 33], [15, 40, 75], [43, 21], [50, 12], [0, 5, 1], []], ![[26, 28, 51, 52], [9, 1, 77, 42], [66, 61], [17, 63], [17, 72, 2, 6], [7, 77]], ![[55, 43, 73, 23], [48, 46, 1, 36], [44, 11], [28, 69], [69, 17, 25, 65], [75, 77]]]
 h' := ![![[77, 75, 34], [74, 54, 38], [11, 76, 18], [53, 21, 42], [0, 80, 57], [0, 0, 1], [0, 1]], ![[11, 7, 49], [62, 56, 27], [61, 60, 54], [1, 35, 12], [71, 9, 48], [65, 74, 7], [77, 75, 34]], ![[0, 1], [70, 56, 18], [57, 30, 11], [73, 27, 29], [66, 77, 61], [76, 9, 75], [11, 7, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50, 18], []]
 b := ![[], [74, 77, 19], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [67, 25, 78, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![27639, -3818, -25730]
  a := ![-1, -1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![333, -46, -310]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 571787 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def PBC83 : ContainsPrimesAboveP 83 ![I83N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI83N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![83, 0, 0]]) timesTableT_eq_Table B_one_repr 83 (by decide) 𝕀

instance hp89 : Fact (Nat.Prime 89) := {out := by norm_num}

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-2, -20, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-2, -20, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![87, 69, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-2, -20, 1], ![-69, 22, -99], ![975, -485, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -69, 89]], ![![-1, -1, 1], ![96, 77, -99], ![9, -7, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [33, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 88], [0, 1]]
 g := ![![[85, 34], [64], [18], [23, 4], [40, 69], [1]], ![[34, 55], [64], [18], [17, 85], [70, 20], [1]]]
 h' := ![![[43, 88], [15, 52], [13, 81], [42, 14], [15, 87], [56, 43], [0, 1]], ![[0, 1], [26, 37], [25, 8], [21, 75], [18, 2], [36, 46], [43, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [53, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [33, 46, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1684, -1761, 3430]
  a := ![2, -2, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3334, -2679, 3430]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![10, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![10, 1, 0]] 
 ![![89, 0, 0], ![10, 1, 0], ![87, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![10, 1, 0], ![1, 10, 5], ![-49, 24, 11]]]
  hmulB := by decide  
  f := ![![![0, 89, 45], ![89, -801, 0]], ![![1, 10, 5], ![1, -89, 0]], ![![0, 87, 44], ![87, -783, 0]]]
  g := ![![![1, 0, 0], ![-10, 89, 0], ![-87, 0, 89]], ![![0, 1, 0], ![-6, 10, 5], ![-14, 24, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-2, -20, 1]] ![![89, 0, 0], ![10, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![890, 89, 0]], ![![-178, -1780, 89], ![-89, -178, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![10, 1, 0]]], ![![![-2, -20, 1]], ![![-1, -2, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![11, 42, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![11, 42, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![11, 42, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![11, 42, 1], ![-7, 35, 211], ![-2063, 1003, 77]]]
  hmulB := by decide  
  f := ![![![-10, -42, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-11, -42, 97]], ![![0, 0, 1], ![-24, -91, 211], ![-30, -23, 77]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [4, 46, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [51, 96], [0, 1]]
 g := ![![[60, 73], [65], [54], [1], [96], [51, 1]], ![[0, 24], [65], [54], [1], [96], [5, 96]]]
 h' := ![![[51, 96], [23, 49], [63, 68], [45, 65], [7, 1], [87, 75], [0, 1]], ![[0, 1], [0, 48], [39, 29], [62, 32], [58, 96], [32, 22], [51, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [47, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [4, 46, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-313787, -353217, 1656311]
  a := ![-65, 1, -261]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-191064, -720807, 1656311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-17, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-17, 1, 0]] 
 ![![97, 0, 0], ![80, 1, 0], ![20, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-17, 1, 0], ![1, -17, 5], ![-49, 24, -16]]]
  hmulB := by decide  
  f := ![![![-3158, 57159, -16815], ![1164, 326211, 0]], ![![-2602, 47131, -13865], ![971, 268981, 0]], ![![-645, 11785, -3467], ![275, 67260, 0]]]
  g := ![![![1, 0, 0], ![-80, 97, 0], ![-20, 0, 97]], ![![-1, 1, 0], ![13, -17, 5], ![-17, 24, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![11, 42, 1]] ![![97, 0, 0], ![-17, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1649, 97, 0]], ![![1067, 4074, 97], ![-194, -679, 194]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-17, 1, 0]]], ![![![11, 42, 1]], ![![-2, -7, 2]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-5, 25, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-5, 25, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![96, 25, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-5, 25, 1], ![-24, 19, 126], ![-1230, 595, 44]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-96, -25, 101]], ![![-1, 0, 1], ![-120, -31, 126], ![-54, -5, 44]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [81, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 100], [0, 1]]
 g := ![![[57, 5], [16], [48, 76], [70], [82], [29, 1]], ![[0, 96], [16], [30, 25], [70], [82], [58, 100]]]
 h' := ![![[29, 100], [93, 56], [51, 97], [35, 50], [94, 26], [75, 53], [0, 1]], ![[0, 1], [0, 45], [36, 4], [71, 51], [40, 75], [97, 48], [29, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [67]]
 b := ![[], [95, 84]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [81, 72, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![415, -1065, 2139]
  a := ![-2, 1, -11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2029, -540, 2139]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-25, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-25, 1, 0]] 
 ![![101, 0, 0], ![76, 1, 0], ![57, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-25, 1, 0], ![1, -25, 5], ![-49, 24, -24]]]
  hmulB := by decide  
  f := ![![![-2, 699, -140], ![101, 2828, 0]], ![![5, 524, -105], ![102, 2121, 0]], ![![11, 394, -79], ![106, 1596, 0]]]
  g := ![![![1, 0, 0], ![-76, 101, 0], ![-57, 0, 101]], ![![-1, 1, 0], ![16, -25, 5], ![-5, 24, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-5, 25, 1]] ![![101, 0, 0], ![-25, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-2525, 101, 0]], ![![-505, 2525, 101], ![101, -606, 101]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-25, 1, 0]]], ![![![-5, 25, 1]], ![![1, -6, 1]]]]
 hle2 := by decide  


def PBC101 : ContainsPrimesAboveP 101 ![I101N0, I101N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI101N0
    exact isPrimeI101N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 101 (by decide) (𝕀 ⊙ MulI101N0)
instance hp103 : Fact (Nat.Prime 103) := {out := by norm_num}

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [77, 76, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [9, 77, 75], [56, 25, 28], [0, 1]]
 g := ![![[36, 98, 18], [74, 21, 49], [7, 91, 19], [74, 26], [35, 2], [1]], ![[38, 41, 45, 95], [48, 90, 38, 74], [19, 101, 61, 6], [85, 64], [54, 68], [68, 50, 9, 90]], ![[86, 79, 1, 33], [12, 19, 41, 91], [50, 63, 18, 9], [19, 82], [9, 49], [54, 95, 8, 13]]]
 h' := ![![[9, 77, 75], [70, 30, 92], [79, 83, 7], [0, 45, 88], [41, 32, 52], [26, 27, 65], [0, 1]], ![[56, 25, 28], [20, 20, 18], [9, 39, 14], [81, 52, 13], [72, 68, 95], [25, 11, 45], [9, 77, 75]], ![[0, 1], [12, 53, 96], [65, 84, 82], [47, 6, 2], [58, 3, 59], [66, 65, 96], [56, 25, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 83], []]
 b := ![[], [49, 59, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [77, 76, 38, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![52118, -8549, -50985]
  a := ![-1, -1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![506, -83, -495]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 1092727 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def PBC103 : ContainsPrimesAboveP 103 ![I103N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI103N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![103, 0, 0]]) timesTableT_eq_Table B_one_repr 103 (by decide) 𝕀

instance hp107 : Fact (Nat.Prime 107) := {out := by norm_num}

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0]] 
 ![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [2, 98, 78, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [20, 4, 58], [9, 102, 49], [0, 1]]
 g := ![![[97, 88, 1], [11, 34, 42], [98, 30], [29, 80, 1], [87, 92], [1]], ![[82, 94, 6, 55], [92, 45, 57, 5], [13, 40], [45, 60, 59, 24], [68, 33], [55, 40, 10, 51]], ![[80, 19, 44, 48], [74, 1, 105, 99], [13, 41], [7, 16, 78, 27], [106, 56], [18, 106, 63, 56]]]
 h' := ![![[20, 4, 58], [85, 83, 1], [65, 37, 91], [49, 4, 64], [44, 28, 106], [105, 9, 29], [0, 1]], ![[9, 102, 49], [96, 42, 101], [11, 80, 86], [95, 74, 19], [6, 81, 24], [79, 79, 56], [20, 4, 58]], ![[0, 1], [23, 89, 5], [74, 97, 37], [97, 29, 24], [35, 105, 84], [51, 19, 22], [9, 102, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 26], []]
 b := ![[], [66, 100, 18], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [2, 98, 78, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8696532, 3711081, 1969121]
  a := ![2, 19, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81276, 34683, 18403]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 1225043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def PBC107 : ContainsPrimesAboveP 107 ![I107N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI107N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![107, 0, 0]]) timesTableT_eq_Table B_one_repr 107 (by decide) 𝕀



lemma PB109I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 108 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 108 (by omega)

def PB109I2 : PrimesBelowBoundCertificateInterval O 79 108 109 where
  m := 6
  g := ![1, 2, 2, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107]
  hP := PB109I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0]
    · exact ![I107N0]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI83N0
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
  β := ![I89N1, I97N1, I101N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
