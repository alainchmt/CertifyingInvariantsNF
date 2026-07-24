
import IdealArithmetic.Examples.NF3_1_603288_2.RI3_1_603288_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![17, 9, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![17, 9, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![17, 9, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![17, 9, 1], ![140, -4, 18], ![1260, -119, -4]]]
  hmulB := by decide  
  f := ![![![-16, -9, -1], ![83, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -9, 83]], ![![0, 0, 1], ![-2, -2, 18], ![16, -1, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [17, 27, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 82], [0, 1]]
 g := ![![[26, 44], [14, 40], [68], [41], [76, 65], [1]], ![[0, 39], [13, 43], [68], [41], [64, 18], [1]]]
 h' := ![![[56, 82], [11, 25], [81, 17], [18, 63], [36, 37], [66, 56], [0, 1]], ![[0, 1], [0, 58], [37, 66], [60, 20], [33, 46], [48, 27], [56, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [9, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [17, 27, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![297, 1, -46]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![13, 5, -46]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-18, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-18, 1, 0]] 
 ![![83, 0, 0], ![65, 1, 0], ![4, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-18, 1, 0], ![0, -18, 2], ![140, -21, -18]]]
  hmulB := by decide  
  f := ![![![1225, -68, 0], ![5644, 0, 0]], ![![955, -53, 0], ![4400, 0, 0]], ![![92, 4, -1], ![424, 42, 0]]]
  g := ![![![1, 0, 0], ![-65, 83, 0], ![-4, 0, 83]], ![![-1, 1, 0], ![14, -18, 2], ![19, -21, -18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![17, 9, 1]] ![![83, 0, 0], ![-18, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1494, 83, 0]], ![![1411, 747, 83], ![-166, -166, 0]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-18, 1, 0]]], ![![![17, 9, 1]], ![![-2, -2, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![37, -39, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![37, -39, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![37, 50, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![37, -39, 1], ![140, 16, -78], ![-5460, 889, 16]]]
  hmulB := by decide  
  f := ![![![-36, 39, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-37, -50, 89]], ![![0, -1, 1], ![34, 44, -78], ![-68, 1, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [82, 65, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 88], [0, 1]]
 g := ![![[67, 5], [67], [55], [83, 2], [9, 42], [1]], ![[9, 84], [67], [55], [42, 87], [38, 47], [1]]]
 h' := ![![[24, 88], [15, 19], [13, 45], [47, 12], [63, 25], [7, 24], [0, 1]], ![[0, 1], [26, 70], [25, 44], [68, 77], [40, 64], [49, 65], [24, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [69, 61]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [82, 65, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1662, 756, 8]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22, 4, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-11, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-11, 1, 0]] 
 ![![89, 0, 0], ![78, 1, 0], ![73, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-11, 1, 0], ![0, -11, 2], ![140, -21, -11]]]
  hmulB := by decide  
  f := ![![![914, -83, 0], ![7387, 0, 0]], ![![804, -73, 0], ![6498, 0, 0]], ![![766, -64, -1], ![6191, 45, 0]]]
  g := ![![![1, 0, 0], ![-78, 89, 0], ![-73, 0, 89]], ![![-1, 1, 0], ![8, -11, 2], ![29, -21, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![37, -39, 1]] ![![89, 0, 0], ![-11, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![-979, 89, 0]], ![![3293, -3471, 89], ![-267, 445, -89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![-11, 1, 0]]], ![![![37, -39, 1]], ![![-3, 5, -1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![45, -20, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![45, -20, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![45, 77, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![45, -20, 1], ![140, 24, -40], ![-2800, 490, 24]]]
  hmulB := by decide  
  f := ![![![-44, 20, -1], ![97, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -77, 97]], ![![0, -1, 1], ![20, 32, -40], ![-40, -14, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [52, 22, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [75, 96], [0, 1]]
 g := ![![[34, 73], [1], [27], [44], [93], [75, 1]], ![[77, 24], [1], [27], [44], [93], [53, 96]]]
 h' := ![![[75, 96], [9, 48], [62, 96], [37, 67], [26, 74], [77, 44], [0, 1]], ![[0, 1], [20, 49], [84, 1], [18, 30], [47, 23], [79, 53], [75, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [92, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [52, 22, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2460, 6, 87]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, -69, 87]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![40, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![40, 1, 0]] 
 ![![97, 0, 0], ![40, 1, 0], ![73, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![40, 1, 0], ![0, 40, 2], ![140, -21, 40]]]
  hmulB := by decide  
  f := ![![![521, 13, 0], ![-1261, 0, 0]], ![![200, 5, 0], ![-484, 0, 0]], ![![449, -9, -1], ![-1087, 49, 0]]]
  g := ![![![1, 0, 0], ![-40, 97, 0], ![-73, 0, 97]], ![![0, 1, 0], ![-18, 40, 2], ![-20, -21, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![45, -20, 1]] ![![97, 0, 0], ![40, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![3880, 97, 0]], ![![4365, -1940, 97], ![1940, -776, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![40, 1, 0]]], ![![![45, -20, 1]], ![![20, -8, 0]]]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-19, -9, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-19, -9, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![82, 92, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-19, -9, 1], ![140, -40, -18], ![-1260, 259, -40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-82, -92, 101]], ![![-1, -1, 1], ![16, 16, -18], ![20, 39, -40]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [20, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 100], [0, 1]]
 g := ![![[29, 96], [79], [45, 54], [33], [76], [26, 1]], ![[0, 5], [79], [35, 47], [33], [76], [52, 100]]]
 h' := ![![[26, 100], [16, 46], [9, 68], [68, 16], [18, 72], [86, 50], [0, 1]], ![[0, 1], [0, 55], [60, 33], [80, 85], [72, 29], [73, 51], [26, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [61]]
 b := ![[], [58, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [20, 75, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-744, 833, -418]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![332, 389, -418]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![18, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![18, 1, 0]] 
 ![![101, 0, 0], ![18, 1, 0], ![40, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![18, 1, 0], ![0, 18, 2], ![140, -21, 18]]]
  hmulB := by decide  
  f := ![![![955, 53, 0], ![-5353, 0, 0]], ![![162, 9, 0], ![-908, 0, 0]], ![![380, 12, -1], ![-2130, 51, 0]]]
  g := ![![![1, 0, 0], ![-18, 101, 0], ![-40, 0, 101]], ![![0, 1, 0], ![-4, 18, 2], ![-2, -21, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-19, -9, 1]] ![![101, 0, 0], ![18, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![1818, 101, 0]], ![![-1919, -909, 101], ![-202, -202, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![18, 1, 0]]], ![![![-19, -9, 1]], ![![-2, -2, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![40, -24, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![40, -24, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![40, 79, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![40, -24, 1], ![140, 19, -48], ![-3360, 574, 19]]]
  hmulB := by decide  
  f := ![![![-39, 24, -1], ![103, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-40, -79, 103]], ![![0, -1, 1], ![20, 37, -48], ![-40, -9, 19]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [98, 90, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 102], [0, 1]]
 g := ![![[85, 41], [10, 23], [97, 56], [19], [97], [13, 1]], ![[0, 62], [0, 80], [1, 47], [19], [97], [26, 102]]]
 h' := ![![[13, 102], [50, 12], [73, 34], [55, 57], [75, 88], [65, 71], [0, 1]], ![[0, 1], [0, 91], [0, 69], [75, 46], [86, 15], [61, 32], [13, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [78, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [98, 90, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![378, -62, -109]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![46, 83, -109]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![48, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![48, 1, 0]] 
 ![![103, 0, 0], ![48, 1, 0], ![84, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![48, 1, 0], ![0, 48, 2], ![140, -21, 48]]]
  hmulB := by decide  
  f := ![![![1441, 30, 0], ![-3090, 0, 0]], ![![624, 13, 0], ![-1338, 0, 0]], ![![1164, 0, -1], ![-2496, 52, 0]]]
  g := ![![![1, 0, 0], ![-48, 103, 0], ![-84, 0, 103]], ![![0, 1, 0], ![-24, 48, 2], ![-28, -21, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![40, -24, 1]] ![![103, 0, 0], ![48, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![4944, 103, 0]], ![![4120, -2472, 103], ![2060, -1133, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![48, 1, 0]]], ![![![40, -24, 1]], ![![20, -11, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![44, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![44, 1, 0]] 
 ![![107, 0, 0], ![44, 1, 0], ![102, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![44, 1, 0], ![0, 44, 2], ![140, -21, 44]]]
  hmulB := by decide  
  f := ![![![1585, 36, 0], ![-3852, 0, 0]], ![![660, 15, 0], ![-1604, 0, 0]], ![![1506, 12, -1], ![-3660, 54, 0]]]
  g := ![![![1, 0, 0], ![-44, 107, 0], ![-102, 0, 107]], ![![0, 1, 0], ![-20, 44, 2], ![-32, -21, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-24, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-24, 1, 0]] 
 ![![107, 0, 0], ![83, 1, 0], ![33, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-24, 1, 0], ![0, -24, 2], ![140, -21, -24]]]
  hmulB := by decide  
  f := ![![![1681, -70, 0], ![7490, 0, 0]], ![![1321, -55, 0], ![5886, 0, 0]], ![![531, -10, -1], ![2366, 54, 0]]]
  g := ![![![1, 0, 0], ![-83, 107, 0], ![-33, 0, 107]], ![![-1, 1, 0], ![18, -24, 2], ![25, -21, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-20, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-20, 1, 0]] 
 ![![107, 0, 0], ![87, 1, 0], ![14, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-20, 1, 0], ![0, -20, 2], ![140, -21, -20]]]
  hmulB := by decide  
  f := ![![![1941, -97, 0], ![10379, 0, 0]], ![![1561, -78, 0], ![8347, 0, 0]], ![![282, -4, -1], ![1508, 54, 0]]]
  g := ![![![1, 0, 0], ![-87, 107, 0], ![-14, 0, 107]], ![![-1, 1, 0], ![16, -20, 2], ![21, -21, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![44, 1, 0]] ![![107, 0, 0], ![-24, 1, 0]]
  ![![107, 0, 0], ![7, 10, 1]] where
 M := ![![![11449, 0, 0], ![-2568, 107, 0]], ![![4708, 107, 0], ![-1056, 20, 2]]]
 hmul := by decide  
 g := ![![![![100, -10, -1], ![107, 0, 0]], ![![-24, 1, 0], ![0, 0, 0]]], ![![![37, -9, -1], ![107, 0, 0]], ![![-10, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![7, 10, 1]] ![![107, 0, 0], ![-20, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-2140, 107, 0]], ![![749, 1070, 107], ![0, -214, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-20, 1, 0]]], ![![![7, 10, 1]], ![![0, -2, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![54, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![54, 1, 0]] 
 ![![109, 0, 0], ![54, 1, 0], ![68, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![54, 1, 0], ![0, 54, 2], ![140, -21, 54]]]
  hmulB := by decide  
  f := ![![![1243, 23, 0], ![-2507, 0, 0]], ![![594, 11, 0], ![-1198, 0, 0]], ![![716, -14, -1], ![-1444, 55, 0]]]
  g := ![![![1, 0, 0], ![-54, 109, 0], ![-68, 0, 109]], ![![0, 1, 0], ![-28, 54, 2], ![-22, -21, 54]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-40, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-40, 1, 0]] 
 ![![109, 0, 0], ![69, 1, 0], ![72, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-40, 1, 0], ![0, -40, 2], ![140, -21, -40]]]
  hmulB := by decide  
  f := ![![![1841, -46, 0], ![5014, 0, 0]], ![![1161, -29, 0], ![3162, 0, 0]], ![![1208, -10, -1], ![3290, 55, 0]]]
  g := ![![![1, 0, 0], ![-69, 109, 0], ![-72, 0, 109]], ![![-1, 1, 0], ![24, -40, 2], ![41, -21, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-14, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-14, 1, 0]] 
 ![![109, 0, 0], ![95, 1, 0], ![11, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-14, 1, 0], ![0, -14, 2], ![140, -21, -14]]]
  hmulB := by decide  
  f := ![![![659, -47, 0], ![5123, 0, 0]], ![![561, -40, 0], ![4361, 0, 0]], ![![85, 1, -1], ![661, 55, 0]]]
  g := ![![![1, 0, 0], ![-95, 109, 0], ![-11, 0, 109]], ![![-1, 1, 0], ![12, -14, 2], ![21, -21, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![54, 1, 0]] ![![109, 0, 0], ![-40, 1, 0]]
  ![![109, 0, 0], ![10, 7, 1]] where
 M := ![![![11881, 0, 0], ![-4360, 109, 0]], ![![5886, 109, 0], ![-2160, 14, 2]]]
 hmul := by decide  
 g := ![![![![99, -7, -1], ![109, 0, 0]], ![![-40, 1, 0], ![0, 0, 0]]], ![![![44, -6, -1], ![109, 0, 0]], ![![-20, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![10, 7, 1]] ![![109, 0, 0], ![-14, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-1526, 109, 0]], ![![1090, 763, 109], ![0, -109, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-14, 1, 0]]], ![![![10, 7, 1]], ![![0, -1, 0]]]]
 hle2 := by decide  


def PBC109 : ContainsPrimesAboveP 109 ![I109N0, I109N1, I109N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI109N0
    exact isPrimeI109N1
    exact isPrimeI109N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 109 (by decide) (𝕀 ⊙ MulI109N0 ⊙ MulI109N1)
instance hp113 : Fact (Nat.Prime 113) := {out := by norm_num}

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![62, 23, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![62, 23, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![62, 23, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![62, 23, 1], ![140, 41, 46], ![3220, -413, 41]]]
  hmulB := by decide  
  f := ![![![-61, -23, -1], ![113, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -23, 113]], ![![0, 0, 1], ![-24, -9, 46], ![6, -12, 41]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [18, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 112], [0, 1]]
 g := ![![[97, 44], [64], [52], [53], [56, 30], [62, 1]], ![[0, 69], [64], [52], [53], [108, 83], [11, 112]]]
 h' := ![![[62, 112], [38, 65], [25, 105], [31, 39], [9, 77], [14, 97], [0, 1]], ![[0, 1], [0, 48], [94, 8], [76, 74], [37, 36], [39, 16], [62, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [54, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [18, 51, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5390, 279, 754]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-366, -151, 754]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-46, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-46, 1, 0]] 
 ![![113, 0, 0], ![67, 1, 0], ![72, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-46, 1, 0], ![0, -46, 2], ![140, -21, -46]]]
  hmulB := by decide  
  f := ![![![4693, -102, 0], ![11526, 0, 0]], ![![2807, -61, 0], ![6894, 0, 0]], ![![3000, -42, -1], ![7368, 57, 0]]]
  g := ![![![1, 0, 0], ![-67, 113, 0], ![-72, 0, 113]], ![![-1, 1, 0], ![26, -46, 2], ![43, -21, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![62, 23, 1]] ![![113, 0, 0], ![-46, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5198, 113, 0]], ![![7006, 2599, 113], ![-2712, -1017, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-46, 1, 0]]], ![![![62, 23, 1]], ![![-24, -9, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![51, 3, 2]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![51, 3, 2]] 
 ![![127, 0, 0], ![0, 127, 0], ![89, 65, 1]] where
  M :=![![![51, 3, 2], ![280, 9, 6], ![420, 77, 9]]]
  hmulB := by decide  
  f := ![![![-3, 1, 0]], ![![0, -3, 2]], ![![-1, -1, 1]]]
  g := ![![![-1, -1, 2], ![-2, -3, 6], ![-3, -4, 9]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [64, 28, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [99, 126], [0, 1]]
 g := ![![[56, 2], [7, 32], [28, 1], [71, 74], [105, 113], [99, 1]], ![[0, 125], [0, 95], [0, 126], [31, 53], [116, 14], [71, 126]]]
 h' := ![![[99, 126], [60, 111], [113, 63], [28, 1], [11, 57], [14, 85], [0, 1]], ![[0, 1], [0, 16], [0, 64], [0, 126], [66, 70], [47, 42], [99, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [24, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [64, 28, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-803, 274, -29]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 17, -29]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![-3, 1, 0]] 
 ![![127, 0, 0], ![124, 1, 0], ![59, 0, 1]] where
  M :=![![![-3, 1, 0], ![0, -3, 2], ![140, -21, -3]]]
  hmulB := by decide  
  f := ![![![51, 3, 2]], ![![52, 3, 2]], ![![27, 2, 1]]]
  g := ![![![-1, 1, 0], ![2, -3, 2], ![23, -21, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![51, 3, 2]] ![![-3, 1, 0]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-20, 62, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-20, 62, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![111, 62, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-20, 62, 1], ![140, -41, 124], ![8680, -1232, -41]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-111, -62, 131]], ![![-1, 0, 1], ![-104, -59, 124], ![101, 10, -41]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [101, 126, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 130], [0, 1]]
 g := ![![[22, 48], [69, 91], [52], [101], [107], [25], [1]], ![[0, 83], [0, 40], [52], [101], [107], [25], [1]]]
 h' := ![![[5, 130], [105, 110], [21, 22], [66, 24], [124, 25], [78, 32], [30, 5], [0, 1]], ![[0, 1], [0, 21], [0, 109], [55, 107], [118, 106], [107, 99], [55, 126], [5, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112]]
 b := ![[], [122, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [101, 126, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![661, 322, 170]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-139, -78, 170]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![7, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![7, 1, 0]] 
 ![![131, 0, 0], ![7, 1, 0], ![41, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![7, 1, 0], ![0, 7, 2], ![140, -21, 7]]]
  hmulB := by decide  
  f := ![![![484, 69, 0], ![-9039, 0, 0]], ![![14, 2, 0], ![-261, 0, 0]], ![![144, 17, -1], ![-2689, 66, 0]]]
  g := ![![![1, 0, 0], ![-7, 131, 0], ![-41, 0, 131]], ![![0, 1, 0], ![-1, 7, 2], ![0, -21, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-20, 62, 1]] ![![131, 0, 0], ![7, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![917, 131, 0]], ![![-2620, 8122, 131], ![0, 393, 131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![7, 1, 0]]], ![![![-20, 62, 1]], ![![0, 3, 1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![31, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![31, 1, 0]] 
 ![![137, 0, 0], ![31, 1, 0], ![136, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![31, 1, 0], ![0, 31, 2], ![140, -21, 31]]]
  hmulB := by decide  
  f := ![![![1861, 60, 0], ![-8220, 0, 0]], ![![403, 13, 0], ![-1780, 0, 0]], ![![1880, 45, -1], ![-8304, 69, 0]]]
  g := ![![![1, 0, 0], ![-31, 137, 0], ![-136, 0, 137]], ![![0, 1, 0], ![-9, 31, 2], ![-25, -21, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![48, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![48, 1, 0]] 
 ![![137, 0, 0], ![48, 1, 0], ![81, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![48, 1, 0], ![0, 48, 2], ![140, -21, 48]]]
  hmulB := by decide  
  f := ![![![865, 18, 0], ![-2466, 0, 0]], ![![240, 5, 0], ![-684, 0, 0]], ![![489, -14, -1], ![-1394, 69, 0]]]
  g := ![![![1, 0, 0], ![-48, 137, 0], ![-81, 0, 137]], ![![0, 1, 0], ![-18, 48, 2], ![-20, -21, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![58, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![58, 1, 0]] 
 ![![137, 0, 0], ![58, 1, 0], ![99, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![58, 1, 0], ![0, 58, 2], ![140, -21, 58]]]
  hmulB := by decide  
  f := ![![![1277, 22, 0], ![-3014, 0, 0]], ![![522, 9, 0], ![-1232, 0, 0]], ![![883, -14, -1], ![-2084, 69, 0]]]
  g := ![![![1, 0, 0], ![-58, 137, 0], ![-99, 0, 137]], ![![0, 1, 0], ![-26, 58, 2], ![-32, -21, 58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![31, 1, 0]] ![![137, 0, 0], ![48, 1, 0]]
  ![![137, 0, 0], ![59, -29, 1]] where
 M := ![![![18769, 0, 0], ![6576, 137, 0]], ![![4247, 137, 0], ![1488, 79, 2]]]
 hmul := by decide  
 g := ![![![![78, 29, -1], ![137, 0, 0]], ![![-11, 30, -1], ![137, 0, 0]]], ![![![-28, 30, -1], ![137, 0, 0]], ![![-49, 30, -1], ![139, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![59, -29, 1]] ![![137, 0, 0], ![58, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![7946, 137, 0]], ![![8083, -3973, 137], ![3562, -1644, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![58, 1, 0]]], ![![![59, -29, 1]], ![![26, -12, 0]]]]
 hle2 := by decide  


def PBC137 : ContainsPrimesAboveP 137 ![I137N0, I137N1, I137N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI137N0
    exact isPrimeI137N1
    exact isPrimeI137N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 137 (by decide) (𝕀 ⊙ MulI137N0 ⊙ MulI137N1)


lemma PB220I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB220I2 : PrimesBelowBoundCertificateInterval O 79 137 220 where
  m := 11
  g := ![2, 2, 2, 2, 2, 3, 3, 2, 2, 2, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB220I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
    · exact ![I137N0, I137N1, I137N2]
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
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![109, 109, 109]
    · exact ![12769, 113]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![137, 137, 137]
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
      exact NI101N1
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
      exact NI109N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I89N1, I97N1, I101N1, I103N1, I107N0, I107N1, I107N2, I109N0, I109N1, I109N2, I113N1, I127N1, I131N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [I89N1], [I97N1], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N0, I109N1, I109N2], [I113N1], [I127N1], [I131N1], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
