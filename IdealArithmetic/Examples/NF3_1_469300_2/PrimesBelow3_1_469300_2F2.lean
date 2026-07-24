
import IdealArithmetic.Examples.NF3_1_469300_2.RI3_1_469300_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [33, 71, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 15, 59], [44, 67, 24], [0, 1]]
 g := ![![[75, 69, 27], [40, 32, 10], [21, 7], [46, 81], [7, 59, 1], []], ![[72, 39, 22, 40], [73, 14, 63, 4], [82, 33], [61, 9], [19, 46, 63, 81], [64, 78]], ![[23, 5, 5, 57], [44, 66, 47, 58], [70, 11], [47, 36], [44, 1, 6, 5], [16, 78]]]
 h' := ![![[15, 15, 59], [8, 6, 39], [82, 67, 33], [51, 33, 67], [18, 46, 9], [0, 0, 1], [0, 1]], ![[44, 67, 24], [43, 77, 62], [70, 81, 22], [28, 30, 45], [76, 23, 80], [22, 55, 67], [15, 15, 59]], ![[0, 1], [72, 0, 65], [26, 18, 28], [57, 20, 54], [23, 14, 77], [80, 28, 15], [44, 67, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3, 72], []]
 b := ![[], [82, 22, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [33, 71, 24, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-234807, -86901, -8217]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2829, -1047, -99]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-42, -26, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-42, -26, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![47, 63, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-42, -26, 1], ![380, 53, -26], ![-9880, -2090, 53]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-47, -63, 89]], ![![-1, -1, 1], ![18, 19, -26], ![-139, -61, 53]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [8, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [1, 88], [0, 1]]
 g := ![![[11, 78], [34], [80], [40, 79], [74, 1], [1]], ![[0, 11], [34], [80], [30, 10], [75, 88], [1]]]
 h' := ![![[1, 88], [16, 73], [33, 37], [36, 13], [31, 41], [81, 1], [0, 1]], ![[0, 1], [0, 16], [70, 52], [49, 76], [72, 48], [82, 88], [1, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [3]]
 b := ![[], [66, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [8, 88, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4639, 2108, 1117]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-642, -767, 1117]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![26, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![26, 1, 0]] 
 ![![89, 0, 0], ![26, 1, 0], ![36, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![26, 1, 0], ![0, 26, 1], ![380, 95, 26]]]
  hmulB := by decide  
  f := ![![![521, 20, 0], ![-1780, 0, 0]], ![![130, 5, 0], ![-444, 0, 0]], ![![216, 8, 0], ![-738, 1, 0]]]
  g := ![![![1, 0, 0], ![-26, 89, 0], ![-36, 0, 89]], ![![0, 1, 0], ![-8, 26, 1], ![-34, 95, 26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-42, -26, 1]] ![![89, 0, 0], ![26, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![2314, 89, 0]], ![![-3738, -2314, 89], ![-712, -623, 0]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![26, 1, 0]]], ![![![-42, -26, 1]], ![![-8, -7, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-23, 13, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-23, 13, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![74, 13, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-23, 13, 1], ![380, 72, 13], ![4940, 1615, 72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -13, 97]], ![![-1, 0, 1], ![-6, -1, 13], ![-4, 7, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [77, 65, 1] where
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
 g := ![![[21, 50], [62], [62], [1], [44], [32, 1]], ![[69, 47], [62], [62], [1], [44], [64, 96]]]
 h' := ![![[32, 96], [49, 70], [78, 81], [14, 81], [73, 1], [58, 74], [0, 1]], ![[0, 1], [58, 27], [51, 16], [84, 16], [8, 96], [1, 23], [32, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [90, 55]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [77, 65, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-747, 127, 159]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-129, -20, 159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-13, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-13, 1, 0]] 
 ![![97, 0, 0], ![84, 1, 0], ![25, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-13, 1, 0], ![0, -13, 1], ![380, 95, -13]]]
  hmulB := by decide  
  f := ![![![248, -19, 0], ![1843, 0, 0]], ![![222, -17, 0], ![1650, 0, 0]], ![![80, -6, 0], ![595, 1, 0]]]
  g := ![![![1, 0, 0], ![-84, 97, 0], ![-25, 0, 97]], ![![-1, 1, 0], ![11, -13, 1], ![-75, 95, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-23, 13, 1]] ![![97, 0, 0], ![-13, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-1261, 97, 0]], ![![-2231, 1261, 97], ![679, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-13, 1, 0]]], ![![![-23, 13, 1]], ![![7, -1, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [56, 88, 62, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [8, 1, 75], [31, 99, 26], [0, 1]]
 g := ![![[72, 89, 21], [78, 14], [60, 62, 54], [44, 100], [36, 6], [1]], ![[35, 71, 73, 11], [2, 30], [94, 85, 67, 28], [38, 56], [45, 43], [15, 58, 31, 99]], ![[16, 7, 54, 62], [94, 36], [58, 23, 37, 66], [88, 22], [81, 22], [100, 75, 62, 2]]]
 h' := ![![[8, 1, 75], [98, 82, 83], [74, 100, 32], [41, 26, 85], [9, 90, 10], [45, 13, 39], [0, 1]], ![[31, 99, 26], [3, 10, 25], [32, 26, 63], [64, 63, 63], [24, 29, 64], [76, 68, 89], [8, 1, 75]], ![[0, 1], [88, 9, 94], [91, 76, 6], [15, 12, 54], [87, 83, 27], [52, 20, 74], [31, 99, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 82], []]
 b := ![[], [21, 63, 42], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [56, 88, 62, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3071713, -1523585, -179275]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30413, -15085, -1775]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-93, 38, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-93, 38, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![10, 38, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-93, 38, 1], ![380, 2, 38], ![14440, 3990, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -38, 103]], ![![-1, 0, 1], ![0, -14, 38], ![140, 38, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [39, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [56, 102], [0, 1]]
 g := ![![[91, 7], [60, 13], [49, 18], [72], [49], [56, 1]], ![[71, 96], [67, 90], [27, 85], [72], [49], [9, 102]]]
 h' := ![![[56, 102], [29, 25], [46, 42], [36, 11], [75, 81], [82, 7], [0, 1]], ![[0, 1], [90, 78], [29, 61], [34, 92], [79, 22], [62, 96], [56, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30]]
 b := ![[], [95, 15]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [39, 47, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![799, 523, 49]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3, -13, 49]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-38, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-38, 1, 0]] 
 ![![103, 0, 0], ![65, 1, 0], ![101, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-38, 1, 0], ![0, -38, 1], ![380, 95, -38]]]
  hmulB := by decide  
  f := ![![![1179, -31, 0], ![3193, 0, 0]], ![![761, -20, 0], ![2061, 0, 0]], ![![1117, -29, 0], ![3025, 1, 0]]]
  g := ![![![1, 0, 0], ![-65, 103, 0], ![-101, 0, 103]], ![![-1, 1, 0], ![23, -38, 1], ![-19, 95, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-93, 38, 1]] ![![103, 0, 0], ![-38, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-3914, 103, 0]], ![![-9579, 3914, 103], ![3914, -1442, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-38, 1, 0]]], ![![![-93, 38, 1]], ![![38, -14, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-62, -51, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-62, -51, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![45, 56, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-62, -51, 1], ![380, 33, -51], ![-19380, -4465, 33]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -56, 107]], ![![-1, -1, 1], ![25, 27, -51], ![-195, -59, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [86, 49, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [58, 106], [0, 1]]
 g := ![![[69, 56], [87, 52], [47], [51, 99], [23], [58, 1]], ![[0, 51], [0, 55], [47], [15, 8], [23], [9, 106]]]
 h' := ![![[58, 106], [8, 22], [25, 42], [1, 49], [24, 62], [41, 68], [0, 1]], ![[0, 1], [0, 85], [0, 65], [61, 58], [89, 45], [26, 39], [58, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [47, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [86, 49, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14576, 4959, 507]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-77, -219, 507]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![51, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![51, 1, 0]] 
 ![![107, 0, 0], ![51, 1, 0], ![74, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![51, 1, 0], ![0, 51, 1], ![380, 95, 51]]]
  hmulB := by decide  
  f := ![![![868, 17, 0], ![-1819, 0, 0]], ![![408, 8, 0], ![-855, 0, 0]], ![![586, 11, 0], ![-1228, 1, 0]]]
  g := ![![![1, 0, 0], ![-51, 107, 0], ![-74, 0, 107]], ![![0, 1, 0], ![-25, 51, 1], ![-77, 95, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-62, -51, 1]] ![![107, 0, 0], ![51, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5457, 107, 0]], ![![-6634, -5457, 107], ![-2782, -2568, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![51, 1, 0]]], ![![![-62, -51, 1]], ![![-26, -24, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-47, -22, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-47, -22, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![62, 87, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-47, -22, 1], ![380, 48, -22], ![-8360, -1710, 48]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -87, 109]], ![![-1, -1, 1], ![16, 18, -22], ![-104, -54, 48]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [60, 78, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 108], [0, 1]]
 g := ![![[34, 20], [5], [50, 29], [42, 102], [78], [31, 1]], ![[0, 89], [5], [77, 80], [43, 7], [78], [62, 108]]]
 h' := ![![[31, 108], [6, 42], [52, 88], [96, 62], [56, 50], [102, 29], [0, 1]], ![[0, 1], [0, 67], [55, 21], [56, 47], [80, 59], [20, 80], [31, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [33, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [60, 78, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2297, 38, 28]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-37, -22, 28]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![22, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![22, 1, 0]] 
 ![![109, 0, 0], ![22, 1, 0], ![61, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![22, 1, 0], ![0, 22, 1], ![380, 95, 22]]]
  hmulB := by decide  
  f := ![![![67, 3, 0], ![-327, 0, 0]], ![![-22, -1, 0], ![110, 0, 0]], ![![27, 1, 0], ![-131, 1, 0]]]
  g := ![![![1, 0, 0], ![-22, 109, 0], ![-61, 0, 109]], ![![0, 1, 0], ![-5, 22, 1], ![-28, 95, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-47, -22, 1]] ![![109, 0, 0], ![22, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![2398, 109, 0]], ![![-5123, -2398, 109], ![-654, -436, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![22, 1, 0]]], ![![![-47, -22, 1]], ![![-6, -4, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [57, 51, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [88, 64, 45], [66, 48, 68], [0, 1]]
 g := ![![[50, 92, 30], [88, 41], [88, 62], [104, 61], [39, 103, 99], [1]], ![[79, 59, 74, 38], [103, 51], [57, 85], [32, 50], [104, 111, 13, 39], [43, 47, 86, 47]], ![[66, 43, 59, 20], [23, 30], [3, 81], [93, 28], [49, 104, 35, 42], [79, 53, 54, 66]]]
 h' := ![![[88, 64, 45], [20, 28, 16], [8, 54, 70], [74, 79, 66], [37, 22, 20], [56, 62, 41], [0, 1]], ![[66, 48, 68], [92, 79, 107], [58, 72, 27], [97, 38, 56], [0, 86, 29], [4, 94, 12], [88, 64, 45]], ![[0, 1], [31, 6, 103], [41, 100, 16], [41, 109, 104], [12, 5, 64], [41, 70, 60], [66, 48, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91, 82], []]
 b := ![[], [108, 21, 71], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [57, 51, 72, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1698277, 825126, 104864]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![15029, 7302, 928]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 1442897 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def PBC113 : ContainsPrimesAboveP 113 ![I113N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![113, 0, 0]]) timesTableT_eq_Table B_one_repr 113 (by decide) 𝕀

instance hp127 : Fact (Nat.Prime 127) := {out := by norm_num}

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-14, -9, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-14, -9, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![113, 118, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-14, -9, 1], ![380, 81, -9], ![-3420, -475, 81]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-113, -118, 127]], ![![-1, -1, 1], ![11, 9, -9], ![-99, -79, 81]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [5, 122, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 126], [0, 1]]
 g := ![![[126, 1], [101, 35], [16, 117], [47, 62], [111, 19], [5, 1]], ![[4, 126], [22, 92], [93, 10], [103, 65], [79, 108], [10, 126]]]
 h' := ![![[5, 126], [3, 126], [47, 110], [19, 102], [80, 69], [102, 20], [0, 1]], ![[0, 1], [125, 1], [89, 17], [21, 25], [44, 58], [75, 107], [5, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [50]]
 b := ![[], [1, 25]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [5, 122, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14947, -3540, 732]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-769, -708, 732]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![9, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![9, 1, 0]] 
 ![![127, 0, 0], ![9, 1, 0], ![46, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![9, 1, 0], ![0, 9, 1], ![380, 95, 9]]]
  hmulB := by decide  
  f := ![![![874, 97, 0], ![-12319, 0, 0]], ![![54, 6, 0], ![-761, 0, 0]], ![![316, 35, 0], ![-4454, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 127, 0], ![-46, 0, 127]], ![![0, 1, 0], ![-1, 9, 1], ![-7, 95, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![-14, -9, 1]] ![![127, 0, 0], ![9, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![1143, 127, 0]], ![![-1778, -1143, 127], ![254, 0, 0]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![9, 1, 0]]], ![![![-14, -9, 1]], ![![2, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-34, -42, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-34, -42, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![97, 89, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-34, -42, 1], ![380, 61, -42], ![-15960, -3610, 61]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-97, -89, 131]], ![![-1, -1, 1], ![34, 29, -42], ![-167, -69, 61]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [51, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 130], [0, 1]]
 g := ![![[62, 101], [83, 125], [105], [41], [33], [62], [1]], ![[78, 30], [60, 6], [105], [41], [33], [62], [1]]]
 h' := ![![[113, 130], [90, 25], [77, 16], [89, 74], [79, 98], [94, 65], [80, 113], [0, 1]], ![[0, 1], [33, 106], [51, 115], [67, 57], [18, 33], [103, 66], [11, 18], [113, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48]]
 b := ![[], [85, 24]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [51, 18, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-306, 146, 140]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-106, -94, 140]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![42, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![42, 1, 0]] 
 ![![131, 0, 0], ![42, 1, 0], ![70, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![42, 1, 0], ![0, 42, 1], ![380, 95, 42]]]
  hmulB := by decide  
  f := ![![![2101, 50, 0], ![-6550, 0, 0]], ![![630, 15, 0], ![-1964, 0, 0]], ![![1106, 26, 0], ![-3448, 1, 0]]]
  g := ![![![1, 0, 0], ![-42, 131, 0], ![-70, 0, 131]], ![![0, 1, 0], ![-14, 42, 1], ![-50, 95, 42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-34, -42, 1]] ![![131, 0, 0], ![42, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![5502, 131, 0]], ![![-4454, -5502, 131], ![-1048, -1703, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![42, 1, 0]]], ![![![-34, -42, 1]], ![![-8, -13, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-23, 49, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-23, 49, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![114, 49, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-23, 49, 1], ![380, 72, 49], ![18620, 5035, 72]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-114, -49, 137]], ![![-1, 0, 1], ![-38, -17, 49], ![76, 11, 72]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [90, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 136], [0, 1]]
 g := ![![[60, 11], [133], [38], [85, 68], [119], [98], [1]], ![[118, 126], [133], [38], [45, 69], [119], [98], [1]]]
 h' := ![![[80, 136], [5, 55], [78, 63], [22, 60], [105, 43], [102, 16], [47, 80], [0, 1]], ![[0, 1], [21, 82], [49, 74], [27, 77], [120, 94], [12, 121], [8, 57], [80, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [98, 114]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [90, 57, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3188, 904, 52]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-20, -12, 52]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-49, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-49, 1, 0]] 
 ![![137, 0, 0], ![88, 1, 0], ![65, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-49, 1, 0], ![0, -49, 1], ![380, 95, -49]]]
  hmulB := by decide  
  f := ![![![1079, -22, 0], ![3014, 0, 0]], ![![736, -15, 0], ![2056, 0, 0]], ![![557, -11, 0], ![1556, 1, 0]]]
  g := ![![![1, 0, 0], ![-88, 137, 0], ![-65, 0, 137]], ![![-1, 1, 0], ![31, -49, 1], ![-35, 95, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-23, 49, 1]] ![![137, 0, 0], ![-49, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-6713, 137, 0]], ![![-3151, 6713, 137], ![1507, -2329, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-49, 1, 0]]], ![![![-23, 49, 1]], ![![11, -17, 0]]]]
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


lemma PB194I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB194I2 : PrimesBelowBoundCertificateInterval O 79 137 194 where
  m := 11
  g := ![1, 2, 2, 1, 2, 2, 2, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB194I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0, I89N1]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0, I131N1]
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
    · exact ![571787]
    · exact ![7921, 89]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![10609, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![17161, 131]
    · exact ![18769, 137]
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
      exact NI109N1
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
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
  β := ![I89N1, I97N1, I103N1, I107N1, I109N1, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [], [I103N1], [I107N1], [I109N1], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
