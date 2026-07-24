
import IdealArithmetic.Examples.NF3_1_853335_2.RI3_1_853335_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-17, -31, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-17, -31, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![66, 52, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-17, -31, 1], ![203, 4, -217], ![-6293, -622, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-66, -52, 83]], ![![-1, -1, 1], ![175, 136, -217], ![-79, -10, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [50, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [77, 82], [0, 1]]
 g := ![![[30, 7], [51, 27], [38], [65], [52, 36], [1]], ![[71, 76], [55, 56], [38], [65], [2, 47], [1]]]
 h' := ![![[77, 82], [23, 16], [57, 39], [52, 72], [56, 56], [33, 77], [0, 1]], ![[0, 1], [10, 67], [72, 44], [35, 11], [52, 27], [69, 6], [77, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81]]
 b := ![[], [80, 82]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [50, 6, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![456, 65, 22]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -13, 22]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-32, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-32, 1, 0]] 
 ![![83, 0, 0], ![51, 1, 0], ![79, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-32, 1, 0], ![0, -32, 7], ![203, 21, -32]]]
  hmulB := by decide  
  f := ![![![673, -21, 0], ![1743, 0, 0]], ![![449, -14, 0], ![1163, 0, 0]], ![![629, -15, -1], ![1629, 12, 0]]]
  g := ![![![1, 0, 0], ![-51, 83, 0], ![-79, 0, 83]], ![![-1, 1, 0], ![13, -32, 7], ![20, 21, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-17, -31, 1]] ![![83, 0, 0], ![-32, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-2656, 83, 0]], ![![-1411, -2573, 83], ![747, 996, -249]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-32, 1, 0]]], ![![![-17, -31, 1]], ![![9, 12, -3]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![-34, 7, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![-34, 7, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![55, 7, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![-34, 7, 1], ![203, -13, 49], ![1421, 176, -13]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-55, -7, 89]], ![![-1, 0, 1], ![-28, -4, 49], ![24, 3, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [84, 6, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 88], [0, 1]]
 g := ![![[70, 71], [73], [17], [69, 64], [80, 36], [1]], ![[0, 18], [73], [17], [41, 25], [42, 53], [1]]]
 h' := ![![[83, 88], [81, 58], [28, 47], [78, 62], [44, 81], [5, 83], [0, 1]], ![[0, 1], [0, 31], [13, 42], [62, 27], [3, 8], [41, 6], [83, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19]]
 b := ![[], [73, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [84, 6, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2357, 1, 229]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-168, -18, 229]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![40, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![40, 1, 0]] 
 ![![89, 0, 0], ![40, 1, 0], ![13, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![40, 1, 0], ![0, 40, 7], ![203, 21, 40]]]
  hmulB := by decide  
  f := ![![![1081, 27, 0], ![-2403, 0, 0]], ![![520, 13, 0], ![-1156, 0, 0]], ![![157, -19, -4], ![-349, 51, 0]]]
  g := ![![![1, 0, 0], ![-40, 89, 0], ![-13, 0, 89]], ![![0, 1, 0], ![-19, 40, 7], ![-13, 21, 40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![-34, 7, 1]] ![![89, 0, 0], ![40, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![3560, 89, 0]], ![![-3026, 623, 89], ![-1157, 267, 89]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![40, 1, 0]]], ![![![-34, 7, 1]], ![![-13, 3, 1]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-55, 3, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-55, 3, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![42, 3, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-55, 3, 1], ![203, -34, 21], ![609, 92, -34]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -3, 97]], ![![-1, 0, 1], ![-7, -1, 21], ![21, 2, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [52, 31, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [66, 96], [0, 1]]
 g := ![![[92, 70], [33], [86], [89], [35], [66, 1]], ![[56, 27], [33], [86], [89], [35], [35, 96]]]
 h' := ![![[66, 96], [34, 19], [2, 18], [20, 38], [34, 34], [60, 36], [0, 1]], ![[0, 1], [27, 78], [26, 79], [6, 59], [47, 63], [11, 61], [66, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [55]]
 b := ![[], [14, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [52, 31, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1758, -110, 125]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-36, -5, 125]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-21, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-21, 1, 0]] 
 ![![97, 0, 0], ![76, 1, 0], ![34, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-21, 1, 0], ![0, -21, 7], ![203, 21, -21]]]
  hmulB := by decide  
  f := ![![![988, -47, 0], ![4559, 0, 0]], ![![778, -37, 0], ![3590, 0, 0]], ![![358, -14, -1], ![1652, 14, 0]]]
  g := ![![![1, 0, 0], ![-76, 97, 0], ![-34, 0, 97]], ![![-1, 1, 0], ![14, -21, 7], ![-7, 21, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-55, 3, 1]] ![![97, 0, 0], ![-21, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-2037, 97, 0]], ![![-5335, 291, 97], ![1358, -97, 0]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-21, 1, 0]]], ![![![-55, 3, 1]], ![![14, -1, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [87, 47, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [33, 86, 25], [46, 14, 76], [0, 1]]
 g := ![![[24, 23, 43], [90, 37], [32, 34, 25], [50, 96], [5, 80], [1]], ![[70, 65, 95, 81], [98, 71], [35, 94, 2, 70], [51, 52], [83, 14], [98, 14, 7, 71]], ![[2, 14, 77, 25], [3, 9], [91, 37, 54, 100], [15, 23], [69, 100], [97, 40, 37, 30]]]
 h' := ![![[33, 86, 25], [65, 53, 12], [44, 60, 21], [49, 83, 96], [64, 74, 46], [14, 54, 79], [0, 1]], ![[46, 14, 76], [54, 41, 79], [55, 58, 77], [20, 90, 86], [35, 41, 70], [40, 14, 32], [33, 86, 25]], ![[0, 1], [55, 7, 10], [35, 84, 3], [39, 29, 20], [43, 87, 86], [17, 33, 91], [46, 14, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 100], []]
 b := ![[], [35, 36, 97], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [87, 47, 22, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-72720, -19190, -3131]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-720, -190, -31]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-45, -51, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-45, -51, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![58, 52, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-45, -51, 1], ![203, -24, -357], ![-10353, -1042, -24]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-58, -52, 103]], ![![-1, -1, 1], ![203, 180, -357], ![-87, 2, -24]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [65, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [92, 102], [0, 1]]
 g := ![![[100, 61], [67, 26], [12, 100], [68], [46], [92, 1]], ![[47, 42], [90, 77], [45, 3], [68], [46], [81, 102]]]
 h' := ![![[92, 102], [74, 24], [44, 52], [68, 93], [33, 58], [97, 56], [0, 1]], ![[0, 1], [16, 79], [90, 51], [75, 10], [13, 45], [99, 47], [92, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [89, 63]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [65, 11, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![471, 60, 17]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -8, 17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![48, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![48, 1, 0]] 
 ![![103, 0, 0], ![48, 1, 0], ![24, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![48, 1, 0], ![0, 48, 7], ![203, 21, 48]]]
  hmulB := by decide  
  f := ![![![1441, 30, 0], ![-3090, 0, 0]], ![![624, 13, 0], ![-1338, 0, 0]], ![![264, -22, -4], ![-566, 59, 0]]]
  g := ![![![1, 0, 0], ![-48, 103, 0], ![-24, 0, 103]], ![![0, 1, 0], ![-24, 48, 7], ![-19, 21, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-45, -51, 1]] ![![103, 0, 0], ![48, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![4944, 103, 0]], ![![-4635, -5253, 103], ![-1957, -2472, -309]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![48, 1, 0]]], ![![![-45, -51, 1]], ![![-19, -24, -3]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![3, -26, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![3, -26, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![3, 81, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![3, -26, 1], ![203, 24, -182], ![-5278, -517, 24]]]
  hmulB := by decide  
  f := ![![![-2, 26, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-3, -81, 107]], ![![0, -1, 1], ![7, 138, -182], ![-50, -23, 24]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [41, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [54, 106], [0, 1]]
 g := ![![[30, 47], [28, 29], [81], [74, 44], [89], [54, 1]], ![[0, 60], [96, 78], [81], [96, 63], [89], [1, 106]]]
 h' := ![![[54, 106], [29, 49], [49, 52], [69, 9], [8, 30], [33, 93], [0, 1]], ![[0, 1], [0, 58], [75, 55], [20, 98], [23, 77], [26, 14], [54, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [100]]
 b := ![[], [41, 50]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [41, 53, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7809, 1872, 2603]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![0, -1953, 2603]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-32, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-32, 1, 0]] 
 ![![107, 0, 0], ![75, 1, 0], ![83, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-32, 1, 0], ![0, -32, 7], ![203, 21, -32]]]
  hmulB := by decide  
  f := ![![![3297, -103, 0], ![11021, 0, 0]], ![![2305, -72, 0], ![7705, 0, 0]], ![![2585, -67, -3], ![8641, 46, 0]]]
  g := ![![![1, 0, 0], ![-75, 107, 0], ![-83, 0, 107]], ![![-1, 1, 0], ![17, -32, 7], ![12, 21, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![3, -26, 1]] ![![107, 0, 0], ![-32, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-3424, 107, 0]], ![![321, -2782, 107], ![107, 856, -214]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-32, 1, 0]]], ![![![3, -26, 1]], ![![1, 8, -2]]]]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [45, 51, 45, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [62, 94, 40], [2, 14, 69], [0, 1]]
 g := ![![[18, 57, 61], [88, 12], [94, 35, 66], [25], [11, 63], [1]], ![[1, 70, 78, 23], [105, 43], [39, 69, 30, 99], [63, 48, 85, 98], [51, 82], [27, 68, 47, 17]], ![[103, 99, 7, 37], [61, 5], [21, 64, 83, 67], [57, 45, 33, 11], [85, 100], [85, 33, 58, 92]]]
 h' := ![![[62, 94, 40], [78, 85, 37], [21, 88, 11], [74, 49, 34], [4, 104], [64, 58, 64], [0, 1]], ![[2, 14, 69], [76, 64, 103], [21, 9, 77], [91, 83, 38], [21, 75, 18], [38, 35, 55], [62, 94, 40]], ![[0, 1], [44, 69, 78], [101, 12, 21], [14, 86, 37], [103, 39, 91], [107, 16, 99], [2, 14, 69]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 54], []]
 b := ![[], [58, 62, 15], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [45, 51, 45, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19729, -2943, 981]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![181, -27, 9]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [62, 60, 29, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [31, 69, 91], [53, 43, 22], [0, 1]]
 g := ![![[56, 65, 9], [57, 64], [29, 25], [27, 100], [18, 109, 50], [1]], ![[74, 8, 75, 44], [104, 30], [89, 61], [55, 11], [49, 45, 8, 56], [92, 103, 33, 87]], ![[97, 53, 36, 83], [101, 11], [8, 112], [36, 26], [84, 2, 96, 104], [8, 31, 97, 26]]]
 h' := ![![[31, 69, 91], [1, 92, 3], [91, 56, 8], [104, 15, 108], [14, 74, 103], [51, 53, 84], [0, 1]], ![[53, 43, 22], [65, 47, 26], [80, 94, 16], [93, 86, 20], [0, 44, 89], [18, 6, 73], [31, 69, 91]], ![[0, 1], [110, 87, 84], [65, 76, 89], [30, 12, 98], [51, 108, 34], [12, 54, 69], [53, 43, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 80], []]
 b := ![[], [66, 111, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [62, 60, 29, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![123283, 22261, 9605]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1091, 197, 85]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![30, 7, -4]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![30, 7, -4]] 
 ![![127, 0, 0], ![0, 127, 0], ![56, 30, 1]] where
  M :=![![![30, 7, -4], ![-812, -54, 49], ![1421, 31, -54]]]
  hmulB := by decide  
  f := ![![![11, 2, 1]], ![![203, 32, 14]], ![![56, 9, 4]]]
  g := ![![![2, 1, -4], ![-28, -12, 49], ![35, 13, -54]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [51, 125, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [2, 126], [0, 1]]
 g := ![![[117, 38], [41, 74], [90, 117], [11, 37], [36, 50], [2, 1]], ![[66, 89], [62, 53], [70, 10], [85, 90], [9, 77], [4, 126]]]
 h' := ![![[2, 126], [68, 61], [109, 70], [74, 102], [69, 52], [25, 80], [0, 1]], ![[0, 1], [63, 66], [122, 57], [24, 25], [46, 75], [58, 47], [2, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94]]
 b := ![[], [80, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [51, 125, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-7815, -2014, 1042]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-521, -262, 1042]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 2, 1]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![11, 2, 1]] 
 ![![127, 0, 0], ![44, 1, 0], ![50, 0, 1]] where
  M :=![![![11, 2, 1], ![203, 32, 14], ![406, 71, 32]]]
  hmulB := by decide  
  f := ![![![30, 7, -4]], ![![4, 2, -1]], ![![23, 3, -2]]]
  g := ![![![-1, 2, 1], ![-15, 32, 14], ![-34, 71, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![30, 7, -4]] ![![11, 2, 1]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-40, -4, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-40, -4, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![91, 127, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-40, -4, 1], ![203, -19, -28], ![-812, -55, -19]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-91, -127, 131]], ![![-1, -1, 1], ![21, 27, -28], ![7, 18, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [25, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 130], [0, 1]]
 g := ![![[71, 21], [12, 65], [77], [129], [108], [75], [1]], ![[0, 110], [48, 66], [77], [129], [108], [75], [1]]]
 h' := ![![[59, 130], [93, 105], [74, 14], [77, 48], [114, 103], [60, 34], [106, 59], [0, 1]], ![[0, 1], [0, 26], [114, 117], [27, 83], [34, 28], [101, 97], [50, 72], [59, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [71, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [25, 72, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![724, -111, 126]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-82, -123, 126]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![28, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![28, 1, 0]] 
 ![![131, 0, 0], ![28, 1, 0], ![19, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![28, 1, 0], ![0, 28, 7], ![203, 21, 28]]]
  hmulB := by decide  
  f := ![![![2045, 73, 0], ![-9563, 0, 0]], ![![420, 15, 0], ![-1964, 0, 0]], ![![253, -7, -4], ![-1183, 75, 0]]]
  g := ![![![1, 0, 0], ![-28, 131, 0], ![-19, 0, 131]], ![![0, 1, 0], ![-7, 28, 7], ![-7, 21, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![-40, -4, 1]] ![![131, 0, 0], ![28, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![3668, 131, 0]], ![![-5240, -524, 131], ![-917, -131, 0]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![28, 1, 0]]], ![![![-40, -4, 1]], ![![-7, -1, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [49, 93, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [133, 131, 74], [102, 5, 63], [0, 1]]
 g := ![![[56, 28, 123], [59, 69], [28, 39], [79, 65, 65], [125, 76], [98, 1], []], ![[51, 119, 132, 1], [66, 19], [80, 93], [53, 54, 100, 136], [100, 130], [102, 25], [90, 133]], ![[10, 67, 91, 7], [63, 11], [49, 68], [59, 101, 93, 98], [91, 77], [135, 36], [101, 133]]]
 h' := ![![[133, 131, 74], [86, 88, 64], [127, 18, 84], [102, 129, 83], [89, 45, 105], [130, 16, 58], [0, 0, 1], [0, 1]], ![[102, 5, 63], [53, 8, 119], [37, 116, 108], [126, 41, 97], [92, 10, 19], [34, 13, 104], [127, 94, 5], [133, 131, 74]], ![[0, 1], [64, 41, 91], [0, 3, 82], [88, 104, 94], [136, 82, 13], [38, 108, 112], [112, 43, 131], [102, 5, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [30, 16], []]
 b := ![[], [59, 71, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [49, 93, 39, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-79597, -18084, -4521]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-581, -132, -33]
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
  g := ![2, 2, 2, 1, 2, 2, 1, 1, 2, 2, 1]
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
    · exact ![I113N0]
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
    · exact ![1442897]
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
  β := ![I83N1, I89N1, I97N1, I103N1, I107N1, I127N1, I131N1]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [I107N1], [], [], [I127N1], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
