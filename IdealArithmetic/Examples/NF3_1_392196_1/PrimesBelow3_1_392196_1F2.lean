
import IdealArithmetic.Examples.NF3_1_392196_1.RI3_1_392196_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-83, -101, 154]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-83, -101, 154]] 
 ![![83, 0, 0], ![0, 83, 0], ![0, 43, 1]] where
  M :=![![![-83, -101, 154], ![12118, -3269, -298], ![-996, 3146, -3519]]]
  hmulB := by decide  
  f := ![![![149893, 1555, 6428]], ![![517350, 5367, 22186]], ![![273086, 2833, 11711]]]
  g := ![![![-1, -81, 154], ![146, 115, -298], ![-12, 1861, -3519]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [10, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 82], [0, 1]]
 g := ![![[1, 25], [5, 70], [31], [33], [30, 17], [1]], ![[0, 58], [52, 13], [31], [33], [26, 66], [1]]]
 h' := ![![[73, 82], [33, 78], [9, 53], [30, 60], [32, 45], [73, 73], [0, 1]], ![[0, 1], [0, 5], [60, 30], [11, 23], [80, 38], [7, 10], [73, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [69, 47]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [10, 10, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![415, 54, -213]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 111, -213]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149893, 1555, 6428]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![149893, 1555, 6428]] 
 ![![83, 0, 0], ![72, 1, 0], ![18, 0, 1]] where
  M :=![![![149893, 1555, 6428], ![517350, 5367, 22186], ![420088, 4358, 18015]]]
  hmulB := by decide  
  f := ![![![-83, -101, 154]], ![![74, -127, 130]], ![![-30, 16, -9]]]
  g := ![![![-937, 1555, 6428], ![-3234, 5367, 22186], ![-2626, 4358, 18015]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-83, -101, 154]] ![![149893, 1555, 6428]]
  ![![83, 0, 0]] where
 M := ![![![83, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![54, 27, 1]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0], ![54, 27, 1]] 
 ![![89, 0, 0], ![0, 89, 0], ![54, 27, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![54, 27, 1], ![134, -22, 164], ![2206, -588, 87]]]
  hmulB := by decide  
  f := ![![![-53, -27, -1], ![89, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-54, -27, 89]], ![![0, 0, 1], ![-98, -50, 164], ![-28, -33, 87]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [3, 86, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 88], [0, 1]]
 g := ![![[88, 88], [34], [42], [24, 81], [9, 9], [1]], ![[85, 1], [34], [42], [0, 8], [36, 80], [1]]]
 h' := ![![[3, 88], [34, 55], [74, 52], [17, 24], [62, 9], [86, 3], [0, 1]], ![[0, 1], [21, 34], [52, 37], [0, 65], [0, 80], [6, 86], [3, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [31]]
 b := ![[], [88, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [3, 86, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3117, 1334, -389]
  a := ![2, -5, 7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![201, 133, -389]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0], ![14, 1, 0]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![89, 0, 0], ![14, 1, 0]] 
 ![![89, 0, 0], ![14, 1, 0], ![2, 0, 1]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]], ![![14, 1, 0], ![2, 12, 6], ![80, -22, 16]]]
  hmulB := by decide  
  f := ![![![9857, 61294, 30660], ![2314, -454790, 0]], ![![1550, 9632, 4818], ![357, -71467, 0]], ![![216, 1377, 689], ![87, -10220, 0]]]
  g := ![![![1, 0, 0], ![-14, 89, 0], ![-2, 0, 89]], ![![0, 1, 0], ![-2, 12, 6], ![4, -22, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![89, 0, 0], ![54, 27, 1]] ![![89, 0, 0], ![14, 1, 0]]
  ![![89, 0, 0]] where
 M := ![![![7921, 0, 0], ![1246, 89, 0]], ![![4806, 2403, 89], ![890, 356, 178]]]
 hmul := by decide  
 g := ![![![![89, 0, 0]], ![![14, 1, 0]]], ![![![54, 27, 1]], ![![10, 4, 2]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [48, 12, 91, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 35], [74, 61], [0, 1]]
 g := ![![[58, 32, 79], [96, 44], [38, 12], [14, 93], [72, 36], [1]], ![[10, 82, 66], [14, 85], [95, 32], [92, 54], [49, 96], [1]], ![[82, 80, 49], [54, 65], [53, 53], [9, 47], [20, 62], [1]]]
 h' := ![![[29, 35], [91, 69, 46], [25, 88, 74], [54, 93, 77], [12, 15, 53], [49, 85, 6], [0, 1]], ![[74, 61], [38, 56, 90], [15, 40, 52], [93, 0, 41], [12, 57, 32], [91, 23, 75], [29, 35]], ![[0, 1], [43, 69, 58], [93, 66, 68], [42, 4, 76], [59, 25, 12], [7, 86, 16], [74, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26], []]
 b := ![[], [54, 43, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [48, 12, 91, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![843016136, 619047016, -1084740136]
  a := ![-65, 2, -131]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8690888, 6381928, -11182888]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 912673 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def PBC97 : ContainsPrimesAboveP 97 ![I97N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI97N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![97, 0, 0]]) timesTableT_eq_Table B_one_repr 97 (by decide) 𝕀

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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [45, 86, 8, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 9, 72], [72, 91, 29], [0, 1]]
 g := ![![[13, 13, 52], [92, 80], [43, 15, 37], [1, 31], [56, 64], [1]], ![[80, 55, 19, 75], [2, 24], [48, 23, 65, 61], [3, 20], [18, 78], [82, 70, 63, 53]], ![[75, 43, 6, 41], [49, 1], [86, 76, 22, 94], [92, 88], [29, 65], [88, 68, 40, 48]]]
 h' := ![![[21, 9, 72], [55, 11, 70], [85, 66, 79], [55, 5, 21], [10, 44, 43], [56, 15, 93], [0, 1]], ![[72, 91, 29], [34, 47, 92], [15, 13, 23], [44, 90, 49], [52, 12, 11], [16, 89, 49], [21, 9, 72]], ![[0, 1], [3, 43, 40], [84, 22, 100], [81, 6, 31], [22, 45, 47], [32, 98, 60], [72, 91, 29]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39, 18], []]
 b := ![[], [80, 55, 25], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [45, 86, 8, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-827089, 348450, -134229]
  a := ![-2, 4, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-8189, 3450, -1329]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![11, 1, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![11, 1, 0]] 
 ![![103, 0, 0], ![11, 1, 0], ![1, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![11, 1, 0], ![2, 9, 6], ![80, -22, 13]]]
  hmulB := by decide  
  f := ![![![12392, 56681, 37800], ![1957, -648900, 0]], ![![1322, 6046, 4032], ![207, -69216, 0]], ![![117, 550, 367], ![50, -6300, 0]]]
  g := ![![![1, 0, 0], ![-11, 103, 0], ![-1, 0, 103]], ![![0, 1, 0], ![-1, 9, 6], ![3, -22, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N0 : Nat.card (O ⧸ I103N0) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N0)

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := prime_ideal_of_norm_prime hp103.out _ NI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![28, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![28, 1, 0]] 
 ![![103, 0, 0], ![28, 1, 0], ![85, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![28, 1, 0], ![2, 26, 6], ![80, -22, 30]]]
  hmulB := by decide  
  f := ![![![14541, 210437, 48576], ![6077, -833888, 0]], ![![3952, 57184, 13200], ![1649, -226600, 0]], ![![12011, 173662, 40087], ![4974, -688160, 0]]]
  g := ![![![1, 0, 0], ![-28, 103, 0], ![-85, 0, 103]], ![![0, 1, 0], ![-12, 26, 6], ![-18, -22, 30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1

def I103N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-39, 1, 0]] i)))

def SI103N2: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-39, 1, 0]] 
 ![![103, 0, 0], ![64, 1, 0], ![60, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-39, 1, 0], ![2, -41, 6], ![80, -22, -37]]]
  hmulB := by decide  
  f := ![![![2677, -67634, 9900], ![-1648, -169950, 0]], ![![1661, -42015, 6150], ![-1029, -105575, 0]], ![![1581, -39399, 5767], ![-903, -99000, 0]]]
  g := ![![![1, 0, 0], ![-64, 103, 0], ![-60, 0, 103]], ![![-1, 1, 0], ![22, -41, 6], ![36, -22, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N2 : Nat.card (O ⧸ I103N2) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N2)

lemma isPrimeI103N2 : Ideal.IsPrime I103N2 := prime_ideal_of_norm_prime hp103.out _ NI103N2
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![11, 1, 0]] ![![103, 0, 0], ![28, 1, 0]]
  ![![103, 0, 0], ![-17, -11, 1]] where
 M := ![![![10609, 0, 0], ![2884, 103, 0]], ![![1133, 103, 0], ![310, 37, 6]]]
 hmul := by decide  
 g := ![![![![103, 0, 0], ![0, 0, 0]], ![![28, 1, 0], ![0, 0, 0]]], ![![![11, 1, 0], ![0, 0, 0]], ![![4, 1, 0], ![6, 0, 0]]]]
 hle2 := by decide  

def MulI103N1 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-17, -11, 1]] ![![103, 0, 0], ![-39, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![-4017, 103, 0]], ![![-1751, -1133, 103], ![721, 412, -103]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![-39, 1, 0]]], ![![![-17, -11, 1]], ![![7, 4, -1]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-24, -17, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-24, -17, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![83, 90, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-24, -17, 1], ![46, -12, -100], ![-1314, 380, -79]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -90, 107]], ![![-1, -1, 1], ![78, 84, -100], ![49, 70, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [23, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [104, 106], [0, 1]]
 g := ![![[42, 14], [34, 47], [101], [42, 57], [89], [104, 1]], ![[0, 93], [0, 60], [101], [85, 50], [89], [101, 106]]]
 h' := ![![[104, 106], [74, 96], [40, 49], [104, 84], [39, 48], [69, 93], [0, 1]], ![[0, 1], [0, 11], [0, 58], [66, 23], [2, 59], [4, 14], [104, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [40, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [23, 3, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![435, 54, -192]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![153, 162, -192]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-7, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-7, 1, 0]] 
 ![![107, 0, 0], ![100, 1, 0], ![79, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-7, 1, 0], ![2, -9, 6], ![80, -22, -5]]]
  hmulB := by decide  
  f := ![![![5944, -26896, 17934], ![-535, -319823, 0]], ![![5552, -25132, 16758], ![-534, -298851, 0]], ![![4390, -19858, 13241], ![-373, -236131, 0]]]
  g := ![![![1, 0, 0], ![-100, 107, 0], ![-79, 0, 107]], ![![-1, 1, 0], ![4, -9, 6], ![25, -22, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-24, -17, 1]] ![![107, 0, 0], ![-7, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-749, 107, 0]], ![![-2568, -1819, 107], ![214, 107, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-7, 1, 0]]], ![![![-24, -17, 1]], ![![2, 1, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![17, 7, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![17, 7, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![17, 7, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![17, 7, 1], ![94, -19, 44], ![606, -148, 10]]]
  hmulB := by decide  
  f := ![![![-16, -7, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -7, 109]], ![![0, 0, 1], ![-6, -3, 44], ![4, -2, 10]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [83, 72, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 108], [0, 1]]
 g := ![![[14, 88], [63], [34, 45], [37, 16], [48], [37, 1]], ![[0, 21], [63], [64, 64], [84, 93], [48], [74, 108]]]
 h' := ![![[37, 108], [38, 52], [12, 64], [90, 63], [83, 105], [90, 87], [0, 1]], ![[0, 1], [0, 57], [91, 45], [23, 46], [44, 4], [39, 22], [37, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [61, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [83, 72, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16429, -3090, 2159]
  a := ![2, 18, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-186, -167, 2159]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-44, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-44, 1, 0]] 
 ![![109, 0, 0], ![65, 1, 0], ![99, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-44, 1, 0], ![2, -46, 6], ![80, -22, -42]]]
  hmulB := by decide  
  f := ![![![8305, -241542, 31512], ![-5450, -572468, 0]], ![![4943, -143996, 18786], ![-3269, -341279, 0]], ![![7535, -219382, 28621], ![-4970, -519948, 0]]]
  g := ![![![1, 0, 0], ![-65, 109, 0], ![-99, 0, 109]], ![![-1, 1, 0], ![22, -46, 6], ![52, -22, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![17, 7, 1]] ![![109, 0, 0], ![-44, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-4796, 109, 0]], ![![1853, 763, 109], ![-654, -327, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-44, 1, 0]]], ![![![17, 7, 1]], ![![-6, -3, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-9, -30, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-9, -30, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![104, 83, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-9, -30, 1], ![20, 29, -178], ![-2354, 666, -90]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-104, -83, 113]], ![![-1, -1, 1], ![164, 131, -178], ![62, 72, -90]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [4, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 112], [0, 1]]
 g := ![![[23, 85], [52], [32], [31], [13, 112], [21, 1]], ![[0, 28], [52], [32], [31], [105, 1], [42, 112]]]
 h' := ![![[21, 112], [67, 56], [7, 39], [94, 91], [61, 101], [29, 98], [0, 1]], ![[0, 1], [0, 57], [35, 74], [84, 22], [35, 12], [53, 15], [21, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [42]]
 b := ![[], [62, 21]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [4, 92, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2194, 1350, -949]
  a := ![-2, 4, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![854, 709, -949]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-48, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-48, 1, 0]] 
 ![![113, 0, 0], ![65, 1, 0], ![90, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-48, 1, 0], ![2, -50, 6], ![80, -22, -46]]]
  hmulB := by decide  
  f := ![![![5713, -185964, 22320], ![-4068, -420360, 0]], ![![3319, -106930, 12834], ![-2259, -241707, 0]], ![![4554, -148113, 17777], ![-3231, -334800, 0]]]
  g := ![![![1, 0, 0], ![-65, 113, 0], ![-90, 0, 113]], ![![-1, 1, 0], ![24, -50, 6], ![50, -22, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-9, -30, 1]] ![![113, 0, 0], ![-48, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5424, 113, 0]], ![![-1017, -3390, 113], ![452, 1469, -226]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-48, 1, 0]]], ![![![-9, -30, 1]], ![![4, 13, -2]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0]] 
 ![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [119, 96, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [57, 114, 19], [72, 12, 108], [0, 1]]
 g := ![![[23, 27, 38], [23, 32, 47], [120, 6, 79], [90, 33, 2], [111, 5, 4], [1]], ![[6, 29, 96, 61], [66, 96, 34, 50], [78, 4, 106, 70], [114, 94, 1, 30], [55, 63, 112, 52], [58, 61, 20, 1]], ![[58, 39, 46, 86], [120, 21, 18, 7], [46, 16, 109, 5], [120, 75, 93, 108], [74, 30, 9, 20], [29, 94, 40, 126]]]
 h' := ![![[57, 114, 19], [57, 41, 66], [71, 71, 89], [85, 7, 98], [126, 116, 16], [8, 31, 2], [0, 1]], ![[72, 12, 108], [27, 78, 47], [66, 26, 4], [52, 35, 39], [22, 91, 110], [110, 35, 105], [57, 114, 19]], ![[0, 1], [80, 8, 14], [123, 30, 34], [123, 85, 117], [121, 47, 1], [100, 61, 20], [72, 12, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 67], []]
 b := ![[], [106, 125, 70], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [119, 96, 125, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![169037, -45720, 8382]
  a := ![2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1331, -360, 66]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 2048383 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def PBC127 : ContainsPrimesAboveP 127 ![I127N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![127, 0, 0]]) timesTableT_eq_Table B_one_repr 127 (by decide) 𝕀

instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![16, -19, 1]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![16, -19, 1]] 
 ![![131, 0, 0], ![0, 131, 0], ![16, 112, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![16, -19, 1], ![42, 32, -112], ![-1474, 424, -43]]]
  hmulB := by decide  
  f := ![![![-15, 19, -1], ![131, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-16, -112, 131]], ![![0, -1, 1], ![14, 96, -112], ![-6, 40, -43]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [77, 10, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 130], [0, 1]]
 g := ![![[92, 114], [9, 89], [35], [7], [125], [100], [1]], ![[0, 17], [36, 42], [35], [7], [125], [100], [1]]]
 h' := ![![[121, 130], [93, 101], [25, 73], [121, 64], [108, 111], [63, 16], [54, 121], [0, 1]], ![[0, 1], [0, 30], [81, 58], [5, 67], [46, 20], [34, 115], [23, 10], [121, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [92, 97]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [77, 10, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4652, 600, -2100]
  a := ![-5, 0, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![292, 1800, -2100]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-19, 1, 0]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-19, 1, 0]] 
 ![![131, 0, 0], ![112, 1, 0], ![43, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-19, 1, 0], ![2, -21, 6], ![80, -22, -17]]]
  hmulB := by decide  
  f := ![![![3378, -36451, 10416], ![-655, -227416, 0]], ![![2874, -31159, 8904], ![-654, -194404, 0]], ![![1112, -11965, 3419], ![-193, -74648, 0]]]
  g := ![![![1, 0, 0], ![-112, 131, 0], ![-43, 0, 131]], ![![-1, 1, 0], ![16, -21, 6], ![25, -22, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![131, 0, 0], ![16, -19, 1]] ![![131, 0, 0], ![-19, 1, 0]]
  ![![131, 0, 0]] where
 M := ![![![17161, 0, 0], ![-2489, 131, 0]], ![![2096, -2489, 131], ![-262, 393, -131]]]
 hmul := by decide  
 g := ![![![![131, 0, 0]], ![![-19, 1, 0]]], ![![![16, -19, 1]], ![![-2, 3, -1]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-12, 6, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-12, 6, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![125, 6, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-12, 6, 1], ![92, -46, 38], ![526, -126, -21]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-125, -6, 137]], ![![-1, 0, 1], ![-34, -2, 38], ![23, 0, -21]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [68, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [107, 136], [0, 1]]
 g := ![![[77, 135], [22], [38], [101, 32], [37], [78], [1]], ![[0, 2], [22], [38], [100, 105], [37], [78], [1]]]
 h' := ![![[107, 136], [114, 86], [69, 61], [119, 77], [112, 124], [5, 96], [69, 107], [0, 1]], ![[0, 1], [0, 51], [20, 76], [1, 60], [91, 13], [2, 41], [10, 30], [107, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [51, 113]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [68, 30, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-14108, 5136, -1336]
  a := ![4, -12, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1116, 96, -1336]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-38, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-38, 1, 0]] 
 ![![137, 0, 0], ![99, 1, 0], ![21, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-38, 1, 0], ![2, -40, 6], ![80, -22, -36]]]
  hmulB := by decide  
  f := ![![![-4075, 92146, -13824], ![1918, 315648, 0]], ![![-2947, 66550, -9984], ![1371, 227968, 0]], ![![-603, 14124, -2119], ![372, 48384, 0]]]
  g := ![![![1, 0, 0], ![-99, 137, 0], ![-21, 0, 137]], ![![-1, 1, 0], ![28, -40, 6], ![22, -22, -36]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-12, 6, 1]] ![![137, 0, 0], ![-38, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-5206, 137, 0]], ![![-1644, 822, 137], ![548, -274, 0]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-38, 1, 0]]], ![![![-12, 6, 1]], ![![4, -2, 0]]]]
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


lemma PB178I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB178I2 : PrimesBelowBoundCertificateInterval O 79 137 178 where
  m := 11
  g := ![2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB178I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0, I89N1]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0, I103N1, I103N2]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
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
    · exact ![6889, 83]
    · exact ![7921, 89]
    · exact ![912673]
    · exact ![1030301]
    · exact ![103, 103, 103]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
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
      exact NI83N1
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
      exact NI89N1
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I89N1, I103N0, I103N1, I103N2, I107N1, I109N1, I113N1, I131N1, I137N1]
  Il := ![[I83N1], [I89N1], [], [], [I103N0, I103N1, I103N2], [I107N1], [I109N1], [I113N1], [], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
