
import IdealArithmetic.Examples.NF3_1_369800_2.RI3_1_369800_2
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [12, 49, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 75, 31], [36, 7, 52], [0, 1]]
 g := ![![[27, 3, 9], [52, 10, 63], [71, 77], [26, 75], [61, 44, 1], []], ![[59, 71, 45, 11], [53, 23, 33, 10], [31, 7], [38, 25], [49, 24, 76, 25], [39, 48]], ![[17, 20, 17, 60], [11, 19, 7, 19], [42, 10], [62, 3], [31, 5, 52, 8], [18, 48]]]
 h' := ![![[8, 75, 31], [40, 24, 80], [77, 11, 48], [79, 50, 49], [15, 52, 18], [0, 0, 1], [0, 1]], ![[36, 7, 52], [33, 17, 59], [29, 54, 13], [22, 32, 67], [48, 73, 78], [11, 41, 7], [8, 75, 31]], ![[0, 1], [71, 42, 27], [23, 18, 22], [19, 1, 50], [79, 41, 70], [1, 42, 75], [36, 7, 52]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77, 14], []]
 b := ![[], [61, 74, 29], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [12, 49, 39, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-841869, -252569, -39508]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-10143, -3043, -476]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [13, 84, 87, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 71, 13], [50, 17, 76], [0, 1]]
 g := ![![[79, 47, 47], [15, 1], [24, 18], [16, 41, 47], [9, 2, 1], []], ![[82, 13, 62, 12], [73, 45], [30, 40], [67, 9, 56, 51], [49, 52, 62, 19], [48, 80]], ![[29, 79, 35, 74], [9, 71], [84, 69], [38, 33, 40, 70], [38, 6, 37, 60], [74, 80]]]
 h' := ![![[41, 71, 13], [51, 52, 74], [54, 51, 1], [59, 64, 75], [61, 19, 15], [0, 0, 1], [0, 1]], ![[50, 17, 76], [34, 7, 65], [87, 10, 57], [78, 7, 60], [52, 50, 57], [78, 38, 17], [41, 71, 13]], ![[0, 1], [51, 30, 39], [48, 28, 31], [61, 18, 43], [51, 20, 17], [25, 51, 71], [50, 17, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [86, 15], []]
 b := ![[], [14, 73, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [13, 84, 87, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6261862, 3098713, 784268]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70358, 34817, 8812]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0]] 
 ![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [68, 26, 60, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 80, 67], [31, 16, 30], [0, 1]]
 g := ![![[37, 39, 93], [6, 12], [71, 2], [47, 73], [35, 11], [1]], ![[57, 31, 88, 46], [2, 33], [27, 6], [33, 81], [72, 2], [17, 85, 81, 63]], ![[87, 61, 42, 63], [7, 86], [74, 65], [89, 48], [42, 79], [89, 49, 32, 34]]]
 h' := ![![[6, 80, 67], [69, 10, 53], [34, 23, 20], [77, 59, 83], [13, 35, 48], [29, 71, 37], [0, 1]], ![[31, 16, 30], [76, 31, 63], [55, 82, 18], [57, 53, 43], [78, 94, 9], [30, 90, 14], [6, 80, 67]], ![[0, 1], [5, 56, 78], [44, 89, 59], [41, 82, 68], [51, 65, 40], [71, 33, 46], [31, 16, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 61], []]
 b := ![[], [37, 40, 57], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [68, 26, 60, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22575555736, -8171418128, -1599648340]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-232737688, -84241424, -16491220]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-91, 22, 1]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-91, 22, 1]] 
 ![![101, 0, 0], ![0, 101, 0], ![10, 22, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-91, 22, 1], ![349, -20, 45], ![7393, 1761, 2]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-10, -22, 101]], ![![-1, 0, 1], ![-1, -10, 45], ![73, 17, 2]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [52, 41, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [60, 100], [0, 1]]
 g := ![![[61, 68], [9], [20, 81], [24], [68], [60, 1]], ![[0, 33], [9], [32, 20], [24], [68], [19, 100]]]
 h' := ![![[60, 100], [28, 13], [71, 98], [22, 92], [19, 23], [11, 13], [0, 1]], ![[0, 1], [0, 88], [93, 3], [88, 9], [86, 78], [84, 88], [60, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53]]
 b := ![[], [13, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [52, 41, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1680, 4302, 1582]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-140, -302, 1582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0], ![-45, 1, 0]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![101, 0, 0], ![-45, 1, 0]] 
 ![![101, 0, 0], ![56, 1, 0], ![99, 0, 1]] where
  M :=![![![101, 0, 0], ![0, 101, 0], ![0, 0, 101]], ![![-45, 1, 0], ![1, -45, 2], ![327, 71, -44]]]
  hmulB := by decide  
  f := ![![![884, -57951, 2576], ![-909, -130088, 0]], ![![490, -32125, 1428], ![-504, -72114, 0]], ![![846, -56803, 2525], ![-937, -127512, 0]]]
  g := ![![![1, 0, 0], ![-56, 101, 0], ![-99, 0, 101]], ![![-1, 1, 0], ![23, -45, 2], ![7, 71, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![101, 0, 0], ![-91, 22, 1]] ![![101, 0, 0], ![-45, 1, 0]]
  ![![101, 0, 0]] where
 M := ![![![10201, 0, 0], ![-4545, 101, 0]], ![![-9191, 2222, 101], ![4444, -1010, 0]]]
 hmul := by decide  
 g := ![![![![101, 0, 0]], ![![-45, 1, 0]]], ![![![-91, 22, 1]], ![![44, -10, 0]]]]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![-25, -17, 1]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![-25, -17, 1]] 
 ![![103, 0, 0], ![0, 103, 0], ![78, 86, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![-25, -17, 1], ![310, 46, -33], ![-5360, -1008, 29]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-78, -86, 103]], ![![-1, -1, 1], ![28, 28, -33], ![-74, -34, 29]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [95, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [47, 102], [0, 1]]
 g := ![![[96, 61], [7, 97], [62, 2], [19], [32], [47, 1]], ![[79, 42], [34, 6], [53, 101], [19], [32], [94, 102]]]
 h' := ![![[47, 102], [56, 24], [84, 71], [98, 65], [7, 88], [67, 54], [0, 1]], ![[0, 1], [51, 79], [22, 32], [63, 38], [23, 15], [30, 49], [47, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [29]]
 b := ![[], [97, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [95, 56, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2145, 1026, 182]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-117, -142, 182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![33, 1, 0]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![33, 1, 0]] 
 ![![103, 0, 0], ![33, 1, 0], ![74, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![33, 1, 0], ![1, 33, 2], ![327, 71, 34]]]
  hmulB := by decide  
  f := ![![![260, 10723, 650], ![206, -33475, 0]], ![![71, 3431, 208], ![104, -10712, 0]], ![![190, 7704, 467], ![138, -24050, 0]]]
  g := ![![![1, 0, 0], ![-33, 103, 0], ![-74, 0, 103]], ![![0, 1, 0], ![-12, 33, 2], ![-44, 71, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![103, 0, 0], ![-25, -17, 1]] ![![103, 0, 0], ![33, 1, 0]]
  ![![103, 0, 0]] where
 M := ![![![10609, 0, 0], ![3399, 103, 0]], ![![-2575, -1751, 103], ![-515, -515, 0]]]
 hmul := by decide  
 g := ![![![![103, 0, 0]], ![![33, 1, 0]]], ![![![-25, -17, 1]], ![![-5, -5, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![17, 1, 0]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![17, 1, 0]] 
 ![![107, 0, 0], ![17, 1, 0], ![70, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![17, 1, 0], ![1, 17, 2], ![327, 71, 18]]]
  hmulB := by decide  
  f := ![![![-423, -7496, -882], ![-107, 47187, 0]], ![![-70, -1190, -140], ![1, 7490, 0]], ![![-278, -4904, -577], ![-62, 30870, 0]]]
  g := ![![![1, 0, 0], ![-17, 107, 0], ![-70, 0, 107]], ![![0, 1, 0], ![-4, 17, 2], ![-20, 71, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N0 : Nat.card (O ⧸ I107N0) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N0)

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := prime_ideal_of_norm_prime hp107.out _ NI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-14, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![-14, 1, 0]] 
 ![![107, 0, 0], ![93, 1, 0], ![63, 0, 1]] where
  M :=![![![-14, 1, 0], ![1, -14, 2], ![327, 71, -13]]]
  hmulB := by decide  
  f := ![![![40, 13, 2]], ![![41, 13, 2]], ![![67, 20, 3]]]
  g := ![![![-1, 1, 0], ![11, -14, 2], ![-51, 71, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1

def I107N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-4, 1, 0]] i)))

def SI107N2: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-4, 1, 0]] 
 ![![107, 0, 0], ![103, 1, 0], ![46, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-4, 1, 0], ![1, -4, 2], ![327, 71, -3]]]
  hmulB := by decide  
  f := ![![![-7415, 29754, -14880], ![642, 796080, 0]], ![![-7140, 28639, -14322], ![536, 766227, 0]], ![![-3186, 12791, -6397], ![323, 342240, 0]]]
  g := ![![![1, 0, 0], ![-103, 107, 0], ![-46, 0, 107]], ![![-1, 1, 0], ![3, -4, 2], ![-64, 71, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N2 : Nat.card (O ⧸ I107N2) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N2)

lemma isPrimeI107N2 : Ideal.IsPrime I107N2 := prime_ideal_of_norm_prime hp107.out _ NI107N2
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![17, 1, 0]] ![![-14, 1, 0]]
  ![![107, 0, 0], ![-65, -52, 1]] where
 M := ![![![-1498, 107, 0]], ![![-237, 3, 2]]]
 hmul := by decide  
 g := ![![![![51, 53, -1], ![107, 0, 0]]], ![![![-1, 1, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI107N1 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-65, -52, 1]] ![![107, 0, 0], ![-4, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![-428, 107, 0]], ![![-6955, -5564, 107], ![535, 214, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![-4, 1, 0]]], ![![![-65, -52, 1]], ![![5, 2, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![8, 14, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![8, 14, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![8, 14, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![8, 14, 1], ![341, 79, 29], ![4777, 1193, 93]]]
  hmulB := by decide  
  f := ![![![-7, -14, -1], ![109, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-8, -14, 109]], ![![0, 0, 1], ![1, -3, 29], ![37, -1, 93]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [28, 54, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 108], [0, 1]]
 g := ![![[72, 74], [66], [107, 43], [12, 82], [82], [55, 1]], ![[0, 35], [66], [74, 66], [53, 27], [82], [1, 108]]]
 h' := ![![[55, 108], [89, 40], [56, 75], [100, 77], [80, 55], [95, 54], [0, 1]], ![[0, 1], [0, 69], [39, 34], [84, 32], [53, 54], [13, 55], [55, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [89, 80]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [28, 54, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![39570, 10987, 1649]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![242, -111, 1649]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-29, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-29, 1, 0]] 
 ![![109, 0, 0], ![80, 1, 0], ![16, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-29, 1, 0], ![1, -29, 2], ![327, 71, -28]]]
  hmulB := by decide  
  f := ![![![-738, 24791, -1710], ![436, 93195, 0]], ![![-539, 18180, -1254], ![328, 68343, 0]], ![![-107, 3639, -251], ![69, 13680, 0]]]
  g := ![![![1, 0, 0], ![-80, 109, 0], ![-16, 0, 109]], ![![-1, 1, 0], ![21, -29, 2], ![-45, 71, -28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![8, 14, 1]] ![![109, 0, 0], ![-29, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3161, 109, 0]], ![![872, 1526, 109], ![109, -327, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-29, 1, 0]]], ![![![8, 14, 1]], ![![1, -3, 0]]]]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [33, 31, 90, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 19, 21], [40, 93, 92], [0, 1]]
 g := ![![[69, 65, 51], [96, 26], [107, 83], [83, 98], [19, 6, 77], [1]], ![[4, 22, 45, 108], [38, 91], [1, 49], [17, 95], [43, 21, 45, 10], [89, 65, 49, 108]], ![[9, 26, 57, 93], [45, 61], [107, 102], [0, 63], [1, 38, 60, 20], [95, 77, 97, 5]]]
 h' := ![![[96, 19, 21], [3, 54, 86], [32, 89, 34], [88, 24, 99], [51, 76, 95], [80, 82, 23], [0, 1]], ![[40, 93, 92], [17, 63, 92], [49, 41, 59], [67, 32, 106], [96, 11, 35], [60, 43, 19], [96, 19, 21]], ![[0, 1], [35, 109, 48], [86, 96, 20], [112, 57, 21], [15, 26, 96], [71, 101, 71], [40, 93, 92]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 103], []]
 b := ![[], [43, 43, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [33, 31, 90, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-599239, -324762, -65766]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5303, -2874, -582]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51225, -14496, -2188]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![-51225, -14496, -2188]] 
 ![![127, 0, 0], ![0, 127, 0], ![111, 5, 1]] where
  M :=![![![-51225, -14496, -2188], ![-729972, -206573, -31180], ![-5175604, -1464628, -221069]]]
  hmulB := by decide  
  f := ![![![1689, 80, -28]], ![![-9076, -299, 132]], ![![1281, 59, -21]]]
  g := ![![![1509, -28, -2188], ![21504, -399, -31180], ![152465, -2829, -221069]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [30, 59, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [68, 126], [0, 1]]
 g := ![![[57, 72], [11, 11], [30, 71], [115, 2], [48, 103], [68, 1]], ![[0, 55], [124, 116], [32, 56], [124, 125], [67, 24], [9, 126]]]
 h' := ![![[68, 126], [51, 31], [116, 97], [106, 84], [84, 111], [119, 22], [0, 1]], ![[0, 1], [0, 96], [108, 30], [103, 43], [12, 16], [91, 105], [68, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [126, 71]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [30, 59, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5953, 3815, 1398]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1175, -25, 1398]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1689, 80, -28]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![1689, 80, -28]] 
 ![![127, 0, 0], ![116, 1, 0], ![67, 0, 1]] where
  M :=![![![1689, 80, -28], ![-9076, -299, 132], ![20588, 108, -219]]]
  hmulB := by decide  
  f := ![![![-51225, -14496, -2188]], ![![-52536, -14867, -2244]], ![![-67777, -19180, -2895]]]
  g := ![![![-45, 80, -28], ![132, -299, 132], ![179, 108, -219]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![-51225, -14496, -2188]] ![![1689, 80, -28]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [63, 110, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [80, 55, 120], [112, 75, 11], [0, 1]]
 g := ![![[32, 28, 101], [71, 68, 112], [70, 59], [40, 64], [125, 105], [61, 1], []], ![[48, 85, 43, 54], [81, 97, 69, 79], [79, 77], [115, 113], [98, 13], [82, 123], [14, 121]], ![[114, 56, 73, 5], [46, 109, 59, 20], [49, 121], [11, 12], [38, 60], [52, 12], [123, 121]]]
 h' := ![![[80, 55, 120], [112, 10, 106], [107, 39, 51], [71, 53, 94], [87, 45, 123], [87, 39, 74], [0, 0, 1], [0, 1]], ![[112, 75, 11], [119, 62, 111], [113, 7, 121], [51, 102, 48], [22, 8, 84], [68, 42, 12], [16, 30, 75], [80, 55, 120]], ![[0, 1], [43, 59, 45], [120, 85, 90], [71, 107, 120], [41, 78, 55], [83, 50, 45], [79, 101, 55], [112, 75, 11]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44, 45], []]
 b := ![[], [98, 95, 16], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [63, 110, 70, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9625487, -3258625, -579675]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-73477, -24875, -4425]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [16, 127, 105, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [18, 17, 111], [14, 119, 26], [0, 1]]
 g := ![![[16, 10, 109], [61, 22], [96, 118], [112, 31, 133], [98, 8], [32, 1], []], ![[38, 1, 27, 57], [39, 119], [98, 73], [122, 122, 107, 110], [129, 8], [100, 50], [61, 128]], ![[99, 125, 65, 12], [102, 38], [78, 107], [113, 94, 84, 29], [], [68, 15], [9, 128]]]
 h' := ![![[18, 17, 111], [90, 99, 71], [92, 52, 61], [126, 80, 114], [2, 135, 63], [36, 30, 75], [0, 0, 1], [0, 1]], ![[14, 119, 26], [105, 29, 121], [27, 92, 16], [122, 82, 115], [127, 125, 14], [37, 73, 62], [33, 133, 119], [18, 17, 111]], ![[0, 1], [99, 9, 82], [19, 130, 60], [50, 112, 45], [99, 14, 60], [109, 34], [52, 4, 17], [14, 119, 26]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 36], []]
 b := ![[], [112, 121, 33], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [16, 127, 105, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11858172, 849126, 1238206]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-86556, 6198, 9038]
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



lemma PB173I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB173I2 : PrimesBelowBoundCertificateInterval O 79 137 173 where
  m := 11
  g := ![1, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB173I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0, I101N1]
    · exact ![I103N0, I103N1]
    · exact ![I107N0, I107N1, I107N2]
    · exact ![I109N0, I109N1]
    · exact ![I113N0]
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
    · exact ![571787]
    · exact ![704969]
    · exact ![912673]
    · exact ![10201, 101]
    · exact ![10609, 103]
    · exact ![107, 107, 107]
    · exact ![11881, 109]
    · exact ![1442897]
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
    · dsimp ; intro j
      fin_cases j
      exact NI89N0
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I101N1, I103N1, I107N0, I107N1, I107N2, I109N1, I127N1]
  Il := ![[], [], [], [I101N1], [I103N1], [I107N0, I107N1, I107N2], [I109N1], [], [I127N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
