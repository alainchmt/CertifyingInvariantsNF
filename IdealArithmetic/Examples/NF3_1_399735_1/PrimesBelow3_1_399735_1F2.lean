
import IdealArithmetic.Examples.NF3_1_399735_1.RI3_1_399735_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-20, -34, 1]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-20, -34, 1]] 
 ![![83, 0, 0], ![0, 83, 0], ![63, 49, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-20, -34, 1], ![384, 22, -69], ![-13440, -2430, 91]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-63, -49, 83]], ![![-1, -1, 1], ![57, 41, -69], ![-231, -83, 91]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [26, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 82], [0, 1]]
 g := ![![[38, 16], [14, 36], [38], [11], [13, 64], [1]], ![[0, 67], [53, 47], [38], [11], [27, 19], [1]]]
 h' := ![![[8, 82], [51, 4], [9, 77], [82, 72], [77, 29], [57, 8], [0, 1]], ![[0, 1], [0, 79], [44, 6], [77, 11], [60, 54], [38, 75], [8, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [33, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [26, 75, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1178, 2152, 464]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-338, -248, 464]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![83, 0, 0], ![-14, 1, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![83, 0, 0], ![-14, 1, 0]] 
 ![![83, 0, 0], ![69, 1, 0], ![75, 0, 1]] where
  M :=![![![83, 0, 0], ![0, 83, 0], ![0, 0, 83]], ![![-14, 1, 0], ![0, -13, 2], ![384, 76, -15]]]
  hmulB := by decide  
  f := ![![![225, -16, 0], ![1328, 0, 0]], ![![183, -13, 0], ![1080, 0, 0]], ![![205, -8, -1], ![1210, 42, 0]]]
  g := ![![![1, 0, 0], ![-69, 83, 0], ![-75, 0, 83]], ![![-1, 1, 0], ![9, -13, 2], ![-45, 76, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![83, 0, 0], ![-20, -34, 1]] ![![83, 0, 0], ![-14, 1, 0]]
  ![![83, 0, 0]] where
 M := ![![![6889, 0, 0], ![-1162, 83, 0]], ![![-1660, -2822, 83], ![664, 498, -83]]]
 hmul := by decide  
 g := ![![![![83, 0, 0]], ![![-14, 1, 0]]], ![![![-20, -34, 1]], ![![8, 6, -1]]]]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [84, 38, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [49, 15, 59], [26, 73, 30], [0, 1]]
 g := ![![[81, 40, 4], [55, 2], [41, 81], [62, 73, 78], [69, 75, 1], []], ![[76, 85, 31, 60], [38, 80], [65, 16], [35, 27, 44, 33], [12, 4, 79, 63], [28, 10]], ![[60, 82, 11, 66], [29, 20], [1, 80], [81, 53, 44, 60], [10, 50, 46, 75], [57, 10]]]
 h' := ![![[49, 15, 59], [57, 65, 87], [7, 7, 25], [43, 88, 80], [78, 67, 16], [0, 0, 1], [0, 1]], ![[26, 73, 30], [29, 63, 40], [62, 24, 13], [87, 64, 85], [51, 24, 48], [49, 11, 73], [49, 15, 59]], ![[0, 1], [3, 50, 51], [6, 58, 51], [1, 26, 13], [19, 87, 25], [71, 78, 15], [26, 73, 30]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 58], []]
 b := ![[], [0, 78, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [84, 38, 14, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3274043, 1816401, 371486]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![36787, 20409, 4174]
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


def P97P0 : CertificateIrreducibleZModOfList' 97 3 2 6 [79, 44, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [77, 49, 41], [63, 47, 56], [0, 1]]
 g := ![![[42, 39, 2], [87, 16], [77, 44], [76, 47], [63, 6], [1]], ![[80, 73, 76, 45], [6, 27], [49, 1], [71, 94], [87, 44], [53, 7, 10, 51]], ![[17, 49, 92, 71], [77, 89], [8, 91], [41, 86], [63, 88], [45, 38, 88, 46]]]
 h' := ![![[77, 49, 41], [15, 78, 14], [1, 63, 93], [19, 47, 23], [3, 20, 12], [18, 53, 43], [0, 1]], ![[63, 47, 56], [8, 94, 73], [71, 92, 67], [16, 3, 1], [75, 71, 26], [35, 43, 23], [77, 49, 41]], ![[0, 1], [94, 22, 10], [58, 39, 34], [60, 47, 73], [1, 6, 59], [15, 1, 31], [63, 47, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 11], []]
 b := ![[], [39, 68, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 3
  hpos := by decide
  P := [79, 44, 54, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-20273, -44814, -21437]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-209, -462, -221]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [7, 60, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 36, 35], [67, 64, 66], [0, 1]]
 g := ![![[3, 64, 100], [56, 70], [47, 64, 6], [55, 31], [7, 96], [1]], ![[16, 79, 85, 26], [57, 23], [67, 91, 11, 67], [48, 64], [58, 84], [52, 85, 13, 51]], ![[25, 33, 70, 29], [86, 20], [55, 80, 48, 41], [72, 13], [27, 58], [57, 27, 49, 50]]]
 h' := ![![[80, 36, 35], [82, 56, 10], [75, 22, 75], [19, 18, 39], [0, 51, 43], [94, 41, 46], [0, 1]], ![[67, 64, 66], [85, 48, 75], [22, 71, 15], [88, 63, 96], [90, 80, 93], [71, 79, 36], [80, 36, 35]], ![[0, 1], [92, 98, 16], [47, 8, 11], [44, 20, 67], [12, 71, 66], [91, 82, 19], [67, 64, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 14], []]
 b := ![[], [61, 82, 40], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [7, 60, 55, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8225541, -3501468, -607616]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81441, -34668, -6016]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![103, 0, 0]] 
 ![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [28, 22, 47, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [93, 29, 55], [66, 73, 48], [0, 1]]
 g := ![![[96, 28, 76], [29, 2, 33], [64, 38, 33], [33, 59], [9, 46], [1]], ![[6, 86, 37, 16], [32, 34, 1, 19], [26, 4, 86, 52], [23, 7], [53, 36], [72, 61, 42, 30]], ![[1, 13, 45, 6], [97, 78, 84, 54], [16, 81, 73, 95], [13, 64], [36, 28], [5, 92, 50, 73]]]
 h' := ![![[93, 29, 55], [12, 60, 30], [62, 83, 41], [86, 7, 62], [17, 55, 33], [75, 81, 56], [0, 1]], ![[66, 73, 48], [33, 57, 31], [91, 76, 39], [84, 62, 70], [78, 63, 78], [74, 52, 97], [93, 29, 55]], ![[0, 1], [12, 89, 42], [25, 47, 23], [89, 34, 74], [12, 88, 95], [89, 73, 53], [66, 73, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83, 89], []]
 b := ![[], [16, 44, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [28, 22, 47, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2333156, -846660, -131222]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-22652, -8220, -1274]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![-26, -11, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![-26, -11, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![81, 96, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![-26, -11, 1], ![384, 39, -23], ![-4608, -682, 62]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-81, -96, 107]], ![![-1, -1, 1], ![21, 21, -23], ![-90, -62, 62]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [51, 88, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [19, 106], [0, 1]]
 g := ![![[29, 81], [93, 25], [11], [0, 44], [14], [19, 1]], ![[70, 26], [33, 82], [11], [87, 63], [14], [38, 106]]]
 h' := ![![[19, 106], [72, 98], [81, 102], [0, 15], [71, 77], [101, 96], [0, 1]], ![[0, 1], [8, 9], [93, 5], [71, 92], [36, 30], [106, 11], [19, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47]]
 b := ![[], [71, 77]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [51, 88, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![153356, 133954, 35807]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-25673, -30874, 35807]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![23, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![23, 1, 0]] 
 ![![107, 0, 0], ![23, 1, 0], ![45, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![23, 1, 0], ![0, 24, 2], ![384, 76, 22]]]
  hmulB := by decide  
  f := ![![![231, 10, 0], ![-1070, 0, 0]], ![![23, 1, 0], ![-106, 0, 0]], ![![95, -8, -1], ![-440, 54, 0]]]
  g := ![![![1, 0, 0], ![-23, 107, 0], ![-45, 0, 107]], ![![0, 1, 0], ![-6, 24, 2], ![-22, 76, 22]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![-26, -11, 1]] ![![107, 0, 0], ![23, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![2461, 107, 0]], ![![-2782, -1177, 107], ![-214, -214, 0]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![23, 1, 0]]], ![![![-26, -11, 1]], ![![-2, -2, 0]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-92, 15, 1]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-92, 15, 1]] 
 ![![109, 0, 0], ![0, 109, 0], ![17, 15, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-92, 15, 1], ![384, -1, 29], ![5376, 1294, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-17, -15, 109]], ![![-1, 0, 1], ![-1, -4, 29], ![54, 16, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [47, 95, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [14, 108], [0, 1]]
 g := ![![[60, 4], [97], [55, 49], [33, 29], [74], [14, 1]], ![[7, 105], [97], [87, 60], [3, 80], [74], [28, 108]]]
 h' := ![![[14, 108], [108, 107], [31, 73], [84, 102], [26, 62], [105, 40], [0, 1]], ![[0, 1], [80, 2], [72, 36], [95, 7], [22, 47], [11, 69], [14, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [54]]
 b := ![[], [29, 27]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [47, 95, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1105, 648, 174]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17, -18, 174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![-29, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![-29, 1, 0]] 
 ![![109, 0, 0], ![80, 1, 0], ![30, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![-29, 1, 0], ![0, -28, 2], ![384, 76, -30]]]
  hmulB := by decide  
  f := ![![![2901, -100, 0], ![10900, 0, 0]], ![![2118, -73, 0], ![7958, 0, 0]], ![![816, -14, -1], ![3066, 55, 0]]]
  g := ![![![1, 0, 0], ![-80, 109, 0], ![-30, 0, 109]], ![![-1, 1, 0], ![20, -28, 2], ![-44, 76, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![-92, 15, 1]] ![![109, 0, 0], ![-29, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![-3161, 109, 0]], ![![-10028, 1635, 109], ![3052, -436, 0]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![-29, 1, 0]]], ![![![-92, 15, 1]], ![![28, -4, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-6, 25, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-6, 25, 1]] 
 ![![113, 0, 0], ![0, 113, 0], ![107, 25, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-6, 25, 1], ![384, 95, 49], ![9216, 2054, 46]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-107, -25, 113]], ![![-1, 0, 1], ![-43, -10, 49], ![38, 8, 46]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [50, 64, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [49, 112], [0, 1]]
 g := ![![[51, 52], [63], [15], [69], [97, 32], [49, 1]], ![[0, 61], [63], [15], [69], [83, 81], [98, 112]]]
 h' := ![![[49, 112], [10, 39], [30, 17], [21, 69], [9, 42], [36, 91], [0, 1]], ![[0, 1], [0, 74], [72, 96], [12, 44], [33, 71], [88, 22], [49, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [92]]
 b := ![[], [3, 46]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [50, 64, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1970, 6331, 2233]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2097, -438, 2233]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0], ![-49, 1, 0]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![113, 0, 0], ![-49, 1, 0]] 
 ![![113, 0, 0], ![64, 1, 0], ![67, 0, 1]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]], ![![-49, 1, 0], ![0, -48, 2], ![384, 76, -50]]]
  hmulB := by decide  
  f := ![![![3431, -70, 0], ![7910, 0, 0]], ![![1912, -39, 0], ![4408, 0, 0]], ![![2069, -18, -1], ![4770, 57, 0]]]
  g := ![![![1, 0, 0], ![-64, 113, 0], ![-67, 0, 113]], ![![-1, 1, 0], ![26, -48, 2], ![-10, 76, -50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![113, 0, 0], ![-6, 25, 1]] ![![113, 0, 0], ![-49, 1, 0]]
  ![![113, 0, 0]] where
 M := ![![![12769, 0, 0], ![-5537, 113, 0]], ![![-678, 2825, 113], ![678, -1130, 0]]]
 hmul := by decide  
 g := ![![![![113, 0, 0]], ![![-49, 1, 0]]], ![![![-6, 25, 1]], ![![6, -10, 0]]]]
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


def P127P0 : CertificateIrreducibleZModOfList' 127 3 2 6 [103, 107, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [6, 82, 24], [98, 44, 103], [0, 1]]
 g := ![![[32, 89, 32], [11, 112, 9], [44, 106, 18], [19, 105, 9], [108, 121, 21], [1]], ![[113, 59, 124, 114], [108, 34, 119, 110], [115, 64, 72, 109], [21, 71, 60, 78], [29, 86, 59, 108], [80, 7, 20, 108]], ![[9, 82, 47, 21], [45, 105, 36, 122], [50, 121, 25, 124], [99, 30, 122, 122], [43, 103, 40, 70], [79, 51, 30, 19]]]
 h' := ![![[6, 82, 24], [10, 63, 64], [40, 32, 3], [75, 16, 48], [52, 52, 3], [24, 20, 104], [0, 1]], ![[98, 44, 103], [41, 95, 10], [55, 11, 11], [6, 17, 83], [60, 0, 110], [104, 83, 103], [6, 82, 24]], ![[0, 1], [21, 96, 53], [107, 84, 113], [37, 94, 123], [47, 75, 14], [113, 24, 47], [98, 44, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 37], []]
 b := ![[], [17, 56, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 3
  hpos := by decide
  P := [103, 107, 23, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-31215711, -10094976, -1460246]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-245793, -79488, -11498]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![131, 0, 0]] 
 ![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [69, 2, 70, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [36, 85, 67], [25, 45, 64], [0, 1]]
 g := ![![[102, 33, 109], [5, 94, 59], [36, 117], [100, 100], [57, 112], [61, 1], []], ![[103, 70, 65, 103], [8, 93, 86, 23], [56, 75], [], [112, 91], [51, 60], [32, 35]], ![[96, 17, 57, 101], [109, 33, 22, 39], [61, 5], [54, 100], [48, 55], [46, 20], [35, 35]]]
 h' := ![![[36, 85, 67], [48, 4, 90], [122, 81, 94], [95, 115, 95], [24, 93, 10], [114, 71, 51], [0, 0, 1], [0, 1]], ![[25, 45, 64], [118, 6, 126], [102, 24, 94], [125, 5, 59], [16, 37], [43, 73, 109], [5, 104, 45], [36, 85, 67]], ![[0, 1], [47, 121, 46], [126, 26, 74], [76, 11, 108], [38, 1, 121], [72, 118, 102], [44, 27, 85], [25, 45, 64]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60, 14], []]
 b := ![[], [107, 4, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [69, 2, 70, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1834, 40348, 16113]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![14, 308, 123]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-47, 62, 1]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-47, 62, 1]] 
 ![![137, 0, 0], ![0, 137, 0], ![90, 62, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-47, 62, 1], ![384, 91, 123], ![23424, 4866, -32]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -62, 137]], ![![-1, 0, 1], ![-78, -55, 123], ![192, 50, -32]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [66, 82, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [55, 136], [0, 1]]
 g := ![![[22, 112], [100], [88], [19, 7], [76], [11], [1]], ![[17, 25], [100], [88], [130, 130], [76], [11], [1]]]
 h' := ![![[55, 136], [4, 89], [113, 127], [116, 122], [19, 12], [68, 58], [71, 55], [0, 1]], ![[0, 1], [104, 48], [111, 10], [113, 15], [131, 125], [107, 79], [82, 82], [55, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [107, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [66, 82, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9365, 9709, 2258]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1415, -951, 2258]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![14, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![14, 1, 0]] 
 ![![137, 0, 0], ![14, 1, 0], ![32, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![14, 1, 0], ![0, 15, 2], ![384, 76, 13]]]
  hmulB := by decide  
  f := ![![![603, 43, 0], ![-5891, 0, 0]], ![![42, 3, 0], ![-410, 0, 0]], ![![120, 1, -1], ![-1172, 69, 0]]]
  g := ![![![1, 0, 0], ![-14, 137, 0], ![-32, 0, 137]], ![![0, 1, 0], ![-2, 15, 2], ![-8, 76, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-47, 62, 1]] ![![137, 0, 0], ![14, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![1918, 137, 0]], ![![-6439, 8494, 137], ![-274, 959, 137]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![14, 1, 0]]], ![![![-47, 62, 1]], ![![-2, 7, 1]]]]
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


lemma PB179I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB179I2 : PrimesBelowBoundCertificateInterval O 79 137 179 where
  m := 11
  g := ![2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB179I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0]
    · exact ![I131N0]
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
    · exact ![704969]
    · exact ![912673]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![2048383]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI97N0
    · dsimp ; intro j
      fin_cases j
      exact NI101N0
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
      exact NI137N1
  β := ![I83N1, I107N1, I109N1, I113N1, I137N1]
  Il := ![[I83N1], [], [], [], [], [I107N1], [I109N1], [I113N1], [], [], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
