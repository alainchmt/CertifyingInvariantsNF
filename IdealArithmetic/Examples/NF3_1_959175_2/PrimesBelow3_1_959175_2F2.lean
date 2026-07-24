
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-789, -32, -47]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-789, -32, -47]] 
 ![![83, 0, 0], ![0, 83, 0], ![68, 36, 1]] where
  M :=![![![-789, -32, -47], ![-8535, -349, -510], ![-8740, -355, -524]]]
  hmulB := by decide  
  f := ![![![-22, 1, 1]], ![![180, -32, 15]], ![![63, -13, 7]]]
  g := ![![![29, 20, -47], ![315, 217, -510], ![324, 223, -524]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [46, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [53, 82], [0, 1]]
 g := ![![[62, 23], [68, 63], [3], [61], [79, 70], [1]], ![[36, 60], [4, 20], [3], [61], [54, 13], [1]]]
 h' := ![![[53, 82], [26, 40], [9, 35], [8, 13], [18, 12], [37, 53], [0, 1]], ![[0, 1], [71, 43], [38, 48], [33, 70], [73, 71], [24, 30], [53, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [9, 67]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [46, 30, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5546, 2443, -1742]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1494, 785, -1742]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22, 1, 1]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-22, 1, 1]] 
 ![![83, 0, 0], ![28, 1, 0], ![33, 0, 1]] where
  M :=![![![-22, 1, 1], ![180, -32, 15], ![245, 5, -27]]]
  hmulB := by decide  
  f := ![![![-789, -32, -47]], ![![-369, -15, -22]], ![![-419, -17, -25]]]
  g := ![![![-1, 1, 1], ![7, -32, 15], ![12, 5, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-789, -32, -47]] ![![-22, 1, 1]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![89, 0, 0]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![89, 0, 0]] 
 ![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]] where
  M :=![![![89, 0, 0], ![0, 89, 0], ![0, 0, 89]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [18, 16, 56, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 0, 77], [66, 88, 12], [0, 1]]
 g := ![![[76, 60, 2], [32, 49], [49, 57], [36, 35, 2], [5, 33, 1], []], ![[72, 56, 41, 6], [55, 73], [72, 40], [79, 80, 69, 51], [71, 79, 51, 77], [35, 55]], ![[75, 10, 18, 33], [36, 87], [31, 73], [60, 56, 43, 28], [41, 52], [11, 55]]]
 h' := ![![[56, 0, 77], [58, 82, 64], [10, 56, 82], [64, 41, 71], [88, 38, 64], [0, 0, 1], [0, 1]], ![[66, 88, 12], [28, 35, 20], [22, 81, 47], [61, 43, 60], [86, 35, 14], [14, 52, 88], [56, 0, 77]], ![[0, 1], [43, 61, 5], [54, 41, 49], [16, 5, 47], [17, 16, 11], [64, 37], [66, 88, 12]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [49, 41], []]
 b := ![[], [24, 40, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [18, 16, 56, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87169982, -6422863, 271094]
  a := ![-12, -7, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![979438, -72167, 3046]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-10, 10, 1]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-10, 10, 1]] 
 ![![97, 0, 0], ![0, 97, 0], ![87, 10, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-10, 10, 1], ![135, -38, 132], ![1910, -67, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-87, -10, 97]], ![![-1, 0, 1], ![-117, -14, 132], ![17, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [83, 67, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [30, 96], [0, 1]]
 g := ![![[16, 62], [24], [4], [25], [32], [30, 1]], ![[33, 35], [24], [4], [25], [32], [60, 96]]]
 h' := ![![[30, 96], [94, 81], [7, 86], [57, 95], [17, 92], [32, 41], [0, 1]], ![[0, 1], [2, 16], [65, 11], [94, 2], [61, 5], [1, 56], [30, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [81, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [83, 67, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3552396, 4167834, -2253743]
  a := ![197, 67, -525]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2058021, 275312, -2253743]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![97, 0, 0], ![-35, 1, 0]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![97, 0, 0], ![-35, 1, 0]] 
 ![![97, 0, 0], ![62, 1, 0], ![94, 0, 1]] where
  M :=![![![97, 0, 0], ![0, 97, 0], ![0, 0, 97]], ![![-35, 1, 0], ![-5, -37, 13], ![185, -8, -33]]]
  hmulB := by decide  
  f := ![![![12781, 103932, -36504], ![-3492, 272376, 0]], ![![8166, 66401, -23322], ![-2230, 174018, 0]], ![![12372, 100718, -35375], ![-3422, 263952, 0]]]
  g := ![![![1, 0, 0], ![-62, 97, 0], ![-94, 0, 97]], ![![-1, 1, 0], ![11, -37, 13], ![39, -8, -33]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![97, 0, 0], ![-10, 10, 1]] ![![97, 0, 0], ![-35, 1, 0]]
  ![![97, 0, 0]] where
 M := ![![![9409, 0, 0], ![-3395, 97, 0]], ![![-970, 970, 97], ![485, -388, 97]]]
 hmul := by decide  
 g := ![![![![97, 0, 0]], ![![-35, 1, 0]]], ![![![-10, 10, 1]], ![![5, -4, 1]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [36, 59, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [21, 89, 14], [76, 11, 87], [0, 1]]
 g := ![![[92, 27, 22], [64, 49], [65, 87, 49], [96, 58], [4, 16], [1]], ![[7, 33, 4, 54], [84, 45], [18, 53, 62, 36], [62, 37], [89, 6], [41, 35, 47, 17]], ![[36, 77, 74, 16], [73, 65], [28, 45, 22, 24], [12, 4], [63, 13], [2, 22, 72, 84]]]
 h' := ![![[21, 89, 14], [5, 4, 27], [84, 33, 7], [43, 88, 94], [41, 2, 82], [65, 42, 97], [0, 1]], ![[76, 11, 87], [39, 49, 50], [72, 93, 34], [71, 71, 44], [92, 5, 21], [8, 39, 39], [21, 89, 14]], ![[0, 1], [29, 48, 24], [58, 76, 60], [74, 43, 64], [1, 94, 99], [59, 20, 66], [76, 11, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 66], []]
 b := ![[], [47, 76, 53], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [36, 59, 4, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-83962007, 7343407, -1304112]
  a := ![12, 6, -31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-831307, 72707, -12912]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [91, 74, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [43, 46], [64, 56], [0, 1]]
 g := ![![[98, 28, 76], [101, 24, 13], [71, 61, 13], [11, 100], [90, 16], [1]], ![[98, 51, 33], [38, 2, 7], [54, 56, 7], [88, 68], [57, 15], [1]], ![[66, 24, 97], [89, 77, 83], [58, 89, 83], [25, 38], [84, 72], [1]]]
 h' := ![![[43, 46], [79, 87, 73], [28, 69, 61], [70, 70, 42], [91, 99, 10], [12, 29, 4], [0, 1]], ![[64, 56], [56, 64, 71], [12, 71, 17], [89, 40, 86], [75, 30, 45], [3, 60, 18], [43, 46]], ![[0, 1], [84, 55, 62], [96, 66, 25], [40, 96, 78], [7, 77, 48], [21, 14, 81], [64, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51], []]
 b := ![[], [43, 90, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [91, 74, 99, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4454029, 741806, -368225]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43243, 7202, -3575]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![13, -12, 1]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![107, 0, 0], ![13, -12, 1]] 
 ![![107, 0, 0], ![0, 107, 0], ![13, 95, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![13, -12, 1], ![245, 29, -154], ![-2160, 109, -18]]]
  hmulB := by decide  
  f := ![![![-12, 12, -1], ![107, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-13, -95, 107]], ![![0, -1, 1], ![21, 137, -154], ![-18, 17, -18]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [69, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [50, 106], [0, 1]]
 g := ![![[52, 76], [99, 13], [11], [49, 11], [44], [50, 1]], ![[0, 31], [0, 94], [11], [64, 96], [44], [100, 106]]]
 h' := ![![[50, 106], [17, 66], [20, 21], [43, 15], [101, 15], [81, 77], [0, 1]], ![[0, 1], [0, 41], [0, 86], [44, 92], [102, 92], [79, 30], [50, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [49, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [69, 57, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![149177, 501, 2446]
  a := ![-8, 16, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1097, -2167, 2446]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![107, 0, 0], ![47, 1, 0]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![107, 0, 0], ![47, 1, 0]] 
 ![![107, 0, 0], ![47, 1, 0], ![18, 0, 1]] where
  M :=![![![107, 0, 0], ![0, 107, 0], ![0, 0, 107]], ![![47, 1, 0], ![-5, 45, 13], ![185, -8, 49]]]
  hmulB := by decide  
  f := ![![![18501, -191940, -55432], ![6420, 456248, 0]], ![![8091, -84267, -24336], ![2890, 200304, 0]], ![![3111, -32289, -9325], ![1083, 76752, 0]]]
  g := ![![![1, 0, 0], ![-47, 107, 0], ![-18, 0, 107]], ![![0, 1, 0], ![-22, 45, 13], ![-3, -8, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![107, 0, 0], ![13, -12, 1]] ![![107, 0, 0], ![47, 1, 0]]
  ![![107, 0, 0]] where
 M := ![![![11449, 0, 0], ![5029, 107, 0]], ![![1391, -1284, 107], ![856, -535, -107]]]
 hmul := by decide  
 g := ![![![![107, 0, 0]], ![![47, 1, 0]]], ![![![13, -12, 1]], ![![8, -5, -1]]]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![18, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![109, 0, 0], ![18, 1, 0]] 
 ![![109, 0, 0], ![18, 1, 0], ![11, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![18, 1, 0], ![-5, 16, 13], ![185, -8, 20]]]
  hmulB := by decide  
  f := ![![![19636, -64297, -52221], ![2725, 437853, 0]], ![![3225, -10613, -8619], ![546, 72267, 0]], ![![1976, -6489, -5270], ![309, 44187, 0]]]
  g := ![![![1, 0, 0], ![-18, 109, 0], ![-11, 0, 109]], ![![0, 1, 0], ![-4, 16, 13], ![1, -8, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![43, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![109, 0, 0], ![43, 1, 0]] 
 ![![109, 0, 0], ![43, 1, 0], ![82, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![43, 1, 0], ![-5, 41, 13], ![185, -8, 45]]]
  hmulB := by decide  
  f := ![![![9490, -87357, -27690], ![2943, 232170, 0]], ![![3727, -34451, -10920], ![1200, 91560, 0]], ![![7101, -65719, -20831], ![2311, 174660, 0]]]
  g := ![![![1, 0, 0], ![-43, 109, 0], ![-82, 0, 109]], ![![0, 1, 0], ![-26, 41, 13], ![-29, -8, 45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![109, 0, 0], ![48, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![109, 0, 0], ![48, 1, 0]] 
 ![![109, 0, 0], ![48, 1, 0], ![31, 0, 1]] where
  M :=![![![109, 0, 0], ![0, 109, 0], ![0, 0, 109]], ![![48, 1, 0], ![-5, 46, 13], ![185, -8, 50]]]
  hmulB := by decide  
  f := ![![![6291, -66720, -18850], ![2180, 158050, 0]], ![![2758, -29357, -8294], ![982, 69542, 0]], ![![1761, -18976, -5361], ![684, 44950, 0]]]
  g := ![![![1, 0, 0], ![-48, 109, 0], ![-31, 0, 109]], ![![0, 1, 0], ![-24, 46, 13], ![-9, -8, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![18, 1, 0]] ![![109, 0, 0], ![43, 1, 0]]
  ![![109, 0, 0], ![34, -29, 1]] where
 M := ![![![11881, 0, 0], ![4687, 109, 0]], ![![1962, 109, 0], ![769, 59, 13]]]
 hmul := by decide  
 g := ![![![![75, 29, -1], ![109, 0, 0]], ![![9, 30, -1], ![109, 0, 0]]], ![![![-16, 30, -1], ![109, 0, 0]], ![![3, 4, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![109, 0, 0], ![34, -29, 1]] ![![109, 0, 0], ![48, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![11881, 0, 0], ![5232, 109, 0]], ![![3706, -3161, 109], ![1962, -1308, -327]]]
 hmul := by decide  
 g := ![![![![109, 0, 0]], ![![48, 1, 0]]], ![![![34, -29, 1]], ![![18, -12, -3]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113, 0, 0]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![113, 0, 0]] 
 ![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]] where
  M :=![![![113, 0, 0], ![0, 113, 0], ![0, 0, 113]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [91, 8, 0, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [37, 29, 14], [76, 83, 99], [0, 1]]
 g := ![![[89, 58, 82], [47, 4], [21, 1], [50, 56], [64], [1]], ![[95, 26, 62, 49], [104, 44], [98, 16], [29, 4], [68, 93, 87, 14], [53, 96, 102, 32]], ![[20, 111, 97, 41], [78, 14], [58, 25], [97, 112], [54, 69, 23, 99], [62, 25, 101, 81]]]
 h' := ![![[37, 29, 14], [16, 8, 46], [98, 73, 111], [75, 67, 1], [52, 85, 100], [22, 105], [0, 1]], ![[76, 83, 99], [14, 66, 88], [41, 46, 65], [91, 97, 4], [73, 21, 111], [65, 107, 1], [37, 29, 14]], ![[0, 1], [73, 39, 92], [74, 107, 50], [43, 62, 108], [13, 7, 15], [92, 14, 112], [76, 83, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 24], []]
 b := ![[], [40, 10, 79], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [91, 8, 0, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-30074498, 2263503, 127803]
  a := ![8, 6, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-266146, 20031, 1131]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![4, -37, 1]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![127, 0, 0], ![4, -37, 1]] 
 ![![127, 0, 0], ![0, 127, 0], ![4, 90, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![4, -37, 1], ![370, 70, -479], ![-6785, 309, -77]]]
  hmulB := by decide  
  f := ![![![-3, 37, -1], ![127, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-4, -90, 127]], ![![0, -1, 1], ![18, 340, -479], ![-51, 57, -77]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [95, 99, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [28, 126], [0, 1]]
 g := ![![[112, 79], [61, 72], [91, 99], [90, 64], [108, 122], [28, 1]], ![[38, 48], [45, 55], [69, 28], [104, 63], [95, 5], [56, 126]]]
 h' := ![![[28, 126], [47, 29], [118, 31], [86, 90], [27, 119], [7, 54], [0, 1]], ![[0, 1], [97, 98], [97, 96], [66, 37], [57, 8], [122, 73], [28, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [73, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [95, 99, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![10860, 9781, -2873]
  a := ![-10, -3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![176, 2113, -2873]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-29, 1, 0]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-29, 1, 0]] 
 ![![127, 0, 0], ![98, 1, 0], ![77, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-29, 1, 0], ![-5, -31, 13], ![185, -8, -27]]]
  hmulB := by decide  
  f := ![![![18847, 121546, -50960], ![-3302, 497840, 0]], ![![14541, 93764, -39312], ![-2539, 384048, 0]], ![![11434, 73693, -30897], ![-1971, 301840, 0]]]
  g := ![![![1, 0, 0], ![-98, 127, 0], ![-77, 0, 127]], ![![-1, 1, 0], ![16, -31, 13], ![24, -8, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![127, 0, 0], ![4, -37, 1]] ![![127, 0, 0], ![-29, 1, 0]]
  ![![127, 0, 0]] where
 M := ![![![16129, 0, 0], ![-3683, 127, 0]], ![![508, -4699, 127], ![254, 1143, -508]]]
 hmul := by decide  
 g := ![![![![127, 0, 0]], ![![-29, 1, 0]]], ![![![4, -37, 1]], ![![2, 9, -4]]]]
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


def P131P0 : CertificateIrreducibleZModOfList' 131 3 2 7 [62, 93, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [103, 114, 59], [18, 16, 72], [0, 1]]
 g := ![![[123, 9, 49], [48, 111, 59], [11, 7], [0, 123], [3, 49], [121, 1], []], ![[32, 96, 85, 39], [50, 19, 39, 105], [127, 27], [79, 49], [50, 129], [94, 125], [126, 75]], ![[31, 118, 106, 98], [32, 53, 85, 127], [39, 59], [102, 43], [94, 48], [110, 27], [113, 75]]]
 h' := ![![[103, 114, 59], [37, 45, 7], [115, 121, 37], [81, 34, 111], [122, 113, 75], [96, 82, 7], [0, 0, 1], [0, 1]], ![[18, 16, 72], [16, 53, 16], [1, 21, 2], [43, 23, 114], [15, 50, 7], [87, 79, 103], [46, 42, 16], [103, 114, 59]], ![[0, 1], [54, 33, 108], [29, 120, 92], [58, 74, 37], [116, 99, 49], [124, 101, 21], [130, 89, 114], [18, 16, 72]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 114], []]
 b := ![[], [111, 102, 78], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 3
  hpos := by decide
  P := [62, 93, 10, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-159397918, 15394465, -5304845]
  a := ![15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1216778, 117515, -40495]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-60, 1, 0]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-60, 1, 0]] 
 ![![137, 0, 0], ![77, 1, 0], ![135, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-60, 1, 0], ![-5, -62, 13], ![185, -8, -58]]]
  hmulB := by decide  
  f := ![![![29076, 412680, -86515], ![-9590, 911735, 0]], ![![16361, 231919, -48620], ![-5342, 512380, 0]], ![![28620, 406656, -85252], ![-9522, 898425, 0]]]
  g := ![![![1, 0, 0], ![-77, 137, 0], ![-135, 0, 137]], ![![-1, 1, 0], ![22, -62, 13], ![63, -8, -58]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N0 : Nat.card (O ⧸ I137N0) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N0)

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := prime_ideal_of_norm_prime hp137.out _ NI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-58, 1, 0]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-58, 1, 0]] 
 ![![137, 0, 0], ![79, 1, 0], ![27, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-58, 1, 0], ![-5, -60, 13], ![185, -8, -56]]]
  hmulB := by decide  
  f := ![![![51755, 706082, -152958], ![-16714, 1611942, 0]], ![![29861, 407110, -88192], ![-9589, 929408, 0]], ![![10249, 139154, -30145], ![-3178, 317682, 0]]]
  g := ![![![1, 0, 0], ![-79, 137, 0], ![-27, 0, 137]], ![![-1, 1, 0], ![32, -60, 13], ![17, -8, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1

def I137N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![137, 0, 0], ![-19, 1, 0]] i)))

def SI137N2: IdealEqSpanCertificate' Table ![![137, 0, 0], ![-19, 1, 0]] 
 ![![137, 0, 0], ![118, 1, 0], ![127, 0, 1]] where
  M :=![![![137, 0, 0], ![0, 137, 0], ![0, 0, 137]], ![![-19, 1, 0], ![-5, -21, 13], ![185, -8, -17]]]
  hmulB := by decide  
  f := ![![![9948, 42343, -26208], ![-959, 276192, 0]], ![![8567, 36462, -22568], ![-821, 237832, 0]], ![![9208, 39253, -24295], ![-989, 256032, 0]]]
  g := ![![![1, 0, 0], ![-118, 137, 0], ![-127, 0, 137]], ![![-1, 1, 0], ![6, -21, 13], ![24, -8, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N2 : Nat.card (O ⧸ I137N2) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N2)

lemma isPrimeI137N2 : Ideal.IsPrime I137N2 := prime_ideal_of_norm_prime hp137.out _ NI137N2
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![-60, 1, 0]] ![![137, 0, 0], ![-58, 1, 0]]
  ![![137, 0, 0], ![46, 54, 1]] where
 M := ![![![18769, 0, 0], ![-7946, 137, 0]], ![![-8220, 137, 0], ![3475, -120, 13]]]
 hmul := by decide  
 g := ![![![![91, -54, -1], ![137, 0, 0]], ![![-58, 1, 0], ![0, 0, 0]]], ![![![-60, 1, 0], ![0, 0, 0]], ![![21, -6, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI137N1 : IdealMulLeCertificate' Table 
  ![![137, 0, 0], ![46, 54, 1]] ![![137, 0, 0], ![-19, 1, 0]]
  ![![137, 0, 0]] where
 M := ![![![18769, 0, 0], ![-2603, 137, 0]], ![![6302, 7398, 137], ![-959, -1096, 685]]]
 hmul := by decide  
 g := ![![![![137, 0, 0]], ![![-19, 1, 0]]], ![![![46, 54, 1]], ![![-7, -8, 5]]]]
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


lemma PB278I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB278I2 : PrimesBelowBoundCertificateInterval O 79 137 278 where
  m := 11
  g := ![2, 1, 2, 1, 1, 2, 3, 1, 2, 1, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB278I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0, I83N1]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0]
    · exact ![I127N0, I127N1]
    · exact ![I131N0]
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
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![109, 109, 109]
    · exact ![1442897]
    · exact ![16129, 127]
    · exact ![2248091]
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
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
      exact NI107N1
    · dsimp ; intro j
      fin_cases j
      exact NI109N0
      exact NI109N1
      exact NI109N2
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
      exact NI137N1
      exact NI137N2
  β := ![I83N1, I97N1, I107N1, I109N0, I109N1, I109N2, I127N1, I137N0, I137N1, I137N2]
  Il := ![[I83N1], [], [I97N1], [], [], [I107N1], [I109N0, I109N1, I109N2], [], [I127N1], [], [I137N0, I137N1, I137N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
