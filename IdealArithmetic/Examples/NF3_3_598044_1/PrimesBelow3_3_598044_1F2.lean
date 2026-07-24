
import IdealArithmetic.Examples.NF3_3_598044_1.RI3_3_598044_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [37, 20, 5, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [46, 39, 74], [32, 43, 9], [0, 1]]
 g := ![![[1, 67, 63], [53, 68, 40], [8, 23], [70, 33], [5, 78, 1], []], ![[35, 14, 69, 66], [61, 60, 42, 42], [28, 30], [71, 27], [23, 31, 71, 42], [55, 81]], ![[47, 31, 47, 61], [3, 8, 41, 25], [69, 11], [58, 36], [8, 50, 32, 77], [37, 81]]]
 h' := ![![[46, 39, 74], [31, 23, 48], [14, 80, 66], [12, 42, 40], [64, 2, 38], [0, 0, 1], [0, 1]], ![[32, 43, 9], [80, 37, 31], [76, 70, 43], [38, 36, 14], [80, 75, 39], [81, 72, 43], [46, 39, 74]], ![[0, 1], [60, 23, 4], [56, 16, 57], [6, 5, 29], [49, 6, 6], [70, 11, 39], [32, 43, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 64], []]
 b := ![[], [72, 9, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [37, 20, 5, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9628, -88063, -48555]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![116, -1061, -585]
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


def P89P0 : CertificateIrreducibleZModOfList' 89 3 2 6 [5, 71, 22, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 18, 5], [8, 70, 84], [0, 1]]
 g := ![![[6, 34, 80], [14, 84], [25, 53], [15, 58, 50], [57, 67, 1], []], ![[3, 5, 36, 49], [81, 67], [58, 21], [54, 77, 61, 8], [26, 18, 25, 25], [75, 25]], ![[34, 21, 58, 72], [68, 39], [79, 10], [72, 84, 78, 50], [42, 83, 48, 71], [85, 25]]]
 h' := ![![[59, 18, 5], [76, 20, 76], [71, 64, 66], [14, 37, 63], [71, 68, 36], [0, 0, 1], [0, 1]], ![[8, 70, 84], [38, 77, 80], [49, 42, 45], [28, 11, 56], [21, 36, 12], [80, 56, 70], [59, 18, 5]], ![[0, 1], [34, 81, 22], [75, 72, 67], [84, 41, 59], [79, 74, 41], [84, 33, 18], [8, 70, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [73, 75], []]
 b := ![[], [24, 9, 74], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 3
  hpos := by decide
  P := [5, 71, 22, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2937, 74582, 126736]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-33, 838, 1424]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![82, 63, 11]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![82, 63, 11]] 
 ![![97, 0, 0], ![0, 97, 0], ![78, 41, 1]] where
  M :=![![![82, 63, 11], ![-66, 607, 126], ![-345, 2613, 544]]]
  hmulB := by decide  
  f := ![![![10, -57, 13]], ![![-78, 499, -114]], ![![-21, 140, -32]]]
  g := ![![![-8, -4, 11], ![-102, -47, 126], ![-441, -203, 544]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [16, 92, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [5, 96], [0, 1]]
 g := ![![[30, 91], [89], [35], [54], [81], [5, 1]], ![[0, 6], [89], [35], [54], [81], [10, 96]]]
 h' := ![![[5, 96], [23, 73], [34, 63], [20, 36], [60, 32], [17, 9], [0, 1]], ![[0, 1], [0, 24], [58, 34], [6, 61], [26, 65], [62, 88], [5, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20]]
 b := ![[], [72, 10]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [16, 92, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1773, -3, 78]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-81, -33, 78]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10, 57, -13]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-10, 57, -13]] 
 ![![97, 0, 0], ![15, 1, 0], ![74, 0, 1]] where
  M :=![![![-10, 57, -13], ![78, -499, 114], ![-381, 2433, -556]]]
  hmulB := by decide  
  f := ![![![-82, -63, -11]], ![![-12, -16, -3]], ![![-59, -75, -14]]]
  g := ![![![1, 57, -13], ![-9, -499, 114], ![44, 2433, -556]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![82, 63, 11]] ![![-10, 57, -13]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [70, 18, 15, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 60, 95], [19, 40, 6], [0, 1]]
 g := ![![[38, 41, 14], [29, 100], [70, 3, 47], [57, 36], [94, 23], [1]], ![[14, 85, 58, 23], [50, 43], [33, 92, 51, 95], [67, 64], [80, 68], [32, 100, 24, 87]], ![[84, 95, 83, 68], [41, 80], [92, 52, 41, 87], [23, 4], [37, 4], [77, 58, 70, 14]]]
 h' := ![![[67, 60, 95], [68, 45, 69], [49, 70, 91], [5, 95, 42], [37, 26, 95], [31, 83, 86], [0, 1]], ![[19, 40, 6], [72, 8, 66], [80, 51, 89], [1, 17, 100], [34, 20, 8], [68, 19, 13], [67, 60, 95]], ![[0, 1], [7, 48, 67], [7, 81, 22], [58, 90, 60], [31, 55, 99], [55, 100, 2], [19, 40, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 12], []]
 b := ![[], [17, 8, 2], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [70, 18, 15, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![19190, -222200, -206242]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![190, -2200, -2042]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [69, 11, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [67, 21, 41], [91, 81, 62], [0, 1]]
 g := ![![[5, 52, 97], [4, 84, 13], [82, 59, 52], [77, 23], [56, 38], [1]], ![[68, 55, 91, 41], [70, 41, 35, 16], [23, 1, 99, 50], [10, 64], [27, 66], [14, 87, 68, 14]], ![[40, 15, 0, 53], [34, 76, 36, 54], [46, 3, 18, 101], [84, 13], [46, 13], [65, 83, 39, 89]]]
 h' := ![![[67, 21, 41], [33, 80, 32], [7, 21, 61], [16, 32, 19], [73, 31, 34], [34, 92, 55], [0, 1]], ![[91, 81, 62], [73, 55, 1], [2, 31, 34], [57, 58, 70], [51, 51, 8], [67, 95, 90], [67, 21, 41]], ![[0, 1], [64, 71, 70], [83, 51, 8], [82, 13, 14], [78, 21, 61], [70, 19, 61], [91, 81, 62]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [85, 44], []]
 b := ![[], [37, 25, 14], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [69, 11, 48, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7725, -67362, -31930]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![75, -654, -310]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-56294, 433285, 90169]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![-56294, 433285, 90169]] 
 ![![107, 0, 0], ![0, 107, 0], ![94, 99, 1]] where
  M :=![![![-56294, 433285, 90169], ![-541014, 4164089, 866570], ![-2329203, 17927463, 3730804]]]
  hmulB := by decide  
  f := ![![![16022, -1, -387]], ![![2322, -233, -2]], ![![16213, -206, -344]]]
  g := ![![![-79740, -79378, 90169], ![-766342, -762863, 866570], ![-3299297, -3284319, 3730804]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [57, 1, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 106], [0, 1]]
 g := ![![[92, 92], [7, 90], [33], [67, 9], [33], [106, 1]], ![[0, 15], [24, 17], [33], [58, 98], [33], [105, 106]]]
 h' := ![![[106, 106], [29, 29], [64, 25], [33, 56], [84, 3], [57, 51], [0, 1]], ![[0, 1], [0, 78], [39, 82], [84, 51], [81, 104], [6, 56], [106, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [33, 66]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [57, 1, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3658, 34417, 19385]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-17064, -17614, 19385]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![16022, -1, -387]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![16022, -1, -387]] 
 ![![107, 0, 0], ![16, 1, 0], ![78, 0, 1]] where
  M :=![![![16022, -1, -387], ![2322, -233, -2], ![-1155, 1119, -232]]]
  hmulB := by decide  
  f := ![![![-56294, 433285, 90169]], ![![-13474, 103707, 21582]], ![![-62805, 483399, 100598]]]
  g := ![![![432, -1, -387], ![58, -233, -2], ![-9, 1119, -232]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![-56294, 433285, 90169]] ![![16022, -1, -387]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![602737, -1022, -14330]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![602737, -1022, -14330]] 
 ![![109, 0, 0], ![0, 109, 0], ![84, 35, 1]] where
  M :=![![![602737, -1022, -14330], ![85980, -145, -2044], ![-36858, 66, 877]]]
  hmulB := by decide  
  f := ![![![-71, 454, -102]], ![![612, -3901, 908]], ![![114, -725, 173]]]
  g := ![![![16573, 4592, -14330], ![2364, 655, -2044], ![-1014, -281, 877]]]
  hle1 := by decide   
  hle2 := by decide  


def P109P0 : CertificateIrreducibleZModOfList' 109 2 2 6 [11, 73, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [36, 108], [0, 1]]
 g := ![![[76, 80], [31], [77, 3], [48, 106], [93], [36, 1]], ![[13, 29], [31], [76, 106], [49, 3], [93], [72, 108]]]
 h' := ![![[36, 108], [66, 25], [25, 85], [17, 60], [32, 91], [40, 86], [0, 1]], ![[0, 1], [94, 84], [33, 24], [106, 49], [38, 18], [84, 23], [36, 108]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [39]]
 b := ![[], [85, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 2
  hpos := by decide
  P := [11, 73, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-82, 311, 121]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-94, -36, 121]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI109N0 B_one_repr
lemma NI109N0 : Nat.card (O ⧸ I109N0) = 11881 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, -454, 102]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![71, -454, 102]] 
 ![![109, 0, 0], ![39, 1, 0], ![92, 0, 1]] where
  M :=![![![71, -454, 102], ![-612, 3901, -908], ![3030, -19374, 4355]]]
  hmulB := by decide  
  f := ![![![-602737, 1022, 14330]], ![![-216447, 367, 5146]], ![![-508394, 862, 12087]]]
  g := ![![![77, -454, 102], ![-635, 3901, -908], ![3284, -19374, 4355]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![602737, -1022, -14330]] ![![71, -454, 102]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-7502, 47893, -10943]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-7502, 47893, -10943]] 
 ![![113, 0, 0], ![0, 113, 0], ![98, 68, 1]] where
  M :=![![![-7502, 47893, -10943], ![65658, -419215, 95786], ![-320187, 2044335, -467108]]]
  hmulB := by decide  
  f := ![![![-70, -403, -81]], ![![486, -3875, -806]], ![![251, -2829, -586]]]
  g := ![![![9424, 7009, -10943], ![-82490, -61351, 95786], ![402269, 299183, -467108]]]
  hle1 := by decide   
  hle2 := by decide  


def P113P0 : CertificateIrreducibleZModOfList' 113 2 2 6 [58, 7, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [106, 112], [0, 1]]
 g := ![![[80, 105], [7], [15], [4], [35, 81], [106, 1]], ![[23, 8], [7], [15], [4], [33, 32], [99, 112]]]
 h' := ![![[106, 112], [35, 52], [21, 32], [10, 69], [4, 111], [67, 104], [0, 1]], ![[0, 1], [10, 61], [23, 81], [92, 44], [18, 2], [17, 9], [106, 112]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [34, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 2
  hpos := by decide
  P := [58, 7, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47, 1215, 1103]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-957, -653, 1103]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI113N0 B_one_repr
lemma NI113N0 : Nat.card (O ⧸ I113N0) = 12769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, -403, -81]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![-70, -403, -81]] 
 ![![113, 0, 0], ![90, 1, 0], ![86, 0, 1]] where
  M :=![![![-70, -403, -81], ![486, -3875, -806], ![2175, -16683, -3472]]]
  hmulB := by decide  
  f := ![![![-7502, 47893, -10943]], ![![-5394, 34435, -7868]], ![![-8543, 54541, -12462]]]
  g := ![![![382, -403, -81], ![3704, -3875, -806], ![15949, -16683, -3472]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-7502, 47893, -10943]] ![![-70, -403, -81]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![328, -1485, 337]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![328, -1485, 337]] 
 ![![127, 0, 0], ![34, 1, 0], ![40, 0, 1]] where
  M :=![![![328, -1485, 337], ![-2022, 12997, -2970], ![9921, -63381, 14482]]]
  hmulB := by decide  
  f := ![![![-19016, 146373, 30461]], ![![-6530, 50263, 10460]], ![![-12185, 93789, 19518]]]
  g := ![![![294, -1485, 337], ![-2560, 12997, -2970], ![12485, -63381, 14482]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N0 : Nat.card (O ⧸ I127N0) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N0)

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := prime_ideal_of_norm_prime hp127.out _ NI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9439, -14, -224]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![9439, -14, -224]] 
 ![![127, 0, 0], ![35, 1, 0], ![5, 0, 1]] where
  M :=![![![9439, -14, -224], ![1344, 17, -28], ![-588, 84, 31]]]
  hmulB := by decide  
  f := ![![![-2879, 18382, -4200]], ![![-595, 3799, -868]], ![![-1081, 6902, -1577]]]
  g := ![![![87, -14, -224], ![7, 17, -28], ![-29, 84, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1

def I127N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73447, -134, -1744]] i)))

def SI127N2: IdealEqSpanCertificate' Table ![![73447, -134, -1744]] 
 ![![127, 0, 0], ![57, 1, 0], ![125, 0, 1]] where
  M :=![![![73447, -134, -1744], ![10464, 65, -268], ![-4428, -396, 199]]]
  hmulB := by decide  
  f := ![![![93193, -717290, -149272]], ![![48879, -376213, -78292]], ![![122087, -939682, -195553]]]
  g := ![![![2355, -134, -1744], ![317, 65, -268], ![-53, -396, 199]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N2 : Nat.card (O ⧸ I127N2) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N2)

lemma isPrimeI127N2 : Ideal.IsPrime I127N2 := prime_ideal_of_norm_prime hp127.out _ NI127N2
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![328, -1485, 337]] ![![9439, -14, -224]]
  ![![901996, -1529, -21445]] where
 M := ![![![901996, -1529, -21445]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI127N1 : IdealMulLeCertificate' Table 
  ![![901996, -1529, -21445]] ![![73447, -134, -1744]]
  ![![127, 0, 0]] where
 M := ![![![66327859216, -112474629, -1576938807]]]
 hmul := by decide  
 g := ![![![![522266608, -885627, -12416841]]]]
 hle2 := by decide  


def PBC127 : ContainsPrimesAboveP 127 ![I127N0, I127N1, I127N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI127N0
    exact isPrimeI127N1
    exact isPrimeI127N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 127 (by decide) (𝕀 ⊙ MulI127N0 ⊙ MulI127N1)
instance hp131 : Fact (Nat.Prime 131) := {out := by norm_num}

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-419441, 712, 9972]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![-419441, 712, 9972]] 
 ![![131, 0, 0], ![0, 131, 0], ![75, 110, 1]] where
  M :=![![![-419441, 712, 9972], ![-59832, 95, 1424], ![25644, -12, -617]]]
  hmulB := by decide  
  f := ![![![317, -2440, -508]], ![![3048, -23459, -4880]], ![![2841, -21866, -4549]]]
  g := ![![![-8911, -8368, 9972], ![-1272, -1195, 1424], ![549, 518, -617]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [102, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 130], [0, 1]]
 g := ![![[99, 9], [35, 27], [27], [1], [16], [121], [1]], ![[0, 122], [0, 104], [27], [1], [16], [121], [1]]]
 h' := ![![[120, 130], [98, 128], [56, 17], [94, 17], [14, 1], [27, 127], [29, 120], [0, 1]], ![[0, 1], [0, 3], [0, 114], [38, 114], [3, 130], [71, 4], [19, 11], [120, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [84]]
 b := ![[], [100, 42]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [102, 11, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-340, 3868, 1550]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-890, -1272, 1550]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-317, 2440, 508]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-317, 2440, 508]] 
 ![![131, 0, 0], ![42, 1, 0], ![14, 0, 1]] where
  M :=![![![-317, 2440, 508], ![-3048, 23459, 4880], ![-13116, 100956, 21019]]]
  hmulB := by decide  
  f := ![![![419441, -712, -9972]], ![![134934, -229, -3208]], ![![44630, -76, -1061]]]
  g := ![![![-839, 2440, 508], ![-8066, 23459, 4880], ![-34714, 100956, 21019]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![-419441, 712, 9972]] ![![-317, 2440, 508]]
  ![![131, 0, 0]] where
 M := ![![![-131, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P137P0 : CertificateIrreducibleZModOfList' 137 3 2 7 [4, 68, 14, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 36, 88], [30, 100, 49], [0, 1]]
 g := ![![[11, 86, 133], [72, 88], [54, 101], [76, 76, 16], [23, 81], [123, 1], []], ![[62, 119, 39, 103], [133, 61], [11, 14], [74, 22, 101, 88], [54, 34], [123, 136], [122, 72]], ![[87, 63, 37, 126], [54, 22], [124, 32], [51, 10, 117, 129], [1, 37], [109, 63], [24, 72]]]
 h' := ![![[93, 36, 88], [124, 72, 63], [136, 80, 15], [107, 86, 85], [30, 31, 133], [56, 126, 128], [0, 0, 1], [0, 1]], ![[30, 100, 49], [89, 98, 32], [115, 42, 46], [76, 29, 39], [135, 37, 136], [112, 19, 50], [78, 30, 100], [93, 36, 88]], ![[0, 1], [54, 104, 42], [74, 15, 76], [61, 22, 13], [73, 69, 5], [25, 129, 96], [119, 107, 36], [30, 100, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2, 106], []]
 b := ![[], [78, 81, 114], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 3
  hpos := by decide
  P := [4, 68, 14, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5754, -411, 4932]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![42, -3, 36]
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



lemma PB172I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB172I2 : PrimesBelowBoundCertificateInterval O 79 137 172 where
  m := 11
  g := ![1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 1]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB172I2_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I83N0]
    · exact ![I89N0]
    · exact ![I97N0, I97N1]
    · exact ![I101N0]
    · exact ![I103N0]
    · exact ![I107N0, I107N1]
    · exact ![I109N0, I109N1]
    · exact ![I113N0, I113N1]
    · exact ![I127N0, I127N1, I127N2]
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
    · exact ![571787]
    · exact ![704969]
    · exact ![9409, 97]
    · exact ![1030301]
    · exact ![1092727]
    · exact ![11449, 107]
    · exact ![11881, 109]
    · exact ![12769, 113]
    · exact ![127, 127, 127]
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
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
    · dsimp ; intro j
      fin_cases j
      exact NI127N0
      exact NI127N1
      exact NI127N2
    · dsimp ; intro j
      fin_cases j
      exact NI131N0
      exact NI131N1
    · dsimp ; intro j
      fin_cases j
      exact NI137N0
  β := ![I97N1, I107N1, I109N1, I113N1, I127N0, I127N1, I127N2, I131N1]
  Il := ![[], [], [I97N1], [], [], [I107N1], [I109N1], [I113N1], [I127N0, I127N1, I127N2], [I131N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
