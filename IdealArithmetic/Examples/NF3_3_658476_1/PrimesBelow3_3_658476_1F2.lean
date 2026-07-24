
import IdealArithmetic.Examples.NF3_3_658476_1.RI3_3_658476_1
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


def P83P0 : CertificateIrreducibleZModOfList' 83 3 2 6 [67, 72, 12, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 44, 22], [65, 38, 61], [0, 1]]
 g := ![![[73, 42, 12], [80, 38, 77], [42, 37], [26, 7], [72, 71, 1], []], ![[61, 17, 52, 15], [1, 73, 33, 43], [58, 16], [0, 70], [7, 31, 50, 62], [29, 69]], ![[72, 10, 15, 23], [26, 1, 1, 17], [14, 28], [54, 41], [22, 43, 75, 70], [73, 69]]]
 h' := ![![[6, 44, 22], [35, 77, 26], [0, 42, 49], [18, 18, 55], [73, 19, 16], [0, 0, 1], [0, 1]], ![[65, 38, 61], [51, 81, 26], [18, 5, 47], [70, 31, 79], [53, 14, 30], [2, 42, 38], [6, 44, 22]], ![[0, 1], [8, 8, 31], [59, 36, 70], [82, 34, 32], [31, 50, 37], [81, 41, 44], [65, 38, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [41, 6], []]
 b := ![[], [68, 5, 45], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 3
  hpos := by decide
  P := [67, 72, 12, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-498, -48555, -46812]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-6, -585, -564]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13, 410, -98]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-13, 410, -98]] 
 ![![89, 0, 0], ![0, 89, 0], ![41, 83, 1]] where
  M :=![![![-13, 410, -98], ![-98, -3817, 918], ![508, 19688, -4735]]]
  hmulB := by decide  
  f := ![![![-1, 134, 26]], ![![26, 1251, 242]], ![![25, 1287, 249]]]
  g := ![![![45, 96, -98], ![-424, -899, 918], ![2187, 4637, -4735]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [19, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 88], [0, 1]]
 g := ![![[19, 47], [55], [21], [41, 36], [65, 25], [1]], ![[51, 42], [55], [21], [39, 53], [29, 64], [1]]]
 h' := ![![[84, 88], [39, 74], [85, 12], [22, 33], [11, 6], [70, 84], [0, 1]], ![[0, 1], [25, 15], [25, 77], [35, 56], [70, 83], [6, 5], [84, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28]]
 b := ![[], [35, 14]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [19, 5, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7, 12, 710]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-327, -662, 710]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1, -134, -26]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![1, -134, -26]] 
 ![![89, 0, 0], ![13, 1, 0], ![87, 0, 1]] where
  M :=![![![1, -134, -26], ![-26, -1251, -242], ![-108, -5216, -1009]]]
  hmulB := by decide  
  f := ![![![13, -410, 98]], ![![3, -17, 4]], ![![7, -622, 149]]]
  g := ![![![45, -134, -26], ![419, -1251, -242], ![1747, -5216, -1009]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-13, 410, -98]] ![![1, -134, -26]]
  ![![89, 0, 0]] where
 M := ![![![-89, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6, -45, 11]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![-6, -45, 11]] 
 ![![97, 0, 0], ![0, 97, 0], ![70, 40, 1]] where
  M :=![![![-6, -45, 11], ![11, 422, -101], ![-56, -2166, 523]]]
  hmulB := by decide  
  f := ![![![-20, 3, 1]], ![![1, 26, 5]], ![![-14, 14, 3]]]
  g := ![![![-8, -5, 11], ![73, 46, -101], ![-378, -238, 523]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [18, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 96], [0, 1]]
 g := ![![[24, 27], [25], [48], [70], [96], [53, 1]], ![[0, 70], [25], [48], [70], [96], [9, 96]]]
 h' := ![![[53, 96], [38, 67], [10, 5], [96, 57], [80, 19], [16, 75], [0, 1]], ![[0, 1], [0, 30], [81, 92], [13, 40], [20, 78], [14, 22], [53, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [21, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [18, 44, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1297, -21, 128]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-79, -53, 128]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, -3, -1]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![20, -3, -1]] 
 ![![97, 0, 0], ![18, 1, 0], ![23, 0, 1]] where
  M :=![![![20, -3, -1], ![-1, -26, -5], ![-2, -108, -21]]]
  hmulB := by decide  
  f := ![![![6, 45, -11]], ![![1, 4, -1]], ![![2, 33, -8]]]
  g := ![![![1, -3, -1], ![6, -26, -5], ![25, -108, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![-6, -45, 11]] ![![20, -3, -1]]
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

def I101N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 320, 62]] i)))

def SI101N0: IdealEqSpanCertificate' Table ![![7, 320, 62]] 
 ![![101, 0, 0], ![0, 101, 0], ![5, 41, 1]] where
  M :=![![![7, 320, 62], ![62, 2993, 578], ![258, 12458, 2415]]]
  hmulB := by decide  
  f := ![![![271, -4, -6]], ![![-6, 9, -2]], ![![11, 3, -1]]]
  g := ![![![-3, -22, 62], ![-28, -205, 578], ![-117, -857, 2415]]]
  hle1 := by decide   
  hle2 := by decide  


def P101P0 : CertificateIrreducibleZModOfList' 101 2 2 6 [95, 29, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [72, 100], [0, 1]]
 g := ![![[12, 84], [36], [15, 81], [100], [6], [72, 1]], ![[0, 17], [36], [90, 20], [100], [6], [43, 100]]]
 h' := ![![[72, 100], [34, 36], [90, 6], [37, 92], [12, 91], [28, 39], [0, 1]], ![[0, 1], [0, 65], [17, 95], [96, 9], [100, 10], [8, 62], [72, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [81, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 2
  hpos := by decide
  P := [95, 29, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![120, 277, 933]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45, -376, 933]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI101N0 : Ideal.IsPrime I101N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI101N0 B_one_repr
lemma NI101N0 : Nat.card (O ⧸ I101N0) = 10201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI101N0

def I101N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-271, 4, 6]] i)))

def SI101N1: IdealEqSpanCertificate' Table ![![-271, 4, 6]] 
 ![![101, 0, 0], ![20, 1, 0], ![93, 0, 1]] where
  M :=![![![-271, 4, 6], ![6, -9, 2], ![-2, 46, -11]]]
  hmulB := by decide  
  f := ![![![-7, -320, -62]], ![![-2, -93, -18]], ![![-9, -418, -81]]]
  g := ![![![-9, 4, 6], ![0, -9, 2], ![1, 46, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI101N1 : Nat.card (O ⧸ I101N1) = 101 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI101N1)

lemma isPrimeI101N1 : Ideal.IsPrime I101N1 := prime_ideal_of_norm_prime hp101.out _ NI101N1
def MulI101N0 : IdealMulLeCertificate' Table 
  ![![7, 320, 62]] ![![-271, 4, 6]]
  ![![101, 0, 0]] where
 M := ![![![-101, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P103P0 : CertificateIrreducibleZModOfList' 103 3 2 6 [24, 9, 55, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [80, 3, 45], [71, 99, 58], [0, 1]]
 g := ![![[31, 7, 41], [2, 67, 52], [54, 15, 82], [65, 32], [33, 38], [1]], ![[27, 50, 89, 102], [39, 94, 97, 69], [71, 30, 97, 37], [60, 2], [67, 29], [75, 0, 99, 73]], ![[28, 37, 28, 4], [47, 25, 98, 100], [16, 96, 59, 4], [49, 18], [11, 23], [97, 85, 6, 30]]]
 h' := ![![[80, 3, 45], [55, 17, 12], [43, 96, 19], [85, 76, 44], [93, 47, 49], [79, 94, 48], [0, 1]], ![[71, 99, 58], [92, 75, 99], [92, 17, 21], [78, 7, 51], [73, 33, 65], [41, 69, 21], [80, 3, 45]], ![[0, 1], [44, 11, 95], [38, 93, 63], [88, 20, 8], [53, 23, 92], [27, 43, 34], [71, 99, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21, 56], []]
 b := ![[], [98, 8, 72], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 3
  hpos := by decide
  P := [24, 9, 55, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-412, -34196, -29767]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -332, -289]
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


def P107P0 : CertificateIrreducibleZModOfList' 107 3 2 6 [96, 11, 96, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [98, 38, 101], [20, 68, 6], [0, 1]]
 g := ![![[77, 13, 85], [38, 72, 13], [29, 48], [17, 85, 100], [19, 14], [1]], ![[58, 14, 77, 34], [54, 30, 45, 1], [68, 34], [68, 27, 37, 62], [9, 52], [42, 91, 16, 105]], ![[37, 15, 92, 94], [98, 86, 42, 80], [50, 81], [39, 11, 21, 15], [33, 105], [29, 11, 90, 2]]]
 h' := ![![[98, 38, 101], [97, 2, 37], [85, 62, 21], [80, 80, 35], [9, 24, 97], [11, 96, 11], [0, 1]], ![[20, 68, 6], [56, 37, 43], [101, 3, 93], [67, 10, 81], [19, 81, 32], [54, 36, 65], [98, 38, 101]], ![[0, 1], [78, 68, 27], [48, 42, 100], [51, 17, 98], [22, 2, 85], [80, 82, 31], [20, 68, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68, 51], []]
 b := ![[], [0, 104, 62], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 3
  hpos := by decide
  P := [96, 11, 96, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![592780, 35984314, 19952718]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5540, 336302, 186474]
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


def P109P0 : CertificateIrreducibleZModOfList' 109 3 2 6 [29, 104, 25, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [74, 108, 43], [10, 0, 66], [0, 1]]
 g := ![![[20, 77, 29], [21, 80], [84, 42, 84], [42, 49, 21], [39, 80], [1]], ![[32, 66, 39, 45], [64, 105], [52, 15, 73, 29], [46, 94, 32, 105], [55, 9], [54, 17, 61, 46]], ![[58, 65, 51, 63], [101, 106], [8, 93, 55, 22], [22, 40, 45, 89], [28, 21], [33, 3, 60, 63]]]
 h' := ![![[74, 108, 43], [72, 41, 47], [71, 108, 25], [90, 49, 53], [37, 92, 28], [80, 5, 84], [0, 1]], ![[10, 0, 66], [70, 1, 19], [89, 79, 66], [35, 3, 36], [20, 100, 32], [31, 26, 106], [74, 108, 43]], ![[0, 1], [9, 67, 43], [39, 31, 18], [93, 57, 20], [56, 26, 49], [43, 78, 28], [10, 0, 66]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [65, 70], []]
 b := ![[], [4, 8, 44], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI109N0 : CertifiedPrimeIdeal' SI109N0 109 where
  n := 3
  hpos := by decide
  P := [29, 104, 25, 1]
  hirr := P109P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![218, 13625, 3597]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2, 125, 33]
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


def P113P0 : CertificateIrreducibleZModOfList' 113 3 2 6 [29, 43, 17, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [90, 99, 13], [6, 13, 100], [0, 1]]
 g := ![![[106, 43, 52], [81, 105], [109, 56], [99, 63], [33, 52, 63], [1]], ![[1, 54, 56, 8], [13, 77], [41, 95], [18, 9], [54, 23, 78, 104], [23, 16, 75, 50]], ![[109, 24, 40, 1], [61, 50], [1, 32], [64, 83], [85, 1, 72, 97], [101, 20, 96, 63]]]
 h' := ![![[90, 99, 13], [49, 62, 74], [5, 94, 52], [51, 106, 13], [60, 61, 17], [84, 70, 96], [0, 1]], ![[6, 13, 100], [67, 20, 73], [61, 99, 90], [32, 28, 78], [21, 28, 110], [48, 59, 11], [90, 99, 13]], ![[0, 1], [100, 31, 79], [93, 33, 84], [3, 92, 22], [27, 24, 99], [112, 97, 6], [6, 13, 100]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89, 34], []]
 b := ![[], [9, 56, 93], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI113N0 : CertifiedPrimeIdeal' SI113N0 113 where
  n := 3
  hpos := by decide
  P := [29, 43, 17, 1]
  hirr := P113P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1808, 208146, 255606]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![16, 1842, 2262]
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

def I127N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4123, 198600, 38418]] i)))

def SI127N0: IdealEqSpanCertificate' Table ![![4123, 198600, 38418]] 
 ![![127, 0, 0], ![0, 127, 0], ![118, 71, 1]] where
  M :=![![![4123, 198600, 38418], ![38418, 1854697, 358782], ![160182, 7733022, 1495915]]]
  hmulB := by decide  
  f := ![![![-287, -11652, 2802]], ![![2802, 108547, -26106]], ![![1186, 45449, -10931]]]
  g := ![![![-35663, -19914, 38418], ![-333054, -185975, 358782], ![-1388644, -775409, 1495915]]]
  hle1 := by decide   
  hle2 := by decide  


def P127P0 : CertificateIrreducibleZModOfList' 127 2 2 6 [45, 114, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 1]
 hbits := by decide
 h := ![[0, 1], [13, 126], [0, 1]]
 g := ![![[11, 13], [8, 44], [3, 82], [73, 11], [71, 9], [13, 1]], ![[53, 114], [72, 83], [53, 45], [89, 116], [61, 118], [26, 126]]]
 h' := ![![[13, 126], [21, 93], [119, 67], [17, 92], [107, 97], [50, 124], [0, 1]], ![[0, 1], [87, 34], [101, 60], [70, 35], [98, 30], [11, 3], [13, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [45, 81]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI127N0 : CertifiedPrimeIdeal' SI127N0 127 where
  n := 2
  hpos := by decide
  P := [45, 114, 1]
  hirr := P127P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![337, 2492, 908]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-841, -488, 908]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI127N0 : Ideal.IsPrime I127N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI127N0 B_one_repr
lemma NI127N0 : Nat.card (O ⧸ I127N0) = 16129 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI127N0

def I127N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![287, 11652, -2802]] i)))

def SI127N1: IdealEqSpanCertificate' Table ![![287, 11652, -2802]] 
 ![![127, 0, 0], ![113, 1, 0], ![36, 0, 1]] where
  M :=![![![287, 11652, -2802], ![-2802, -108547, 26106], ![14454, 559878, -134653]]]
  hmulB := by decide  
  f := ![![![-4123, -198600, -38418]], ![![-3971, -191311, -37008]], ![![-2430, -117186, -22669]]]
  g := ![![![-9571, 11652, -2802], ![89159, -108547, 26106], ![-459876, 559878, -134653]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI127N1 : Nat.card (O ⧸ I127N1) = 127 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI127N1)

lemma isPrimeI127N1 : Ideal.IsPrime I127N1 := prime_ideal_of_norm_prime hp127.out _ NI127N1
def MulI127N0 : IdealMulLeCertificate' Table 
  ![![4123, 198600, 38418]] ![![287, 11652, -2802]]
  ![![127, 0, 0]] where
 M := ![![![-127, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I131N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![524883, 25339534, 4901808]] i)))

def SI131N0: IdealEqSpanCertificate' Table ![![524883, 25339534, 4901808]] 
 ![![131, 0, 0], ![0, 131, 0], ![36, 46, 1]] where
  M :=![![![524883, 25339534, 4901808], ![4901808, 236642161, 45777260], ![20437726, 986661994, 190864901]]]
  hmulB := by decide  
  f := ![![![-1791, -54878, 13208]], ![![13208, 511275, -122964]], ![![3626, 144320, -34707]]]
  g := ![![![-1343055, -1527814, 4901808], ![-12542592, -14268029, 45777260], ![-52295410, -59489492, 190864901]]]
  hle1 := by decide   
  hle2 := by decide  


def P131P0 : CertificateIrreducibleZModOfList' 131 2 2 7 [11, 52, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 130], [0, 1]]
 g := ![![[100, 12], [2, 55], [1], [28], [112], [84], [1]], ![[0, 119], [24, 76], [1], [28], [112], [84], [1]]]
 h' := ![![[79, 130], [109, 55], [90, 29], [106, 1], [105, 40], [114, 51], [120, 79], [0, 1]], ![[0, 1], [0, 76], [23, 102], [54, 130], [121, 91], [82, 80], [73, 52], [79, 130]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [13]]
 b := ![[], [38, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI131N0 : CertifiedPrimeIdeal' SI131N0 131 where
  n := 2
  hpos := by decide
  P := [11, 52, 1]
  hirr := P131P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![855, -21, 122]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-27, -43, 122]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI131N0 : Ideal.IsPrime I131N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI131N0 B_one_repr
lemma NI131N0 : Nat.card (O ⧸ I131N0) = 17161 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI131N0

def I131N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1791, -54878, 13208]] i)))

def SI131N1: IdealEqSpanCertificate' Table ![![-1791, -54878, 13208]] 
 ![![131, 0, 0], ![40, 1, 0], ![97, 0, 1]] where
  M :=![![![-1791, -54878, 13208], ![13208, 511275, -122964], ![-68086, -2637122, 634239]]]
  hmulB := by decide  
  f := ![![![524883, 25339534, 4901808]], ![![197688, 9543691, 1846180]], ![![544667, 26294632, 5086567]]]
  g := ![![![6963, -54878, 13208], ![-64964, 511275, -122964], ![335081, -2637122, 634239]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI131N1 : Nat.card (O ⧸ I131N1) = 131 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI131N1)

lemma isPrimeI131N1 : Ideal.IsPrime I131N1 := prime_ideal_of_norm_prime hp131.out _ NI131N1
def MulI131N0 : IdealMulLeCertificate' Table 
  ![![524883, 25339534, 4901808]] ![![-1791, -54878, 13208]]
  ![![131, 0, 0]] where
 M := ![![![131, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I137N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![32129, -380, -734]] i)))

def SI137N0: IdealEqSpanCertificate' Table ![![32129, -380, -734]] 
 ![![137, 0, 0], ![0, 137, 0], ![102, 114, 1]] where
  M :=![![![32129, -380, -734], ![-734, 187, -26], ![354, -926, 213]]]
  hmulB := by decide  
  f := ![![![-115, -5552, -1074]], ![![-1074, -51849, -10030]], ![![-1012, -48856, -9451]]]
  g := ![![![781, 608, -734], ![14, 23, -26], ![-156, -184, 213]]]
  hle1 := by decide   
  hle2 := by decide  


def P137P0 : CertificateIrreducibleZModOfList' 137 2 2 7 [89, 15, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [122, 136], [0, 1]]
 g := ![![[111, 72], [73], [133], [37, 78], [126], [88], [1]], ![[127, 65], [73], [133], [100, 59], [126], [88], [1]]]
 h' := ![![[122, 136], [20, 88], [107, 115], [132, 63], [132, 30], [89, 117], [48, 122], [0, 1]], ![[0, 1], [70, 49], [26, 22], [9, 74], [93, 107], [115, 20], [136, 15], [122, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [66, 91]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI137N0 : CertifiedPrimeIdeal' SI137N0 137 where
  n := 2
  hpos := by decide
  P := [89, 15, 1]
  hirr := P137P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![129, 1764, 1472]
  a := ![1, -5, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1095, -1212, 1472]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI137N0 : Ideal.IsPrime I137N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI137N0 B_one_repr
lemma NI137N0 : Nat.card (O ⧸ I137N0) = 18769 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI137N0

def I137N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![115, 5552, 1074]] i)))

def SI137N1: IdealEqSpanCertificate' Table ![![115, 5552, 1074]] 
 ![![137, 0, 0], ![47, 1, 0], ![105, 0, 1]] where
  M :=![![![115, 5552, 1074], ![1074, 51849, 10030], ![4478, 216182, 41819]]]
  hmulB := by decide  
  f := ![![![-32129, 380, 734]], ![![-11017, 129, 252]], ![![-24627, 298, 561]]]
  g := ![![![-2727, 5552, 1074], ![-25467, 51849, 10030], ![-106183, 216182, 41819]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI137N1 : Nat.card (O ⧸ I137N1) = 137 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI137N1)

lemma isPrimeI137N1 : Ideal.IsPrime I137N1 := prime_ideal_of_norm_prime hp137.out _ NI137N1
def MulI137N0 : IdealMulLeCertificate' Table 
  ![![32129, -380, -734]] ![![115, 5552, 1074]]
  ![![137, 0, 0]] where
 M := ![![![-137, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB181I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 137 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 137 (by omega)

def PB181I2 : PrimesBelowBoundCertificateInterval O 79 137 181 where
  m := 11
  g := ![1, 2, 2, 2, 1, 1, 1, 1, 2, 2, 2]
  P := ![83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137]
  hP := PB181I2_primes
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
    · exact ![I109N0]
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
    · exact ![10201, 101]
    · exact ![1092727]
    · exact ![1225043]
    · exact ![1295029]
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
      exact NI101N1
    · dsimp ; intro j
      fin_cases j
      exact NI103N0
    · dsimp ; intro j
      fin_cases j
      exact NI107N0
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
      exact NI137N1
  β := ![I89N1, I97N1, I101N1, I127N1, I131N1, I137N1]
  Il := ![[], [I89N1], [I97N1], [I101N1], [], [], [], [], [I127N1], [I131N1], [I137N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
