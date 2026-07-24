
import IdealArithmetic.Examples.NF3_3_274505_1.RI3_3_274505_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp83 : Fact (Nat.Prime 83) := {out := by norm_num}

def I83N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2431, -1526, -196]] i)))

def SI83N0: IdealEqSpanCertificate' Table ![![-2431, -1526, -196]] 
 ![![83, 0, 0], ![0, 83, 0], ![34, 73, 1]] where
  M :=![![![-2431, -1526, -196], ![-21364, -13407, -1722], ![-187698, -117796, -15129]]]
  hmulB := by decide  
  f := ![![![123, -14, 0]], ![![0, 123, -14]], ![![32, 93, -11]]]
  g := ![![![51, 154, -196], ![448, 1353, -1722], ![3936, 11887, -15129]]]
  hle1 := by decide   
  hle2 := by decide  


def P83P0 : CertificateIrreducibleZModOfList' 83 2 2 6 [36, 42, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [41, 82], [0, 1]]
 g := ![![[15, 30], [39, 78], [49], [10], [67, 21], [1]], ![[0, 53], [0, 5], [49], [10], [15, 62], [1]]]
 h' := ![![[41, 82], [7, 14], [71, 59], [80, 76], [78, 50], [47, 41], [0, 1]], ![[0, 1], [0, 69], [0, 24], [42, 7], [53, 33], [68, 42], [41, 82]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [25]]
 b := ![[], [55, 54]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI83N0 : CertifiedPrimeIdeal' SI83N0 83 where
  n := 2
  hpos := by decide
  P := [36, 42, 1]
  hirr := P83P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![363, 235, 18]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-3, -13, 18]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI83N0 : Ideal.IsPrime I83N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI83N0 B_one_repr
lemma NI83N0 : Nat.card (O ⧸ I83N0) = 6889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI83N0

def I83N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-123, 14, 0]] i)))

def SI83N1: IdealEqSpanCertificate' Table ![![-123, 14, 0]] 
 ![![83, 0, 0], ![9, 1, 0], ![2, 0, 1]] where
  M :=![![![-123, 14, 0], ![0, -123, 14], ![1526, 784, -109]]]
  hmulB := by decide  
  f := ![![![2431, 1526, 196]], ![![521, 327, 42]], ![![2320, 1456, 187]]]
  g := ![![![-3, 14, 0], ![13, -123, 14], ![-64, 784, -109]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI83N1 : Nat.card (O ⧸ I83N1) = 83 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI83N1)

lemma isPrimeI83N1 : Ideal.IsPrime I83N1 := prime_ideal_of_norm_prime hp83.out _ NI83N1
def MulI83N0 : IdealMulLeCertificate' Table 
  ![![-2431, -1526, -196]] ![![-123, 14, 0]]
  ![![83, 0, 0]] where
 M := ![![![-83, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I89N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3089, -281, 72]] i)))

def SI89N0: IdealEqSpanCertificate' Table ![![-3089, -281, 72]] 
 ![![89, 0, 0], ![0, 89, 0], ![77, 27, 1]] where
  M :=![![![-3089, -281, 72], ![7848, 943, -209], ![-22781, -3856, 734]]]
  hmulB := by decide  
  f := ![![![-1278, -802, -103]], ![![-11227, -7046, -905]], ![![-5620, -3527, -453]]]
  g := ![![![-97, -25, 72], ![269, 74, -209], ![-891, -266, 734]]]
  hle1 := by decide   
  hle2 := by decide  


def P89P0 : CertificateIrreducibleZModOfList' 89 2 2 6 [18, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 88], [0, 1]]
 g := ![![[15, 5], [81], [80], [65, 64], [81, 9], [1]], ![[0, 84], [81], [80], [51, 25], [54, 80], [1]]]
 h' := ![![[86, 88], [57, 19], [64, 9], [76, 76], [55, 8], [71, 86], [0, 1]], ![[0, 1], [0, 70], [37, 80], [26, 13], [31, 81], [80, 3], [86, 88]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [82]]
 b := ![[], [17, 41]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI89N0 : CertifiedPrimeIdeal' SI89N0 89 where
  n := 2
  hpos := by decide
  P := [18, 3, 1]
  hirr := P89P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-311, 811, 508]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-443, -145, 508]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI89N0 : Ideal.IsPrime I89N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI89N0 B_one_repr
lemma NI89N0 : Nat.card (O ⧸ I89N0) = 7921 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI89N0

def I89N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1278, 802, 103]] i)))

def SI89N1: IdealEqSpanCertificate' Table ![![1278, 802, 103]] 
 ![![89, 0, 0], ![61, 1, 0], ![17, 0, 1]] where
  M :=![![![1278, 802, 103], ![11227, 7046, 905], ![98645, 61907, 7951]]]
  hmulB := by decide  
  f := ![![![3089, 281, -72]], ![![2029, 182, -47]], ![![846, 97, -22]]]
  g := ![![![-555, 802, 103], ![-4876, 7046, 905], ![-42841, 61907, 7951]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI89N1 : Nat.card (O ⧸ I89N1) = 89 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI89N1)

lemma isPrimeI89N1 : Ideal.IsPrime I89N1 := prime_ideal_of_norm_prime hp89.out _ NI89N1
def MulI89N0 : IdealMulLeCertificate' Table 
  ![![-3089, -281, 72]] ![![1278, 802, 103]]
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

def I97N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![225, 74, -12]] i)))

def SI97N0: IdealEqSpanCertificate' Table ![![225, 74, -12]] 
 ![![97, 0, 0], ![0, 97, 0], ![54, 10, 1]] where
  M :=![![![225, 74, -12], ![-1308, -447, 62], ![6758, 2164, -385]]]
  hmulB := by decide  
  f := ![![![-391, -26, 8]], ![![872, 57, -18]], ![![-148, -10, 3]]]
  g := ![![![9, 2, -12], ![-48, -11, 62], ![284, 62, -385]]]
  hle1 := by decide   
  hle2 := by decide  


def P97P0 : CertificateIrreducibleZModOfList' 97 2 2 6 [71, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [64, 96], [0, 1]]
 g := ![![[92, 1], [95], [18], [1], [73], [64, 1]], ![[59, 96], [95], [18], [1], [73], [31, 96]]]
 h' := ![![[64, 96], [14, 1], [58, 17], [50, 42], [86, 1], [15, 48], [0, 1]], ![[0, 1], [78, 96], [79, 80], [22, 55], [53, 96], [80, 49], [64, 96]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [39, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI97N0 : CertifiedPrimeIdeal' SI97N0 97 where
  n := 2
  hpos := by decide
  P := [71, 33, 1]
  hirr := P97P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1946, -42, 151]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -16, 151]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI97N0 : Ideal.IsPrime I97N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI97N0 B_one_repr
lemma NI97N0 : Nat.card (O ⧸ I97N0) = 9409 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI97N0

def I97N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-391, -26, 8]] i)))

def SI97N1: IdealEqSpanCertificate' Table ![![-391, -26, 8]] 
 ![![97, 0, 0], ![86, 1, 0], ![73, 0, 1]] where
  M :=![![![-391, -26, 8], ![872, 57, -18], ![-1962, -136, 39]]]
  hmulB := by decide  
  f := ![![![225, 74, -12]], ![![186, 61, -10]], ![![239, 78, -13]]]
  g := ![![![13, -26, 8], ![-28, 57, -18], ![71, -136, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI97N1 : Nat.card (O ⧸ I97N1) = 97 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI97N1)

lemma isPrimeI97N1 : Ideal.IsPrime I97N1 := prime_ideal_of_norm_prime hp97.out _ NI97N1
def MulI97N0 : IdealMulLeCertificate' Table 
  ![![225, 74, -12]] ![![-391, -26, 8]]
  ![![97, 0, 0]] where
 M := ![![![97, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P101P0 : CertificateIrreducibleZModOfList' 101 3 2 6 [69, 18, 32, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [46, 95, 44], [23, 5, 57], [0, 1]]
 g := ![![[33, 33, 37], [45, 20], [68, 91, 9], [12, 6], [98, 14], [1]], ![[86, 55, 28, 57], [79, 20], [12, 53], [65, 71], [48, 31], [46, 61, 99, 41]], ![[61, 40, 36, 29], [46, 80], [8, 46, 99, 8], [31, 23], [59, 70], [68, 78, 52, 60]]]
 h' := ![![[46, 95, 44], [21, 41, 21], [55, 1, 90], [38, 21, 98], [19, 57, 39], [32, 83, 69], [0, 1]], ![[23, 5, 57], [33, 95, 91], [63, 27, 90], [2, 85], [12, 46, 77], [30, 2, 58], [46, 95, 44]], ![[0, 1], [53, 66, 90], [55, 73, 22], [74, 96, 3], [71, 99, 86], [1, 16, 75], [23, 5, 57]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [48, 48], []]
 b := ![[], [40, 69, 54], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI101N0 : CertifiedPrimeIdeal' SI101N0 101 where
  n := 3
  hpos := by decide
  P := [69, 18, 32, 1]
  hirr := P101P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-474902, -375417, -72114]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4702, -3717, -714]
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

def I103N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77, 53, 7]] i)))

def SI103N0: IdealEqSpanCertificate' Table ![![77, 53, 7]] 
 ![![103, 0, 0], ![0, 103, 0], ![11, 37, 1]] where
  M :=![![![77, 53, 7], ![763, 469, 60], ![6540, 4123, 529]]]
  hmulB := by decide  
  f := ![![![7, 8, -1]], ![![-109, -49, 7]], ![![-31, -14, 2]]]
  g := ![![![0, -2, 7], ![1, -17, 60], ![7, -150, 529]]]
  hle1 := by decide   
  hle2 := by decide  


def P103P0 : CertificateIrreducibleZModOfList' 103 2 2 6 [34, 74, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [29, 102], [0, 1]]
 g := ![![[87, 100], [46, 19], [102, 92], [50], [83], [29, 1]], ![[0, 3], [82, 84], [92, 11], [50], [83], [58, 102]]]
 h' := ![![[29, 102], [84, 93], [34, 88], [84, 35], [41, 87], [44, 86], [0, 1]], ![[0, 1], [0, 10], [11, 15], [69, 68], [92, 16], [66, 17], [29, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [69, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI103N0 : CertifiedPrimeIdeal' SI103N0 103 where
  n := 2
  hpos := by decide
  P := [34, 74, 1]
  hirr := P103P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![361, 203, -14]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5, 7, -14]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI103N0 : Ideal.IsPrime I103N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI103N0 B_one_repr
lemma NI103N0 : Nat.card (O ⧸ I103N0) = 10609 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI103N0

def I103N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 8, -1]] i)))

def SI103N1: IdealEqSpanCertificate' Table ![![7, 8, -1]] 
 ![![103, 0, 0], ![65, 1, 0], ![101, 0, 1]] where
  M :=![![![7, 8, -1], ![-109, -49, 7], ![763, 283, -42]]]
  hmulB := by decide  
  f := ![![![77, 53, 7]], ![![56, 38, 5]], ![![139, 92, 12]]]
  g := ![![![-4, 8, -1], ![23, -49, 7], ![-130, 283, -42]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI103N1 : Nat.card (O ⧸ I103N1) = 103 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI103N1)

lemma isPrimeI103N1 : Ideal.IsPrime I103N1 := prime_ideal_of_norm_prime hp103.out _ NI103N1
def MulI103N0 : IdealMulLeCertificate' Table 
  ![![77, 53, 7]] ![![7, 8, -1]]
  ![![103, 0, 0]] where
 M := ![![![103, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I107N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, -9, -2]] i)))

def SI107N0: IdealEqSpanCertificate' Table ![![9, -9, -2]] 
 ![![107, 0, 0], ![0, 107, 0], ![49, 58, 1]] where
  M :=![![![9, -9, -2], ![-218, -103, -11], ![-1199, -834, -114]]]
  hmulB := by decide  
  f := ![![![24, 6, -1]], ![![-109, -32, 5]], ![![-43, -13, 2]]]
  g := ![![![1, 1, -2], ![3, 5, -11], ![41, 54, -114]]]
  hle1 := by decide   
  hle2 := by decide  


def P107P0 : CertificateIrreducibleZModOfList' 107 2 2 6 [36, 81, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [26, 106], [0, 1]]
 g := ![![[29, 3], [13, 53], [89], [16, 16], [4], [26, 1]], ![[0, 104], [0, 54], [89], [4, 91], [4], [52, 106]]]
 h' := ![![[26, 106], [67, 18], [82, 38], [66, 93], [50, 103], [27, 105], [0, 1]], ![[0, 1], [0, 89], [0, 69], [23, 14], [53, 4], [82, 2], [26, 106]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [37]]
 b := ![[], [27, 72]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI107N0 : CertifiedPrimeIdeal' SI107N0 107 where
  n := 2
  hpos := by decide
  P := [36, 81, 1]
  hirr := P107P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4369, 3870, 539]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-206, -256, 539]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI107N0 : Ideal.IsPrime I107N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI107N0 B_one_repr
lemma NI107N0 : Nat.card (O ⧸ I107N0) = 11449 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI107N0

def I107N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![24, 6, -1]] i)))

def SI107N1: IdealEqSpanCertificate' Table ![![24, 6, -1]] 
 ![![107, 0, 0], ![48, 1, 0], ![50, 0, 1]] where
  M :=![![![24, 6, -1], ![-109, -32, 5], ![545, 171, -27]]]
  hmulB := by decide  
  f := ![![![9, -9, -2]], ![![2, -5, -1]], ![![-7, -12, -2]]]
  g := ![![![-2, 6, -1], ![11, -32, 5], ![-59, 171, -27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI107N1 : Nat.card (O ⧸ I107N1) = 107 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI107N1)

lemma isPrimeI107N1 : Ideal.IsPrime I107N1 := prime_ideal_of_norm_prime hp107.out _ NI107N1
def MulI107N0 : IdealMulLeCertificate' Table 
  ![![9, -9, -2]] ![![24, 6, -1]]
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

def I109N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![0, 1, 0]] i)))

def SI109N0: IdealEqSpanCertificate' Table ![![0, 1, 0]] 
 ![![109, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![0, 1, 0], ![0, 0, 1], ![109, 56, 1]]]
  hmulB := by decide  
  f := ![![![-56, -1, 1]], ![![1, 0, 0]], ![![0, 1, 0]]]
  g := ![![![0, 1, 0], ![0, 0, 1], ![1, 56, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N0 : Nat.card (O ⧸ I109N0) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N0)

lemma isPrimeI109N0 : Ideal.IsPrime I109N0 := prime_ideal_of_norm_prime hp109.out _ NI109N0

def I109N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 1, 0]] i)))

def SI109N1: IdealEqSpanCertificate' Table ![![7, 1, 0]] 
 ![![109, 0, 0], ![7, 1, 0], ![60, 0, 1]] where
  M :=![![![7, 1, 0], ![0, 7, 1], ![109, 56, 8]]]
  hmulB := by decide  
  f := ![![![0, -8, 1]], ![![1, 0, 0]], ![![-7, -7, 1]]]
  g := ![![![0, 1, 0], ![-1, 7, 1], ![-7, 56, 8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N1 : Nat.card (O ⧸ I109N1) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N1)

lemma isPrimeI109N1 : Ideal.IsPrime I109N1 := prime_ideal_of_norm_prime hp109.out _ NI109N1

def I109N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, 1, 0]] i)))

def SI109N2: IdealEqSpanCertificate' Table ![![-8, 1, 0]] 
 ![![109, 0, 0], ![101, 1, 0], ![45, 0, 1]] where
  M :=![![![-8, 1, 0], ![0, -8, 1], ![109, 56, -7]]]
  hmulB := by decide  
  f := ![![![0, 7, 1]], ![![1, 7, 1]], ![![8, 8, 1]]]
  g := ![![![-1, 1, 0], ![7, -8, 1], ![-48, 56, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI109N2 : Nat.card (O ⧸ I109N2) = 109 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI109N2)

lemma isPrimeI109N2 : Ideal.IsPrime I109N2 := prime_ideal_of_norm_prime hp109.out _ NI109N2
def MulI109N0 : IdealMulLeCertificate' Table 
  ![![0, 1, 0]] ![![7, 1, 0]]
  ![![0, 7, 1]] where
 M := ![![![0, 7, 1]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI109N1 : IdealMulLeCertificate' Table 
  ![![0, 7, 1]] ![![-8, 1, 0]]
  ![![109, 0, 0]] where
 M := ![![![109, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I113N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-33, -5, 1]] i)))

def SI113N0: IdealEqSpanCertificate' Table ![![-33, -5, 1]] 
 ![![113, 0, 0], ![30, 1, 0], ![4, 0, 1]] where
  M :=![![![-33, -5, 1], ![109, 23, -4], ![-436, -115, 19]]]
  hmulB := by decide  
  f := ![![![23, 20, 3]], ![![9, 7, 1]], ![![23, 15, 2]]]
  g := ![![![1, -5, 1], ![-5, 23, -4], ![26, -115, 19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N0 : Nat.card (O ⧸ I113N0) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N0)

lemma isPrimeI113N0 : Ideal.IsPrime I113N0 := prime_ideal_of_norm_prime hp113.out _ NI113N0

def I113N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![194, 13, -4]] i)))

def SI113N1: IdealEqSpanCertificate' Table ![![194, 13, -4]] 
 ![![113, 0, 0], ![37, 1, 0], ![100, 0, 1]] where
  M :=![![![194, 13, -4], ![-436, -30, 9], ![981, 68, -21]]]
  hmulB := by decide  
  f := ![![![18, 1, -3]], ![![3, -1, -1]], ![![14, -3, -4]]]
  g := ![![![1, 13, -4], ![-2, -30, 9], ![5, 68, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N1 : Nat.card (O ⧸ I113N1) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N1)

lemma isPrimeI113N1 : Ideal.IsPrime I113N1 := prime_ideal_of_norm_prime hp113.out _ NI113N1

def I113N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-60, -38, -5]] i)))

def SI113N2: IdealEqSpanCertificate' Table ![![-60, -38, -5]] 
 ![![113, 0, 0], ![45, 1, 0], ![9, 0, 1]] where
  M :=![![![-60, -38, -5], ![-545, -340, -43], ![-4687, -2953, -383]]]
  hmulB := by decide  
  f := ![![![-3241, -211, 66]], ![![-1227, -80, 25]], ![![-398, -25, 8]]]
  g := ![![![15, -38, -5], ![134, -340, -43], ![1165, -2953, -383]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI113N2 : Nat.card (O ⧸ I113N2) = 113 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI113N2)

lemma isPrimeI113N2 : Ideal.IsPrime I113N2 := prime_ideal_of_norm_prime hp113.out _ NI113N2
def MulI113N0 : IdealMulLeCertificate' Table 
  ![![-33, -5, 1]] ![![194, 13, -4]]
  ![![-3241, -211, 66]] where
 M := ![![![-3241, -211, 66]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI113N1 : IdealMulLeCertificate' Table 
  ![![-3241, -211, 66]] ![![-60, -38, -5]]
  ![![113, 0, 0]] where
 M := ![![![113, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC113 : ContainsPrimesAboveP 113 ![I113N0, I113N1, I113N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI113N0
    exact isPrimeI113N1
    exact isPrimeI113N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 113 (by decide) (𝕀 ⊙ MulI113N0 ⊙ MulI113N1)


lemma PB117I2_primes (p : ℕ) :
  p ∈ Set.range ![83, 89, 97, 101, 103, 107, 109, 113] ↔ Nat.Prime p ∧ 79 < p ∧ p ≤ 116 := by
  rw [← List.mem_ofFn']
  convert primes_range 79 116 (by omega)

def PB117I2 : PrimesBelowBoundCertificateInterval O 79 116 117 where
  m := 8
  g := ![2, 2, 2, 1, 2, 2, 3, 3]
  P := ![83, 89, 97, 101, 103, 107, 109, 113]
  hP := PB117I2_primes
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
    · exact ![I109N0, I109N1, I109N2]
    · exact ![I113N0, I113N1, I113N2]
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
    · exact ![109, 109, 109]
    · exact ![113, 113, 113]
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
      exact NI109N1
      exact NI109N2
    · dsimp ; intro j
      fin_cases j
      exact NI113N0
      exact NI113N1
      exact NI113N2
  β := ![I83N1, I89N1, I97N1, I103N1, I107N1, I109N0, I109N1, I109N2, I113N0, I113N1, I113N2]
  Il := ![[I83N1], [I89N1], [I97N1], [], [I103N1], [I107N1], [I109N0, I109N1, I109N2], [I113N0, I113N1, I113N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
