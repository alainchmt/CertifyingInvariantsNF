
import IdealArithmetic.Examples.NF3_3_564980_1.RI3_3_564980_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1267, -1708, 368]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-1267, -1708, 368]] 
 ![![139, 0, 0], ![0, 139, 0], ![6, 15, 1]] where
  M :=![![![-1267, -1708, 368], ![10068, 14189, -3048], ![-41040, -58120, 12481]]]
  hmulB := by decide  
  f := ![![![-409, -508, -112]], ![![-4092, -5113, -1128]], ![![-606, -757, -167]]]
  g := ![![![-25, -52, 368], ![204, 431, -3048], ![-834, -1765, 12481]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [80, 14, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 138], [0, 1]]
 g := ![![[94, 106], [27, 131], [131], [27, 80], [63], [57], [1]], ![[0, 33], [0, 8], [131], [19, 59], [63], [57], [1]]]
 h' := ![![[125, 138], [64, 84], [10, 100], [64, 39], [80, 48], [33, 52], [59, 125], [0, 1]], ![[0, 1], [0, 55], [0, 39], [74, 100], [103, 91], [0, 87], [116, 14], [125, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9]]
 b := ![[], [101, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [80, 14, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![344, 304, 150]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4, -14, 150]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-409, -508, -112]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-409, -508, -112]] 
 ![![139, 0, 0], ![108, 1, 0], ![76, 0, 1]] where
  M :=![![![-409, -508, -112], ![-4092, -5113, -1128], ![-20400, -25480, -5621]]]
  hmulB := by decide  
  f := ![![![-1267, -1708, 368]], ![![-912, -1225, 264]], ![![-988, -1352, 291]]]
  g := ![![![453, -508, -112], ![4560, -5113, -1128], ![22724, -25480, -5621]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-1267, -1708, 368]] ![![-409, -508, -112]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0)
instance hp149 : Fact (Nat.Prime 149) := {out := by norm_num}

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0]] 
 ![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [49, 125, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 26, 47], [34, 122, 102], [0, 1]]
 g := ![![[138, 12, 39], [98, 123], [84, 69, 7], [55, 45], [105, 70, 61], [126, 1], []], ![[38, 144, 112, 76], [1, 96], [121, 116, 25, 28], [90, 148], [13, 123, 55, 1], [101, 133], [62, 123]], ![[137, 11, 135, 17], [106, 26], [46, 104, 6, 145], [63, 121], [144, 147, 64, 124], [22, 80], [7, 123]]]
 h' := ![![[92, 26, 47], [122, 120, 28], [56, 131, 47], [119, 123, 93], [70, 37, 55], [84, 144, 106], [0, 0, 1], [0, 1]], ![[34, 122, 102], [84, 146, 116], [122, 21, 120], [66, 57, 141], [30, 133, 105], [87, 63, 32], [62, 96, 122], [92, 26, 47]], ![[0, 1], [146, 32, 5], [107, 146, 131], [46, 118, 64], [2, 128, 138], [119, 91, 11], [68, 53, 26], [34, 122, 102]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 79], []]
 b := ![[], [56, 78, 11], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [49, 125, 23, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![147808, 124117, 248681]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![992, 833, 1669]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 3307949 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def PBC149 : ContainsPrimesAboveP 149 ![I149N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![149, 0, 0]]) timesTableT_eq_Table B_one_repr 149 (by decide) 𝕀

instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![219, 276, 61]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![219, 276, 61]] 
 ![![151, 0, 0], ![0, 151, 0], ![63, 7, 1]] where
  M :=![![![219, 276, 61], ![2228, 2781, 613], ![11089, 13849, 3057]]]
  hmulB := by decide  
  f := ![![![-80, -7, 3]], ![![89, 46, -11]], ![![-30, -2, 1]]]
  g := ![![![-24, -1, 61], ![-241, -10, 613], ![-1202, -50, 3057]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [97, 108, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [43, 150], [0, 1]]
 g := ![![[149, 137], [104, 124], [88, 31], [31], [15, 124], [37], [1]], ![[0, 14], [0, 27], [62, 120], [31], [62, 27], [37], [1]]]
 h' := ![![[43, 150], [29, 52], [71, 44], [18, 129], [55, 22], [82, 44], [54, 43], [0, 1]], ![[0, 1], [0, 99], [0, 107], [129, 22], [95, 129], [11, 107], [91, 108], [43, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148]]
 b := ![[], [70, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [97, 108, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![154251, 155606, 184274]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-75861, -7512, 184274]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-80, -7, 3]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-80, -7, 3]] 
 ![![151, 0, 0], ![136, 1, 0], ![39, 0, 1]] where
  M :=![![![-80, -7, 3], ![89, 46, -11], ![-113, -183, 39]]]
  hmulB := by decide  
  f := ![![![219, 276, 61]], ![![212, 267, 59]], ![![130, 163, 36]]]
  g := ![![![5, -7, 3], ![-38, 46, -11], ![154, -183, 39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![219, 276, 61]] ![![-80, -7, 3]]
  ![![151, 0, 0]] where
 M := ![![![151, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4951, -7028, 1509]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-4951, -7028, 1509]] 
 ![![157, 0, 0], ![0, 157, 0], ![58, 38, 1]] where
  M :=![![![-4951, -7028, 1509], ![41260, 58427, -12547], ![-169063, -239343, 51399]]]
  hmulB := by decide  
  f := ![![![336, 405, 89]], ![![3253, 4074, 899]], ![![1015, 1265, 279]]]
  g := ![![![-589, -410, 1509], ![4898, 3409, -12547], ![-20065, -13965, 51399]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [154, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 156], [0, 1]]
 g := ![![[11, 52], [58], [9, 108], [142, 31], [107, 154], [147], [1]], ![[0, 105], [58], [119, 49], [66, 126], [8, 3], [147], [1]]]
 h' := ![![[33, 156], [118, 44], [27, 134], [112, 118], [7, 38], [136, 25], [3, 33], [0, 1]], ![[0, 1], [0, 113], [53, 23], [81, 39], [5, 119], [19, 132], [150, 124], [33, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [95, 156]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [154, 124, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![516, 625, 442]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-160, -103, 442]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![336, 405, 89]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![336, 405, 89]] 
 ![![157, 0, 0], ![80, 1, 0], ![19, 0, 1]] where
  M :=![![![336, 405, 89], ![3253, 4074, 899], ![16253, 20303, 4479]]]
  hmulB := by decide  
  f := ![![![-4951, -7028, 1509]], ![![-2260, -3209, 689]], ![![-1676, -2375, 510]]]
  g := ![![![-215, 405, 89], ![-2164, 4074, 899], ![-10784, 20303, 4479]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-4951, -7028, 1509]] ![![336, 405, 89]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [44, 57, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [127, 28, 19], [27, 134, 144], [0, 1]]
 g := ![![[149, 116, 95], [147, 162, 64], [101, 91], [48, 62], [63, 113], [24, 154, 1], []], ![[64, 103, 120, 127], [90, 117, 48, 63], [161, 104], [87, 33], [88, 156], [81, 36, 78, 5], [97, 35]], ![[100, 71, 95, 150], [87, 21, 28, 61], [144, 9], [117, 26], [30, 54], [81, 3, 111, 100], [135, 35]]]
 h' := ![![[127, 28, 19], [52, 4, 101], [134, 15, 155], [103, 125, 108], [52, 118, 15], [85, 6, 90], [0, 0, 1], [0, 1]], ![[27, 134, 144], [145, 54, 81], [61, 76, 28], [138, 157, 58], [124, 37, 14], [35, 126, 112], [125, 43, 134], [127, 28, 19]], ![[0, 1], [13, 105, 144], [10, 72, 143], [106, 44, 160], [53, 8, 134], [45, 31, 124], [5, 120, 28], [27, 134, 144]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [109, 46], []]
 b := ![[], [20, 31, 152], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [44, 57, 9, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-37327, -45151, -15648]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-229, -277, -96]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, -2, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-1, -2, 0]] 
 ![![167, 0, 0], ![84, 1, 0], ![63, 0, 1]] where
  M :=![![![-1, -2, 0], ![-2, -1, -4], ![-64, -84, -3]]]
  hmulB := by decide  
  f := ![![![333, 6, -8]], ![![166, 3, -4]], ![![125, 2, -3]]]
  g := ![![![1, -2, 0], ![2, -1, -4], ![43, -84, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-230, -321, 69]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-230, -321, 69]] 
 ![![167, 0, 0], ![94, 1, 0], ![8, 0, 1]] where
  M :=![![![-230, -321, 69], ![1887, 2668, -573], ![-7719, -10929, 2347]]]
  hmulB := by decide  
  f := ![![![521, 714, 159]], ![![328, 445, 99]], ![![197, 249, 55]]]
  g := ![![![176, -321, 69], ![-1463, 2668, -573], ![5993, -10929, 2347]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-129, -36, -5]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![-129, -36, -5]] 
 ![![167, 0, 0], ![155, 1, 0], ![12, 0, 1]] where
  M :=![![![-129, -36, -5], ![-196, -339, -77], ![-1337, -1697, -375]]]
  hmulB := by decide  
  f := ![![![-3544, -5015, 1077]], ![![-3113, -4405, 946]], ![![-977, -1383, 297]]]
  g := ![![![33, -36, -5], ![319, -339, -77], ![1594, -1697, -375]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-1, -2, 0]] ![![-230, -321, 69]]
  ![![-3544, -5015, 1077]] where
 M := ![![![-3544, -5015, 1077]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![-3544, -5015, 1077]] ![![-129, -36, -5]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1, I167N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
    exact isPrimeI167N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0 ⊙ MulI167N1)


lemma PB168I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 167 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 167 (by omega)

def PB168I3 : PrimesBelowBoundCertificateInterval O 137 167 168 where
  m := 6
  g := ![2, 1, 2, 2, 1, 3]
  P := ![139, 149, 151, 157, 163, 167]
  hP := PB168I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1, I167N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC139
    · exact PBC149
    · exact PBC151
    · exact PBC157
    · exact PBC163
    · exact PBC167
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![167, 167, 167]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
      exact NI167N2
  β := ![I139N1, I151N1, I157N1, I167N0, I167N1, I167N2]
  Il := ![[I139N1], [], [I151N1], [I157N1], [], [I167N0, I167N1, I167N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
