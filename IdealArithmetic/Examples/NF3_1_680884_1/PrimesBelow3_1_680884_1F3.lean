
import IdealArithmetic.Examples.NF3_1_680884_1.RI3_1_680884_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0]] 
 ![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [112, 117, 18, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [81, 121, 63], [40, 17, 76], [0, 1]]
 g := ![![[3, 82, 9], [59, 113, 80], [3, 89], [24, 35, 120], [24, 37], [121, 1], []], ![[136, 127, 76, 47], [78, 92, 5, 67], [50, 65], [59, 75, 117, 7], [43, 100], [82, 11], [99, 77]], ![[123, 57, 22, 101], [85, 57, 20, 22], [131, 45], [63, 38, 65, 58], [116, 107], [49, 46], [86, 77]]]
 h' := ![![[81, 121, 63], [64, 87, 3], [66, 35, 48], [92, 88, 111], [127, 46, 113], [70, 48, 68], [0, 0, 1], [0, 1]], ![[40, 17, 76], [63, 94, 111], [82, 76, 102], [119, 66, 64], [69, 29, 93], [115, 113, 10], [60, 90, 17], [81, 121, 63]], ![[0, 1], [20, 97, 25], [126, 28, 128], [131, 124, 103], [75, 64, 72], [138, 117, 61], [30, 49, 121], [40, 17, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 89], []]
 b := ![[], [90, 103, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [112, 117, 18, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1015395, -302047, -48650]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-7305, -2173, -350]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 2685619 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def PBC139 : ContainsPrimesAboveP 139 ![I139N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![139, 0, 0]]) timesTableT_eq_Table B_one_repr 139 (by decide) 𝕀

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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [49, 55, 11, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 99, 13], [25, 49, 136], [0, 1]]
 g := ![![[95, 88, 73], [99, 76], [53, 0, 16], [77, 46], [81, 146, 35], [138, 1], []], ![[49, 54, 113, 138], [29, 133], [125, 80, 34, 131], [100, 5], [84, 102, 2, 51], [30, 17], [119, 20]], ![[107, 68, 57, 139], [86, 144], [13, 137, 64, 44], [19, 69], [133, 21, 25, 10], [31, 116], [145, 20]]]
 h' := ![![[113, 99, 13], [139, 85, 85], [85, 93, 134], [37, 127, 145], [54, 133, 33], [92, 109, 66], [0, 0, 1], [0, 1]], ![[25, 49, 136], [47, 57, 55], [96, 138, 27], [46, 112, 114], [124, 11, 68], [73, 124, 32], [84, 98, 49], [113, 99, 13]], ![[0, 1], [82, 7, 9], [78, 67, 137], [77, 59, 39], [76, 5, 48], [85, 65, 51], [76, 51, 99], [25, 49, 136]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [10, 144], []]
 b := ![[], [26, 42, 115], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [49, 55, 11, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7520179, 3164462, 684655]
  a := ![2, -2, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![50471, 21238, 4595]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-122, 64, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-122, 64, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![29, 64, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-122, 64, 1], ![419, -49, 129], ![22934, 4886, 15]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-29, -64, 151]], ![![-1, 0, 1], ![-22, -55, 129], ![149, 26, 15]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [84, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 150], [0, 1]]
 g := ![![[106, 9], [135, 124], [134, 94], [139], [102, 90], [25], [1]], ![[0, 142], [0, 27], [0, 57], [139], [99, 61], [25], [1]]]
 h' := ![![[5, 150], [136, 3], [69, 107], [113, 68], [39, 21], [124, 40], [67, 5], [0, 1]], ![[0, 1], [0, 148], [0, 44], [0, 83], [144, 130], [22, 111], [92, 146], [5, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34]]
 b := ![[], [33, 17]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [84, 146, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![880144, 922564, 316802]
  a := ![-65, 1, -66]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-55014, -128164, 316802]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![22, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![22, 1, 0]] 
 ![![151, 0, 0], ![22, 1, 0], ![136, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![22, 1, 0], ![1, 22, 2], ![355, 73, 23]]]
  hmulB := by decide  
  f := ![![![-10867, -249239, -22660], ![-3171, 1710830, 0]], ![![-1584, -36297, -3300], ![-452, 249150, 0]], ![![-9784, -224480, -20409], ![-2880, 1540880, 0]]]
  g := ![![![1, 0, 0], ![-22, 151, 0], ![-136, 0, 151]], ![![0, 1, 0], ![-5, 22, 2], ![-29, 73, 23]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-122, 64, 1]] ![![151, 0, 0], ![22, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![3322, 151, 0]], ![![-18422, 9664, 151], ![-2265, 1359, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![22, 1, 0]]], ![![![-122, 64, 1]], ![![-15, 9, 1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![55, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![55, 1, 0]] 
 ![![157, 0, 0], ![55, 1, 0], ![58, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![55, 1, 0], ![1, 55, 2], ![355, 73, 56]]]
  hmulB := by decide  
  f := ![![![126, 9899, 360], ![157, -28260, 0]], ![![8, 3464, 126], ![158, -9891, 0]], ![![49, 3657, 133], ![51, -10440, 0]]]
  g := ![![![1, 0, 0], ![-55, 157, 0], ![-58, 0, 157]], ![![0, 1, 0], ![-20, 55, 2], ![-44, 73, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-35, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-35, 1, 0]] 
 ![![157, 0, 0], ![122, 1, 0], ![16, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-35, 1, 0], ![1, -35, 2], ![355, 73, -34]]]
  hmulB := by decide  
  f := ![![![819, -31078, 1776], ![-314, -139416, 0]], ![![656, -24149, 1380], ![-156, -108330, 0]], ![![112, -3168, 181], ![96, -14208, 0]]]
  g := ![![![1, 0, 0], ![-122, 157, 0], ![-16, 0, 157]], ![![-1, 1, 0], ![27, -35, 2], ![-51, 73, -34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1

def I157N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-135, -34, 6]] i)))

def SI157N2: IdealEqSpanCertificate' Table ![![-135, -34, 6]] 
 ![![157, 0, 0], ![136, 1, 0], ![94, 0, 1]] where
  M :=![![![-135, -34, 6], ![2096, 303, -62], ![-10786, -1198, 269]]]
  hmulB := by decide  
  f := ![![![-7231, -1958, -290]], ![![-6932, -1877, -278]], ![![-9152, -2478, -367]]]
  g := ![![![25, -34, 6], ![-212, 303, -62], ![808, -1198, 269]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N2 : Nat.card (O ⧸ I157N2) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N2)

lemma isPrimeI157N2 : Ideal.IsPrime I157N2 := prime_ideal_of_norm_prime hp157.out _ NI157N2
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![55, 1, 0]] ![![157, 0, 0], ![-35, 1, 0]]
  ![![7231, 1958, 290]] where
 M := ![![![24649, 0, 0], ![-5495, 157, 0]], ![![8635, 157, 0], ![-1924, 20, 2]]]
 hmul := by decide  
 g := ![![![![21195, 5338, -942]], ![![-6821, -1493, 272]]], ![![![5329, 1567, -268]], ![![-1784, -440, 78]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![7231, 1958, 290]] ![![-135, -34, 6]]
  ![![157, 0, 0]] where
 M := ![![![-157, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![30, 58, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![30, 58, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![30, 58, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![30, 58, 1], ![413, 103, 117], ![20804, 4448, 161]]]
  hmulB := by decide  
  f := ![![![-29, -58, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -58, 163]], ![![0, 0, 1], ![-19, -41, 117], ![98, -30, 161]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [27, 45, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [118, 162], [0, 1]]
 g := ![![[56, 136], [113, 121], [140], [40], [21], [140, 69], [1]], ![[130, 27], [47, 42], [140], [40], [21], [132, 94], [1]]]
 h' := ![![[118, 162], [46, 138], [103, 152], [121, 125], [68, 140], [132, 64], [136, 118], [0, 1]], ![[0, 1], [30, 25], [109, 11], [38, 38], [125, 23], [23, 99], [42, 45], [118, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [21]]
 b := ![[], [114, 92]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [27, 45, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1742, 4661, 1612]
  a := ![-2, 1, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-286, -545, 1612]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![46, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![46, 1, 0]] 
 ![![163, 0, 0], ![46, 1, 0], ![2, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![46, 1, 0], ![1, 46, 2], ![355, 73, 47]]]
  hmulB := by decide  
  f := ![![![2317, 125571, 5460], ![1467, -444990, 0]], ![![632, 35417, 1540], ![490, -125510, 0]], ![![-6, 1540, 67], ![140, -5460, 0]]]
  g := ![![![1, 0, 0], ![-46, 163, 0], ![-2, 0, 163]], ![![0, 1, 0], ![-13, 46, 2], ![-19, 73, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![30, 58, 1]] ![![163, 0, 0], ![46, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![7498, 163, 0]], ![![4890, 9454, 163], ![1793, 2771, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![46, 1, 0]]], ![![![30, 58, 1]], ![![11, 17, 1]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2468, 133, -42]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![2468, 133, -42]] 
 ![![167, 0, 0], ![0, 167, 0], ![148, 136, 1]] where
  M :=![![![2468, 133, -42], ![-14777, -598, 224], ![38227, 721, -465]]]
  hmulB := by decide  
  f := ![![![698, 189, 28]], ![![10129, 2742, 406]], ![![9305, 2519, 373]]]
  g := ![![![52, 35, -42], ![-287, -186, 224], ![641, 383, -465]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [66, 143, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 166], [0, 1]]
 g := ![![[30, 124], [85, 32], [50, 84], [54], [8], [135, 75], [1]], ![[0, 43], [18, 135], [62, 83], [54], [8], [98, 92], [1]]]
 h' := ![![[24, 166], [68, 25], [40, 52], [80, 90], [114, 87], [108, 141], [101, 24], [0, 1]], ![[0, 1], [0, 142], [119, 115], [69, 77], [31, 80], [152, 26], [9, 143], [24, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152]]
 b := ![[], [90, 76]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [66, 143, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2201, 1007, 16]
  a := ![-1, -1, -2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -7, 16]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![698, 189, 28]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![698, 189, 28]] 
 ![![167, 0, 0], ![61, 1, 0], ![144, 0, 1]] where
  M :=![![![698, 189, 28], ![10129, 2742, 406], ![73087, 19789, 2931]]]
  hmulB := by decide  
  f := ![![![2468, 133, -42]], ![![813, 45, -14]], ![![2357, 119, -39]]]
  g := ![![![-89, 189, 28], ![-1291, 2742, 406], ![-9318, 19789, 2931]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![2468, 133, -42]] ![![698, 189, 28]]
  ![![167, 0, 0]] where
 M := ![![![167, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  


def PBC167 : ContainsPrimesAboveP 167 ![I167N0, I167N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
    exact isPrimeI167N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 167 (by decide) (𝕀 ⊙ MulI167N0)
instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-37, 4, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-37, 4, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![136, 4, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-37, 4, 1], ![359, 36, 9], ![1634, 506, 40]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-136, -4, 173]], ![![-1, 0, 1], ![-5, 0, 9], ![-22, 2, 40]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [171, 3, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [170, 172], [0, 1]]
 g := ![![[85, 15], [37], [44, 10], [155, 164], [118], [134, 9], [1]], ![[40, 158], [37], [14, 163], [9, 9], [118], [107, 164], [1]]]
 h' := ![![[170, 172], [33, 154], [88, 146], [137, 23], [92, 106], [95, 139], [2, 170], [0, 1]], ![[0, 1], [90, 19], [169, 27], [68, 150], [120, 67], [24, 34], [11, 3], [170, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71]]
 b := ![[], [10, 122]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [171, 3, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![42938, 10381, 1514]
  a := ![2, 19, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-942, 25, 1514]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-9, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-9, 1, 0]] 
 ![![173, 0, 0], ![164, 1, 0], ![133, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-9, 1, 0], ![1, -9, 2], ![355, 73, -8]]]
  hmulB := by decide  
  f := ![![![-13838, 125271, -27840], ![1557, 2408160, 0]], ![![-13122, 118747, -26390], ![1385, 2282735, 0]], ![![-10642, 96307, -21403], ![1129, 1851360, 0]]]
  g := ![![![1, 0, 0], ![-164, 173, 0], ![-133, 0, 173]], ![![-1, 1, 0], ![7, -9, 2], ![-61, 73, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-37, 4, 1]] ![![173, 0, 0], ![-9, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-1557, 173, 0]], ![![-6401, 692, 173], ![692, 0, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-9, 1, 0]]], ![![![-37, 4, 1]], ![![4, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![24, -12, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![24, -12, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![24, 167, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![24, -12, 1], ![343, 97, -23], ![-4046, -662, 85]]]
  hmulB := by decide  
  f := ![![![-23, 12, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-24, -167, 179]], ![![0, -1, 1], ![5, 22, -23], ![-34, -83, 85]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [106, 115, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 178], [0, 1]]
 g := ![![[148, 76], [177, 87], [12], [45], [118, 101], [124, 158], [1]], ![[0, 103], [17, 92], [12], [45], [138, 78], [33, 21], [1]]]
 h' := ![![[64, 178], [33, 75], [81, 96], [10, 38], [22, 90], [102, 97], [73, 64], [0, 1]], ![[0, 1], [0, 104], [139, 83], [115, 141], [54, 89], [45, 82], [52, 115], [64, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70]]
 b := ![[], [133, 35]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [106, 115, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4575, 945, 324]
  a := ![-2, 3, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-69, -297, 324]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![23, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![23, 1, 0]] 
 ![![179, 0, 0], ![23, 1, 0], ![94, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![23, 1, 0], ![1, 23, 2], ![355, 73, 24]]]
  hmulB := by decide  
  f := ![![![-10772, -255699, -22236], ![-2685, 1990122, 0]], ![![-1382, -32842, -2856], ![-357, 255612, 0]], ![![-5664, -134278, -11677], ![-1354, 1045092, 0]]]
  g := ![![![1, 0, 0], ![-23, 179, 0], ![-94, 0, 179]], ![![0, 1, 0], ![-4, 23, 2], ![-20, 73, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![24, -12, 1]] ![![179, 0, 0], ![23, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![4117, 179, 0]], ![![4296, -2148, 179], ![895, -179, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![23, 1, 0]]], ![![![24, -12, 1]], ![![5, -1, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0)
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [104, 49, 133, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 53, 34], [119, 127, 147], [0, 1]]
 g := ![![[79, 65, 55], [149, 176], [20, 26, 170], [127, 65], [159, 51, 65], [83, 48, 1], []], ![[3, 52, 124, 13], [170, 176], [143, 152, 35, 143], [6, 55], [6, 136, 83, 38], [82, 157, 90, 137], [86, 70]], ![[66, 160, 5, 46], [], [54, 111, 157, 156], [44, 119], [138, 137, 76, 29], [179, 27, 131, 62], [154, 70]]]
 h' := ![![[110, 53, 34], [27, 159, 112], [92, 81, 151], [67, 26, 129], [116, 177, 80], [56, 172, 80], [0, 0, 1], [0, 1]], ![[119, 127, 147], [120, 50, 82], [116, 37, 30], [86, 167, 72], [23, 36, 69], [137, 133, 80], [79, 166, 127], [110, 53, 34]], ![[0, 1], [152, 153, 168], [40, 63], [71, 169, 161], [22, 149, 32], [91, 57, 21], [136, 15, 53], [119, 127, 147]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97, 135], []]
 b := ![[], [35, 15, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [104, 49, 133, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7993503, 2828668, 560376]
  a := ![2, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![44163, 15628, 3096]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def PBC181 : ContainsPrimesAboveP 181 ![I181N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![181, 0, 0]]) timesTableT_eq_Table B_one_repr 181 (by decide) 𝕀

instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-138, 72, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-138, 72, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![53, 72, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-138, 72, 1], ![427, -65, 145], ![25774, 5470, 7]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-53, -72, 191]], ![![-1, 0, 1], ![-38, -55, 145], ![133, 26, 7]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [88, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [59, 190], [0, 1]]
 g := ![![[97, 144], [122, 81], [32, 134], [188, 3], [96, 72], [175, 43], [1]], ![[189, 47], [126, 110], [107, 57], [174, 188], [142, 119], [38, 148], [1]]]
 h' := ![![[59, 190], [151, 179], [49, 9], [73, 158], [147, 167], [71, 151], [103, 59], [0, 1]], ![[0, 1], [16, 12], [7, 182], [36, 33], [68, 24], [3, 40], [146, 132], [59, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [136]]
 b := ![[], [95, 68]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [88, 132, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4803, 5350, 1215]
  a := ![-5, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-312, -430, 1215]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![46, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![46, 1, 0]] 
 ![![191, 0, 0], ![46, 1, 0], ![184, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![46, 1, 0], ![1, 46, 2], ![355, 73, 47]]]
  hmulB := by decide  
  f := ![![![-1157, -59613, -2592], ![-573, 247536, 0]], ![![-312, -14352, -624], ![1, 59592, 0]], ![![-1150, -57429, -2497], ![-405, 238464, 0]]]
  g := ![![![1, 0, 0], ![-46, 191, 0], ![-184, 0, 191]], ![![0, 1, 0], ![-13, 46, 2], ![-61, 73, 47]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-138, 72, 1]] ![![191, 0, 0], ![46, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![8786, 191, 0]], ![![-26358, 13752, 191], ![-5921, 3247, 191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![46, 1, 0]]], ![![![-138, 72, 1]], ![![-31, 17, 1]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-118, -59, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-118, -59, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![75, 134, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-118, -59, 1], ![296, -45, -117], ![-20731, -4093, -104]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-75, -134, 193]], ![![-1, -1, 1], ![47, 81, -117], ![-67, 51, -104]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [43, 58, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [135, 192], [0, 1]]
 g := ![![[136, 9], [28], [97], [85], [81], [56], [135, 1]], ![[0, 184], [28], [97], [85], [81], [56], [77, 192]]]
 h' := ![![[135, 192], [19, 190], [79, 75], [191, 167], [117, 49], [133, 184], [178, 40], [0, 1]], ![[0, 1], [0, 3], [168, 118], [155, 26], [170, 144], [76, 9], [174, 153], [135, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [141]]
 b := ![[], [18, 167]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [43, 58, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-34505, -1716, 3104]
  a := ![4, -10, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1385, -2164, 3104]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-76, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-76, 1, 0]] 
 ![![193, 0, 0], ![117, 1, 0], ![104, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-76, 1, 0], ![1, -76, 2], ![355, 73, -75]]]
  hmulB := by decide  
  f := ![![![-2044, 213170, -5610], ![1930, 541365, 0]], ![![-1243, 129194, -3400], ![1159, 328100, 0]], ![![-1040, 114868, -3023], ![1196, 291720, 0]]]
  g := ![![![1, 0, 0], ![-117, 193, 0], ![-104, 0, 193]], ![![-1, 1, 0], ![45, -76, 2], ![-2, 73, -75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![-118, -59, 1]] ![![193, 0, 0], ![-76, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-14668, 193, 0]], ![![-22774, -11387, 193], ![9264, 4439, -193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-76, 1, 0]]], ![![![-118, -59, 1]], ![![48, 23, -1]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0)


lemma PB234I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB234I3 : PrimesBelowBoundCertificateInterval O 137 193 234 where
  m := 11
  g := ![1, 1, 2, 3, 2, 2, 2, 2, 1, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB234I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1, I157N2]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1]
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
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![36481, 191]
    · exact ![37249, 193]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
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
      exact NI157N2
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I151N1, I157N0, I157N1, I157N2, I163N1, I167N1, I173N1, I179N1, I191N1, I193N1]
  Il := ![[], [], [I151N1], [I157N0, I157N1, I157N2], [I163N1], [I167N1], [I173N1], [I179N1], [], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
