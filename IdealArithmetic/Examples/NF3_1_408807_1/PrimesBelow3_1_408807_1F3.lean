
import IdealArithmetic.Examples.NF3_1_408807_1.RI3_1_408807_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [79, 50, 97, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [73, 45, 65], [108, 93, 74], [0, 1]]
 g := ![![[124, 4, 46], [50, 96, 117], [3, 34], [113, 68, 79], [21, 31], [42, 1], []], ![[108, 84, 96, 54], [26, 88, 126, 121], [130, 31], [134, 27, 102, 54], [3, 69], [121, 31], [98, 55]], ![[98, 5, 89, 135], [98, 44, 19, 48], [63, 83], [114, 29, 136, 48], [20, 24], [123, 79], [89, 55]]]
 h' := ![![[73, 45, 65], [81, 70, 18], [29, 84, 16], [108, 65, 112], [55, 67, 94], [18, 45, 46], [0, 0, 1], [0, 1]], ![[108, 93, 74], [121, 36, 108], [79, 39, 137], [87, 90, 46], [107, 97, 31], [30, 44, 114], [89, 105, 93], [73, 45, 65]], ![[0, 1], [129, 33, 13], [107, 16, 125], [48, 123, 120], [78, 114, 14], [44, 50, 118], [46, 34, 45], [108, 93, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 39], []]
 b := ![[], [138, 17, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [79, 50, 97, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23074, -834, -2363]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![166, -6, -17]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [32, 108, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 145, 16], [74, 3, 133], [0, 1]]
 g := ![![[11, 52, 36], [1, 9], [86, 24, 148], [19, 129], [36, 55, 36], [20, 1], []], ![[122, 93, 90, 47], [42, 124], [4, 90, 112, 104], [53, 20], [116, 90, 71, 4], [82, 9], [75, 107]], ![[86, 44, 135, 49], [105, 5], [20, 90, 118, 68], [66, 28], [112, 118, 13, 69], [90, 16], [107, 107]]]
 h' := ![![[95, 145, 16], [100, 6, 143], [79, 144, 3], [98, 75, 44], [40, 13, 125], [105, 43, 143], [0, 0, 1], [0, 1]], ![[74, 3, 133], [107, 74, 78], [109, 120, 78], [127, 74, 140], [66, 42, 136], [51, 75, 74], [69, 83, 3], [95, 145, 16]], ![[0, 1], [3, 69, 77], [54, 34, 68], [129, 0, 114], [30, 94, 37], [64, 31, 81], [115, 66, 145], [74, 3, 133]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [142, 147], []]
 b := ![[], [120, 62, 56], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [32, 108, 129, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![57067, 12516, -18774]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![383, 84, -126]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-21, -52, 1]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-21, -52, 1]] 
 ![![151, 0, 0], ![0, 151, 0], ![130, 99, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-21, -52, 1], ![105, -42, -156], ![-5460, 1127, -42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-130, -99, 151]], ![![-1, -1, 1], ![135, 102, -156], ![0, 35, -42]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [31, 123, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 150], [0, 1]]
 g := ![![[116, 39], [19, 91], [43, 47], [37], [45, 22], [29], [1]], ![[0, 112], [0, 60], [0, 104], [37], [57, 129], [29], [1]]]
 h' := ![![[28, 150], [15, 48], [26, 53], [149, 54], [115, 43], [62, 133], [120, 28], [0, 1]], ![[0, 1], [0, 103], [0, 98], [0, 97], [111, 108], [11, 18], [149, 123], [28, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [76, 124]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [31, 123, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3955, 72, -13]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-15, 9, -13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![5, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![5, 1, 0]] 
 ![![151, 0, 0], ![5, 1, 0], ![42, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![5, 1, 0], ![0, 5, 3], ![105, -21, 5]]]
  hmulB := by decide  
  f := ![![![566, 113, 0], ![-17063, 0, 0]], ![![10, 2, 0], ![-301, 0, 0]], ![![152, 27, -2], ![-4582, 101, 0]]]
  g := ![![![1, 0, 0], ![-5, 151, 0], ![-42, 0, 151]], ![![0, 1, 0], ![-1, 5, 3], ![0, -21, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-21, -52, 1]] ![![151, 0, 0], ![5, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![755, 151, 0]], ![![-3171, -7852, 151], ![0, -302, -151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![5, 1, 0]]], ![![![-21, -52, 1]], ![![0, -2, -1]]]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-15, 50, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-15, 50, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![142, 50, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-15, 50, 1], ![105, -36, 150], ![5250, -1015, -36]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-142, -50, 157]], ![![-1, 0, 1], ![-135, -48, 150], ![66, 5, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [123, 130, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [27, 156], [0, 1]]
 g := ![![[107, 115], [51], [105, 30], [97, 25], [143, 100], [101], [1]], ![[72, 42], [51], [130, 127], [144, 132], [17, 57], [101], [1]]]
 h' := ![![[27, 156], [118, 127], [116, 88], [1, 40], [152, 152], [37, 10], [34, 27], [0, 1]], ![[0, 1], [93, 30], [137, 69], [139, 117], [17, 5], [150, 147], [135, 130], [27, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [18, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [123, 130, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-376, 573, -582]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![524, 189, -582]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![7, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![7, 1, 0]] 
 ![![157, 0, 0], ![7, 1, 0], ![36, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![7, 1, 0], ![0, 7, 3], ![105, -21, 7]]]
  hmulB := by decide  
  f := ![![![302, 43, 0], ![-6751, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![68, 5, -2], ![-1520, 105, 0]]]
  g := ![![![1, 0, 0], ![-7, 157, 0], ![-36, 0, 157]], ![![0, 1, 0], ![-1, 7, 3], ![0, -21, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-15, 50, 1]] ![![157, 0, 0], ![7, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![1099, 157, 0]], ![![-2355, 7850, 157], ![0, 314, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![7, 1, 0]]], ![![![-15, 50, 1]], ![![0, 2, 1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![67, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![67, 1, 0]] 
 ![![163, 0, 0], ![67, 1, 0], ![25, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![67, 1, 0], ![0, 67, 3], ![105, -21, 67]]]
  hmulB := by decide  
  f := ![![![3284, 49, 0], ![-7987, 0, 0]], ![![1340, 20, 0], ![-3259, 0, 0]], ![![456, -38, -2], ![-1109, 109, 0]]]
  g := ![![![1, 0, 0], ![-67, 163, 0], ![-25, 0, 163]], ![![0, 1, 0], ![-28, 67, 3], ![-1, -21, 67]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-46, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-46, 1, 0]] 
 ![![163, 0, 0], ![117, 1, 0], ![1, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-46, 1, 0], ![0, -46, 3], ![105, -21, -46]]]
  hmulB := by decide  
  f := ![![![2531, -55, 0], ![8965, 0, 0]], ![![1841, -40, 0], ![6521, 0, 0]], ![![81, 29, -2], ![287, 109, 0]]]
  g := ![![![1, 0, 0], ![-117, 163, 0], ![-1, 0, 163]], ![![-1, 1, 0], ![33, -46, 3], ![16, -21, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-21, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-21, 1, 0]] 
 ![![163, 0, 0], ![142, 1, 0], ![16, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-21, 1, 0], ![0, -21, 3], ![105, -21, -21]]]
  hmulB := by decide  
  f := ![![![2941, -140, 0], ![22820, 0, 0]], ![![2542, -121, 0], ![19724, 0, 0]], ![![316, -1, -2], ![2452, 109, 0]]]
  g := ![![![1, 0, 0], ![-142, 163, 0], ![-16, 0, 163]], ![![-1, 1, 0], ![18, -21, 3], ![21, -21, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![67, 1, 0]] ![![163, 0, 0], ![-46, 1, 0]]
  ![![163, 0, 0], ![5, 7, 1]] where
 M := ![![![26569, 0, 0], ![-7498, 163, 0]], ![![10921, 163, 0], ![-3082, 21, 3]]]
 hmul := by decide  
 g := ![![![![158, -7, -1], ![163, 0, 0]], ![![-46, 1, 0], ![0, 0, 0]]], ![![![62, -6, -1], ![163, 0, 0]], ![![-19, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![5, 7, 1]] ![![163, 0, 0], ![-21, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-3423, 163, 0]], ![![815, 1141, 163], ![0, -163, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-21, 1, 0]]], ![![![5, 7, 1]], ![![0, -1, 0]]]]
 hle2 := by decide  


def PBC163 : ContainsPrimesAboveP 163 ![I163N0, I163N1, I163N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
    exact isPrimeI163N1
    exact isPrimeI163N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 163 (by decide) (𝕀 ⊙ MulI163N0 ⊙ MulI163N1)
instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [16, 22, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 18, 97], [4, 148, 70], [0, 1]]
 g := ![![[102, 60, 8], [157, 12, 29], [102, 69, 147], [60, 62], [24, 54], [72, 42, 1], []], ![[139, 43, 0, 152], [27, 38, 75, 132], [60, 140, 137, 63], [122, 28], [44, 62], [119, 113, 105, 114], [41, 57]], ![[76, 33, 127, 37], [91, 25, 13, 13], [89, 68, 6, 91], [43, 130], [101, 1], [40, 35, 25, 135], [68, 57]]]
 h' := ![![[38, 18, 97], [160, 136, 26], [38, 55, 153], [49, 149, 100], [72, 60, 79], [17, 82, 80], [0, 0, 1], [0, 1]], ![[4, 148, 70], [98, 37, 6], [114, 53, 90], [9, 166, 28], [142, 81, 144], [41, 31, 88], [120, 55, 148], [38, 18, 97]], ![[0, 1], [53, 161, 135], [69, 59, 91], [158, 19, 39], [126, 26, 111], [89, 54, 166], [97, 112, 18], [4, 148, 70]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [74, 152], []]
 b := ![[], [26, 154, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [16, 22, 125, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28891, -1002, -2839]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![173, -6, -17]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def PBC167 : ContainsPrimesAboveP 167 ![I167N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI167N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![167, 0, 0]]) timesTableT_eq_Table B_one_repr 167 (by decide) 𝕀

instance hp173 : Fact (Nat.Prime 173) := {out := by norm_num}

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-5, -7, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-5, -7, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![168, 166, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-5, -7, 1], ![105, -26, -21], ![-735, 182, -26]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-168, -166, 173]], ![![-1, -1, 1], ![21, 20, -21], ![21, 26, -26]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [92, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [39, 172], [0, 1]]
 g := ![![[103, 126], [169], [26, 139], [34, 54], [157], [70, 137], [1]], ![[0, 47], [169], [84, 34], [64, 119], [157], [50, 36], [1]]]
 h' := ![![[39, 172], [57, 105], [30, 13], [159, 100], [52, 20], [134, 147], [81, 39], [0, 1]], ![[0, 1], [0, 68], [18, 160], [80, 73], [140, 153], [158, 26], [45, 134], [39, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [12]]
 b := ![[], [56, 6]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [92, 134, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4217, 1821, 1198]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1139, -1139, 1198]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![21, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![21, 1, 0]] 
 ![![173, 0, 0], ![21, 1, 0], ![26, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![21, 1, 0], ![0, 21, 3], ![105, -21, 21]]]
  hmulB := by decide  
  f := ![![![652, 31, 0], ![-5363, 0, 0]], ![![42, 2, 0], ![-345, 0, 0]], ![![64, -4, -1], ![-526, 58, 0]]]
  g := ![![![1, 0, 0], ![-21, 173, 0], ![-26, 0, 173]], ![![0, 1, 0], ![-3, 21, 3], ![0, -21, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![-5, -7, 1]] ![![173, 0, 0], ![21, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![3633, 173, 0]], ![![-865, -1211, 173], ![0, -173, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![21, 1, 0]]], ![![![-5, -7, 1]], ![![0, -1, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![9, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![9, 1, 0]] 
 ![![179, 0, 0], ![9, 1, 0], ![152, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![9, 1, 0], ![0, 9, 3], ![105, -21, 9]]]
  hmulB := by decide  
  f := ![![![163, 18, 0], ![-3222, 0, 0]], ![![-9, -1, 0], ![180, 0, 0]], ![![136, 12, -1], ![-2688, 60, 0]]]
  g := ![![![1, 0, 0], ![-9, 179, 0], ![-152, 0, 179]], ![![0, 1, 0], ![-3, 9, 3], ![-6, -21, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![75, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![75, 1, 0]] 
 ![![179, 0, 0], ![75, 1, 0], ![94, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![75, 1, 0], ![0, 75, 3], ![105, -21, 75]]]
  hmulB := by decide  
  f := ![![![3901, 52, 0], ![-9308, 0, 0]], ![![1575, 21, 0], ![-3758, 0, 0]], ![![2036, 2, -1], ![-4858, 60, 0]]]
  g := ![![![1, 0, 0], ![-75, 179, 0], ![-94, 0, 179]], ![![0, 1, 0], ![-33, 75, 3], ![-30, -21, 75]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-84, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-84, 1, 0]] 
 ![![179, 0, 0], ![95, 1, 0], ![154, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-84, 1, 0], ![0, -84, 3], ![105, -21, -84]]]
  hmulB := by decide  
  f := ![![![13273, -158, 0], ![28282, 0, 0]], ![![7141, -85, 0], ![15216, 0, 0]], ![![11438, -108, -1], ![24372, 60, 0]]]
  g := ![![![1, 0, 0], ![-95, 179, 0], ![-154, 0, 179]], ![![-1, 1, 0], ![42, -84, 3], ![84, -21, -84]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![9, 1, 0]] ![![179, 0, 0], ![75, 1, 0]]
  ![![179, 0, 0], ![46, 28, 1]] where
 M := ![![![32041, 0, 0], ![13425, 179, 0]], ![![1611, 179, 0], ![675, 84, 3]]]
 hmul := by decide  
 g := ![![![![133, -28, -1], ![179, 0, 0]], ![![29, -27, -1], ![179, 0, 0]]], ![![![-37, -27, -1], ![179, 0, 0]], ![![3, 0, 0], ![3, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![46, 28, 1]] ![![179, 0, 0], ![-84, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-15036, 179, 0]], ![![8234, 5012, 179], ![-3759, -2327, 0]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-84, 1, 0]]], ![![![46, 28, 1]], ![![-21, -13, 0]]]]
 hle2 := by decide  


def PBC179 : ContainsPrimesAboveP 179 ![I179N0, I179N1, I179N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
    exact isPrimeI179N1
    exact isPrimeI179N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 179 (by decide) (𝕀 ⊙ MulI179N0 ⊙ MulI179N1)


lemma PB181I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 180 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 180 (by omega)

def PB181I3 : PrimesBelowBoundCertificateInterval O 137 180 181 where
  m := 8
  g := ![1, 1, 2, 2, 3, 1, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB181I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![2685619]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![24649, 157]
    · exact ![163, 163, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![179, 179, 179]
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
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
      exact NI163N2
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
  β := ![I151N1, I157N1, I163N0, I163N1, I163N2, I173N1, I179N0, I179N1, I179N2]
  Il := ![[], [], [I151N1], [I157N1], [I163N0, I163N1, I163N2], [], [I173N1], [I179N0, I179N1, I179N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
