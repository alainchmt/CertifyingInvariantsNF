
import IdealArithmetic.Examples.NF3_1_557179_1.RI3_1_557179_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![33, 29, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![33, 29, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![33, 29, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![33, 29, 1], ![-144, 63, 261], ![-4160, 13, 34]]]
  hmulB := by decide  
  f := ![![![-32, -29, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -29, 139]], ![![0, 0, 1], ![-63, -54, 261], ![-38, -7, 34]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [85, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 138], [0, 1]]
 g := ![![[30, 80], [91, 46], [24], [70, 41], [121], [80], [1]], ![[82, 59], [107, 93], [24], [48, 98], [121], [80], [1]]]
 h' := ![![[91, 138], [49, 48], [79, 121], [27, 21], [65, 67], [8, 11], [54, 91], [0, 1]], ![[0, 1], [108, 91], [109, 18], [131, 118], [46, 72], [36, 128], [134, 48], [91, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [90, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [85, 48, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5083, -4648, -491]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![80, 69, -491]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![17, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![17, 1, 0]] 
 ![![139, 0, 0], ![17, 1, 0], ![105, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![17, 1, 0], ![0, 18, 9], ![-144, 1, 17]]]
  hmulB := by decide  
  f := ![![![1259, 74, 0], ![-10286, 0, 0]], ![![153, 9, 0], ![-1250, 0, 0]], ![![953, 52, -2], ![-7786, 31, 0]]]
  g := ![![![1, 0, 0], ![-17, 139, 0], ![-105, 0, 139]], ![![0, 1, 0], ![-9, 18, 9], ![-14, 1, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![33, 29, 1]] ![![139, 0, 0], ![17, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![2363, 139, 0]], ![![4587, 4031, 139], ![417, 556, 278]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![17, 1, 0]]], ![![![33, 29, 1]], ![![3, 4, 2]]]]
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [93, 65, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 83, 145], [8, 65, 4], [0, 1]]
 g := ![![[96, 2, 1], [19, 118], [95, 63, 118], [47, 130], [124, 139, 28], [20, 1], []], ![[81, 28, 135, 22], [38, 36], [141, 96, 4, 100], [142, 125], [12, 12, 49, 28], [85, 53], [103, 16]], ![[24, 102, 57, 45], [80, 124], [123, 87, 96, 144], [24, 100], [107, 93, 6, 73], [8, 35], [95, 16]]]
 h' := ![![[12, 83, 145], [20, 140, 1], [105, 51, 72], [4, 72, 72], [90, 140, 117], [77, 97, 37], [0, 0, 1], [0, 1]], ![[8, 65, 4], [13, 65, 101], [92, 117, 6], [94, 72, 71], [28, 89, 42], [61, 100, 80], [101, 67, 65], [12, 83, 145]], ![[0, 1], [117, 93, 47], [16, 130, 71], [83, 5, 6], [123, 69, 139], [103, 101, 32], [20, 82, 83], [8, 65, 4]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [81, 68], []]
 b := ![[], [18, 66, 17], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [93, 65, 129, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2879276, -288166, -15049]
  a := ![-1, 1, 11]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![19324, -1934, -101]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [15, 147, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [48, 71, 10], [60, 79, 141], [0, 1]]
 g := ![![[27, 65, 9], [123, 105, 49], [10, 91, 91], [106, 29], [138, 114, 20], [108, 1], []], ![[38, 91, 57, 84], [125, 39, 68, 137], [88, 101, 97, 36], [113, 37], [149, 59, 130, 94], [24, 50], [140, 100]], ![[4, 11, 97, 51], [31, 144, 68, 35], [95, 85, 69, 135], [118, 58], [103, 128, 133, 113], [107, 58], [9, 100]]]
 h' := ![![[48, 71, 10], [118, 126, 148], [1, 7, 7], [44, 109, 53], [44, 70, 28], [41, 115, 41], [0, 0, 1], [0, 1]], ![[60, 79, 141], [118, 76, 117], [104, 104, 19], [82, 104, 143], [56, 76, 43], [33, 82, 10], [53, 138, 79], [48, 71, 10]], ![[0, 1], [1, 100, 37], [63, 40, 125], [120, 89, 106], [94, 5, 80], [120, 105, 100], [143, 13, 71], [60, 79, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 54], []]
 b := ![[], [136, 134, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [15, 147, 43, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100113, 2416, -7097]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-663, 16, -47]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 3442951 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def PBC151 : ContainsPrimesAboveP 151 ![I151N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![151, 0, 0]]) timesTableT_eq_Table B_one_repr 151 (by decide) 𝕀

instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [14, 93, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 122, 59], [18, 34, 98], [0, 1]]
 g := ![![[60, 84, 86], [13, 146], [45, 2, 127], [150, 123, 30], [15, 134, 86], [120, 1], []], ![[153, 86, 88, 97], [9, 144], [45, 141, 40, 77], [107, 28, 149, 107], [18, 23, 80, 7], [124, 57], [52, 27]], ![[137, 57, 71, 116], [101, 3], [130, 74, 43, 150], [28, 74, 28, 59], [17, 67, 153, 112], [24, 126], [13, 27]]]
 h' := ![![[102, 122, 59], [136, 146, 137], [155, 53, 97], [98, 11, 21], [104, 37, 40], [47, 130, 20], [0, 0, 1], [0, 1]], ![[18, 34, 98], [17, 33, 84], [92, 72, 145], [2, 16, 107], [145, 37, 89], [58, 41, 29], [99, 49, 34], [102, 122, 59]], ![[0, 1], [81, 135, 93], [125, 32, 72], [138, 130, 29], [13, 83, 28], [46, 143, 108], [142, 108, 122], [18, 34, 98]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152, 68], []]
 b := ![[], [150, 22, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [14, 93, 37, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-15797183, 21666, 205827]
  a := ![1, -2, -19]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-100619, 138, 1311]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def PBC157 : ContainsPrimesAboveP 157 ![I157N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![157, 0, 0]]) timesTableT_eq_Table B_one_repr 157 (by decide) 𝕀

instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![31, 1, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![31, 1, 0]] 
 ![![163, 0, 0], ![31, 1, 0], ![89, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![31, 1, 0], ![0, 32, 9], ![-144, 1, 31]]]
  hmulB := by decide  
  f := ![![![3287, 106, 0], ![-17278, 0, 0]], ![![589, 19, 0], ![-3096, 0, 0]], ![![1751, 28, -8], ![-9204, 145, 0]]]
  g := ![![![1, 0, 0], ![-31, 163, 0], ![-89, 0, 163]], ![![0, 1, 0], ![-11, 32, 9], ![-18, 1, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N0 : Nat.card (O ⧸ I163N0) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N0)

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := prime_ideal_of_norm_prime hp163.out _ NI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![51, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![51, 1, 0]] 
 ![![163, 0, 0], ![51, 1, 0], ![140, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![51, 1, 0], ![0, 52, 9], ![-144, 1, 51]]]
  hmulB := by decide  
  f := ![![![409, 8, 0], ![-1304, 0, 0]], ![![51, 1, 0], ![-162, 0, 0]], ![![320, -40, -8], ![-1020, 145, 0]]]
  g := ![![![1, 0, 0], ![-51, 163, 0], ![-140, 0, 163]], ![![0, 1, 0], ![-24, 52, 9], ![-45, 1, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1

def I163N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![80, 1, 0]] i)))

def SI163N2: IdealEqSpanCertificate' Table ![![163, 0, 0], ![80, 1, 0]] 
 ![![163, 0, 0], ![80, 1, 0], ![95, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![80, 1, 0], ![0, 81, 9], ![-144, 1, 80]]]
  hmulB := by decide  
  f := ![![![1761, 22, 0], ![-3586, 0, 0]], ![![880, 11, 0], ![-1792, 0, 0]], ![![1045, 22, 1], ![-2128, -18, 0]]]
  g := ![![![1, 0, 0], ![-80, 163, 0], ![-95, 0, 163]], ![![0, 1, 0], ![-45, 81, 9], ![-48, 1, 80]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N2 : Nat.card (O ⧸ I163N2) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N2)

lemma isPrimeI163N2 : Ideal.IsPrime I163N2 := prime_ideal_of_norm_prime hp163.out _ NI163N2
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![31, 1, 0]] ![![163, 0, 0], ![51, 1, 0]]
  ![![163, 0, 0], ![67, -27, 1]] where
 M := ![![![26569, 0, 0], ![8313, 163, 0]], ![![5053, 163, 0], ![1581, 83, 9]]]
 hmul := by decide  
 g := ![![![![96, 27, -1], ![163, 0, 0]], ![![-16, 28, -1], ![163, 0, 0]]], ![![![-36, 28, -1], ![163, 0, 0]], ![![6, 2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI163N1 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![67, -27, 1]] ![![163, 0, 0], ![80, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![13040, 163, 0]], ![![10921, -4401, 163], ![5216, -2119, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![80, 1, 0]]], ![![![67, -27, 1]], ![![32, -13, -1]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [41, 164, 36, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 110, 114], [36, 56, 53], [0, 1]]
 g := ![![[71, 43, 121], [143, 9, 31], [117, 47, 54], [109, 29], [102, 29], [130, 131, 1], []], ![[129, 113, 146, 76], [155, 94, 86, 99], [44, 40, 81, 3], [48, 61], [16, 44], [42, 62, 81, 124], [108, 137]], ![[119, 141, 109, 20], [39, 96, 1, 39], [24, 51, 40, 35], [131, 11], [81, 31], [18, 51, 138, 20], [2, 137]]]
 h' := ![![[95, 110, 114], [149, 5, 156], [46, 122, 71], [23, 22, 87], [22, 96, 153], [14, 29, 14], [0, 0, 1], [0, 1]], ![[36, 56, 53], [157, 48, 121], [15, 112, 15], [83, 14, 32], [61, 144, 140], [160, 79, 82], [88, 76, 56], [95, 110, 114]], ![[0, 1], [1, 114, 57], [118, 100, 81], [54, 131, 48], [9, 94, 41], [18, 59, 71], [45, 91, 110], [36, 56, 53]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 112], []]
 b := ![[], [35, 4, 125], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [41, 164, 36, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11324103, 20374, 173179]
  a := ![0, -2, -17]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-67809, 122, 1037]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [13, 170, 1, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 164, 110], [86, 8, 63], [0, 1]]
 g := ![![[20, 73, 100], [124, 151], [106, 41, 118], [160, 138, 77], [157, 54], [4, 172, 1], []], ![[62, 63, 94, 63], [26, 109], [61, 60, 98, 171], [124, 14, 97, 99], [32, 25], [95, 4, 39, 120], [106, 163]], ![[123, 46, 68, 123], [152, 56], [146, 36, 63, 123], [139, 7, 107, 94], [140, 106], [98, 126, 146, 86], [153, 163]]]
 h' := ![![[86, 164, 110], [154, 0, 10], [6, 147, 18], [169, 46, 139], [144, 110, 115], [121, 25, 153], [0, 0, 1], [0, 1]], ![[86, 8, 63], [130, 72, 80], [45, 156, 52], [20, 137, 117], [159, 11, 45], [70, 150, 168], [136, 111, 8], [86, 164, 110]], ![[0, 1], [75, 101, 83], [119, 43, 103], [34, 163, 90], [132, 52, 13], [7, 171, 25], [44, 62, 164], [86, 8, 63]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79, 74], []]
 b := ![[], [149, 27, 122], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [13, 170, 1, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9445636169, -161165416, -151054604]
  a := ![1, 20, 161]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![54599053, -931592, -873148]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def PBC173 : ContainsPrimesAboveP 173 ![I173N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![173, 0, 0]]) timesTableT_eq_Table B_one_repr 173 (by decide) 𝕀

instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![24, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![24, 1, 0]] 
 ![![179, 0, 0], ![24, 1, 0], ![172, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![24, 1, 0], ![0, 25, 9], ![-144, 1, 24]]]
  hmulB := by decide  
  f := ![![![2137, 89, 0], ![-15931, 0, 0]], ![![264, 11, 0], ![-1968, 0, 0]], ![![2084, 84, -1], ![-15536, 20, 0]]]
  g := ![![![1, 0, 0], ![-24, 179, 0], ![-172, 0, 179]], ![![0, 1, 0], ![-12, 25, 9], ![-24, 1, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![31, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![31, 1, 0]] 
 ![![179, 0, 0], ![31, 1, 0], ![29, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![31, 1, 0], ![0, 32, 9], ![-144, 1, 31]]]
  hmulB := by decide  
  f := ![![![1489, 48, 0], ![-8592, 0, 0]], ![![217, 7, 0], ![-1252, 0, 0]], ![![235, 4, -1], ![-1356, 20, 0]]]
  g := ![![![1, 0, 0], ![-31, 179, 0], ![-29, 0, 179]], ![![0, 1, 0], ![-7, 32, 9], ![-6, 1, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-56, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-56, 1, 0]] 
 ![![179, 0, 0], ![123, 1, 0], ![155, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-56, 1, 0], ![0, -55, 9], ![-144, 1, -56]]]
  hmulB := by decide  
  f := ![![![5713, -102, 0], ![18258, 0, 0]], ![![3977, -71, 0], ![12710, 0, 0]], ![![4937, -82, -1], ![15778, 20, 0]]]
  g := ![![![1, 0, 0], ![-123, 179, 0], ![-155, 0, 179]], ![![-1, 1, 0], ![30, -55, 9], ![47, 1, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![24, 1, 0]] ![![179, 0, 0], ![31, 1, 0]]
  ![![179, 0, 0], ![23, 46, 1]] where
 M := ![![![32041, 0, 0], ![5549, 179, 0]], ![![4296, 179, 0], ![744, 56, 9]]]
 hmul := by decide  
 g := ![![![![156, -46, -1], ![179, 0, 0]], ![![8, -45, -1], ![179, 0, 0]]], ![![![1, -45, -1], ![179, 0, 0]], ![![3, -2, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![23, 46, 1]] ![![179, 0, 0], ![-56, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-10024, 179, 0]], ![![4117, 8234, 179], ![-1432, -2506, 358]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-56, 1, 0]]], ![![![23, 46, 1]], ![![-8, -14, 2]]]]
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
instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-137, 13, -10]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-137, 13, -10]] 
 ![![181, 0, 0], ![0, 181, 0], ![68, 53, 1]] where
  M :=![![![-137, 13, -10], ![1440, -134, 117], ![-2032, 173, -147]]]
  hmulB := by decide  
  f := ![![![3, -1, -1]], ![![144, 1, -9]], ![![44, 0, -3]]]
  g := ![![![3, 3, -10], ![-36, -35, 117], ![44, 44, -147]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [21, 149, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [32, 180], [0, 1]]
 g := ![![[145, 126], [116], [35, 4], [70], [51, 125], [111, 119], [1]], ![[14, 55], [116], [163, 177], [70], [69, 56], [118, 62], [1]]]
 h' := ![![[32, 180], [38, 137], [170, 72], [22, 2], [15, 34], [22, 46], [160, 32], [0, 1]], ![[0, 1], [78, 44], [121, 109], [86, 179], [17, 147], [46, 135], [98, 149], [32, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124]]
 b := ![[], [94, 62]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [21, 149, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5167, -3242, 2466]
  a := ![-1, 2, 15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-955, -740, 2466]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3, 1, 1]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-3, 1, 1]] 
 ![![181, 0, 0], ![66, 1, 0], ![112, 0, 1]] where
  M :=![![![-3, 1, 1], ![-144, -1, 9], ![-128, -15, -2]]]
  hmulB := by decide  
  f := ![![![137, -13, 10]], ![![42, -4, 3]], ![![96, -9, 7]]]
  g := ![![![-1, 1, 1], ![-6, -1, 9], ![6, -15, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-137, 13, -10]] ![![-3, 1, 1]]
  ![![181, 0, 0]] where
 M := ![![![-181, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![74, -57, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![74, -57, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![74, 134, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![74, -57, 1], ![-144, 18, -513], ![8224, -73, 75]]]
  hmulB := by decide  
  f := ![![![-73, 57, -1], ![191, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-74, -134, 191]], ![![0, -1, 1], ![198, 360, -513], ![14, -53, 75]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [70, 165, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [26, 190], [0, 1]]
 g := ![![[16, 134], [31, 27], [100, 17], [12, 13], [162, 81], [184, 103], [1]], ![[62, 57], [160, 164], [160, 174], [159, 178], [167, 110], [188, 88], [1]]]
 h' := ![![[26, 190], [122, 158], [67, 119], [115, 50], [120, 83], [108, 182], [121, 26], [0, 1]], ![[0, 1], [28, 33], [105, 72], [78, 141], [177, 108], [65, 9], [33, 165], [26, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [27]]
 b := ![[], [111, 109]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [70, 165, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-11578, -10156, 5047]
  a := ![0, 3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2016, -3594, 5047]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-60, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-60, 1, 0]] 
 ![![191, 0, 0], ![131, 1, 0], ![116, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-60, 1, 0], ![0, -59, 9], ![-144, 1, -60]]]
  hmulB := by decide  
  f := ![![![9841, -164, 0], ![31324, 0, 0]], ![![6781, -113, 0], ![21584, 0, 0]], ![![5956, -73, -4], ![18958, 85, 0]]]
  g := ![![![1, 0, 0], ![-131, 191, 0], ![-116, 0, 191]], ![![-1, 1, 0], ![35, -59, 9], ![35, 1, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![74, -57, 1]] ![![191, 0, 0], ![-60, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-11460, 191, 0]], ![![14134, -10887, 191], ![-4584, 3438, -573]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-60, 1, 0]]], ![![![74, -57, 1]], ![![-24, 18, -3]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![48, 1, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![48, 1, 0]] 
 ![![193, 0, 0], ![48, 1, 0], ![189, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![48, 1, 0], ![0, 49, 9], ![-144, 1, 48]]]
  hmulB := by decide  
  f := ![![![6097, 127, 0], ![-24511, 0, 0]], ![![1488, 31, 0], ![-5982, 0, 0]], ![![5997, 114, -2], ![-24109, 43, 0]]]
  g := ![![![1, 0, 0], ![-48, 193, 0], ![-189, 0, 193]], ![![0, 1, 0], ![-21, 49, 9], ![-48, 1, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N0 : Nat.card (O ⧸ I193N0) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N0)

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := prime_ideal_of_norm_prime hp193.out _ NI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-44, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-44, 1, 0]] 
 ![![193, 0, 0], ![149, 1, 0], ![90, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-44, 1, 0], ![0, -43, 9], ![-144, 1, -44]]]
  hmulB := by decide  
  f := ![![![6073, -138, 0], ![26634, 0, 0]], ![![4709, -107, 0], ![20652, 0, 0]], ![![2842, -55, -2], ![12464, 43, 0]]]
  g := ![![![1, 0, 0], ![-149, 193, 0], ![-90, 0, 193]], ![![-1, 1, 0], ![29, -43, 9], ![19, 1, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-5, 1, 0]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-5, 1, 0]] 
 ![![193, 0, 0], ![188, 1, 0], ![105, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-5, 1, 0], ![0, -4, 9], ![-144, 1, -5]]]
  hmulB := by decide  
  f := ![![![601, -120, 0], ![23160, 0, 0]], ![![586, -117, 0], ![22582, 0, 0]], ![![325, -64, -2], ![12524, 43, 0]]]
  g := ![![![1, 0, 0], ![-188, 193, 0], ![-105, 0, 193]], ![![-1, 1, 0], ![-1, -4, 9], ![1, 1, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![48, 1, 0]] ![![193, 0, 0], ![-44, 1, 0]]
  ![![193, 0, 0], ![87, 22, 1]] where
 M := ![![![37249, 0, 0], ![-8492, 193, 0]], ![![9264, 193, 0], ![-2112, 5, 9]]]
 hmul := by decide  
 g := ![![![![106, -22, -1], ![193, 0, 0]], ![![-44, 1, 0], ![0, 0, 0]]], ![![![-39, -21, -1], ![193, 0, 0]], ![![-15, -1, 0], ![9, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![87, 22, 1]] ![![193, 0, 0], ![-5, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-965, 193, 0]], ![![16791, 4246, 193], ![-579, 0, 193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-5, 1, 0]]], ![![![87, 22, 1]], ![![-3, 0, 1]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)


lemma PB212I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB212I3 : PrimesBelowBoundCertificateInterval O 137 193 212 where
  m := 11
  g := ![2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 3]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB212I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1, I163N2]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0, I193N1, I193N2]
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
    · exact ![19321, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![163, 163, 163]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![193, 193, 193]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
      exact NI179N1
      exact NI179N2
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
  β := ![I139N1, I163N0, I163N1, I163N2, I179N0, I179N1, I179N2, I181N1, I191N1, I193N0, I193N1, I193N2]
  Il := ![[I139N1], [], [], [], [I163N0, I163N1, I163N2], [], [], [I179N0, I179N1, I179N2], [I181N1], [I191N1], [I193N0, I193N1, I193N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
