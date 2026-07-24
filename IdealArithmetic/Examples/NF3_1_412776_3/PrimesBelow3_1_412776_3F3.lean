
import IdealArithmetic.Examples.NF3_1_412776_3.RI3_1_412776_3
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![28, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![28, 1, 0]] 
 ![![139, 0, 0], ![28, 1, 0], ![25, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![28, 1, 0], ![0, 28, 2], ![112, -21, 28]]]
  hmulB := by decide  
  f := ![![![85, 3, 0], ![-417, 0, 0]], ![![-28, -1, 0], ![140, 0, 0]], ![![-25, -15, -1], ![125, 70, 0]]]
  g := ![![![1, 0, 0], ![-28, 139, 0], ![-25, 0, 139]], ![![0, 1, 0], ![-6, 28, 2], ![0, -21, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![50, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![50, 1, 0]] 
 ![![139, 0, 0], ![50, 1, 0], ![1, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![50, 1, 0], ![0, 50, 2], ![112, -21, 50]]]
  hmulB := by decide  
  f := ![![![2701, 54, 0], ![-7506, 0, 0]], ![![950, 19, 0], ![-2640, 0, 0]], ![![-41, -26, -1], ![114, 70, 0]]]
  g := ![![![1, 0, 0], ![-50, 139, 0], ![-1, 0, 139]], ![![0, 1, 0], ![-18, 50, 2], ![8, -21, 50]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![61, 1, 0]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![139, 0, 0], ![61, 1, 0]] 
 ![![139, 0, 0], ![61, 1, 0], ![16, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![61, 1, 0], ![0, 61, 2], ![112, -21, 61]]]
  hmulB := by decide  
  f := ![![![2807, 46, 0], ![-6394, 0, 0]], ![![1159, 19, 0], ![-2640, 0, 0]], ![![288, -26, -1], ![-656, 70, 0]]]
  g := ![![![1, 0, 0], ![-61, 139, 0], ![-16, 0, 139]], ![![0, 1, 0], ![-27, 61, 2], ![3, -21, 61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![28, 1, 0]] ![![139, 0, 0], ![50, 1, 0]]
  ![![139, 0, 0], ![5, 39, 1]] where
 M := ![![![19321, 0, 0], ![6950, 139, 0]], ![![3892, 139, 0], ![1400, 78, 2]]]
 hmul := by decide  
 g := ![![![![134, -39, -1], ![139, 0, 0]], ![![45, -38, -1], ![139, 0, 0]]], ![![![23, -38, -1], ![139, 0, 0]], ![![10, 0, 0], ![2, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![5, 39, 1]] ![![139, 0, 0], ![61, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![8479, 139, 0]], ![![695, 5421, 139], ![417, 2363, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![61, 1, 0]]], ![![![5, 39, 1]], ![![3, 17, 1]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 139 (by decide) (𝕀 ⊙ MulI139N0 ⊙ MulI139N1)
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [57, 147, 107, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 98, 82], [9, 50, 67], [0, 1]]
 g := ![![[70, 36, 140], [79, 140], [85, 48, 16], [58, 35], [76, 68, 37], [42, 1], []], ![[81, 126, 3, 36], [94, 54], [42, 41, 8, 73], [146, 53], [110, 80, 117, 36], [13, 116], [33, 19]], ![[51, 81, 82, 33], [13, 114], [118, 72, 117, 110], [21, 1], [122, 101, 105, 96], [108, 68], [48, 19]]]
 h' := ![![[33, 98, 82], [85, 56, 17], [72, 123, 17], [93, 71, 4], [138, 101, 83], [139, 27, 127], [0, 0, 1], [0, 1]], ![[9, 50, 67], [91, 113, 78], [54, 123, 59], [13, 5, 62], [17, 133, 65], [127, 136, 71], [102, 87, 50], [33, 98, 82]], ![[0, 1], [5, 129, 54], [148, 52, 73], [95, 73, 83], [10, 64, 1], [86, 135, 100], [27, 62, 98], [9, 50, 67]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 18], []]
 b := ![[], [78, 41, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [57, 147, 107, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![24585, 2086, -2831]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![165, 14, -19]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [52, 66, 129, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 142, 71], [75, 8, 80], [0, 1]]
 g := ![![[62, 48, 36], [43, 124, 50], [1, 8, 20], [71, 49], [66, 105, 17], [22, 1], []], ![[104, 103, 74, 132], [25, 103, 136, 104], [145, 101, 124, 150], [103, 45], [33, 106, 124, 114], [124, 64], [149, 58]], ![[50, 117, 40, 21], [70, 102, 130, 80], [114, 28, 88, 11], [56, 49], [35, 45, 129, 103], [111, 81], [140, 58]]]
 h' := ![![[98, 142, 71], [29, 62, 145], [99, 10, 72], [103, 131, 41], [41, 18, 144], [64, 6, 116], [0, 0, 1], [0, 1]], ![[75, 8, 80], [103, 150, 126], [19, 21, 78], [98, 23, 116], [138, 60, 14], [18, 150, 146], [44, 33, 8], [98, 142, 71]], ![[0, 1], [113, 90, 31], [73, 120, 1], [57, 148, 145], [141, 73, 144], [2, 146, 40], [6, 118, 142], [75, 8, 80]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [119, 4], []]
 b := ![[], [74, 141, 68], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [52, 66, 129, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![125330, 12684, -19026]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![830, 84, -126]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![42, -51, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![42, -51, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![42, 106, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![42, -51, 1], ![112, 21, -102], ![-5712, 1127, 21]]]
  hmulB := by decide  
  f := ![![![-41, 51, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-42, -106, 157]], ![![0, -1, 1], ![28, 69, -102], ![-42, -7, 21]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [49, 120, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 156], [0, 1]]
 g := ![![[121, 141], [118], [83, 39], [37, 19], [25, 148], [113], [1]], ![[0, 16], [118], [113, 118], [112, 138], [6, 9], [113], [1]]]
 h' := ![![[37, 156], [95, 112], [15, 78], [71, 143], [31, 126], [4, 84], [108, 37], [0, 1]], ![[0, 1], [0, 45], [75, 79], [24, 14], [140, 31], [129, 73], [64, 120], [37, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123]]
 b := ![[], [79, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [49, 120, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3759, 90, -11]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-21, 8, -11]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-55, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-55, 1, 0]] 
 ![![157, 0, 0], ![102, 1, 0], ![136, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-55, 1, 0], ![0, -55, 2], ![112, -21, -55]]]
  hmulB := by decide  
  f := ![![![1761, -32, 0], ![5024, 0, 0]], ![![1156, -21, 0], ![3298, 0, 0]], ![![1578, -1, -1], ![4502, 79, 0]]]
  g := ![![![1, 0, 0], ![-102, 157, 0], ![-136, 0, 157]], ![![-1, 1, 0], ![34, -55, 2], ![62, -21, -55]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![42, -51, 1]] ![![157, 0, 0], ![-55, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-8635, 157, 0]], ![![6594, -8007, 157], ![-2198, 2826, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-55, 1, 0]]], ![![![42, -51, 1]], ![![-14, 18, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-18, 15, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-18, 15, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![145, 15, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-18, 15, 1], ![112, -39, 30], ![1680, -259, -39]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-145, -15, 163]], ![![-1, 0, 1], ![-26, -3, 30], ![45, 2, -39]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [99, 19, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 162], [0, 1]]
 g := ![![[43, 135], [], [], [118], [115], [0, 35], [1]], ![[86, 28], [], [], [118], [115], [150, 128], [1]]]
 h' := ![![[144, 162], [0, 61], [77], [27], [25, 97], [0, 142], [64, 144], [0, 1]], ![[0, 1], [145, 102], [77], [27], [138, 66], [73, 21], [99, 19], [144, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [103, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [99, 19, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-553, 651, -250]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![219, 27, -250]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-30, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-30, 1, 0]] 
 ![![163, 0, 0], ![133, 1, 0], ![39, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-30, 1, 0], ![0, -30, 2], ![112, -21, -30]]]
  hmulB := by decide  
  f := ![![![4111, -137, 0], ![22331, 0, 0]], ![![3361, -112, 0], ![18257, 0, 0]], ![![1023, -19, -1], ![5557, 82, 0]]]
  g := ![![![1, 0, 0], ![-133, 163, 0], ![-39, 0, 163]], ![![-1, 1, 0], ![24, -30, 2], ![25, -21, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-18, 15, 1]] ![![163, 0, 0], ![-30, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-4890, 163, 0]], ![![-2934, 2445, 163], ![652, -489, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-30, 1, 0]]], ![![![-18, 15, 1]], ![![4, -3, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [164, 147, 125, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [69, 54, 13], [140, 112, 154], [0, 1]]
 g := ![![[23, 105, 4], [25, 59, 99], [136, 88, 157], [150, 132], [47, 38], [114, 42, 1], []], ![[12, 119, 133, 110], [11, 127, 25, 59], [86, 25, 162, 160], [123, 27], [20, 108], [45, 164, 35, 80], [152, 2]], ![[57, 136, 92, 6], [70, 35, 129, 126], [33, 10, 23, 18], [50, 19], [77, 44], [121, 44, 88, 1], [11, 2]]]
 h' := ![![[69, 54, 13], [75, 141, 165], [74, 54, 44], [57, 23, 149], [38, 138, 93], [8, 68, 120], [0, 0, 1], [0, 1]], ![[140, 112, 154], [38, 145, 106], [49, 67, 119], [89, 153, 120], [87, 136, 19], [148, 77, 129], [40, 144, 112], [69, 54, 13]], ![[0, 1], [88, 48, 63], [80, 46, 4], [82, 158, 65], [44, 60, 55], [100, 22, 85], [94, 23, 54], [140, 112, 154]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [18, 64], []]
 b := ![[], [25, 13, 85], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [164, 147, 125, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![28724, 2338, -3173]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![172, 14, -19]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![39, -3, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![39, -3, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![39, 170, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![39, -3, 1], ![112, 18, -6], ![-336, 119, 18]]]
  hmulB := by decide  
  f := ![![![-38, 3, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -170, 173]], ![![0, -1, 1], ![2, 6, -6], ![-6, -17, 18]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [99, 117, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 172], [0, 1]]
 g := ![![[127, 81], [21], [29, 9], [64, 144], [84], [5, 22], [1]], ![[165, 92], [21], [14, 164], [170, 29], [84], [26, 151], [1]]]
 h' := ![![[56, 172], [53, 9], [70, 114], [65, 3], [45, 161], [24, 118], [74, 56], [0, 1]], ![[0, 1], [38, 164], [53, 59], [60, 170], [65, 12], [58, 55], [96, 117], [56, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [99]]
 b := ![[], [171, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [99, 117, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4473, 1519, 820]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-159, -797, 820]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![6, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![6, 1, 0]] 
 ![![173, 0, 0], ![6, 1, 0], ![155, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![6, 1, 0], ![0, 6, 2], ![112, -21, 6]]]
  hmulB := by decide  
  f := ![![![163, 27, 0], ![-4671, 0, 0]], ![![-6, -1, 0], ![174, 0, 0]], ![![145, 21, -1], ![-4155, 87, 0]]]
  g := ![![![1, 0, 0], ![-6, 173, 0], ![-155, 0, 173]], ![![0, 1, 0], ![-2, 6, 2], ![-4, -21, 6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![39, -3, 1]] ![![173, 0, 0], ![6, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![1038, 173, 0]], ![![6747, -519, 173], ![346, 0, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![6, 1, 0]]], ![![![39, -3, 1]], ![![2, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [145, 135, 140, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 144, 94], [105, 34, 85], [0, 1]]
 g := ![![[156, 86, 147], [3, 32, 85], [68, 16], [109, 17], [12, 172, 146], [133, 39, 1], []], ![[79, 51, 59, 50], [22, 84, 139, 8], [14, 61], [170, 9], [60, 164, 122, 137], [19, 56, 164, 11], [72, 65]], ![[174, 168, 2, 146], [150, 8, 93, 29], [170, 95], [157, 121], [91, 163, 78, 31], [18, 82, 159, 126], [81, 65]]]
 h' := ![![[113, 144, 94], [102, 75, 133], [65, 102, 62], [120, 20, 4], [50, 172, 14], [47, 18, 135], [0, 0, 1], [0, 1]], ![[105, 34, 85], [72, 3, 116], [80, 9, 61], [61, 91, 47], [3, 60, 176], [24, 156, 17], [2, 153, 34], [113, 144, 94]], ![[0, 1], [106, 101, 109], [145, 68, 56], [56, 68, 128], [154, 126, 168], [144, 5, 27], [175, 26, 144], [105, 34, 85]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [96, 125], []]
 b := ![[], [78, 84, 12], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [145, 135, 140, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-113307, 26671, 1432]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-633, 149, 8]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-43, -1, -2]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-43, -1, -2]] 
 ![![181, 0, 0], ![0, 181, 0], ![112, 91, 1]] where
  M :=![![![-43, -1, -2], ![-224, -1, -2], ![-112, -91, -1]]]
  hmulB := by decide  
  f := ![![![1, -1, 0]], ![![0, 1, -2]], ![![0, 0, -1]]]
  g := ![![![1, 1, -2], ![0, 1, -2], ![0, 0, -1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [98, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [110, 180], [0, 1]]
 g := ![![[106, 122], [25], [8, 126], [29], [8, 100], [86, 154], [1]], ![[132, 59], [25], [112, 55], [29], [148, 81], [12, 27], [1]]]
 h' := ![![[110, 180], [64, 159], [121, 5], [34, 137], [121, 36], [79, 171], [83, 110], [0, 1]], ![[0, 1], [178, 22], [128, 176], [81, 44], [99, 145], [65, 10], [56, 71], [110, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [33, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [98, 71, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4236, 314, 266]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-188, -132, 266]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-1, 1, 0]] 
 ![![181, 0, 0], ![180, 1, 0], ![90, 0, 1]] where
  M :=![![![-1, 1, 0], ![0, -1, 2], ![112, -21, -1]]]
  hmulB := by decide  
  f := ![![![43, 1, 2]], ![![44, 1, 2]], ![![22, 1, 1]]]
  g := ![![![-1, 1, 0], ![0, -1, 2], ![22, -21, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-43, -1, -2]] ![![-1, 1, 0]]
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


lemma PB182I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 181 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 181 (by omega)

def PB182I3 : PrimesBelowBoundCertificateInterval O 137 181 182 where
  m := 9
  g := ![3, 1, 1, 2, 2, 1, 2, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181]
  hP := PB182I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · dsimp ; intro j
      fin_cases j
      exact NI139N0
      exact NI139N1
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
      exact NI157N1
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
      exact NI163N1
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
  β := ![I139N0, I139N1, I139N2, I157N1, I163N1, I173N1, I181N1]
  Il := ![[I139N0, I139N1, I139N2], [], [], [I157N1], [I163N1], [], [I173N1], [], [I181N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
