
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![39, 59, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![39, 59, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![39, 59, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![39, 59, 1], ![-8, -62, 178], ![3057, -2475, 57]]]
  hmulB := by decide  
  f := ![![![-38, -59, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-39, -59, 139]], ![![0, 0, 1], ![-50, -76, 178], ![6, -42, 57]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [127, 134, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 138], [0, 1]]
 g := ![![[12, 81], [108, 34], [80], [104, 38], [116], [25], [1]], ![[0, 58], [0, 105], [80], [16, 101], [116], [25], [1]]]
 h' := ![![[5, 138], [45, 130], [135, 112], [136, 48], [36, 49], [27, 106], [12, 5], [0, 1]], ![[0, 1], [0, 9], [0, 27], [98, 91], [3, 90], [1, 33], [37, 134], [5, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [118]]
 b := ![[], [61, 59]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [127, 134, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![694, 27, -777]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![223, 330, -777]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-39, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-39, 1, 0]] 
 ![![139, 0, 0], ![100, 1, 0], ![82, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-39, 1, 0], ![-1, -40, 3], ![51, -42, -38]]]
  hmulB := by decide  
  f := ![![![-5129, -205200, 15390], ![0, -713070, 0]], ![![-3689, -147600, 11070], ![1, -512910, 0]], ![![-2996, -121054, 9079], ![106, -420660, 0]]]
  g := ![![![1, 0, 0], ![-100, 139, 0], ![-82, 0, 139]], ![![-1, 1, 0], ![27, -40, 3], ![53, -42, -38]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![39, 59, 1]] ![![139, 0, 0], ![-39, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-5421, 139, 0]], ![![5421, 8201, 139], ![-1529, -2363, 139]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-39, 1, 0]]], ![![![39, 59, 1]], ![![-11, -17, 1]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![62, 35, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![62, 35, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![62, 35, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![62, 35, 1], ![16, -15, 106], ![1833, -1467, 56]]]
  hmulB := by decide  
  f := ![![![-61, -35, -1], ![149, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-62, -35, 149]], ![![0, 0, 1], ![-44, -25, 106], ![-11, -23, 56]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [24, 141, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 148], [0, 1]]
 g := ![![[99, 118], [103], [91, 130], [5], [42, 143], [64], [1]], ![[0, 31], [103], [88, 19], [5], [143, 6], [64], [1]]]
 h' := ![![[8, 148], [129, 77], [51, 111], [62, 32], [35, 68], [83, 128], [125, 8], [0, 1]], ![[0, 1], [0, 72], [45, 38], [20, 117], [132, 81], [64, 21], [40, 141], [8, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [56]]
 b := ![[], [37, 28]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [24, 141, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1423, 2852, -1549]
  a := ![-3, -5, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![635, 383, -1549]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![43, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![43, 1, 0]] 
 ![![149, 0, 0], ![43, 1, 0], ![93, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![43, 1, 0], ![-1, 42, 3], ![51, -42, 44]]]
  hmulB := by decide  
  f := ![![![-3379, 141960, 10140], ![0, -503620, 0]], ![![-975, 40950, 2925], ![1, -145275, 0]], ![![-2148, 88605, 6329], ![135, -314340, 0]]]
  g := ![![![1, 0, 0], ![-43, 149, 0], ![-93, 0, 149]], ![![0, 1, 0], ![-14, 42, 3], ![-15, -42, 44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![62, 35, 1]] ![![149, 0, 0], ![43, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![6407, 149, 0]], ![![9238, 5215, 149], ![2682, 1490, 149]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![43, 1, 0]]], ![![![62, 35, 1]], ![![18, 10, 1]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0)
instance hp151 : Fact (Nat.Prime 151) := {out := by norm_num}

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-66, 1, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-66, 1, 0]] 
 ![![151, 0, 0], ![85, 1, 0], ![86, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-66, 1, 0], ![-1, -67, 3], ![51, -42, -65]]]
  hmulB := by decide  
  f := ![![![1299, 82543, -3696], ![151, 186032, 0]], ![![760, 46430, -2079], ![152, 104643, 0]], ![![756, 47011, -2105], ![123, 105952, 0]]]
  g := ![![![1, 0, 0], ![-85, 151, 0], ![-86, 0, 151]], ![![-1, 1, 0], ![36, -67, 3], ![61, -42, -65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N0 : Nat.card (O ⧸ I151N0) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N0)

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := prime_ideal_of_norm_prime hp151.out _ NI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-49, 1, 0]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-49, 1, 0]] 
 ![![151, 0, 0], ![102, 1, 0], ![89, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-49, 1, 0], ![-1, -50, 3], ![51, -42, -48]]]
  hmulB := by decide  
  f := ![![![-6725, -336300, 20178], ![0, -1015626, 0]], ![![-4542, -227150, 13629], ![1, -685993, 0]], ![![-3942, -198217, 11893], ![67, -598614, 0]]]
  g := ![![![1, 0, 0], ![-102, 151, 0], ![-89, 0, 151]], ![![-1, 1, 0], ![32, -50, 3], ![57, -42, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1

def I151N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0], ![-36, 1, 0]] i)))

def SI151N2: IdealEqSpanCertificate' Table ![![151, 0, 0], ![-36, 1, 0]] 
 ![![151, 0, 0], ![115, 1, 0], ![59, 0, 1]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]], ![![-36, 1, 0], ![-1, -37, 3], ![51, -42, -35]]]
  hmulB := by decide  
  f := ![![![-1689, -62530, 5070], ![0, -255190, 0]], ![![-1286, -47619, 3861], ![1, -194337, 0]], ![![-633, -24433, 1981], ![113, -99710, 0]]]
  g := ![![![1, 0, 0], ![-115, 151, 0], ![-59, 0, 151]], ![![-1, 1, 0], ![27, -37, 3], ![46, -42, -35]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N2 : Nat.card (O ⧸ I151N2) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N2)

lemma isPrimeI151N2 : Ideal.IsPrime I151N2 := prime_ideal_of_norm_prime hp151.out _ NI151N2
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![-66, 1, 0]] ![![151, 0, 0], ![-49, 1, 0]]
  ![![151, 0, 0], ![71, 62, 1]] where
 M := ![![![22801, 0, 0], ![-7399, 151, 0]], ![![-9966, 151, 0], ![3233, -116, 3]]]
 hmul := by decide  
 g := ![![![![80, -62, -1], ![151, 0, 0]], ![![-49, 1, 0], ![0, 0, 0]]], ![![![-66, 1, 0], ![0, 0, 0]], ![![-51, -64, -1], ![154, 0, 0]]]]
 hle2 := by decide  

def MulI151N1 : IdealMulLeCertificate' Table 
  ![![151, 0, 0], ![71, 62, 1]] ![![151, 0, 0], ![-36, 1, 0]]
  ![![151, 0, 0]] where
 M := ![![![22801, 0, 0], ![-5436, 151, 0]], ![![10721, 9362, 151], ![-2567, -2265, 151]]]
 hmul := by decide  
 g := ![![![![151, 0, 0]], ![![-36, 1, 0]]], ![![![71, 62, 1]], ![![-17, -15, 1]]]]
 hle2 := by decide  


def PBC151 : ContainsPrimesAboveP 151 ![I151N0, I151N1, I151N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI151N0
    exact isPrimeI151N1
    exact isPrimeI151N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 151 (by decide) (𝕀 ⊙ MulI151N0 ⊙ MulI151N1)
instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![83, -78, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![83, -78, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![83, 79, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![83, -78, 1], ![129, 119, -233], ![-3930, 3279, -36]]]
  hmulB := by decide  
  f := ![![![-82, 78, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-83, -79, 157]], ![![0, -1, 1], ![124, 118, -233], ![-6, 39, -36]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [37, 151, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 156], [0, 1]]
 g := ![![[55, 17], [144], [58, 35], [108, 156], [29, 17], [36], [1]], ![[0, 140], [144], [111, 122], [102, 1], [131, 140], [36], [1]]]
 h' := ![![[6, 156], [45, 71], [52, 12], [86, 105], [26, 129], [37, 86], [120, 6], [0, 1]], ![[0, 1], [0, 86], [124, 145], [88, 52], [15, 28], [82, 71], [156, 151], [6, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [129]]
 b := ![[], [42, 143]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [37, 151, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![201989, 25025, -194556]
  a := ![1, 2, -67]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![104141, 98057, -194556]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![76, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![76, 1, 0]] 
 ![![157, 0, 0], ![76, 1, 0], ![36, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![76, 1, 0], ![-1, 75, 3], ![51, -42, 77]]]
  hmulB := by decide  
  f := ![![![-1239, 93000, 3720], ![0, -194680, 0]], ![![-600, 45000, 1800], ![1, -94200, 0]], ![![-348, 21324, 853], ![132, -44640, 0]]]
  g := ![![![1, 0, 0], ![-76, 157, 0], ![-36, 0, 157]], ![![0, 1, 0], ![-37, 75, 3], ![3, -42, 77]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![83, -78, 1]] ![![157, 0, 0], ![76, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![11932, 157, 0]], ![![13031, -12246, 157], ![6437, -5809, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![76, 1, 0]]], ![![![83, -78, 1]], ![![41, -37, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![56, -28, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![56, -28, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![56, 135, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![56, -28, 1], ![79, 42, -83], ![-1380, 1179, -13]]]
  hmulB := by decide  
  f := ![![![-55, 28, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -135, 163]], ![![0, -1, 1], ![29, 69, -83], ![-4, 18, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [63, 80, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [83, 162], [0, 1]]
 g := ![![[97, 51], [11, 84], [131], [51], [77], [120, 43], [1]], ![[92, 112], [137, 79], [131], [51], [77], [103, 120], [1]]]
 h' := ![![[83, 162], [122, 122], [10, 35], [73, 91], [134, 122], [101, 136], [100, 83], [0, 1]], ![[0, 1], [142, 41], [144, 128], [128, 72], [154, 41], [142, 27], [143, 80], [83, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [156]]
 b := ![[], [23, 78]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [63, 80, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![104, 3208, -3328]
  a := ![3, 4, -8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1144, 2776, -3328]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-80, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-80, 1, 0]] 
 ![![163, 0, 0], ![83, 1, 0], ![13, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-80, 1, 0], ![-1, -81, 3], ![51, -42, -79]]]
  hmulB := by decide  
  f := ![![![3876, 307394, -11385], ![163, 618585, 0]], ![![2013, 156491, -5796], ![164, 314916, 0]], ![![316, 24516, -908], ![27, 49335, 0]]]
  g := ![![![1, 0, 0], ![-83, 163, 0], ![-13, 0, 163]], ![![-1, 1, 0], ![41, -81, 3], ![28, -42, -79]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![56, -28, 1]] ![![163, 0, 0], ![-80, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-13040, 163, 0]], ![![9128, -4564, 163], ![-4401, 2282, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-80, 1, 0]]], ![![![56, -28, 1]], ![![-27, 14, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-500, 259, 153]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-500, 259, 153]] 
 ![![167, 0, 0], ![0, 167, 0], ![155, 65, 1]] where
  M :=![![![-500, 259, 153], ![7544, -7185, 930], ![20553, -10419, -6514]]]
  hmulB := by decide  
  f := ![![![-338280, -557, -8025]], ![![-408718, -673, -9696]], ![![-475531, -783, -11281]]]
  g := ![![![-145, -58, 153], ![-818, -405, 930], ![6169, 2473, -6514]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [34, 47, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 166], [0, 1]]
 g := ![![[134, 130], [88, 6], [22, 27], [2], [93], [74, 38], [1]], ![[36, 37], [140, 161], [89, 140], [2], [93], [125, 129], [1]]]
 h' := ![![[120, 166], [14, 56], [87, 29], [155, 148], [132, 154], [156, 60], [133, 120], [0, 1]], ![[0, 1], [54, 111], [60, 138], [46, 19], [75, 13], [8, 107], [4, 47], [120, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [150]]
 b := ![[], [9, 75]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [34, 47, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![514, 27, -516]
  a := ![1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![482, 201, -516]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![338280, 557, 8025]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![338280, 557, 8025]] 
 ![![167, 0, 0], ![138, 1, 0], ![155, 0, 1]] where
  M :=![![![338280, 557, 8025], ![408718, 673, 9696], ![413607, 681, 9812]]]
  hmulB := by decide  
  f := ![![![500, -259, -153]], ![![368, -171, -132]], ![![341, -178, -103]]]
  g := ![![![-5883, 557, 8025], ![-7108, 673, 9696], ![-7193, 681, 9812]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-500, 259, 153]] ![![338280, 557, 8025]]
  ![![167, 0, 0]] where
 M := ![![![-167, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0]] 
 ![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [56, 42, 162, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [119, 130, 125], [65, 42, 48], [0, 1]]
 g := ![![[106, 95, 117], [148, 95], [53, 121, 10], [127, 143, 4], [33, 25], [79, 11, 1], []], ![[5, 170, 118, 111], [64, 56], [72, 131, 94, 66], [167, 54, 138, 69], [48, 133], [100, 156, 68, 98], [62, 55]], ![[97, 106, 155, 108], [57, 152], [9, 33, 42, 166], [118, 54, 142, 80], [122, 34], [71, 94, 62, 3], [139, 55]]]
 h' := ![![[119, 130, 125], [53, 88, 64], [146, 9, 152], [154, 4, 23], [168, 68, 2], [74, 45, 5], [0, 0, 1], [0, 1]], ![[65, 42, 48], [26, 67, 21], [91, 1, 70], [125, 128, 82], [55, 13, 107], [54, 131, 126], [136, 171, 42], [119, 130, 125]], ![[0, 1], [129, 18, 88], [42, 163, 124], [40, 41, 68], [65, 92, 64], [82, 170, 42], [74, 2, 130], [65, 42, 48]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [87, 60], []]
 b := ![[], [87, 59, 131], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [56, 42, 162, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![572803, -36330, -330776]
  a := ![-1, 18, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3311, -210, -1912]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-29, 74, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-29, 74, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![150, 74, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-29, 74, 1], ![-23, -145, 223], ![3822, -3105, 4]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-150, -74, 179]], ![![-1, 0, 1], ![-187, -93, 223], ![18, -19, 4]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [19, 5, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 178], [0, 1]]
 g := ![![[151, 66], [152, 129], [88], [15], [79, 117], [65, 25], [1]], ![[0, 113], [44, 50], [88], [15], [31, 62], [119, 154], [1]]]
 h' := ![![[174, 178], [155, 31], [119, 147], [1, 25], [110, 33], [18, 98], [160, 174], [0, 1]], ![[0, 1], [0, 148], [100, 32], [55, 154], [124, 146], [65, 81], [6, 5], [174, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [151]]
 b := ![[], [144, 165]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [19, 5, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-855, 1404, -668]
  a := ![1, 4, -4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![555, 284, -668]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-44, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-44, 1, 0]] 
 ![![179, 0, 0], ![135, 1, 0], ![175, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-44, 1, 0], ![-1, -45, 3], ![51, -42, -43]]]
  hmulB := by decide  
  f := ![![![-3415, -153720, 10248], ![0, -611464, 0]], ![![-2575, -115920, 7728], ![1, -461104, 0]], ![![-3335, -150285, 10019], ![15, -597800, 0]]]
  g := ![![![1, 0, 0], ![-135, 179, 0], ![-175, 0, 179]], ![![-1, 1, 0], ![31, -45, 3], ![74, -42, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![-29, 74, 1]] ![![179, 0, 0], ![-44, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-7876, 179, 0]], ![![-5191, 13246, 179], ![1253, -3401, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-44, 1, 0]]], ![![![-29, 74, 1]], ![![7, -19, 1]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [20, 80, 142, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [109, 92, 82], [111, 88, 99], [0, 1]]
 g := ![![[76, 165, 99], [64, 101], [41, 178, 56], [73, 45], [92, 82, 133], [174, 39, 1], []], ![[126, 65, 126, 137], [147, 142], [66, 161, 97, 82], [72, 56], [6, 81, 49, 59], [103, 62, 88, 60], [32, 27]], ![[133, 180, 43, 178], [92, 5], [82, 62, 59, 48], [31, 55], [19, 78, 81, 38], [72, 45, 2, 87], [15, 27]]]
 h' := ![![[109, 92, 82], [153, 123, 113], [85, 146, 120], [164, 172, 31], [151, 102, 100], [140, 142, 26], [0, 0, 1], [0, 1]], ![[111, 88, 99], [141, 56, 120], [179, 137, 88], [134, 89, 180], [137, 145, 150], [3, 153, 176], [19, 123, 88], [109, 92, 82]], ![[0, 1], [18, 2, 129], [132, 79, 154], [42, 101, 151], [149, 115, 112], [114, 67, 160], [75, 58, 92], [111, 88, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 94], []]
 b := ![[], [3, 140, 43], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [20, 80, 142, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12308, -160004, 170502]
  a := ![-2, -1, 6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-68, -884, 942]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [96, 137, 158, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 21, 49], [131, 169, 142], [0, 1]]
 g := ![![[5, 32, 100], [65, 90, 40], [133, 97, 90], [124, 85, 177], [31, 29, 43], [188, 33, 1], []], ![[45, 46, 95, 2], [76, 130, 112, 77], [56, 21, 100, 102], [132, 85, 120, 5], [84, 4, 94, 27], [165, 25, 77, 32], [116, 109]], ![[126, 148, 173, 22], [174, 58, 131, 151], [136, 55, 120, 164], [98, 85, 96, 71], [82, 48, 82, 87], [64, 48, 172, 165], [23, 109]]]
 h' := ![![[93, 21, 49], [63, 104, 10], [29, 186, 123], [129, 161, 102], [80, 86, 122], [97, 108, 59], [0, 0, 1], [0, 1]], ![[131, 169, 142], [145, 8, 101], [27, 23, 105], [178, 133, 106], [141, 127, 2], [164, 11, 174], [187, 88, 169], [93, 21, 49]], ![[0, 1], [103, 79, 80], [27, 173, 154], [90, 88, 174], [102, 169, 67], [109, 72, 149], [55, 103, 21], [131, 169, 142]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [53, 61], []]
 b := ![[], [163, 95, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [96, 137, 158, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![416571, 42975, -379135]
  a := ![0, 0, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2181, 225, -1985]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def PBC191 : ContainsPrimesAboveP 191 ![I191N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![191, 0, 0]]) timesTableT_eq_Table B_one_repr 191 (by decide) 𝕀

instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![90, 96, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![90, 96, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![90, 96, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![90, 96, 1], ![-45, -48, 289], ![4944, -4029, 145]]]
  hmulB := by decide  
  f := ![![![-89, -96, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-90, -96, 193]], ![![0, 0, 1], ![-135, -144, 289], ![-42, -93, 145]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [151, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [96, 192], [0, 1]]
 g := ![![[85, 170], [28], [101], [63], [137], [36], [96, 1]], ![[0, 23], [28], [101], [63], [137], [36], [192, 192]]]
 h' := ![![[96, 192], [77, 154], [32, 75], [6, 115], [107, 177], [23, 41], [172, 187], [0, 1]], ![[0, 1], [0, 39], [91, 118], [45, 78], [115, 16], [99, 152], [175, 6], [96, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45]]
 b := ![[], [78, 119]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [151, 97, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6903, 6996, -1640]
  a := ![-2, -12, 8]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![729, 852, -1640]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-96, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-96, 1, 0]] 
 ![![193, 0, 0], ![97, 1, 0], ![48, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-96, 1, 0], ![-1, -97, 3], ![51, -42, -95]]]
  hmulB := by decide  
  f := ![![![353, 24831, -768], ![193, 49408, 0]], ![![129, 12416, -384], ![1, 24704, 0]], ![![144, 6175, -191], ![161, 12288, 0]]]
  g := ![![![1, 0, 0], ![-97, 193, 0], ![-48, 0, 193]], ![![-1, 1, 0], ![48, -97, 3], ![45, -42, -95]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![90, 96, 1]] ![![193, 0, 0], ![-96, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-18528, 193, 0]], ![![17370, 18528, 193], ![-8685, -9264, 193]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-96, 1, 0]]], ![![![90, 96, 1]], ![![-45, -48, 1]]]]
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


lemma PB278I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB278I3 : PrimesBelowBoundCertificateInterval O 137 193 278 where
  m := 11
  g := ![2, 2, 3, 2, 2, 2, 1, 2, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB278I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1, I151N2]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![151, 151, 151]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![5177717]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![6967871]
    · exact ![37249, 193]
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
      exact NI149N1
    · dsimp ; intro j
      fin_cases j
      exact NI151N0
      exact NI151N1
      exact NI151N2
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
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
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
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N1, I151N0, I151N1, I151N2, I157N1, I163N1, I167N1, I179N1, I193N1]
  Il := ![[I139N1], [I149N1], [I151N0, I151N1, I151N2], [I157N1], [I163N1], [I167N1], [], [I179N1], [], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
