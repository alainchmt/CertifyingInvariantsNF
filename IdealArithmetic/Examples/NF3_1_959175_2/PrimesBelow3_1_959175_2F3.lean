
import IdealArithmetic.Examples.NF3_1_959175_2.RI3_1_959175_2
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![13, 1, 0]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![13, 1, 0]] 
 ![![139, 0, 0], ![13, 1, 0], ![10, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![13, 1, 0], ![-5, 11, 13], ![185, -8, 15]]]
  hmulB := by decide  
  f := ![![![7426, -16483, -19474], ![695, 208222, 0]], ![![687, -1541, -1820], ![140, 19460, 0]], ![![532, -1186, -1401], ![74, 14980, 0]]]
  g := ![![![1, 0, 0], ![-13, 139, 0], ![-10, 0, 139]], ![![0, 1, 0], ![-2, 11, 13], ![1, -8, 15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![54, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![54, 1, 0]] 
 ![![139, 0, 0], ![54, 1, 0], ![83, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![54, 1, 0], ![-5, 52, 13], ![185, -8, 56]]]
  hmulB := by decide  
  f := ![![![5900, -69226, -17303], ![1946, 185009, 0]], ![![2261, -26890, -6721], ![835, 71863, 0]], ![![3544, -41336, -10332], ![1108, 110473, 0]]]
  g := ![![![1, 0, 0], ![-54, 139, 0], ![-83, 0, 139]], ![![0, 1, 0], ![-28, 52, 13], ![-29, -8, 56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1

def I139N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-49, -2, -3]] i)))

def SI139N2: IdealEqSpanCertificate' Table ![![-49, -2, -3]] 
 ![![139, 0, 0], ![72, 1, 0], ![61, 0, 1]] where
  M :=![![![-49, -2, -3], ![-545, -21, -32], ![-550, -23, -32]]]
  hmulB := by decide  
  f := ![![![64, -5, -1]], ![![32, -2, -1]], ![![21, -2, 0]]]
  g := ![![![2, -2, -3], ![21, -21, -32], ![22, -23, -32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N2 : Nat.card (O ⧸ I139N2) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N2)

lemma isPrimeI139N2 : Ideal.IsPrime I139N2 := prime_ideal_of_norm_prime hp139.out _ NI139N2
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![13, 1, 0]] ![![139, 0, 0], ![54, 1, 0]]
  ![![64, -5, -1]] where
 M := ![![![19321, 0, 0], ![7506, 139, 0]], ![![1807, 139, 0], ![697, 65, 13]]]
 hmul := by decide  
 g := ![![![![-6811, -278, -417]], ![![-3191, -129, -194]]], ![![![-1182, -47, -71]], ![![-552, -22, -33]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![64, -5, -1]] ![![-49, -2, -3]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-29, 39, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-29, 39, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![120, 39, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-29, 39, 1], ![-10, -115, 509], ![7275, -299, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-120, -39, 149]], ![![-1, 0, 1], ![-410, -134, 509], ![15, -13, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [7, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 148], [0, 1]]
 g := ![![[8, 64], [85], [], [], [13, 45], [7], [1]], ![[0, 85], [85], [], [], [26, 104], [7], [1]]]
 h' := ![![[93, 148], [1, 8], [0, 95], [86], [58], [0, 94], [142, 93], [0, 1]], ![[0, 1], [0, 141], [44, 54], [86], [58], [100, 55], [0, 56], [93, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135]]
 b := ![[], [102, 142]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [7, 56, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5637, 2469, -2080]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1713, 561, -2080]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-62, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-62, 1, 0]] 
 ![![149, 0, 0], ![87, 1, 0], ![107, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-62, 1, 0], ![-5, -64, 13], ![185, -8, -60]]]
  hmulB := by decide  
  f := ![![![5977, 86028, -17472], ![-1788, 200256, 0]], ![![3487, 50183, -10192], ![-1042, 116816, 0]], ![![4323, 61778, -12547], ![-1210, 143808, 0]]]
  g := ![![![1, 0, 0], ![-87, 149, 0], ![-107, 0, 149]], ![![-1, 1, 0], ![28, -64, 13], ![49, -8, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-29, 39, 1]] ![![149, 0, 0], ![-62, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-9238, 149, 0]], ![![-4321, 5811, 149], ![1788, -2533, 447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-62, 1, 0]]], ![![![-29, 39, 1]], ![![12, -17, 3]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![151, 0, 0]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![151, 0, 0]] 
 ![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]] where
  M :=![![![151, 0, 0], ![0, 151, 0], ![0, 0, 151]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [78, 58, 48, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 65, 83], [19, 85, 68], [0, 1]]
 g := ![![[57, 75, 98], [106, 40, 47], [82, 109, 136], [147, 25], [57, 40, 59], [103, 1], []], ![[29, 28, 132, 75], [67, 126, 66, 114], [26, 21, 132, 102], [95, 10], [46, 52, 65, 24], [129, 128], [87, 94]], ![[124, 83, 83, 22], [71, 75, 60, 39], [84, 116, 42, 88], [9, 118], [100, 69, 149, 55], [28, 148], [102, 94]]]
 h' := ![![[84, 65, 83], [37, 141, 131], [97, 85, 97], [120, 54, 102], [84, 122, 146], [120, 139, 132], [0, 0, 1], [0, 1]], ![[19, 85, 68], [139, 122, 37], [56, 150, 49], [33, 56, 15], [73, 120, 37], [22, 44, 107], [119, 52, 85], [84, 65, 83]], ![[0, 1], [143, 39, 134], [65, 67, 5], [29, 41, 34], [60, 60, 119], [143, 119, 63], [106, 99, 65], [19, 85, 68]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11, 30], []]
 b := ![[], [139, 42, 147], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [78, 58, 48, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![87351386, -6551437, 334012]
  a := ![-12, -7, 31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![578486, -43387, 2212]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![43, -4, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![43, -4, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![43, 153, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![43, -4, 1], ![205, 43, -50], ![-680, 45, 28]]]
  hmulB := by decide  
  f := ![![![-42, 4, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -153, 157]], ![![0, -1, 1], ![15, 49, -50], ![-12, -27, 28]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [9, 57, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 156], [0, 1]]
 g := ![![[111, 35], [118], [3, 145], [152, 58], [113, 36], [109], [1]], ![[0, 122], [118], [59, 12], [143, 99], [102, 121], [109], [1]]]
 h' := ![![[100, 156], [138, 52], [130, 78], [45, 50], [82, 23], [42, 151], [148, 100], [0, 1]], ![[0, 1], [0, 105], [80, 79], [21, 107], [27, 134], [70, 6], [100, 57], [100, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15]]
 b := ![[], [96, 86]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [9, 57, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3550352, 4167164, -2248493]
  a := ![197, 67, -525]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![638443, 2217749, -2248493]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![50, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![50, 1, 0]] 
 ![![157, 0, 0], ![50, 1, 0], ![129, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![50, 1, 0], ![-5, 48, 13], ![185, -8, 52]]]
  hmulB := by decide  
  f := ![![![15861, -164762, -44616], ![4082, 538824, 0]], ![![5010, -52425, -14196], ![1414, 171444, 0]], ![![13017, -135378, -36659], ![3402, 442728, 0]]]
  g := ![![![1, 0, 0], ![-50, 157, 0], ![-129, 0, 157]], ![![0, 1, 0], ![-26, 48, 13], ![-39, -8, 52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![43, -4, 1]] ![![157, 0, 0], ![50, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![7850, 157, 0]], ![![6751, -628, 157], ![2355, -157, 0]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![50, 1, 0]]], ![![![43, -4, 1]], ![![15, -1, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-7, -8, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-7, -8, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![156, 155, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-7, -8, 1], ![225, 1, -102], ![-1420, 77, -30]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-156, -155, 163]], ![![-1, -1, 1], ![99, 97, -102], ![20, 29, -30]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [52, 155, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 162], [0, 1]]
 g := ![![[50, 39], [120, 161], [51], [83], [71], [6, 64], [1]], ![[36, 124], [104, 2], [51], [83], [71], [29, 99], [1]]]
 h' := ![![[8, 162], [117, 56], [40, 18], [35, 41], [90, 88], [14, 76], [111, 8], [0, 1]], ![[0, 1], [76, 107], [21, 145], [37, 122], [142, 75], [133, 87], [12, 155], [8, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [9, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [52, 155, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9284, 16471, -12552]
  a := ![12, 6, -31]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![11956, 12037, -12552]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-61, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-61, 1, 0]] 
 ![![163, 0, 0], ![102, 1, 0], ![30, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-61, 1, 0], ![-5, -63, 13], ![185, -8, -59]]]
  hmulB := by decide  
  f := ![![![2877, 39316, -8112], ![-652, 101712, 0]], ![![1768, 24573, -5070], ![-488, 63570, 0]], ![![534, 7236, -1493], ![-108, 18720, 0]]]
  g := ![![![1, 0, 0], ![-102, 163, 0], ![-30, 0, 163]], ![![-1, 1, 0], ![37, -63, 13], ![17, -8, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![-7, -8, 1]] ![![163, 0, 0], ![-61, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-9943, 163, 0]], ![![-1141, -1304, 163], ![652, 489, -163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-61, 1, 0]]], ![![![-7, -8, 1]], ![![4, 3, -1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-13, -41, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-13, -41, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![154, 126, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-13, -41, 1], ![390, 61, -531], ![-7525, 341, -102]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-154, -126, 167]], ![![-1, -1, 1], ![492, 401, -531], ![49, 79, -102]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [102, 89, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 166], [0, 1]]
 g := ![![[68, 147], [53, 2], [97, 3], [25], [85], [58, 72], [1]], ![[11, 20], [42, 165], [164, 164], [25], [85], [163, 95], [1]]]
 h' := ![![[78, 166], [105, 100], [126, 154], [143, 62], [45, 5], [96, 69], [65, 78], [0, 1]], ![[0, 1], [56, 67], [114, 13], [136, 105], [101, 162], [134, 98], [137, 89], [78, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [2]]
 b := ![[], [128, 1]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [102, 89, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5897, 2502, -2509]
  a := ![5, 1, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2349, 1908, -2509]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![30, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![30, 1, 0]] 
 ![![167, 0, 0], ![30, 1, 0], ![102, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![30, 1, 0], ![-5, 28, 13], ![185, -8, 32]]]
  hmulB := by decide  
  f := ![![![31141, -179116, -83148], ![4676, 1068132, 0]], ![![5590, -32149, -14924], ![836, 191716, 0]], ![![19026, -109400, -50785], ![2824, 652392, 0]]]
  g := ![![![1, 0, 0], ![-30, 167, 0], ![-102, 0, 167]], ![![0, 1, 0], ![-13, 28, 13], ![-17, -8, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![-13, -41, 1]] ![![167, 0, 0], ![30, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![5010, 167, 0]], ![![-2171, -6847, 167], ![0, -1169, -501]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![30, 1, 0]]], ![![![-13, -41, 1]], ![![0, -7, -3]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![45, 72, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![45, 72, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![45, 72, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![45, 72, 1], ![-175, -107, 938], ![13380, -563, 182]]]
  hmulB := by decide  
  f := ![![![-44, -72, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-45, -72, 173]], ![![0, 0, 1], ![-245, -391, 938], ![30, -79, 182]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [171, 131, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 172], [0, 1]]
 g := ![![[21, 152], [15], [60, 139], [107, 169], [54], [39, 34], [1]], ![[4, 21], [15], [16, 34], [112, 4], [54], [83, 139], [1]]]
 h' := ![![[42, 172], [71, 49], [120, 154], [41, 73], [137, 13], [78, 153], [2, 42], [0, 1]], ![[0, 1], [53, 124], [14, 19], [166, 100], [164, 160], [103, 20], [36, 131], [42, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [1, 140]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [171, 131, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![148687, 1685, 4000]
  a := ![-8, 16, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-181, -1655, 4000]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-73, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-73, 1, 0]] 
 ![![173, 0, 0], ![100, 1, 0], ![164, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-73, 1, 0], ![-5, -75, 13], ![185, -8, -71]]]
  hmulB := by decide  
  f := ![![![54213, 923876, -160121], ![-17473, 2130841, 0]], ![![31362, 533983, -92547], ![-10033, 1231587, 0]], ![![51399, 875813, -151791], ![-16549, 2019988, 0]]]
  g := ![![![1, 0, 0], ![-100, 173, 0], ![-164, 0, 173]], ![![-1, 1, 0], ![31, -75, 13], ![73, -8, -71]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![45, 72, 1]] ![![173, 0, 0], ![-73, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-12629, 173, 0]], ![![7785, 12456, 173], ![-3460, -5363, 865]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-73, 1, 0]]], ![![![45, 72, 1]], ![![-20, -31, 5]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![88, -50, 1]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![88, -50, 1]] 
 ![![179, 0, 0], ![0, 179, 0], ![88, 129, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![88, -50, 1], ![435, 180, -648], ![-9190, 413, -19]]]
  hmulB := by decide  
  f := ![![![-87, 50, -1], ![179, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-88, -129, 179]], ![![0, -1, 1], ![321, 468, -648], ![-42, 16, -19]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [45, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [61, 178], [0, 1]]
 g := ![![[114, 4], [130, 171], [110], [12], [66, 49], [68, 141], [1]], ![[0, 175], [0, 8], [110], [12], [12, 130], [77, 38], [1]]]
 h' := ![![[61, 178], [57, 2], [29, 23], [135, 17], [73, 141], [162, 7], [134, 61], [0, 1]], ![[0, 1], [0, 177], [0, 156], [98, 162], [82, 38], [52, 172], [96, 118], [61, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [104, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [45, 118, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-19287, 8481, -5937]
  a := ![8, 6, -21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2811, 4326, -5937]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-68, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-68, 1, 0]] 
 ![![179, 0, 0], ![111, 1, 0], ![19, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-68, 1, 0], ![-5, -70, 13], ![185, -8, -66]]]
  hmulB := by decide  
  f := ![![![40081, 623065, -115700], ![-11635, 1593100, 0]], ![![24871, 386300, -71734], ![-7159, 987722, 0]], ![![4281, 66135, -12281], ![-1165, 169100, 0]]]
  g := ![![![1, 0, 0], ![-111, 179, 0], ![-19, 0, 179]], ![![-1, 1, 0], ![42, -70, 13], ![13, -8, -66]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![88, -50, 1]] ![![179, 0, 0], ![-68, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-12172, 179, 0]], ![![15752, -8950, 179], ![-5549, 3580, -716]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-68, 1, 0]]], ![![![88, -50, 1]], ![![-31, 20, -4]]]]
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


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [161, 31, 58, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [56, 60, 148], [67, 120, 33], [0, 1]]
 g := ![![[39, 21, 129], [171, 156], [4, 118, 148], [53, 101], [83, 127, 4], [75, 123, 1], []], ![[20, 28, 13, 34], [97, 52], [162, 107, 132, 60], [55, 165], [25, 138, 161, 1], [34, 51, 27, 106], [29, 3]], ![[156, 90, 84, 111], [73, 34], [91, 112, 175, 80], [33, 126], [61, 108, 146, 145], [34, 103, 9, 64], [144, 3]]]
 h' := ![![[56, 60, 148], [46, 19, 126], [80, 59, 95], [30, 2, 94], [31, 137, 120], [52, 135, 2], [0, 0, 1], [0, 1]], ![[67, 120, 33], [174, 46, 13], [15, 49, 41], [116, 160, 173], [37, 76, 105], [21, 133, 129], [96, 89, 120], [56, 60, 148]], ![[0, 1], [16, 116, 42], [179, 73, 45], [163, 19, 95], [74, 149, 137], [124, 94, 50], [129, 92, 60], [67, 120, 33]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120, 6], []]
 b := ![[], [156, 17, 66], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [161, 31, 58, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![43716206, -3559184, 1200030]
  a := ![-10, -3, 26]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![241526, -19664, 6630]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![19, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![19, 1, 0]] 
 ![![191, 0, 0], ![19, 1, 0], ![107, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![19, 1, 0], ![-5, 17, 13], ![185, -8, 21]]]
  hmulB := by decide  
  f := ![![![98734, -338513, -258830], ![8213, 3802810, 0]], ![![9805, -33665, -25740], ![956, 378180, 0]], ![![55315, -189638, -144999], ![4568, 2130370, 0]]]
  g := ![![![1, 0, 0], ![-19, 191, 0], ![-107, 0, 191]], ![![0, 1, 0], ![-9, 17, 13], ![-10, -8, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-12, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-12, 1, 0]] 
 ![![191, 0, 0], ![179, 1, 0], ![163, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-12, 1, 0], ![-5, -14, 13], ![185, -8, -10]]]
  hmulB := by decide  
  f := ![![![54970, 154363, -143325], ![-2483, 2105775, 0]], ![![51517, 144660, -134316], ![-2291, 1973412, 0]], ![![46910, 131734, -122314], ![-2144, 1797075, 0]]]
  g := ![![![1, 0, 0], ![-179, 191, 0], ![-163, 0, 191]], ![![-1, 1, 0], ![2, -14, 13], ![17, -8, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-7, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-7, 1, 0]] 
 ![![191, 0, 0], ![184, 1, 0], ![127, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-7, 1, 0], ![-5, -9, 13], ![185, -8, -5]]]
  hmulB := by decide  
  f := ![![![16882, 30413, -43927], ![-382, 645389, 0]], ![![16262, 29297, -42315], ![-381, 621705, 0]], ![![11227, 20222, -29208], ![-205, 429133, 0]]]
  g := ![![![1, 0, 0], ![-184, 191, 0], ![-127, 0, 191]], ![![-1, 1, 0], ![0, -9, 13], ![12, -8, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![19, 1, 0]] ![![191, 0, 0], ![-12, 1, 0]]
  ![![191, 0, 0], ![-62, -29, 1]] where
 M := ![![![36481, 0, 0], ![-2292, 191, 0]], ![![3629, 191, 0], ![-233, 5, 13]]]
 hmul := by decide  
 g := ![![![![191, 0, 0], ![0, 0, 0]], ![![50, 30, -1], ![191, 0, 0]]], ![![![19, 1, 0], ![0, 0, 0]], ![![3, 2, 0], ![13, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-62, -29, 1]] ![![191, 0, 0], ![-7, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-1337, 191, 0]], ![![-11842, -5539, 191], ![764, 191, -382]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-7, 1, 0]]], ![![![-62, -29, 1]], ![![4, 1, -2]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![44, 48, 1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0], ![44, 48, 1]] 
 ![![193, 0, 0], ![0, 193, 0], ![44, 48, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![44, 48, 1], ![-55, -60, 626], ![8940, -371, 133]]]
  hmulB := by decide  
  f := ![![![-43, -48, -1], ![193, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-44, -48, 193]], ![![0, 0, 1], ![-143, -156, 626], ![16, -35, 133]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [95, 75, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [118, 192], [0, 1]]
 g := ![![[143, 128], [2], [84], [62], [177], [50], [118, 1]], ![[0, 65], [2], [84], [62], [177], [50], [43, 192]]]
 h' := ![![[118, 192], [66, 163], [16, 52], [135, 85], [106, 107], [138, 131], [177, 126], [0, 1]], ![[0, 1], [0, 30], [169, 141], [129, 108], [187, 86], [156, 62], [184, 67], [118, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [117, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [95, 75, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23320, 24475, -15875]
  a := ![15, 5, -40]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3740, 4075, -15875]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0], ![-47, 1, 0]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![193, 0, 0], ![-47, 1, 0]] 
 ![![193, 0, 0], ![146, 1, 0], ![60, 0, 1]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]], ![![-47, 1, 0], ![-5, -49, 13], ![185, -8, -45]]]
  hmulB := by decide  
  f := ![![![60798, 623045, -165282], ![-11387, 2453802, 0]], ![![45971, 471278, -125021], ![-8684, 1856081, 0]], ![![18889, 193693, -51383], ![-3589, 762840, 0]]]
  g := ![![![1, 0, 0], ![-146, 193, 0], ![-60, 0, 193]], ![![-1, 1, 0], ![33, -49, 13], ![21, -8, -45]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![193, 0, 0], ![44, 48, 1]] ![![193, 0, 0], ![-47, 1, 0]]
  ![![193, 0, 0]] where
 M := ![![![37249, 0, 0], ![-9071, 193, 0]], ![![8492, 9264, 193], ![-2123, -2316, 579]]]
 hmul := by decide  
 g := ![![![![193, 0, 0]], ![![-47, 1, 0]]], ![![![44, 48, 1]], ![![-11, -12, 3]]]]
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
  g := ![3, 2, 1, 2, 2, 2, 2, 2, 1, 3, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB278I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N2]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1]
    · exact ![I181N0]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![139, 139, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![32041, 179]
    · exact ![5929741]
    · exact ![191, 191, 191]
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
      exact NI139N2
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
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
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N0, I139N1, I139N2, I149N1, I157N1, I163N1, I167N1, I173N1, I179N1, I191N0, I191N1, I191N2, I193N1]
  Il := ![[I139N0, I139N1, I139N2], [I149N1], [], [I157N1], [I163N1], [I167N1], [I173N1], [I179N1], [], [I191N0, I191N1, I191N2], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
