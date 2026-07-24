
import IdealArithmetic.Examples.NF3_3_787077_1.RI3_3_787077_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![113885, 39010, -27344]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![113885, 39010, -27344]] 
 ![![139, 0, 0], ![0, 139, 0], ![133, 13, 1]] where
  M :=![![![113885, 39010, -27344], ![-1644652, -562061, 394112], ![3551390, 1213322, -850809]]]
  hmulB := by decide  
  f := ![![![156815, 93398, 38224]], ![![2594908, 1545505, 632512]], ![![424067, 252571, 103367]]]
  g := ![![![26983, 2838, -27344], ![-388932, -40903, 394112], ![839633, 88301, -850809]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [87, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 138], [0, 1]]
 g := ![![[54, 96], [47, 106], [107], [6, 127], [11], [89], [1]], ![[101, 43], [96, 33], [107], [87, 12], [11], [89], [1]]]
 h' := ![![[28, 138], [81, 97], [48, 55], [34, 61], [129, 108], [104, 122], [52, 28], [0, 1]], ![[0, 1], [17, 42], [59, 84], [74, 78], [95, 31], [45, 17], [2, 111], [28, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [60, 95]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [87, 111, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1613, 2598, 3044]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2901, -266, 3044]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-156815, -93398, -38224]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-156815, -93398, -38224]] 
 ![![139, 0, 0], ![38, 1, 0], ![14, 0, 1]] where
  M :=![![![-156815, -93398, -38224], ![-2594908, -1545505, -632512], ![-4355114, -2593870, -1061565]]]
  hmulB := by decide  
  f := ![![![-113885, -39010, 27344]], ![![-19302, -6621, 4640]], ![![-37020, -12658, 8875]]]
  g := ![![![28255, -93398, -38224], ![467550, -1545505, -632512], ![784704, -2593870, -1061565]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![113885, 39010, -27344]] ![![-156815, -93398, -38224]]
  ![![139, 0, 0]] where
 M := ![![![-139, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3849, 46, -166]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![3849, 46, -166]] 
 ![![149, 0, 0], ![0, 149, 0], ![19, 120, 1]] where
  M :=![![![3849, 46, -166], ![-10366, -827, 866], ![9538, 1832, -1435]]]
  hmulB := by decide  
  f := ![![![-2683, -1598, -654]], ![![-44398, -26443, -10822]], ![![-36599, -21798, -8921]]]
  g := ![![![47, 134, -166], ![-180, -703, 866], ![247, 1168, -1435]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [139, 70, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 148], [0, 1]]
 g := ![![[142, 37], [86], [64, 85], [1], [29, 145], [132], [1]], ![[85, 112], [86], [74, 64], [1], [11, 4], [132], [1]]]
 h' := ![![[79, 148], [114, 127], [44, 58], [74, 95], [141, 148], [79, 88], [10, 79], [0, 1]], ![[0, 1], [15, 22], [7, 91], [129, 54], [62, 1], [28, 61], [142, 70], [79, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [133, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [139, 70, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-681, 961, 3101]
  a := ![2, 2, 9]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-400, -2491, 3101]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2683, 1598, 654]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![2683, 1598, 654]] 
 ![![149, 0, 0], ![86, 1, 0], ![12, 0, 1]] where
  M :=![![![2683, 1598, 654], ![44398, 26443, 10822], ![74514, 44380, 18163]]]
  hmulB := by decide  
  f := ![![![-3849, -46, 166]], ![![-2152, -21, 90]], ![![-374, -16, 23]]]
  g := ![![![-957, 1598, 654], ![-15836, 26443, 10822], ![-26578, 44380, 18163]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![3849, 46, -166]] ![![2683, 1598, 654]]
  ![![149, 0, 0]] where
 M := ![![![-149, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-10186, -6067, -2483]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-10186, -6067, -2483]] 
 ![![151, 0, 0], ![0, 151, 0], ![134, 59, 1]] where
  M :=![![![-10186, -6067, -2483], ![-168563, -100394, -41087], ![-282901, -168494, -68958]]]
  hmulB := by decide  
  f := ![![![374, 16, -23]], ![![-1417, -245, 197]], ![![-209, -78, 54]]]
  g := ![![![2136, 930, -2483], ![35345, 15389, -41087], ![59321, 25828, -68958]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [103, 118, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [33, 150], [0, 1]]
 g := ![![[29, 22], [82, 116], [148, 121], [29], [8, 16], [32], [1]], ![[0, 129], [135, 35], [64, 30], [29], [83, 135], [32], [1]]]
 h' := ![![[33, 150], [10, 18], [7, 56], [113, 140], [82, 123], [65, 147], [48, 33], [0, 1]], ![[0, 1], [0, 133], [43, 95], [52, 11], [64, 28], [84, 4], [80, 118], [33, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [62]]
 b := ![[], [17, 31]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [103, 118, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2895596, 4585543, 6171280]
  a := ![-129, -193, -452]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5457324, -2380927, 6171280]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![374, 16, -23]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![374, 16, -23]] 
 ![![151, 0, 0], ![135, 1, 0], ![12, 0, 1]] where
  M :=![![![374, 16, -23], ![-1417, -245, 197], ![1928, 533, -387]]]
  hmulB := by decide  
  f := ![![![-10186, -6067, -2483]], ![![-10223, -6089, -2492]], ![![-2683, -1598, -654]]]
  g := ![![![-10, 16, -23], ![194, -245, 197], ![-433, 533, -387]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-10186, -6067, -2483]] ![![374, 16, -23]]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0]] 
 ![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [65, 50, 4, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [42, 17, 154], [111, 139, 3], [0, 1]]
 g := ![![[38, 62, 81], [81, 49], [51, 56, 51], [17, 127, 140], [2, 12, 57], [153, 1], []], ![[101, 113, 144, 75], [63, 76], [149, 153, 138, 118], [49, 10, 119, 11], [5, 121, 132, 36], [44, 10], [19, 9]], ![[107, 6, 28, 35], [118, 42], [146, 44, 126, 37], [63, 6, 59, 144], [88, 39, 71, 140], [127, 132], [13, 9]]]
 h' := ![![[42, 17, 154], [83, 4, 9], [139, 126, 150], [151, 102, 69], [27, 152, 104], [103, 135, 123], [0, 0, 1], [0, 1]], ![[111, 139, 3], [145, 47, 140], [1, 65, 62], [116, 3, 22], [40, 91, 27], [33, 124, 50], [58, 50, 139], [42, 17, 154]], ![[0, 1], [34, 106, 8], [47, 123, 102], [105, 52, 66], [90, 71, 26], [134, 55, 141], [15, 107, 17], [111, 139, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [123, 43], []]
 b := ![[], [19, 105, 119], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [65, 50, 4, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-759095, -1396201, -1982282]
  a := ![-3, -4, -13]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4835, -8893, -12626]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [90, 111, 77, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [106, 4, 38], [143, 158, 125], [0, 1]]
 g := ![![[93, 70, 24], [67, 42, 132], [64, 140], [50, 41], [32, 41], [113, 86, 1], []], ![[86, 121, 91, 54], [0, 92, 146, 132], [153, 93], [35, 115], [107, 121], [33, 62, 21, 135], [119, 140]], ![[95, 25, 128, 108], [122, 105, 7, 42], [158, 145], [94, 14], [134, 151], [38, 120, 113, 44], [32, 140]]]
 h' := ![![[106, 4, 38], [1, 7, 137], [38, 60, 28], [147, 14, 38], [75, 53, 81], [99, 92, 82], [0, 0, 1], [0, 1]], ![[143, 158, 125], [107, 111, 70], [99, 113, 21], [103, 35, 16], [51, 60, 142], [8, 31, 152], [37, 141, 158], [106, 4, 38]], ![[0, 1], [119, 45, 119], [140, 153, 114], [4, 114, 109], [92, 50, 103], [116, 40, 92], [128, 22, 4], [143, 158, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [94, 139], []]
 b := ![[], [14, 103, 95], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [90, 111, 77, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1555835, -1398051, -1274660]
  a := ![-3, -5, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-9545, -8577, -7820]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0]] 
 ![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [166, 61, 149, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 26, 165], [89, 140, 2], [0, 1]]
 g := ![![[96, 139, 116], [30, 30, 63], [74, 12, 6], [77, 157], [76, 33], [96, 18, 1], []], ![[65, 43, 122, 83], [117, 7, 157, 113], [51, 4, 63, 51], [48, 100], [154, 122], [41, 109, 111, 45], [135, 4]], ![[26, 68, 32, 93], [140, 49, 15, 130], [156, 138, 101, 31], [128, 116], [136, 77], [108, 121, 89, 16], [131, 4]]]
 h' := ![![[96, 26, 165], [30, 2, 139], [74, 16, 49], [3, 102, 29], [107, 81, 149], [96, 7, 130], [0, 0, 1], [0, 1]], ![[89, 140, 2], [83, 63, 84], [58, 21, 148], [80, 70, 15], [52, 121, 157], [137, 119, 150], [166, 101, 140], [96, 26, 165]], ![[0, 1], [35, 102, 111], [89, 130, 137], [105, 162, 123], [155, 132, 28], [55, 41, 54], [36, 66, 26], [89, 140, 2]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [59, 89], []]
 b := ![[], [105, 77, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [166, 61, 149, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1064312042, 894333430, 755180346]
  a := ![23, 44, 91]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![6373126, 5355290, 4522038]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [168, 83, 10, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [11, 66, 9], [152, 106, 164], [0, 1]]
 g := ![![[106, 86, 132], [131, 136], [61, 42, 40], [21, 166, 25], [155, 37], [17, 163, 1], []], ![[146, 73, 25, 116], [42, 47], [34, 93, 18, 117], [145, 172, 46, 152], [142, 29], [38, 78, 27, 92], [32, 81]], ![[72, 37, 122, 60], [32, 49], [70, 132, 32, 24], [167, 20, 39, 56], [47, 6], [4, 154, 60, 67], [50, 81]]]
 h' := ![![[11, 66, 9], [87, 108, 85], [132, 117, 84], [105, 159, 46], [42, 7, 5], [85, 96, 146], [0, 0, 1], [0, 1]], ![[152, 106, 164], [75, 109, 121], [111, 118, 96], [75, 36, 79], [140, 100, 74], [128, 56, 78], [108, 66, 106], [11, 66, 9]], ![[0, 1], [156, 129, 140], [13, 111, 166], [7, 151, 48], [63, 66, 94], [172, 21, 122], [172, 107, 66], [152, 106, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [90, 104], []]
 b := ![[], [41, 101, 123], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [168, 83, 10, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![36157, 4671, -23355]
  a := ![-1, 0, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![209, 27, -135]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0]] 
 ![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [173, 133, 38, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [93, 158, 170], [48, 20, 9], [0, 1]]
 g := ![![[105, 122, 88], [176, 71, 125], [101, 149], [43, 16], [141, 56, 64], [58, 141, 1], []], ![[30, 6, 102, 133], [8, 144, 172, 26], [5, 138], [46, 57], [178, 144, 109, 105], [10, 109, 43, 159], [164, 81]], ![[4, 105, 90, 45], [99, 25, 176, 173], [80, 25], [2, 45], [121, 65, 33, 88], [152, 33, 85, 31], [146, 81]]]
 h' := ![![[93, 158, 170], [161, 55, 25], [29, 136, 150], [153, 159, 111], [130, 120, 175], [169, 113, 171], [0, 0, 1], [0, 1]], ![[48, 20, 9], [155, 94, 5], [30, 163, 165], [0, 123, 73], [145, 137, 93], [23, 77, 76], [146, 7, 20], [93, 158, 170]], ![[0, 1], [140, 30, 149], [78, 59, 43], [80, 76, 174], [151, 101, 90], [22, 168, 111], [137, 172, 158], [48, 20, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [174, 74], []]
 b := ![[], [94, 115, 48], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [173, 133, 38, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7246457, 7529456, 7887456]
  a := ![5, 8, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![40483, 42064, 44064]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-37074, -22077, -9035]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-37074, -22077, -9035]] 
 ![![181, 0, 0], ![0, 181, 0], ![171, 121, 1]] where
  M :=![![![-37074, -22077, -9035], ![-613359, -365320, -149511], ![-1029451, -613128, -250928]]]
  hmulB := by decide  
  f := ![![![2008, 696, -487]], ![![-29289, -10027, 7029]], ![![-17333, -5926, 4155]]]
  g := ![![![8331, 5918, -9035], ![137862, 97931, -149511], ![231377, 164360, -250928]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [56, 158, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 180], [0, 1]]
 g := ![![[61, 139], [43], [21, 56], [126], [92, 80], [179, 167], [1]], ![[0, 42], [43], [42, 125], [126], [122, 101], [38, 14], [1]]]
 h' := ![![[23, 180], [81, 146], [91, 62], [0, 31], [97, 44], [112, 73], [125, 23], [0, 1]], ![[0, 1], [0, 35], [69, 119], [170, 150], [23, 137], [162, 108], [111, 158], [23, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35]]
 b := ![[], [25, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [56, 158, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![16176, 25380, 31795]
  a := ![-10, -15, -35]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-29949, -21115, 31795]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2008, 696, -487]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![2008, 696, -487]] 
 ![![181, 0, 0], ![121, 1, 0], ![161, 0, 1]] where
  M :=![![![2008, 696, -487], ![-29289, -10027, 7029], ![63328, 21645, -15177]]]
  hmulB := by decide  
  f := ![![![-37074, -22077, -9035]], ![![-28173, -16777, -6866]], ![![-38665, -23025, -9423]]]
  g := ![![![-21, 696, -487], ![289, -10027, 7029], ![-620, 21645, -15177]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-37074, -22077, -9035]] ![![2008, 696, -487]]
  ![![181, 0, 0]] where
 M := ![![![181, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2616, -958, 665]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-2616, -958, 665]] 
 ![![191, 0, 0], ![0, 191, 0], ![38, 110, 1]] where
  M :=![![![-2616, -958, 665], ![39979, 13795, -9659], ![-86954, -29777, 20873]]]
  hmulB := by decide  
  f := ![![![1712, 1019, 417]], ![![28309, 16862, 6901]], ![![16893, 10062, 4118]]]
  g := ![![![-146, -388, 665], ![2131, 5635, -9659], ![-4608, -12177, 20873]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [178, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [173, 190], [0, 1]]
 g := ![![[28, 107], [65, 103], [37, 36], [35, 69], [102, 154], [3, 133], [1]], ![[12, 84], [121, 88], [153, 155], [130, 122], [4, 37], [92, 58], [1]]]
 h' := ![![[173, 190], [81, 38], [99, 165], [73, 6], [180, 159], [39, 125], [13, 173], [0, 1]], ![[0, 1], [161, 153], [185, 26], [156, 185], [183, 32], [81, 66], [146, 18], [173, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [128]]
 b := ![[], [3, 64]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [178, 18, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6354, 4420, 2992]
  a := ![-2, -8, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-562, -1700, 2992]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1712, -1019, -417]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-1712, -1019, -417]] 
 ![![191, 0, 0], ![78, 1, 0], ![70, 0, 1]] where
  M :=![![![-1712, -1019, -417], ![-28309, -16862, -6901], ![-47517, -28300, -11582]]]
  hmulB := by decide  
  f := ![![![2616, 958, -665]], ![![859, 319, -221]], ![![1414, 507, -353]]]
  g := ![![![560, -1019, -417], ![9267, -16862, -6901], ![15553, -28300, -11582]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-2616, -958, 665]] ![![-1712, -1019, -417]]
  ![![191, 0, 0]] where
 M := ![![![-191, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [176, 151, 9, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [144, 88, 146], [40, 104, 47], [0, 1]]
 g := ![![[122, 63, 124], [16, 23], [151, 175], [158, 59], [131, 134], [59, 81], [1]], ![[67, 100, 61, 26], [15, 8], [158, 56], [116, 179], [45, 18], [103, 32], [82, 46, 24, 11]], ![[31, 153, 8, 127], [64, 124], [138, 92], [81, 6], [114, 118], [142, 190], [128, 14, 104, 182]]]
 h' := ![![[144, 88, 146], [164, 167, 33], [144, 147, 71], [146, 192, 102], [111, 56, 32], [134, 72, 83], [17, 42, 184], [0, 1]], ![[40, 104, 47], [126, 17, 22], [8, 110, 89], [105, 71, 40], [177, 28, 117], [143, 68, 37], [124, 32, 178], [144, 88, 146]], ![[0, 1], [91, 9, 138], [57, 129, 33], [42, 123, 51], [189, 109, 44], [48, 53, 73], [170, 119, 24], [40, 104, 47]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111, 36], []]
 b := ![[], [56, 43, 87], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [176, 151, 9, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![867236622, 828446710, 805091780]
  a := ![27, 40, 95]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4493454, 4292470, 4171460]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 7189057 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def PBC193 : ContainsPrimesAboveP 193 ![I193N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![193, 0, 0]]) timesTableT_eq_Table B_one_repr 193 (by decide) 𝕀



lemma PB198I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB198I3 : PrimesBelowBoundCertificateInterval O 137 193 198 where
  m := 11
  g := ![2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB198I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1]
    · exact ![I193N0]
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
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![36481, 191]
    · exact ![7189057]
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
    · dsimp ; intro j
      fin_cases j
      exact NI157N0
    · dsimp ; intro j
      fin_cases j
      exact NI163N0
    · dsimp ; intro j
      fin_cases j
      exact NI167N0
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
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
  β := ![I139N1, I149N1, I151N1, I181N1, I191N1]
  Il := ![[I139N1], [I149N1], [I151N1], [], [], [], [], [], [I181N1], [I191N1], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
