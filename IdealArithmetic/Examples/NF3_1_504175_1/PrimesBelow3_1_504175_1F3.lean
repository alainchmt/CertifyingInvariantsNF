
import IdealArithmetic.Examples.NF3_1_504175_1.RI3_1_504175_1
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


def P139P0 : CertificateIrreducibleZModOfList' 139 3 2 7 [125, 74, 111, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [78, 74, 114], [89, 64, 25], [0, 1]]
 g := ![![[85, 91, 71], [11, 49, 86], [136, 34], [47, 103, 13], [21, 86], [28, 1], []], ![[102, 61, 17, 12], [130, 24, 78, 18], [15, 13], [124, 43, 89, 27], [134, 49], [67, 65], [39, 69]], ![[107, 2, 75, 124], [100, 46, 94, 29], [134, 57], [34, 76, 115, 137], [27, 67], [131, 55], [128, 69]]]
 h' := ![![[78, 74, 114], [15, 88, 99], [76, 74, 124], [102, 46, 112], [85, 107, 41], [114, 27, 15], [0, 0, 1], [0, 1]], ![[89, 64, 25], [80, 49, 105], [84, 116, 109], [98, 11, 41], [37, 97, 88], [61, 130, 7], [97, 33, 64], [78, 74, 114]], ![[0, 1], [48, 2, 74], [106, 88, 45], [68, 82, 125], [15, 74, 10], [38, 121, 117], [122, 106, 74], [89, 64, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 75], []]
 b := ![[], [17, 60, 3], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 3
  hpos := by decide
  P := [125, 74, 111, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-393370, -98134, -3753]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2830, -706, -27]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-13999, -785, 144]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![-13999, -785, 144]] 
 ![![149, 0, 0], ![0, 149, 0], ![88, 8, 1]] where
  M :=![![![-13999, -785, 144], ![79920, 4001, -785], ![-435675, -18205, 4001]]]
  hmulB := by decide  
  f := ![![![11524, 3485, 269]], ![![149295, 45149, 3485]], ![![27803, 8408, 649]]]
  g := ![![![-179, -13, 144], ![1000, 69, -785], ![-5287, -337, 4001]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [93, 24, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 148], [0, 1]]
 g := ![![[106, 30], [143], [127, 7], [26], [31, 133], [129], [1]], ![[131, 119], [143], [108, 142], [26], [117, 16], [129], [1]]]
 h' := ![![[125, 148], [72, 103], [109, 21], [137, 56], [97, 131], [79, 27], [56, 125], [0, 1]], ![[0, 1], [133, 46], [52, 128], [134, 93], [82, 18], [27, 122], [36, 24], [125, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [111]]
 b := ![[], [70, 130]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [93, 24, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6590, 3451, 1195]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-750, -41, 1195]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11524, -3485, -269]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![-11524, -3485, -269]] 
 ![![149, 0, 0], ![141, 1, 0], ![85, 0, 1]] where
  M :=![![![-11524, -3485, -269], ![-149295, -45149, -3485], ![-1934175, -584920, -45149]]]
  hmulB := by decide  
  f := ![![![13999, 785, -144]], ![![12711, 716, -131]], ![![10910, 570, -109]]]
  g := ![![![3374, -3485, -269], ![43711, -45149, -3485], ![566290, -584920, -45149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![-13999, -785, 144]] ![![-11524, -3485, -269]]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5640061099, 914297927, -104177178]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![5640061099, 914297927, -104177178]] 
 ![![151, 0, 0], ![0, 151, 0], ![58, 33, 1]] where
  M :=![![![5640061099, 914297927, -104177178], ![-57818333790, -7382086151, 914297927], ![507435349485, 56468907085, -7382086151]]]
  hmulB := by decide  
  f := ![![![-18978750019966106, -5739434966458297, -443018518890301]], ![![-245875277984117055, -74356064881253731, -5739434966458297]], ![![-82119457490187098, -24834053098856679, -1916903926291490]]]
  g := ![![![77366473, 28822151, -104177178], ![-734090156, -248701442, 914297927], ![6196002293, 1987269868, -7382086151]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [128, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [74, 150], [0, 1]]
 g := ![![[82, 105], [47, 40], [30, 36], [88], [63, 31], [40], [1]], ![[0, 46], [138, 111], [127, 115], [88], [92, 120], [40], [1]]]
 h' := ![![[74, 150], [24, 16], [86, 77], [7, 6], [90, 36], [90, 22], [23, 74], [0, 1]], ![[0, 1], [0, 135], [46, 74], [149, 145], [36, 115], [57, 129], [63, 77], [74, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32]]
 b := ![[], [12, 16]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [128, 77, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1814, 254, 177]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-80, -37, 177]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![18978750019966106, 5739434966458297, 443018518890301]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![18978750019966106, 5739434966458297, 443018518890301]] 
 ![![151, 0, 0], ![118, 1, 0], ![119, 0, 1]] where
  M :=![![![18978750019966106, 5739434966458297, 443018518890301], ![245875277984117055, 74356064881253731, 5739434966458297], ![3185386406384354835, 963304648791404180, 74356064881253731]]]
  hmulB := by decide  
  f := ![![![-5640061099, -914297927, 104177178]], ![![-4024562092, -665596485, 75355027]], ![![-7805315366, -1094505698, 130987883]]]
  g := ![![![-4708568077947409, 5739434966458297, 443018518890301], ![-61000881715313646, 74356064881253731, 5739434966458297], ![-790284330277288294, 963304648791404180, 74356064881253731]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![5640061099, 914297927, -104177178]] ![![18978750019966106, 5739434966458297, 443018518890301]]
  ![![151, 0, 0]] where
 M := ![![![-151, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [138, 29, 119, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 4, 73], [47, 152, 84], [0, 1]]
 g := ![![[140, 119, 30], [71, 75], [101, 77, 148], [136, 64, 141], [89, 59, 4], [38, 1], []], ![[52, 97, 50, 97], [30, 57], [35, 54, 5, 125], [5, 35, 124, 151], [59, 139, 97, 87], [84, 25], [85, 148]], ![[13, 31, 5, 62], [130, 144], [86, 13, 8, 88], [134, 151, 154, 95], [31, 126, 75, 134], [135, 16], [74, 148]]]
 h' := ![![[148, 4, 73], [62, 105, 117], [35, 107, 111], [72, 138, 84], [121, 154, 45], [94, 16, 2], [0, 0, 1], [0, 1]], ![[47, 152, 84], [43, 96, 15], [27, 24, 34], [151, 102, 77], [9, 117, 27], [45, 143, 59], [126, 118, 152], [148, 4, 73]], ![[0, 1], [127, 113, 25], [13, 26, 12], [143, 74, 153], [3, 43, 85], [69, 155, 96], [4, 39, 4], [47, 152, 84]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [32, 131], []]
 b := ![[], [37, 118, 138], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [138, 29, 119, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-6848968, -2811085, -271453]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-43624, -17905, -1729]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-96102094889449, -29062594911579, -2243298831345]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-96102094889449, -29062594911579, -2243298831345]] 
 ![![163, 0, 0], ![0, 163, 0], ![125, 24, 1]] where
  M :=![![![-96102094889449, -29062594911579, -2243298831345], ![-1245030851396475, -376514448807574, -29062594911579], ![-16129740175926345, -4877855215343850, -376514448807574]]]
  hmulB := by decide  
  f := ![![![-96002002, -5015208, 959103]], ![![532302165, 23885873, -5015208]], ![![-12321710, -909441, 143612]]]
  g := ![![![1130737785452, 152003540127, -2243298831345], ![14649039954300, 1969250485094, -29062594911579], ![189782613036935, 25512218135202, -376514448807574]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [36, 139, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [24, 162], [0, 1]]
 g := ![![[108, 77], [18, 40], [22], [41], [134], [34, 87], [1]], ![[0, 86], [0, 123], [22], [41], [134], [3, 76], [1]]]
 h' := ![![[24, 162], [4, 27], [100, 23], [136, 115], [109, 82], [80, 121], [127, 24], [0, 1]], ![[0, 1], [0, 136], [0, 140], [125, 48], [121, 81], [50, 42], [51, 139], [24, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [83]]
 b := ![[], [154, 123]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [36, 139, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1146, 666, -13]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![17, 6, -13]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![96002002, 5015208, -959103]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![96002002, 5015208, -959103]] 
 ![![163, 0, 0], ![139, 1, 0], ![76, 0, 1]] where
  M :=![![![96002002, 5015208, -959103], ![-532302165, -23885873, 5015208], ![2783440440, 94598835, -23885873]]]
  hmulB := by decide  
  f := ![![![96102094889449, 29062594911579, 2243298831345]], ![![89590319270122, 27093344426485, 2091295291218]], ![![143763799923463, 43476149868858, 3355859877238]]]
  g := ![![![-3240614, 5015208, -959103], ![14764898, -23885873, 5015208], ![-52456879, 94598835, -23885873]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-96102094889449, -29062594911579, -2243298831345]] ![![96002002, 5015208, -959103]]
  ![![163, 0, 0]] where
 M := ![![![-163, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3179186, -302392, 42283]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-3179186, -302392, 42283]] 
 ![![167, 0, 0], ![0, 167, 0], ![5, 111, 1]] where
  M :=![![![-3179186, -302392, 42283], ![23467065, 2106189, -302392], ![-167827560, -14331935, 2106189]]]
  hmulB := by decide  
  f := ![![![611794103, 185014949, 14281031]], ![![7925972205, 2396922978, 185014949]], ![![5901348395, 1784648899, 137754416]]]
  g := ![![![-20303, -29915, 42283], ![149575, 213603, -302392], ![-1068015, -1485742, 2106189]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [152, 150, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [17, 166], [0, 1]]
 g := ![![[157, 89], [7, 88], [139, 54], [132], [24], [79, 122], [1]], ![[0, 78], [0, 79], [55, 113], [132], [24], [149, 45], [1]]]
 h' := ![![[17, 166], [105, 151], [81, 64], [8, 87], [115, 93], [16, 58], [15, 17], [0, 1]], ![[0, 1], [0, 16], [0, 103], [151, 80], [26, 74], [0, 109], [137, 150], [17, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [22]]
 b := ![[], [157, 11]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [152, 150, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![21393, 8193, 638]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![109, -375, 638]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-611794103, -185014949, -14281031]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-611794103, -185014949, -14281031]] 
 ![![167, 0, 0], ![56, 1, 0], ![37, 0, 1]] where
  M :=![![![-611794103, -185014949, -14281031], ![-7925972205, -2396922978, -185014949], ![-102683296695, -31052840830, -2396922978]]]
  hmulB := by decide  
  f := ![![![3179186, 302392, -42283]], ![![925553, 88789, -12368]], ![![1709326, 152817, -21980]]]
  g := ![![![61541564, -185014949, -14281031], ![797289028, -2396922978, -185014949], ![10329113413, -31052840830, -2396922978]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-3179186, -302392, 42283]] ![![-611794103, -185014949, -14281031]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![50890303814, 4447919059, -646536221]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![50890303814, 4447919059, -646536221]] 
 ![![173, 0, 0], ![0, 173, 0], ![102, 153, 1]] where
  M :=![![![50890303814, 4447919059, -646536221], ![-358827602655, -29926723811, 4447919059], ![2468595077745, 197162279720, -29926723811]]]
  hmulB := by decide  
  f := ![![![107785759406920117, 32595895713654773, 2516029108328250]], ![![1396396155122178750, 422289397947951367, 32595895713654773]], ![![1403083707018945663, 424311805596291164, 32752002376801232]]]
  g := ![![![675358372, 597502664, -646536221], ![-4696620501, -4106695606, 4447919059], ![31913993679, 27606653311, -29926723811]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [149, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 172], [0, 1]]
 g := ![![[124, 36], [83], [4, 121], [145, 35], [78], [94, 14], [1]], ![[0, 137], [83], [87, 52], [159, 138], [78], [65, 159], [1]]]
 h' := ![![[35, 172], [136, 6], [96, 157], [20, 11], [18, 143], [7, 50], [24, 35], [0, 1]], ![[0, 1], [0, 167], [55, 16], [59, 162], [6, 30], [27, 123], [38, 138], [35, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [44]]
 b := ![[], [134, 22]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [149, 138, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-3318, 213, -2]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, 3, -2]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-107785759406920117, -32595895713654773, -2516029108328250]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-107785759406920117, -32595895713654773, -2516029108328250]] 
 ![![173, 0, 0], ![20, 1, 0], ![119, 0, 1]] where
  M :=![![![-107785759406920117, -32595895713654773, -2516029108328250], ![-1396396155122178750, -422289397947951367, -32595895713654773], ![-18090722121078399015, -5470883119329025375, -422289397947951367]]]
  hmulB := by decide  
  f := ![![![-50890303814, -4447919059, 646536221]], ![![-3809124125, -341223453, 49033557]], ![![-49274804807, -4199217617, 617714070]]]
  g := ![![![4875951553510041, -32595895713654773, -2516029108328250], ![63169383778969749, -422289397947951367, -32595895713654773], ![818377911105828446, -5470883119329025375, -422289397947951367]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![50890303814, 4447919059, -646536221]] ![![-107785759406920117, -32595895713654773, -2516029108328250]]
  ![![173, 0, 0]] where
 M := ![![![-173, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [125, 154, 37, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [38, 142, 172], [104, 36, 7], [0, 1]]
 g := ![![[67, 162, 108], [154, 2, 126], [145, 70], [72, 29], [174, 9, 4], [141, 142, 1], []], ![[145, 6, 100, 68], [90, 108, 134, 42], [102, 66], [100, 59], [8, 19, 28, 135], [92, 72, 27, 57], [137, 49]], ![[62, 121, 158, 127], [46, 105, 108, 130], [161, 172], [30, 68], [169, 52, 47, 123], [176, 74, 100, 96], [123, 49]]]
 h' := ![![[38, 142, 172], [82, 136, 114], [142, 106, 22], [176, 53, 41], [88, 90, 71], [96, 95, 177], [0, 0, 1], [0, 1]], ![[104, 36, 7], [98, 81, 109], [4, 114, 50], [89, 93, 31], [136, 13, 136], [163, 170, 158], [71, 37, 36], [38, 142, 172]], ![[0, 1], [175, 141, 135], [10, 138, 107], [96, 33, 107], [83, 76, 151], [120, 93, 23], [95, 142, 142], [104, 36, 7]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [140, 36], []]
 b := ![[], [166, 102, 133], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [125, 154, 37, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![3379520, 1401749, 151255]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![18880, 7831, 845]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-744750326, -225222739, -17384611]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-744750326, -225222739, -17384611]] 
 ![![181, 0, 0], ![0, 181, 0], ![36, 121, 1]] where
  M :=![![![-744750326, -225222739, -17384611], ![-9648459105, -2917826701, -225222739], ![-124998620145, -37801301480, -2917826701]]]
  hmulB := by decide  
  f := ![![![120499, 16739, -2010]], ![![-1115550, -130751, 16739]], ![![-670461, -78682, 10068]]]
  g := ![![![-656930, 10377432, -17384611], ![-8510721, 134442678, -225222739], ![-110258889, 1741744361, -2917826701]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [39, 56, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [125, 180], [0, 1]]
 g := ![![[20, 65], [49], [24, 122], [59], [33, 136], [159, 59], [1]], ![[0, 116], [49], [70, 59], [59], [19, 45], [113, 122], [1]]]
 h' := ![![[125, 180], [136, 80], [150, 7], [90, 22], [161, 125], [134, 90], [142, 125], [0, 1]], ![[0, 1], [0, 101], [120, 174], [125, 159], [39, 56], [162, 91], [20, 56], [125, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112]]
 b := ![[], [120, 56]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [39, 56, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-22045, -3380, 720]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-265, -500, 720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-120499, -16739, 2010]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-120499, -16739, 2010]] 
 ![![181, 0, 0], ![60, 1, 0], ![20, 0, 1]] where
  M :=![![![-120499, -16739, 2010], ![1115550, 130751, -16739], ![-9290145, -976825, 130751]]]
  hmulB := by decide  
  f := ![![![744750326, 225222739, 17384611]], ![![300184965, 90780061, 7007179]], ![![772892965, 233733460, 18041541]]]
  g := ![![![4661, -16739, 2010], ![-35330, 130751, -16739], ![258035, -976825, 130751]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-744750326, -225222739, -17384611]] ![![-120499, -16739, 2010]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0]] 
 ![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [188, 106, 93, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 142, 166], [36, 48, 25], [0, 1]]
 g := ![![[148, 187, 149], [163, 16, 147], [97, 99, 149], [88, 190, 147], [87, 67, 100], [139, 98, 1], []], ![[146, 143, 130, 137], [105, 124, 150, 175], [165, 113, 134, 111], [154, 26, 141, 159], [149, 87, 136, 74], [140, 160, 64, 82], [97, 52]], ![[142, 93, 20, 103], [106, 38, 168, 27], [84, 127, 176, 121], [180, 184, 5, 163], [17, 34, 123, 13], [29, 179, 164, 51], [47, 52]]]
 h' := ![![[62, 142, 166], [107, 28, 128], [100, 119, 23], [73, 153, 128], [70, 35, 168], [35, 76, 181], [0, 0, 1], [0, 1]], ![[36, 48, 25], [143, 178, 96], [16, 85, 39], [28, 165, 27], [152, 9, 122], [69, 148, 103], [124, 33, 48], [62, 142, 166]], ![[0, 1], [163, 176, 158], [190, 178, 129], [45, 64, 36], [176, 147, 92], [52, 158, 98], [100, 158, 142], [36, 48, 25]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 42], []]
 b := ![[], [145, 69, 101], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [188, 106, 93, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-27695, 130644, 33998]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-145, 684, 178]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [78, 99, 54, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [94, 136, 52], [45, 56, 141], [0, 1]]
 g := ![![[172, 124, 54], [140, 184], [156, 86], [165, 108], [158, 139], [101, 21], [1]], ![[126, 121, 65, 178], [164, 9], [29, 43], [124, 144], [53, 144], [125, 110], [67, 138, 25, 104]], ![[138, 0, 132, 99], [125, 107], [152, 162], [188, 145], [126, 8], [132, 118], [97, 120, 162, 89]]]
 h' := ![![[94, 136, 52], [190, 70, 132], [130, 39, 50], [77, 10, 47], [189, 16, 109], [136, 140, 77], [115, 94, 139], [0, 1]], ![[45, 56, 141], [145, 34, 31], [149, 44, 3], [148, 44, 64], [154, 89, 181], [87, 93, 12], [90, 14, 127], [94, 136, 52]], ![[0, 1], [111, 89, 30], [156, 110, 140], [25, 139, 82], [139, 88, 96], [33, 153, 104], [183, 85, 120], [45, 56, 141]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107, 172], []]
 b := ![[], [57, 98, 160], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [78, 99, 54, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-922733, -273095, -20458]
  a := ![1, -4, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-4781, -1415, -106]
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



lemma PB201I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB201I3 : PrimesBelowBoundCertificateInterval O 137 193 201 where
  m := 11
  g := ![1, 2, 2, 1, 2, 2, 2, 1, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB201I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0]
    · exact ![I149N0, I149N1]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
    · exact ![I191N0]
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
    · exact ![2685619]
    · exact ![22201, 149]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
    · exact ![6967871]
    · exact ![7189057]
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
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I149N1, I151N1, I163N1, I167N1, I173N1, I181N1]
  Il := ![[], [I149N1], [I151N1], [], [I163N1], [I167N1], [I173N1], [], [I181N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
