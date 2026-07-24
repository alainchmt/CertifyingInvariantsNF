
import IdealArithmetic.Examples.NF3_1_672300_4.RI3_1_672300_4
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-6, -10, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-6, -10, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![133, 129, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-6, -10, 1], ![136, -5, -69], ![-1518, 111, -25]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-133, -129, 139]], ![![-1, -1, 1], ![67, 64, -69], ![13, 24, -25]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [107, 53, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [86, 138], [0, 1]]
 g := ![![[133, 13], [107, 122], [11], [112, 42], [65], [29], [1]], ![[0, 126], [35, 17], [11], [110, 97], [65], [29], [1]]]
 h' := ![![[86, 138], [88, 41], [1, 20], [109, 122], [31, 96], [6, 75], [32, 86], [0, 1]], ![[0, 1], [0, 98], [53, 119], [37, 17], [86, 43], [62, 64], [61, 53], [86, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [82, 108]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [107, 53, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2063, 1029, -784]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![765, 735, -784]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![69, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![69, 1, 0]] 
 ![![139, 0, 0], ![69, 1, 0], ![25, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![69, 1, 0], ![2, 68, 7], ![156, -9, 70]]]
  hmulB := by decide  
  f := ![![![10791, 521630, 53704], ![9174, -1066408, 0]], ![![5339, 258911, 26656], ![4588, -529312, 0]], ![![1917, 93818, 9659], ![1698, -191800, 0]]]
  g := ![![![1, 0, 0], ![-69, 139, 0], ![-25, 0, 139]], ![![0, 1, 0], ![-35, 68, 7], ![-7, -9, 70]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![-6, -10, 1]] ![![139, 0, 0], ![69, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![9591, 139, 0]], ![![-834, -1390, 139], ![-278, -695, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![69, 1, 0]]], ![![![-6, -10, 1]], ![![-2, -5, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-46, 61, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-46, 61, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![103, 61, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-46, 61, 1], ![278, -116, 428], ![9558, -528, 6]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-103, -61, 149]], ![![-1, 0, 1], ![-294, -176, 428], ![60, -6, 6]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [74, 70, 1] where
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
 g := ![![[9, 107], [1], [95, 129], [5], [80, 118], [132], [1]], ![[118, 42], [1], [5, 20], [5], [15, 31], [132], [1]]]
 h' := ![![[79, 148], [59, 133], [122, 148], [38, 24], [40, 68], [29, 77], [75, 79], [0, 1]], ![[0, 1], [136, 16], [43, 1], [146, 125], [48, 81], [3, 72], [58, 70], [79, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [40]]
 b := ![[], [104, 20]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [74, 70, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-13973, 7999, -1481]
  a := ![5, -5, 18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![930, 660, -1481]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![19, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![19, 1, 0]] 
 ![![149, 0, 0], ![19, 1, 0], ![143, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![19, 1, 0], ![2, 18, 7], ![156, -9, 20]]]
  hmulB := by decide  
  f := ![![![779, 7342, 2856], ![298, -60792, 0]], ![![85, 935, 364], ![150, -7748, 0]], ![![760, 7047, 2741], ![189, -58344, 0]]]
  g := ![![![1, 0, 0], ![-19, 149, 0], ![-143, 0, 149]], ![![0, 1, 0], ![-9, 18, 7], ![-17, -9, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-46, 61, 1]] ![![149, 0, 0], ![19, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![2831, 149, 0]], ![![-6854, 9089, 149], ![-596, 1043, 447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![19, 1, 0]]], ![![![-46, 61, 1]], ![![-4, 7, 3]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [65, 89, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [111, 17, 8], [102, 133, 143], [0, 1]]
 g := ![![[140, 122, 34], [88, 134, 85], [16, 135, 11], [105, 123], [148, 27, 98], [62, 1], []], ![[106, 30, 143, 8], [21, 99, 33, 88], [90, 95, 26, 78], [59, 34], [109, 86, 34, 21], [103, 22], [12, 64]], ![[17, 138, 18, 112], [41, 118, 9, 133], [128, 22, 139, 109], [114, 38], [100, 132, 117, 60], [8, 138], [28, 64]]]
 h' := ![![[111, 17, 8], [18, 55, 100], [17, 147, 38], [94, 53, 39], [44, 117, 24], [47, 4, 131], [0, 0, 1], [0, 1]], ![[102, 133, 143], [90, 42, 150], [80, 97, 39], [56, 65, 24], [95, 11, 51], [97, 5, 90], [65, 56, 133], [111, 17, 8]], ![[0, 1], [6, 54, 52], [94, 58, 74], [73, 33, 88], [101, 23, 76], [9, 142, 81], [128, 95, 17], [102, 133, 143]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [138, 3], []]
 b := ![[], [77, 120, 94], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [65, 89, 89, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-23329580785, 2911304915, -1063216670]
  a := ![-66, 2, -199]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-154500535, 19280165, -7041170]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![43, -18, 1]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![43, -18, 1]] 
 ![![157, 0, 0], ![0, 157, 0], ![43, 139, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![43, -18, 1], ![120, 52, -125], ![-2766, 183, 16]]]
  hmulB := by decide  
  f := ![![![-42, 18, -1], ![157, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-43, -139, 157]], ![![0, -1, 1], ![35, 111, -125], ![-22, -13, 16]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [98, 154, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 156], [0, 1]]
 g := ![![[24, 42], [51], [119, 108], [140, 30], [5, 93], [9], [1]], ![[150, 115], [51], [129, 49], [73, 127], [127, 64], [9], [1]]]
 h' := ![![[3, 156], [78, 102], [113, 88], [96, 39], [138, 40], [87, 67], [59, 3], [0, 1]], ![[0, 1], [70, 55], [63, 69], [56, 118], [101, 117], [131, 90], [68, 154], [3, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [107]]
 b := ![[], [116, 132]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [98, 154, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9471, 8660, -5540]
  a := ![-5, 4, -18]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1457, 4960, -5540]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-32, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-32, 1, 0]] 
 ![![157, 0, 0], ![125, 1, 0], ![141, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-32, 1, 0], ![2, -33, 7], ![156, -9, -31]]]
  hmulB := by decide  
  f := ![![![12971, -227707, 48307], ![-4082, -1083457, 0]], ![![10349, -181282, 38458], ![-3139, -862558, 0]], ![![11675, -204502, 43384], ![-3539, -973041, 0]]]
  g := ![![![1, 0, 0], ![-125, 157, 0], ![-141, 0, 157]], ![![-1, 1, 0], ![20, -33, 7], ![36, -9, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![43, -18, 1]] ![![157, 0, 0], ![-32, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-5024, 157, 0]], ![![6751, -2826, 157], ![-1256, 628, -157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-32, 1, 0]]], ![![![43, -18, 1]], ![![-8, 4, -1]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-775, 9, 64]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-775, 9, 64]] 
 ![![163, 0, 0], ![0, 163, 0], ![21, 74, 1]] where
  M :=![![![-775, 9, 64], ![10002, -1360, 127], ![4092, 1263, -1342]]]
  hmulB := by decide  
  f := ![![![-10213, -570, -541]], ![![-85536, -4774, -4531]], ![![-40833, -2279, -2163]]]
  g := ![![![-13, -29, 64], ![45, -66, 127], ![198, 617, -1342]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [31, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [72, 162], [0, 1]]
 g := ![![[45, 96], [150, 54], [111], [155], [151], [78, 131], [1]], ![[111, 67], [126, 109], [111], [155], [151], [56, 32], [1]]]
 h' := ![![[72, 162], [77, 111], [73, 124], [55, 130], [123, 36], [27, 71], [132, 72], [0, 1]], ![[0, 1], [82, 52], [36, 39], [124, 33], [107, 127], [86, 92], [100, 91], [72, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [46]]
 b := ![[], [150, 23]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [31, 91, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1911, 1029, -1050]
  a := ![-2, 0, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![147, 483, -1050]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10213, 570, 541]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![10213, 570, 541]] 
 ![![163, 0, 0], ![133, 1, 0], ![77, 0, 1]] where
  M :=![![![10213, 570, 541], ![85536, 4774, 4531], ![111642, 6231, 5914]]]
  hmulB := by decide  
  f := ![![![775, -9, -64]], ![![571, 1, -53]], ![![341, -12, -22]]]
  g := ![![![-658, 570, 541], ![-5511, 4774, 4531], ![-7193, 6231, 5914]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-775, 9, 64]] ![![10213, 570, 541]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![48, 1, 0]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![48, 1, 0]] 
 ![![167, 0, 0], ![48, 1, 0], ![12, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![48, 1, 0], ![2, 47, 7], ![156, -9, 49]]]
  hmulB := by decide  
  f := ![![![-14831, -392505, -58464], ![-6513, 1394784, 0]], ![![-4272, -112789, -16800], ![-1836, 400800, 0]], ![![-1068, -28204, -4201], ![-460, 100224, 0]]]
  g := ![![![1, 0, 0], ![-48, 167, 0], ![-12, 0, 167]], ![![0, 1, 0], ![-14, 47, 7], ![0, -9, 49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N0 : Nat.card (O ⧸ I167N0) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N0)

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := prime_ideal_of_norm_prime hp167.out _ NI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-31, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-31, 1, 0]] 
 ![![167, 0, 0], ![136, 1, 0], ![121, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-31, 1, 0], ![2, -32, 7], ![156, -9, -30]]]
  hmulB := by decide  
  f := ![![![13319, -223978, 49000], ![-3674, -1169000, 0]], ![![10843, -182382, 39900], ![-3005, -951900, 0]], ![![9636, -162283, 35503], ![-2739, -847000, 0]]]
  g := ![![![1, 0, 0], ![-136, 167, 0], ![-121, 0, 167]], ![![-1, 1, 0], ![21, -32, 7], ![30, -9, -30]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1

def I167N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![-17, 1, 0]] i)))

def SI167N2: IdealEqSpanCertificate' Table ![![167, 0, 0], ![-17, 1, 0]] 
 ![![167, 0, 0], ![150, 1, 0], ![52, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![-17, 1, 0], ![2, -18, 7], ![156, -9, -16]]]
  hmulB := by decide  
  f := ![![![34449, -314896, 122472], ![-5344, -2921832, 0]], ![![30936, -282823, 109998], ![-4842, -2624238, 0]], ![![10736, -98052, 38135], ![-1572, -909792, 0]]]
  g := ![![![1, 0, 0], ![-150, 167, 0], ![-52, 0, 167]], ![![-1, 1, 0], ![14, -18, 7], ![14, -9, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N2 : Nat.card (O ⧸ I167N2) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N2)

lemma isPrimeI167N2 : Ideal.IsPrime I167N2 := prime_ideal_of_norm_prime hp167.out _ NI167N2
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![48, 1, 0]] ![![167, 0, 0], ![-31, 1, 0]]
  ![![167, 0, 0], ![74, 50, 1]] where
 M := ![![![27889, 0, 0], ![-5177, 167, 0]], ![![8016, 167, 0], ![-1486, 16, 7]]]
 hmul := by decide  
 g := ![![![![93, -50, -1], ![167, 0, 0]], ![![-31, 1, 0], ![0, 0, 0]]], ![![![-26, -49, -1], ![167, 0, 0]], ![![-12, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI167N1 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![74, 50, 1]] ![![167, 0, 0], ![-17, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![-2839, 167, 0]], ![![12358, 8350, 167], ![-1002, -835, 334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![-17, 1, 0]]], ![![![74, 50, 1]], ![![-6, -5, 2]]]]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [57, 83, 171, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [136, 52, 48], [39, 120, 125], [0, 1]]
 g := ![![[31, 35, 83], [19, 1], [0, 28, 122], [96, 10, 85], [29, 14], [94, 2, 1], []], ![[55, 107, 129, 125], [56, 81], [16, 65, 116, 82], [45, 49, 10, 11], [89, 73], [9, 39, 58, 65], [85, 55]], ![[128, 119, 83, 166], [60, 100], [130, 25, 76, 72], [139, 130, 162, 18], [155, 35], [7, 26, 127, 131], [8, 55]]]
 h' := ![![[136, 52, 48], [128, 96, 157], [0, 78, 172], [64, 136, 45], [102, 156, 137], [5, 42, 138], [0, 0, 1], [0, 1]], ![[39, 120, 125], [119, 29, 93], [71, 102, 164], [21, 65, 164], [96, 16, 54], [49, 118, 65], [157, 148, 120], [136, 52, 48]], ![[0, 1], [153, 48, 96], [74, 166, 10], [9, 145, 137], [24, 1, 155], [6, 13, 143], [27, 25, 52], [39, 120, 125]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 109], []]
 b := ![[], [63, 76, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [57, 83, 171, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14224752, 1096128, 608960]
  a := ![3, 18, 10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![82224, 6336, 3520]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-143, -8, -7]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-143, -8, -7]] 
 ![![179, 0, 0], ![0, 179, 0], ![46, 129, 1]] where
  M :=![![![-143, -8, -7], ![-1108, -72, -63], ![-1542, -75, -88]]]
  hmulB := by decide  
  f := ![![![-9, 1, 0]], ![![2, -10, 7]], ![![0, -7, 5]]]
  g := ![![![1, 5, -7], ![10, 45, -63], ![14, 63, -88]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [145, 171, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 178], [0, 1]]
 g := ![![[95, 100], [124, 74], [125], [56], [28, 82], [161, 64], [1]], ![[0, 79], [0, 105], [125], [56], [147, 97], [136, 115], [1]]]
 h' := ![![[8, 178], [99, 10], [145, 49], [141, 29], [57, 45], [104, 145], [34, 8], [0, 1]], ![[0, 1], [0, 169], [0, 130], [15, 150], [59, 134], [11, 34], [98, 171], [8, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [68]]
 b := ![[], [43, 34]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [145, 171, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8607, 3464, -2518]
  a := ![-3, 4, -10]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![599, 1834, -2518]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-9, 1, 0]] 
 ![![179, 0, 0], ![170, 1, 0], ![13, 0, 1]] where
  M :=![![![-9, 1, 0], ![2, -10, 7], ![156, -9, -8]]]
  hmulB := by decide  
  f := ![![![-143, -8, -7]], ![![-142, -8, -7]], ![![-19, -1, -1]]]
  g := ![![![-1, 1, 0], ![9, -10, 7], ![10, -9, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-143, -8, -7]] ![![-9, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![179, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![30, 65, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![30, 65, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![30, 65, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![30, 65, 1], ![286, -44, 456], ![10182, -564, 86]]]
  hmulB := by decide  
  f := ![![![-29, -65, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-30, -65, 181]], ![![0, 0, 1], ![-74, -164, 456], ![42, -34, 86]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [39, 87, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [94, 180], [0, 1]]
 g := ![![[44, 65], [101], [157, 70], [106], [138, 34], [64, 148], [1]], ![[0, 116], [101], [40, 111], [106], [76, 147], [39, 33], [1]]]
 h' := ![![[94, 180], [99, 101], [31, 120], [161, 147], [48, 58], [38, 136], [142, 94], [0, 1]], ![[0, 1], [0, 80], [89, 61], [42, 34], [70, 123], [152, 45], [109, 87], [94, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [91]]
 b := ![[], [124, 136]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [39, 87, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4269, 4272, -455]
  a := ![4, -1, 14]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![99, 187, -455]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![87, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![87, 1, 0]] 
 ![![181, 0, 0], ![87, 1, 0], ![95, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![87, 1, 0], ![2, 86, 7], ![156, -9, 88]]]
  hmulB := by decide  
  f := ![![![-3767, -221864, -18060], ![-2896, 466980, 0]], ![![-1871, -106633, -8680], ![-1266, 224440, 0]], ![![-1981, -116448, -9479], ![-1512, 245100, 0]]]
  g := ![![![1, 0, 0], ![-87, 181, 0], ![-95, 0, 181]], ![![0, 1, 0], ![-45, 86, 7], ![-41, -9, 88]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![30, 65, 1]] ![![181, 0, 0], ![87, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![15747, 181, 0]], ![![5430, 11765, 181], ![2896, 5611, 543]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![87, 1, 0]]], ![![![30, 65, 1]], ![![16, 31, 3]]]]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [17, 88, 127, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 126, 154], [33, 64, 37], [0, 1]]
 g := ![![[133, 92, 172], [116, 75, 115], [43, 85, 46], [31, 25, 18], [56, 46, 97], [188, 64, 1], []], ![[182, 99, 59, 115], [0, 157, 34, 97], [179, 65, 135, 40], [111, 60, 33, 92], [78, 14, 186, 85], [102, 53, 139, 102], [173, 32]], ![[159, 113, 183, 87], [4, 51, 114, 155], [74, 66, 190, 58], [17, 103, 95, 28], [68, 93, 143, 175], [1, 101, 182, 87], [99, 32]]]
 h' := ![![[31, 126, 154], [129, 111, 73], [33, 134, 146], [46, 103, 115], [3, 138, 171], [51, 131, 80], [0, 0, 1], [0, 1]], ![[33, 64, 37], [179, 86, 183], [79, 162, 184], [155, 131, 111], [142, 24, 108], [40, 12, 82], [121, 66, 64], [31, 126, 154]], ![[0, 1], [158, 185, 126], [52, 86, 52], [75, 148, 156], [11, 29, 103], [20, 48, 29], [170, 125, 126], [33, 64, 37]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [177, 157], []]
 b := ![[], [57, 75, 92], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [17, 88, 127, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-8719723, 1804950, -696195]
  a := ![-5, 0, -15]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-45653, 9450, -3645]
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


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [174, 161, 149, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [63, 151, 187], [174, 41, 6], [0, 1]]
 g := ![![[176, 94, 69], [45, 6], [33, 96], [97, 24], [134, 150], [185, 6], [1]], ![[10, 166, 19, 157], [82, 126], [136, 177], [51, 185], [29, 50], [83, 185], [124, 18, 49, 170]], ![[69, 192, 127, 192], [121, 8], [141, 95], [17, 18], [161, 151], [41, 192], [63, 32, 36, 23]]]
 h' := ![![[63, 151, 187], [158, 109, 29], [123, 31, 149], [70, 163, 176], [100, 11, 88], [16, 109, 27], [19, 32, 44], [0, 1]], ![[174, 41, 6], [165, 115, 149], [99, 23, 133], [105, 13, 62], [115, 169, 68], [170, 184, 67], [152, 33, 68], [63, 151, 187]], ![[0, 1], [29, 162, 15], [168, 139, 104], [34, 17, 148], [167, 13, 37], [179, 93, 99], [128, 128, 81], [174, 41, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [88, 53], []]
 b := ![[], [48, 72, 41], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [174, 161, 149, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![32461056, -965772, -1842764]
  a := ![6, -12, 20]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![168192, -5004, -9548]
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



lemma PB233I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB233I3 : PrimesBelowBoundCertificateInterval O 137 193 233 where
  m := 11
  g := ![2, 2, 1, 2, 2, 3, 1, 2, 2, 1, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB233I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1, I167N2]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
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
    · exact ![19321, 139]
    · exact ![22201, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![26569, 163]
    · exact ![167, 167, 167]
    · exact ![5177717]
    · exact ![32041, 179]
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
      exact NI139N1
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
      exact NI167N2
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
      exact NI181N1
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N1, I157N1, I163N1, I167N0, I167N1, I167N2, I179N1, I181N1]
  Il := ![[I139N1], [I149N1], [], [I157N1], [I163N1], [I167N0, I167N1, I167N2], [], [I179N1], [I181N1], [], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
