
import IdealArithmetic.Examples.NF3_1_516059_1.RI3_1_516059_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![20, 67, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![20, 67, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![20, 67, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![20, 67, 1], ![-151, -207, 472], ![3404, -1746, 198]]]
  hmulB := by decide  
  f := ![![![-19, -67, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-20, -67, 139]], ![![0, 0, 1], ![-69, -229, 472], ![-4, -108, 198]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [78, 43, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [96, 138], [0, 1]]
 g := ![![[95, 41], [29, 69], [137], [57, 78], [118], [42], [1]], ![[0, 98], [120, 70], [137], [39, 61], [118], [42], [1]]]
 h' := ![![[96, 138], [101, 67], [21, 25], [2, 89], [59, 56], [28, 37], [61, 96], [0, 1]], ![[0, 1], [0, 72], [58, 114], [67, 50], [14, 83], [105, 102], [103, 43], [96, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69]]
 b := ![[], [12, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [78, 43, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1450, 618, -1526]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![230, 740, -1526]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![-55, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![-55, 1, 0]] 
 ![![139, 0, 0], ![84, 1, 0], ![80, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![-55, 1, 0], ![-3, -58, 7], ![50, -26, -52]]]
  hmulB := by decide  
  f := ![![![-15451, -328540, 39648], ![3892, -787296, 0]], ![![-9330, -198493, 23954], ![2364, -475658, 0]], ![![-8880, -189088, 22819], ![2272, -453120, 0]]]
  g := ![![![1, 0, 0], ![-84, 139, 0], ![-80, 0, 139]], ![![-1, 1, 0], ![31, -58, 7], ![46, -26, -52]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![20, 67, 1]] ![![139, 0, 0], ![-55, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![-7645, 139, 0]], ![![2780, 9313, 139], ![-1251, -3892, 417]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![-55, 1, 0]]], ![![![20, 67, 1]], ![![-9, -28, 3]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-27, -72, 1]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-27, -72, 1]] 
 ![![149, 0, 0], ![0, 149, 0], ![122, 77, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-27, -72, 1], ![266, 163, -501], ![-3546, 1868, -266]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-122, -77, 149]], ![![-1, -1, 1], ![412, 260, -501], ![194, 150, -266]]]
  hle1 := by decide   
  hle2 := by decide  


def P149P0 : CertificateIrreducibleZModOfList' 149 2 2 7 [106, 8, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [141, 148], [0, 1]]
 g := ![![[31, 145], [125], [75, 113], [17], [74, 64], [64], [1]], ![[63, 4], [125], [65, 36], [17], [9, 85], [64], [1]]]
 h' := ![![[141, 148], [138, 61], [96, 42], [113, 34], [53, 100], [131, 141], [43, 141], [0, 1]], ![[0, 1], [97, 88], [58, 107], [139, 115], [147, 49], [46, 8], [107, 8], [141, 148]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [101]]
 b := ![[], [53, 125]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 2
  hpos := by decide
  P := [106, 8, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-720, 6275, -6281]
  a := ![-7, -9, 16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![5138, 3288, -6281]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI149N0 B_one_repr
lemma NI149N0 : Nat.card (O ⧸ I149N0) = 22201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![54, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![54, 1, 0]] 
 ![![149, 0, 0], ![54, 1, 0], ![117, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![54, 1, 0], ![-3, 51, 7], ![50, -26, 57]]]
  hmulB := by decide  
  f := ![![![7786, -144292, -19803], ![1937, 421521, 0]], ![![2805, -52280, -7175], ![746, 152725, 0]], ![![6120, -113303, -15550], ![1504, 330993, 0]]]
  g := ![![![1, 0, 0], ![-54, 149, 0], ![-117, 0, 149]], ![![0, 1, 0], ![-24, 51, 7], ![-35, -26, 57]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-27, -72, 1]] ![![149, 0, 0], ![54, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![8046, 149, 0]], ![![-4023, -10728, 149], ![-1192, -3725, -447]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![54, 1, 0]]], ![![![-27, -72, 1]], ![![-8, -25, -3]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [64, 15, 43, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [91, 20, 13], [17, 130, 138], [0, 1]]
 g := ![![[67, 73, 58], [27, 7, 62], [123, 126, 84], [86, 8], [17, 71, 31], [108, 1], []], ![[135, 141, 24, 12], [71, 5, 143, 73], [75, 77, 18, 107], [6, 148], [96, 106, 118, 15], [99, 139], [48, 18]], ![[94, 8, 39, 98], [14, 86, 79, 110], [27, 28, 87, 31], [13, 125], [85, 0, 85, 145], [113, 98], [74, 18]]]
 h' := ![![[91, 20, 13], [84, 0, 71], [131, 75, 45], [138, 131, 50], [120, 132, 92], [34, 128, 22], [0, 0, 1], [0, 1]], ![[17, 130, 138], [124, 47, 19], [63, 124, 30], [105, 118, 49], [6, 102, 86], [44, 82, 145], [75, 107, 130], [91, 20, 13]], ![[0, 1], [88, 104, 61], [7, 103, 76], [22, 53, 52], [34, 68, 124], [110, 92, 135], [83, 44, 20], [17, 130, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [20, 40], []]
 b := ![[], [49, 111, 55], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [64, 15, 43, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-222400199, 20781228228, -22268286345]
  a := ![131, 132, -327]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1472849, 137624028, -147472095]
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


def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-59, 1, 0]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-59, 1, 0]] 
 ![![157, 0, 0], ![98, 1, 0], ![105, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-59, 1, 0], ![-3, -62, 7], ![50, -26, -56]]]
  hmulB := by decide  
  f := ![![![17300, 388021, -43806], ![-3925, 982506, 0]], ![![10834, 242187, -27342], ![-2354, 613242, 0]], ![![11599, 259504, -29297], ![-2548, 657090, 0]]]
  g := ![![![1, 0, 0], ![-98, 157, 0], ![-105, 0, 157]], ![![-1, 1, 0], ![34, -62, 7], ![54, -26, -56]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N0 : Nat.card (O ⧸ I157N0) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N0)

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := prime_ideal_of_norm_prime hp157.out _ NI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![157, 0, 0], ![-49, 1, 0]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![157, 0, 0], ![-49, 1, 0]] 
 ![![157, 0, 0], ![108, 1, 0], ![129, 0, 1]] where
  M :=![![![157, 0, 0], ![0, 157, 0], ![0, 0, 157]], ![![-49, 1, 0], ![-3, -52, 7], ![50, -26, -46]]]
  hmulB := by decide  
  f := ![![![5371, 98182, -13216], ![-942, 296416, 0]], ![![3699, 67500, -9086], ![-627, 203786, 0]], ![![4405, 80672, -10859], ![-800, 243552, 0]]]
  g := ![![![1, 0, 0], ![-108, 157, 0], ![-129, 0, 157]], ![![-1, 1, 0], ![30, -52, 7], ![56, -26, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-59, 1, 0]] ![![157, 0, 0], ![-49, 1, 0]]
  ![![157, 0, 0], ![-36, 29, 1]] where
 M := ![![![24649, 0, 0], ![-7693, 157, 0]], ![![-9263, 157, 0], ![2888, -111, 7]]]
 hmul := by decide  
 g := ![![![![157, 0, 0], ![0, 0, 0]], ![![-13, -28, -1], ![157, 0, 0]]], ![![![-23, -28, -1], ![157, 0, 0]], ![![20, -2, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI157N1 : IdealMulLeCertificate' Table 
  ![![157, 0, 0], ![-36, 29, 1]] ![![157, 0, 0], ![-49, 1, 0]]
  ![![157, 0, 0]] where
 M := ![![![24649, 0, 0], ![-7693, 157, 0]], ![![-5652, 4553, 157], ![1727, -1570, 157]]]
 hmul := by decide  
 g := ![![![![157, 0, 0]], ![![-49, 1, 0]]], ![![![-36, 29, 1]], ![![11, -10, 1]]]]
 hle2 := by decide  


def PBC157 : ContainsPrimesAboveP 157 ![I157N0, I157N1, I157N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI157N0
    exact isPrimeI157N1
    exact isPrimeI157N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 157 (by decide) (𝕀 ⊙ MulI157N0 ⊙ MulI157N1)
instance hp163 : Fact (Nat.Prime 163) := {out := by norm_num}

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![56, 29, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![56, 29, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![56, 29, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![56, 29, 1], ![-37, -57, 206], ![1504, -758, 120]]]
  hmulB := by decide  
  f := ![![![-55, -29, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-56, -29, 163]], ![![0, 0, 1], ![-71, -37, 206], ![-32, -26, 120]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [81, 71, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [92, 162], [0, 1]]
 g := ![![[21, 161], [52, 22], [34], [46], [16], [129, 151], [1]], ![[0, 2], [120, 141], [34], [46], [16], [3, 12], [1]]]
 h' := ![![[92, 162], [26, 145], [136, 115], [49, 94], [134, 32], [146, 4], [82, 92], [0, 1]], ![[0, 1], [0, 18], [121, 48], [58, 69], [144, 131], [25, 159], [70, 71], [92, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [33]]
 b := ![[], [56, 98]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [81, 71, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1459, 6120, -7568]
  a := ![7, 8, -16]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![2609, 1384, -7568]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-43, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-43, 1, 0]] 
 ![![163, 0, 0], ![120, 1, 0], ![43, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-43, 1, 0], ![-3, -46, 7], ![50, -26, -40]]]
  hmulB := by decide  
  f := ![![![19272, 308035, -46872], ![-3097, 1091448, 0]], ![![14186, 226748, -34503], ![-2281, 803427, 0]], ![![5117, 81260, -12365], ![-692, 287928, 0]]]
  g := ![![![1, 0, 0], ![-120, 163, 0], ![-43, 0, 163]], ![![-1, 1, 0], ![32, -46, 7], ![30, -26, -40]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![56, 29, 1]] ![![163, 0, 0], ![-43, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-7009, 163, 0]], ![![9128, 4727, 163], ![-2445, -1304, 163]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-43, 1, 0]]], ![![![56, 29, 1]], ![![-15, -8, 1]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![84, 46, 1]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![167, 0, 0], ![84, 46, 1]] 
 ![![167, 0, 0], ![0, 167, 0], ![84, 46, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![84, 46, 1], ![-88, -80, 325], ![2354, -1200, 199]]]
  hmulB := by decide  
  f := ![![![-83, -46, -1], ![167, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-84, -46, 167]], ![![0, 0, 1], ![-164, -90, 325], ![-86, -62, 199]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 2 2 7 [149, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 166], [0, 1]]
 g := ![![[5, 132], [123, 84], [111, 75], [72], [141], [112, 84], [1]], ![[28, 35], [1, 83], [14, 92], [72], [141], [157, 83], [1]]]
 h' := ![![[90, 166], [43, 93], [161, 77], [60, 24], [10, 78], [12, 59], [18, 90], [0, 1]], ![[0, 1], [63, 74], [77, 90], [49, 143], [16, 89], [145, 108], [102, 77], [90, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [137]]
 b := ![[], [7, 152]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 2
  hpos := by decide
  P := [149, 77, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1623, 686, -1764]
  a := ![3, 2, -7]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![897, 490, -1764]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![167, 0, 0], ![9, 1, 0]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![167, 0, 0], ![9, 1, 0]] 
 ![![167, 0, 0], ![9, 1, 0], ![135, 0, 1]] where
  M :=![![![167, 0, 0], ![0, 167, 0], ![0, 0, 167]], ![![9, 1, 0], ![-3, 6, 7], ![50, -26, 12]]]
  hmulB := by decide  
  f := ![![![13615, -27304, -31850], ![668, 759850, 0]], ![![726, -1471, -1715], ![168, 40915, 0]], ![![11007, -22072, -25747], ![524, 614250, 0]]]
  g := ![![![1, 0, 0], ![-9, 167, 0], ![-135, 0, 167]], ![![0, 1, 0], ![-6, 6, 7], ![-8, -26, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI167N1 : Nat.card (O ⧸ I167N1) = 167 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI167N1)

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := prime_ideal_of_norm_prime hp167.out _ NI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![167, 0, 0], ![84, 46, 1]] ![![167, 0, 0], ![9, 1, 0]]
  ![![167, 0, 0]] where
 M := ![![![27889, 0, 0], ![1503, 167, 0]], ![![14028, 7682, 167], ![668, 334, 334]]]
 hmul := by decide  
 g := ![![![![167, 0, 0]], ![![9, 1, 0]]], ![![![84, 46, 1]], ![![4, 2, 2]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![13, 1, 0]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![13, 1, 0]] 
 ![![173, 0, 0], ![13, 1, 0], ![154, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![13, 1, 0], ![-3, 10, 7], ![50, -26, 16]]]
  hmulB := by decide  
  f := ![![![-479, 1600, 1120], ![0, -27680, 0]], ![![-36, 120, 84], ![1, -2076, 0]], ![![-430, 1424, 997], ![48, -24640, 0]]]
  g := ![![![1, 0, 0], ![-13, 173, 0], ![-154, 0, 173]], ![![0, 1, 0], ![-7, 10, 7], ![-12, -26, 16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N0 : Nat.card (O ⧸ I173N0) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N0)

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := prime_ideal_of_norm_prime hp173.out _ NI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![80, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![80, 1, 0]] 
 ![![173, 0, 0], ![80, 1, 0], ![34, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![80, 1, 0], ![-3, 77, 7], ![50, -26, 83]]]
  hmulB := by decide  
  f := ![![![29680, -866532, -78771], ![8823, 1946769, 0]], ![![13689, -400655, -36421], ![4153, 900119, 0]], ![![5840, -170301, -15481], ![1719, 382602, 0]]]
  g := ![![![1, 0, 0], ![-80, 173, 0], ![-34, 0, 173]], ![![0, 1, 0], ![-37, 77, 7], ![-4, -26, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![13, 1, 0]] ![![173, 0, 0], ![80, 1, 0]]
  ![![173, 0, 0], ![74, -86, 1]] where
 M := ![![![29929, 0, 0], ![13840, 173, 0]], ![![2249, 173, 0], ![1037, 90, 7]]]
 hmul := by decide  
 g := ![![![![99, 86, -1], ![173, 0, 0]], ![![6, 87, -1], ![173, 0, 0]]], ![![![-61, 87, -1], ![173, 0, 0]], ![![3, 4, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![74, -86, 1]] ![![173, 0, 0], ![80, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![13840, 173, 0]], ![![12802, -14878, 173], ![6228, -6574, -519]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![80, 1, 0]]], ![![![74, -86, 1]], ![![36, -38, -3]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![80, 1, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0], ![80, 1, 0]] 
 ![![179, 0, 0], ![80, 1, 0], ![168, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![80, 1, 0], ![-3, 77, 7], ![50, -26, 83]]]
  hmulB := by decide  
  f := ![![![9719, -282298, -25662], ![2864, 656214, 0]], ![![4354, -126133, -11466], ![1254, 293202, 0]], ![![9128, -264950, -24085], ![2674, 615888, 0]]]
  g := ![![![1, 0, 0], ![-80, 179, 0], ![-168, 0, 179]], ![![0, 1, 0], ![-41, 77, 7], ![-66, -26, 83]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N0 : Nat.card (O ⧸ I179N0) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N0)

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := prime_ideal_of_norm_prime hp179.out _ NI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-46, 1, 0]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-46, 1, 0]] 
 ![![179, 0, 0], ![133, 1, 0], ![10, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-46, 1, 0], ![-3, -49, 7], ![50, -26, -43]]]
  hmulB := by decide  
  f := ![![![-1587, -27442, 3920], ![358, -100240, 0]], ![![-1155, -20386, 2912], ![359, -74464, 0]], ![![-46, -1534, 219], ![186, -5600, 0]]]
  g := ![![![1, 0, 0], ![-133, 179, 0], ![-10, 0, 179]], ![![-1, 1, 0], ![36, -49, 7], ![22, -26, -43]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0], ![-34, 1, 0]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![179, 0, 0], ![-34, 1, 0]] 
 ![![179, 0, 0], ![145, 1, 0], ![50, 0, 1]] where
  M :=![![![179, 0, 0], ![0, 179, 0], ![0, 0, 179]], ![![-34, 1, 0], ![-3, -37, 7], ![50, -26, -31]]]
  hmulB := by decide  
  f := ![![![14395, 181309, -34300], ![-1611, 877100, 0]], ![![11670, 146860, -27783], ![-1252, 710451, 0]], ![![4020, 50645, -9581], ![-455, 245000, 0]]]
  g := ![![![1, 0, 0], ![-145, 179, 0], ![-50, 0, 179]], ![![-1, 1, 0], ![28, -37, 7], ![30, -26, -31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![80, 1, 0]] ![![179, 0, 0], ![-46, 1, 0]]
  ![![179, 0, 0], ![62, 30, 1]] where
 M := ![![![32041, 0, 0], ![-8234, 179, 0]], ![![14320, 179, 0], ![-3683, 31, 7]]]
 hmul := by decide  
 g := ![![![![117, -30, -1], ![179, 0, 0]], ![![-46, 1, 0], ![0, 0, 0]]], ![![![18, -29, -1], ![179, 0, 0]], ![![-23, -1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![179, 0, 0], ![62, 30, 1]] ![![179, 0, 0], ![-34, 1, 0]]
  ![![179, 0, 0]] where
 M := ![![![32041, 0, 0], ![-6086, 179, 0]], ![![11098, 5370, 179], ![-2148, -1074, 179]]]
 hmul := by decide  
 g := ![![![![179, 0, 0]], ![![-34, 1, 0]]], ![![![62, 30, 1]], ![![-12, -6, 1]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![5, -61, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![5, -61, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![5, 120, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![5, -61, 1], ![233, 162, -424], ![-2996, 1582, -201]]]
  hmulB := by decide  
  f := ![![![-4, 61, -1], ![181, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -120, 181]], ![![0, -1, 1], ![13, 282, -424], ![-11, 142, -201]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [22, 33, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 180], [0, 1]]
 g := ![![[92, 9], [59], [2, 169], [46], [49, 145], [86, 3], [1]], ![[157, 172], [59], [36, 12], [46], [151, 36], [168, 178], [1]]]
 h' := ![![[148, 180], [95, 3], [137, 56], [138, 13], [8, 107], [99, 114], [159, 148], [0, 1]], ![[0, 1], [177, 178], [99, 125], [71, 168], [97, 74], [138, 67], [162, 33], [148, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [98]]
 b := ![[], [175, 49]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [22, 33, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23870, -9578, -656]
  a := ![-5, 14, 12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![150, 382, -656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![62, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![62, 1, 0]] 
 ![![181, 0, 0], ![62, 1, 0], ![20, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![62, 1, 0], ![-3, 59, 7], ![50, -26, 65]]]
  hmulB := by decide  
  f := ![![![31090, -659010, -78183], ![7059, 2021589, 0]], ![![10607, -225689, -26775], ![2535, 692325, 0]], ![![3422, -72819, -8639], ![819, 223380, 0]]]
  g := ![![![1, 0, 0], ![-62, 181, 0], ![-20, 0, 181]], ![![0, 1, 0], ![-21, 59, 7], ![2, -26, 65]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![5, -61, 1]] ![![181, 0, 0], ![62, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![11222, 181, 0]], ![![905, -11041, 181], ![543, -3620, -362]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![62, 1, 0]]], ![![![5, -61, 1]], ![![3, -20, -2]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![18, 1, 0]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![18, 1, 0]] 
 ![![191, 0, 0], ![18, 1, 0], ![152, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![18, 1, 0], ![-3, 15, 7], ![50, -26, 21]]]
  hmulB := by decide  
  f := ![![![26731, -134560, -62790], ![1910, 1713270, 0]], ![![2517, -12676, -5915], ![192, 161395, 0]], ![![21262, -107085, -49969], ![1635, 1363440, 0]]]
  g := ![![![1, 0, 0], ![-18, 191, 0], ![-152, 0, 191]], ![![0, 1, 0], ![-7, 15, 7], ![-14, -26, 21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N0 : Nat.card (O ⧸ I191N0) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N0)

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := prime_ideal_of_norm_prime hp191.out _ NI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![57, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![57, 1, 0]] 
 ![![191, 0, 0], ![57, 1, 0], ![51, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![57, 1, 0], ![-3, 54, 7], ![50, -26, 60]]]
  hmulB := by decide  
  f := ![![![4552, -87053, -11284], ![955, 307892, 0]], ![![1329, -25976, -3367], ![383, 91871, 0]], ![![1188, -23245, -3013], ![347, 82212, 0]]]
  g := ![![![1, 0, 0], ![-57, 191, 0], ![-51, 0, 191]], ![![0, 1, 0], ![-18, 54, 7], ![-8, -26, 60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-75, 1, 0]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-75, 1, 0]] 
 ![![191, 0, 0], ![116, 1, 0], ![37, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-75, 1, 0], ![-3, -78, 7], ![50, -26, -72]]]
  hmulB := by decide  
  f := ![![![-2387, -69892, 6272], ![764, -171136, 0]], ![![-1481, -42434, 3808], ![383, -103904, 0]], ![![-409, -13540, 1215], ![284, -33152, 0]]]
  g := ![![![1, 0, 0], ![-116, 191, 0], ![-37, 0, 191]], ![![-1, 1, 0], ![46, -78, 7], ![30, -26, -72]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![18, 1, 0]] ![![191, 0, 0], ![57, 1, 0]]
  ![![191, 0, 0], ![37, -17, 1]] where
 M := ![![![36481, 0, 0], ![10887, 191, 0]], ![![3438, 191, 0], ![1023, 72, 7]]]
 hmul := by decide  
 g := ![![![![154, 17, -1], ![191, 0, 0]], ![![20, 18, -1], ![191, 0, 0]]], ![![![-19, 18, -1], ![191, 0, 0]], ![![4, 1, 0], ![7, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![37, -17, 1]] ![![191, 0, 0], ![-75, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-14325, 191, 0]], ![![7067, -3247, 191], ![-2674, 1337, -191]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-75, 1, 0]]], ![![![37, -17, 1]], ![![-14, 7, -1]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![193, 0, 0]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![193, 0, 0]] 
 ![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]] where
  M :=![![![193, 0, 0], ![0, 193, 0], ![0, 0, 193]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 3 2 7 [51, 106, 169, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [16, 117, 41], [8, 75, 152], [0, 1]]
 g := ![![[117, 62, 54], [155, 190], [47, 189], [161, 95], [144, 165], [51, 190], [1]], ![[56, 9, 27, 30], [55, 108], [128, 24], [106, 184], [112, 191], [32, 18], [48, 113, 124, 20]], ![[58, 41, 14, 115], [10, 84], [169, 72], [190, 25], [110, 83], [26, 169], [150, 125, 44, 173]]]
 h' := ![![[16, 117, 41], [56, 143, 132], [137, 136, 169], [188, 49, 31], [183, 60, 148], [0, 155, 101], [142, 87, 24], [0, 1]], ![[8, 75, 152], [76, 10, 130], [76, 161, 109], [106, 15, 88], [109, 92, 50], [113, 184, 34], [104, 68, 156], [16, 117, 41]], ![[0, 1], [178, 40, 124], [130, 89, 108], [185, 129, 74], [178, 41, 188], [34, 47, 58], [3, 38, 13], [8, 75, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157, 134], []]
 b := ![[], [151, 140, 105], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 3
  hpos := by decide
  P := [51, 106, 169, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2148669, 2542968, -1578740]
  a := ![5, 8, -12]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-11133, 13176, -8180]
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



lemma PB204I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB204I3 : PrimesBelowBoundCertificateInterval O 137 193 204 where
  m := 11
  g := ![2, 2, 1, 3, 2, 2, 3, 3, 2, 3, 1]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB204I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1]
    · exact ![I151N0]
    · exact ![I157N0, I157N1, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2]
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
    · exact ![157, 157, 157]
    · exact ![26569, 163]
    · exact ![27889, 167]
    · exact ![173, 173, 173]
    · exact ![179, 179, 179]
    · exact ![32761, 181]
    · exact ![191, 191, 191]
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
      exact NI173N1
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
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
  β := ![I139N1, I149N1, I157N0, I157N1, I163N1, I167N1, I173N0, I173N1, I179N0, I179N1, I179N2, I181N1, I191N0, I191N1, I191N2]
  Il := ![[I139N1], [I149N1], [], [I157N0, I157N1, I157N1], [I163N1], [I167N1], [I173N0, I173N1, I173N1], [I179N0, I179N1, I179N2], [I181N1], [I191N0, I191N1, I191N2], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
