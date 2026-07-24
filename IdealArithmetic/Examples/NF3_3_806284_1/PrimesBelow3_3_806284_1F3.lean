
import IdealArithmetic.Examples.NF3_3_806284_1.RI3_3_806284_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![5, -17, 1]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![139, 0, 0], ![5, -17, 1]] 
 ![![139, 0, 0], ![0, 139, 0], ![5, 122, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![5, -17, 1], ![103, 39, -35], ![-1854, -841, 74]]]
  hmulB := by decide  
  f := ![![![-4, 17, -1], ![139, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-5, -122, 139]], ![![0, -1, 1], ![2, 31, -35], ![-16, -71, 74]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [73, 18, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [121, 138], [0, 1]]
 g := ![![[25, 127], [92, 64], [57], [32, 83], [49], [46], [1]], ![[102, 12], [52, 75], [57], [67, 56], [49], [46], [1]]]
 h' := ![![[121, 138], [95, 108], [43, 8], [27, 14], [106, 19], [25, 132], [66, 121], [0, 1]], ![[0, 1], [97, 31], [38, 131], [53, 125], [42, 120], [12, 7], [112, 18], [121, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [52]]
 b := ![[], [95, 26]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [73, 18, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![382, 814, 410]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-12, -354, 410]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![139, 0, 0], ![35, 1, 0]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![139, 0, 0], ![35, 1, 0]] 
 ![![139, 0, 0], ![35, 1, 0], ![65, 0, 1]] where
  M :=![![![139, 0, 0], ![0, 139, 0], ![0, 0, 139]], ![![35, 1, 0], ![0, 36, 2], ![103, 51, 34]]]
  hmulB := by decide  
  f := ![![![71, 2, 0], ![-278, 0, 0]], ![![-35, -1, 0], ![140, 0, 0]], ![![5, -18, -1], ![-18, 70, 0]]]
  g := ![![![1, 0, 0], ![-35, 139, 0], ![-65, 0, 139]], ![![0, 1, 0], ![-10, 36, 2], ![-28, 51, 34]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![139, 0, 0], ![5, -17, 1]] ![![139, 0, 0], ![35, 1, 0]]
  ![![139, 0, 0]] where
 M := ![![![19321, 0, 0], ![4865, 139, 0]], ![![695, -2363, 139], ![278, -556, 0]]]
 hmul := by decide  
 g := ![![![![139, 0, 0]], ![![35, 1, 0]]], ![![![5, -17, 1]], ![![2, -4, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![63, 1, 0]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![149, 0, 0], ![63, 1, 0]] 
 ![![149, 0, 0], ![63, 1, 0], ![70, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![63, 1, 0], ![0, 64, 2], ![103, 51, 62]]]
  hmulB := by decide  
  f := ![![![7372, 117, 0], ![-17433, 0, 0]], ![![3150, 50, 0], ![-7449, 0, 0]], ![![3416, 22, -1], ![-8078, 75, 0]]]
  g := ![![![1, 0, 0], ![-63, 149, 0], ![-70, 0, 149]], ![![0, 1, 0], ![-28, 64, 2], ![-50, 51, 62]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-58, 1, 0]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-58, 1, 0]] 
 ![![149, 0, 0], ![91, 1, 0], ![135, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-58, 1, 0], ![0, -57, 2], ![103, 51, -59]]]
  hmulB := by decide  
  f := ![![![2205, -38, 0], ![5662, 0, 0]], ![![1451, -25, 0], ![3726, 0, 0]], ![![2071, -7, -1], ![5318, 75, 0]]]
  g := ![![![1, 0, 0], ![-91, 149, 0], ![-135, 0, 149]], ![![-1, 1, 0], ![33, -57, 2], ![23, 51, -59]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![149, 0, 0], ![-5, 1, 0]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![149, 0, 0], ![-5, 1, 0]] 
 ![![149, 0, 0], ![144, 1, 0], ![139, 0, 1]] where
  M :=![![![149, 0, 0], ![0, 149, 0], ![0, 0, 149]], ![![-5, 1, 0], ![0, -4, 2], ![103, 51, -6]]]
  hmulB := by decide  
  f := ![![![181, -36, 0], ![5364, 0, 0]], ![![176, -35, 0], ![5216, 0, 0]], ![![171, -32, -1], ![5068, 75, 0]]]
  g := ![![![1, 0, 0], ![-144, 149, 0], ![-139, 0, 149]], ![![-1, 1, 0], ![2, -4, 2], ![-43, 51, -6]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![63, 1, 0]] ![![149, 0, 0], ![-58, 1, 0]]
  ![![149, 0, 0], ![-39, 3, 1]] where
 M := ![![![22201, 0, 0], ![-8642, 149, 0]], ![![9387, 149, 0], ![-3654, 6, 2]]]
 hmul := by decide  
 g := ![![![![149, 0, 0], ![0, 0, 0]], ![![-19, -2, -1], ![149, 0, 0]]], ![![![63, 1, 0], ![0, 0, 0]], ![![15, -3, -1], ![151, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![149, 0, 0], ![-39, 3, 1]] ![![149, 0, 0], ![-5, 1, 0]]
  ![![149, 0, 0]] where
 M := ![![![22201, 0, 0], ![-745, 149, 0]], ![![-5811, 447, 149], ![298, 0, 0]]]
 hmul := by decide  
 g := ![![![![149, 0, 0]], ![![-5, 1, 0]]], ![![![-39, 3, 1]], ![![2, 0, 0]]]]
 hle2 := by decide  


def PBC149 : ContainsPrimesAboveP 149 ![I149N0, I149N1, I149N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI149N0
    exact isPrimeI149N1
    exact isPrimeI149N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 149 (by decide) (𝕀 ⊙ MulI149N0 ⊙ MulI149N1)
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [128, 15, 44, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [37, 125, 142], [70, 25, 9], [0, 1]]
 g := ![![[41, 30, 1], [10, 90, 72], [148, 41, 55], [31, 86], [48, 6, 103], [107, 1], []], ![[34, 15, 135, 129], [110, 73, 68, 142], [12, 91, 56, 150], [114, 55], [3, 36, 147, 147], [25, 21], [75, 81]], ![[14, 128, 119, 74], [114, 142, 146, 38], [43, 15, 106, 8], [85, 4], [2, 27, 121, 125], [90, 72], [57, 81]]]
 h' := ![![[37, 125, 142], [79, 37, 1], [82, 22, 26], [53, 47, 31], [47, 84, 29], [45, 79, 109], [0, 0, 1], [0, 1]], ![[70, 25, 9], [12, 117, 145], [102, 0, 150], [9, 64, 50], [16, 115, 120], [11, 42, 51], [74, 22, 25], [37, 125, 142]], ![[0, 1], [122, 148, 5], [28, 129, 126], [37, 40, 70], [14, 103, 2], [54, 30, 142], [20, 129, 125], [70, 25, 9]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [106, 65], []]
 b := ![[], [70, 73, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [128, 15, 44, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![51038, 330086, 199622]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![338, 2186, 1322]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [10, 150, 138, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [79, 62, 8], [97, 94, 149], [0, 1]]
 g := ![![[102, 101, 82], [34, 30], [8, 79, 49], [3, 110, 51], [37, 79, 90], [19, 1], []], ![[75, 101, 28, 59], [0, 14], [128, 130, 136, 59], [115, 31, 139, 62], [12, 156, 10, 38], [3, 44], [10, 64]], ![[152, 96, 98, 134], [57, 140], [76, 153, 120, 6], [2, 149, 2, 96], [125, 151, 138, 137], [66, 76], [26, 64]]]
 h' := ![![[79, 62, 8], [94, 68, 32], [77, 9, 40], [127, 16, 150], [101, 87, 88], [124, 123, 54], [0, 0, 1], [0, 1]], ![[97, 94, 149], [76, 49, 98], [95, 20, 64], [9, 152, 98], [80, 97, 19], [137, 133, 94], [18, 120, 94], [79, 62, 8]], ![[0, 1], [59, 40, 27], [1, 128, 53], [122, 146, 66], [78, 130, 50], [90, 58, 9], [43, 37, 62], [97, 94, 149]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17, 101], []]
 b := ![[], [133, 47, 7], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [10, 150, 138, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![301754, -4082, -157]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1922, -26, -1]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![33, 7, 1]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0], ![33, 7, 1]] 
 ![![163, 0, 0], ![0, 163, 0], ![33, 7, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![33, 7, 1], ![103, 91, 13], ![618, 383, 78]]]
  hmulB := by decide  
  f := ![![![-32, -7, -1], ![163, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-33, -7, 163]], ![![0, 0, 1], ![-2, 0, 13], ![-12, -1, 78]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 2 2 7 [17, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 162], [0, 1]]
 g := ![![[92, 22], [28, 88], [97], [77], [69], [2, 118], [1]], ![[77, 141], [131, 75], [97], [77], [69], [129, 45], [1]]]
 h' := ![![[66, 162], [13, 48], [115, 67], [121, 89], [146, 27], [129, 45], [146, 66], [0, 1]], ![[0, 1], [84, 115], [136, 96], [127, 74], [135, 136], [2, 118], [101, 97], [66, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [26]]
 b := ![[], [60, 13]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 2
  hpos := by decide
  P := [17, 97, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-400, 1476, 793]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-163, -25, 793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0], ![-13, 1, 0]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![163, 0, 0], ![-13, 1, 0]] 
 ![![163, 0, 0], ![150, 1, 0], ![85, 0, 1]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]], ![![-13, 1, 0], ![0, -12, 2], ![103, 51, -14]]]
  hmulB := by decide  
  f := ![![![1821, -140, 0], ![22820, 0, 0]], ![![1678, -129, 0], ![21028, 0, 0]], ![![963, -68, -1], ![12068, 82, 0]]]
  g := ![![![1, 0, 0], ![-150, 163, 0], ![-85, 0, 163]], ![![-1, 1, 0], ![10, -12, 2], ![-39, 51, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI163N1 : Nat.card (O ⧸ I163N1) = 163 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI163N1)

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := prime_ideal_of_norm_prime hp163.out _ NI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![163, 0, 0], ![33, 7, 1]] ![![163, 0, 0], ![-13, 1, 0]]
  ![![163, 0, 0]] where
 M := ![![![26569, 0, 0], ![-2119, 163, 0]], ![![5379, 1141, 163], ![-326, 0, 0]]]
 hmul := by decide  
 g := ![![![![163, 0, 0]], ![![-13, 1, 0]]], ![![![33, 7, 1]], ![![-2, 0, 0]]]]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [139, 1, 142, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [120, 35, 64], [72, 131, 103], [0, 1]]
 g := ![![[52, 152, 3], [160, 66, 63], [157, 73, 157], [28, 12], [97, 7], [123, 25, 1], []], ![[131, 97, 70, 65], [47, 16, 33, 77], [147, 80, 94, 58], [35, 47], [65, 14], [12, 82, 8, 112], [0, 88]], ![[123, 165, 134, 111], [33, 40, 123, 151], [89, 111, 78, 59], [3, 157], [92, 36], [164, 153, 140, 90], [128, 88]]]
 h' := ![![[120, 35, 64], [138, 95, 105], [54, 58, 118], [141, 60, 18], [5, 42, 124], [104, 76, 72], [0, 0, 1], [0, 1]], ![[72, 131, 103], [164, 95, 129], [142, 86, 132], [9, 91, 19], [71, 81, 61], [103, 135, 101], [38, 9, 131], [120, 35, 64]], ![[0, 1], [100, 144, 100], [114, 23, 84], [128, 16, 130], [85, 44, 149], [101, 123, 161], [84, 158, 35], [72, 131, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [112, 96], []]
 b := ![[], [150, 107, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [139, 1, 142, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-170841, -95190, -7348]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1023, -570, -44]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![18, 37, 1]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![173, 0, 0], ![18, 37, 1]] 
 ![![173, 0, 0], ![0, 173, 0], ![18, 37, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![18, 37, 1], ![103, 106, 73], ![3708, 1913, 33]]]
  hmulB := by decide  
  f := ![![![-17, -37, -1], ![173, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-18, -37, 173]], ![![0, 0, 1], ![-7, -15, 73], ![18, 4, 33]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [84, 161, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [12, 172], [0, 1]]
 g := ![![[74, 138], [14], [73, 43], [163, 51], [15], [58, 144], [1]], ![[0, 35], [14], [70, 130], [83, 122], [15], [56, 29], [1]]]
 h' := ![![[12, 172], [82, 22], [96, 138], [148, 40], [43, 33], [145, 154], [89, 12], [0, 1]], ![[0, 1], [0, 151], [22, 35], [109, 133], [93, 140], [90, 19], [60, 161], [12, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155]]
 b := ![[], [54, 164]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [84, 161, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![41343, 57966, 26315]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-2499, -5293, 26315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![173, 0, 0], ![-73, 1, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![173, 0, 0], ![-73, 1, 0]] 
 ![![173, 0, 0], ![100, 1, 0], ![140, 0, 1]] where
  M :=![![![173, 0, 0], ![0, 173, 0], ![0, 0, 173]], ![![-73, 1, 0], ![0, -72, 2], ![103, 51, -74]]]
  hmulB := by decide  
  f := ![![![9929, -136, 0], ![23528, 0, 0]], ![![5768, -79, 0], ![13668, 0, 0]], ![![8046, -74, -1], ![19066, 87, 0]]]
  g := ![![![1, 0, 0], ![-100, 173, 0], ![-140, 0, 173]], ![![-1, 1, 0], ![40, -72, 2], ![31, 51, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![173, 0, 0], ![18, 37, 1]] ![![173, 0, 0], ![-73, 1, 0]]
  ![![173, 0, 0]] where
 M := ![![![29929, 0, 0], ![-12629, 173, 0]], ![![3114, 6401, 173], ![-1211, -2595, 0]]]
 hmul := by decide  
 g := ![![![![173, 0, 0]], ![![-73, 1, 0]]], ![![![18, 37, 1]], ![![-7, -15, 0]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [53, 143, 79, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [8, 55, 66], [92, 123, 113], [0, 1]]
 g := ![![[37, 7, 22], [173, 161, 126], [82, 15], [54, 42], [165, 85, 57], [12, 100, 1], []], ![[24, 152, 83, 29], [43, 79, 87, 168], [90, 146], [135, 14], [34, 9], [74, 61, 72, 52], [14, 60]], ![[171, 13, 102, 58], [24, 112, 120, 73], [25, 121], [146, 61], [103, 40, 83, 176], [168, 176, 173, 114], [146, 60]]]
 h' := ![![[8, 55, 66], [139, 34, 102], [141, 177, 22], [141, 92, 146], [26, 138, 20], [80, 144, 93], [0, 0, 1], [0, 1]], ![[92, 123, 113], [170, 5, 112], [66, 116, 68], [160, 67, 44], [100, 131, 112], [112, 23], [38, 173, 123], [8, 55, 66]], ![[0, 1], [170, 140, 144], [177, 65, 89], [41, 20, 168], [34, 89, 47], [117, 12, 86], [10, 6, 55], [92, 123, 113]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [133, 85], []]
 b := ![[], [14, 8, 175], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [53, 143, 79, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53342, 37948, 8055]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![298, 212, 45]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![-33, -23, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0], ![-33, -23, 1]] 
 ![![181, 0, 0], ![0, 181, 0], ![148, 158, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![-33, -23, 1], ![103, -5, -47], ![-2472, -1147, 42]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 1, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-148, -158, 181]], ![![-1, -1, 1], ![39, 41, -47], ![-48, -43, 42]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [163, 97, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [84, 180], [0, 1]]
 g := ![![[65, 94], [143], [107, 129], [44], [7, 100], [57, 178], [1]], ![[178, 87], [143], [83, 52], [44], [81, 81], [167, 3], [1]]]
 h' := ![![[84, 180], [102, 53], [116, 163], [16, 55], [126, 15], [121, 171], [18, 84], [0, 1]], ![[0, 1], [29, 128], [52, 18], [111, 126], [119, 166], [5, 10], [15, 97], [84, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [97]]
 b := ![[], [135, 139]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [163, 97, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![678, 2480, 1773]
  a := ![0, 3, 5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1446, -1534, 1773]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0], ![47, 1, 0]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![181, 0, 0], ![47, 1, 0]] 
 ![![181, 0, 0], ![47, 1, 0], ![139, 0, 1]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]], ![![47, 1, 0], ![0, 48, 2], ![103, 51, 46]]]
  hmulB := by decide  
  f := ![![![3103, 66, 0], ![-11946, 0, 0]], ![![799, 17, 0], ![-3076, 0, 0]], ![![2357, 26, -1], ![-9074, 91, 0]]]
  g := ![![![1, 0, 0], ![-47, 181, 0], ![-139, 0, 181]], ![![0, 1, 0], ![-14, 48, 2], ![-48, 51, 46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![181, 0, 0], ![-33, -23, 1]] ![![181, 0, 0], ![47, 1, 0]]
  ![![181, 0, 0]] where
 M := ![![![32761, 0, 0], ![8507, 181, 0]], ![![-5973, -4163, 181], ![-1448, -1086, 0]]]
 hmul := by decide  
 g := ![![![![181, 0, 0]], ![![47, 1, 0]]], ![![![-33, -23, 1]], ![![-8, -6, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-82, 22, 1]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-82, 22, 1]] 
 ![![191, 0, 0], ![0, 191, 0], ![109, 22, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-82, 22, 1], ![103, -9, 43], ![2163, 1148, -52]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![-109, -22, 191]], ![![-1, 0, 1], ![-24, -5, 43], ![41, 12, -52]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [113, 9, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [182, 190], [0, 1]]
 g := ![![[66, 54], [122, 153], [88, 65], [184, 177], [16, 180], [159, 81], [1]], ![[153, 137], [82, 38], [76, 126], [119, 14], [115, 11], [3, 110], [1]]]
 h' := ![![[182, 190], [157, 93], [179, 41], [27, 16], [102, 122], [178, 84], [78, 182], [0, 1]], ![[0, 1], [84, 98], [1, 150], [74, 175], [150, 69], [186, 107], [159, 9], [182, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [86, 104]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [113, 9, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![6315, 5792, 1826]
  a := ![2, -8, -6]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1009, -180, 1826]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![191, 0, 0], ![-43, 1, 0]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![191, 0, 0], ![-43, 1, 0]] 
 ![![191, 0, 0], ![148, 1, 0], ![52, 0, 1]] where
  M :=![![![191, 0, 0], ![0, 191, 0], ![0, 0, 191]], ![![-43, 1, 0], ![0, -42, 2], ![103, 51, -44]]]
  hmulB := by decide  
  f := ![![![3785, -88, 0], ![16808, 0, 0]], ![![2968, -69, 0], ![13180, 0, 0]], ![![1080, -4, -1], ![4796, 96, 0]]]
  g := ![![![1, 0, 0], ![-148, 191, 0], ![-52, 0, 191]], ![![-1, 1, 0], ![32, -42, 2], ![-27, 51, -44]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![191, 0, 0], ![-82, 22, 1]] ![![191, 0, 0], ![-43, 1, 0]]
  ![![191, 0, 0]] where
 M := ![![![36481, 0, 0], ![-8213, 191, 0]], ![![-15662, 4202, 191], ![3629, -955, 0]]]
 hmul := by decide  
 g := ![![![![191, 0, 0]], ![![-43, 1, 0]]], ![![![-82, 22, 1]], ![![19, -5, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![349, 226, 38]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![349, 226, 38]] 
 ![![193, 0, 0], ![0, 193, 0], ![126, 138, 1]] where
  M :=![![![349, 226, 38], ![3914, 2513, 414], ![19364, 12514, 2099]]]
  hmulB := by decide  
  f := ![![![-487, -6, 10]], ![![1030, 17, -22]], ![![410, 8, -9]]]
  g := ![![![-23, -26, 38], ![-250, -283, 414], ![-1270, -1436, 2099]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [91, 104, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [89, 192], [0, 1]]
 g := ![![[139, 83], [62], [18], [72], [6], [134], [89, 1]], ![[192, 110], [62], [18], [72], [6], [134], [178, 192]]]
 h' := ![![[89, 192], [149, 135], [1, 107], [148, 156], [36, 74], [14, 149], [7, 110], [0, 1]], ![[0, 1], [5, 58], [67, 86], [136, 37], [60, 119], [151, 44], [147, 83], [89, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [180]]
 b := ![[], [48, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [91, 104, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1509, 26, 182]
  a := ![13, 0, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-111, -130, 182]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![487, 6, -10]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![487, 6, -10]] 
 ![![193, 0, 0], ![111, 1, 0], ![153, 0, 1]] where
  M :=![![![487, 6, -10], ![-1030, -17, 22], ![1648, 46, -39]]]
  hmulB := by decide  
  f := ![![![-349, -226, -38]], ![![-221, -143, -24]], ![![-377, -244, -41]]]
  g := ![![![7, 6, -10], ![-13, -17, 22], ![13, 46, -39]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![349, 226, 38]] ![![487, 6, -10]]
  ![![193, 0, 0]] where
 M := ![![![-193, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB200I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB200I3 : PrimesBelowBoundCertificateInterval O 137 193 200 where
  m := 11
  g := ![2, 3, 1, 1, 2, 1, 2, 1, 2, 2, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB200I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0]
    · exact ![I163N0, I163N1]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1]
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
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![3869893]
    · exact ![26569, 163]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
    · exact ![32761, 181]
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
      exact NI149N1
      exact NI149N2
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
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
  β := ![I139N1, I149N0, I149N1, I149N2, I163N1, I173N1, I181N1, I191N1, I193N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [], [], [I163N1], [], [I173N1], [], [I181N1], [I191N1], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
