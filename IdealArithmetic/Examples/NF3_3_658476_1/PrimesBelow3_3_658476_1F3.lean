
import IdealArithmetic.Examples.NF3_3_658476_1.RI3_3_658476_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp139 : Fact (Nat.Prime 139) := {out := by norm_num}

def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1350792, -15169, -31053]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![1350792, -15169, -31053]] 
 ![![139, 0, 0], ![0, 139, 0], ![25, 45, 1]] where
  M :=![![![1350792, -15169, -31053], ![-31053, 344, 715], ![15884, -154, -371]]]
  hmulB := by decide  
  f := ![![![-126, -6083, -1177]], ![![-1177, -56820, -10989]], ![![-439, -21193, -4099]]]
  g := ![![![15303, 9944, -31053], ![-352, -229, 715], ![181, 119, -371]]]
  hle1 := by decide   
  hle2 := by decide  


def P139P0 : CertificateIrreducibleZModOfList' 139 2 2 7 [76, 11, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 1, 0, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [128, 138], [0, 1]]
 g := ![![[130, 37], [81, 30], [25], [19, 116], [77], [121], [1]], ![[1, 102], [29, 109], [25], [133, 23], [77], [121], [1]]]
 h' := ![![[128, 138], [99, 68], [43, 126], [85, 134], [92, 106], [55, 63], [63, 128], [0, 1]], ![[0, 1], [46, 71], [47, 13], [1, 5], [38, 33], [57, 76], [45, 11], [128, 138]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38]]
 b := ![[], [35, 19]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI139N0 : CertifiedPrimeIdeal' SI139N0 139 where
  n := 2
  hpos := by decide
  P := [76, 11, 1]
  hirr := P139P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![79, 309, 359]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-64, -114, 359]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI139N0 B_one_repr
lemma NI139N0 : Nat.card (O ⧸ I139N0) = 19321 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-126, -6083, -1177]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![-126, -6083, -1177]] 
 ![![139, 0, 0], ![50, 1, 0], ![115, 0, 1]] where
  M :=![![![-126, -6083, -1177], ![-1177, -56820, -10989], ![-4906, -236852, -45831]]]
  hmulB := by decide  
  f := ![![![1350792, -15169, -31053]], ![![485673, -5454, -11165]], ![![1117676, -12551, -25694]]]
  g := ![![![3161, -6083, -1177], ![29522, -56820, -10989], ![123081, -236852, -45831]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![1350792, -15169, -31053]] ![![-126, -6083, -1177]]
  ![![139, 0, 0]] where
 M := ![![![139, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I149N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![204, -1, -5]] i)))

def SI149N0: IdealEqSpanCertificate' Table ![![204, -1, -5]] 
 ![![149, 0, 0], ![64, 1, 0], ![6, 0, 1]] where
  M :=![![![204, -1, -5], ![-5, -12, 3], ![4, 62, -15]]]
  hmulB := by decide  
  f := ![![![-6, -325, -63]], ![![-3, -160, -31]], ![![-2, -98, -19]]]
  g := ![![![2, -1, -5], ![5, -12, 3], ![-26, 62, -15]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N0 : Nat.card (O ⧸ I149N0) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N0)

lemma isPrimeI149N0 : Ideal.IsPrime I149N0 := prime_ideal_of_norm_prime hp149.out _ NI149N0

def I149N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![174, -15433, 3697]] i)))

def SI149N1: IdealEqSpanCertificate' Table ![![174, -15433, 3697]] 
 ![![149, 0, 0], ![105, 1, 0], ![97, 0, 1]] where
  M :=![![![174, -15433, 3697], ![3697, 143712, -34563], ![-19130, -741256, 178275]]]
  hmulB := by decide  
  f := ![![![225672, 10894643, 2107515]], ![![173175, 8360275, 1617254]], ![![205888, 9939545, 1922756]]]
  g := ![![![8470, -15433, 3697], ![-78748, 143712, -34563], ![406175, -741256, 178275]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N1 : Nat.card (O ⧸ I149N1) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N1)

lemma isPrimeI149N1 : Ideal.IsPrime I149N1 := prime_ideal_of_norm_prime hp149.out _ NI149N1

def I149N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![77560, -871, -1783]] i)))

def SI149N2: IdealEqSpanCertificate' Table ![![77560, -871, -1783]] 
 ![![149, 0, 0], ![129, 1, 0], ![108, 0, 1]] where
  M :=![![![77560, -871, -1783], ![-1783, 20, 41], ![912, -10, -21]]]
  hmulB := by decide  
  f := ![![![10, 461, 51]], ![![9, 417, 50]], ![![10, 460, 49]]]
  g := ![![![2567, -871, -1783], ![-59, 20, 41], ![30, -10, -21]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI149N2 : Nat.card (O ⧸ I149N2) = 149 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI149N2)

lemma isPrimeI149N2 : Ideal.IsPrime I149N2 := prime_ideal_of_norm_prime hp149.out _ NI149N2
def MulI149N0 : IdealMulLeCertificate' Table 
  ![![204, -1, -5]] ![![174, -15433, 3697]]
  ![![127449, 414236, -102624]] where
 M := ![![![127449, 414236, -102624]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI149N1 : IdealMulLeCertificate' Table 
  ![![127449, 414236, -102624]] ![![77560, -871, -1783]]
  ![![149, 0, 0]] where
 M := ![![![9052768564, -101697119, -208102787]]]
 hmul := by decide  
 g := ![![![![60756836, -682531, -1396663]]]]
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


def P151P0 : CertificateIrreducibleZModOfList' 151 3 2 7 [136, 63, 108, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [2, 106, 100], [41, 44, 51], [0, 1]]
 g := ![![[131, 57, 116], [142, 27, 45], [91, 35, 84], [42, 125], [137, 36, 72], [43, 1], []], ![[79, 20, 131, 39], [60, 123, 74, 17], [19, 51, 112, 86], [52, 21], [131, 23, 39, 125], [7, 124], [12, 34]], ![[7, 148, 122, 143], [144, 93, 141, 28], [53, 95, 12, 129], [107, 4], [4, 90, 112, 71], [113, 62], [61, 34]]]
 h' := ![![[2, 106, 100], [16, 102, 95], [6, 25, 137], [34, 5, 50], [92, 83, 27], [41, 24, 125], [0, 0, 1], [0, 1]], ![[41, 44, 51], [33, 89, 35], [47, 7, 72], [33, 68, 133], [92, 14, 126], [137, 30, 48], [33, 27, 44], [2, 106, 100]], ![[0, 1], [7, 111, 21], [21, 119, 93], [28, 78, 119], [50, 54, 149], [120, 97, 129], [29, 124, 106], [41, 44, 51]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [45, 147], []]
 b := ![[], [36, 60, 145], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 3
  hpos := by decide
  P := [136, 63, 108, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2718, -26274, 194790]
  a := ![-1, 1, 4]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-18, -174, 1290]
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

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![36, 1721, 303]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![36, 1721, 303]] 
 ![![157, 0, 0], ![0, 157, 0], ![11, 129, 1]] where
  M :=![![![36, 1721, 303], ![303, 14786, 3139], ![1418, 67640, 11647]]]
  hmulB := by decide  
  f := ![![![-255474, 2869, 5873]], ![![5873, -66, -135]], ![![-13093, 147, 301]]]
  g := ![![![-21, -238, 303], ![-218, -2485, 3139], ![-807, -9139, 11647]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 2 2 7 [83, 132, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 156], [0, 1]]
 g := ![![[134, 10], [48], [154, 3], [51, 81], [36, 39], [154], [1]], ![[70, 147], [48], [72, 154], [35, 76], [69, 118], [154], [1]]]
 h' := ![![[25, 156], [84, 18], [92, 26], [6, 72], [152, 9], [73, 14], [74, 25], [0, 1]], ![[0, 1], [63, 139], [114, 131], [79, 85], [63, 148], [109, 143], [71, 132], [25, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [60]]
 b := ![[], [96, 30]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 2
  hpos := by decide
  P := [83, 132, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4270, -21, 40]
  a := ![-64, 0, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -33, 40]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-255474, 2869, 5873]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-255474, 2869, 5873]] 
 ![![157, 0, 0], ![57, 1, 0], ![74, 0, 1]] where
  M :=![![![-255474, 2869, 5873], ![5873, -66, -135], ![-3004, 34, 69]]]
  hmulB := by decide  
  f := ![![![36, 1721, 303]], ![![15, 719, 130]], ![![26, 1242, 217]]]
  g := ![![![-5437, 2869, 5873], ![125, -66, -135], ![-64, 34, 69]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![36, 1721, 303]] ![![-255474, 2869, 5873]]
  ![![157, 0, 0]] where
 M := ![![![157, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0]] 
 ![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]] where
  M :=![![![163, 0, 0], ![0, 163, 0], ![0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [40, 133, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [31, 115, 105], [26, 47, 58], [0, 1]]
 g := ![![[150], [49, 53, 100], [31, 14], [], [158, 161], [19, 57, 1], []], ![[15, 47, 155, 13], [38, 42, 85, 139], [20, 131], [107, 46], [141, 69], [114, 124, 84, 159], [86, 104]], ![[87, 100, 152, 150], [30, 73, 37, 83], [8, 144], [156, 46], [141, 77], [120, 89, 135, 135], [133, 104]]]
 h' := ![![[31, 115, 105], [159, 98], [111, 46, 153], [84, 33, 60], [128, 95], [55, 83, 145], [0, 0, 1], [0, 1]], ![[26, 47, 58], [100, 23, 21], [84, 157, 122], [45, 37, 91], [139, 4, 32], [143, 110, 45], [129, 8, 47], [31, 115, 105]], ![[0, 1], [99, 42, 142], [151, 123, 51], [54, 93, 12], [153, 64, 131], [67, 133, 136], [83, 155, 115], [26, 47, 58]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [38, 5], []]
 b := ![[], [114, 37, 31], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [40, 133, 106, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1304, -16626, -119968]
  a := ![1, -2, -5]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![8, -102, -736]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [152, 137, 94, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [148, 113, 161], [92, 53, 6], [0, 1]]
 g := ![![[21, 68, 32], [97, 97, 56], [125, 25, 141], [71, 94], [47, 97], [15, 73, 1], []], ![[48, 151, 1, 165], [76, 138, 3, 40], [32, 72, 133, 164], [98, 96], [161, 154], [97, 37, 25, 13], [103, 36]], ![[37, 109, 37, 157], [44, 97, 107, 63], [19, 8, 88, 88], [77, 132], [40, 132], [77, 110, 152, 128], [91, 36]]]
 h' := ![![[148, 113, 161], [119, 131, 115], [38, 26, 132], [110, 63, 59], [61, 55, 125], [58, 42, 127], [0, 0, 1], [0, 1]], ![[92, 53, 6], [54, 66, 132], [135, 126, 160], [145, 7, 77], [126, 35, 116], [7, 77, 133], [69, 4, 53], [148, 113, 161]], ![[0, 1], [59, 137, 87], [97, 15, 42], [148, 97, 31], [117, 77, 93], [39, 48, 74], [143, 163, 113], [92, 53, 6]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [124, 123], []]
 b := ![[], [113, 48, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [152, 137, 94, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-167, -21543, -14863]
  a := ![0, -2, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1, -129, -89]
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


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [75, 154, 73, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [28, 64, 134], [72, 108, 39], [0, 1]]
 g := ![![[25, 133, 25], [145, 15], [105, 93, 109], [72, 31, 38], [158, 95], [158, 100, 1], []], ![[118, 161, 129, 2], [170, 96], [171, 135, 154, 8], [42, 67, 27, 58], [34, 15], [35, 126, 18, 94], [58, 137]], ![[150, 31, 16, 71], [55, 144], [46, 82, 168, 48], [83, 59, 0, 50], [30, 43], [110, 113, 165, 65], [153, 137]]]
 h' := ![![[28, 64, 134], [166, 92, 5], [83, 22, 154], [136, 114, 52], [44, 29, 111], [87, 0, 152], [0, 0, 1], [0, 1]], ![[72, 108, 39], [136, 87, 66], [118, 166, 31], [65, 42, 132], [162, 125, 131], [64, 75, 154], [67, 120, 108], [28, 64, 134]], ![[0, 1], [74, 167, 102], [96, 158, 161], [51, 17, 162], [156, 19, 104], [26, 98, 40], [110, 53, 64], [72, 108, 39]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [5, 84], []]
 b := ![[], [172, 139, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [75, 154, 73, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![583702, 35359297, 19509383]
  a := ![1, 20, 21]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![3374, 204389, 112771]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![342581, -3820, -7882]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![342581, -3820, -7882]] 
 ![![179, 0, 0], ![0, 179, 0], ![34, 40, 1]] where
  M :=![![![342581, -3820, -7882], ![-7882, -165, 242], ![4062, 1262, -407]]]
  hmulB := by decide  
  f := ![![![1331, 64256, 12430]], ![![12430, 600077, 116082]], ![![3320, 160278, 31005]]]
  g := ![![![3411, 1740, -7882], ![-90, -55, 242], ![100, 98, -407]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 2 2 7 [75, 111, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [68, 178], [0, 1]]
 g := ![![[159, 74], [85, 126], [64], [42], [0, 125], [111, 149], [1]], ![[0, 105], [61, 53], [64], [42], [87, 54], [40, 30], [1]]]
 h' := ![![[68, 178], [69, 49], [26, 157], [72, 171], [0, 159], [88, 29], [104, 68], [0, 1]], ![[0, 1], [0, 130], [141, 22], [65, 8], [72, 20], [91, 150], [74, 111], [68, 178]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [51]]
 b := ![[], [28, 115]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 2
  hpos := by decide
  P := [75, 111, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-32, 373, 157]
  a := ![-1, 2, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-30, -33, 157]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 32041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1331, -64256, -12430]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-1331, -64256, -12430]] 
 ![![179, 0, 0], ![100, 1, 0], ![141, 0, 1]] where
  M :=![![![-1331, -64256, -12430], ![-12430, -600077, -116082], ![-51826, -2501978, -483995]]]
  hmulB := by decide  
  f := ![![![-342581, 3820, 7882]], ![![-191342, 2135, 4402]], ![![-269877, 3002, 6211]]]
  g := ![![![45681, -64256, -12430], ![426608, -600077, -116082], ![1778711, -2501978, -483995]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![342581, -3820, -7882]] ![![-1331, -64256, -12430]]
  ![![179, 0, 0]] where
 M := ![![![-179, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0]]]]
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


lemma PB181I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 180 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 180 (by omega)

def PB181I3 : PrimesBelowBoundCertificateInterval O 137 180 181 where
  m := 8
  g := ![2, 3, 1, 2, 1, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179]
  hP := PB181I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1]
    · exact ![I149N0, I149N1, I149N2]
    · exact ![I151N0]
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0]
    · exact ![I179N0, I179N1]
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
    · exact ![19321, 139]
    · exact ![149, 149, 149]
    · exact ![3442951]
    · exact ![24649, 157]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![5177717]
    · exact ![32041, 179]
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
      exact NI157N1
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
      exact NI179N1
  β := ![I139N1, I149N0, I149N1, I149N2, I157N1, I179N1]
  Il := ![[I139N1], [I149N0, I149N1, I149N2], [], [I157N1], [], [], [], [I179N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
