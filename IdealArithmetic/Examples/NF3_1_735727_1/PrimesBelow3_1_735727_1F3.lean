
import IdealArithmetic.Examples.NF3_1_735727_1.RI3_1_735727_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section 
def I139N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5697033598, 6234323975, 2995216]] i)))

def SI139N0: IdealEqSpanCertificate' Table ![![-5697033598, 6234323975, 2995216]] 
 ![![139, 0, 0], ![23, 1, 0], ![27, 0, 1]] where
  M :=![![![-5697033598, 6234323975, 2995216], ![152756016, -5861770478, 6234323975], ![317950522725, -342735062609, -5861770478]]]
  hmulB := by decide  
  f := ![![![2171081771033167099259, 35517610683655131506, 38884352693983833873]], ![![373510667058676394320, 6110413083367800438, 6689623903922901515]], ![![434752560883179304941, 7112294160077926945, 7786474069076401085]]]
  g := ![![![-1073146445, 6234323975, 2995216], ![-239951585, -5861770478, 6234323975], ![60137588242, -342735062609, -5861770478]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N0 : Nat.card (O ⧸ I139N0) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N0)

lemma isPrimeI139N0 : Ideal.IsPrime I139N0 := prime_ideal_of_norm_prime hp139.out _ NI139N0

def I139N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![143024, -158157, 1725]] i)))

def SI139N1: IdealEqSpanCertificate' Table ![![143024, -158157, 1725]] 
 ![![139, 0, 0], ![58, 1, 0], ![111, 0, 1]] where
  M :=![![![143024, -158157, 1725], ![87975, 48149, -158157], ![-8066007, 8786610, 48149]]]
  hmulB := by decide  
  f := ![![![-1391982203971, -22772003643, -24930579624]], ![![-589974297778, -9651629755, -10566515265]], ![![-1119938106666, -18321523488, -20058234985]]]
  g := ![![![65645, -158157, 1725], ![106840, 48149, -158157], ![-3762834, 8786610, 48149]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI139N1 : Nat.card (O ⧸ I139N1) = 139 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI139N1)

lemma isPrimeI139N1 : Ideal.IsPrime I139N1 := prime_ideal_of_norm_prime hp139.out _ NI139N1
def MulI139N0 : IdealMulLeCertificate' Table 
  ![![-5697033598, 6234323975, 2995216]] ![![143024, -158157, 1725]]
  ![![-290507314842239, 1227520002688921, -995685143215441]] where
 M := ![![![-290507314842239, 1227520002688921, -995685143215441]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
 hle2 := by decide  

def MulI139N1 : IdealMulLeCertificate' Table 
  ![![-290507314842239, 1227520002688921, -995685143215441]] ![![143024, -158157, 1725]]
  ![![139, 0, 0]] where
 M := ![![![8097644889010311048326, -8643647410225253194258, -242583250144054809581]]]
 hmul := by decide  
 g := ![![![![58256438050433892434, -62184513742627720822, -1745203238446437479]]]]
 hle2 := by decide  


def PBC139 : ContainsPrimesAboveP 139 ![I139N0, I139N1, I139N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI139N0
    exact isPrimeI139N1
    exact isPrimeI139N1
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


def P149P0 : CertificateIrreducibleZModOfList' 149 3 2 7 [93, 96, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [75, 25, 127], [35, 123, 22], [0, 1]]
 g := ![![[4, 69, 116], [36, 46], [72, 132, 107], [43, 143], [22, 103, 53], [110, 1], []], ![[136, 67, 28, 46], [56, 37], [126, 65, 104, 81], [103, 118], [67, 131, 103, 113], [28, 80], [139, 37]], ![[92, 131, 34, 96], [51, 45], [68, 29, 32, 104], [37, 7], [64, 43, 95, 42], [85, 29], [95, 37]]]
 h' := ![![[75, 25, 127], [11, 39, 99], [9, 109, 33], [134, 75, 133], [40, 148, 21], [51, 75, 84], [0, 0, 1], [0, 1]], ![[35, 123, 22], [6, 105, 144], [105, 51, 22], [113, 47, 107], [93, 102, 72], [79, 148, 40], [148, 77, 123], [75, 25, 127]], ![[0, 1], [138, 5, 55], [34, 138, 94], [104, 27, 58], [72, 48, 56], [113, 75, 25], [138, 72, 25], [35, 123, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [34, 119], []]
 b := ![[], [85, 38, 107], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI149N0 : CertifiedPrimeIdeal' SI149N0 149 where
  n := 3
  hpos := by decide
  P := [93, 96, 39, 1]
  hirr := P149P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9834, -5960, -5215]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![66, -40, -35]
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

def I151N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-1162694, -19021, -20824]] i)))

def SI151N0: IdealEqSpanCertificate' Table ![![-1162694, -19021, -20824]] 
 ![![151, 0, 0], ![0, 151, 0], ![22, 119, 1]] where
  M :=![![![-1162694, -19021, -20824], ![-1062024, -17374, -19021], ![-970071, -15869, -17374]]]
  hmulB := by decide  
  f := ![![![-77, 98, -15]], ![![-765, 748, 98]], ![![-581, 563, 80]]]
  g := ![![![-4666, 16285, -20824], ![-4262, 14875, -19021], ![-3893, 13587, -17374]]]
  hle1 := by decide   
  hle2 := by decide  


def P151P0 : CertificateIrreducibleZModOfList' 151 2 2 7 [63, 146, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [5, 150], [0, 1]]
 g := ![![[91, 4], [62, 91], [135, 38], [40], [104, 137], [25], [1]], ![[111, 147], [64, 60], [23, 113], [40], [34, 14], [25], [1]]]
 h' := ![![[5, 150], [20, 149], [102, 98], [55, 75], [92, 74], [129, 99], [88, 5], [0, 1]], ![[0, 1], [10, 2], [139, 53], [128, 76], [9, 77], [20, 52], [113, 146], [5, 150]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [8]]
 b := ![[], [141, 4]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI151N0 : CertifiedPrimeIdeal' SI151N0 151 where
  n := 2
  hpos := by decide
  P := [63, 146, 1]
  hirr := P151P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-694, 831, -59]
  a := ![-1, -2, 3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![4, 52, -59]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI151N0 : Ideal.IsPrime I151N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI151N0 B_one_repr
lemma NI151N0 : Nat.card (O ⧸ I151N0) = 22801 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI151N0

def I151N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-77, 98, -15]] i)))

def SI151N1: IdealEqSpanCertificate' Table ![![-77, 98, -15]] 
 ![![151, 0, 0], ![32, 1, 0], ![33, 0, 1]] where
  M :=![![![-77, 98, -15], ![-765, 748, 98], ![4998, -6155, 748]]]
  hmulB := by decide  
  f := ![![![-1162694, -19021, -20824]], ![![-253432, -4146, -4539]], ![![-260523, -4262, -4666]]]
  g := ![![![-18, 98, -15], ![-185, 748, 98], ![1174, -6155, 748]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI151N1 : Nat.card (O ⧸ I151N1) = 151 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI151N1)

lemma isPrimeI151N1 : Ideal.IsPrime I151N1 := prime_ideal_of_norm_prime hp151.out _ NI151N1
def MulI151N0 : IdealMulLeCertificate' Table 
  ![![-1162694, -19021, -20824]] ![![-77, 98, -15]]
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


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [29, 28, 82, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [25, 124, 78], [50, 32, 79], [0, 1]]
 g := ![![[102, 76, 10], [2, 25], [143, 151, 75], [23, 43, 58], [110, 113, 42], [75, 1], []], ![[73, 154, 112, 73], [94, 48], [48, 126, 48, 129], [135, 111, 58, 114], [100, 22, 1, 18], [146, 82], [91, 118]], ![[3, 82, 152, 28], [81, 19], [118, 13, 32, 66], [90, 5, 53, 61], [97, 96, 7, 26], [143, 147], [90, 118]]]
 h' := ![![[25, 124, 78], [85, 147, 18], [92, 46, 152], [118, 138, 111], [107, 138, 134], [23, 69, 102], [0, 0, 1], [0, 1]], ![[50, 32, 79], [7, 74, 110], [8, 1, 131], [128, 95, 29], [110, 47, 137], [106, 145, 11], [27, 73, 32], [25, 124, 78]], ![[0, 1], [117, 93, 29], [116, 110, 31], [146, 81, 17], [117, 129, 43], [103, 100, 44], [47, 84, 124], [50, 32, 79]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [9, 11], []]
 b := ![[], [21, 12, 22], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [29, 28, 82, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![72220, -1413, 1413]
  a := ![-64, 1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![460, -9, 9]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [72, 40, 156, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 116, 127], [104, 46, 36], [0, 1]]
 g := ![![[67, 87, 152], [58, 6, 43], [16, 22], [68, 60], [89, 65], [9, 7, 1], []], ![[95, 16, 63, 23], [48, 23, 22, 27], [81, 57], [56, 104], [38, 56], [162, 24, 109, 108], [68, 155]], ![[92, 27, 44, 158], [104, 107, 103, 93], [154, 62], [124, 100], [32, 43], [113, 98, 149, 143], [159, 155]]]
 h' := ![![[66, 116, 127], [62, 153, 57], [42, 119, 83], [78, 131, 48], [128, 7, 68], [4, 114, 37], [0, 0, 1], [0, 1]], ![[104, 46, 36], [81, 105, 48], [77, 141, 23], [82, 150, 100], [56, 62, 105], [99, 30, 43], [112, 128, 46], [66, 116, 127]], ![[0, 1], [162, 68, 58], [60, 66, 57], [155, 45, 15], [97, 94, 153], [49, 19, 83], [20, 35, 116], [104, 46, 36]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [4, 49], []]
 b := ![[], [8, 108, 24], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [72, 40, 156, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-194296, 358437, -159414]
  a := ![1, 1, -3]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-1192, 2199, -978]
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


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [113, 88, 57, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 0, 4], [107, 166, 163], [0, 1]]
 g := ![![[65, 28, 47], [89, 85, 3], [74, 29, 22], [24, 81], [28, 98], [155, 110, 1], []], ![[8, 149, 74, 77], [23, 74, 130, 141], [157, 96, 115, 64], [84, 98], [77, 27], [85, 9, 108, 4], [90, 16]], ![[139, 56, 54, 52], [60, 119, 79, 117], [144, 52, 3, 37], [54, 44], [86, 7], [47, 125], [98, 16]]]
 h' := ![![[3, 0, 4], [130, 75, 106], [155, 29, 62], [74, 160, 135], [75, 104, 158], [20, 149, 76], [0, 0, 1], [0, 1]], ![[107, 166, 163], [105, 57, 27], [17, 68, 54], [56, 8, 4], [153, 44, 91], [105, 148, 19], [26, 125, 166], [3, 0, 4]], ![[0, 1], [143, 35, 34], [122, 70, 51], [17, 166, 28], [146, 19, 85], [41, 37, 72], [41, 42], [107, 166, 163]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [69, 85], []]
 b := ![[], [129, 50, 104], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [113, 88, 57, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11690, -7014, -6179]
  a := ![0, -1, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![70, -42, -37]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-347645, 402695, -24191]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-347645, 402695, -24191]] 
 ![![173, 0, 0], ![0, 173, 0], ![164, 52, 1]] where
  M :=![![![-347645, 402695, -24191], ![-1233741, 982860, 402695], ![20537445, -23381966, 982860]]]
  hmulB := by decide  
  f := ![![![60010488890, 981736022, 1074795545]], ![![54814572795, 896733915, 981736022]], ![![73654026014, 1204936201, 1319153043]]]
  g := ![![![20923, 9599, -24191], ![-388877, -115360, 402695], ![-813015, -430582, 982860]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 2 2 7 [20, 167, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [6, 172], [0, 1]]
 g := ![![[17, 136], [84], [115, 29], [19, 54], [84], [149, 36], [1]], ![[141, 37], [84], [116, 144], [170, 119], [84], [19, 137], [1]]]
 h' := ![![[6, 172], [56, 84], [122, 55], [139, 95], [14, 20], [134, 55], [153, 6], [0, 1]], ![[0, 1], [41, 89], [106, 118], [17, 78], [134, 153], [118, 118], [16, 167], [6, 172]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [63]]
 b := ![[], [165, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 2
  hpos := by decide
  P := [20, 167, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2126, 1172, 475]
  a := ![1, 19, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-438, -136, 475]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 29929 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![60010488890, 981736022, 1074795545]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![60010488890, 981736022, 1074795545]] 
 ![![173, 0, 0], ![121, 1, 0], ![64, 0, 1]] where
  M :=![![![60010488890, 981736022, 1074795545], ![54814572795, 896733915, 981736022], ![50068537122, 819091585, 896733915]]]
  hmulB := by decide  
  f := ![![![-347645, 402695, -24191]], ![![-250282, 287335, -14592]], ![![-9895, 13818, -3268]]]
  g := ![![![-737378524, 981736022, 1074795545], ![-673533736, 896733915, 981736022], ![-615216851, 819091585, 896733915]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-347645, 402695, -24191]] ![![60010488890, 981736022, 1074795545]]
  ![![173, 0, 0]] where
 M := ![![![173, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0]]]]
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


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [80, 3, 72, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [15, 131, 27], [92, 47, 152], [0, 1]]
 g := ![![[11, 140, 57], [37, 149, 29], [79, 74], [117, 89], [19, 33, 89], [169, 107, 1], []], ![[145, 143, 155, 68], [5, 74, 143, 117], [60, 87], [164, 147], [2, 94, 142, 60], [165, 127, 165, 36], [52, 13]], ![[148, 16, 86, 109], [126, 25, 12, 58], [81, 61], [74, 49], [49, 135, 40, 98], [80, 107, 113, 84], [106, 13]]]
 h' := ![![[15, 131, 27], [83, 146, 93], [149, 75, 71], [174, 57, 49], [91, 63, 39], [84, 62, 140], [0, 0, 1], [0, 1]], ![[92, 47, 152], [46, 55, 79], [55, 58, 171], [102, 23, 83], [79, 140, 133], [2, 125, 20], [3, 49, 47], [15, 131, 27]], ![[0, 1], [34, 157, 7], [6, 46, 116], [159, 99, 47], [72, 155, 7], [147, 171, 19], [163, 130, 131], [92, 47, 152]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 54], []]
 b := ![[], [140, 19, 177], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [80, 3, 72, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-47435, 55848, -4117]
  a := ![-1, 3, -1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-265, 312, -23]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![181, 0, 0]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![181, 0, 0]] 
 ![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]] where
  M :=![![![181, 0, 0], ![0, 181, 0], ![0, 0, 181]]]
  hmulB := by decide  
  f := ![![![1, 0, 0]], ![![0, 1, 0]], ![![0, 0, 1]]]
  g := ![![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [139, 84, 39, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [144, 89, 178], [179, 91, 3], [0, 1]]
 g := ![![[81, 36, 168], [162, 67], [146, 30, 117], [], [129, 131, 20], [170, 142, 1], []], ![[48, 152, 20, 119], [46, 101], [160, 80, 46, 129], [144, 101], [80, 107, 162, 27], [169, 18, 95, 135], [20, 9]], ![[63, 179, 150, 60], [173, 55], [27, 157, 110, 142], [137, 101], [91, 53, 79, 39], [14, 180, 173, 52], [14, 9]]]
 h' := ![![[144, 89, 178], [48, 104, 63], [159, 139, 51], [144, 55, 152], [169, 141], [81, 10, 127], [0, 0, 1], [0, 1]], ![[179, 91, 3], [160, 107, 172], [161, 138, 61], [113, 157, 92], [20, 60, 120], [66, 44, 124], [37, 76, 91], [144, 89, 178]], ![[0, 1], [31, 151, 127], [27, 85, 69], [61, 150, 118], [68, 161, 61], [130, 127, 111], [49, 105, 89], [179, 91, 3]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [28, 173], []]
 b := ![[], [22, 169, 118], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [139, 84, 39, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4706, -8869, 16109]
  a := ![0, 1, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-26, -49, 89]
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


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [141, 119, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [58, 28, 163], [110, 162, 28], [0, 1]]
 g := ![![[47, 60, 156], [174, 164, 135], [181, 130, 59], [49, 88, 52], [5, 84, 45], [28, 168, 1], []], ![[49, 182, 125, 180], [41, 183, 39, 125], [119, 47, 143, 104], [150, 76, 60, 86], [100, 73, 119, 30], [98, 143, 151, 136], [73, 20]], ![[67, 45, 135, 101], [12, 161, 5, 187], [111, 108, 126, 142], [166, 90, 41, 112], [187, 184, 183, 124], [8, 1, 31, 178], [17, 20]]]
 h' := ![![[58, 28, 163], [105, 81, 164], [73, 184, 53], [158, 140, 21], [59, 125, 25], [63, 102, 42], [0, 0, 1], [0, 1]], ![[110, 162, 28], [122, 72, 43], [105, 40, 187], [98, 89, 55], [63, 58, 168], [124, 160, 128], [138, 145, 162], [58, 28, 163]], ![[0, 1], [109, 38, 175], [154, 158, 142], [53, 153, 115], [62, 8, 189], [137, 120, 21], [153, 46, 28], [110, 162, 28]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [71, 124], []]
 b := ![[], [25, 134, 59], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [141, 119, 23, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![247727, -254794, -17954]
  a := ![2, -10, 2]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![1297, -1334, -94]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-655, 718, -1]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-655, 718, -1]] 
 ![![193, 0, 0], ![0, 193, 0], ![76, 54, 1]] where
  M :=![![![-655, 718, -1], ![-51, -600, 718], ![36618, -39541, -600]]]
  hmulB := by decide  
  f := ![![![-148966, -2437, -2668]], ![![-136068, -2226, -2437]], ![![-97375, -1593, -1744]]]
  g := ![![![-3, 4, -1], ![-283, -204, 718], ![426, -37, -600]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [53, 51, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [142, 192], [0, 1]]
 g := ![![[92, 96], [118], [179], [92], [157], [170], [142, 1]], ![[21, 97], [118], [179], [92], [157], [170], [91, 192]]]
 h' := ![![[142, 192], [124, 17], [190, 120], [42, 117], [155, 51], [62, 93], [1, 39], [0, 1]], ![[0, 1], [29, 176], [53, 73], [58, 76], [63, 142], [144, 100], [135, 154], [142, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [148]]
 b := ![[], [150, 74]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [53, 51, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![783, 84, 23]
  a := ![13, -1, 1]
  z := ![1, 0, 0]
  hpol := by decide
  g := ![-5, -6, 23]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![148966, 2437, 2668]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![148966, 2437, 2668]] 
 ![![193, 0, 0], ![139, 1, 0], ![172, 0, 1]] where
  M :=![![![148966, 2437, 2668], ![136068, 2226, 2437], ![124287, 2033, 2226]]]
  hmulB := by decide  
  f := ![![![655, -718, 1]], ![![472, -514, -3]], ![![394, -435, 4]]]
  g := ![![![-3361, 2437, 2668], ![-3070, 2226, 2437], ![-2804, 2033, 2226]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-655, 718, -1]] ![![148966, 2437, 2668]]
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


lemma PB243I3_primes (p : ℕ) :
  p ∈ Set.range ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193] ↔ Nat.Prime p ∧ 137 < p ∧ p ≤ 193 := by
  rw [← List.mem_ofFn']
  convert primes_range 137 193 (by omega)

def PB243I3 : PrimesBelowBoundCertificateInterval O 137 193 243 where
  m := 11
  g := ![3, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2]
  P := ![139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193]
  hP := PB243I3_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I139N0, I139N1, I139N1]
    · exact ![I149N0]
    · exact ![I151N0, I151N1]
    · exact ![I157N0]
    · exact ![I163N0]
    · exact ![I167N0]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
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
    · exact ![139, 139, 139]
    · exact ![3307949]
    · exact ![22801, 151]
    · exact ![3869893]
    · exact ![4330747]
    · exact ![4657463]
    · exact ![29929, 173]
    · exact ![5735339]
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
      exact NI139N1
    · dsimp ; intro j
      fin_cases j
      exact NI149N0
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
      exact NI173N1
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
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
  β := ![I139N0, I139N1, I151N1, I173N1, I193N1]
  Il := ![[I139N0, I139N1, I139N1], [], [I151N1], [], [], [], [I173N1], [], [], [], [I193N1]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
