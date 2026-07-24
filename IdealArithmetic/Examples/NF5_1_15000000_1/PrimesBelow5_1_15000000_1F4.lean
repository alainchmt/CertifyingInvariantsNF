
import IdealArithmetic.Examples.NF5_1_15000000_1.RI5_1_15000000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![185, 33, -69, -14, 70]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![185, 33, -69, -14, 70]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![66, 51, 66, 1, 0], ![45, 143, 1, 0, 1]] where
  M :=![![![185, 33, -69, -14, 70], ![-630, -94, 119, -38, -42], ![378, -385, 56, 426, -114], ![225, 410, -318, -446, 387], ![-885, -273, 267, 105, -226]]]
  hmulB := by decide  
  f := ![![![-22687, 2929, 3569, 2790, -4594]], ![![41346, -5336, -6505, -5086, 8370]], ![![-75330, 9731, 11850, 9262, -15258]], ![![-27381, 3538, 4307, 3366, -5547]], ![![30540, -3941, -4805, -3757, 6182]]]
  g := ![![![-13, -59, 5, -14, 70], ![24, 50, 17, -38, -42], ![-144, -37, -178, 426, -114], ![78, -205, 183, -446, 387], ![15, 170, -41, 105, -226]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [105, 33, 150, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 17, 101], [100, 139, 56], [0, 1]]
 g := ![![[122, 121, 86], [54, 146], [63, 127, 51], [102, 55, 39], [153, 146, 99], [7, 1], []], ![[152, 130, 8, 118], [26, 148], [134, 13, 68, 3], [134, 31, 128, 153], [139, 121, 142, 90], [153, 10], [109, 153]], ![[76, 133, 150, 57], [89, 105], [129, 104, 73, 68], [42, 118, 44, 93], [6, 68, 31, 89], [104, 132], [154, 153]]]
 h' := ![![[64, 17, 101], [109, 39, 20], [136, 29, 97], [123, 54, 88], [106, 19, 143], [50, 135, 16], [0, 0, 1], [0, 1]], ![[100, 139, 56], [65, 111, 125], [35, 108, 84], [96, 122, 102], [117, 50, 130], [64, 95, 2], [30, 98, 139], [64, 17, 101]], ![[0, 1], [86, 7, 12], [47, 20, 133], [131, 138, 124], [152, 88, 41], [81, 84, 139], [110, 59, 17], [100, 139, 56]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [47, 23], []]
 b := ![[], [75, 91, 149], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [105, 33, 150, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![5707410, 3603122, 242966, -845761, -2295435]
  a := ![0, -8, -7, -7, -37]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![1049823, 2388434, 371711, -845761, -2295435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-22687, 2929, 3569, 2790, -4594]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![-22687, 2929, 3569, 2790, -4594]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![136, 52, 1, 0, 0], ![48, 78, 0, 1, 0], ![100, 94, 0, 0, 1]] where
  M :=![![![-22687, 2929, 3569, 2790, -4594], ![41346, -5336, -6505, -5086, 8370], ![-75330, 9731, 11850, 9262, -15258], ![61659, -7958, -9700, -7584, 12483], ![-21453, 2775, 3375, 2637, -4348]]]
  hmulB := by decide  
  f := ![![![185, 33, -69, -14, 70]], ![![-630, -94, 119, -38, -42]], ![![-46, -5, -20, -22, 46]], ![![-255, -34, 36, -26, 3]], ![![-265, -37, 29, -31, 18]]]
  g := ![![![-1163, 201, 3569, 2790, -4594], ![2122, -364, -6505, -5086, 8370], ![-3858, 671, 11850, 9262, -15258], ![3163, -544, -9700, -7584, 12483], ![-1097, 193, 3375, 2637, -4348]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [54, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [88, 156], [0, 1]]
 g := ![![[10, 110], [108], [98, 58], [33, 126], [60, 64], [51], [1]], ![[113, 47], [108], [21, 99], [131, 31], [40, 93], [51], [1]]]
 h' := ![![[88, 156], [52, 61], [46, 39], [102, 134], [57, 122], [5, 8], [103, 88], [0, 1]], ![[0, 1], [82, 96], [24, 118], [119, 23], [117, 35], [81, 149], [154, 69], [88, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [79]]
 b := ![[], [146, 118]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [54, 69, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-1585740, -904086, 390670, 662130, 475632]
  a := ![3, -61, -63, -66, -235]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-853900, -748882, 390670, 662130, 475632]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![185, 33, -69, -14, 70]] ![![-22687, 2929, 3569, 2790, -4594]]
  ![![157, 0, 0, 0, 0]] where
 M := ![![![157, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![163, 0, 0, 0, 0]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![163, 0, 0, 0, 0]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]] where
  M :=![![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![0, 0, 0, 163, 0], ![0, 0, 0, 0, 163]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [90, 26, 88, 82, 150, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [117, 96, 13, 34, 44], [55, 29, 72, 111, 109], [22, 97, 95, 106, 124], [145, 103, 146, 75, 49], [0, 1]]
 g := ![![[15, 66, 51, 67, 113], [81, 85, 95, 95, 88], [147, 35, 110, 14], [137, 29, 101, 134], [65, 62, 65, 6], [1], []], ![[59, 16, 84, 156, 76, 63, 102, 3], [34, 37, 160, 86, 125, 46, 150, 11], [79, 67, 12, 81], [20, 66, 161, 46], [68, 19, 96, 93], [6, 87, 52, 134, 17, 11, 99, 76], [76, 10, 124, 143]], ![[43, 40, 154, 47, 81, 20, 16, 29], [78, 17, 19, 142, 44, 8, 10, 45], [47, 3, 149, 100], [123, 93, 38, 56], [154, 42, 60, 47], [106, 124, 36, 68, 1, 126, 80, 127], [60, 29, 3, 145]], ![[50, 5, 43, 150, 29, 133, 99, 79], [10, 89, 139, 67, 97, 111, 47, 89], [4, 113, 148, 133], [53, 41, 154, 26], [90, 99, 96, 84], [50, 12, 40, 137, 19, 137, 23, 116], [111, 144, 95, 54]], ![[104, 95, 74, 124, 126, 54, 13, 9], [116, 126, 48, 9, 142, 162, 159, 56], [161, 67, 96, 1], [41, 38, 1, 14], [122, 27, 136, 90], [57, 112, 12, 39, 108, 95, 114, 118], [40, 0, 95, 119]]]
 h' := ![![[117, 96, 13, 34, 44], [45, 7, 100, 140, 73], [31, 43, 2, 65, 96], [104, 11, 94, 32, 60], [131, 18, 74, 126, 42], [73, 137, 75, 81, 13], [0, 0, 1], [0, 1]], ![[55, 29, 72, 111, 109], [100, 109, 83, 29, 134], [71, 155, 79, 13, 81], [160, 121, 146, 85, 154], [161, 107, 5, 11, 32], [24, 146, 17, 101, 147], [3, 28, 18, 123, 86], [117, 96, 13, 34, 44]], ![[22, 97, 95, 106, 124], [40, 20, 28, 87, 24], [22, 151, 91, 85, 61], [60, 121, 137, 82, 153], [131, 151, 160, 99, 120], [138, 151, 153, 118, 84], [70, 161, 12, 24, 50], [55, 29, 72, 111, 109]], ![[145, 103, 146, 75, 49], [10, 67, 87, 31, 142], [87, 72, 65, 6, 12], [11, 85, 148, 87, 123], [39, 18, 65, 98, 29], [57, 116, 109, 37, 35], [111, 158, 3, 21, 83], [22, 97, 95, 106, 124]], ![[0, 1], [135, 123, 28, 39, 116], [132, 68, 89, 157, 76], [142, 151, 127, 40, 162], [75, 32, 22, 155, 103], [42, 102, 135, 152, 47], [147, 142, 129, 158, 107], [145, 103, 146, 75, 49]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [130, 157, 157, 75], [], [], []]
 b := ![[], [24, 5, 155, 143, 2], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [90, 26, 88, 82, 150, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-45718819465, -21857852076, 14125282036, 20702622665, 16116979362]
  a := ![1, -6, -6, -7, -24]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-280483555, -134097252, 86658172, 127009955, 98877174]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 115063617043 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def PBC163 : ContainsPrimesAboveP 163 ![I163N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI163N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![163, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 163 (by decide) 𝕀

instance hp167 : Fact (Nat.Prime 167) := {out := by norm_num}

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-70, 21, 11, 5, -21]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-70, 21, 11, 5, -21]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![33, 79, 102, 1, 0], ![43, 153, 151, 0, 1]] where
  M :=![![![-70, 21, 11, 5, -21], ![189, 4, -25, -29, 15], ![-135, 119, 28, 3, -87], ![216, -22, -30, -33, 42], ![-27, 45, 15, 3, -34]]]
  hmulB := by decide  
  f := ![![![-2, 1, -1, -1, 3]], ![![-27, -12, 9, 7, -3]], ![![27, -9, -10, 13, 21]], ![![3, -11, -2, 11, 12]], ![![-1, -19, -1, 18, 17]]]
  g := ![![![4, 17, 16, 5, -21], ![3, 0, 4, -29, 15], ![21, 79, 77, 3, -87], ![-3, -23, -18, -33, 42], ![8, 30, 29, 3, -34]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [85, 85, 118, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [35, 10, 41], [14, 156, 126], [0, 1]]
 g := ![![[88, 50, 96], [99, 165, 66], [39, 73, 108], [23, 115], [59, 89], [145, 49, 1], []], ![[58, 43, 32, 166], [78, 22, 80, 43], [77, 9, 120, 59], [86, 108], [13, 42], [40, 149, 82, 118], [23, 11]], ![[62, 112, 70, 84], [53, 27, 78, 28], [131, 120, 149, 38], [94, 65], [88, 147], [30, 112, 21, 75], [105, 11]]]
 h' := ![![[35, 10, 41], [102, 62, 116], [25, 131, 147], [93, 128, 129], [82, 111, 68], [33, 43, 16], [0, 0, 1], [0, 1]], ![[14, 156, 126], [90, 86, 97], [5, 20, 80], [82, 165, 155], [85, 152, 129], [45, 126, 84], [105, 148, 156], [35, 10, 41]], ![[0, 1], [92, 19, 121], [87, 16, 107], [88, 41, 50], [79, 71, 137], [82, 165, 67], [122, 19, 10], [14, 156, 126]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [152, 116], []]
 b := ![[], [46, 158, 99], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [85, 85, 118, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-395744348, -238215222, 43341766, 113485755, 135378855]
  a := ![1, 26, 22, 17, 121]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-59653084, -179141046, -191463547, 113485755, 135378855]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2, 1, -1, -1, 3]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-2, 1, -1, -1, 3]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![16, 95, 1, 0, 0], ![113, 122, 0, 1, 0], ![98, 17, 0, 0, 1]] where
  M :=![![![-2, 1, -1, -1, 3], ![-27, -12, 9, 7, -3], ![27, -9, -10, 13, 21], ![-54, -4, 8, -9, 0], ![-27, -21, 9, 15, -2]]]
  hmulB := by decide  
  f := ![![![-70, 21, 11, 5, -21]], ![![189, 4, -25, -29, 15]], ![![100, 5, -13, -16, 6]], ![![92, 17, -11, -18, -3]], ![![-22, 13, 4, 0, -11]]]
  g := ![![![-1, 1, -1, -1, 3], ![-4, -10, 9, 7, -3], ![-20, -6, -10, 13, 21], ![5, 2, 8, -9, 0], ![-10, -16, 9, 15, -2]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [146, 103, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [64, 166], [0, 1]]
 g := ![![[11, 93], [27, 2], [121, 137], [50], [56], [137, 88], [1]], ![[118, 74], [155, 165], [38, 30], [50], [56], [91, 79], [1]]]
 h' := ![![[64, 166], [66, 60], [36, 154], [80, 114], [115, 65], [38, 35], [21, 64], [0, 1]], ![[0, 1], [65, 107], [39, 13], [28, 53], [100, 102], [107, 132], [109, 103], [64, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [66]]
 b := ![[], [113, 33]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [146, 103, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-16156, -21889, 6093, 17812, 2166]
  a := ![-1, -6, 1, 10, -51]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-14004, -16830, 6093, 17812, 2166]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-70, 21, 11, 5, -21]] ![![-2, 1, -1, -1, 3]]
  ![![167, 0, 0, 0, 0]] where
 M := ![![![167, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-719, -40, 146, -88, -78]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![-719, -40, 146, -88, -78]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![69, 133, 164, 1, 0], ![9, 90, 97, 0, 1]] where
  M :=![![![-719, -40, 146, -88, -78], ![702, -339, 106, 526, -264], ![2376, 1600, -1445, -1420, 1578], ![-4914, -1666, 1912, 1027, -1788], ![2880, 210, -618, 288, 361]]]
  hmulB := by decide  
  f := ![![![101, 52, 6, -8, -6]], ![![54, 125, 54, 22, -24]], ![![216, 180, 139, 100, 66]], ![![285, 287, 176, 109, 42]], ![![153, 168, 107, 68, 25]]]
  g := ![![![35, 108, 128, -88, -78], ![-192, -269, -350, 526, -264], ![498, 280, 453, -1420, 1578], ![-345, 131, 40, 1027, -1788], ![-117, -408, -479, 288, 361]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 3 2 7 [95, 161, 106, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [152, 34, 99], [88, 138, 74], [0, 1]]
 g := ![![[33, 34, 23], [113, 122], [72, 161, 160], [73, 133, 24], [122, 122], [3, 67, 1], []], ![[91, 57, 62, 46], [10, 21], [155, 83, 78, 123], [90, 131, 73, 44], [32, 116], [23, 113, 75, 2], [117, 113]], ![[43, 52, 48, 42], [7, 90], [102, 157, 40, 155], [120, 54, 119, 145], [98, 38], [153, 50, 129, 82], [142, 113]]]
 h' := ![![[152, 34, 99], [163, 60, 159], [80, 153, 128], [158, 141, 92], [89, 42, 71], [61, 72, 45], [0, 0, 1], [0, 1]], ![[88, 138, 74], [78, 80, 29], [63, 113, 114], [78, 28, 13], [131, 123, 116], [24, 98, 17], [52, 140, 138], [152, 34, 99]], ![[0, 1], [79, 33, 158], [158, 80, 104], [166, 4, 68], [120, 8, 159], [61, 3, 111], [136, 33, 34], [88, 138, 74]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [157, 107], []]
 b := ![[], [150, 144, 116], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 3
  hpos := by decide
  P := [95, 161, 106, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-9845185, -2223394, 2938578, 38780, -2160054]
  a := ![0, -2, -14, -36, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![39997, 1081062, 1191352, 38780, -2160054]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 5177717 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 3, -1, -4, 2]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-5, 3, -1, -4, 2]] 
 ![![173, 0, 0, 0, 0], ![101, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![123, 0, 0, 1, 0], ![95, 0, 0, 0, 1]] where
  M :=![![![-5, 3, -1, -4, 2], ![-18, -12, 11, 10, -12], ![108, 29, -36, -12, 30], ![-117, -16, 30, -4, -21], ![21, -9, 3, 15, -8]]]
  hmulB := by decide  
  f := ![![![-397, -137, 61, 104, 62]], ![![-235, -83, 36, 62, 38]], ![![-30, -13, 4, 8, 6]], ![![-282, -99, 43, 74, 45]], ![![-226, -80, 34, 59, 36]]]
  g := ![![![0, 3, -1, -4, 2], ![6, -12, 11, 10, -12], ![-23, 29, -36, -12, 30], ![22, -16, 30, -4, -21], ![-1, -9, 3, 15, -8]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1

def I173N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![451, 245, -67, -142, -134]] i)))

def SI173N2: IdealEqSpanCertificate' Table ![![451, 245, -67, -142, -134]] 
 ![![173, 0, 0, 0, 0], ![110, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![125, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![451, 245, -67, -142, -134], ![1206, 786, -149, -386, -426], ![3834, 2335, -404, -1102, -1158], ![387, 362, 28, -74, -141], ![1959, 1299, -93, -471, -554]]]
  hmulB := by decide  
  f := ![![![-28741, -4667, 7851, 94, -5894]], ![![-17968, -2986, 4953, 138, -3746]], ![![-1676, -7, 284, -302, -106]], ![![-21364, -3721, 6001, 362, -4607]], ![![-9160, -1478, 2496, 19, -1870]]]
  g := ![![![-1, 245, -67, -142, -134], ![-60, 786, -149, -386, -426], ![-248, 2335, -404, -1102, -1158], ![-128, 362, 28, -74, -141], ![-280, 1299, -93, -471, -554]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N2 : Nat.card (O ⧸ I173N2) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N2)

lemma isPrimeI173N2 : Ideal.IsPrime I173N2 := prime_ideal_of_norm_prime hp173.out _ NI173N2
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![-719, -40, 146, -88, -78]] ![![-5, 3, -1, -4, 2]]
  ![![28741, 4667, -7851, -94, 5894]] where
 M := ![![![28741, 4667, -7851, -94, 5894]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI173N1 : IdealMulLeCertificate' Table 
  ![![28741, 4667, -7851, -94, 5894]] ![![451, 245, -67, -142, -134]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC173 : ContainsPrimesAboveP 173 ![I173N0, I173N1, I173N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI173N0
    exact isPrimeI173N1
    exact isPrimeI173N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 173 (by decide) (𝕀 ⊙ MulI173N0 ⊙ MulI173N1)
instance hp179 : Fact (Nat.Prime 179) := {out := by norm_num}

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0, 0, 0]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]] where
  M :=![![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [92, 117, 14, 87, 109, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [129, 3, 5, 35, 178], [59, 170, 76, 82, 90], [149, 95, 4, 143, 107], [91, 89, 94, 98, 162], [0, 1]]
 g := ![![[20, 6, 11, 106, 75], [61, 173, 29, 31, 5], [144, 27, 173, 135], [60, 102, 178, 153], [13, 125, 129, 28, 67], [1], []], ![[45, 47, 7, 31, 170, 164, 125, 130], [123, 92, 142, 133, 25, 85, 121, 166], [34, 145, 160, 124], [12, 75, 168, 93], [158, 117, 43, 107, 128, 129, 92, 6], [149, 88, 115, 23, 100, 108, 111, 26], [172, 54, 0, 1]], ![[46, 163, 170, 104, 23, 72, 17, 28], [128, 95, 111, 125, 131, 145, 5, 178], [55, 65, 126, 29], [111, 72, 79, 126], [106, 42, 92, 126, 140, 178, 93, 63], [87, 174, 174, 63, 40, 104, 71, 71], [28, 5, 10, 45]], ![[56, 67, 5, 60, 145, 24, 46, 110], [17, 126, 65, 138, 172, 21, 47, 177], [156, 107, 45, 20], [162, 162, 177, 81], [100, 43, 147, 65, 91, 114, 66, 85], [135, 31, 110, 93, 116, 101, 55, 126], [137, 12, 40, 172]], ![[124, 91, 48, 59, 41, 90, 104, 164], [101, 56, 162, 92, 13, 95, 8, 167], [60, 135, 177, 12], [30, 32, 18, 56], [55, 2, 128, 14, 142, 35, 11, 26], [89, 89, 10, 116, 17, 7, 77, 2], [150, 88, 72, 110]]]
 h' := ![![[129, 3, 5, 35, 178], [116, 85, 53, 167, 95], [91, 3, 176, 117, 30], [56, 24, 132, 102, 80], [57, 97, 44, 11, 42], [87, 62, 165, 92, 70], [0, 0, 1], [0, 1]], ![[59, 170, 76, 82, 90], [122, 153, 162, 22, 7], [108, 152, 68, 130, 152], [112, 70, 126, 77, 126], [58, 137, 99, 79, 123], [175, 55, 40, 74, 129], [101, 26, 91, 50, 42], [129, 3, 5, 35, 178]], ![[149, 95, 4, 143, 107], [118, 125, 100, 6, 134], [136, 167, 121, 13, 101], [149, 23, 35, 95, 71], [115, 34, 74, 40, 157], [44, 72, 59, 42, 22], [10, 35, 171, 134, 121], [59, 170, 76, 82, 90]], ![[91, 89, 94, 98, 162], [15, 103, 131, 76, 158], [152, 170, 103, 157, 149], [149, 48, 15, 153, 119], [14, 73, 178, 156, 170], [122, 137, 32, 171, 134], [110, 79, 172, 43, 36], [149, 95, 4, 143, 107]], ![[0, 1], [46, 71, 91, 87, 143], [60, 45, 69, 120, 105], [63, 14, 50, 110, 141], [106, 17, 142, 72, 45], [143, 32, 62, 158, 3], [30, 39, 102, 131, 159], [91, 89, 94, 98, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [155, 32, 162, 107], [], [], []]
 b := ![[], [31, 140, 42, 176, 107], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 5
  hpos := by decide
  P := [92, 117, 14, 87, 109, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![76659613821, -73853215842, 6410907554, 100721648725, 43649860451]
  a := ![13, -6, -1, 5, -43]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![428265999, -412587798, 35815126, 562690775, 243853969]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 183765996899 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def PBC179 : ContainsPrimesAboveP 179 ![I179N0] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI179N0
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate (u := ![![179, 0, 0, 0, 0]]) timesTableT_eq_Table B_one_repr 179 (by decide) 𝕀

instance hp181 : Fact (Nat.Prime 181) := {out := by norm_num}

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, -1, -3, 3, 1]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![20, -1, -3, 3, 1]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![164, 167, 1, 0, 0], ![130, 135, 0, 1, 0], ![122, 95, 0, 0, 1]] where
  M :=![![![20, -1, -3, 3, 1], ![-9, 14, -7, -15, 9], ![-81, -43, 42, 29, -45], ![144, 42, -50, -17, 42], ![-57, 3, 9, -15, -4]]]
  hmulB := by decide  
  f := ![![![-28, -43, -1, 11, 23]], ![![-207, -98, 13, 43, 33]], ![![-218, -131, 11, 50, 52]], ![![-175, -104, 9, 40, 41]], ![![-128, -81, 6, 30, 33]]]
  g := ![![![0, 0, -3, 3, 1], ![11, 13, -7, -15, 9], ![-29, -37, 42, 29, -45], ![30, 37, -50, -17, 42], ![5, 5, 9, -15, -4]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 2 2 7 [21, 77, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 180], [0, 1]]
 g := ![![[64, 52], [135], [143, 176], [156], [95, 45], [106, 137], [1]], ![[42, 129], [135], [166, 5], [156], [69, 136], [55, 44], [1]]]
 h' := ![![[104, 180], [107, 41], [74, 139], [179, 151], [177, 86], [127, 81], [160, 104], [0, 1]], ![[0, 1], [27, 140], [50, 42], [136, 30], [71, 95], [44, 100], [116, 77], [104, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [17]]
 b := ![[], [101, 99]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 2
  hpos := by decide
  P := [21, 77, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![728, -310, -218, -25, 747]
  a := ![-1, 0, -2, -5, 9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-284, -174, -218, -25, 747]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-11, -26, -18, -10, -4]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-11, -26, -18, -10, -4]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![105, 140, 1, 0, 0], ![164, 34, 0, 1, 0], ![161, 106, 0, 0, 1]] where
  M :=![![![-11, -26, -18, -10, -4], ![36, -17, -64, -64, -30], ![270, 62, -171, -218, -192], ![288, 142, -58, -81, -60], ![462, 252, -120, -210, -185]]]
  hmulB := by decide  
  f := ![![![-120347, 15534, 18934, 14802, -24368]], ![![219312, -28309, -34504, -26972, 44406]], ![![97611, -12600, -15357, -12004, 19764]], ![![-66040, 8524, 10390, 8123, -13372]], ![![20759, -2680, -3266, -2552, 4203]]]
  g := ![![![23, 18, -18, -10, -4], ![122, 79, -64, -64, -30], ![469, 286, -171, -218, -192], ![162, 96, -58, -81, -60], ![427, 242, -120, -210, -185]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P1 : CertificateIrreducibleZModOfList' 181 2 2 7 [132, 124, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [57, 180], [0, 1]]
 g := ![![[160, 48], [73], [166, 176], [180], [148, 80], [5, 172], [1]], ![[0, 133], [73], [62, 5], [180], [2, 101], [35, 9], [1]]]
 h' := ![![[57, 180], [78, 132], [170, 142], [95, 30], [12, 162], [64, 73], [49, 57], [0, 1]], ![[0, 1], [0, 49], [119, 39], [176, 151], [15, 19], [62, 108], [40, 124], [57, 180]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [120]]
 b := ![[], [100, 60]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N1 : CertifiedPrimeIdeal' SI181N1 181 where
  n := 2
  hpos := by decide
  P := [132, 124, 1]
  hirr := P181P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-53163, -41529, 15875, 32198, 27393]
  a := ![3, 10, 6, -2, 63]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63043, -34599, 15875, 32198, 27393]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N1 B_one_repr
lemma NI181N1 : Nat.card (O ⧸ I181N1) = 32761 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-25864, 3339, 4069, 3181, -5237]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-25864, 3339, 4069, 3181, -5237]] 
 ![![181, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![52, 0, 1, 0, 0], ![105, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-25864, 3339, 4069, 3181, -5237], ![47133, -6084, -7415, -5797, 9543], ![-85887, 11089, 13512, 10563, -17391], ![70290, -9074, -11058, -8645, 14232], ![-24465, 3159, 3849, 3009, -4954]]]
  hmulB := by decide  
  f := ![![![260, -11, -77, 65, 161]], ![![71, -5, -22, 20, 50]], ![![65, -13, -18, 27, 47]], ![![156, -3, -49, 34, 99]], ![![117, -12, -36, 36, 83]]]
  g := ![![![-1481, 3339, 4069, 3181, -5237], ![2699, -6084, -7415, -5797, 9543], ![-4918, 11089, 13512, 10563, -17391], ![4025, -9074, -11058, -8645, 14232], ![-1401, 3159, 3849, 3009, -4954]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![20, -1, -3, 3, 1]] ![![-11, -26, -18, -10, -4]]
  ![![260, -11, -77, 65, 161]] where
 M := ![![![260, -11, -77, 65, 161]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![260, -11, -77, 65, 161]] ![![-25864, 3339, 4069, 3181, -5237]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC181 : ContainsPrimesAboveP 181 ![I181N0, I181N1, I181N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI181N0
    exact isPrimeI181N1
    exact isPrimeI181N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 181 (by decide) (𝕀 ⊙ MulI181N0 ⊙ MulI181N1)
instance hp191 : Fact (Nat.Prime 191) := {out := by norm_num}

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-71, -10, 18, 0, -8]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-71, -10, 18, 0, -8]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![97, 75, 8, 1, 0], ![176, 49, 141, 0, 1]] where
  M :=![![![-71, -10, 18, 0, -8], ![72, -29, 2, 48, 0], ![0, 74, -73, -88, 144], ![-342, -156, 148, 111, -138], ![186, -6, -54, 30, 67]]]
  hmulB := by decide  
  f := ![![![-265, 38, 42, 32, -56]], ![![504, -55, -78, -64, 96]], ![![-864, 138, 141, 104, -192]], ![![31, 3, -4, -5, 2]], ![![-754, 123, 123, 90, -169]]]
  g := ![![![7, 2, 6, 0, -8], ![-24, -19, -2, 48, 0], ![-88, -2, -103, -88, 144], ![69, -9, 98, 111, -138], ![-76, -29, -51, 30, 67]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [20, 188, 186, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [63, 167, 115], [133, 23, 76], [0, 1]]
 g := ![![[121, 155, 150], [176, 35, 49], [178, 137, 136], [177, 10, 154], [68, 91, 80], [28, 5, 1], []], ![[51, 101, 130, 138], [131, 134, 127, 60], [16, 182, 173, 128], [159, 163, 160, 4], [170, 29, 169, 49], [59, 128, 169, 97], [58, 46]], ![[20, 20, 4, 155], [39, 167, 169, 122], [29, 38, 176, 99], [118, 110, 184, 11], [175, 22, 62, 55], [30, 58, 58, 37], [97, 46]]]
 h' := ![![[63, 167, 115], [109, 5, 36], [69, 176, 7], [89, 96, 30], [168, 81, 125], [13, 175, 135], [0, 0, 1], [0, 1]], ![[133, 23, 76], [127, 152, 66], [69, 137, 155], [64, 151, 79], [181, 104, 157], [40, 67, 119], [135, 50, 23], [63, 167, 115]], ![[0, 1], [86, 34, 89], [20, 69, 29], [187, 135, 82], [42, 6, 100], [80, 140, 128], [87, 141, 167], [133, 23, 76]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102, 99], []]
 b := ![[], [98, 173, 39], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [20, 188, 186, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-4198978, -2752436, 672360, 1468926, 1319342]
  a := ![1, 4, 0, -5, 31]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1983712, -929684, -1031970, 1468926, 1319342]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, -3, 5, 3, -5]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![-16, -3, 5, 3, -5]] 
 ![![191, 0, 0, 0, 0], ![172, 1, 0, 0, 0], ![21, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![92, 0, 0, 0, 1]] where
  M :=![![![-16, -3, 5, 3, -5], ![45, 4, -11, -1, 9], ![-81, 7, 10, -15, -3], ![36, -20, 6, 23, -12], ![33, 15, -15, -9, 14]]]
  hmulB := by decide  
  f := ![![![-200, -167, -51, -7, 19]], ![![-181, -152, -47, -7, 17]], ![![-21, -20, -9, -4, 0]], ![![-94, -80, -26, -5, 8]], ![![-89, -77, -27, -7, 6]]]
  g := ![![![3, -3, 5, 3, -5], ![-6, 4, -11, -1, 9], ![1, 7, 10, -15, -3], ![12, -20, 6, 23, -12], ![-14, 15, -15, -9, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-16, 21, 5, -1, -15]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-16, 21, 5, -1, -15]] 
 ![![191, 0, 0, 0, 0], ![180, 1, 0, 0, 0], ![70, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![97, 0, 0, 0, 1]] where
  M :=![![![-16, 21, 5, -1, -15], ![135, 34, -13, -23, -3], ![27, 131, 22, -15, -69], ![108, -10, -12, -9, 24], ![9, 45, 15, 3, -16]]]
  hmulB := by decide  
  f := ![![![1036, -179, -55, 401, -99]], ![![981, -162, -57, 371, -87]], ![![323, -85, 2, 159, -57]], ![![166, -1, -27, 32, 9]], ![![503, -88, -26, 196, -49]]]
  g := ![![![-14, 21, 5, -1, -15], ![-23, 34, -13, -23, -3], ![-95, 131, 22, -15, -69], ![3, -10, -12, -9, 24], ![-40, 45, 15, 3, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-71, -10, 18, 0, -8]] ![![-16, -3, 5, 3, -5]]
  ![![-1036, 179, 55, -401, 99]] where
 M := ![![![-1036, 179, 55, -401, 99]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-1036, 179, 55, -401, 99]] ![![-16, 21, 5, -1, -15]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-191, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![803, 317, -191, -218, -194]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![803, 317, -191, -218, -194]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![0, 0, 193, 0, 0], ![0, 0, 0, 193, 0], ![162, 69, 191, 25, 1]] where
  M :=![![![803, 317, -191, -218, -194], ![1746, 1194, -429, -910, -654], ![5886, 3279, -716, -1858, -2730], ![2763, 1402, -656, -678, 135], ![3399, 2595, -285, -1359, -1498]]]
  hmulB := by decide  
  f := ![![![69647, -8991, -10957, -8566, 14102]], ![![-126918, 16384, 19967, 15610, -25698]], ![![231282, -29857, -36386, -28446, 46830]], ![![-189279, 24434, 29778, 23280, -38325]], ![![217794, -28116, -34264, -26787, 44099]]]
  g := ![![![167, 71, 191, 24, -194], ![558, 240, 645, 80, -654], ![2322, 993, 2698, 344, -2730], ![-99, -41, -137, -21, 135], ![1275, 549, 1481, 187, -1498]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 4 2 7 [44, 11, 0, 43, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [17, 142, 108, 21], [183, 100, 64, 192], [143, 143, 21, 173], [0, 1]]
 g := ![![[4, 109, 143, 112], [14, 16, 48], [64, 37, 143], [177, 120, 179], [105, 42, 4], [112, 150, 1], []], ![[57, 62, 46, 142, 135, 54], [1, 80, 59], [109, 110, 28], [99, 99, 131], [90, 26, 92], [12, 51, 36], [109, 90, 118, 158, 0, 190]], ![[46, 34, 132, 93, 79, 84], [73, 79, 46], [160, 113, 67], [91, 114, 28], [36, 2, 3], [105, 55, 112], [85, 165, 91, 102, 42, 192]], ![[33, 185, 145, 127, 170, 173], [44, 181, 109], [14, 39, 96], [104, 40, 168], [108, 110, 50], [135, 148, 138], [68, 181, 154, 5, 184, 106]]]
 h' := ![![[17, 142, 108, 21], [93, 100, 169, 150], [138, 72, 9, 137], [161, 71, 176, 170], [6, 190, 153, 117], [90, 81, 43, 191], [0, 0, 0, 1], [0, 1]], ![[183, 100, 64, 192], [145, 62, 106, 174], [31, 142, 131, 161], [52, 65, 140, 75], [111, 190, 141, 175], [37, 94, 48, 142], [117, 32, 85, 6], [17, 142, 108, 21]], ![[143, 143, 21, 173], [166, 3, 95, 63], [26, 164, 45, 25], [73, 190, 62, 158], [105, 104, 104, 75], [96, 184, 16, 179], [85, 189, 179, 150], [183, 100, 64, 192]], ![[0, 1], [188, 28, 16, 192], [192, 8, 8, 63], [6, 60, 8, 176], [170, 95, 181, 19], [167, 27, 86, 67], [160, 165, 122, 36], [143, 143, 21, 173]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [162, 30, 61], []]
 b := ![[], [], [153, 30, 188, 61], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 4
  hpos := by decide
  P := [44, 11, 0, 43, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![4618314, 394753, -753832, 453804, -191469]
  a := ![4, -1, 0, 2, -9]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![184644, 70498, 185579, 27153, -191469]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 1387488001 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![69647, -8991, -10957, -8566, 14102]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![69647, -8991, -10957, -8566, 14102]] 
 ![![193, 0, 0, 0, 0], ![118, 1, 0, 0, 0], ![165, 0, 1, 0, 0], ![135, 0, 0, 1, 0], ![46, 0, 0, 0, 1]] where
  M :=![![![69647, -8991, -10957, -8566, 14102], ![-126918, 16384, 19967, 15610, -25698], ![231282, -29857, -36386, -28446, 46830], ![-189279, 24434, 29778, 23280, -38325], ![65883, -8505, -10365, -8103, 13340]]]
  hmulB := by decide  
  f := ![![![803, 317, -191, -218, -194]], ![![500, 200, -119, -138, -122]], ![![717, 288, -167, -196, -180]], ![![576, 229, -137, -156, -135]], ![![209, 89, -47, -59, -54]]]
  g := ![![![17856, -8991, -10957, -8566, 14102], ![-32539, 16384, 19967, 15610, -25698], ![59296, -29857, -36386, -28446, 46830], ![-48527, 24434, 29778, 23280, -38325], ![16891, -8505, -10365, -8103, 13340]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![803, 317, -191, -218, -194]] ![![69647, -8991, -10957, -8566, 14102]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![106, -176, 90, 177, -125]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![106, -176, 90, 177, -125]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![185, 177, 156, 1, 0], ![124, 189, 61, 0, 1]] where
  M :=![![![106, -176, 90, 177, -125], ![1125, 571, -548, -369, 531], ![-4779, -1016, 1437, 139, -1107], ![4599, 360, -982, 560, 525], ![-102, 582, -372, -738, 541]]]
  hmulB := by decide  
  f := ![![![710, 422, -106, -235, -239]], ![![2151, 1321, -272, -671, -705]], ![![6345, 3994, -667, -1861, -2013]], ![![7628, 4749, -872, -2298, -2453]], ![![4492, 2781, -535, -1372, -1455]]]
  g := ![![![-87, -40, -101, 177, -125], ![18, -175, 125, -369, 531], ![542, 932, 240, 139, -1107], ![-833, -1005, -611, 560, 525], ![352, 147, 415, -738, 541]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [164, 106, 169, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [84, 141, 147], [141, 55, 50], [0, 1]]
 g := ![![[110, 159, 65], [167, 193], [11, 8, 70], [19, 41], [46, 81], [59, 193], [1]], ![[114, 109, 165, 67], [26, 155], [180, 51, 184, 84], [60, 93], [9, 169], [164, 70], [78, 133, 103, 95]], ![[30, 8, 1, 110], [155, 142], [105, 185, 173, 45], [149, 24], [94, 90], [24, 138], [163, 159, 80, 102]]]
 h' := ![![[84, 141, 147], [168, 157, 38], [166, 107, 28], [40, 190, 55], [2, 65, 108], [81, 14, 188], [33, 91, 28], [0, 1]], ![[141, 55, 50], [61, 153, 150], [42, 91, 130], [184, 176, 26], [119, 123, 129], [77, 68, 184], [141, 2, 142], [84, 141, 147]], ![[0, 1], [9, 84, 9], [193, 196, 39], [34, 28, 116], [47, 9, 157], [57, 115, 22], [168, 104, 27], [141, 55, 50]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23, 63], []]
 b := ![[], [131, 94, 84], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [164, 106, 169, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![1917924287, 1187470983, -162031949, -523740991, -675120435]
  a := ![7, -46, -47, -48, -205]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![926522546, 1124301465, 622964006, -523740991, -675120435]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-31025, 4005, 4881, 3816, -6282]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-31025, 4005, 4881, 3816, -6282]] 
 ![![197, 0, 0, 0, 0], ![71, 1, 0, 0, 0], ![81, 0, 1, 0, 0], ![80, 0, 0, 1, 0], ![157, 0, 0, 0, 1]] where
  M :=![![![-31025, 4005, 4881, 3816, -6282], ![56538, -7298, -8895, -6954, 11448], ![-103032, 13299, 16210, 12672, -20862], ![84321, -10884, -13266, -10370, 17073], ![-29349, 3789, 4617, 3609, -5942]]]
  hmulB := by decide  
  f := ![![![1319, 1017, 111, -180, -342]], ![![491, 379, 42, -66, -126]], ![![567, 444, 55, -72, -144]], ![![527, 408, 48, -68, -135]], ![![1042, 810, 96, -135, -266]]]
  g := ![![![-151, 4005, 4881, 3816, -6282], ![275, -7298, -8895, -6954, 11448], ![-501, 13299, 16210, 12672, -20862], ![410, -10884, -13266, -10370, 17073], ![-143, 3789, 4617, 3609, -5942]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![20, 4, -6, -1, 5]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![20, 4, -6, -1, 5]] 
 ![![197, 0, 0, 0, 0], ![95, 1, 0, 0, 0], ![37, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![64, 0, 0, 0, 1]] where
  M :=![![![20, 4, -6, -1, 5], ![-45, -1, 8, -7, -3], ![27, -28, 13, 37, -21], ![45, 40, -34, -38, 39], ![-78, -18, 24, 6, -19]]]
  hmulB := by decide  
  f := ![![![856, 26, -122, -133, 83]], ![![409, 15, -58, -64, 38]], ![![179, 8, -25, -28, 16]], ![![269, 10, -38, -42, 25]], ![![284, 10, -40, -44, 27]]]
  g := ![![![-2, 4, -6, -1, 5], ![2, -1, 8, -7, -3], ![6, -28, 13, 37, -21], ![-13, 40, -34, -38, 39], ![8, -18, 24, 6, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![106, -176, 90, 177, -125]] ![![-31025, 4005, 4881, 3816, -6282]]
  ![![-3918776, 505795, 616599, 482265, -793649]] where
 M := ![![![-3918776, 505795, 616599, 482265, -793649]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-3918776, 505795, 616599, 482265, -793649]] ![![20, 4, -6, -1, 5]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![-881575, 130611, 130217, 104410, -172178]]]
 hmul := by decide  
 g := ![![![![-4475, 663, 661, 530, -874]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1)


lemma PB242I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB242I4 : PrimesBelowBoundCertificateInterval O 151 197 242 where
  m := 9
  g := ![2, 1, 2, 3, 1, 3, 3, 2, 3]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB242I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1, I173N2]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1]
    · exact ![I197N0, I197N1, I197N2]
  hC := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact PBC157
    · exact PBC163
    · exact PBC167
    · exact PBC173
    · exact PBC179
    · exact PBC181
    · exact PBC191
    · exact PBC193
    · exact PBC197
  N := fun i => by
    cases i
    rename_i i h
    interval_cases i
    · exact ![3869893, 24649]
    · exact ![115063617043]
    · exact ![4657463, 27889]
    · exact ![5177717, 173, 173]
    · exact ![183765996899]
    · exact ![32761, 32761, 181]
    · exact ![6967871, 191, 191]
    · exact ![1387488001, 193]
    · exact ![7645373, 197, 197]
  hNz := by decide
  hN := fun i => by
    cases i
    rename_i i h
    interval_cases i 
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
      exact NI167N1
    · dsimp ; intro j
      fin_cases j
      exact NI173N0
      exact NI173N1
      exact NI173N2
    · dsimp ; intro j
      fin_cases j
      exact NI179N0
    · dsimp ; intro j
      fin_cases j
      exact NI181N0
      exact NI181N1
      exact NI181N2
    · dsimp ; intro j
      fin_cases j
      exact NI191N0
      exact NI191N1
      exact NI191N2
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
  β := ![I173N1, I173N2, I181N2, I191N1, I191N2, I193N1, I197N1, I197N2]
  Il := ![[], [], [], [I173N1, I173N2], [], [I181N2], [I191N1, I191N2], [I193N1], [I197N1, I197N2]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
