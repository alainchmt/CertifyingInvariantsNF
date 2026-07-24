
import IdealArithmetic.Examples.NF5_3_112500000_1.RI5_3_112500000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![84, 22, 2, 4, -9]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![84, 22, 2, 4, -9]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![22, 39, 32, 1, 0], ![140, 137, 14, 0, 1]] where
  M :=![![![84, 22, 2, 4, -9], ![-212, 5, 30, -32, 8], ![126, -101, 43, 138, -32], ![-219, 16, -40, -77, 61], ![579, 160, -18, 18, -20]]]
  hmulB := by decide  
  f := ![![![1410, -38, 86, 206, -159]], ![![-3644, 99, -222, -532, 412]], ![![4722, -123, 289, 690, -532]], ![![225, -5, 14, 33, -25]], ![![-1481, 41, -90, -216, 168]]]
  g := ![![![8, 7, 0, 4, -9], ![-4, 1, 6, -32, 8], ![10, -7, -25, 138, -32], ![-45, -34, 10, -77, 61], ![19, 14, -2, 18, -20]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 3 2 7 [7, 57, 89, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [104, 131, 96], [121, 25, 61], [0, 1]]
 g := ![![[30, 72, 100], [70, 93], [96, 135, 143], [48, 67, 118], [27, 60, 39], [68, 1], []], ![[81, 86, 113, 91], [32, 105], [97, 10, 134, 151], [81, 107, 85, 32], [4, 64, 114, 133], [134, 154], [133, 110]], ![[104, 145, 77, 131], [136, 122], [16, 22, 31, 5], [66, 41, 76, 152], [154, 83], [105, 48], [11, 110]]]
 h' := ![![[104, 131, 96], [33, 148, 147], [113, 33, 67], [135, 17, 92], [125, 107, 78], [152, 42, 14], [0, 0, 1], [0, 1]], ![[121, 25, 61], [99, 135, 142], [3, 135, 133], [95, 92, 7], [109, 94, 133], [40, 20, 143], [151, 57, 25], [104, 131, 96]], ![[0, 1], [99, 31, 25], [57, 146, 114], [44, 48, 58], [138, 113, 103], [6, 95], [120, 100, 131], [121, 25, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [110, 74], []]
 b := ![[], [133, 7, 81], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 3
  hpos := by decide
  P := [7, 57, 89, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-12489892, -6397682, -5578045, -5916054, -2214261]
  a := ![-9, -7, -7, -10, -17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![2723948, 3361033, 1367741, -5916054, -2214261]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 3869893 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1410, -38, 86, 206, -159]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![1410, -38, 86, 206, -159]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![69, 62, 1, 0, 0], ![69, 70, 0, 1, 0], ![106, 4, 0, 0, 1]] where
  M :=![![![1410, -38, 86, 206, -159], ![-3644, 99, -222, -532, 412], ![4722, -123, 289, 690, -532], ![-4683, 126, -284, -683, 529], ![3203, -84, 198, 472, -360]]]
  hmulB := by decide  
  f := ![![![84, 22, 2, 4, -9]], ![![-212, 5, 30, -32, 8]], ![![-46, 11, 13, -10, -1]], ![![-59, 12, 14, -13, 0]], ![![55, 16, 2, 2, -6]]]
  g := ![![![-12, -122, 86, 206, -159], ![30, 315, -222, -532, 412], ![-41, -409, 289, 690, -532], ![38, 404, -284, -683, 529], ![-31, -280, 198, 472, -360]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P1 : CertificateIrreducibleZModOfList' 157 2 2 7 [89, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [52, 156], [0, 1]]
 g := ![![[10, 30], [118], [25, 130], [66, 33], [62, 109], [35], [1]], ![[0, 127], [118], [34, 27], [55, 124], [78, 48], [35], [1]]]
 h' := ![![[52, 156], [118, 40], [130, 78], [92, 82], [134, 70], [96, 100], [68, 52], [0, 1]], ![[0, 1], [0, 117], [104, 79], [117, 75], [6, 87], [115, 57], [103, 105], [52, 156]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [23]]
 b := ![[], [15, 90]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N1 : CertifiedPrimeIdeal' SI157N1 157 where
  n := 2
  hpos := by decide
  P := [89, 105, 1]
  hirr := P157P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![743983, 423438, 402212, 429658, 193914]
  a := ![-53, -53, -57, -58, -104]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-491783, -352646, 402212, 429658, 193914]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N1 B_one_repr
lemma NI157N1 : Nat.card (O ⧸ I157N1) = 24649 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![84, 22, 2, 4, -9]] ![![1410, -38, 86, 206, -159]]
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


def P163P0 : CertificateIrreducibleZModOfList' 163 5 2 7 [8, 124, 118, 127, 49, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [90, 53, 133, 15, 150], [10, 83, 50, 53, 63], [56, 108, 8, 79, 10], [121, 81, 135, 16, 103], [0, 1]]
 g := ![![[111, 71, 153, 121, 51], [112, 148, 17, 115, 1], [87, 22, 8, 9], [89, 129, 129, 69], [147, 101, 95, 119], [1], []], ![[63, 50, 156, 11, 115, 110, 157, 40], [23, 33, 85, 28, 111, 153, 113, 24], [132, 130, 59, 39], [2, 132, 141, 21], [57, 18, 82, 158], [3, 155, 127, 19, 155, 96, 59, 47], [33, 18, 131, 6]], ![[99, 134, 0, 30, 101, 113, 21, 50], [59, 75, 5, 5, 95, 131, 94, 3], [161, 64, 81, 41], [103, 157, 135, 6], [84, 107, 150, 61], [34, 138, 153, 52, 12, 9, 30, 141], [96, 96, 136, 57]], ![[91, 131, 119, 151, 66, 37, 70, 39], [48, 98, 155, 153, 18, 40, 62, 35], [152, 77, 80, 14], [128, 11, 68, 41], [7, 35, 151, 118], [134, 143, 159, 70, 74, 126, 16, 43], [20, 64, 103, 100]], ![[11, 111, 154, 38, 75, 138, 77, 11], [44, 73, 121, 108, 102, 84, 98, 154], [91, 24, 93, 65], [67, 98, 64, 83], [128, 93, 135, 156], [103, 89, 67, 119, 100, 135, 79, 149], [18, 110, 2, 14]]]
 h' := ![![[90, 53, 133, 15, 150], [82, 113, 158, 139, 122], [134, 142, 98, 82, 1], [129, 62, 74, 102, 3], [29, 63, 0, 39, 45], [155, 39, 45, 36, 114], [0, 0, 1], [0, 1]], ![[10, 83, 50, 53, 63], [66, 47, 134, 134, 115], [107, 155, 58, 149, 33], [115, 104, 86, 102, 56], [91, 117, 20, 80, 99], [59, 11, 82, 0, 141], [12, 88, 15, 59, 94], [90, 53, 133, 15, 150]], ![[56, 108, 8, 79, 10], [98, 7, 82, 89, 154], [63, 46, 119, 10, 135], [84, 62, 77, 29, 81], [16, 43, 121, 98, 13], [6, 60, 71, 59, 86], [147, 72, 32, 142, 93], [10, 83, 50, 53, 63]], ![[121, 81, 135, 16, 103], [85, 89, 100, 20, 66], [71, 80, 77, 26, 30], [31, 5, 160, 58, 60], [27, 27, 60, 42, 81], [75, 35, 151, 102, 97], [42, 139, 136, 115, 71], [56, 108, 8, 79, 10]], ![[0, 1], [95, 70, 15, 107, 32], [1, 66, 137, 59, 127], [27, 93, 92, 35, 126], [143, 76, 125, 67, 88], [29, 18, 140, 129, 51], [153, 27, 142, 10, 68], [121, 81, 135, 16, 103]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153, 114, 71, 62], [], [], []]
 b := ![[], [115, 35, 154, 18, 80], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 5
  hpos := by decide
  P := [8, 124, 118, 127, 49, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-100820005483, -51499373388, -43819369870, -46722866050, -18070105346]
  a := ![-4, -3, -4, -6, -7]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-618527641, -315947076, -268830490, -286643350, -110859542]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-254, -82, 78, 46, -29]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![-254, -82, 78, 46, -29]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![78, 18, 166, 1, 0], ![144, 112, 13, 0, 1]] where
  M :=![![![-254, -82, 78, 46, -29], ![-540, -547, -66, 260, 92], ![1038, 307, -521, -274, 260], ![515, 438, 152, -137, -153], ![-899, 136, 622, 20, -336]]]
  hmulB := by decide  
  f := ![![![968, -34, 54, 136, -113]], ![![-2604, 33, -186, -400, 272]], ![![3078, -185, 119, 386, -400]], ![![3211, -196, 122, 401, -419]], ![![-661, -23, -69, -120, 52]]]
  g := ![![![2, 14, -43, 46, -29], ![-204, -93, -266, 260, 92], ![-90, -143, 249, -274, 260], ![199, 120, 149, -137, -153], ![275, 224, 10, 20, -336]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [70, 97, 23, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [160, 42, 129], [151, 124, 38], [0, 1]]
 g := ![![[117, 157, 76], [82, 134, 152], [39, 165, 84], [87, 65], [28, 132], [98, 144, 1], []], ![[104, 20, 161, 119], [124, 105, 64, 46], [66, 33, 13, 86], [113, 12], [41, 93], [163, 77, 62, 45], [2, 108]], ![[72, 50, 22, 62], [91, 84, 162, 50], [157, 63, 139, 112], [52, 2], [69, 29], [88, 136, 156, 65], [93, 108]]]
 h' := ![![[160, 42, 129], [105, 58, 110], [109, 18, 73], [34, 147, 77], [46, 121, 30], [154, 120, 74], [0, 0, 1], [0, 1]], ![[151, 124, 38], [43, 143, 80], [20, 4, 18], [14, 110, 121], [143, 145, 124], [95, 121, 107], [76, 8, 124], [160, 42, 129]], ![[0, 1], [112, 133, 144], [24, 145, 76], [90, 77, 136], [35, 68, 13], [32, 93, 153], [92, 159, 42], [151, 124, 38]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [70, 21], []]
 b := ![[], [8, 34, 128], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [70, 97, 23, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![613210427, 322074517, 282442428, 300824327, 121571315]
  a := ![28, 32, 24, 19, 64]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-241660817, -112028447, -306795347, 300824327, 121571315]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![968, -34, 54, 136, -113]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![968, -34, 54, 136, -113]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![85, 4, 1, 0, 0], ![137, 63, 0, 1, 0], ![126, 47, 0, 0, 1]] where
  M :=![![![968, -34, 54, 136, -113], ![-2604, 33, -186, -400, 272], ![3078, -185, 119, 386, -400], ![-3343, 36, -244, -517, 345], ![1855, -236, -14, 158, -308]]]
  hmulB := by decide  
  f := ![![![-254, -82, 78, 46, -29]], ![![-540, -547, -66, 260, 92]], ![![-136, -53, 35, 28, -11]], ![![-409, -271, 40, 135, 10]], ![![-349, -215, 44, 108, 2]]]
  g := ![![![-48, -21, 54, 136, -113], ![202, 79, -186, -400, 272], ![-57, -37, 119, 386, -400], ![268, 104, -244, -517, 345], ![121, 26, -14, 158, -308]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [111, 105, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 166], [0, 1]]
 g := ![![[19, 75], [55, 152], [93, 87], [107], [124], [116, 3], [1]], ![[160, 92], [127, 15], [143, 80], [107], [124], [135, 164], [1]]]
 h' := ![![[62, 166], [74, 24], [31, 94], [12, 134], [52, 21], [150, 142], [56, 62], [0, 1]], ![[0, 1], [59, 143], [14, 73], [137, 33], [18, 146], [103, 25], [59, 105], [62, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [89]]
 b := ![[], [40, 128]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [111, 105, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![11995, 15417, 11534, 10684, 10022]
  a := ![-7, -18, -1, 12, -32]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22125, -7035, 11534, 10684, 10022]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![-254, -82, 78, 46, -29]] ![![968, -34, 54, 136, -113]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6749, -571, 540, 330, -548]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![6749, -571, 540, 330, -548]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![161, 139, 47, 96, 1]] where
  M :=![![![6749, -571, 540, 330, -548], ![-12072, 1607, -1158, 388, 660], ![6762, -2293, 1109, -2542, 388], ![-4594, 2323, -1008, 3017, -684], ![-7774, -1843, 202, -4586, 2003]]]
  hmulB := by decide  
  f := ![![![-15, -11, -6, -2, 0]], ![![-12, -11, -34, -32, -4]], ![![-82, -23, -49, -78, -32]], ![![-114, -57, -22, -23, -16]], ![![-111, -58, -59, -62, -21]]]
  g := ![![![549, 437, 152, 306, -548], ![-684, -521, -186, -364, 660], ![-322, -325, -99, -230, 388], ![610, 563, 180, 397, -684], ![-1909, -1620, -543, -1138, 2003]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [14, 127, 50, 57, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [3, 105, 142, 102], [53, 120, 9, 157], [60, 120, 22, 87], [0, 1]]
 g := ![![[111, 44, 171, 52], [108, 51, 100], [48, 171, 129, 148], [68, 24], [137, 50, 132], [116, 1], []], ![[121, 172, 69, 140, 117, 3], [121, 150, 95], [45, 104, 151, 70, 143, 168], [171, 169, 84, 79, 106, 105], [103, 78, 158], [138, 148, 169, 37, 9, 72], [137, 93, 24]], ![[70, 55, 101, 147, 156, 1], [1, 50, 126], [137, 117, 120, 122, 143, 157], [116, 2, 71, 129, 10, 138], [21, 0, 92], [115, 67, 74, 44, 35, 43], [163, 171, 83]], ![[47, 74, 6, 81, 13, 7], [55, 97, 158], [156, 28, 73, 8, 135, 19], [73, 138, 119, 110, 164, 42], [22, 125, 54], [78, 146, 0, 71, 79, 162], [20, 51, 130]]]
 h' := ![![[3, 105, 142, 102], [99, 111, 155, 158], [20, 117, 119, 163], [86, 81, 12, 119], [149, 24, 102], [106, 132, 128, 85], [0, 0, 1], [0, 1]], ![[53, 120, 9, 157], [11, 0, 143, 70], [54, 48, 127, 152], [48, 166, 83, 117], [128, 171, 135, 149], [79, 1, 97, 136], [167, 94, 146, 47], [3, 105, 142, 102]], ![[60, 120, 22, 87], [7, 78, 135, 153], [114, 158, 43, 68], [126, 43, 73, 172], [161, 103, 59, 79], [52, 10, 67, 145], [8, 5, 68, 108], [53, 120, 9, 157]], ![[0, 1], [52, 157, 86, 138], [87, 23, 57, 136], [47, 56, 5, 111], [111, 48, 50, 118], [65, 30, 54, 153], [33, 74, 131, 18], [60, 120, 22, 87]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [118, 66, 68], []]
 b := ![[], [], [119, 154, 19, 134], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [14, 127, 50, 57, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-5464475382, -120718458, -632050, -1209703674, 619783758]
  a := ![-12, 18, -14, -54, 18]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-608379540, -498674340, -168384212, -350918754, 619783758]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -11, -6, -2, 0]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-15, -11, -6, -2, 0]] 
 ![![173, 0, 0, 0, 0], ![154, 1, 0, 0, 0], ![79, 0, 1, 0, 0], ![48, 0, 0, 1, 0], ![81, 0, 0, 0, 1]] where
  M :=![![![-15, -11, -6, -2, 0], ![-12, -11, -34, -32, -4], ![-82, -23, -49, -78, -32], ![-114, -57, -22, -23, -16], ![-322, -181, -100, -82, -37]]]
  hmulB := by decide  
  f := ![![![6749, -571, 540, 330, -548]], ![![5938, -499, 474, 296, -484]], ![![3121, -274, 253, 136, -248]], ![![1846, -145, 144, 109, -156]], ![![3115, -278, 254, 128, -245]]]
  g := ![![![13, -11, -6, -2, 0], ![36, -11, -34, -32, -4], ![79, -23, -49, -78, -32], ![74, -57, -22, -23, -16], ![245, -181, -100, -82, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![6749, -571, 540, 330, -548]] ![![-15, -11, -6, -2, 0]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-305, -221, 20, 110, 14]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![-305, -221, 20, 110, 14]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![9, 134, 28, 1, 0], ![176, 146, 165, 0, 1]] where
  M :=![![![-305, -221, 20, 110, 14], ![376, -89, -374, -44, 220], ![2266, 1343, -243, -638, -44], ![-848, -143, 364, 109, -166], ![-2664, -1397, 606, 782, -167]]]
  hmulB := by decide  
  f := ![![![-2559, 73, -154, -370, 290]], ![![6652, -165, 418, 976, -740]], ![![-8462, 275, -487, -1202, 976]], ![![3575, -78, 232, 531, -392]], ![![-4922, 192, -261, -680, 585]]]
  g := ![![![-21, -95, -30, 110, 14], ![-212, -147, -198, -44, 220], ![88, 521, 139, -638, -44], ![153, 53, 138, 109, -166], ![110, -457, 35, 782, -167]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 3 2 7 [107, 22, 88, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [62, 104, 155], [29, 74, 24], [0, 1]]
 g := ![![[155, 79, 65], [74, 177, 158], [155, 57], [111, 27], [156, 21, 169], [25, 91, 1], []], ![[105, 130, 75, 169], [57, 26, 45, 110], [63, 93], [112, 106], [26, 40, 153, 66], [23, 68, 110, 141], [168, 39]], ![[107, 128, 70, 24], [137, 159, 164, 166], [117, 116], [151, 110], [148, 174, 74, 2], [112, 127, 68, 34], [120, 39]]]
 h' := ![![[62, 104, 155], [137, 167, 94], [111, 117, 64], [172, 54, 86], [134, 149, 57], [10, 95, 166], [0, 0, 1], [0, 1]], ![[29, 74, 24], [60, 162, 84], [65, 61, 138], [177, 104, 56], [40, 62, 105], [55, 19, 159], [9, 15, 74], [62, 104, 155]], ![[0, 1], [120, 29, 1], [77, 1, 156], [148, 21, 37], [175, 147, 17], [158, 65, 33], [173, 164, 104], [29, 74, 24]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [171, 148], []]
 b := ![[], [86, 130, 36], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 3
  hpos := by decide
  P := [107, 22, 88, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![356778767, 183602299, 163475113, 173655551, 65297244]
  a := ![34, 13, 25, 47, 42]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-70940984, -182232621, -86440925, 173655551, 65297244]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI179N0 : Ideal.IsPrime I179N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI179N0 B_one_repr
lemma NI179N0 : Nat.card (O ⧸ I179N0) = 5735339 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI179N0

def I179N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-28, -4, 14, 4, -7]] i)))

def SI179N1: IdealEqSpanCertificate' Table ![![-28, -4, 14, 4, -7]] 
 ![![179, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![116, 0, 1, 0, 0], ![77, 0, 0, 1, 0], ![114, 0, 0, 0, 1]] where
  M :=![![![-28, -4, 14, 4, -7], ![-140, -101, 6, 48, 8], ![102, -13, -87, -14, 48], ![115, 90, 8, -39, -17], ![-11, 98, 86, -34, -60]]]
  hmulB := by decide  
  f := ![![![225834, -6112, 13774, 32894, -25463]], ![![24496, -663, 1494, 3568, -2762]], ![![150562, -4075, 9183, 21930, -16976]], ![![92965, -2516, 5670, 13541, -10482]], ![![146677, -3970, 8946, 21364, -16538]]]
  g := ![![![-6, -4, 14, 4, -7], ![-18, -101, 6, 48, 8], ![34, -13, -87, -14, 48], ![12, 90, 8, -39, -17], ![-15, 98, 86, -34, -60]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N1 : Nat.card (O ⧸ I179N1) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N1)

lemma isPrimeI179N1 : Ideal.IsPrime I179N1 := prime_ideal_of_norm_prime hp179.out _ NI179N1

def I179N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-8, -4, 0, 0, -1]] i)))

def SI179N2: IdealEqSpanCertificate' Table ![![-8, -4, 0, 0, -1]] 
 ![![179, 0, 0, 0, 0], ![170, 1, 0, 0, 0], ![49, 0, 1, 0, 0], ![56, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![-8, -4, 0, 0, -1], ![-24, -17, -10, -4, 0], ![-10, -9, -27, -26, -4], ![-23, -6, -6, -13, -7], ![-101, -44, -20, -30, -20]]]
  hmulB := by decide  
  f := ![![![5930, -80, 336, 998, -713]], ![![5540, -75, 314, 932, -666]], ![![1752, -23, 99, 296, -211]], ![![1725, -24, 98, 289, -207]], ![![1559, -20, 88, 264, -188]]]
  g := ![![![4, -4, 0, 0, -1], ![20, -17, -10, -4, 0], ![25, -9, -27, -26, -4], ![13, -6, -6, -13, -7], ![61, -44, -20, -30, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI179N2 : Nat.card (O ⧸ I179N2) = 179 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI179N2)

lemma isPrimeI179N2 : Ideal.IsPrime I179N2 := prime_ideal_of_norm_prime hp179.out _ NI179N2
def MulI179N0 : IdealMulLeCertificate' Table 
  ![![-305, -221, 20, 110, 14]] ![![-28, -4, 14, 4, -7]]
  ![![54016, 34553, -5252, -16874, -1383]] where
 M := ![![![54016, 34553, -5252, -16874, -1383]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI179N1 : IdealMulLeCertificate' Table 
  ![![54016, 34553, -5252, -16874, -1383]] ![![-8, -4, 0, 0, -1]]
  ![![179, 0, 0, 0, 0]] where
 M := ![![![-681095, -594101, -74822, 259192, 112770]]]
 hmul := by decide  
 g := ![![![![-3805, -3319, -418, 1448, 630]]]]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-194, -253, 256, 284, -165]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-194, -253, 256, 284, -165]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![0, 0, 0, 181, 0], ![101, 86, 16, 63, 1]] where
  M :=![![![-194, -253, 256, 284, -165], ![-3448, -1651, -324, 308, 568], ![6492, 1148, -1407, -144, 308], ![-1911, 1181, 346, -1149, -1], ![147, 299, 2034, 882, -1434]]]
  hmulB := by decide  
  f := ![![![9536, -257, 582, 1390, -1075]], ![![-24636, 669, -1500, -3588, 2780]], ![![31860, -852, 1949, 4648, -3588]], ![![-31607, 859, -1924, -4603, 3567]], ![![-14450, 395, -878, -2103, 1632]]]
  g := ![![![91, 77, 16, 59, -165], ![-336, -279, -52, -196, 568], ![-136, -140, -35, -108, 308], ![-10, 7, 2, -6, -1], ![801, 683, 138, 504, -1434]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 4 2 7 [170, 79, 39, 147, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [176, 22, 16, 124], [162, 24, 126, 111], [58, 134, 39, 127], [0, 1]]
 g := ![![[16, 79, 32, 67], [141, 77, 169], [82, 129, 124, 142], [143, 5, 25], [56, 55, 45, 56], [34, 1], []], ![[93, 27, 42, 8, 160, 155], [85, 35, 111], [74, 33, 98, 149, 75, 115], [44, 93, 20], [106, 169, 97, 120, 67, 149], [60, 38, 8, 2, 35, 118], [70, 42, 172]], ![[72, 136, 89, 50, 137, 138], [114, 148, 62], [104, 102, 114, 127, 135, 152], [7, 21, 165], [167, 132, 122, 162, 130, 25], [132, 147, 5, 65, 56, 49], [142, 178, 13]], ![[112, 104, 98, 23, 150, 84], [105, 22, 133], [25, 40, 70, 12, 180, 149], [150, 69, 125], [74, 164, 25, 177, 162, 71], [45, 4, 3, 25, 122, 90], [121, 88, 20]]]
 h' := ![![[176, 22, 16, 124], [112, 135, 88, 51], [178, 42, 137, 13], [24, 95, 72, 88], [73, 126, 175, 176], [12, 40, 43, 31], [0, 0, 1], [0, 1]], ![[162, 24, 126, 111], [90, 20, 124, 104], [28, 94, 12, 78], [11, 64, 81, 135], [34, 45, 168, 127], [71, 149, 8, 113], [71, 142, 150, 12], [176, 22, 16, 124]], ![[58, 134, 39, 127], [57, 33, 13, 94], [147, 80, 29, 116], [65, 4, 36, 33], [168, 71, 7, 105], [114, 91, 67, 109], [113, 145, 42, 137], [162, 24, 126, 111]], ![[0, 1], [85, 174, 137, 113], [4, 146, 3, 155], [88, 18, 173, 106], [130, 120, 12, 135], [92, 82, 63, 109], [170, 75, 169, 32], [58, 134, 39, 127]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [173, 130, 152], []]
 b := ![[], [], [157, 72, 145, 178], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 4
  hpos := by decide
  P := [170, 79, 39, 147, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![7269672, 3524644, 3731788, 4424292, 1825720]
  a := ![-4, 0, -4, -9, -2]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-978608, -847996, -140772, -611028, 1825720]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 1073283121 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-9536, 257, -582, -1390, 1075]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-9536, 257, -582, -1390, 1075]] 
 ![![181, 0, 0, 0, 0], ![55, 1, 0, 0, 0], ![26, 0, 1, 0, 0], ![34, 0, 0, 1, 0], ![67, 0, 0, 0, 1]] where
  M :=![![![-9536, 257, -582, -1390, 1075], ![24636, -669, 1500, 3588, -2780], ![-31860, 852, -1949, -4648, 3588], ![31607, -859, 1924, 4603, -3567], ![-21591, 567, -1328, -3156, 2426]]]
  hmulB := by decide  
  f := ![![![194, 253, -256, -284, 165]], ![![78, 86, -76, -88, 47]], ![![-8, 30, -29, -40, 22]], ![![47, 41, -50, -47, 31]], ![![71, 92, -106, -110, 69]]]
  g := ![![![-184, 257, -582, -1390, 1075], ![479, -669, 1500, 3588, -2780], ![-610, 852, -1949, -4648, 3588], ![615, -859, 1924, 4603, -3567], ![-406, 567, -1328, -3156, 2426]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-194, -253, 256, 284, -165]] ![![-9536, 257, -582, -1390, 1075]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-181, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23677, -640, 1444, 3450, -2670]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![23677, -640, 1444, 3450, -2670]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![124, 88, 1, 0, 0], ![78, 52, 0, 1, 0], ![124, 4, 0, 0, 1]] where
  M :=![![![23677, -640, 1444, 3450, -2670], ![-61192, 1653, -3732, -8916, 6900], ![79068, -2138, 4821, 11520, -8916], ![-78504, 2122, -4788, -11439, 8852], ![53528, -1448, 3264, 7798, -6037]]]
  hmulB := by decide  
  f := ![![![-165, -20, 12, -18, 6]], ![![168, -141, -4, 132, -36]], ![![-32, -78, 5, 48, -12]], ![![-18, -46, 4, 29, -8]], ![![-108, -16, 8, -10, 3]]]
  g := ![![![-489, -1552, 1444, 3450, -2670], ![1264, 4011, -3732, -8916, 6900], ![-1632, -5182, 4821, 11520, -8916], ![1622, 5146, -4788, -11439, 8852], ![-1104, -3508, 3264, 7798, -6037]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 2 2 7 [22, 91, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [100, 190], [0, 1]]
 g := ![![[117, 12], [29, 30], [69, 59], [108, 34], [39, 108], [108, 68], [1]], ![[171, 179], [164, 161], [48, 132], [70, 157], [143, 83], [32, 123], [1]]]
 h' := ![![[100, 190], [126, 48], [10, 52], [107, 170], [97, 176], [107, 47], [169, 100], [0, 1]], ![[0, 1], [151, 143], [53, 139], [108, 21], [125, 15], [32, 144], [46, 91], [100, 190]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [153]]
 b := ![[], [186, 172]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 2
  hpos := by decide
  P := [22, 91, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![53152, 36881, 33590, 33906, 24024]
  a := ![15, 17, 12, 6, 36]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-50972, -25017, 33590, 33906, 24024]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 36481 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 2, 2, -2]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![11, 0, 2, 2, -2]] 
 ![![191, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![83, 0, 1, 0, 0], ![159, 0, 0, 1, 0], ![141, 0, 0, 0, 1]] where
  M :=![![![11, 0, 2, 2, -2], ![-44, -7, 0, 0, 4], ![48, -4, -3, 8, 0], ![-28, 10, -2, -9, 4], ![40, 14, 10, 2, -7]]]
  hmulB := by decide  
  f := ![![![4773, 112, 214, 1102, -670]], ![![43, 1, 2, 10, -6]], ![![2209, 52, 99, 510, -310]], ![![3833, 90, 172, 885, -538]], ![![3655, 86, 164, 844, -513]]]
  g := ![![![-1, 0, 2, 2, -2], ![-3, -7, 0, 0, 4], ![-5, -4, -3, 8, 0], ![5, 10, -2, -9, 4], ![-1, 14, 10, 2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![57, 25, 22, 24, 8]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![57, 25, 22, 24, 8]] 
 ![![191, 0, 0, 0, 0], ![52, 1, 0, 0, 0], ![176, 0, 1, 0, 0], ![144, 0, 0, 1, 0], ![3, 0, 0, 0, 1]] where
  M :=![![![57, 25, 22, 24, 8], ![236, 131, 110, 116, 48], ![686, 337, 289, 310, 116], ![352, 193, 162, 171, 70], ![1236, 623, 532, 568, 217]]]
  hmulB := by decide  
  f := ![![![-501, -49, 36, -68, 32]], ![![-132, -15, 10, -16, 8]], ![![-470, -45, 31, -66, 32]], ![![-364, -35, 28, -49, 22]], ![![-21, 0, 2, -4, 1]]]
  g := ![![![-45, 25, 22, 24, 8], ![-224, 131, 110, 116, 48], ![-590, 337, 289, 310, 116], ![-330, 193, 162, 171, 70], ![-1085, 623, 532, 568, 217]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2

def I191N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, -29, -40, 6, 25]] i)))

def SI191N3: IdealEqSpanCertificate' Table ![![22, -29, -40, 6, 25]] 
 ![![191, 0, 0, 0, 0], ![149, 1, 0, 0, 0], ![73, 0, 1, 0, 0], ![98, 0, 0, 1, 0], ![76, 0, 0, 0, 1]] where
  M :=![![![22, -29, -40, 6, 25], ![520, 293, -88, -152, 12], ![56, 282, 217, -88, -152], ![-475, -305, 42, 147, 15], ![-513, -569, -162, 232, 156]]]
  hmulB := by decide  
  f := ![![![-107368, 2897, -6566, -15632, 12089]], ![![-82308, 2220, -5034, -11984, 9267]], ![![-42912, 1157, -2625, -6248, 4831]], ![![-53231, 1435, -3256, -7751, 5993]], ![![-43993, 1185, -2692, -6406, 4952]]]
  g := ![![![25, -29, -40, 6, 25], ![-119, 293, -88, -152, 12], ![-197, 282, 217, -88, -152], ![138, -305, 42, 147, 15], ![322, -569, -162, 232, 156]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N3 : Nat.card (O ⧸ I191N3) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N3)

lemma isPrimeI191N3 : Ideal.IsPrime I191N3 := prime_ideal_of_norm_prime hp191.out _ NI191N3
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![23677, -640, 1444, 3450, -2670]] ![![11, 0, 2, 2, -2]]
  ![![154519, -4176, 9422, 22516, -17424]] where
 M := ![![![154519, -4176, 9422, 22516, -17424]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![154519, -4176, 9422, 22516, -17424]] ![![57, 25, 22, 24, 8]]
  ![![675107, -18431, 41040, 98264, -76232]] where
 M := ![![![675107, -18431, 41040, 98264, -76232]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N2 : IdealMulLeCertificate' Table 
  ![![675107, -18431, 41040, 98264, -76232]] ![![22, -29, -40, 6, 25]]
  ![![191, 0, 0, 0, 0]] where
 M := ![![![-1910, 382, 0, -382, 191]]]
 hmul := by decide  
 g := ![![![![-10, 2, 0, -2, 1]]]]
 hle2 := by decide  


def PBC191 : ContainsPrimesAboveP 191 ![I191N0, I191N1, I191N2, I191N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI191N0
    exact isPrimeI191N1
    exact isPrimeI191N2
    exact isPrimeI191N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 191 (by decide) (𝕀 ⊙ MulI191N0 ⊙ MulI191N1 ⊙ MulI191N2)
instance hp193 : Fact (Nat.Prime 193) := {out := by norm_num}

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![879, 41, 28, 80, -84]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![879, 41, 28, 80, -84]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![151, 17, 1, 0, 0], ![188, 116, 0, 1, 0], ![42, 72, 0, 0, 1]] where
  M :=![![![879, 41, 28, 80, -84], ![-1960, 175, -30, -328, 160], ![1890, -409, 305, 558, -328], ![-2460, 17, -260, -367, 350], ![2460, 221, -138, 84, -97]]]
  hmulB := by decide  
  f := ![![![-3093, 377, 226, -500, 732]], ![![18020, 2769, 2670, 5284, -1000]], ![![-881, 569, 435, 78, 512]], ![![7972, 2053, 1846, 2733, 102]], ![![6058, 1173, 1092, 1892, -177]]]
  g := ![![![-77, -19, 28, 80, -84], ![298, 141, -30, -328, 160], ![-701, -242, 305, 558, -328], ![472, 113, -260, -367, 350], ![60, -1, -138, 84, -97]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [155, 30, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [163, 192], [0, 1]]
 g := ![![[50, 157], [139], [108], [185], [185], [150], [163, 1]], ![[165, 36], [139], [108], [185], [185], [150], [133, 192]]]
 h' := ![![[163, 192], [92, 93], [54, 77], [179, 109], [26, 68], [41, 125], [18, 166], [0, 1]], ![[0, 1], [4, 100], [60, 116], [190, 84], [109, 125], [151, 68], [56, 27], [163, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [102]]
 b := ![[], [186, 51]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [155, 30, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9828, 9491, 6974, 6327, 7203]
  a := ![6, 12, 2, -5, 22]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-13136, -7055, 6974, 6327, 7203]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![129, 5, 8, 30, -16]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![129, 5, 8, 30, -16]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![118, 9, 1, 0, 0], ![186, 86, 0, 1, 0], ![74, 81, 0, 0, 1]] where
  M :=![![![129, 5, 8, 30, -16], ![-368, 7, -6, -76, 60], ![714, 51, 61, 178, -76], ![-626, 7, -12, -131, 100], ![746, 81, 86, 202, -61]]]
  hmulB := by decide  
  f := ![![![129, 41, -10, -14, -4]], ![![-116, 89, 54, -48, -28]], ![![72, 28, -3, -10, -4]], ![![72, 79, 14, -35, -16]], ![![4, 54, 18, -26, -13]]]
  g := ![![![-27, -7, 8, 30, -16], ![52, 9, -6, -76, 60], ![-176, -50, 61, 178, -76], ![92, 17, -12, -131, 100], ![-220, -68, 86, 202, -61]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P1 : CertificateIrreducibleZModOfList' 193 2 2 7 [88, 138, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [55, 192], [0, 1]]
 g := ![![[120, 181], [184], [75], [175], [59], [27], [55, 1]], ![[39, 12], [184], [75], [175], [59], [27], [110, 192]]]
 h' := ![![[55, 192], [177, 48], [100, 50], [36, 123], [31, 102], [165, 32], [178, 42], [0, 1]], ![[0, 1], [115, 145], [148, 143], [46, 70], [44, 91], [188, 161], [172, 151], [55, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [80]]
 b := ![[], [58, 40]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N1 : CertifiedPrimeIdeal' SI193N1 193 where
  n := 2
  hpos := by decide
  P := [88, 138, 1]
  hirr := P193P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![23208, 11647, 12722, 15447, 7739]
  a := ![12, 6, 8, 15, 17]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-25512, -10664, 12722, 15447, 7739]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N1 B_one_repr
lemma NI193N1 : Nat.card (O ⧸ I193N1) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51, -6, -6, -14, 4]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-51, -6, -6, -14, 4]] 
 ![![193, 0, 0, 0, 0], ![141, 1, 0, 0, 0], ![192, 0, 1, 0, 0], ![112, 0, 0, 1, 0], ![155, 0, 0, 0, 1]] where
  M :=![![![-51, -6, -6, -14, 4], ![84, -23, -16, 8, -28], ![-352, -72, -67, -112, 8], ![158, -32, -22, 19, -46], ![-458, -128, -114, -162, -13]]]
  hmulB := by decide  
  f := ![![![-5551, 134, -310, -790, 608]], ![![-3983, 95, -222, -566, 436]], ![![-5616, 136, -315, -800, 616]], ![![-3126, 76, -174, -445, 342]], ![![-4523, 110, -252, -644, 495]]]
  g := ![![![15, -6, -6, -14, 4], ![51, -23, -16, 8, -28], ![176, -72, -67, -112, 8], ![72, -32, -22, 19, -46], ![309, -128, -114, -162, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![879, 41, 28, 80, -84]] ![![129, 5, 8, 30, -16]]
  ![![5551, -134, 310, 790, -608]] where
 M := ![![![5551, -134, 310, 790, -608]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![5551, -134, 310, 790, -608]] ![![-51, -6, -6, -14, 4]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-193, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 12, 6, -6, -6]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![5, 12, 6, -6, -6]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![4, 192, 1, 0, 0], ![137, 158, 0, 1, 0], ![96, 32, 0, 0, 1]] where
  M :=![![![5, 12, 6, -6, -6], ![-132, -61, 24, 24, -12], ![-120, -120, -49, 24, 24], ![96, 54, -30, -43, 0], ![132, 126, -18, -102, -37]]]
  hmulB := by decide  
  f := ![![![-263, -60, 6, -150, 66]], ![![1596, 175, 24, 600, -300]], ![![1532, 168, 23, 576, -288]], ![![1117, 100, 24, 383, -198]], ![![108, -2, 6, 18, -13]]]
  g := ![![![7, 0, 6, -6, -6], ![-12, -41, 24, 24, -12], ![-28, 24, -49, 24, 24], ![31, 64, -30, -43, 0], ![90, 106, -18, -102, -37]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 2 2 7 [109, 48, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [149, 196], [0, 1]]
 g := ![![[89, 47], [6], [33, 10], [190], [137], [193], [149, 1]], ![[0, 150], [6], [144, 187], [190], [137], [193], [101, 196]]]
 h' := ![![[149, 196], [174, 176], [146, 177], [129, 73], [101, 105], [125, 48], [110, 28], [0, 1]], ![[0, 1], [0, 21], [121, 20], [171, 124], [183, 92], [185, 149], [145, 169], [149, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [170]]
 b := ![[], [70, 85]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 2
  hpos := by decide
  P := [109, 48, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![133172, 70679, 69743, 72272, 24690]
  a := ![-25, -6, -33, -52, -30]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-63032, -129589, 69743, 72272, 24690]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![98, -2, 6, 14, -11]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![98, -2, 6, 14, -11]] 
 ![![197, 0, 0, 0, 0], ![87, 1, 0, 0, 0], ![57, 0, 1, 0, 0], ![23, 0, 0, 1, 0], ![161, 0, 0, 0, 1]] where
  M :=![![![98, -2, 6, 14, -11], ![-252, 7, -14, -36, 28], ![322, -11, 21, 50, -36], ![-319, 10, -20, -47, 37], ![231, 0, 14, 32, -24]]]
  hmulB := by decide  
  f := ![![![1468, 26, 66, 348, -205]], ![![624, 11, 28, 148, -87]], ![![466, 9, 21, 110, -65]], ![![129, 2, 6, 31, -18]], ![![1239, 22, 56, 294, -173]]]
  g := ![![![7, -2, 6, 14, -11], ![-19, 7, -14, -36, 28], ![24, -11, 21, 50, -36], ![-25, 10, -20, -47, 37], ![13, 0, 14, 32, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N1 : Nat.card (O ⧸ I197N1) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N1)

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := prime_ideal_of_norm_prime hp197.out _ NI197N1

def I197N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![431, 314, -8, -146, -34]] i)))

def SI197N2: IdealEqSpanCertificate' Table ![![431, 314, -8, -146, -34]] 
 ![![197, 0, 0, 0, 0], ![154, 1, 0, 0, 0], ![159, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![83, 0, 0, 0, 1]] where
  M :=![![![431, 314, -8, -146, -34], ![-832, -13, 544, 108, -292], ![-2960, -1948, 239, 940, 108], ![1216, 328, -520, -249, 240], ![3992, 2158, -744, -1134, 137]]]
  hmulB := by decide  
  f := ![![![-570725, 15226, -34744, -83490, 64462]], ![![-438650, 11703, -26704, -64168, 49544]], ![![-470351, 12546, -28633, -68810, 53126]], ![![-74365, 1986, -4528, -10875, 8398]], ![![-247067, 6588, -15040, -36148, 27907]]]
  g := ![![![-201, 314, -8, -146, -34], ![-326, -13, 544, 108, -292], ![1131, -1948, 239, 940, 108], ![105, 328, -520, -249, 240], ![-957, 2158, -744, -1134, 137]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N2 : Nat.card (O ⧸ I197N2) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N2)

lemma isPrimeI197N2 : Ideal.IsPrime I197N2 := prime_ideal_of_norm_prime hp197.out _ NI197N2

def I197N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 11, 2, -4, -2]] i)))

def SI197N3: IdealEqSpanCertificate' Table ![![13, 11, 2, -4, -2]] 
 ![![197, 0, 0, 0, 0], ![163, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![64, 0, 0, 1, 0], ![184, 0, 0, 0, 1]] where
  M :=![![![13, 11, 2, -4, -2], ![-44, -11, 22, 12, -8], ![-74, -63, 3, 38, 12], ![62, 27, -14, -11, 8], ![166, 101, -4, -32, 1]]]
  hmulB := by decide  
  f := ![![![-42391, 1179, -2596, -6120, 4762]], ![![-34521, 960, -2114, -4984, 3878]], ![![-3509, 98, -215, -506, 394]], ![![-13066, 363, -800, -1887, 1468]], ![![-40070, 1115, -2454, -5784, 4501]]]
  g := ![![![-6, 11, 2, -4, -2], ![11, -11, 22, 12, -8], ![28, -63, 3, 38, 12], ![-25, 27, -14, -11, 8], ![-73, 101, -4, -32, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI197N3 : Nat.card (O ⧸ I197N3) = 197 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI197N3)

lemma isPrimeI197N3 : Ideal.IsPrime I197N3 := prime_ideal_of_norm_prime hp197.out _ NI197N3
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![5, 12, 6, -6, -6]] ![![98, -2, 6, 14, -11]]
  ![![-74, -52, 24, 28, -13]] where
 M := ![![![-74, -52, 24, 28, -13]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N1 : IdealMulLeCertificate' Table 
  ![![-74, -52, 24, 28, -13]] ![![431, 314, -8, -146, -34]]
  ![![-77518, -88182, -26848, 35518, 25231]] where
 M := ![![![-77518, -88182, -26848, 35518, 25231]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI197N2 : IdealMulLeCertificate' Table 
  ![![-77518, -88182, -26848, 35518, 25231]] ![![13, 11, 2, -4, -2]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![11249488, 5316045, -2773760, -2966426, 847691]]]
 hmul := by decide  
 g := ![![![![57104, 26985, -14080, -15058, 4303]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1, I197N2, I197N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
    exact isPrimeI197N2
    exact isPrimeI197N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0 ⊙ MulI197N1 ⊙ MulI197N2)


lemma PB519I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB519I4 : PrimesBelowBoundCertificateInterval O 151 197 519 where
  m := 9
  g := ![2, 1, 2, 2, 3, 2, 4, 3, 4]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB519I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0, I179N1, I179N2]
    · exact ![I181N0, I181N1]
    · exact ![I191N0, I191N1, I191N2, I191N3]
    · exact ![I193N0, I193N1, I193N2]
    · exact ![I197N0, I197N1, I197N2, I197N3]
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
    · exact ![895745041, 173]
    · exact ![5735339, 179, 179]
    · exact ![1073283121, 181]
    · exact ![36481, 191, 191, 191]
    · exact ![37249, 37249, 193]
    · exact ![38809, 197, 197, 197]
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
      exact NI191N3
    · dsimp ; intro j
      fin_cases j
      exact NI193N0
      exact NI193N1
      exact NI193N2
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
      exact NI197N2
      exact NI197N3
  β := ![I173N1, I179N1, I179N2, I181N1, I191N1, I191N2, I191N3, I193N2, I197N1, I197N2, I197N3]
  Il := ![[], [], [], [I173N1], [I179N1, I179N2], [I181N1], [I191N1, I191N2, I191N3], [I193N2], [I197N1, I197N2, I197N3]]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
