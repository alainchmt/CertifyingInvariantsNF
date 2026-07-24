
import IdealArithmetic.Examples.NF5_1_16200000_1.RI5_1_16200000_1
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section instance hp157 : Fact (Nat.Prime 157) := {out := by norm_num}

def I157N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-99, -204, 109, -50, 205]] i)))

def SI157N0: IdealEqSpanCertificate' Table ![![-99, -204, 109, -50, 205]] 
 ![![157, 0, 0, 0, 0], ![0, 157, 0, 0, 0], ![0, 0, 157, 0, 0], ![0, 0, 0, 157, 0], ![47, 35, 156, 84, 1]] where
  M :=![![![-99, -204, 109, -50, 205], ![410, 155, -139, 58, -175], ![-350, 40, 268, -218, 517], ![312, 386, -334, 267, -1236], ![242, 80, -249, 192, -536]]]
  hmulB := by decide  
  f := ![![![73, 28, 91, -8, 125]], ![![250, 95, 315, -28, 433]], ![![866, 328, 1086, -96, 1493]], ![![1368, 518, 1718, -153, 2364]], ![![1671, 633, 2097, -186, 2884]]]
  g := ![![![-62, -47, -203, -110, 205], ![55, 40, 173, 94, -175], ![-157, -115, -512, -278, 517], ![372, 278, 1226, 663, -1236], ![162, 120, 531, 288, -536]]]
  hle1 := by decide   
  hle2 := by decide  


def P157P0 : CertificateIrreducibleZModOfList' 157 4 2 7 [142, 57, 0, 128, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 1, 0, 0, 1]
 hbits := by decide
 h := ![[0, 1], [66, 28, 35, 125], [12, 114, 81, 90], [108, 14, 41, 99], [0, 1]]
 g := ![![[130, 56, 78, 117], [120, 146, 48], [106, 22, 91, 132], [35, 80, 109, 99], [127, 144, 54, 56], [1], []], ![[85, 150, 122, 76, 15, 54], [126, 85, 153], [43, 72, 32, 82, 113, 112], [107, 119, 153, 19, 96, 94], [139, 140, 113, 67, 80, 65], [154, 63, 11], [138, 138, 82]], ![[135, 82, 55, 111, 78, 37], [134, 80, 153], [55, 98, 18, 6, 85, 67], [123, 57, 121, 145, 41, 132], [47, 46, 61, 148, 118, 124], [46, 152, 90], [123, 7, 93]], ![[91, 100, 10, 26, 96, 57], [145, 89, 47], [101, 3, 63, 117, 37, 122], [73, 87, 62, 21, 111, 27], [34, 13, 26, 77, 115, 64], [124, 11, 153], [120, 13, 67]]]
 h' := ![![[66, 28, 35, 125], [2, 4, 150, 91], [20, 30, 30, 131], [54, 117, 133, 140], [21, 13, 155, 141], [15, 100, 0, 29], [0, 0, 1], [0, 1]], ![[12, 114, 81, 90], [50, 115, 65, 58], [94, 17, 151, 101], [17, 100, 39, 111], [64, 2, 87, 24], [76, 59, 155, 130], [146, 98, 24, 47], [66, 28, 35, 125]], ![[108, 14, 41, 99], [127, 26, 151, 69], [1, 92, 116, 101], [151, 61, 62, 129], [102, 39, 126, 84], [97, 18, 64, 77], [105, 69, 79, 54], [12, 114, 81, 90]], ![[0, 1], [53, 12, 105, 96], [62, 18, 17, 138], [107, 36, 80, 91], [150, 103, 103, 65], [7, 137, 95, 78], [119, 147, 53, 56], [108, 14, 41, 99]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [113, 134, 27], []]
 b := ![[], [], [89, 101, 135, 141], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI157N0 : CertifiedPrimeIdeal' SI157N0 157 where
  n := 4
  hpos := by decide
  P := [142, 57, 0, 128, 1]
  hirr := P157P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![2031493374, 775898912, 2536522053, -222071054, 3478531341]
  a := ![0, 36, -63, 23, -131]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-1028404329, -770526739, -3440218899, -1862539514, 3478531341]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI157N0 : Ideal.IsPrime I157N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI157N0 B_one_repr
lemma NI157N0 : Nat.card (O ⧸ I157N0) = 607573201 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI157N0

def I157N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![73, 28, 91, -8, 125]] i)))

def SI157N1: IdealEqSpanCertificate' Table ![![73, 28, 91, -8, 125]] 
 ![![157, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![65, 0, 0, 1, 0], ![142, 0, 0, 0, 1]] where
  M :=![![![73, 28, 91, -8, 125], ![250, 95, 315, -28, 433], ![866, 328, 1086, -96, 1493], ![1368, 518, 1718, -153, 2364], ![158, 60, 199, -18, 274]]]
  hmulB := by decide  
  f := ![![![-99, -204, 109, -50, 205]], ![![-10, -25, 13, -6, 25]], ![![-47, -92, 51, -24, 96]], ![![-39, -82, 43, -19, 77]], ![![-88, -184, 97, -44, 182]]]
  g := ![![![-154, 28, 91, -8, 125], ![-533, 95, 315, -28, 433], ![-1838, 328, 1086, -96, 1493], ![-2909, 518, 1718, -153, 2364], ![-337, 60, 199, -18, 274]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI157N1 : Nat.card (O ⧸ I157N1) = 157 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI157N1)

lemma isPrimeI157N1 : Ideal.IsPrime I157N1 := prime_ideal_of_norm_prime hp157.out _ NI157N1
def MulI157N0 : IdealMulLeCertificate' Table 
  ![![-99, -204, 109, -50, 205]] ![![73, 28, 91, -8, 125]]
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

def I163N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-4517, -1815, -5603, 466, -7618]] i)))

def SI163N0: IdealEqSpanCertificate' Table ![![-4517, -1815, -5603, 466, -7618]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![0, 0, 163, 0, 0], ![153, 117, 19, 1, 0], ![136, 9, 149, 0, 1]] where
  M :=![![![-4517, -1815, -5603, 466, -7618], ![-15236, -5764, -19543, 1700, -26906], ![-53812, -19773, -67782, 6226, -93730], ![-86112, -32841, -106467, 9533, -146160], ![-9900, -4175, -12083, 950, -16255]]]
  hmulB := by decide  
  f := ![![![-4119, 607, -201, 160, 646]], ![![1292, -6086, 4305, -2494, 7070]], ![![14140, 15985, -12310, 6940, -24506]], ![![-1445, -1985, 1511, -855, 2938]], ![![9500, 14714, -11130, 6310, -21367]]]
  g := ![![![5891, 75, 6875, 466, -7618], ![20760, 230, 24277, 1700, -26906], ![72030, 585, 84538, 6226, -93730], ![112473, 1026, 131842, 9533, -146160], ![12610, 190, 14674, 950, -16255]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P0 : CertificateIrreducibleZModOfList' 163 3 2 7 [33, 149, 99, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [135, 5, 73], [92, 157, 90], [0, 1]]
 g := ![![[70, 2, 36], [132, 58, 40], [131, 146], [149, 84], [118, 36], [35, 64, 1], []], ![[132, 15, 66, 48], [81, 131, 21, 37], [88, 121], [16, 65], [26, 58], [32, 42, 39, 20], [138, 113]], ![[109, 140, 89, 150], [57, 89, 55, 56], [35, 134], [153, 131], [26, 150], [97, 94, 100, 131], [121, 113]]]
 h' := ![![[135, 5, 73], [45, 107, 6], [93, 59, 23], [129, 159, 31], [51, 77, 128], [149, 8, 6], [0, 0, 1], [0, 1]], ![[92, 157, 90], [20, 135, 114], [77, 120, 94], [79, 141, 11], [97, 56, 126], [125, 129, 59], [142, 42, 157], [135, 5, 73]], ![[0, 1], [40, 84, 43], [122, 147, 46], [138, 26, 121], [121, 30, 72], [1, 26, 98], [70, 121, 5], [92, 157, 90]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [36, 34], []]
 b := ![[], [153, 9, 4], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N0 : CertifiedPrimeIdeal' SI163N0 163 where
  n := 3
  hpos := by decide
  P := [33, 149, 99, 1]
  hirr := P163P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-18231694010, -5893615279, -24598094093, 2387736401, -34770451664]
  a := ![3, 431, -805, 243, -1672]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26657828607, 169787060, 31354798848, 2387736401, -34770451664]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N0 : Ideal.IsPrime I163N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N0 B_one_repr
lemma NI163N0 : Nat.card (O ⧸ I163N0) = 4330747 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N0

def I163N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![4119, -607, 201, -160, -646]] i)))

def SI163N1: IdealEqSpanCertificate' Table ![![4119, -607, 201, -160, -646]] 
 ![![163, 0, 0, 0, 0], ![0, 163, 0, 0, 0], ![70, 125, 1, 0, 0], ![26, 47, 0, 1, 0], ![40, 116, 0, 0, 1]] where
  M :=![![![4119, -607, 201, -160, -646], ![-1292, 6086, -4305, 2494, -7070], ![-14140, -15985, 12310, -6940, 24506], ![25152, 8079, -7251, 3907, -18480], ![9804, 11161, -8591, 4844, -17087]]]
  hmulB := by decide  
  f := ![![![4517, 1815, 5603, -466, 7618]], ![![15236, 5764, 19543, -1700, 26906]], ![![13954, 5321, 17809, -1542, 24480]], ![![5642, 2153, 7182, -623, 9870]], ![![12012, 4573, 15357, -1330, 21117]]]
  g := ![![![123, 348, 201, -160, -646], ![3178, 7651, -4305, 2494, -7070], ![-10280, -24977, 12310, -6940, 24506], ![7180, 17635, -7251, 3907, -18480], ![7170, 17420, -8591, 4844, -17087]]]
  hle1 := by decide   
  hle2 := by decide  


def P163P1 : CertificateIrreducibleZModOfList' 163 2 2 7 [31, 119, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [44, 162], [0, 1]]
 g := ![![[109, 65], [107, 144], [64], [155], [54], [141, 143], [1]], ![[35, 98], [86, 19], [64], [155], [54], [76, 20], [1]]]
 h' := ![![[44, 162], [106, 37], [49, 151], [136, 155], [41, 36], [30, 124], [132, 44], [0, 1]], ![[0, 1], [104, 126], [10, 12], [110, 8], [158, 127], [107, 39], [112, 119], [44, 162]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [77]]
 b := ![[], [131, 120]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI163N1 : CertifiedPrimeIdeal' SI163N1 163 where
  n := 2
  hpos := by decide
  P := [31, 119, 1]
  hirr := P163P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![14239, 3988, 13789, -976, 17793]
  a := ![1, 34, -62, 20, -129]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-10045, -22931, 13789, -976, 17793]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI163N1 : Ideal.IsPrime I163N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI163N1 B_one_repr
lemma NI163N1 : Nat.card (O ⧸ I163N1) = 26569 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI163N1
def MulI163N0 : IdealMulLeCertificate' Table 
  ![![-4517, -1815, -5603, 466, -7618]] ![![4119, -607, 201, -160, -646]]
  ![![163, 0, 0, 0, 0]] where
 M := ![![![-163, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I167N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![189, 91, 246, -14, 323]] i)))

def SI167N0: IdealEqSpanCertificate' Table ![![189, 91, 246, -14, 323]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![0, 0, 167, 0, 0], ![102, 162, 64, 1, 0], ![20, 74, 48, 0, 1]] where
  M :=![![![189, 91, 246, -14, 323], ![646, 210, 906, -84, 1279], ![2558, 861, 3123, -326, 4379], ![4056, 1687, 4753, -399, 6396], ![394, 235, 510, -12, 632]]]
  hmulB := by decide  
  f := ![![![-173, 53, -28, 18, -7]], ![![-14, -320, 230, -132, 397]], ![![794, 743, -581, 326, -1183]], ![![178, 5, -15, 7, -68]], ![![198, 75, -66, 36, -160]]]
  g := ![![![-29, -129, -86, -14, 323], ![-98, -484, -330, -84, 1279], ![-310, -1619, -1115, -326, 4379], ![-498, -2437, -1657, -399, 6396], ![-66, -267, -174, -12, 632]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P0 : CertificateIrreducibleZModOfList' 167 3 2 7 [124, 127, 24, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [95, 96, 126], [48, 70, 41], [0, 1]]
 g := ![![[76, 89, 127], [88, 44, 72], [97, 21, 154], [47, 85], [86, 9], [115, 143, 1], []], ![[79, 81, 121, 58], [138, 73, 65, 133], [49, 161, 81, 58], [18, 11], [23, 18], [129, 32, 53, 1], [47, 11]], ![[75, 42, 71, 59], [64, 109, 158, 149], [29, 105, 77, 134], [44, 76], [124, 94], [5, 27, 29, 102], [132, 11]]]
 h' := ![![[95, 96, 126], [110, 84, 131], [163, 97, 78], [149, 159, 133], [74, 72, 69], [102, 61, 164], [0, 0, 1], [0, 1]], ![[48, 70, 41], [45, 13, 48], [61, 8, 147], [76, 136, 119], [53, 146, 41], [147, 22, 128], [24, 52, 70], [95, 96, 126]], ![[0, 1], [94, 70, 155], [7, 62, 109], [154, 39, 82], [44, 116, 57], [132, 84, 42], [131, 115, 96], [48, 70, 41]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [19, 99], []]
 b := ![[], [151, 111, 35], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N0 : CertifiedPrimeIdeal' SI167N0 167 where
  n := 3
  hpos := by decide
  P := [124, 127, 24, 1]
  hirr := P167P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![915709990, 275636538, 1209173555, -128651654, 1726343765]
  a := ![1, -178, 320, -109, 665]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-122686806, -638516372, -439650427, -128651654, 1726343765]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N0 : Ideal.IsPrime I167N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N0 B_one_repr
lemma NI167N0 : Nat.card (O ⧸ I167N0) = 4657463 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N0

def I167N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-173, 53, -28, 18, -7]] i)))

def SI167N1: IdealEqSpanCertificate' Table ![![-173, 53, -28, 18, -7]] 
 ![![167, 0, 0, 0, 0], ![0, 167, 0, 0, 0], ![29, 39, 1, 0, 0], ![19, 6, 0, 1, 0], ![53, 162, 0, 0, 1]] where
  M :=![![![-173, 53, -28, 18, -7], ![-14, -320, 230, -132, 397], ![794, 743, -581, 326, -1183], ![-1176, -283, 275, -147, 756], ![-550, -519, 406, -228, 826]]]
  hmulB := by decide  
  f := ![![![189, 91, 246, -14, 323]], ![![646, 210, 906, -84, 1279]], ![![199, 70, 273, -24, 381]], ![![69, 28, 89, -7, 121]], ![![689, 234, 960, -86, 1347]]]
  g := ![![![4, 13, -28, 18, -7], ![-151, -436, 230, -132, 397], ![444, 1276, -581, 326, -1183], ![-278, -794, 275, -147, 756], ![-310, -891, 406, -228, 826]]]
  hle1 := by decide   
  hle2 := by decide  


def P167P1 : CertificateIrreducibleZModOfList' 167 2 2 7 [139, 69, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 0, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [98, 166], [0, 1]]
 g := ![![[87, 150], [110, 56], [22, 88], [116], [133], [124, 85], [1]], ![[91, 17], [87, 111], [129, 79], [116], [133], [104, 82], [1]]]
 h' := ![![[98, 166], [74, 22], [115, 132], [122, 103], [106, 28], [132, 119], [28, 98], [0, 1]], ![[0, 1], [59, 145], [25, 35], [29, 64], [11, 139], [104, 48], [113, 69], [98, 166]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [11]]
 b := ![[], [148, 89]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI167N1 : CertifiedPrimeIdeal' SI167N1 167 where
  n := 2
  hpos := by decide
  P := [139, 69, 1]
  hirr := P167P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![44999, 19020, 13734, 158, 13264]
  a := ![-1, 70, -111, 53, -232]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-6343, -15966, 13734, 158, 13264]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI167N1 : Ideal.IsPrime I167N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI167N1 B_one_repr
lemma NI167N1 : Nat.card (O ⧸ I167N1) = 27889 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI167N1
def MulI167N0 : IdealMulLeCertificate' Table 
  ![![189, 91, 246, -14, 323]] ![![-173, 53, -28, 18, -7]]
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

def I173N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![1815, 425, -414, 220, -1145]] i)))

def SI173N0: IdealEqSpanCertificate' Table ![![1815, 425, -414, 220, -1145]] 
 ![![173, 0, 0, 0, 0], ![0, 173, 0, 0, 0], ![0, 0, 173, 0, 0], ![0, 0, 0, 173, 0], ![114, 51, 151, 61, 1]] where
  M :=![![![1815, 425, -414, 220, -1145], ![-2290, 1006, -590, 362, -445], ![-890, -4969, 3653, -2100, 6463], ![7608, 4997, -4045, 2259, -8820], ![590, 3469, -2548, 1466, -4508]]]
  hmulB := by decide  
  f := ![![![35, 13, 40, -4, 55]], ![![110, 48, 134, -10, 179]], ![![358, 135, 475, -40, 655]], ![![600, 205, 763, -75, 1068]], ![![580, 213, 750, -67, 1038]]]
  g := ![![![765, 340, 997, 405, -1145], ![280, 137, 385, 159, -445], ![-4264, -1934, -5620, -2291, 6463], ![5856, 2629, 7675, 3123, -8820], ![2974, 1349, 3920, 1598, -4508]]]
  hle1 := by decide   
  hle2 := by decide  


def P173P0 : CertificateIrreducibleZModOfList' 173 4 2 7 [50, 76, 18, 130, 1] where
 m := 1
 P := ![2]
 exp := ![2]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 1, 0, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [102, 117, 26, 35], [78, 75, 95, 116], [36, 153, 52, 22], [0, 1]]
 g := ![![[81, 69, 45, 81], [17, 20, 109], [163, 125, 27, 21], [85, 23, 154, 132], [125, 4, 167], [43, 1], []], ![[71, 91, 82, 67, 62, 34], [31, 136, 167], [7, 22, 62, 87, 52, 54], [34, 118, 119, 22, 116, 164], [138, 141, 52], [102, 46, 30, 121, 28, 43], [137, 0, 14]], ![[9, 127, 93, 110, 100, 52], [6, 101, 73], [45, 60, 4, 166, 76, 164], [95, 1, 52, 141, 25, 1], [117, 55, 106], [54, 51, 170, 112, 172, 96], [123, 165, 135]], ![[11, 42, 129, 155, 75, 47], [105, 50, 83], [124, 157, 50, 34, 156, 24], [69, 45, 19, 24, 99, 157], [124, 100, 38], [139, 69, 144, 28, 26, 9], [139, 91, 138]]]
 h' := ![![[102, 117, 26, 35], [30, 17, 155, 9], [154, 135, 20, 52], [75, 152, 104, 59], [91, 78, 120, 88], [99, 142, 15, 101], [0, 0, 1], [0, 1]], ![[78, 75, 95, 116], [56, 59, 171, 137], [7, 28, 58, 72], [69, 2, 25, 57], [6, 36, 3, 165], [32, 107, 41, 158], [94, 135, 84, 59], [102, 117, 26, 35]], ![[36, 153, 52, 22], [68, 135, 35, 50], [56, 55, 131, 65], [42, 144, 93, 65], [149, 59, 8, 112], [64, 36, 121, 25], [107, 157, 152, 12], [78, 75, 95, 116]], ![[0, 1], [162, 135, 158, 150], [7, 128, 137, 157], [136, 48, 124, 165], [69, 0, 42, 154], [53, 61, 169, 62], [55, 54, 109, 102], [36, 153, 52, 22]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [], [141, 168, 139], []]
 b := ![[], [], [5, 74, 62, 51], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI173N0 : CertifiedPrimeIdeal' SI173N0 173 where
  n := 4
  hpos := by decide
  P := [50, 76, 18, 130, 1]
  hirr := P173P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-806186446, -393065048, 84338920, 33373456, 239193856]
  a := ![0, -42, 54, -42, 112]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-162279110, -72785848, -208288632, -84147120, 239193856]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI173N0 : Ideal.IsPrime I173N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI173N0 B_one_repr
lemma NI173N0 : Nat.card (O ⧸ I173N0) = 895745041 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI173N0

def I173N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-35, -13, -40, 4, -55]] i)))

def SI173N1: IdealEqSpanCertificate' Table ![![-35, -13, -40, 4, -55]] 
 ![![173, 0, 0, 0, 0], ![88, 1, 0, 0, 0], ![41, 0, 1, 0, 0], ![55, 0, 0, 1, 0], ![105, 0, 0, 0, 1]] where
  M :=![![![-35, -13, -40, 4, -55], ![-110, -48, -134, 10, -179], ![-358, -135, -475, 40, -655], ![-600, -205, -763, 75, -1068], ![-82, -29, -88, 10, -122]]]
  hmulB := by decide  
  f := ![![![-1815, -425, 414, -220, 1145]], ![![-910, -222, 214, -114, 585]], ![![-425, -72, 77, -40, 234]], ![![-621, -164, 155, -83, 415]], ![![-1105, -278, 266, -142, 721]]]
  g := ![![![48, -13, -40, 4, -55], ![161, -48, -134, 10, -179], ![564, -135, -475, 40, -655], ![906, -205, -763, 75, -1068], ![106, -29, -88, 10, -122]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI173N1 : Nat.card (O ⧸ I173N1) = 173 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI173N1)

lemma isPrimeI173N1 : Ideal.IsPrime I173N1 := prime_ideal_of_norm_prime hp173.out _ NI173N1
def MulI173N0 : IdealMulLeCertificate' Table 
  ![![1815, 425, -414, 220, -1145]] ![![-35, -13, -40, 4, -55]]
  ![![173, 0, 0, 0, 0]] where
 M := ![![![-173, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![-1, 0, 0, 0, 0]]]]
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

def I179N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![179, 0, 0, 0, 0]] i)))

def SI179N0: IdealEqSpanCertificate' Table ![![179, 0, 0, 0, 0]] 
 ![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]] where
  M :=![![![179, 0, 0, 0, 0], ![0, 179, 0, 0, 0], ![0, 0, 179, 0, 0], ![0, 0, 0, 179, 0], ![0, 0, 0, 0, 179]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0]], ![![0, 1, 0, 0, 0]], ![![0, 0, 1, 0, 0]], ![![0, 0, 0, 1, 0]], ![![0, 0, 0, 0, 1]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  


def P179P0 : CertificateIrreducibleZModOfList' 179 5 2 7 [62, 119, 90, 122, 158, 1] where
 m := 1
 P := ![5]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 0, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [174, 97, 130, 38, 94], [69, 133, 107, 166, 14], [59, 52, 113, 54, 77], [77, 75, 8, 100, 173], [0, 1]]
 g := ![![[130, 162, 107, 136, 9], [131, 168, 31, 59, 80], [80, 160, 112, 9], [170, 90, 61, 74], [75, 73, 145, 20, 83], [1], []], ![[27, 116, 128, 175, 53, 47, 109, 73], [2, 67, 73, 74, 143, 16, 96, 24], [96, 154, 164, 27], [2, 67, 37, 171], [25, 62, 120, 2, 129, 7, 24, 40], [104, 96, 4, 11, 176, 160, 154, 131], [145, 101, 96, 65]], ![[24, 60, 1, 71, 147, 74, 116, 13], [136, 89, 19, 75, 97, 141, 76, 81], [29, 142, 125, 13], [71, 156, 16, 126], [10, 99, 82, 81, 79, 161, 1, 81], [72, 83, 116, 128, 99, 107, 115, 31], [42, 49, 172, 17]], ![[129, 32, 16, 77, 47, 36, 35, 14], [93, 146, 120, 164, 127, 171, 166, 68], [105, 169], [155, 58, 149, 67], [155, 77, 63, 15, 51, 66, 97, 61], [165, 114, 128, 76, 9, 142, 100, 129], [22, 60, 7, 22]], ![[86, 85, 144, 147, 70, 45, 165, 155], [132, 123, 133, 47, 6, 14, 124, 108], [49, 58, 19, 117], [142, 7, 28, 126], [173, 103, 26, 106, 172, 93, 38, 67], [8, 72, 90, 1, 77, 89, 3, 156], [37, 126, 93, 36]]]
 h' := ![![[174, 97, 130, 38, 94], [112, 71, 69, 21, 3], [168, 84, 118, 82, 120], [37, 80, 141, 162, 176], [4, 59, 174, 56, 49], [117, 60, 89, 57, 21], [0, 0, 1], [0, 1]], ![[69, 133, 107, 166, 14], [170, 171, 19, 87, 134], [48, 3, 34, 102, 85], [123, 102, 151, 42, 57], [151, 54, 61, 15, 156], [124, 126, 82, 20, 139], [164, 36, 0, 148, 7], [174, 97, 130, 38, 94]], ![[59, 52, 113, 54, 77], [11, 96, 35, 167, 37], [4, 118, 0, 13, 72], [141, 174, 35, 163, 27], [28, 55, 167, 46, 22], [51, 90, 57, 99, 72], [9, 115, 8, 87, 33], [69, 133, 107, 166, 14]], ![[77, 75, 8, 100, 173], [111, 150, 33, 124, 7], [90, 46, 86, 27, 136], [48, 44, 160, 166], [156, 53, 100, 32, 109], [108, 3, 138, 10, 53], [148, 156, 40, 146, 2], [59, 52, 113, 54, 77]], ![[0, 1], [15, 49, 23, 138, 177], [44, 107, 120, 134, 124], [155, 137, 50, 4, 98], [3, 137, 35, 30, 22], [87, 79, 171, 172, 73], [55, 51, 130, 156, 137], [77, 75, 8, 100, 173]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [135, 56, 96, 168], [], [], []]
 b := ![[], [27, 94, 121, 110, 82], [], [], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI179N0 : CertifiedPrimeIdeal' SI179N0 179 where
  n := 5
  hpos := by decide
  P := [62, 119, 90, 122, 158, 1]
  hirr := P179P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-2697828079392, -1032176833296, -3416401445326, 302963910706, -4692117819806]
  a := ![13, 62, -101, 45, -211]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-15071665248, -5766351024, -19086041594, 1692535814, -26212948714]
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

def I181N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-51643, -42627, 33624, -18816, 70065]] i)))

def SI181N0: IdealEqSpanCertificate' Table ![![-51643, -42627, 33624, -18816, 70065]] 
 ![![181, 0, 0, 0, 0], ![0, 181, 0, 0, 0], ![0, 0, 181, 0, 0], ![80, 133, 132, 1, 0], ![102, 157, 120, 0, 1]] where
  M :=![![![-51643, -42627, 33624, -18816, 70065], ![140130, 43628, -39408, 21198, -101259], ![-202518, 53595, -26971, 17712, 2457], ![-67608, -199779, 147603, -84307, 269316], ![142050, -36759, 18318, -12078, -2752]]]
  hmulB := by decide  
  f := ![![![1241, 1137, -414, 96, -1215]], ![![-2430, 1370, -1452, 1122, -3771]], ![![-7542, -7965, 2399, -972, 8073]], ![![-6686, -4321, 519, 137, 2637]], ![![-6378, -3427, 90, 384, 1373]]]
  g := ![![![-31453, -47184, -32544, -18816, 70065], ![48468, 72497, 51456, 21198, -101259], ![-10332, -14850, -14695, 17712, 2457], ![-114880, -172760, -116253, -84307, 269316], ![7674, 11059, 10734, -12078, -2752]]]
  hle1 := by decide   
  hle2 := by decide  


def P181P0 : CertificateIrreducibleZModOfList' 181 3 2 7 [105, 93, 74, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [113, 143, 120], [175, 37, 61], [0, 1]]
 g := ![![[142, 174, 154], [150, 129], [75, 25, 170], [45, 39], [141, 150, 43], [134, 107, 1], []], ![[110, 146, 117, 23], [128, 46], [155, 51, 32, 72], [123, 36], [125, 78, 1, 18], [45, 93, 27, 113], [58, 101]], ![[64, 50, 151, 41], [86, 180], [147, 154, 173, 151], [40, 102], [167, 92, 16, 88], [150, 133, 131, 118], [117, 101]]]
 h' := ![![[113, 143, 120], [135, 5, 71], [89, 4, 126], [83, 159, 129], [37, 48, 138], [48, 14, 119], [0, 0, 1], [0, 1]], ![[175, 37, 61], [146, 59, 150], [83, 63, 74], [162, 52, 142], [81, 6, 6], [31, 23, 110], [163, 29, 37], [113, 143, 120]], ![[0, 1], [131, 117, 141], [78, 114, 162], [43, 151, 91], [108, 127, 37], [107, 144, 133], [59, 152, 143], [175, 37, 61]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [103, 111], []]
 b := ![[], [175, 156, 76], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI181N0 : CertifiedPrimeIdeal' SI181N0 181 where
  n := 3
  hpos := by decide
  P := [105, 93, 74, 1]
  hirr := P181P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![-356485, -158638, -340371, 27944, -430087]
  a := ![-1, 4, -12, -1, -25]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![228049, 351649, 262881, 27944, -430087]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI181N0 : Ideal.IsPrime I181N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI181N0 B_one_repr
lemma NI181N0 : Nat.card (O ⧸ I181N0) = 5929741 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI181N0

def I181N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-2223, -40, 156, -66, 802]] i)))

def SI181N1: IdealEqSpanCertificate' Table ![![-2223, -40, 156, -66, 802]] 
 ![![181, 0, 0, 0, 0], ![38, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![86, 0, 0, 1, 0], ![72, 0, 0, 0, 1]] where
  M :=![![![-2223, -40, 156, -66, 802], ![1604, -2407, 1640, -962, 2426], ![4852, 7552, -5711, 3238, -10958], ![-11760, -5080, 4328, -2367, 10248], ![-3352, -5268, 3982, -2258, 7633]]]
  hmulB := by decide  
  f := ![![![-4523, -4528, 1712, -490, 5030]], ![![-894, -975, 388, -126, 1130]], ![![48, 72, -19, 14, -74]], ![![-2362, -2088, 744, -155, 2188]], ![![-1912, -1900, 714, -202, 2101]]]
  g := ![![![-295, -40, 156, -66, 802], ![-30, -2407, 1640, -962, 2426], ![1388, 7552, -5711, 3238, -10958], ![-2046, -5080, 4328, -2367, 10248], ![-964, -5268, 3982, -2258, 7633]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N1 : Nat.card (O ⧸ I181N1) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N1)

lemma isPrimeI181N1 : Ideal.IsPrime I181N1 := prime_ideal_of_norm_prime hp181.out _ NI181N1

def I181N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3105, 1894, -1185, 716, -1285]] i)))

def SI181N2: IdealEqSpanCertificate' Table ![![-3105, 1894, -1185, 716, -1285]] 
 ![![181, 0, 0, 0, 0], ![60, 1, 0, 0, 0], ![20, 0, 1, 0, 0], ![94, 0, 0, 1, 0], ![170, 0, 0, 0, 1]] where
  M :=![![![-3105, 1894, -1185, 716, -1285], ![-2570, -8017, 5915, -3380, 10759], ![21518, 16246, -12920, 7212, -27325], ![-26040, -3272, 3844, -1935, 12852], ![-14966, -11362, 9031, -5042, 19082]]]
  hmulB := by decide  
  f := ![![![-12973, -14222, 5161, -1858, 15787]], ![![-4126, -4773, 1781, -682, 5423]], ![![-1054, -1054, 354, -114, 1107]], ![![-7462, -7276, 2450, -739, 7606]], ![![-12508, -13670, 4953, -1776, 15154]]]
  g := ![![![321, 1894, -1185, 716, -1285], ![-6360, -8017, 5915, -3380, 10759], ![18080, 16246, -12920, 7212, -27325], ![-10550, -3272, 3844, -1935, 12852], ![-12618, -11362, 9031, -5042, 19082]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI181N2 : Nat.card (O ⧸ I181N2) = 181 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI181N2)

lemma isPrimeI181N2 : Ideal.IsPrime I181N2 := prime_ideal_of_norm_prime hp181.out _ NI181N2
def MulI181N0 : IdealMulLeCertificate' Table 
  ![![-51643, -42627, 33624, -18816, 70065]] ![![-2223, -40, 156, -66, 802]]
  ![![195990609, 85080217, -72428070, 39620826, -171302803]] where
 M := ![![![195990609, 85080217, -72428070, 39620826, -171302803]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI181N1 : IdealMulLeCertificate' Table 
  ![![195990609, 85080217, -72428070, 39620826, -171302803]] ![![-3105, 1894, -1185, 716, -1285]]
  ![![181, 0, 0, 0, 0]] where
 M := ![![![-853722768237, 329154793551, -187961882459, 117449336160, -116966096206]]]
 hmul := by decide  
 g := ![![![![-4716700377, 1818534771, -1038463439, 648891360, -646221526]]]]
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

def I191N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-29, 292, -172, 114, -490]] i)))

def SI191N0: IdealEqSpanCertificate' Table ![![-29, 292, -172, 114, -490]] 
 ![![191, 0, 0, 0, 0], ![0, 191, 0, 0, 0], ![0, 0, 191, 0, 0], ![21, 68, 68, 1, 0], ![148, 62, 38, 0, 1]] where
  M :=![![![-29, 292, -172, 114, -490], ![-980, -509, 76, 66, 286], ![572, -1652, 1075, -750, 3014], ![3504, 2196, -468, -97, -1608], ![48, 1288, -722, 458, -2065]]]
  hmulB := by decide  
  f := ![![![69, 108, -80, 46, -154]], ![![-308, -179, 152, -82, 334]], ![![668, 84, -79, 46, -298]], ![![135, -20, 16, -7, -6]], ![![84, 42, -28, 18, -69]]]
  g := ![![![367, 120, 56, 114, -490], ![-234, -119, -80, 66, 286], ![-2250, -720, -327, -750, 3014], ![1275, 568, 352, -97, -1608], ![1550, 514, 244, 458, -2065]]]
  hle1 := by decide   
  hle2 := by decide  


def P191P0 : CertificateIrreducibleZModOfList' 191 3 2 7 [57, 168, 86, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 1, 1, 1, 1, 1, 0, 1]
 hbits := by decide
 h := ![[0, 1], [23, 84, 27], [82, 106, 164], [0, 1]]
 g := ![![[13, 94, 150], [152, 3, 102], [136, 153, 108], [54, 14, 3], [32, 12, 20], [161, 105, 1], []], ![[97, 106, 18, 23], [97, 110, 41, 90], [45, 135, 5, 125], [31, 5, 15, 149], [69, 131, 86, 81], [151, 105, 102, 64], [97, 156]], ![[169, 189, 185, 93], [15, 55, 41, 57], [57, 181, 78, 95], [156, 77, 112, 140], [160, 74, 173, 145], [9, 76, 15, 106], [151, 156]]]
 h' := ![![[23, 84, 27], [122, 16, 36], [79, 48, 169], [169, 9, 47], [86, 133, 24], [182, 10, 163], [0, 0, 1], [0, 1]], ![[82, 106, 164], [30, 163, 46], [21, 53, 110], [115, 132, 68], [37, 7, 23], [27, 82, 167], [157, 68, 106], [23, 84, 27]], ![[0, 1], [114, 12, 109], [174, 90, 103], [75, 50, 76], [180, 51, 144], [55, 99, 52], [27, 123, 84], [82, 106, 164]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [35, 153], []]
 b := ![[], [96, 90, 58], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI191N0 : CertifiedPrimeIdeal' SI191N0 191 where
  n := 3
  hpos := by decide
  P := [57, 168, 86, 1]
  hirr := P191P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![309746, 217984, 100946, 12803, 48536]
  a := ![3, -18, 28, -15, 56]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-37395, -19172, -13686, 12803, 48536]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI191N0 : Ideal.IsPrime I191N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI191N0 B_one_repr
lemma NI191N0 : Nat.card (O ⧸ I191N0) = 6967871 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI191N0

def I191N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![261, -207, 134, -80, 167]] i)))

def SI191N1: IdealEqSpanCertificate' Table ![![261, -207, 134, -80, 167]] 
 ![![191, 0, 0, 0, 0], ![77, 1, 0, 0, 0], ![183, 0, 1, 0, 0], ![174, 0, 0, 1, 0], ![101, 0, 0, 0, 1]] where
  M :=![![![261, -207, 134, -80, 167], ![334, 788, -586, 334, -1085], ![-2170, -1505, 1207, -672, 2591], ![2424, 181, -269, 129, -1044], ![1510, 1053, -844, 470, -1810]]]
  hmulB := by decide  
  f := ![![![115, -713, 688, -288, 1589]], ![![63, -281, 282, -118, 646]], ![![121, -654, 661, -268, 1504]], ![![78, -665, 655, -261, 1494]], ![![59, -394, 376, -158, 871]]]
  g := ![![![-59, -207, 134, -80, 167], ![515, 788, -586, 334, -1085], ![-1319, -1505, 1207, -672, 2591], ![632, 181, -269, 129, -1044], ![921, 1053, -844, 470, -1810]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N1 : Nat.card (O ⧸ I191N1) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N1)

lemma isPrimeI191N1 : Ideal.IsPrime I191N1 := prime_ideal_of_norm_prime hp191.out _ NI191N1

def I191N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-21, -9, -26, 2, -35]] i)))

def SI191N2: IdealEqSpanCertificate' Table ![![-21, -9, -26, 2, -35]] 
 ![![191, 0, 0, 0, 0], ![169, 1, 0, 0, 0], ![89, 0, 1, 0, 0], ![35, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  M :=![![![-21, -9, -26, 2, -35], ![-70, -26, -92, 8, -127], ![-254, -91, -319, 30, -443], ![-408, -157, -499, 45, -684], ![-46, -21, -56, 4, -74]]]
  hmulB := by decide  
  f := ![![![365, 377, -292, 162, -569]], ![![317, 331, -256, 142, -498]], ![![181, 176, -137, 76, -270]], ![![65, 76, -59, 33, -113]], ![![38, 47, -36, 20, -68]]]
  g := ![![![24, -9, -26, 2, -35], ![80, -26, -92, 8, -127], ![278, -91, -319, 30, -443], ![447, -157, -499, 45, -684], ![53, -21, -56, 4, -74]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI191N2 : Nat.card (O ⧸ I191N2) = 191 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI191N2)

lemma isPrimeI191N2 : Ideal.IsPrime I191N2 := prime_ideal_of_norm_prime hp191.out _ NI191N2
def MulI191N0 : IdealMulLeCertificate' Table 
  ![![-29, 292, -172, 114, -490]] ![![261, -207, 134, -80, 167]]
  ![![-365, -377, 292, -162, 569]] where
 M := ![![![-365, -377, 292, -162, 569]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI191N1 : IdealMulLeCertificate' Table 
  ![![-365, -377, 292, -162, 569]] ![![-21, -9, -26, 2, -35]]
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

def I193N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-5, 2, -6, 2, -10]] i)))

def SI193N0: IdealEqSpanCertificate' Table ![![-5, 2, -6, 2, -10]] 
 ![![193, 0, 0, 0, 0], ![0, 193, 0, 0, 0], ![132, 144, 1, 0, 0], ![146, 24, 0, 1, 0], ![47, 34, 0, 0, 1]] where
  M :=![![![-5, 2, -6, 2, -10], ![-20, -15, -6, -2, -2], ![-4, -10, -43, 2, -58], ![-48, 6, -78, 11, -120], ![-24, -2, -8, 2, -13]]]
  hmulB := by decide  
  f := ![![![3, -10, 10, -6, 10]], ![![20, 45, -46, 30, -94]], ![![16, 26, -27, 18, -62]], ![![6, -2, 2, -1, -4]], ![![5, 6, -6, 4, -15]]]
  g := ![![![5, 6, -6, 2, -10], ![6, 5, -6, -2, -2], ![42, 42, -43, 2, -58], ![74, 78, -78, 11, -120], ![7, 8, -8, 2, -13]]]
  hle1 := by decide   
  hle2 := by decide  


def P193P0 : CertificateIrreducibleZModOfList' 193 2 2 7 [42, 140, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 0, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [53, 192], [0, 1]]
 g := ![![[132, 23], [49], [100], [143], [12], [172], [53, 1]], ![[0, 170], [49], [100], [143], [12], [172], [106, 192]]]
 h' := ![![[53, 192], [97, 71], [15, 186], [111, 10], [83, 23], [104, 165], [90, 65], [0, 1]], ![[0, 1], [0, 122], [30, 7], [62, 183], [144, 170], [164, 28], [61, 128], [53, 192]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [76]]
 b := ![[], [151, 38]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI193N0 : CertifiedPrimeIdeal' SI193N0 193 where
  n := 2
  hpos := by decide
  P := [42, 140, 1]
  hirr := P193P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![22375, -1790, 25647, -7573, 44656]
  a := ![1, -48, 78, -35, 163]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-22571, -26070, 25647, -7573, 44656]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI193N0 : Ideal.IsPrime I193N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI193N0 B_one_repr
lemma NI193N0 : Nat.card (O ⧸ I193N0) = 37249 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI193N0

def I193N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-6951, -2637, -8710, 774, -11975]] i)))

def SI193N1: IdealEqSpanCertificate' Table ![![-6951, -2637, -8710, 774, -11975]] 
 ![![193, 0, 0, 0, 0], ![133, 1, 0, 0, 0], ![67, 0, 1, 0, 0], ![110, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] where
  M :=![![![-6951, -2637, -8710, 774, -11975], ![-23950, -9104, -30048, 2660, -41299], ![-82598, -31319, -103741, 9202, -142655], ![-130680, -49497, -164007, 14579, -225564], ![-15150, -5745, -18960, 1688, -26068]]]
  hmulB := by decide  
  f := ![![![-79679, -293, 4772, -1894, 27341]], ![![-54625, -663, 3604, -1490, 19314]], ![![-26715, 1318, 581, -48, 7420]], ![![-47626, -1099, 3517, -1515, 17482]], ![![-47305, -1162, 3544, -1534, 17451]]]
  g := ![![![11375, -2637, -8710, 774, -11975], ![39245, -9104, -30048, 2660, -41299], ![135447, -31319, -103741, 9202, -142655], ![214124, -49497, -164007, 14579, -225564], ![24763, -5745, -18960, 1688, -26068]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N1 : Nat.card (O ⧸ I193N1) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N1)

lemma isPrimeI193N1 : Ideal.IsPrime I193N1 := prime_ideal_of_norm_prime hp193.out _ NI193N1

def I193N2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-3051, -1231, 1060, -578, 2551]] i)))

def SI193N2: IdealEqSpanCertificate' Table ![![-3051, -1231, 1060, -578, 2551]] 
 ![![193, 0, 0, 0, 0], ![134, 1, 0, 0, 0], ![186, 0, 1, 0, 0], ![16, 0, 0, 1, 0], ![93, 0, 0, 0, 1]] where
  M :=![![![-3051, -1231, 1060, -578, 2551], ![5102, -496, 64, -92, -1117], ![-2234, 6927, -4859, 2822, -7793], ![-10344, -9279, 7263, -4075, 14940], ![1602, -4815, 3372, -1960, 5396]]]
  hmulB := by decide  
  f := ![![![-27059, -35335, 14154, -5942, 42371]], ![![-18348, -24604, 9964, -4264, 29777]], ![![-25360, -32867, 13123, -5478, 39305]], ![![-3992, -2899, 771, -33, 2492]], ![![-13689, -17766, 7098, -2966, 21257]]]
  g := ![![![-1364, -1231, 1060, -578, 2551], ![855, -496, 64, -92, -1117], ![3383, 6927, -4859, 2822, -7793], ![-7472, -9279, 7263, -4075, 14940], ![-2336, -4815, 3372, -1960, 5396]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N2 : Nat.card (O ⧸ I193N2) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N2)

lemma isPrimeI193N2 : Ideal.IsPrime I193N2 := prime_ideal_of_norm_prime hp193.out _ NI193N2

def I193N3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![25, -6, 3, -2, -1]] i)))

def SI193N3: IdealEqSpanCertificate' Table ![![25, -6, 3, -2, -1]] 
 ![![193, 0, 0, 0, 0], ![168, 1, 0, 0, 0], ![147, 0, 1, 0, 0], ![113, 0, 0, 1, 0], ![147, 0, 0, 0, 1]] where
  M :=![![![25, -6, 3, -2, -1], ![-2, 43, -31, 18, -53], ![-106, -106, 82, -46, 167], ![168, 44, -40, 21, -108], ![74, 74, -57, 32, -116]]]
  hmulB := by decide  
  f := ![![![-39, 46, 29, 28, -5]], ![![-34, 39, 27, 24, -1]], ![![-23, 36, 27, 20, 4]], ![![-15, 34, 21, 17, -1]], ![![-31, 36, 22, 22, -5]]]
  g := ![![![5, -6, 3, -2, -1], ![16, 43, -31, 18, -53], ![-71, -106, 82, -46, 167], ![63, 44, -40, 21, -108], ![49, 74, -57, 32, -116]]]
  hle1 := by decide   
  hle2 := by decide  

lemma NI193N3 : Nat.card (O ⧸ I193N3) = 193 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl SI193N3)

lemma isPrimeI193N3 : Ideal.IsPrime I193N3 := prime_ideal_of_norm_prime hp193.out _ NI193N3
def MulI193N0 : IdealMulLeCertificate' Table 
  ![![-5, 2, -6, 2, -10]] ![![-6951, -2637, -8710, 774, -11975]]
  ![![372583, 141347, 467486, -41484, 642759]] where
 M := ![![![372583, 141347, 467486, -41484, 642759]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N1 : IdealMulLeCertificate' Table 
  ![![372583, 141347, 467486, -41484, 642759]] ![![-3051, -1231, 1060, -578, 2551]]
  ![![-1151649, -436812, -1445230, 128254, -1987160]] where
 M := ![![![-1151649, -436812, -1445230, 128254, -1987160]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  

def MulI193N2 : IdealMulLeCertificate' Table 
  ![![-1151649, -436812, -1445230, 128254, -1987160]] ![![25, -6, 3, -2, -1]]
  ![![193, 0, 0, 0, 0]] where
 M := ![![![-226389, -85306, -284675, 25476, -391597]]]
 hmul := by decide  
 g := ![![![![-1173, -442, -1475, 132, -2029]]]]
 hle2 := by decide  


def PBC193 : ContainsPrimesAboveP 193 ![I193N0, I193N1, I193N2, I193N3] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI193N0
    exact isPrimeI193N1
    exact isPrimeI193N2
    exact isPrimeI193N3
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 193 (by decide) (𝕀 ⊙ MulI193N0 ⊙ MulI193N1 ⊙ MulI193N2)
instance hp197 : Fact (Nat.Prime 197) := {out := by norm_num}

def I197N0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, -69, 41, -24, 46]] i)))

def SI197N0: IdealEqSpanCertificate' Table ![![101, -69, 41, -24, 46]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![0, 0, 197, 0, 0], ![178, 29, 166, 1, 0], ![185, 95, 186, 0, 1]] where
  M :=![![![101, -69, 41, -24, 46], ![92, 264, -195, 110, -346], ![-692, -527, 436, -248, 910], ![864, 153, -165, 91, -528], ![480, 375, -309, 176, -647]]]
  hmulB := by decide  
  f := ![![![-15, -5, -27, 2, -38]], ![![-76, -18, -97, 12, -142]], ![![-284, -115, -312, 30, -422]], ![![-266, -105, -304, 29, -414]], ![![-319, -122, -367, 36, -503]]]
  g := ![![![-21, -19, -23, -24, 46], ![226, 152, 233, 110, -346], ![-634, -405, -648, -248, 910], ![418, 242, 421, 91, -528], ![451, 288, 461, 176, -647]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P0 : CertificateIrreducibleZModOfList' 197 3 2 7 [35, 74, 167, 1] where
 m := 1
 P := ![3]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [41, 17, 66], [186, 179, 131], [0, 1]]
 g := ![![[72, 46, 76], [68, 37], [4, 167, 182], [18, 169], [113, 134], [102, 112], [1]], ![[46, 129, 108, 194], [168, 181], [106, 13, 109, 14], [49, 85], [54, 191], [49, 190], [71, 29, 160, 73]], ![[107, 195, 22, 131], [152, 49], [186, 64, 121, 27], [105, 169], [66, 43], [174, 109], [99, 133, 168, 124]]]
 h' := ![![[41, 17, 66], [81, 168, 154], [57, 114, 49], [98, 58, 24], [149, 164, 184], [19, 16, 118], [162, 123, 30], [0, 1]], ![[186, 179, 131], [165, 104, 42], [23, 149, 141], [162, 158, 47], [33, 183, 26], [100, 141, 114], [47, 71, 92], [41, 17, 66]], ![[0, 1], [84, 122, 1], [171, 131, 7], [122, 178, 126], [137, 47, 184], [110, 40, 162], [129, 3, 75], [186, 179, 131]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [15, 104], []]
 b := ![[], [165, 60, 82], []]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N0 : CertifiedPrimeIdeal' SI197N0 197 where
  n := 3
  hpos := by decide
  P := [35, 74, 167, 1]
  hirr := P197P0
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![9259, 24232, -17392, 10850, -38488]
  a := ![4, 3, -4, 3, -8]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![26387, 17086, 27108, 10850, -38488]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N0 : Ideal.IsPrime I197N0 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N0 B_one_repr
lemma NI197N0 : Nat.card (O ⧸ I197N0) = 7645373 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N0

def I197N1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![-15, -5, -27, 2, -38]] i)))

def SI197N1: IdealEqSpanCertificate' Table ![![-15, -5, -27, 2, -38]] 
 ![![197, 0, 0, 0, 0], ![0, 197, 0, 0, 0], ![44, 62, 1, 0, 0], ![15, 169, 0, 1, 0], ![141, 22, 0, 0, 1]] where
  M :=![![![-15, -5, -27, 2, -38], ![-76, -18, -97, 12, -142], ![-284, -115, -312, 30, -422], ![-384, -183, -477, 29, -624], ![-24, -9, -57, 2, -79]]]
  hmulB := by decide  
  f := ![![![101, -69, 41, -24, 46]], ![![92, 264, -195, 110, -346]], ![![48, 65, -50, 28, -94]], ![![91, 222, -165, 93, -296]], ![![85, -18, 6, -4, -9]]]
  g := ![![![33, 11, -27, 2, -38], ![122, 36, -97, 12, -142], ![368, 119, -312, 30, -422], ![549, 194, -477, 29, -624], ![69, 25, -57, 2, -79]]]
  hle1 := by decide   
  hle2 := by decide  


def P197P1 : CertificateIrreducibleZModOfList' 197 2 2 7 [104, 44, 1] where
 m := 1
 P := ![2]
 exp := ![1]
 hneq := by decide
 hP := by decide
 hlen := by decide
 htr := by decide
 bit := ![1, 0, 1, 0, 0, 0, 1, 1]
 hbits := by decide
 h := ![[0, 1], [153, 196], [0, 1]]
 g := ![![[8, 36], [54], [120, 175], [97], [178], [132], [153, 1]], ![[0, 161], [54], [103, 22], [97], [178], [132], [109, 196]]]
 h' := ![![[153, 196], [130, 191], [128, 137], [119, 61], [102, 140], [117, 93], [45, 59], [0, 1]], ![[0, 1], [0, 6], [10, 60], [193, 136], [49, 57], [162, 104], [10, 138], [153, 196]]]
 hs := by decide
 hz := by decide
 hmul := by decide
 a := ![[], [183]]
 b := ![[], [43, 190]]
 hhz := by decide
 hhn := by decide
 hgcd := by decide

def PI197N1 : CertifiedPrimeIdeal' SI197N1 197 where
  n := 2
  hpos := by decide
  P := [104, 44, 1]
  hirr := P197P1
  hd := by decide
  hij := by decide
  hcard := by decide
  hneq := by decide
  hlen := by decide
  c := ![13621, 5710, 22433, -1371, 30320]
  a := ![7, 22, -51, 7, -98]
  z := ![1, 0, 0, 0, 0]
  hpol := by decide
  g := ![-26538, -9241, 22433, -1371, 30320]
  hcmem := by decide
  hpmem := by decide

lemma isPrimeI197N1 : Ideal.IsPrime I197N1 := CertifiedPrimeIdeal'.isPrime timesTableT_eq_Table rfl PI197N1 B_one_repr
lemma NI197N1 : Nat.card (O ⧸ I197N1) = 38809 := CertifiedPrimeIdeal'.idealNorm timesTableT_eq_Table PI197N1
def MulI197N0 : IdealMulLeCertificate' Table 
  ![![101, -69, 41, -24, 46]] ![![-15, -5, -27, 2, -38]]
  ![![197, 0, 0, 0, 0]] where
 M := ![![![197, 0, 0, 0, 0]]]
 hmul := by decide  
 g := ![![![![1, 0, 0, 0, 0]]]]
 hle2 := by decide  


def PBC197 : ContainsPrimesAboveP 197 ![I197N0, I197N1] where 
  Ip := by 
    intro i 
    fin_cases i 
    exact isPrimeI197N0
    exact isPrimeI197N1
  hPprod := by 
    simp only [← Fin.prod_ofFn]
    exact ideal_le_singleton_IdealMulLeChainCertificate timesTableT_eq_Table B_one_repr 197 (by decide) (𝕀 ⊙ MulI197N0)


lemma PB251I4_primes (p : ℕ) :
  p ∈ Set.range ![157, 163, 167, 173, 179, 181, 191, 193, 197] ↔ Nat.Prime p ∧ 151 < p ∧ p ≤ 197 := by
  rw [← List.mem_ofFn']
  convert primes_range 151 197 (by omega)

def PB251I4 : PrimesBelowBoundCertificateInterval O 151 197 251 where
  m := 9
  g := ![2, 2, 2, 2, 1, 3, 3, 4, 2]
  P := ![157, 163, 167, 173, 179, 181, 191, 193, 197]
  hP := PB251I4_primes
  I := fun i => by
    cases i
    rename_i i h
    interval_cases i 
    · exact ![I157N0, I157N1]
    · exact ![I163N0, I163N1]
    · exact ![I167N0, I167N1]
    · exact ![I173N0, I173N1]
    · exact ![I179N0]
    · exact ![I181N0, I181N1, I181N2]
    · exact ![I191N0, I191N1, I191N2]
    · exact ![I193N0, I193N1, I193N2, I193N3]
    · exact ![I197N0, I197N1]
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
    · exact ![607573201, 157]
    · exact ![4330747, 26569]
    · exact ![4657463, 27889]
    · exact ![895745041, 173]
    · exact ![183765996899]
    · exact ![5929741, 181, 181]
    · exact ![6967871, 191, 191]
    · exact ![37249, 193, 193, 193]
    · exact ![7645373, 38809]
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
      exact NI193N2
      exact NI193N3
    · dsimp ; intro j
      fin_cases j
      exact NI197N0
      exact NI197N1
  β := ![I157N1, I173N1, I181N1, I181N2, I191N1, I191N2, I193N1, I193N2, I193N3]
  Il := ![[I157N1], [], [], [I173N1], [], [I181N1, I181N2], [I191N1, I191N2], [I193N1, I193N2, I193N3], []]
  hIl := by
      intro i
      cases i
      rename_i i h
      interval_cases i
      all_goals rfl
  hβ := by simp
